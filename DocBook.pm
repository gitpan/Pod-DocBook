#
# $Id$
#
# Copyright (c)1998-1999 Alligator Descartes <descarte@arcana.co.uk>
# Original Portions Copyright (c)Tom Christiansen
#
# $Log$
#
package Pod::DocBook;

use Pod::Functions;
use Getopt::Long;    # package for handling command-line parameters
require Exporter;
@ISA = Exporter;
@EXPORT = qw( pod2docbook );
use Cwd;
$VERSION = '0.06';

use Carp;

use strict;

=head1 NAME

Pod::DocBook - module to convert pod files to DocBook SGML

=head1 SYNOPSIS

    use Pod::DocBook;
    pod2docbook( [options] );

=head1 DESCRIPTION

Converts files from pod format ( see L<perlpod> ) to DocBook format.
It can automatically generate indexes (but SGML does this better) and
cross-references.

=head1 ARGUMENTS

Pod::DocBook takes the following arguments:

=over 4

=item help

    --help

Displays the usage message.

=item infile

    --infile=name

Specify the pod file to convert.  Input is taken from STDIN if no
infile is specified.

=item outfile

    --outfile=name

Specify the SGML file to create.  Output goes to STDOUT if no outfile
is specified.

=item title

    --title=title

Specify the title of the resulting SGML file.

=item no-header

    --no-header

Doesn't write a default header out for the DTD.

=item no-footer

    --no-footer

Doesn't write a default footer out for the DTD.

=item custom-header

    --custom-header=file

Read DTD header from a file.

=item custom-footer

    --custom-footer=file

Read footer from a file.

=item root-id

    --root-id

Specifies the root identifier for the base element used in the new SGML
document. The default is the part of the NAME header before '-' or some
short version of the full NAME header or something loosely resembling
the filename or I<pod2docbook-ch-1> if none of the above is defined.

=item verbose

    --verbose

Display progress messages.

=item style

    --style=article|book|chapter_in_book

Use 'article' or 'book' instead of default (chapter_in_book) style
(i.e. toplevel markup is sect1, not chapter; headers are different)

=item firstsect

    --firstsect=n

Start with <lt>sect I<n><gt> as the top level tag. Mainly useful for
including the docbook file into other SGML files. Use with
--no-header, --no-footer, otherwise the result will likely violate the
docbook DTD.

=back

=head1 LINKS

This release features some support for LE<lt>E<gt> tag
links. Basically anything within a single POD document should
work. External links are guessed and may of course fail. You'll need
to put together all of your converted PODs in order for SGML links to
work. Since the Id-attributes of entities are loosely based on
filename and entity name, you may get namespace conflicts. Internal
links should still work, but there is little chance for you to reach
these entities automatically from the outside.

=head1 EXAMPLE

    pod2docbook( "pod2docbook", "--infile=foo.pod", 
                 "--outfile=/perl/nmanual/foo.sgml" );

=head1 AUTHOR

Alligator Descartes E<lt>descarte@arcana.co.ukE<gt> from the original
L<pod2html> source code by Tom Christiansen, E<lt>tchrist@perl.comE<gt>,
for it is he. Many thanks to Chris Maden of O'Reilly & Associations for
doing serious road-testing on this module.

Jan Iven E<lt>jiven@gmx.de<gt> fixed a few things and had a shot at
LE<lt>E<gt> tags.


=head1 BUGS

Has trouble with CE<lt>E<gt> etc in = commands.

=head1 LIMITATIONS

There seems to be some kind of item linking using the CE<lt>E<gt>
tag. Since according to L<perlpod> item links are done with
the CE<lt>E<gt> tag, this is not supported here.

=head1 SEE ALSO

L<perlpod>

=head1 COPYRIGHT

This program is distributed under the Artistic License.

=cut

my $sectActive = 0;
my @sectStack = ();

my $listitemActive = 0;

my $noheader = 0;
my $nofooter = 0;

my $customheader = '';
my $customfooter= '';

my $firstSect1 = 1;

my $needpara = 0;  # Remember to print a <para></para> if nobody else will

# What names to map to the different Headings
my @sectNames = ('part',
		 'chapter',
		 'sect1',
		 'sect2',
		 'sect3',
		 'sect4',
		 'sect5',
		 'para');

my $defaultrootId = "pod2docbook-ch-1";
my $rootId = undef;

my @begin_stack = ();        # begin/end stack

my @libpods = ();            # files to search for links from C<> directives
my $sgmlfile = "";        # write to stdout by default
my $podfile = "";        # read from stdin by default
my @podpath = ();        # list of directories containing library pods.
my $podroot = ".";        # filesystem base directory from which all
                #   relative paths in $podpath stem.
my $recurse = 1;        # recurse on subdirectories in $podpath.
my $verbose = 0;        # not verbose by default
my $doindex = 0;               # non-zero if we should generate an index
my $listlevel = 0;        # current list depth
my @listitem = ();        # stack of SGML commands to use when a =item is
                #   encountered.  the top of the stack is the
                #   current list.
my @listdata = ();        # similar to @listitem, but for the text after
                #   an =item
my @listend = ();        # similar to @listitem, but the text to use to
                #   end the list.
my $ignore = 1;            # whether or not to format text.  we don't
                #   format text until we hit our first pod
                #   directive.
my $style = 'book';   # or 'article'

my %items_named = ();        # for the multiples of the same item in perlfunc
my @items_seen = ();
my $netscape = 0;        # whether or not to use netscape directives.
my $title;            # title to give the pod(s)
my $top = 1;            # true if we are at the top of the doc.  used
                #   to prevent the first <HR> directive.
my $paragraph;            # which paragraph we're processing (used
                #   for error messages)
my %sections = ();        # sections within this page
my %items = ();            # associative array used to find the location
                #   of =item directives referenced by C<> links
sub init_globals {
#$dircache = "pod2docbook-dircache";
#$itemcache = "pod2docbook-itemcache";

@begin_stack = ();        # begin/end stack

@libpods = ();            # files to search for links from C<> directives
$sgmlfile = "";        # write to stdout by default
$podfile = "";        # read from stdin by default
@podpath = ();        # list of directories containing library pods.
$podroot = ".";        # filesystem base directory from which all
                #   relative paths in $podpath stem.
$recurse = 1;        # recurse on subdirectories in $podpath.
$verbose = 0;        # not verbose by default
$doindex = 0;               # non-zero if we should generate an index
$listlevel = 0;        # current list depth
@listitem = ();        # stack of SGML commands to use when a =item is
                #   encountered.  the top of the stack is the
                #   current list.
@listdata = ();        # similar to @listitem, but for the text after
                #   an =item
@listend = ();        # similar to @listitem, but the text to use to
                #   end the list.
$ignore = 1;            # whether or not to format text.  we don't
                #   format text until we hit our first pod
                #   directive.
$style = 'chapter_in_book';   # or 'article'

$customheader = '';
$customfooter= '';


@items_seen = ();
%items_named = ();
$netscape = 0;        # whether or not to use netscape directives.
$title = '';            # title to give the pod(s)
$top = 1;            # true if we are at the top of the doc.  used
                #   to prevent the first <HR> directive.
$paragraph = '';            # which paragraph we're processing (used
                #   for error messages)
%sections = ();        # sections within this page

}

sub pod2docbook {
    local(@ARGV) = @_;
    local($/);
    local $_;

    init_globals();

    # parse the command-line parameters
    parse_command_line();

    # set some variables to their default values if necessary
    local *POD;
    unless (@ARGV && $ARGV[0]) { 
    $podfile  = "-" unless $podfile;    # stdin
    open(POD, "<$podfile")
        || die "$0: cannot open $podfile file for input: $!\n";
    } else {
    $podfile = $ARGV[0];  # XXX: might be more filenames
    *POD = *ARGV;
    } 
    $sgmlfile = "-" unless $sgmlfile;    # stdout

    # read the pod a paragraph at a time
    warn "Scanning for sections in input file(s)\n" if $verbose;
    $/ = "";
    my @poddata  = <POD>;
    close(POD);

    # scan the pod for =head[1-6] directives and build an index
    my $index = scan_headings(\%sections, @poddata);

    unless($index) {
      warn "No pod in $podfile\n" if $verbose;
      return;
    }

    # scan the pod for =item directives
    scan_items(\%items, @poddata);


    # open the output file
    open( SGML, ">$sgmlfile")
        || die "$0: cannot open $sgmlfile file for output: $!\n";

    # put a title in the SGML file, unless it is explicitly specified
    my $giventitle = $title; # save the given title while we do the matching
    $title = '';
    my $shorttitle = ''; # used for unique section-IDs

    TITLE_SEARCH: {
    for (my $i = 0; $i < @poddata; $i++) { 
        if ($poddata[$i] =~ /^=head1\s*NAME\b/m) {
	  for my $para ( @poddata[$i, $i+1] ) { 
            last TITLE_SEARCH
	      if ($title) = $para =~ /(\S+\s+-+.*?\S)[\n\s]*$/s;
	  }
        }
      } 
    } 

    # Try to separate scriptname from one-line description
    if ($title =~ /(\S+)\s+-+\s+/) {
      $shorttitle = $1;
    }

    # next set the rootID based on some reasonable guesswork
    # 1. explicitly set by -rootId
    # 2. short title: NAME foo - ....
    # 3. long title: NAME foo bar baz
    # 4. filename w/o extensions
    # 5. default
    #  2.-4. will be mangled to conform to SGML naming conventions
    if (!defined($rootId)) {
      my $message;
      if ($shorttitle) {
	$message = "short title";
	$rootId = $shorttitle;
      } elsif ($title) {
	$message = "full title";
	$rootId = $title;
      } elsif ($podfile && $podfile ne '-') {
	$message = "filename";
	$rootId = $podfile;
	$rootId =~ s/\.(pm|pl|pod)$//g;
      } else {
	$message = "default id";
	$rootId = $defaultrootId;
      }
      $rootId = sgmlify($rootId);
      warn "adopted $message \"$rootId\" as root Id\n" if $verbose;
    } else {
      warn "root Id set to \"$rootId\"\n" if $verbose;
    }


    if ($title and $giventitle) {
      warn "overriding found title \"$title\" with \"$giventitle\"\n"
	if $verbose;
      $title = $giventitle;
    }

    if (!$shorttitle and !$title and $podfile =~ /\.pod$/) {
    # probably a split pod so take first =head[12] as title
    for (my $i = 0; $i < @poddata; $i++) { 
        last if ($title) = $poddata[$i] =~ /^=head[12]\s*(.*?)\s*/;
    } 
    warn "adopted '$title' as title for $podfile\n"
        if $verbose and $title;
    } 
    unless ($title) { 
    warn "$0: no title for $podfile";
    $podfile =~ /^(.*)(\.[^.\/]+)?$/;
    $title = ($podfile eq "-" ? 'No Title' : $1);
    warn "using $title" if $verbose;
    }



    ## now write the complete header

    if ($noheader) {
      # NO HEADER wanted. simply put a top-level element with the title here
      my $poplevel = 0;
      push @sectStack, $poplevel;
      print SGML <<END_OF_HEAD;
<$sectNames[0] id="$rootId">
  <title>$title</title>

END_OF_HEAD
    } elsif ($customheader) {
      # CUSTOM HEADER file. Not much we can do regarding title or rootId...

	if (open(HEADER, "<$customheader")) {
	  my @tmp = <HEADER>;
	  close(HEADER);
	  print SGML @tmp;
	} else {
	  warn "$0: cannot open $customheader file for input: $!\n";
	}
    } elsif ($style eq 'article'){
      # books typically start with chapters, nor parts...
      shift @sectNames;

      print SGML <<END_OF_HEAD;
<!DOCTYPE article PUBLIC "-//Davenport//DTD DocBook V3.0//EN" [
]
>
<!-- -->
<!-- \$Id\$ -->
<!-- -->
<!-- \$Log\$ -->
<!-- -->
<!-- General reminders: -->

<article id="$rootId">
  <artheader>
    <title>$title</title>
  </artheader>
END_OF_HEAD

    } elsif ($style eq 'book') {

	print SGML <<END_OF_HEAD;
<!DOCTYPE book PUBLIC "-//Davenport//DTD DocBook V3.0//EN">
<!-- -->
<!-- \$Id\$ -->
<!-- -->
<!-- \$Log\$ -->
<!-- -->
<!-- General reminders: -->

<book id="$rootId">
  <title>$title</title>

END_OF_HEAD

    } elsif ($style eq 'chapter_in_book') {
      # compatibility style: book with one chapter (not part)
      shift @sectNames;
      my $poplevel = 0;
      push @sectStack, $poplevel;

      print SGML <<END_OF_HEAD;
<!DOCTYPE book PUBLIC "-//Davenport//DTD DocBook V3.0//EN">
<!-- -->
<!-- \$Id\$ -->
<!-- -->
<!-- \$Log\$ -->
<!-- -->
<!-- General reminders: -->

<book id="$rootId">
  <title>$title</title>

  <$sectNames[0] id="$rootId-c">
    <title>$title</title>
END_OF_HEAD

    } else {
      die "no header for style $style, use a custom header";
    }

    # normally no index is needed for SGML files. The SGML interpreter
    # does a better job of this. However, if you still insist...

    if ( $doindex ) {
      $index =~ s/--+/-/g;
      print SGML "<$sectNames[0]  id=\"$rootId-autogen-index\">\n";
      print SGML "<!-- INDEX BEGIN -->\n";
      print SGML $index;
      print SGML "<!-- INDEX END -->\n\n";
      print SGML "</$sectNames[0]>\n\n";
    }

    # now convert this file
    warn "Converting input file\n" if $verbose;
    foreach my $i (0..$#poddata) {
    $_ = $poddata[$i];
    $paragraph = $i+1;
    if (/^(=.*)/s) {    # is it a pod directive?
        $ignore = 0;
        $_ = $1;
        if (/^=begin\s+(\S+)\s*(.*)/si) {# =begin
            process_begin($1, $2);
          } elsif (/^=end\s+(\S+)\s*(.*)/si) {# =end
            process_end($1, $2);
          } elsif (/^=cut/) {            # =cut
            process_cut();
          } elsif (/^=pod/) {            # =pod
            process_pod();
          } else {
            next if @begin_stack &&
	      $begin_stack[-1] !~ /^(pod2)?docbook|sgml$/;

        if (/^=(head[1-6])\s+(.*)/s) {    # =head[1-6] heading
            process_head($1, $2);
          } elsif (/^=item\s*(.*)/sm) {    # =item text
            process_item($1);
          } elsif (/^=over\s*(.*)/) {        # =over N
            process_over();
          } elsif (/^=back/) {        # =back
            process_back();
          } elsif (/^=for\s+(\S+)\s+(.*)/si) {# =for
            process_for($1,$2);
          } else {
            /^=(\S*)\s*/;
            warn "$0: $podfile: unknown pod directive '$1' in "
               . "paragraph $paragraph.  ignoring.\n";
          }
        }
        $top = 0;
    }
    else {
        next if $ignore;
        next if @begin_stack &&
	  $begin_stack[-1] !~ /^(pod2)?docbook|sgml$/;
        my $text = $_;
        process_text(\$text, 1);
        print SGML "<para>\n$text\n</para>\n\n";
	$needpara = 0;    # we have just printed a para...
	
    }
    }

    # finish off any pending directives
    print_para_if_needed();

    my $popLevel = pop @sectStack;
    while ( defined $popLevel ) {
#        print STDERR "Clearing down stack $popLevel\n";
        print SGML "</".$sectNames[$popLevel].">\n\n";
        $popLevel = pop @sectStack;
      }

    if ( $nofooter == 0 ) {
      if ($customfooter) {
	if (open(FOOTER, "<$customfooter")) {
	  my @tmp = <FOOTER>;
	  close(FOOTER);
	  print SGML @tmp;
	} else {
	  warn "$0: cannot open $customfooter file for input: $!\n";
	}
      } elsif ($style eq 'article') {
        print SGML <<END_OF_TAIL;

</article>
END_OF_TAIL

      } elsif ($style eq 'book' or
	       $style eq 'chapter_in_book') {
        print SGML <<END_OF_TAIL;

</book>    <!-- End of the book -->
END_OF_TAIL
      } else {
	die "unknown style $style in tail";
      }
    }

    # close the sgml file
    close( SGML );

    warn "Finished\n" if $verbose;
}

##############################################################################

my $usage;            # see below
sub usage {
    my $podfile = shift;
    warn "$0: $podfile: @_\n" if @_;
    die $usage;
}

$usage =<<END_OF_USAGE;
Usage:  $0 --help --infile=<name> --outfile=<name> --verbose
           --title=<title> --root-id=<root id>

  --help       - prints this message.
  --infile     - filename for the pod to convert (input taken from stdin
                 by default).
  --outfile    - filename for the resulting sgml file (output sent to
                 stdout by default).
  --title      - title that will appear in resulting SGML file.
  --no-header  - Doesn't write a header out for the SGML file
  --no-footer  - Doesn't write a footer out for the SGML file
  --custom-header - read header from a file
  --custom-footer - read footer from a file
  --root-id    - Specifies the root identifier for chapter and section tags
  --firstsect  - Section level to start with
  --verbose    - self-explanatory
  --style      - 'book', 'chapter_in_book' (default) or 'article'

END_OF_USAGE

sub parse_command_line {
    my ( $opt_help, $opt_infile, $opt_outfile, 
         $opt_title, $opt_verbose, $opt_header, $opt_footer,
         $opt_cust_header, $opt_cust_footer, $opt_rootId,
	 $opt_style, $opt_firstsect );
    my $result = GetOptions(
                'help'       => \$opt_help,
                'infile=s'   => \$opt_infile,
                'outfile=s'  => \$opt_outfile,
                'title=s'    => \$opt_title,
                'no-header' => \$opt_header,
                'no-footer' => \$opt_footer,
                'custom-header=s' => \$opt_cust_header,
                'custom-footer=s' => \$opt_cust_footer,
                'root-id=s'   => \$opt_rootId,
                'verbose'    => \$opt_verbose,
                'style=s'    => \$opt_style,
                'firstsect=s'    => \$opt_firstsect,
               );
    usage("-", "invalid parameters") if not $result;

    usage("-") if defined $opt_help;    # see if the user asked for help
    $opt_help = "";            # just to make -w shut-up.

    $podfile  = $opt_infile if defined $opt_infile;
    $sgmlfile = $opt_outfile if defined $opt_outfile;

    $noheader = 1 if defined $opt_header;
    $nofooter = 1 if defined $opt_footer;

    $customheader = $opt_cust_header if defined $opt_cust_header;
    $customfooter = $opt_cust_footer if defined $opt_cust_footer;

    $rootId = $opt_rootId if defined $opt_rootId;

    $title    = $opt_title if defined $opt_title;
    $verbose  = defined $opt_verbose ? 1 : 0;

    $style = $opt_style if defined $opt_style;

    $opt_firstsect = 0 unless defined $opt_firstsect;
    while ($opt_firstsect) {
      $opt_firstsect--;
      shift @sectNames;
    }
    die "Can't start a section level $opt_firstsect: not enough section tags"
      unless $#sectNames >=0;
}


sub scan_headings {
    my($sections, @data) = @_;
    my($tag, $which_head, $title, $listdepth, $index);

    # here we need    local $ignore = 0;
    #  unfortunately, we can't have it, because $ignore is lexical
    $ignore = 0;

    $listdepth = 0;
    $index = "";

    # scan for =head directives, note their name, and build an index
    #  pointing to each of them. Compute some Id for the title as well.
    foreach my $line (@data) {
      if ($line =~ /^=(head)([1-6])\s+(.*)/s) {
	($tag,$which_head, $title) = ($1,$2,$3);
	chomp($title);
	my $id = sgmlify($title);
	if ($$sections{$id}) {
	  my $i = 0;
	  my $tempid=$id;
	  while ($$sections{$tempid}) {
	    $i++;
	    $tempid = $id ."-". $i;
	  }
	  $id = $tempid;
	  warn "$0: section title '$title' won't give an unique id, using '$id'\n";
	}
	$$sections{$id} = $title;
	
	
	if ($which_head > $listdepth) {
	  $index .= "\n" . ("\t" x $listdepth) . "<itemizedList>\n";
	} elsif ($which_head < $listdepth) {
	  $listdepth--;
	  $index .= "\n" . ("\t" x $listdepth) . "</itemizedList>\n";
	}
	$listdepth = $which_head;
	
	$index .= "\n" . ("\t" x $listdepth) . "<listitem><para>" .
	  "<link linkend=\"$id\">".
	    process_text( \$title, 0 ) . "</link></para></listitem>";
      }
    }

    # finish off the lists
    while ($listdepth--) {
    $index .= "\n" . ("\t" x $listdepth) . "</itemizedList>\n";
    }

    # get rid of bogus lists
    $index =~ s,\t*<UL>\s*</UL>\n,,g;

    $ignore = 1;    # restore old value;

    return $index;
}

#
# scan_items - scans the pod specified by $pod for =item directives.  we
#  will use this information later on in resolving C<> links.
#
sub scan_items {
    my($items, @poddata) = @_;
    my($i, $item);


    for (@poddata) {

      # remove any formatting instructions
      s,[A-Z]<([^<>]*)>,$1,g;

      # figure out what kind of item it is and get the rest of the string
      if (/^=item\s+([\w*]*)\s*.*$/s) {
	$item = undef;

        if ($1 eq "*") {        # bullet list
	  if ( /\A=item\s+\*\s*(.*?)\s*\Z/s) {
	    $item = $1;
	  }
        } elsif ($1 =~ /^[0-9]+/) {    # numbered list
	  if ( /\A=item\s+[0-9]+\.?(.*?)\s*\Z/s) {
	    $item = $1;
	  }
        } else {
	  if ( /\A=item\s+(.*?)\s*\Z/s) {
	    $item = $1;
	  }
        }

	if ($item) {
	  my $id = sgmlify($item);
	  if ($$items{$id}) {
	    my $i = 0;
	    my $tempid=$id;
	    while ($$items{$tempid}) {
	      $i++;
	      $tempid = $id ."-". $i;
	    }
	    $id = $tempid;
	    warn "$0: item '$item' won't give an unique id, using '$id'\n";
	  }
	  $$items{$id} = $item;
	}
      }
    }
}

#
# process_head - convert a pod head[1-6] tag and convert it to DocBook format.
#
sub process_head {
    my($tag, $heading) = @_;
    my $firstword;

    # figure out the level of the =head
    $tag =~ /head([1-6])/;
    my $level = $1;

    # can't have a heading full of spaces and speechmarks and so on
    $firstword = $heading;
    $firstword =~ s/\s*(\w+)\s.*/$1/;
    chomp($heading);

    ### If a sect is active, close it off...
    print_para_if_needed();
    my $popLevel = pop @sectStack;
    while ( defined $popLevel && $level <= $popLevel ) {
      print SGML <<"EOSGML";
</$sectNames[$popLevel]>

EOSGML

      $popLevel = pop @sectStack;
    }

    if ( defined $popLevel ) {
      push @sectStack, $popLevel;
    }

    # find a suitable Id for this section
    my $sectionId = find_id($heading, \%sections);

    ### Convert the heading and print it out.
    my $convert = $heading;
    process_text(\$convert, 0);

    print SGML <<"EOSGML";
  <$sectNames[$level]  id="$rootId-$sectionId">
    <title>$convert</title>
EOSGML

    ### Set the active sect level
    push @sectStack, $level;
    $sectActive = $level;

    $needpara = 1; # remember to print a <para> next
}

#
# process_item - convert a pod item tag and convert it to SGML format.
#
sub process_item {
  my ($text) = @_;
  my($i, $quote, $name);

  my $need_preamble = 0;
  my $this_entry;

  print_para_if_needed();

  # lots of documents start a list without doing an =over.  this is
  # bad!  but, the proper thing to do seems to be to just assume
  # they did do an =over.  so warn them once and then continue.
  warn "$0: $podfile: unexpected =item directive in paragraph $paragraph.  ignoring.\n"
    unless $listlevel;
  process_over() unless $listlevel;

  return unless $listlevel;

  # remove formatting instructions from the text
  1 while $text =~ s/[A-Z]<([^<>]*)>/$1/g;
  pre_escape(\$text);

  $need_preamble = $items_seen[$listlevel]++ == 0;

  # check if this is the first =item after an =over  , NO
  #    $i = $listlevel - 1;    , NO
  # my $need_new = $listlevel >= @listitem;

  if ( $text =~ /\A\*/ ) {        # bullet-point list
    if ( $listitemActive == 1 ) {
      print SGML "</listitem>\n";
      $listitemActive = 0;
    }
    if ( $need_preamble ) {
      push( @listend,  "</listitem></itemizedList>\n" );
      print SGML "<itemizedList>\n";
    }

    $text =~ /\A\*\s*(.*?)\s*\Z/s;
    my $itemId = "id=\"$rootId-".find_id($1, \%items)."\"" if $1;
    print SGML "<listitem $itemId>\n";
    if ($1) {
      print SGML "<para>";
      print SGML $1;
      print SGML "</para>\n";
    } else {
      $needpara = 1;
    }
    $listitemActive = 1;

  } elsif ( $text =~ /\A[0-9\#]+/ ) {    # numbered list

    if ( $listitemActive == 1 ) {
      print_para_if_needed();
      print SGML "</listitem>\n";
      $listitemActive = 0;
    }
    if ($need_preamble) {
      push( @listend,  "</listitem></orderedlist>\n" );
      print SGML "<orderedList>\n";
    }

    $text =~ /\A[0-9]+\.?(.*?)\s*\Z/s;
    my $itemId = "id=\"$rootId-".find_id($1, \%items)."\"" if $1;
    print SGML "<listitem $itemId>\n";
    if ($1) {
      print SGML "<para>\n";
      print SGML $1;
      print SGML "</para>\n";
    } else {
      $needpara = 1;
    }
    $listitemActive = 1;

  } else { # all others. just stick everything into the <varlistentry>

    if ( $listitemActive == 1 ) {
      print_para_if_needed();
      print SGML "</listitem></varlistentry>\n";
      $listitemActive = 0;
    }
    if ( $need_preamble ) {
      push( @listend,  "</listitem></varlistentry></variablelist>\n" );
      print SGML "<variableList>\n";
    }

    $text =~ /\A\s*(.*?)\s*\Z/s;
    my $itemId = "id=\"$rootId-".find_id($1, \%items)."\"" if $1;
    print SGML "<varlistentry $itemId>\n";
    print SGML "<term><emphasis>";
    print SGML $1 if $1;
    print SGML "</emphasis></term>\n";
    print SGML "<listitem>\n";
    $needpara = 1;  # need a <para></para> soon...
    $listitemActive = 1;
  }

  print SGML "\n";
}

#
# process_over - process a pod over tag and start a corresponding SGML
# list.
#
sub process_over {
    # look whether we are in a nested list
    if ($listlevel) {
      print SGML "<!-- nested at level $listlevel -->\n";
#      push( @listend,  "</listitem> <!-- nested at level $listlevel -->\n" );

    }
    # start a new list

    $listlevel++;
    $listitemActive = 0;
}

#
# process_back - process a pod back tag and convert it to SGML format.
#
sub process_back {
    warn "$0: $podfile: unexpected =back directive in paragraph $paragraph.  ignoring.\n"
    unless $listlevel;
    return unless $listlevel;

    # close off the list.  note, I check to see if $listend[$listlevel] is
    # defined because an =item directive may have never appeared and thus
    # $listend[$listlevel] may have never been initialized.
    $listlevel--;

    print_para_if_needed();
    print SGML $listend[$listlevel] if defined $listend[$listlevel];
    print SGML "\n";

    # don't need the corresponding perl code anymore
    pop(@listitem);
    pop(@listdata);
    pop(@listend);

    pop(@items_seen);

    # If we were inside a nested list, we need to close its <listitem>
    $listitemActive = ($listlevel > 0);
}

#
# process_cut - process a pod cut tag, thus stop ignoring pod directives.
#
sub process_cut {
    $ignore = 1;
}

#
# process_pod - process a pod pod tag, thus ignore pod directives until we see a
# corresponding cut.
#
sub process_pod {
    # no need to set $ignore to 0 cause the main loop did it
}

#
# process_for - process a =for pod tag.  if it's for (pod2)docbook or
# sgml, split it out verbatim, otherwise ignore it.
#
sub process_for {
    my($whom, $text) = @_;

    print_para_if_needed();
    if ( $whom =~ /^(pod2)?docbook|sgml$/i) {
    print SGML $text;
    } 
}

#
# process_begin - process a =begin pod tag.  this pushes
# whom we're beginning on the begin stack.  if there's a
# begin stack, we only print if it us.
#
sub process_begin {
    my ( $whom, $text ) = @_;

    print_para_if_needed();

    $whom = lc( $whom );
    push ( @begin_stack, $whom );
    if ( $whom =~ /^(pod2)?docbook|sgml$/) {
#        print STDERR "Dumping raw SGML: $text\n";
        print SGML $text if $text;
      } else {
#        print STDERR "Begin tag, but not dumping\n";
      }
  }

#
# process_end - process a =end pod tag.  pop the
# begin stack.  die if we're mismatched.
#
sub process_end {
    my($whom, $text) = @_;
    $whom = lc($whom);
    if ($begin_stack[-1] ne $whom ) {
    die "Unmatched begin/end at chunk $paragraph\n"
    } 
    pop @begin_stack;
}

#
# process_text - handles plaintext that appears in the input pod file.
# there may be pod commands embedded within the text so those must be
# converted to docbook commands.
#
sub process_text {
    my($text, $escapeQuotes) = @_;
    my($result, $rest, $s1, $s2, $s3, $s4, $match, $bf);
    my($podcommand, $params, $tag, $quote);

    return if $ignore;

    $quote  = 0;                # status of double-quote conversion
    $result = "";
    $rest = $$text;

    $rest =~ s/\n+$//;    # cut of trailing paragraph separators

    if ($rest =~ /^\s+/) {    # preformatted text, no pod directives
      $rest =~ s/\n+\Z//;
      $rest =~ s#.*#
        my $line = $&;
      1 while $line =~ s/\t+/' ' x (length($&) * 8 - length($`) % 8)/e;
      $line;
      #eg;

      $rest   =~ s/&/&amp;/g;
      $rest   =~ s/</&lt;/g;
      $rest   =~ s/>/&gt;/g;
      #    $rest   =~ s/"/&quot;/g;

      # no special "perl" links are recognized. Hey, they'd have to be
      # defined inside the SGML doc to be of any use... use L<> if you
      # really need these.

      my $urls = '(' . join ('|', qw{
				     http
				     telnet
				     mailto
				     news
				     gopher
				     file
				     wais
				     ftp
				    } )
        . ')';

      my $ltrs = '\w';
      my $gunk = '/#~:.?+=&%@!\-';
      my $punc = '.:?\-';
      my $any  = "${ltrs}${gunk}${punc}";

      $rest =~ s{
		 \b		# start at word boundary
		 (		# begin $1  {
		  $urls     :	# need resource and a colon
		  [$any] +?	# followed by one or more
                                #  of any valid character, but
		                #  be conservative and take only
		                #  what you need to....
		 )		# end   $1  }
		 (?=		# look-ahead non-consumptive assertion
		  [$punc]*	# either 0 or more puntuation
		  [^$any]	#   followed by a non-url char
		  |		# or else
		  $		#   then end of the string
		 )
		}{$1}igox;

      $result =   "<screen>\n"	# text should be as it is (verbatim)
	. "$rest\n"
          . "</screen>\n\n";
    } else {			# formatted text
      # parse through the string, stopping each time we find a
      # pod-escape.  once the string has been throughly processed
      # we can output it.
      while ( length $rest) {
        # check to see if there are any possible pod directives in
        # the remaining part of the text.
        if ($rest =~ m/[BCEIFLSZ]</) {
	  warn "\$rest\t= $rest\n" unless
            $rest =~ /\A
	      ([^<]*?)
		([BCEIFLSZ]?)
		  <
		    (.*)\Z/xs;

	  $s1 = $1;		# pure text
	  $s2 = $2;		# the type of pod-escape that follows
	  $s3 = '<';		# '<'
	  $s4 = $3;		# the rest of the string
        } else {
	  $s1 = $rest;
	  $s2 = "";
	  $s3 = "";
	  $s4 = "";
        }

        if ($s3 eq '<' && $s2) { # a pod-escape
	  $result    .= ($escapeQuotes ? process_puretext($s1, \$quote) : $s1);
	  $podcommand = "$s2<";
	  $rest       = $s4;

	  # find the matching '>'
	  $match = 1;
	  $bf = 0;
	  while ($match && !$bf) {
            $bf = 1;
            if ($rest =~ /\A([^<>]*[BCEIFLSZ]<)(.*)\Z/s) {
	      $bf = 0;
	      $match++;
	      $podcommand .= $1;
	      $rest        = $2;
            } elsif ($rest =~ /\A([^>]*>)(.*)\Z/s) {
	      $bf = 0;
	      $match--;
	      $podcommand .= $1;
	      $rest        = $2;
            }
	  }

	  if ($match != 0) {
            warn <<WARN;
$0: $podfile: cannot find matching > for $s2 in paragraph $paragraph.
WARN
		$result .= substr $podcommand, 0, 2;
            $rest = substr($podcommand, 2) . $rest;
            next;
	  }

	  # pull out the parameters to the pod-escape
	  $podcommand =~ /^([BCFEILSZ]?)<(.*)>$/s;
	  $tag    = $1;
	  $params = $2;

	  # process the text within the pod-escape so that any escapes
	  # which must occur do.
	  process_text(\$params, 0) unless $tag eq 'L';

	  $s1 = $params;
	  if (!$tag || $tag eq " ") { #  <> : no tag
            $s1 = "&lt;$params&gt;";
	  } elsif ($tag eq "L") { # L<> : link 
            $s1 = process_L($params);
	  } elsif ($tag eq "I" || # I<> : italicize text
		   $tag eq "B" || # B<> : bold text
		   $tag eq "F") { # F<> : file specification
            $s1 = process_BFI($tag, $params);
	  } elsif ($tag eq "C") { # C<> : literal code
            $s1 = process_C($params, 1);
	  } elsif ($tag eq "E") { # E<> : escape
            $s1 = process_E($params);
	  } elsif ($tag eq "Z") { # Z<> : zero-width character
            $s1 = process_Z($params);
	  } elsif ($tag eq "S") { # S<> : non-breaking space
            $s1 = process_S($params);
	  } elsif ($tag eq "X") { # S<> : non-breaking space
            $s1 = process_X($params);
	  } else {
            warn "$0: $podfile: unhandled tag '$tag' in paragraph $paragraph\n";
	  }

	  $result .= "$s1";
        } else {
	  # for pure text we must deal with implicit links and
	  # double-quotes among other things.
	  $result .= ($escapeQuotes ? process_puretext("$s1$s2$s3", \$quote) : "$s1$s2$s3");
	  $rest    = $s4;
        }
      }
    }
    $$text = $result;
}

sub html_escape {
    my $rest = $_[0];
    $rest   =~ s/&/&amp;/g;
    $rest   =~ s/</&lt;/g;
    $rest   =~ s/>/&gt;/g;
#    $rest   =~ s/"/&quot;/g;
    return $rest;
} 

#
# process_puretext - process pure text (without pod-escapes) converting
#  double-quotes and handling implicit C<> links.
#
sub process_puretext {
    my($text, $quote) = @_;
    my(@words, $result, $rest, $lead, $trail);

    # convert double-quotes to single-quotes
    $text =~ s/\A([^"]*)"/$1''/s if $$quote;
    while ($text =~ s/\A([^"]*)["]([^"]*)["]/$1``$2''/sg) {}

    $$quote = ($text =~ m/"/ ? 1 : 0); #" (cperl-mode needs this..)
    $text =~ s/\A([^"]*)"/$1``/s if $$quote;

    # keep track of leading and trailing white-space
    $lead  = ($text =~ /\A(\s*)/s ? $1 : "");
    $trail = ($text =~ /(\s*)\Z/s ? $1 : "");

    # collapse all white space into a single space
    $text =~ s/\s+/ /g;
    @words = split(" ", $text);

    # process each word individually
    foreach my $word (@words) {
    # see if we can infer a link
    if ($word =~ /^\w+\(/) {
        # has parenthesis so should have been a C<> ref
        $word = process_C($word);
    } elsif ($word =~ /^[\$\@%&*]+\w+$/) {
        # perl variables, should be a C<> ref
        $word = process_C($word, 1);
    } else { 
        $word = html_escape($word) if $word =~ /[&<>]/;
    }
    }

    # build a new string based upon our conversion
    $result = "";
    $rest   = join(" ", @words);
    while (length($rest) > 75) {
    if ( $rest =~ m/^(.{0,75})\s(.*?)$/o ||
         $rest =~ m/^(\S*)\s(.*?)$/o) {

        $result .= "$1\n";
        $rest    = $2;
    } else {
        $result .= "$rest\n";
        $rest    = "";
    }
    }
    $result .= $rest if $rest;

    # restore the leading and trailing white-space
    $result = "$lead$result$trail";

    return $result;
}

#
# pre_escape - convert & in text to $amp;
#
sub pre_escape {
    my($str) = @_;

    $$str =~ s,&,&amp;,g;
}

#
# process_L - convert a pod L<> directive to a corresponding SGML
# link. Since SGML won't do references across file
# borders, guessing a filename somewhere else is pretty in vain.
#
# Unlike the other directives, this should be called with an unprocessed
# string, else tags in the link won't be matched.
#
sub process_L {
  my($str) = @_;
  my($s1, $s2, $page, $section); # work strings
  my $linktext; # the textual representation for the link
  my $link;     # the referenced Id

  for ($str) {
    s/\n/ /g;		# undo word-wrapped tags

    # check for explicit linktext
    if (m,(.*)\|(.*),) {
      $linktext = $1;
      $_ = $2;
    }
    # make sure sections start with a /
    s,^",/",g;
    s,^,/,g if (!m,/, && / /);

    # check if there's a section specified
    if (m,^(.*?)/"?(.*?)"?$,) {	# yes
      ($page, $section) = ($1, $2);
    } else {			# no
      ($page, $section) = ($str, "");
    }

    # check if the "page" is rather  a section in this page
    if (defined $sections{sgmlify($page)} or
	defined $items{sgmlify($page)}) {
      $section = $page;
      $page = "";
    }
  }

  if (!$page) {
    # some kind of LOCAL reference
    $link = sgmlify($section);
    if ($sections{$link} ||
	$items{$link}) {
      $link = "$rootId-$link";
      $linktext = $section unless defined($linktext);
    } else {
      warn "$0: $podfile: cannot resolve L<$str> in paragraph $paragraph: no such (local) section or item '$section')\n";
    }
  } else {
    # anything else can't be checked right now.
    my $otherroot = sgmlify($page);
    if ($section) {
      $link = $otherroot."-".sgmlify($section);
      $linktext =  $section unless defined($linktext);
    } else {
      $link = "$otherroot";
      $linktext = "the $page manpage" unless defined($linktext); # yuck.
    }
  }

  process_text(\$linktext, 0);
  $s1 = "<link linkend=\"$link\">$linktext</link>";
  return $s1;
}

#
# process_BFI - process any of the B<>, F<>, or I<> pod-escapes and
# convert them to corresponding docbook directives.  Trouble is that
# DocBook has no explicit visual markups. So we use <emphhasis> with
# different roles for both B<> and I<>.
#

sub process_BFI {
    my($tag, $str) = @_;
    my($s1);            # work string
    my(%repltext) = (
        'B' => "<emphasis role=\"bold\">$str</emphasis>",
        'F' => "<filename>$str</filename>",
        'I' => "<emphasis role=\"italic\">$str</emphasis>"
      );

    # extract the modified text and convert to docbook
    $s1 = $repltext{$tag};
    return $s1;
}

#
# process_C - process the C<> pod-escape.
# This is supposed to contain CODE. Somehow it is being used in Pod::HTML for
# referencing items as well?
#
sub process_C {
    my($str, $doref) = @_;
    my($s1, $s2);

    $s1 = $str;
    $s1 =~ s/\([^()]*\)//g;    # delete parentheses
    $s2 = $s1;
    $s1 =~ s/\W//g;        # delete bogus characters

    $s1 = "<literal role=\"code\">$str</literal>";

    return $s1;
}

#
# process_E - process the E<> pod directive which seems to escape a character.
#
sub process_E {
    my($str) = @_;

    for ($str) {
    s,([^/].*),\&$1\;,g;
    }

    return $str;
}

#
# process_Z - process the Z<> pod directive which really just amounts to
# ignoring it.  this allows someone to start a paragraph with an =
#
sub process_Z {
    my($str) = @_;

    # there is no equivalent in SGML for this so just ignore it.
    $str = "";
    return $str;
}

#
# process_S - process the S<> pod directive which means to convert all
# spaces in the string to non-breaking spaces (in SGML/HTML-eze).
#
sub process_S {
    my($str) = @_;

    # convert all spaces in the text to non-breaking spaces in SGML.
    $str =~ s/ /&nbsp;/g;
    return $str;
}

#
# process_X - this is supposed to make an index entry.  we'll just 
# ignore it.
#
sub process_X {
    return '';
}


#
# finish_list - finish off any pending SGML lists.  this should be called
# after the entire pod file has been read and converted.
#
sub finish_list {
  print_para_if_needed();
  while ($listlevel >= 0) {
    #    print SGML "</DL>\n";
    $listlevel--;
  }
}

#
# find_id find a suitable Id for this section/item/whatever. This Id
# should already be in the index hash.
#
sub find_id {
  my ($heading, $index) = @_;
  my $tryId = sgmlify($heading);
    if ($$index{$tryId} ne $heading) {
      # some kind of collision ocurred... find the real Id for the
      # section/item
      $tryId = undef;
    IDLOOP:
      for my $otherid (keys(%$index)) {
	if ($heading eq $$index{$otherid}) {
	  $tryId = $otherid;
	  last IDLOOP;
	}
      }
      die "$0: can't find Id for section/item '$heading' after collision"
	unless $tryId;
    }
  return $tryId;
}


#
# sgmlify - converts a pod section specification to a suitable section
# specification for SGML.
#
sub sgmlify {
  my ($heading) = @_;
  $heading = lc($heading);
  $heading =~ s/[^\w]/-/g;
  $heading =~ s/[_-]+/-/g;
  $heading = substr($heading, 0, 16).".." if (length($heading) > 16);
  return $heading;
}


sub print_para_if_needed () {
  if ($needpara) {
    print SGML <<"EOSGML";

<!-- Bogus hack to ensure that each sect has a paragraph in it -->
<para></para>

EOSGML
  $needpara = 0;
  }
}


BEGIN {
}

1;


