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
$VERSION = '0.05';

use Carp;

use strict;

=head1 NAME

Pod::DocBook - module to convert pod files to DocBook SGML

=head1 SYNOPSIS

    use Pod::DocBook;
    pod2docbook( [options] );

=head1 DESCRIPTION

Converts files from pod format ( see L<perlpod> ) to DocBook format.  It
can automatically generate indexes and cross-references, and it keeps
a cache of things it knows how to cross-reference.

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

Specify the HTML file to create.  Output goes to STDOUT if no outfile
is specified.

=item title

    --title=title

Specify the title of the resulting HTML file.

=item no-header

    --no-header

Doesn't write a default header out for the DTD.

=item no-footer

    --no-footer

Doesn't write a default footer out for the DTD.

=item root-id

    --root-id

Specifies the root identifier for the base element used in chapter and section
tags. The default is I<pod2docbook-ch-1>.

=item verbose

    --verbose

Display progress messages.

=back

=head1 EXAMPLE

    pod2docbook( "pod2docbook", "--infile=foo.pod", 
                 "--outfile=/perl/nmanual/foo.sgml" );

=head1 AUTHOR

Alligator Descartes E<lt>descarte@arcana.co.ukE<gt> from the original
L<pod2html> source code by Tom Christiansen, E<lt>tchrist@perl.comE<gt>,
for it is he. Many thanks to Chris Maden of O'Reilly & Associations for
doing serious road-testing on this module.

=head1 BUGS

Has trouble with C<> etc in = commands.

=head1 LIMITATIONS

Nested =over/=back lists are not supported within DocBook.

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

my $firstSect1 = 1;

### Setup the section indices...
my @sectIndex = ( 'X', 1, 'a', 1, 'a', 1, 'a' );

my $rootId = "pod2docbook-ch-1";

my @begin_stack = ();        # begin/end stack

my @libpods = ();            # files to search for links from C<> directives
my $htmlroot = "/";            # http-server base directory from which all
                #   relative paths in $podpath stem.
my $sgmlfile = "";        # write to stdout by default
my $podfile = "";        # read from stdin by default
my @podpath = ();        # list of directories containing library pods.
my $podroot = ".";        # filesystem base directory from which all
                #   relative paths in $podpath stem.
my $recurse = 1;        # recurse on subdirectories in $podpath.
my $verbose = 0;        # not verbose by default
my $doindex = 1;               # non-zero if we should generate an index
my $listlevel = 0;        # current list depth
my @listitem = ();        # stack of HTML commands to use when a =item is
                #   encountered.  the top of the stack is the
                #   current list.
my @listdata = ();        # similar to @listitem, but for the text after
                #   an =item
my @listend = ();        # similar to @listitem, but the text to use to
                #   end the list.
my $ignore = 1;            # whether or not to format text.  we don't
                #   format text until we hit our first pod
                #   directive.

my %items_named = ();        # for the multiples of the same item in perlfunc
my @items_seen = ();
my $netscape = 0;        # whether or not to use netscape directives.
my $title;            # title to give the pod(s)
my $top = 1;            # true if we are at the top of the doc.  used
                #   to prevent the first <HR> directive.
my $paragraph;            # which paragraph we're processing (used
                #   for error messages)
my %pages = ();            # associative array used to find the location
                #   of pages referenced by L<> links.
my %sections = ();        # sections within this page
my %items = ();            # associative array used to find the location
                #   of =item directives referenced by C<> links
sub init_globals {
#$dircache = "pod2docbook-dircache";
#$itemcache = "pod2docbook-itemcache";

@begin_stack = ();        # begin/end stack

@libpods = ();            # files to search for links from C<> directives
$htmlroot = "/";            # http-server base directory from which all
                #   relative paths in $podpath stem.
$sgmlfile = "";        # write to stdout by default
$podfile = "";        # read from stdin by default
@podpath = ();        # list of directories containing library pods.
$podroot = ".";        # filesystem base directory from which all
                #   relative paths in $podpath stem.
$recurse = 1;        # recurse on subdirectories in $podpath.
$verbose = 0;        # not verbose by default
$doindex = 1;               # non-zero if we should generate an index
$listlevel = 0;        # current list depth
@listitem = ();        # stack of HTML commands to use when a =item is
                #   encountered.  the top of the stack is the
                #   current list.
@listdata = ();        # similar to @listitem, but for the text after
                #   an =item
@listend = ();        # similar to @listitem, but the text to use to
                #   end the list.
$ignore = 1;            # whether or not to format text.  we don't
                #   format text until we hit our first pod
                #   directive.

@items_seen = ();
%items_named = ();
$netscape = 0;        # whether or not to use netscape directives.
$title = '';            # title to give the pod(s)
$top = 1;            # true if we are at the top of the doc.  used
                #   to prevent the first <HR> directive.
$paragraph = '';            # which paragraph we're processing (used
                #   for error messages)
%sections = ();        # sections within this page

# These are not reinitialised here but are kept as a cache.
# See get_cache and related cache management code.
#%pages = ();            # associative array used to find the location
                #   of pages referenced by L<> links.
#%items = ();            # associative array used to find the location
                #   of =item directives referenced by C<> links
}

sub pod2docbook {
    local(@ARGV) = @_;
    local($/);
    local $_;

    init_globals();

    # cache of %pages and %items from last time we ran pod2docbook

    #undef $opt_help if defined $opt_help;

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
    $htmlroot = "" if $htmlroot eq "/";    # so we don't get a //

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

    # open the output file
    open( SGML, ">$sgmlfile")
        || die "$0: cannot open $sgmlfile file for output: $!\n";

    # put a title in the HTML file
    $title = '';
    TITLE_SEARCH: {
    for (my $i = 0; $i < @poddata; $i++) { 
        if ($poddata[$i] =~ /^=head1\s*NAME\b/m) {
        for my $para ( @poddata[$i, $i+1] ) { 
            last TITLE_SEARCH if ($title) = $para =~ /(\S+\s+-+\s*.*)/s;
        }
        } 

    } 
    } 
    if (!$title and $podfile =~ /\.pod$/) {
    # probably a split pod so take first =head[12] as title
    for (my $i = 0; $i < @poddata; $i++) { 
        last if ($title) = $poddata[$i] =~ /^=head[12]\s*(.*)/;
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

    if ( $noheader == 0 ) {
        print SGML <<END_OF_HEAD;
<!DOCTYPE book PUBLIC "-//Davenport//DTD DocBook V2.4.1//EN" "/opt/texmf/gmat/sgml/Davenport/dtds/2.4.1/docbook.dtd">
<!-- -->
<!-- \$Id\$ -->
<!-- -->
<!-- \$Log\$ -->
<!-- -->
<!-- General reminders: -->

<book>

<chapter id="$rootId"><title>$title</title>
END_OF_HEAD
      }

    # load/reload/validate/cache %pages and %items
#    get_cache($dircache, $itemcache, \@podpath, $podroot, $recurse);

    # scan the pod for =item directives
    scan_items("", \%items, @poddata);

    # put an index at the top of the file.  note, if $doindex is 0 we
    # still generate an index, but surround it with an html comment.
    # that way some other program can extract it if desired.
    $doindex = 0;
    if ( $doindex ) {
        $index =~ s/--+/-/g;
        print SGML "<sect1 id=\"index\">\n";
        print SGML "<!-- INDEX BEGIN -->\n";
        print SGML "<!--\n" unless $doindex;
        print SGML $index;
        print SGML "-->\n" unless $doindex;
        print SGML "<!-- INDEX END -->\n\n";
        print SGML "</sect1>\n\n";
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
            next if @begin_stack && $begin_stack[-1] ne 'html';

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
        next if @begin_stack && $begin_stack[-1] ne 'html';
        my $text = $_;
        process_text(\$text, 1);
        print SGML "<para>\n$text\n</para>\n\n";
    }
    }

    # finish off any pending directives
    my $popLevel = pop @sectStack;
    while ( defined $popLevel ) {
#        print STDERR "Clearing down stack $popLevel\n";
        print SGML "</sect$popLevel>\n\n";
        $popLevel = pop @sectStack;
      }
    print SGML "</chapter>\n\n";

    if ( $nofooter == 0 ) {
        print SGML <<END_OF_TAIL;

</book>    <!-- End of the book -->
END_OF_TAIL
      }

    # close the html file
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
  --outfile    - filename for the resulting html file (output sent to
                 stdout by default).
  --title      - title that will appear in resulting html file.
  --no-header  - Doesn't write a header out for the SGML file
  --no-footer  - Doesn't write a footer out for the SGML file
  --root-id    - Specifies the root identifier for chapter and section tags
  --verbose    - self-explanatory

END_OF_USAGE

sub parse_command_line {
    my ( $opt_help, $opt_infile, $opt_outfile, 
         $opt_title, $opt_verbose, $opt_header, $opt_footer, $opt_rootId );
    my $result = GetOptions(
                'help'       => \$opt_help,
                'infile=s'   => \$opt_infile,
                'outfile=s'  => \$opt_outfile,
                'title=s'    => \$opt_title,
                'no-header' => \$opt_header,
                'no-footer' => \$opt_footer,
                'root-id=s'   => \$opt_rootId,
                'verbose'    => \$opt_verbose,
               );
    usage("-", "invalid parameters") if not $result;

    usage("-") if defined $opt_help;    # see if the user asked for help
    $opt_help = "";            # just to make -w shut-up.

    $podfile  = $opt_infile if defined $opt_infile;
    $sgmlfile = $opt_outfile if defined $opt_outfile;

    $noheader = 1 if defined $opt_header;
    $nofooter = 1 if defined $opt_footer;

    $rootId = $opt_rootId if defined $opt_rootId;

    $title    = $opt_title if defined $opt_title;
    $verbose  = defined $opt_verbose ? 1 : 0;
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
    #  pointing to each of them.
    foreach my $line (@data) {
    if ($line =~ /^=(head)([1-6])\s+(.*)/) {
        ($tag,$which_head, $title) = ($1,$2,$3);
        chomp($title);
        $$sections{htmlify(0,$title)} = 1;

        if ($which_head > $listdepth) {
        $index .= "\n" . ("\t" x $listdepth) . "<itemizedList>\n";
        } elsif ($which_head < $listdepth) {
        $listdepth--;
        $index .= "\n" . ("\t" x $listdepth) . "</itemizedList>\n";
        }
        $listdepth = $which_head;

        $index .= "\n" . ("\t" x $listdepth) . "<listitem><para>" .
                  process_text( \$title, 0 ) . "</para></listitem>";
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
    my($pod, @poddata) = @_;
    my($i, $item);
    local $_;

    $pod =~ s/\.pod$//;
    $pod .= ".html" if $pod;

    foreach $i (0..$#poddata) {
    $_ = $poddata[$i];

    # remove any formatting instructions
    s,[A-Z]<([^<>]*)>,$1,g;

    # figure out what kind of item it is and get the first word of
    #  it's name.
    if (/^=item\s+(\w*)\s*.*$/s) {
        if ($1 eq "*") {        # bullet list
        /\A=item\s+\*\s*(.*?)\s*\Z/s;
        $item = $1;
        } elsif ($1 =~ /^[0-9]+/) {    # numbered list
        /\A=item\s+[0-9]+\.?(.*?)\s*\Z/s;
        $item = $1;
        } else {
#        /\A=item\s+(.*?)\s*\Z/s;
        /\A=item\s+(\w*)/s;
        $item = $1;
        }

        $items{$item} = "$pod" if $item;
    }
    }
}

#
# process_head - convert a pod head[1-6] tag and convert it to HTML format.
#
sub process_head {
    my($tag, $heading) = @_;
    my $firstword;

    # figure out the level of the =head
    $tag =~ /head([1-6])/;
    my $level = $1;

    # can't have a heading full of spaces and speechmarks and so on
    $firstword = $heading; $firstword =~ s/\s*(\w+)\s.*/$1/;

#    print STDERR "process_head: $level\n";

    ### If a sect is active, close it off...
    my $popLevel = pop @sectStack;
    while ( defined $popLevel && $level <= $popLevel ) {
#        print STDERR "Popping sectStack: $popLevel\t$#sectStack\n";
        print SGML "</sect$popLevel>";
        print SGML "\n\n";
        if ( ( $popLevel ) % 2 == 0 ) {
            $sectIndex[$popLevel+1] = 1;
          } else {
            $sectIndex[$popLevel+1] = 'a';
          }
        $sectIndex[$popLevel]++;
        $popLevel = pop @sectStack;
      }
    if ( defined $popLevel ) {
        push @sectStack, $popLevel;
      }

    ### Convert the heading and print it out.
    my $convert = $heading; process_text(\$convert, 0);
    if ( $firstSect1 == 1 ) {
        print SGML "<chapter id=\"$rootId\"><title>$convert</title>";
        $firstSect1 = 0;
      } else {
        ### Create the section index...
        my $sectionIndex = "";
        for ( my $i = 1 ; $i <= $level ; $i++ ) {
            $sectionIndex .= "$sectIndex[$i]";
            if ( $i < $level ) {
                $sectionIndex .= "-";
              }
          }
        print SGML "<sect$level id=\"$rootId-sect-$sectionIndex\"><title>$convert</title>";

        ### Set the active sect level
        push @sectStack, $level;
        $sectActive = $level;
      }
    print SGML "\n<!-- Bogus hack to ensure that each sect has a paragraph in it -->\n";
    print SGML "<para>\n</para>\n";
    print SGML "\n\n";

#    print STDERR "Sect stack: ";
#    foreach my $stack ( @sectStack ) {
#        print STDERR "$stack ";
#      }
#    print STDERR "\n";
}

#
# process_item - convert a pod item tag and convert it to HTML format.
#
sub process_item {
    my $text = $_[0];
    my($i, $quote, $name);

    my $need_preamble = 0;
    my $this_entry;


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

    # check if this is the first =item after an =over
    $i = $listlevel - 1;
    my $need_new = $listlevel >= @listitem;

    if ( $text =~ /\A\*/ ) {        # bullet-point list
        if ( $listitemActive == 1 ) {
            print SGML "</listitem>\n";
            $listitemActive = 0;
          }
        if ( $need_preamble ) {
            push( @listend,  "</listitem></itemizedList>\n" );
            print SGML "<itemizedList>\n";
          }
        print SGML "<listitem>";
        $text =~ /\A\*\s*(.*)\Z/s;
        $quote = 1;
        #print SGML process_puretext($1, \$quote);
        print SGML "<para>\n";
        print SGML $1;
        print SGML "</para>\n";
        $listitemActive = 1;
      } elsif ($text =~ /\A[0-9#]+/) {    # numbered list
        if ( $listitemActive == 1 ) {
            print SGML "</listitem>\n";
            $listitemActive = 0;
          }
        if ($need_preamble) {
            push( @listend,  "</listitem></orderedlist>\n" );
            print SGML "<orderedList>\n";
          }
        print SGML "<listitem>\n";
        $text =~ /\A[0-9]+\.?(.*)\Z/s;
        $quote = 1;
        #print SGML process_puretext($1, \$quote);
        print SGML "<para>\n";
        print SGML $1 if $1;
        print SGML "</para>\n";
        $listitemActive = 1;
      } else {            # all others
        if ( $listitemActive == 1 ) {
            print SGML "</listitem></varlistentry>\n";
            $listitemActive = 0;
          }
        if ( $need_preamble ) {
            push( @listend,  "</listitem></varlistentry></variablelist>\n" );
            print SGML "<variableList>\n";
          }
        print SGML "<varlistentry><term><emphasis>";
        $quote = 1;
        #print SGML process_puretext($text, \$quote);
#        print SGML "<para>\n";
        print SGML $text;
#        print SGML "</para>\n";
        print SGML "</emphasis></term>\n";
        print SGML "<listitem><para></para>\n";
        $listitemActive = 1;
      }

    print SGML "\n";
  }

#
# process_over - process a pod over tag and start a corresponding HTML
# list.
#
sub process_over {
    # start a new list
    $listlevel++;
}

#
# process_back - process a pod back tag and convert it to HTML format.
#
sub process_back {
    warn "$0: $podfile: unexpected =back directive in paragraph $paragraph.  ignoring.\n"
    unless $listlevel;
    return unless $listlevel;

    # close off the list.  note, I check to see if $listend[$listlevel] is
    # defined because an =item directive may have never appeared and thus
    # $listend[$listlevel] may have never been initialized.
    $listlevel--;
    print SGML $listend[$listlevel] if defined $listend[$listlevel];
    print SGML "\n";

    # don't need the corresponding perl code anymore
    pop(@listitem);
    pop(@listdata);
    pop(@listend);

    pop(@items_seen);

    $listitemActive = 0;
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
# process_for - process a =for pod tag.  if it's for html, split
# it out verbatim, otherwise ignore it.
#
sub process_for {
    my($whom, $text) = @_;
    if ( $whom =~ /^(pod2)?docbook$/i) {
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
    $whom = lc( $whom );
    push ( @begin_stack, $whom );
    if ( $whom =~ /^(pod2)?docbook$/) {
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
# converted to html commands.
#
sub process_text {
    my($text, $escapeQuotes) = @_;
    my($result, $rest, $s1, $s2, $s3, $s4, $match, $bf);
    my($podcommand, $params, $tag, $quote);

    return if $ignore;

    $quote  = 0;                # status of double-quote conversion
    $result = "";
    $rest = $$text;

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

    # try and create links for all occurrences of perl.* within
    # the preformatted text.
    $rest =~ s{
            (\s*)(perl\w+)
          }{
            if (defined $pages{$2}) {    # is a link
            qq($1$2);
            } else {
            "$1$2";
            }
          }xeg;
    $rest =~ s/()([^>:]*:)?([^>:]*)\.pod:([^>:]*:)?/$1$3.html/g;

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
        \b                          # start at word boundary
        (                           # begin $1  {
          $urls     :               # need resource and a colon
          [$any] +?                 # followed by on or more
                                    #  of any valid character, but
                                    #  be conservative and take only
                                    #  what you need to....
        )                           # end   $1  }
        (?=                         # look-ahead non-consumptive assertion
                [$punc]*            # either 0 or more puntuation
                [^$any]             #   followed by a non-url char
            |                       # or else
                $                   #   then end of the string
        )
      }{$1}igox;

    $result =   "<screen>\n"    # text should be as it is (verbatim)
          . "$rest\n"
          . "</screen>\n\n";
    } else {            # formatted text
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

        $s1 = $1;    # pure text
        $s2 = $2;    # the type of pod-escape that follows
        $s3 = '<';    # '<'
        $s4 = $3;    # the rest of the string
        } else {
        $s1 = $rest;
        $s2 = "";
        $s3 = "";
        $s4 = "";
        }

        if ($s3 eq '<' && $s2) {    # a pod-escape
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
        if (!$tag || $tag eq " ") {    #  <> : no tag
            $s1 = "&lt;$params&gt;";
        } elsif ($tag eq "L") {        # L<> : link 
            $s1 = process_L($params);
        } elsif ($tag eq "I" ||        # I<> : italicize text
             $tag eq "B" ||        # B<> : bold text
             $tag eq "F") {        # F<> : file specification
            $s1 = process_BFI($tag, $params);
        } elsif ($tag eq "C") {        # C<> : literal code
            $s1 = process_C($params, 1);
        } elsif ($tag eq "E") {        # E<> : escape
            $s1 = process_E($params);
        } elsif ($tag eq "Z") {        # Z<> : zero-width character
            $s1 = process_Z($params);
        } elsif ($tag eq "S") {        # S<> : non-breaking space
            $s1 = process_S($params);
        } elsif ($tag eq "X") {        # S<> : non-breaking space
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

    $$quote = ($text =~ m/"/ ? 1 : 0);
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
#        $word =~ /^[^()]*]\(/;
#        if (defined $items{$1} && $items{$1}) {
#        $word =   "\n<CODE><A HREF=\"$htmlroot/$items{$1}#item_"
#            . htmlify(0,$word)
#            . "\">$word</A></CODE>";
#        } elsif (defined $items{$word} && $items{$word}) {
#        $word =   "\n<CODE><A HREF=\"$htmlroot/$items{$word}#item_"
#            . htmlify(0,$word)
#            . "\">$word</A></CODE>";
#        } else {
#        $word =   "\n<CODE><A HREF=\"#item_"
#            . htmlify(0,$word)
#            . "\">$word</A></CODE>";
#        }
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
# process_L - convert a pod L<> directive to a corresponding HTML link.
#  most of the links made are inferred rather than known about directly
#  (i.e it's not known whether the =head\d section exists in the target file,
#   or whether a .pod file exists in the case of split files).  however, the
#  guessing usually works.
#
# Unlike the other directives, this should be called with an unprocessed
# string, else tags in the link won't be matched.
#
sub process_L {
    my($str) = @_;
    my($s1, $s2, $linktext, $page, $section, $link);    # work strings

    $str =~ s/\n/ /g;            # undo word-wrapped tags
    $s1 = $str;
    for ($s1) {
    # a :: acts like a /
    s,::,/,;

    # make sure sections start with a /
    s,^",/",g;
    s,^,/,g if (!m,/, && / /);

    # check if there's a section specified
    if (m,^(.*?)/"?(.*?)"?$,) {    # yes
        ($page, $section) = ($1, $2);
    } else {            # no
        ($page, $section) = ($str, "");
    }

    # check if we know that this is a section in this page
    if (!defined $pages{$page} && defined $sections{$page}) {
        $section = $page;
        $page = "";
    }
    }

    if ($page eq "") {
    $link = "#" . htmlify(0,$section);
    $linktext = $section;
    } elsif (!defined $pages{$page}) {
    warn "$0: $podfile: cannot resolve L<$str> in paragraph $paragraph: no such page '$page'\n";
    $link = "";
    $linktext = $page;
    } else {
    $linktext  = ($section ? "$section" : "the $page manpage");
    $section = htmlify(0,$section) if $section ne "";

    # if there is a directory by the name of the page, then assume that an
    # appropriate section will exist in the subdirectory
    if ($section ne "" && $pages{$page} =~ /([^:]*[^(\.pod|\.pm)]):/) {
        $link = "$htmlroot/$1/$section.html";

    # since there is no directory by the name of the page, the section will
    # have to exist within a .html of the same name.  thus, make sure there
    # is a .pod or .pm that might become that .html
    } else {
        $section = "#$section";
        # check if there is a .pod with the page name
        if ($pages{$page} =~ /([^:]*)\.pod:/) {
        $link = "$htmlroot/$1.html$section";
        } elsif ($pages{$page} =~ /([^:]*)\.pm:/) {
        $link = "$htmlroot/$1.html$section";
        } else {
        warn "$0: $podfile: cannot resolve L$str in paragraph $paragraph: ".
                 "no .pod or .pm found\n";
        $link = "";
        $linktext = $section;
        }
    }
    }

    process_text(\$linktext, 0);
    $s1 = "<emphasis>$linktext</emphasis>";
    return $s1;
}

#
# process_BFI - process any of the B<>, F<>, or I<> pod-escapes and
# convert them to corresponding HTML directives.
#
sub process_BFI {
    my($tag, $str) = @_;
    my($s1);            # work string
    my(%repltext) = (
        'B' => 'emphasis',
        'F' => 'emphasis',
        'I' => 'emphasis'
      );

    # extract the modified text and convert to HTML
    $s1 = "<$repltext{$tag}>$str</$repltext{$tag}>";
    return $s1;
}

#
# process_C - process the C<> pod-escape.
#
sub process_C {
    my($str, $doref) = @_;
    my($s1, $s2);

    $s1 = $str;
    $s1 =~ s/\([^()]*\)//g;    # delete parentheses
    $s2 = $s1;
    $s1 =~ s/\W//g;        # delete bogus characters

    # if there was a pod file that we found earlier with an appropriate
    # =item directive, then create a link to that page.
#    if ($doref && defined $items{$s1}) {
#    $s1 = ($items{$s1} ?
#           "<A HREF=\"$htmlroot/$items{$s1}#item_" . htmlify(0,$s2) .  "\">$str</A>" :
#           "<A HREF=\"#item_" . htmlify(0,$s2) .  "\">$str</A>");
#    $s1 =~ s,(perl\w+/(\S+)\.html)#item_\2\b,$1,; 
#    confess "s1 has space: $s1" if $s1 =~ /HREF="[^"]*\s[^"]*"/;
#    } else {
    $s1 = "<literal>$str</literal>";
    # warn "$0: $podfile: cannot resolve C<$str> in paragraph $paragraph\n" if $verbose
#    }

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

    # there is no equivalent in HTML for this so just ignore it.
    $str = "";
    return $str;
}

#
# process_S - process the S<> pod directive which means to convert all
# spaces in the string to non-breaking spaces (in HTML-eze).
#
sub process_S {
    my($str) = @_;

    # convert all spaces in the text to non-breaking spaces in HTML.
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
# finish_list - finish off any pending HTML lists.  this should be called
# after the entire pod file has been read and converted.
#
sub finish_list {
    while ($listlevel >= 0) {
#    print SGML "</DL>\n";
    $listlevel--;
    }
}

#
# htmlify - converts a pod section specification to a suitable section
# specification for HTML.  if first arg is 1, only takes 1st word.
#
sub htmlify {
    my($compact, $heading) = @_;

    if ($compact) {
      $heading =~ /^(\w+)/;
      $heading = $1;
    } 

  # $heading = lc($heading);
  $heading =~ s/[^\w\s]/_/g;
  $heading =~ s/(\s+)/ /g;
  $heading =~ s/^\s*(.*?)\s*$/$1/s;
  $heading =~ s/ /_/g;
  $heading =~ s/\A(.{32}).*\Z/$1/s;
  $heading =~ s/\s+\Z//;
  $heading =~ s/_{2,}/_/g;

  return $heading;
}

BEGIN {
}

1;
