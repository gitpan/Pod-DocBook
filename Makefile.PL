###
### Makefile.PL
### 
### Meta-Makefile for pod2docbook
###

BEGIN { require 5.003 }

use ExtUtils::MakeMaker 5.16, qw(WriteMakefile $Verbose);
use Config;

%opts = (
	'NAME'=> 'Pod::DocBook',
	'VERSION_FROM' => 'DocBook.pm',
	'EXE_FILES' => [ 'pod2docbook' ],
	'dist' => { 'COMPRESS' => 'gzip -v -9 -f', 'SUFFIX' => '.gz' },
  );

warn <<EOM;

EOM

WriteMakefile( %opts );

warn <<EOM;

    To read this module, type:

        make install

    and if this is successful, read the instructions by typing:

        perldoc pod2docbook

    A small test POD file called ``test.pod'' is located within the pod
    sub-directory and contains most POD tags. This can be used to test the
    correctness of your SGML output.

EOM

exit;

__END__
