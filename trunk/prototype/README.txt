--------------------------------------------------------------------------------
PROTOTYPE LANGUAGE IMPLEMENTATION ("Dead Parrot")
--------------------------------------------------------------------------------

Javascript prototype implementation of the paper's language.

THIS IS NOT A COMPLETED PROJECT THERE ARE KNOWN BUGS AND MISSING FEATURES

================================================================================
DEVELOPMENT NOTES
================================================================================

1. Minimalistic file server.
   To launch a simple local server (so that AJAX calls work), install 
   node-static ( https://github.com/cloudhead/node-static ):
		npm install -g node-static
   (may need preceding 'sudo') and then run from 'trunk/' directory:
		static

2. Generating static grammar.
   To generate the (static) grammar javascript file you need to install jison 
( http://zaach.github.com/jison/ ) that can also be done through node.js' npm
with the command:
		npm install jison -g
	(may also need preceding 'sudo')
and then calling jison with our grammar to generate the grammar.js file:	
		jison grammar.jison
Then you need to change all parts of the code that include 'jison.js' and link
them to the generated 'grammar.js' and use that 'grammar' var directly.

To facilitate testing this code will use re-generation of the grammar.

================================================================================
LIBRARIES
================================================================================

We use the following libraries, see https://code.google.com/p/dead-parrot/ for
links to their respective sources. The source code includes COPIES of these
libraries for convenience since they were not significantly changed.
[copies of around August 21st, 2012 - should probably update them soon...]

Notes about the two most important libraries used and location of plugin files:

 * jison ( http://zaach.github.com/jison/ )
	The custom rules are in 'grammar.jison' file.
	Library files were fetched from the project's github repo.
	NOTE: jison was modified so that errors use 'this.lexer.yylineno' 
	instead of just 'yylineno' for line number.
	There was a line mismatch with the default variable.

 * ace editor ( http://ace.ajax.org/index.html )
	Custom highlighter mode is in 'mode-grammar.js' and some styles were 
	slightly changed to adjust their look and feel with the particular needs of
	the language, namely make certain tokens clearer to see.
	Library files are based on the project's github 'ace-builds' repo
    (and not the one directly linked from the project's website) and is
    a copy of the 'src-noconflict' folder.

================================================================================
LICENSE
================================================================================

Copyright (C) 2013 Filipe Militao <filipe.militao@cs.cmu.edu>
GPL v3 Licensed http://www.gnu.org/licenses/

