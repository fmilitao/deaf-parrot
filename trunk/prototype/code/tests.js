// Copyright (C) 2013 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

// http://qunitjs.com/cookbook/

QUnit.config.urlConfig.push({
	id:"cache",
	label:"Cache Files",
	tooltip:"Enable Caching of Test Files."
	 });

var cache_examples = !!QUnit.urlParams.cache;
console.debug( 'AJAX Cache: '+cache_examples );

$.ajaxSetup({ cache: cache_examples });

// this cache is different from jQueries since we are just avoiding
// re-fetching the same file multiple times, but on each test we must
// make sure that we are using the most up to date version of that test.
var cache = {};

var fetchCode = function(file) {
	var res = {};
	if( !cache.hasOwnProperty(file) ){
		$.ajax({
			type : 'GET',
			async : false,
			url : file,
			success : function(data) {
				res.data = data;
				cache[file] = data;
			}
		});
	}else{
		res.data = cache[file];
	}
	
	/*
	 * test results, assumed format:
	 * FIRST LINE (interpreter result)
	 * 	//OK VALUE
	 * 	//FAIL ERROR_MESSAGE
	 * SECOND LINE (typechecker result)
	 * 	//OK VALUE
	 * 	//FAIL ERROR_MESSAGE
	 */
	var lines = res.data.split('\n');
	
	// interprester results:
	var i = 0;
	var result_type = lines[i].substr(0,lines[i].indexOf(' '));
	var result = lines[i].substr(lines[i].indexOf(' ')+1);

	res.i_ok = undefined;
	res.i_fail = undefined;
	if( result_type == '//OK')
		res.i_ok = result;
	else if( result_type == '//FAIL')
		res.i_fail = result;
	else
		throw new Error('Unexpected test result: '+result_type+' on '+file);

	// typechecker results:
	i = 1;
	result_type = lines[i].substr(0,lines[i].indexOf(' '));
	result = lines[i].substr(lines[i].indexOf(' ')+1);

	res.t_ok = undefined;
	res.t_fail = undefined;
	if( result_type == '//OK')
		res.t_ok = result;
	else if( result_type == '//FAIL')
		res.t_fail = result;
	else
		throw new Error('Unexpected test result: '+result_type+' on '+file);

	return res;
};

var examples_dir = "examples/tests/";
var examples = [];

// synchronous fetch of test list
$.ajax({
		type : 'GET',
		async : false,
		url : "examples/tests-list",
		success : function(data) {
			examples = data.split('\n');
			var tmp = [];
			for(var i=0;i<examples.length;++i){
				if( examples[i][0] != '#' ) // ignore commented stuff
					tmp.push( examples[i] );
			}
			examples = tmp;
		}
	});

var parser = Parser('code/grammar.jison');
var interpreter = Interpreter.run;
var typechecker = TypeChecker.check;

var ast_cache = {};
var parseCode = function(file,data) {
	if( !ast_cache.hasOwnProperty(file) ){
		var ast = parser( data );
		ast_cache[file] = ast;
		return ast;
	}
	return ast_cache[file];
};

//QUnit.config.reorder = false;

module('Fetch Files');

	test( "Fetches", function() {
		for( var i in examples ){
			var f = fetchCode(examples_dir+examples[i]);
		  	ok( f !== null && f !== undefined , "'"+examples[i]+"' fetched.");
		}
	});

module('Parser');

	test( "Parses", function() {
		for( var i in examples ){
			var test = fetchCode( examples_dir+examples[i] );
			var ast = parseCode( examples[i], test.data ); //parser(test.data);
		  	ok( ast !== null , "'"+examples[i]+"' parsed.");
		}
	});

module('Interpreter');

	test( "Runs", function() {
		for( var i in examples ){
			var test = fetchCode(examples_dir+examples[i]);
			var ast = parseCode( examples[i], test.data ); //parser(test.data);
			if( ast === null ){
				// forced failure due to paserser failur
		  		ok( false , "'"+examples[i]+"' parser failure.");
		  		continue;
		  	}
		  	try{
		  		equal( interpreter( ast ).toString(),
					test.i_ok, "'"+examples[i]+"' result check." );
		  	}catch(e){
		  		equal( e.message,
					test.i_fail, "'"+examples[i]+"' error check." );
		  	}
		}
	});
	


module('Typechecker');

	test( "Checks", function() {
		for( var i in examples ){
			var test = fetchCode(examples_dir+examples[i]);
			var ast = parseCode( examples[i], test.data );; //parser(test.data);
		  	if( ast === null ){
				// forced failure due to paserser failur
		  		ok( false , "'"+examples[i]+"' parser failure.");
		  		continue;
		  	}
		  	try{
		  		equal( typechecker( ast , null , null ).toString(),
					test.t_ok, "'"+examples[i]+"' type check." );
		  	}catch(e){
		  		equal( e.message,
					test.t_fail, "'"+examples[i]+"' error check." );
		  	}
		}
	});
	
/*
test( "hello test", function() {
  ok( 1 == "1", "Passed!" );
  equal( 1, 1, 'one equals one');
  //deepEqual( {a:"asd"}, {a:"Asd"});  
});

test( "subtyping", function() {
  ok( 1 == "1", "Passed!" );
  equal( 1, 1, 'one equals one');
  //deepEqual( {a:"asd"}, {a:"Asd"});  
});

//ok( true , "OK!\nAST:\n"+JSON.stringify(ast,undefined,2) );
*/



