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
	
module('Typechecker.Components');
// FIXME: substitution, equals

	test( "Subtyping", function() {
		
		typechecker( function(exports,subtype,_){
			var t = exports.factory;
			
			var t_none = new t.NoneType();
			var t_int = new t.PrimitiveType('int');
			var t_boolean = new t.PrimitiveType('boolean');
			var t_string = new t.PrimitiveType('string');
			
			// int <: int
			equal( subtype( t_int, t_int ), true );
			equal( subtype( t_string, t_string ), true );
			equal( subtype( t_int, t_string ), false );
			
			// !int <: int
			equal( subtype(new t.BangType( t_int ), t_int ), true );
			equal( subtype(new t.BangType( t_boolean ), t_boolean ), true );
			
			// int <: !int
			equal( subtype( t_int, new t.BangType( t_int )), true );
			equal( subtype( t_string,new t.BangType( t_string )), true );
			
			// int <: none
			equal( subtype( t_int, t_none ), false );
			equal( subtype( t_none, t_int ), false );
			
			// records
			var t_rec1 = new t.RecordType();
			t_rec1.add('a',t_int);
			t_rec1.add('b',t_int);
			
			var t_rec2 = new t.RecordType();
			t_rec2.add('a',t_int);

			equal( subtype( t_rec2, t_rec1 ), false );
			equal( subtype( t_rec1, t_rec2 ), true );
			
			t_rec2.add('b',t_string);
			equal( subtype( t_rec2, t_rec1 ), false );
			equal( subtype( t_rec1, t_rec2 ), false );
			
			// unit
			var t_unit = new t.BangType( new t.RecordType() );
			
			equal( subtype( t_unit, t_none ), false );
			equal( subtype( t_unit, t_int ), false );
			equal( subtype( t_rec1, t_unit ), false );
			equal( subtype(new t.BangType(t_int), t_unit ), true );
			equal( subtype(new t.BangType(t_string), t_unit ), true );

			// basic references
			var t_ref1 = new t.ReferenceType( new t.LocationVariable('p'));
			var t_ref2 = new t.ReferenceType( new t.LocationVariable('p'));
			var t_ref3 = new t.ReferenceType( new t.LocationVariable('q'));
			
			equal( subtype( t_ref1, t_ref1 ), true );
			equal( subtype( t_ref2, t_ref1 ), true );
			equal( subtype( t_ref1, t_ref2 ), true );
			equal( subtype( t_ref1, t_ref3 ), false );
			equal( subtype( t_ref3, t_ref2 ), false );
			
			// function type
			var t_fun1 = new t.FunctionType( t_int, t_boolean );
			var t_fun2 = new t.FunctionType( t_boolean, t_int );
			equal( subtype( t_fun1, t_fun2 ), false );
			equal( subtype( t_fun2, t_fun1 ), false );
			
			t_fun1 = new t.FunctionType( new t.BangType(t_int), t_boolean );
			t_fun2 = new t.FunctionType( t_int, t_boolean );
			equal( subtype( t_fun1, t_fun2 ), true );
			equal( subtype( t_fun2, t_fun1 ), true );
			
			// contra-variant
			t_fun1 = new t.FunctionType( new t.BangType(t_rec1), t_boolean ); // ![] -o boolean
			t_fun2 = new t.FunctionType( t_rec1, t_boolean ); // [] -o boolean
			equal( subtype( t_fun1, t_fun2 ), false );
			equal( subtype( t_fun2, t_fun1 ), true );
			
			// co-variant
			t_fun1 = new t.FunctionType( t_int, new t.BangType(t_rec1) );
			t_fun2 = new t.FunctionType( t_int, t_rec1 );
			equal( subtype( t_fun1, t_fun2 ), true );
			equal( subtype( t_fun2, t_fun1 ), false );
			
			// tuples
			var t_tuple1 = new t.TupleType();
			var t_tuple2 = new t.TupleType();
			equal( subtype( t_tuple1, t_tuple2 ), true );
			
			t_tuple1.add( t_int );
			equal( subtype( t_tuple1, t_tuple2 ), false );
			equal( subtype( t_tuple2, t_tuple1 ), false );
			
			t_tuple2.add( t_int );
			t_tuple2.add( t_boolean );
			equal( subtype( t_tuple1, t_tuple2 ), false );
			equal( subtype( t_tuple2, t_tuple1 ), false );
			
			// sums
			var t_sum1 = new t.SumType();
			var t_sum2 = new t.SumType();
			equal( subtype( t_sum1, t_sum2 ), true );
			
			t_sum1.add('a',t_int);
			t_sum2.add('a',t_int);
			equal( subtype( t_sum1, t_sum2 ), true );
			
			t_sum2.add('b',t_int);
			equal( subtype( t_sum2, t_sum1 ), false );
			equal( subtype( t_sum1, t_sum2 ), true );
			
			// var capabilities
			var t_cap1 = new t.CapabilityType(new t.LocationVariable('p'),t_int);
			var t_cap2 = new t.CapabilityType(new t.LocationVariable('p'),t_int);
			equal( subtype( t_cap1, t_cap2 ), true );
			equal( subtype( t_cap2, t_cap1 ), true );
			
			t_cap1 = new t.CapabilityType(new t.LocationVariable('p'), t_sum1 );
			t_cap2 = new t.CapabilityType(new t.LocationVariable('p'), t_sum2 );
			equal( subtype( t_cap1, t_cap2 ), true );
			equal( subtype( t_cap2, t_cap1 ), false );
			
			// stacked type
			var t_s1 = new t.StackedType( t_int, t_boolean );
			var t_s2 = new t.StackedType( t_boolean, t_int );
			equal( subtype( t_s1, t_s1 ), true );
			equal( subtype( t_s2, t_s2 ), true );
			equal( subtype( t_s1, t_s2 ), false );
			equal( subtype( t_s2, t_s1 ), false );
			
			
			// FIXME type variable and location variables
			// FIXME forall, exists, delayed app, recursive types
			// FIXME alternative type, star type
			// FIXME rely type, guarantee type
			
		} );
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



