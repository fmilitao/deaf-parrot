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
	
	test( "Equals", function() {
		typechecker( function(exports,_,equals){
			var t = exports.factory;
		
			var t_none = new t.NoneType();
			var t_int = new t.PrimitiveType('int');
			var t_boolean = new t.PrimitiveType('boolean');
			var t_string = new t.PrimitiveType('string');
		
			equal( equals( t_int, t_int ), true );
			equal( equals( t_string, t_string ), true );
			equal( equals( t_int, t_string ), false );
			equal( equals(new t.BangType( t_int ), t_int ), false );
			equal( equals(new t.BangType( t_boolean ), t_boolean ), false );
			equal( equals( t_int, t_none ), false );
			equal( equals( t_none, t_int ), false );

			var t_rec1 = new t.RecordType();
			t_rec1.add('a',t_int);
			t_rec1.add('b',t_int);
			
			var t_rec2 = new t.RecordType();
			t_rec2.add('a',t_int);

			equal( equals( t_rec2, t_rec1 ), false );
			equal( equals( t_rec1, t_rec2 ), false );
			
			t_rec2.add('b',t_int);
			equal( equals( t_rec2, t_rec1 ), true );
			equal( equals( t_rec1, t_rec2 ), true );
			
			// unit
			var t_unit = new t.BangType( new t.RecordType() );
			
			equal( equals( t_unit, t_none ), false );
			equal( equals( t_unit, t_int ), false );
			equal( equals( t_rec1, t_unit ), false );

			// basic references
			var t_ref1 = new t.ReferenceType( new t.LocationVariable('p'));
			var t_ref2 = new t.ReferenceType( new t.LocationVariable('p'));
			var t_ref3 = new t.ReferenceType( new t.LocationVariable('q'));
			
			equal( equals( t_ref1, t_ref1 ), true );
			equal( equals( t_ref2, t_ref1 ), true );
			equal( equals( t_ref1, t_ref2 ), true );
			equal( equals( t_ref1, t_ref3 ), false );
			equal( equals( t_ref3, t_ref2 ), false );
			
			// function type
			var t_fun1 = new t.FunctionType( t_int, t_boolean );
			var t_fun2 = new t.FunctionType( t_boolean, t_int );
			equal( equals( t_fun1, t_fun2 ), false );
			equal( equals( t_fun2, t_fun1 ), false );
			
			t_fun1 = new t.FunctionType( t_int, t_boolean );
			t_fun2 = new t.FunctionType( t_int, t_boolean );
			equal( equals( t_fun1, t_fun2 ), true );
			equal( equals( t_fun2, t_fun1 ), true );
			
			// tuples
			var t_tuple1 = new t.TupleType();
			var t_tuple2 = new t.TupleType();
			equal( equals( t_tuple1, t_tuple2 ), true );
			
			t_tuple1.add( t_int );
			equal( equals( t_tuple1, t_tuple2 ), false );
			equal( equals( t_tuple2, t_tuple1 ), false );
			
			t_tuple2.add( t_int );
			t_tuple2.add( t_boolean );
			equal( equals( t_tuple1, t_tuple2 ), false );
			equal( equals( t_tuple2, t_tuple1 ), false );
			
			// sums
			var t_sum1 = new t.SumType();
			var t_sum2 = new t.SumType();
			equal( equals( t_sum1, t_sum2 ), true );
			
			t_sum1.add('a',t_int);
			t_sum2.add('a',t_int);
			equal( equals( t_sum1, t_sum2 ), true );
			
			t_sum2.add('b',t_int);
			equal( equals( t_sum2, t_sum1 ), false );
			equal( equals( t_sum1, t_sum2 ), false );
			
			// var capabilities
			var t_cap1 = new t.CapabilityType(new t.LocationVariable('p'),t_int);
			var t_cap2 = new t.CapabilityType(new t.LocationVariable('p'),t_int);
			equal( equals( t_cap1, t_cap2 ), true );
			equal( equals( t_cap2, t_cap1 ), true );
			
			t_cap1 = new t.CapabilityType(new t.LocationVariable('p'), t_sum1 );
			t_cap2 = new t.CapabilityType(new t.LocationVariable('p'), t_sum2 );
			equal( equals( t_cap1, t_cap2 ), false );
			equal( equals( t_cap2, t_cap1 ), false );
			
			// stacked type
			var t_s1 = new t.StackedType( t_int, t_boolean );
			var t_s2 = new t.StackedType( t_boolean, t_int );
			equal( equals( t_s1, t_s1 ), true );
			equal( equals( t_s2, t_s2 ), true );
			equal( equals( t_s1, t_s2 ), false );
			equal( equals( t_s2, t_s1 ), false );
			
			// location variables
			var t_loc1 = new t.LocationVariable('q');
			var t_loc2 = new t.LocationVariable('p');
			var t_loc3 = new t.LocationVariable('q');
			equal( equals( t_loc1, t_loc2 ), false );
			equal( equals( t_loc2, t_loc1 ), false );
			equal( equals( t_loc1, t_loc3 ), true );
			
			// star type
			var t_star1 = new t.StarType();
			var t_star2 = new t.StarType();
			
			equal( equals( t_star2, t_star1 ), true );
			equal( equals( t_star1, t_star2 ), true );
			
			t_star1.add( t_int );
			t_star1.add( t_boolean );
			t_star1.add( t_string );
			t_star2.add( t_string );
			t_star2.add( t_int );
			t_star2.add( t_boolean );
			equal( equals( t_star2, t_star1 ), true );
			equal( equals( t_star1, t_star2 ), true );
			
			t_star2.add( t_int );
			equal( equals( t_star2, t_star1 ), false );
			equal( equals( t_star1, t_star2 ), false );
			
			var t_rely1 = new t.RelyType( t_int, t_boolean );
			var t_rely2 = new t.RelyType( t_int, t_string );
			var t_rely3 = new t.RelyType( t_int, t_boolean );
			equal( equals( t_rely2, t_rely1 ), false );
			equal( equals( t_rely1, t_rely2 ), false );
			equal( equals( t_rely1, t_rely3 ), true );
			
			var t_g1 = new t.GuaranteeType( t_int, t_boolean );
			var t_g2 = new t.GuaranteeType( t_int, t_string );
			var t_g3 = new t.GuaranteeType( t_int, t_boolean );
			equal( equals( t_g2, t_g1 ), false );
			equal( equals( t_g1, t_g2 ), false );
			equal( equals( t_g1, t_g3 ), true );
			
			// 'unbounded' type variables
			var t_var1 = new t.TypeVariable('X');
			var t_var2 = new t.TypeVariable('X');
			var t_var3 = new t.TypeVariable('Y');
			equal( equals( t_var1, t_var2 ), true );
			equal( equals( t_var2, t_var3 ), false );			
			equal( equals( t_var3, t_var2 ), false );
			
			// forall and exists
			var t_f1 = new t.ForallType(new t.TypeVariable('X'),new t.TypeVariable('X'));
			var t_f2 = new t.ForallType(new t.TypeVariable('Y'),new t.TypeVariable('Y'));
			var t_f3 = new t.ForallType(new t.TypeVariable('Z'),new t.BangType(new t.TypeVariable('Z')));
			equal( equals( t_f1, t_f2 ), true );
			equal( equals( t_f1, t_f3 ), false );
			equal( equals( t_f3, t_f1 ), false );
			
			var t_e1 = new t.ExistsType(new t.TypeVariable('X'),new t.TypeVariable('X'));
			var t_e2 = new t.ExistsType(new t.TypeVariable('Y'),new t.TypeVariable('Y'));
			var t_e3 = new t.ExistsType(new t.TypeVariable('Z'),new t.BangType(new t.TypeVariable('Z')));
			equal( equals( t_e1, t_e2 ), true );
			equal( equals( t_e1, t_e3 ), false );
			equal( equals( t_e3, t_e1 ), false );
			
			// alternative
			var t_alt1 = new t.AlternativeType();
			var t_alt2 = new t.AlternativeType();
			
			equal( equals( t_alt2, t_alt1 ), true );
			equal( equals( t_alt1, t_alt2 ), true );
			
			t_alt1.add( t_int );
			t_alt1.add( t_boolean );
			t_alt1.add( t_string );
			t_alt2.add( t_string );
			t_alt2.add( t_int );
			t_alt2.add( t_boolean );
			equal( equals( t_alt2, t_alt1 ), true );
			equal( equals( t_alt1, t_alt2 ), true );
			
			t_alt2.add( t_int );
			equal( equals( t_alt2, t_alt1 ), false );
			equal( equals( t_alt1, t_alt2 ), false );
						
			// recursive types
			var t_r1 = new t.RecursiveType(new t.TypeVariable('X'),new t.TypeVariable('X'));
			var t_r2 = new t.RecursiveType(new t.TypeVariable('Y'),new t.TypeVariable('Y'));
			equal( equals( t_r1, t_r2 ), true );
			
			// rec X.(a#int + b#X) === rec Y.( (b#rec Z.(b#Z + a#int)) + a#int )
			var t_tmp1 = new t.SumType();
			t_tmp1.add('a',t_int);
			t_tmp1.add('b',new t.TypeVariable('X'));
			var t_r3 = new t.RecursiveType(new t.TypeVariable('X'),t_tmp1);
			
			var t_tmp2 = new t.SumType();
			t_tmp2.add('b',new t.TypeVariable('Z'));
			t_tmp2.add('a',t_int);
			var t_r4 = new t.RecursiveType(new t.TypeVariable('Z'),t_tmp2);
			
			var t_tmp3 = new t.SumType();
			t_tmp3.add('a',t_int);
			t_tmp3.add('b',t_r4);
			
			equal( equals( t_tmp3, t_r3 ), true );
			equal( equals( t_tmp3, t_r4 ), true );
			equal( equals( t_tmp3, t_tmp2 ), false );

			// FIXME delayed app
		});
	} );

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
			
			// location variables
			var t_loc1 = new t.LocationVariable('q');
			var t_loc2 = new t.LocationVariable('p');
			var t_loc3 = new t.LocationVariable('q');
			equal( subtype( t_loc1, t_loc2 ), false );
			equal( subtype( t_loc2, t_loc1 ), false );
			equal( subtype( t_loc1, t_loc3 ), true );
			
			// star type
			var t_star1 = new t.StarType();
			var t_star2 = new t.StarType();
			
			equal( subtype( t_star2, t_star1 ), true );
			equal( subtype( t_star1, t_star2 ), true );
			
			t_star1.add( t_int );
			t_star1.add( t_boolean );
			t_star1.add( t_string );
			t_star2.add( t_string );
			t_star2.add( t_int );
			t_star2.add( t_boolean );
			equal( subtype( t_star2, t_star1 ), true );
			equal( subtype( t_star1, t_star2 ), true );
			
			t_star2.add( t_int );
			equal( subtype( t_star2, t_star1 ), false );
			equal( subtype( t_star1, t_star2 ), false );
			var t_rely1 = new t.RelyType( t_int, t_boolean );
			var t_rely2 = new t.RelyType( t_int, t_string );
			var t_rely3 = new t.RelyType( t_int, t_boolean );
			equal( subtype( t_rely2, t_rely1 ), false );
			equal( subtype( t_rely1, t_rely2 ), false );
			equal( subtype( t_rely1, t_rely3 ), true );
			
			var t_g1 = new t.GuaranteeType( t_int, t_boolean );
			var t_g2 = new t.GuaranteeType( t_int, t_string );
			var t_g3 = new t.GuaranteeType( t_int, t_boolean );
			equal( subtype( t_g2, t_g1 ), false );
			equal( subtype( t_g1, t_g2 ), false );
			equal( subtype( t_g1, t_g3 ), true );
			
			// 'unbounded' type variables
			var t_var1 = new t.TypeVariable('X');
			var t_var2 = new t.TypeVariable('X');
			var t_var3 = new t.TypeVariable('Y');
			equal( subtype( t_var1, t_var2 ), true );
			equal( subtype( t_var2, t_var3 ), false );			
			equal( subtype( t_var3, t_var2 ), false );
			
			// forall, exists
			// FIXME forall, exists
			// FIXME delayed app, recursive types
			// FIXME alternative type X <: X  (+) Y, etc.
			
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


