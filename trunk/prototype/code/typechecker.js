// Copyright (C) 2013 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/**
 * Notes:
 * 	- syntax direct alternatives using: @p Expression. Later this can be 
 * replaced with just linear search for the correct way to open an (+) type.
 * 
 * REQUIRED Global variables (all declared in parser.js):
 * 	- AST.kinds, for all AST case analysis needs.
 *  - assertf, for error handling/flagging.
 */

var TypeChecker = (function(AST,assertF){

	var exports = {};
	
	/*
	 * WARNING - Usage Notes:
	 * The following two function smake use of a side-effect when evaluating
	 * an OR such that A || B will only compute B if A is NOT true. Therefore
	 * the following functions make use of that assumption on their argument
	 * such that if the argument is true, then the function does nothing, else
	 * it throws the respective error with the argument which should be a string
	 * so that it can be used as:
	 *		assert( CONDITION || EXPENSIVE_ERROR_MSG , AST );
	 * and not compute EXPENSIVE_ERROR_MSG unless CONDITION is false.
	 */
	
	// yields true or string on error
	var assert = function( msg, ast ){
		// if a boolean and true
		if( typeof(msg) === 'boolean' && msg )
			return;
		assertF( 'Type error', false, msg, ast );
	}
	
	// these are program assertions and should never be seen by users
	// unless there is a major malfunction in the code (bug...)
	var error = function(msg){
		// if a boolean and true
		if( typeof(msg) === 'boolean' && msg )
			return;
		// else it should be a string with the type error
		assertF( 'Bug Alert', false, msg, undefined ); // undefined blamed 'ast'
	}

	//
	// TYPES
	//
	
	var types = {}; // types enumeration, useful for case analysis
	var fct = {}; // types factory

	var newType = function( type, constructor ){
		error( ( !types.hasOwnProperty(type) && !fct.hasOwnProperty(type) )
			|| ( '@newType: already exists: '+type ) );
		
		// default stuff for that particular type
		constructor.prototype.type = type;

		// later it may be useful to change away from strings, but for now
		// they are very useful when debugging problems.
		types[type] = type;
		fct[type] = constructor;
		return constructor;
	};
	
	// Note: all constructors are labelled to make heap profiling easier.
	
	var FunctionType = newType('FunctionType',
		function FunctionType( argument, body ) {
			this.argument = function(){ return argument; }
			this.body = function(){ return body; }
		}
	);
	
	var BangType = newType('BangType',
		function BangType( inner ) {
			this.inner = function(){ return inner; }
		}
	);
	
	var SumType = newType('SumType',
		function SumType() {
			var tags = {};
			this.add = function( tag, inner ){
				if ( tags.hasOwnProperty(tag) )
					return undefined; // already exists!
				tags[tag] = inner;
				return true;
			}
			this.tags = function(){ return Object.keys(tags); }
			this.inner = function(tag){ return tags[tag]; }
		}
	);
	
	var StarType = newType('StarType',
		function StarType() {
			var types = [];
			this.add = function( inner ){
				types.push(inner);
				return true;
			}
			this.inner = function(){ return types; }
		}
	);
	
	var AlternativeType = newType('AlternativeType',
		function AlternativeType() {
			var alts = [];
			this.add = function( inner ){
				alts.push(inner);
				return true;
			}
			this.inner = function(){ return alts; }
		}
	);
	
	var ForallType = newType('ForallType',
		function ForallType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	var ExistsType = newType('ExistsType',
		function ExistsType( id, inner ) {
			this.id = function(){ return id; }
			this.inner = function(){ return inner; }
		}
	);
	
	var RecordType = newType('RecordType',
		function RecordType(){
			var fields = {};
			this.add = function(id, type) {
				if ( fields.hasOwnProperty(id) ){
					return undefined;
				}
				fields[id] = type;
				return true;
			}
			this.select = function(id) {
				if (fields.hasOwnProperty(id)) {
					return fields[id];
				} else {
					return undefined;
				}
			}
			this.isEmpty = function(){
				return Object.keys(fields).length===0;
			}
			this.getFields = function(){
				return fields;
			}
		}
	);
	
	var NoneType = newType('NoneType',
		function NoneType(){
			// intentionally empty	
		}
	);
	
	// singleton value for this type.
	NoneType = new NoneType();
	
	var TupleType = newType('TupleType',
		function TupleType(){
			var values = [];
			this.add = function(type) {
				values.push(type);
				return true;
			}
			this.getValues = function(){
				return values;
			}
		}
	);

	var ReferenceType = newType('ReferenceType',
		function ReferenceType( location ){
			this.location = function(){ return location; }
		}
	);
	
	var StackedType = newType('StackedType',
		function StackedType( left, right ){
			this.left = function(){ return left; }
			this.right = function(){ return right; }
		}
	);
	
	var CapabilityType = newType('CapabilityType',
		function CapabilityType( loc, val ){
			this.location = function(){ return loc; }
			this.value = function(){ return val; }
		}
	);
	
	var LocationVariable = newType('LocationVariable',
		function LocationVariable( name ){
			var n = name === null ? 't<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new LocationVariable(n); }
		}
	);
	
	var TypeVariable = newType('TypeVariable',
		function TypeVariable( name ){
			var n = name === null ? 'T<sub>'+(unique_counter++)+'</sub>' : name;
			
			this.name = function(){ return n; }
			this.clone = function( n ){ return new TypeVariable(n); }
		}
	);
	
	var PrimitiveType = newType('PrimitiveType',
		function PrimitiveType( name ){
			this.name = function(){ return name; }
		}
	);
	
	var RelyType = newType('RelyType',
		function RelyType( rely, guarantee ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);
	
	var GuaranteeType = newType('GuaranteeType',
		function GuaranteeType( guarantee, rely ){
			this.rely = function(){ return rely; }
			this.guarantee = function(){ return guarantee; }
		}
	);
	
	var DefinitionType = newType('DefinitionType',
		function DefinitionType( definition_name, arg ){
			this.definition = function(){ return definition_name; }
			this.args = function(){ return arg; }
		}
	);
	
	exports.types = types;
	exports.factory = fct;
	
	// append toString method to types
	(function(){
		// defines which types get wrapping parenthesis
		var _wrap = function(t){
			if( t.type === types.ReferenceType ||
				t.type === types.FunctionType ||
				t.type === types.StackedType ||
				t.type === types.StarType || 
				t.type === types.AlternativeType ||
				t.type === types.SumType ){
					return '('+t.toString()+')';
				}
			return t.toString();
		};
		var _add = function(t,fun){
			error( !fct[t].hasOwnProperty('toString') || ("Duplicated " +k) );
			fct[t].prototype.toString = fun;
		};
		
		_add( types.FunctionType, function(){
			return _wrap( this.argument() )+" -o "+_wrap( this.body() );
		} );
		
		_add( types.BangType, function(){
			return "!"+_wrap( this.inner() );
		} );

		_add( types.RelyType, function(){
			return _wrap( this.rely() )+' => '+_wrap( this.guarantee() );
		} );

		_add( types.GuaranteeType, function(){
			return _wrap( this.guarantee() )+' ; '+_wrap( this.rely() );
		} );
		
		_add( types.SumType, function(){
			var tags = this.tags();
			var res = [];
			for( var i in tags ){
				res.push( tags[i]+'#'+_wrap( this.inner(tags[i]) ) ); 
			}	
			return res.join('+');
		} );

		_add( types.StarType, function(){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i] ) ); 
			return res.join(' * ');
		} );
		
		_add( types.AlternativeType, function(){
			var inners = this.inner();
			var res = [];
			for( var i=0; i<inners.length; ++i )
				res.push( _wrap( inners[i] ) ); 
			return res.join(' (+) ');
		} );
		
		_add( types.ExistsType, function(){
			return 'exists '+this.id().name()+'.'+_wrap( this.inner() );
		} );
		
		_add( types.ForallType, function(){
			return 'forall '+this.id().name()+'.('+_wrap( this.inner() );
		} );
		
		_add( types.ReferenceType, function(){
			return "ref "+this.location().name();
		} );
		
		_add( types.CapabilityType, function(){
			return 'rw '+this.location().name()+' '+_wrap( this.value() );			
		} );
		
		_add( types.StackedType, function(){
			return _wrap( this.left() )+' :: '+_wrap( this.right() );
		} );
		
		_add( types.RecordType, function(){
			var res = [];
			var fields = this.getFields();
			for( var i in fields )
				res.push(i+": "+_wrap( fields[i]) );
			return "["+res.join()+"]";
		} );
		
		_add( types.TupleType, function(){
			return "["+this.getValues().join()+"]";
		} );
		
		_add( types.DefinitionType, function(){
			return _wrap( this.definition() )+'['+ this.args().join() +']';
		} );
		
		var tmp = function(){ return this.name(); };
		_add( types.LocationVariable, tmp );
		_add( types.TypeVariable, tmp );
		_add( types.PrimitiveType, tmp );
		
		_add( types.NoneType, function(){ return 'none'; });
		
	})();

	//
	// VISITORS
	//
	
	/**
	 * Searchs types 't' for location variable 'loc'. isFree if NOT present.
	 * @param {Type} t that is to be traversed
	 * @param {LocationVariable,TypeVariable} loc that is to be found
	 * @return {Boolean} true if location variableis NOT in type.
	 * Note that all variable names collide so that checking for 
	 * LocationVariable versus TypeVariable is not necessary.
	 */

	var isFree = (function(){
		var _visitor = {};
		var _add = function( k , fun ){
			error( !_visitor.hasOwnProperty(k) || ("Duplicated " +k) );
			_visitor[k] = fun;
		};
		
		_add( types.FunctionType, function(t,loc){
			return isFree( t.argument(), loc ) && isFree( t.body(), loc );
		});
		
		_add( types.BangType, function(t,loc){
			return isFree( t.inner(), loc );
		});
		
		_add( types.RelyType, function(t,loc){
			return isFree( t.rely(), loc ) && isFree( t.guarantee(), loc );
		});
		
		_add( types.GuaranteeType, function(t,loc){
			return isFree( t.guarantee(), loc ) && isFree( t.rely(), loc );
		});
 
		_add( types.SumType, function(t,loc){
			var tags = t.tags();
			for( var i in tags ){
				if( !isFree(t.inner(tags[i]),loc) )
					return false; 
			}	
			return true;
		});

		_add( types.ForallType, function(t,loc){
			if( t.id().name() === loc.name() ) {
				// the name is already bounded, so loc must be fresh
				// because it does not occur free inside t.inner()
				return true;
			}
			return isFree(t.id(),loc) && isFree(t.inner(),loc);
		});
		_add( types.ExistsType, _visitor[types.ForallType] ); //reuse definition

		_add( types.ReferenceType, function(t,loc){
			return isFree( t.location(), loc );
		});

		_add( types.StackedType, function(t,loc){
			return isFree( t.left(), loc ) && isFree( t.right(), loc );
		});
		
		_add( types.CapabilityType, function(t,loc){
			return isFree( t.location(), loc ) && isFree( t.value(), loc );
		});

		_add( types.RecordType, function(t,loc){
			var fs = t.getFields();
			for( var i in fs ){
				if( !isFree(fs[i],loc) )
					return false;
			}
			return true;
		});
		
		_add( types.AlternativeType, function(t,loc){
			var inners = t.inner();
			for( var i=0; i<inners.length; ++i )
				if( !isFree(inners[i],loc) )
					return false;
			return true;
		});
		_add( types.StarType, _visitor[types.AlternativeType] ); //reuse def.
		
		_add( types.TupleType, function(t,loc){
			var vs = t.getValues();
			for( var i in vs ){
				if( !isFree(vs[i],loc) )
					return false;
			}
			return true;
		});
		
		_add( types.TypeVariable, function(t,loc){
			return t.name() !== loc.name();
		});
		_add( types.LocationVariable, _visitor[types.TypeVariable] ); //reuse def.
		
		_add( types.PrimitiveType, function(t,loc){ return true; });
		_add( types.NoneType, _visitor[types.PrimitiveType] );
		
		_add( types.DefinitionType, function(t,loc){
			// t.definition() is a name/identifer.
			var vs = t.args();
			for( var i in vs ){
				if( !isFree(vs[i],loc) )
					return false;
			}
			return true;
		});
		
		// the closure that uses the private _visitor
		return function (t,loc) {
			if( !_visitor.hasOwnProperty( t.type ) )
				error( "@isFree: Not expecting " +t.type );
			return _visitor[t.type](t,loc);
		};
	})();
	
	/**
	 * Substitutes in 'type' any occurances of 'from' to 'to'
	 * 		type[from/to] ('from' for 'to')
	 * @param {Type} type that is to be searched
	 * @param {Type} when 'from' is found, it is replaced with
	 * @param {LocationVariable,TypeVariable} 'to'
	 * @param {Function} equals function to compare types
	 * @return a *copy* of 'type' where all instances of 'from' have been
	 * 	replaced with 'to' (note that each to is the same and never
	 * 	cloned).
	 *  Note that it also RENAMES any bounded variable that colides with the
	 *  'from' name so that bounded names are never wrongly substituted.
	 */
	
	var substitutionF = function(t,from,to,eq){
		
		// for convenience...
		var rec = function(type){
			return substitutionF(type,from,to,eq);
		}
		
		if( eq(t,from) )
			return to;
			
		switch ( t.type ){
		case types.FunctionType:
			return new FunctionType( rec(t.argument()), rec(t.body()) );
		case types.BangType:
			return new BangType( rec(t.inner()) );
		case types.RelyType: {
			return new RelyType( rec(t.rely()), rec(t.guarantee()) );
		}
		case types.GuaranteeType: {
			return new GuaranteeType( rec(t.guarantee()), rec(t.rely()) );
		}
		case types.SumType:{
			var sum = new SumType();
			var tags = t.tags();
			for( var i in tags )
				sum.add( tags[i], rec(t.inner(tags[i])) );
			return sum;
		}
		case types.AlternativeType:{
			var star = new AlternativeType();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}
		case types.StarType:{
			var star = new StarType();
			var inners = t.inner();
			for( var i=0;i<inners.length;++i ){
				star.add( rec(inners[i]) ); 
			}	
			return star;
		}
		// CAPTURE AVOIDANCE in the following cases...
		// Renaming is needed to avoid capture of bounded variables.
		// We have two cases to consider:
		// 1. The variable to be renamed is the same as bounded var:
		// (exists t.A){t/X} "t for X" 
		// in this case, we are done renaming, since t is bounded inside A.
		// 2. The *to* name is the same the bounded var:
		// (exists t.A){g/t} "g for t"
		// in this case we must rename the location 't' to avoid capture
		// in the case when 'g' occurs in A.
		case types.ExistsType: 
		case types.ForallType: {
			if( ( from.type === types.LocationVariable ||
				  from.type === types.TypeVariable )
					&& t.id().name() === from.name() ){
				// 'from' is bounded, thus we are done. 
				return t;
			}
			
			var nvar = t.id();
			var ninner = t.inner();
			if( ( to.type === types.LocationVariable ||
				  to.type === types.TypeVariable )
					&& t.id().name() === to.name() ){
				// capture avoiding substitution 
				nvar = t.id().clone(null); // fresh loc/type-variable
				
				// must use simpler equals function to avoid unending cycles
				ninner = substitutionVarsOnly( t.inner(), t.id(), nvar );
			}
			
			// switch again to figure out what constructor to use.
			switch( t.type ){
				case types.ExistsType:
					return new ExistsType( nvar, rec(ninner) );
				case types.ForallType:
					return new ForallType( nvar, rec(ninner) );
				default:
					error( "@substitution: Not expecting " +t.type );
			}
		}
		case types.ReferenceType:
			return new ReferenceType( rec(t.location()) );
		case types.StackedType:
			return new StackedType( rec(t.left()), rec(t.right()) );
		case types.CapabilityType:
			return new CapabilityType( rec(t.location()), rec(t.value()) );
		case types.RecordType: {
			var r = new RecordType();
			var fs = t.getFields();
			for( var i in fs )
				r.add( i, rec(fs[i]) );
			return r;
		}
		case types.TupleType: {
			var r = new TupleType();
			var fs = t.getValues();
			for( var i in fs )
				r.add( rec(fs[i]) );
			return r;
		}
		case types.DefinitionType: {
			var fs = t.args();
			var tmp = [];
			for( var i in fs )
				tmp = tmp.concat( rec(fs[i]) );
			return new DefinitionType(t.definition(),tmp);
		}
		// these remain UNCHANGED
		// note that Location/Type Variable is tested ABOVE, not here
		case types.LocationVariable:
		case types.TypeVariable:
		case types.PrimitiveType:
		case types.NoneType:
			return t;

		default:
			error( "@substitution: Not expecting " +t.type );
		}
	};
	
	var substitutionVarsOnly = function(type,from,to){
		if( from.type !== to.type ||
			( from.type !== types.LocationVariable && 
				from.type !== types.TypeVariable ) ){
			error( "@substitutionVarsOnly: not a Type/LocationVariable" );
		}
		return substitutionF(type,from,to,function(a,b){
			// same type and same name
			return a.type === b.type && a.name() === b.name();
		});
	};
	
	var substitution = function(t,from,to){
		return substitutionF(t,from,to,equals);
	};
	
	//
	// EQUALS and SUBTYPING
	//	

	/**
	 * Tests if types 'a' and 'b' are the same.
	 * Up to renaming of bounded variables, so that it renames existentials
	 * and foralls. Thus, returns true when they are structurally equal, even
	 * if their labels in existentials are of different strings values.
	 * @param {Type} a
	 * @param {Type} b
	 * @return {Boolean} if the types are equal up to renaming.
	 */
	var equals = function(t1,t2){

		// exactly the same
		if( t1 === t2 )
			return true;
				
		// Only tries to unfold definition if it appears that it will help. 
//XXX: this is a very shallow lookup. won't work with more than 2 typedefs in sequence
//XXX: why won't this work with unAll? (another debugging session needed...)
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;
		if( def1 ^ def2 ){
//debugger
			if( def1 && typedefs[t1.definition()].type === t2.type ){
				t1 = unfoldDefinition(t1);
				// if unfolding worked
				if( t1.type !== types.DefinitionType ){
					return equals( t1, t2 );
				}
			}
			if( def2 && typedefs[t2.definition()].type === t1.type ){
				t2 = unfoldDefinition(t2);
				// if unfolding worked
				if( t2.type !== types.DefinitionType ){
					return equals( t1, t2 );
				}
			}
		}
		
		if( t1.type !== t2.type )
			return false;
			
		// assuming both same type
		switch ( t1.type ){
			case types.ForallType:		
			case types.ExistsType: {
				if( t1.id().type !== t2.id().type )
					return false;
					
				// if name mismatch, do "quick" substitution to make them match
				if( t1.id().name() !== t2.id().name() ){
					var tmp = substitutionVarsOnly(t2.inner(),t2.id(),t1.id());
					return equals( t1.inner(), tmp );
				}
		
				return equals( t1.inner(), t2.inner() );
			}
			case types.TypeVariable:
			case types.LocationVariable: {
				// note: same name for case of variables that are in scope
				// but not declared in the type (i.e. already opened)
				return  t1.name() === t2.name();
			}
			case types.FunctionType:
				return equals( t1.argument(), t2.argument() ) &&
					equals( t1.body(), t2.body() );
			case types.BangType:
				return equals( t1.inner(), t2.inner() );
			case types.RelyType: {
				return equals( t1.rely(), t2.rely() ) &&
					equals( t1.guarantee(), t2.guarantee() );
			}
			case types.GuaranteeType: {
				return equals( t1.guarantee(), t2.guarantee() ) &&
					equals( t1.rely(), t2.rely() );
			}
			case types.SumType: {
				var t1s = t1.tags();
				var t2s = t2.tags();
				// note that it is an array of tags (strings)
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0; i<t1s.length; ++i ){
					if( t2s.indexOf(t1s[i])===-1 ||
						!equals( t1.inner(t1s[i]), t2.inner(t1s[i]) ) )
						return false;
				}
				return true;
			}
			case types.ReferenceType:
				return equals( t1.location(), t2.location() );
			case types.StackedType:
				return equals( t1.left(), t2.left() ) &&
					equals( t1.right(), t2.right() );
			case types.CapabilityType:
				return equals( t1.location(), t2.location() ) &&
					equals( t1.value(), t2.value() );
			case types.RecordType: {
				var t1s = t1.getFields();
				var t2s = t2.getFields();
				if( Object.keys(t1s).length !== Object.keys(t2s).length )
					return false;
				for( var i in t2s )
					if( !t1s.hasOwnProperty(i) || 
						!equals( t1s[i], t2s[i] ) )
						return false;
				return true;
			} 
			case types.TupleType: {
				var t1s = t1.getValues();
				var t2s = t2.getValues();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !equals( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			case types.PrimitiveType:
				return t1.name() === t2.name();
			case types.AlternativeType:
			case types.StarType:{
				var i1s = t1.inner();
				var i2s = t2.inner();
				
				if( i1s.length !== i2s.length )
					return false;
				// any order should do
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					// tries to find matching element
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( equals(curr,tmp) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					// if not found, then must be different
					if( !found ){
						return false;
					}
				}
				return true;
			}
			case types.DefinitionType:{
				if( t1.definition() !== t2.definition() )
					return false;
				
				var t1s = t1.args();
				var t2s = t2.args();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !equals( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			default:
				error( "@equals: Not expecting " +t2.type );
			}
	};
	
	/**
	 * Subtyping two types.
	 * @param {Type} t1
	 * @param {Type} t2
	 * @return {Boolean} true if t1 <: t2 (if t1 can be used as t2).
	 */
	var subtypeOf = function( t1 , t2 ){
	
		if( t1 === t2 || equals(t1,t2) ) // A <: A
			return true;
		
		// if mismatch on DefinitionType
		var def1 = t1.type === types.DefinitionType;
		var def2 = t2.type === types.DefinitionType;
		if( def1 ^ def2 ){
			if( def1 ){
				t1 = unAll(t1,false,true);
				// if unfolding worked
				if( t1.type !== types.DefinitionType ){
					return subtypeOf( t1, t2 );
				}
			}
			if( def2 ){
				t2 = unAll(t2,false,true);
				// if unfolding worked
				if( t2.type !== types.DefinitionType ){
					return subtypeOf( t1, t2 );
				}
			}
		}

		// "pure to linear" - ( t1: !A ) <: ( t2: A )
		if ( t1.type === types.BangType && t2.type !== types.BangType )
			return subtypeOf( t1.inner(), t2 );
	
		// types that can be "banged"
		if ( t2.type === types.BangType &&
			( t1.type === types.ReferenceType
			|| t1.type === types.PrimitiveType
			|| ( t1.type === types.RecordType && t1.isEmpty() ) ) )
			return subtypeOf( t1, t2.inner() );
			
		// "ref" t1: (ref p) <: !(ref p)
		if ( t1.type === types.ReferenceType && t2.type === types.BangType )
			return subtypeOf( t1, t2.inner() );
			
		
		// all remaining rule require equal kind of type
		if( t1.type !== t2.type ){
			return false;
		}
			
		//else: safe to assume same type from here on
		switch ( t1.type ){
			case types.NoneType:
				return true;
			case types.PrimitiveType:
				return t1.name() === t2.name();
			case types.BangType:
				// if t2 is unit: "top" rule
				if( t2.inner().type === types.RecordType && t2.inner().isEmpty() )
					return true;
				return subtypeOf( t1.inner(), t2.inner() );
			case types.ReferenceType:
				return subtypeOf( t1.location(), t2.location() );
			case types.RelyType: {
				return subtypeOf( t1.rely(), t2.rely() ) &&
					subtypeOf( t1.guarantee(), t2.guarantee() );
			}
			case types.GuaranteeType: {
				return subtypeOf( t1.guarantee(), t2.guarantee() ) &&
					subtypeOf( t1.rely(), t2.rely() );
			}
			case types.FunctionType:
				return subtypeOf( t2.argument(), t1.argument() )
					&& subtypeOf( t1.body(), t2.body() );
			case types.RecordType:{
				if( !t1.isEmpty() && t2.isEmpty() )
					return false;

				// all fields of t2 must be in t1
				var t1fields = t1.getFields();
				var t2fields = t2.getFields();				
				for( var i in t2fields ){
					if( !t1fields.hasOwnProperty(i) ||
						!subtypeOf( t1fields[i], t2fields[i] ) ){
						return false;
					}
				}
				return true;
			}
			case types.TupleType: {
				var t1s = t1.getValues();
				var t2s = t2.getValues();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !subtypeOf( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			case types.StackedType:
				return subtypeOf( t1.left(), t2.left() ) &&
					subtypeOf( t1.right(), t2.right() );
			case types.AlternativeType:
			case types.StarType:{
				var i1s = t1.inner();
				var i2s = t2.inner();
				
				if( i1s.length !== i2s.length )
					return false;
				// for *-type, any order will do
				var tmp_i2s = i2s.slice(0); // copies array
				for(var i=0;i<i1s.length;++i){
					var curr = i1s[i];
					var found = false;
					for(var j=0;j<tmp_i2s.length;++j){
						var tmp = tmp_i2s[j];
						if( subtypeOf(curr,tmp) ){
							tmp_i2s.splice(j,1); // removes element
							found = true;
							break; // continue to next
						}
					}
					if( !found )
						return false;
				}
				return true;
			}
			case types.SumType:{
				var i1s = t1.tags();
				var i2s = t2.tags();
				for( var i in i1s ){
					var j = t2.inner(i1s[i]);
					if( j === undefined || // if tag is missing, or
						!subtypeOf( t1.inner(i1s[i]), j ) )
						return false;
				}
				return true;
			}
			case types.CapabilityType:
				return subtypeOf( t1.location(), t2.location() ) &&
					subtypeOf( t1.value(), t2.value() );
				
			case types.ForallType:		
			case types.ExistsType:{
				
				if( t1.id().type !== t2.id().type )
					return false;
				
				// if needs renaming
				if( t1.id().name() !== t2.id().name() ){
					var tmp = substitutionVarsOnly( t2.inner(), t2.id(), t1.id() );
					return subtypeOf( t1.inner(), tmp );
				}

				return subtypeOf( t1.inner(), t2.inner() );
			}

			case types.TypeVariable:
			case types.LocationVariable: {
					return t1.name() === t2.name();
			}

			case types.DefinitionType:{
				if( t1.definition() !== t2.definition() )
					return false;
				
				var t1s = t1.args();
				var t2s = t2.args();
				if( t1s.length !== t2s.length )
					return false;
				for( var i=0;i<t1s.length;++i )
					if( !subtypeOf( t1s[i], t2s[i] ) )
						return false;
				return true;
			}
			default:
				error( "@subtype: Not expecting " +t1.type );
		}

	};
	
	//
	// TYPING ENVIRONMENT
	//
	
	// The typing environment is a spaghetti stack where the parent
	// may be shared among several different typing environments.
	// All methods return:
	// 	undefined - new element collides with a previously existing one;
	//  null/value - if all OK.
	var Environment = function(parent){
		// note that set only works at the local level (i.e. it will never
		// attempt to set something in an upper-level).

		// CAREFUL: '$' and '#' cannot be source-level identifiers
		var TYPE_INDEX='$';
		//var CAP_INDEX='#';
		
		// meant to be $protected fields
		this.$map = {};
		this.$caps = [];
		this.$parent = parent;
		
		// FIXME first attempt
		this.$defocus_guarantee = null;
		this.$defocus_env = null;
		
		var isNonShared = function( t ){
	 		// types that are sure to not interfere with any focused cell
	 		return t.type === types.BangType ||
	 		 ( t.type === types.ForallType && isNonShared( t.inner() ) ) ||
	 		 ( t.type === types.ExistsType && isNonShared( t.inner() ) ) ||
	 		 ( t.type === types.CapabilityType && isNonShared( t.value() ) ) ||
	 		 ( t.type === types.StackedType && isNonShared( t.left() ) 
	 			&& isNonShared( t.right() ) ); 
 		}
 	
 		// splits the environments
		var split = function(a,d_env){
			if( a === null )
				return null;
			
			for( var i in a.$map ){
				var tmp = a.$map[i];
				if( !isNonShared(tmp) && i.indexOf(TYPE_INDEX) !== 0 ){
					// move to defocus environment
					delete a.$map[i];
					d_env.$map[i] = tmp;
				}
			}
			var aa = [];
			var dd = [];
			for( var i=0; i<a.$caps.length;++i ){
				var tmp = a.$caps[i];
				if( !isNonShared(tmp) ){
					dd.push( tmp );
				}else{
					aa.push( tmp );
				}
			}
			a.$caps = aa;
			d_env.$caps = dd;
			
			if( a.$parent !== null ){
				d_env.$parent = new Environment(null);
				split(a.$parent,d_env.$parent);
				
				// nest defocus guarantees, if they exist
				d_env.$parent.$defocus_guarantee = a.$parent.$defocus_guarantee;
				d_env.$parent.$defocus_env = a.$parent.$defocus_env;
				
				a.$parent.$defocus_guarantee = null;
				a.$parent.$defocus_env = null;
			}
			
			return null;
		}
		
		// merge the environments
		var merge = function(a,d_env){
			if( d_env === null )
				return null;
			
			for( var i in d_env.$map ){
				a.$map[i] = d_env.$map[i];
			}
			
			for( var i=0; i<d_env.$caps.length;++i ){
				a.$caps.push( d_env.$caps[i] );
			}
			
			if( a.$parent !== null ){
				return merge(a.$parent,d_env.$parent);
			}
			
			return null;
		}
		
		this.focus = function(t){
			if( t.type !== types.RelyType )
				return undefined;
			
			var tmp = new Environment(null);
			this.$defocus_guarantee = t.guarantee();
			this.$defocus_env = tmp;
			
			split( this, tmp );
			
			// append the focused cap
			this.setCap( t.rely() );
			return true; //signals OK
		}
		
		this.defocus_guarantee = function(){
			if( this.$defocus_guarantee !== null )
				return this.$defocus_guarantee;
			if( this.$parent === null )
				return undefined;
			return this.$parent.defocus_guarantee();
		}
		
		this.defocus = function(){

			if( this.$defocus_guarantee === null ){
				if( this.$parent === null )
					return undefined;
				// search upwards...
				return this.$parent.defocus();
			}
			
			// merge environments
			merge( this, this.$defocus_env );
			this.$defocus_guarantee = null;
			this.$defocus_env = null;
		}
		
		// scope methods		
		this.newScope = function(){
			return new Environment(this);
		}
		this.endScope = function(){
			return this.$parent;
		}
		
		// operations over IDENTIFIERS
		this.set = function(id,value){
			if ( this.$map.hasOwnProperty(id) )
				return undefined; // already exists
			this.$map[id] = value;
			return true; // ok
		}
		this.get = function(id,cond){ // condition for removal
			if ( this.$map.hasOwnProperty(id) ){
				var tmp = this.$map[id];
				if( cond !== undefined && cond(tmp) ){
					// ensures that it is no longer listed
					delete this.$map[id];
				}
				return tmp;
			}
			if( this.$parent === null )
				return undefined;
			return this.$parent.get(id,cond);
		}
		
		// operations over VARIABLES
		// (includes both TypeVariables and LocationVariables)
		this.setType = function(id,value){
			// type variables cannot be hidden, must be unique
			// otherwise it would either require renaming collisions
			// or could allow access to parts that collide. 
			if( this.getType(id) !== undefined )
				return undefined; // already there
			return this.set(TYPE_INDEX+id,value);
		}
		this.getType = function(id){
			return this.get(TYPE_INDEX+id);
		}
		
		// other...
		this.size = function(){
			return Object.keys(this.$map).length+
					this.$caps.length+
				( this.$parent === null ? 0 : this.$parent.size() );
		}
		
		this.clone = function(){
			var env = this.$parent !== null ?
				new Environment( this.$parent.clone() ) :
				new Environment( null );

			for( var i in this.$map ){
				// assuming it is OK to alias content (i.e. immutable stuff)
				env.set( i, this.$map[i] );
			}
			for( var i=0; i<this.$caps.length;++i ){
				env.setCap( this.$caps[i] );
			}
			
			env.$defocus_guarantee = this.$defocus_guarantee;
			// $defocus_env is immutable so it is safe to alias
			env.$defocus_env =  this.$defocus_env;
			
			return env;
		}
		
		// FIXME: more of a merge
		this.isEqual = function(other){
			return comps(this,other,true);
		}
		
		// no order is guaranteed!
		this.visit = function(all,f){
			for( var i in this.$map ){
				var isType = (i[0] === TYPE_INDEX);
				f(i,this.$map[i],false,isType);
			}
			for( var i=0; i<this.$caps.length;++i ){
				f(null,this.$caps[i],true,false);
			}
			if( all && this.$parent !== null )
				this.$parent.visit(all,f);
		}
		
		// -------
		
		this.removeCap = function( searchF ){
			for( var i=0; i<this.$caps.length ; ++i ){
				if( searchF( this.$caps[i] ) ){
					// if found, remove it
					var res = this.$caps[i];
					this.$caps.splice(i,1)[0];
					return res;
				}
			}
			if( this.$parent === null )
				return undefined; // not found
			return this.$parent.removeCap(searchF);
		}
		
		/*
		this.removeRWCap = function( loc_name ){
			return this.removeCap(
				function( c ){
					return c.type === types.CapabilityType &&
						c.loc().name() === loc_name;
				}
			);
		}*/
		
		// Temporary Function
		this.removeNamedCap = function( name ){
			return this.removeCap(
				function( c ){
					return capContains( name, c );
				}
			);
		}
		
		this.setCap = function( c ){
			error( ( c.type !== types.LocationVariable && 
				c.type !== types.GuaranteeType ) || 'Error @setCap' );

			this.$caps.push( c );
			return true;
		}
		
	};
	
	// CAUTION: the following functions/methods ASSUME there is a separation
	// in the domain of LocationVariables and TypeVariables so that just
	// comparing strings is enough to know if some string is equal to some
	// Loc/TypeVariable without needing to compare the types, just strings.
	/**
	 * @param {Type} val
	 * @param {String} id
	 * @return if there is a type/loc variable with name 'id' in type 'val'
	 */
	var capContains = function( name, cap ){
		switch( cap.type ){
			case types.CapabilityType:
				return cap.location().name() === name;
			case types.TypeVariable:
				return cap.name() === name;
			// cap may be anywhere, linear search
			case types.StarType:
			case types.AlternativeType:{
				var ins = cap.inner();
				for(var i=0;i<ins.length;++i){
					if( capContains(name,ins[i]) )
						return true;
				}
				return false;
			}
			case types.RelyType:{
				var rely = cap.rely();
				if( rely.type === types.DefinitionType ){
					rely = unfoldDefinition(rely);
				}
				return rely.location().name() === name;
			}
			case types.DefinitionType:{
				var tmp = unfoldDefinition(cap);
				return capContains(name,tmp); 
			}
			default:
				// another types disallowed, for now
				error( 'Error @capContains: '+cap.type );
		}
	}
	
	// TypeVariables must be upper cased.
	var isTypeVariableName = function(n){
		return n[0] === n[0].toUpperCase();
	}
	
	//
	// TYPE CHECKER
	//
	
	// FIXME clean up
	var comps = function(a,b,merge_caps){
			// compare nulls due to parents
			if( a === null && b === null )
				return true;
			if( a === null ^ b === null )
				return false;
			if( a.size() !== b.size() )
				return false;
			// 1st: just check above, never merging
			if( !comps(a.$parent,b.$parent,false) )
				return false
			
			// 2nd: check keys
			var a_map = a.$map;
			var b_map = b.$map;
			for( var id in a_map ){
				if( !b_map.hasOwnProperty(id) )
					return false;

				if( !equals( a_map[id], b_map[id] ) )
					return false;
			}
			
			var a_caps = a.$caps;
			var b_caps = b.$caps;
			
			// 3rd: merge caps
			if( merge_caps ){
				// this will merge b with a's caps
				// TODO
				
				// find those caps that are common to both
				// and those that will need to be merged with (+)
				var diff_a = [];
				var diff_b = [];
				var common = [];
				var seen = [];
				
				for( var i=0;i<a_caps.length;++i){
					var found = false;
					for( var j=0;j<b_caps.length;++j ){
						if( equals( a_caps[i], b_caps[j] ) && 
							seen.indexOf(j) === -1 ){
							found = true;
							seen.push(j);
							common.push( a_caps[i] );
							break;
						}
					}
					if( !found ){
						diff_a.push( a_caps[i] );
					}
				}
				for( var i=0;i<b_caps.length;++i ){
					if( seen.indexOf(i) === -1 ){
						diff_b.push(b_caps[i]);
					}
				}
				
				a.$caps = common;
				a_caps = common;
	
				if( diff_a.length > 0 || diff_b.length > 0 ){
					// if there is a difference in the two environments
					var at = NoneType;
					if( diff_a.length > 0 ){
						if( diff_a.length > 1 ){
							at = new StarType();
							for( var i = 0 ; i < diff_a.length; ++i ){
								at.add( diff_a[i] );
							}
						}else{
							at = diff_a[0];
						}
					}
					var bt = NoneType;
					if( diff_b.length > 0 ){
						if( diff_b.length > 1 ){
							bt = new StarType();
							for( var i = 0 ; i < diff_b.length; ++i ){
								bt.add( diff_b[i] );
							}
						}else{
							bt = diff_b[0];
						}
					}
					var alter = new AlternativeType();
					alter.add( at );
					alter.add( bt );
					a_caps.push( alter );
				}
				return true;
				
			} else { // just check if equal
				if( a_caps.length !== b_caps.length )
					return false;
				
				// may be with any order
				var seen = [];
				for( var i=0;i<a_caps.length;++i){
					var found = false;
					for( var j=0;j<b_caps.length;++j ){
						if( equals( a_caps[i], b_caps[j] ) && 
							seen.indexOf(j) === -1 ){
							seen.push(j);
							found = true;
							break;
						}
					}
					if( !found )
						return false;
				}
				return true;
			}
		}
		
		
	/**
	 * Attempts to merge the two types given as argument.
	 * @return undefined if they cannot be merged, or the type that is
	 * 	compatible with both.
	 */
	var mergeType = function(t1,t2){
		if( subtypeOf(t1,t2) )
			return t2;
		if( subtypeOf(t2,t1) )
			return t1;

		// if bang mismatch, we need to not consider the sum as banged because
		// our types cannot do a case on whether the type is liner or pure
		var b1 = t1.type === types.BangType;
		var b2 = t2.type === types.BangType;
		
		if( b1 ^ b2 ){
			if( b1 ) t1 = t1.inner();
			if( b2 ) t2 = t2.inner();
		}
		
		var s1 = t1.type === types.StackedType;
		var s2 = t2.type === types.StackedType;
		
		if( s1 ^ s2 ){
			if( !s1 ) t1 = new StackedType(t1,NoneType);
			if( !s2 ) t2 = new StackedType(t2,NoneType);
		}
		
		if( t1.type !== t2.type )
			return undefined;
		// both the same type
		
		if( t1.type === types.StackedType ){
			var left = mergeType( t1.left(), t2.left() );
			if( left === undefined )
				return undefined;
			var right = mergeType( t1.right(), t2.right() );
			if( right === undefined ){
				// if they cannot be merged, then they are alternatives
				// TODO: maybe partially merge is possible?
				right = new AlternativeType();
				right.add( t1.right() );
				right.add( t2.right() );
			}
			return new StackedType(left,right);
		}
		
		if( t1.type === types.BangType ){
			var tmp = mergeType( t1.inner(),t2.inner() );
			if( tmp !== undefined )
				return new BangType( tmp );
		}
		
		if( t1.type === types.SumType ){
			// merge both types
			var tmp = new SumType();
			// add all the labels to the temporary sum
			var tags = t1.tags();
			for( var i in tags ){
				tmp.add( tags[i], t1.inner(tags[i] ) )
			}
			// now check the other to make sure any overlapping is ok or add
			// anything extra that it may have
			tags = t2.tags();
			for( var i in tags ){
				var overlap = tmp.inner(tags[i]);
				if( overlap !== undefined ){
					// make sure they match
					if( !equals( overlap, t2.inner(tags[i]) ))
						return undefined;
				}
				else{
					// make sure it was added.
					if( tmp.add( tags[i], t2.inner(tags[i] ) ) === undefined )
						return undefined;
				}
			}
			return tmp;
		}
		
		// all other cases must have exactly the same type
		if( equals(t1,t2) )
			return t1;
		// FIXME should subtyping replace equals? i.e.:
		// if( subtypeOf(t1,t2) ) return t2;
		// if( subtypeOf(t2,t1) ) return t1;
			
		return undefined;
	}

	/*
	 * bang -- remove bang(s)? !A <: A
	 * rec -- unfold recursive definition(s)?
	 */
	var unAll = function(t,bang,rec){
		var MAX = 100;
		
		while( MAX-->0 ){
			
			// by subtyping rule: !A <: A
			if( bang && t.type === types.BangType ){
				t = t.inner();
				continue;
			}
			
			// by unfold definition
			if( rec && t.type === types.DefinitionType ){
				t = unfoldDefinition(t);
				continue;
			}
			
			break;
		}

		if( MAX === 0 ){
			console.debug('@unAll: MAX UNFOLD REACHED, '+t);
			// returns whatever we got, will likely fail due to a packed
			// definition anyway. But it's not our fault that you gave us a type
			// that is bogus/infinite recursive!
//XXX statically detect infinitely recursive type definitions?
		}
		return t;

	}
		
	// attempts to convert type to bang, if A <: !A
	var purify = function(t){
		t = unAll(t,false,true);	
		if( t.type !== types.BangType ){
			var tmp = new BangType(t);
			if( subtypeOf(t,tmp) )
				return tmp;
		}
		return t;		
	}
	
	/**
	 * unstacks 'type' into the environment 'd'.
	 * @param type - the type with stacked stuff
	 * @param d - the typing environment that is to be extended
	 * @param ast - just for errors
	 * @return {Type} with the resulting type.
	 */
	var unstack = function( type, d, ast ){
		if( type.type === types.StackedType ){
			// all types are on the right, recursion is on left
			var right = unAll(type.right(), false, true);
			unstackType( right, d, ast );
			//unstackType( type.right(), d, ast );
			
			return unstack( type.left(), d, ast );
		}
		
		return type;
	}
	
	var unfoldDefinition = function(d){
		if( d.type !== types.DefinitionType )
			return d;
		
		var t = typedefs[d.definition()];
		var args = d.args();
		var pars = typedefs_args[d.definition()];
		for(var i=0;i<args.length;++i){
			t = substitution(t,pars[i],args[i]);
		}
		return t;
	}
	
	var unstackType = function(t, d, ast){
		switch( t.type ){
		case types.AlternativeType:
		case types.RelyType:
		case types.CapabilityType:
		case types.TypeVariable:
		// FIXME: is duplication check stil needed??
			assert( d.setCap( t ) || ('Duplicated capability for '+ t), ast );
			break;
		case types.StarType:{
			var tps = t.inner();
			for( var i=0; i<tps.length; ++i ){
				unstackType(tps[i], d, ast);
			}
			break;
		}
		case types.NoneType:
			// nothing to add to the environment
			break;
		default: 
			assert( 'Cannot unstack: '+t+' of '+t.type, ast);
		}
	}
	
	/** Attempts to expand a type 't' so as to match type 'p'
	 * complete type. This may fail in certain cases to simplify
	 * but otherwise it will be almost like "auto-stacking" without
	 * having to explicitly state what needs to be pushed.
	 * @param {Type,Null} t - type that is to be expanded, null if
	 * 	nothing is there.
	 * @param {Type} p - type that is the target to match to
	 * @return {Type} that tries to add the missing bits to 'm' as
	 * 	much as possible.
	 */
	var autoStack = function(t,p,e,a){
		// FIXME, rethink now that there exists a cap search...
		p = unAll(p,false,true);
		
		switch( p.type ) {
			case types.StarType: {
				if( t !== null && t.type === types.StarType ){
					// if the type is already a star type, we 
					// assume that it has all types there and do not
					// auto-stack anything since otherwise we would
					// need to compare and see what is missing, etc.
					// NOTE: this type is NOT the one given by the
					// programmer, but one that the typechecker found.
					return t;
				}
				else {
					// any other type should be ignored, but this
					// assert ensures nothing is silently dropped.
					assert( t === null || 'Error @autoStack ', a );
					
					var inners = p.inner();
					var tmp = new StarType();
					for(var i=0;i<inners.length;++i){
						tmp.add( autoStack(null, inners[i],e,a) );
					}
					return tmp;
				}
			}
			case types.StackedType: {
				if( t !== null && t.type === types.StackedType ){
					return new StackedType(
						autoStack( t.left(), p.left(), e, a ),
						autoStack( t.right(), p.right(), e, a ) 
					);
				}
				else{
					// any non-stacked type is assume to be the left
					// part of the soon to be stacked type
					return new StackedType(
						autoStack( t, p.left(), e, a ),
						autoStack( null, p.right(), e, a ) 
					);
				}
			}
			case types.CapabilityType: {
				// note that the capability can either be already
				// (manually) stacked or needs to be automatically
				// stacked.
				var cap_loc = p.location().name();
				if( t !== null && t.type === types.CapabilityType ){
					// if it was manually stacked, then just make
					// sure they are the same thing.
					var t_loc = t.location().name();
					assert( t_loc === cap_loc ||
						('Incompatible capability '+ t_loc+' vs '+cap_loc), a );
					return t;
				} else {
					assert( t === null || 'Error @autoStack ', a );
					var cap = e.removeNamedCap( cap_loc );
					assert( cap !== undefined || ('Missing capability '+cap_loc), a );
					return cap;
				}
			}
			case types.TypeVariable: {
				// analogous case to capabilities, either manually
				// stacked or we need to do it here.
				var p_loc = p.name();
				if( t !== null && t.type === types.TypeVariable ){
					var t_loc = t.name();
					assert( t_loc === p_loc ||
						('Incompatible variable '+t_loc+' vs '+p_loc), a );
					return t;
				} else {
					assert( t === null || 'Error @autoStack ', a );
					// note that, by its name, it must be a TypeVariable
					var cap = e.removeNamedCap( p_loc );
					assert( cap !== undefined || ('Missing capability '+p_loc), a );
					return cap;
				}
			}
			case types.AlternativeType:{
				assert( t === null || 'Error @autoStack ', a);

				// try the whole alternative type first
				var cap = e.removeCap(
					function(c){
						return subtypeOf(c,p);
					}
				);
				// if found, accept 'p'
				if( cap !== undefined )
					return p;
				
				// else, we must have at least one of the alternatives in
				// order to stack (+)
				var alts = p.inner();
				for( var i=0; i<alts.length; ++i ){
					cap = e.removeCap(
						function(c){
							return subtypeOf(c,alts[i]);
						}
					);
					// if found, accept 'p'
					if( cap !== undefined )
						return p;
				}
				assert( 'Failed to stack any of the alternatives', a);
			}
			case types.NoneType:
				// always valid to stack a NoneType
				assert( (t === null || t.type === types.NoneType) ||
					'Error @autoStack ', a );
				return NoneType;
			case types.RelyType: {
				var cap = e.removeCap( function(c){
					return subtypeOf(p,c);
				});
				assert( cap !== undefined || ('Missing capability '+p), a );
				return cap;
			}
			case types.GuaranteeType:
				assert( 'Error @autoStack, Guarantee...', a );
				break;
			default:
				// other types just fall through, leave the given type
				// in but make sure it is not null.
				assert( t !== null || ('Error @autoStack ' + p.type), a);
		}
		return t;
	}
	
	/**
	 * To properly end a scope we use the following idiom: stack all
	 * outstanding capabilities (of the delta environment) on top of the result
	 * 'type' and then pack all bounded type/location variables of the result
	 * @param ast - just for error flagging
	 * @param type - the final result type (should this not be needed?)
	 * @param env - the current scope to end, not that it remains unchanged
	 * @return the type with potentially stacked stuff. 
	 * 
	 * CAREFUL: this may conservatively packs stuff that could be free if it
	 * 	were packed manually! (i.e. there may be a less conservative packing
	 * 	order than the one picked by this function)
	 */
	var safelyEndScope = function( type, env, ast ){
		
		assert( env.$defocus_guarantee === null || 'Cannot drop focus' , ast);
		
		// 1. stack all capabilities
		var tmp = new StarType();

		env.visit(false, //only the elements at this level
			function(id,cap,isCap,isType){
			// ok to ignore type and location variable declarations
			if( isType )
				return;
			
			if( isCap ){
				tmp.add( cap );
				return;
			}
			
			switch( cap.type ){
				// these can be ignored
				case types.BangType:
				case types.PrimitiveType:
					break;
				default:
					// fails if attempting to stack something else
					assert( 'Auto-stack failure, '+id+' : '+cap.type, ast );
			}

		});
		
		var res = type;
		// if there's something to stack
		var ll = tmp.inner().length;
		if( ll > 0 ){
			if( ll === 1 ) // no need for star when there is just one
				res = new StackedType( res, tmp.inner()[0] );
			else
				res = new StackedType( res, tmp );
		}

		// 2. pack all bounded location variables
		env.visit(false,
			function(e,el,isCap,isType){
			// ignores all elements that are not type/location variables
			if( !isType )
				return;

			switch( el.type ){
				case types.LocationVariable:
					if( !isFree(res,el) ){
						var loc = new LocationVariable(null);
						res = new ExistsType( loc, substitution( res, el, loc ) );
					}
					break;
				case types.TypeVariable:
					if( !isFree(res,el) ){
						var loc = new TypeVariable(null);
						res = new ExistsType( loc, substitution( res, el, loc ) );
					}
					break;
				default:
					// fails if attempting to stack something else
					assert( 'Auto-stack failure, '+e+' : '+el.type, ast );
			}
		});
		return res;	
	}


// attempts to bang the result of f() which should only happen
// if it does not change the delta environment
var tryBang = function(ast,env,f){ // tryBang : is a closure
	var initial_size = env.size();
	var result = f(ast,env);
	if( initial_size === env.size() )
		return new BangType(result);
	return result;
};

/**
 * Protocol Conformance
 */
var checkProtocolConformance = function( s, a, b, ast ){
	var visited = [];
	var max_visited = 100; // safeguard against 'equals' bugs...
	
	// checks if state was already visited
	var contains = function(s,a,b){
		for( var i=0; i<visited.length; ++i ){
			var tmp = visited[i];
			if( equals(s,tmp[0]) && equals(a,tmp[1]) && equals(b,tmp[2]) )
				return true;
		}
		return false;
	}
	
	var sim = function(s,p){
		// unfold recursive types, etc.
		p = unAll(p,false,true);
		
		// first protocol
		if( p.type === types.NoneType )
			return { s : s , p : p };

		// now state
		if( s.type === types.AlternativeType ){
			var tmp_s = null;
			var tmp_p = null;
			var alts = s.inner();
			for( var i=0;i<alts.length; ++i ){
				//debugger;
				var tmp = sim(alts[i],p);
				if( tmp_s === null ){
					tmp_s = tmp.s;
					tmp_p = tmp.p;
				}else{
					assert( (equals( tmp_s, tmp.s ) && equals( tmp_p, tmp.p )) ||
						('[Protocol Conformance] Alternatives mimatch.\n'+
						'(1)\tstate:\t'+tmp_s+'\n\tstep:\t'+tmp_p+'\n'+
						'(2)\tstate:\t'+tmp.s+'\n\tstep:\t'+tmp.p+'\n'), ast );
				}
			}
			return { s : tmp_s , p : tmp_p };
		}
		
		if( p.type === types.AlternativeType ){
			var alts = p.inner();
			for( var i=0; i<alts.length; ++i ){
				try{
//console.debug('attempt:: '+alts[i] +' s::'+s);
					return sim(s,alts[i]);
				}catch(e){
					// assume it is an assertion error, continue to try with
					// some other alternative
					continue;
				}
			}
			assert( '[Protocol Conformance] No matching alternative.\n'+
				'state:\t'+s+'\n'+
				'step:\t'+p, ast );
		}
		
		var pp = unAll( p, false, true );
		
		assert( pp.type === types.RelyType ||
			('Expecting RelyType, got: '+pp.type+'\n'+pp), ast);
		
		assert( subtypeOf( s, pp.rely() ) ||
			('Invalid Step: '+s+' VS '+pp.rely()), ast );
		
		var next = pp.guarantee();
		assert( next.type === types.GuaranteeType ||
			('Expecting GuaranteeType, got: '+next.type), ast);
		
		return { s : next.guarantee() , p : next.rely() };		
	}
	
	var work = [];
	work.push( [s,a,b] );

	while( work.length > 0 ){
		var state = work.pop();
		var _s = state[0];
		var _a = state[1];
		var _b = state[2];
		
		// already done
		if( contains(_s,_a,_b) )
			continue;
//console.debug( 's:: '+_s+' p:: '+_a+' q:: '+_b);

		visited.push( [_s,_a,_b] );
		
		var l = sim(_s,_a);
		work.push( [l.s,l.p,_b] );
			
		var r = sim(_s,_b);
		work.push( [r.s,_a,r.p] );
		
		// This is useful to safeguard against different JS implementations...
		// more for debug than requirement of the algorhtm.
		assert( max_visited-- > 0 || 'ERROR: MAX VISITED', ast);
	}
};

	// this wrapper function allows us to inspect the type and envs
	// of some node, while leaving the checker mostly clean.
	var check = function(ast,env) {
		var info = { ast : ast, env : env.clone() };
		type_info.push( info );
		var res = check_inner( ast, env );
		info.res = res;
		return res;
	};

	/**
	 * @param {AST} ast, tree to check
	 * @param {Environment} env, typing environment at beginning
	 * @return either the type checked for 'ast' or throws a type error with
	 * 	what failed to type check.
	 */
	var setupAST = function( kind ) {
		
		switch( kind ) {
			
			// EXPRESSIONS
			case AST.kinds.LET: 
			return function( ast,env ) {
				var value = check( ast.val, env );

				var e = env.newScope();
				// note that it should unstack to the local scope, so as to 
				// leave the enclosing environment unchanged
				value = unstack( value, e, ast );				
				// attempt to make resulting type a bang type
				value = purify(value);
				
				// sequence is encoded as LET with id 'null', but this construct
				// drops the first expression's value so it must be of BangType
				assert( ast.id !== null || value.type === types.BangType ||
					('Cannot drop linear type '+value), ast );
				
				if( ast.id !== null ){
					// creating a new environment should avoid this error, but
					// include this check for consistency
					assert( e.set( ast.id, value ) ||
						('Identifier '+ ast.id +' already in scope'), ast );
				}

				var res = check( ast.exp, e );
				return safelyEndScope( res, e, ast.exp );
			};
			
			case AST.kinds.LET_TUPLE: 
			return function( ast, env ){
				var exp = check( ast.val, env );
				exp = unAll(exp, true, true);
				assert( exp.type === types.TupleType ||
					("Type '" + exp + "' not tuple"), ast.exp);
				
				var values = exp.getValues();
				assert( values.length === ast.ids.length ||
					("Incompatible sizes "+ast.ids.length+" != "+values.length), ast.exp);

				var e = env.newScope();
				for( var i=0; i<ast.ids.length ; ++i ){
					assert( e.set( ast.ids[i], values[i] ) ||
						("Identifier '" + ast.ids[i] + "' already in scope"), ast );
				}
				
				var res = check( ast.exp, e );
				return safelyEndScope( res, e, ast );
			};
			
			case AST.kinds.OPEN: 
			return function( ast, env ){
				var value = check( ast.val, env );
				value = unAll( value, true, true );
				
				assert( value.type === types.ExistsType ||
					("Type '" + value + "' not existential"), ast.exp);

				var loc = ast.type;
				var locvar;
				if( isTypeVariableName(loc) )
					locvar = new TypeVariable(loc);
				else
					locvar = new LocationVariable(loc);

				assert( locvar.type === value.id().type ||
					('Variable mismatch, expecting '+locvar.type
					+' got '+value.id().type), ast.val);

				value = substitution( value.inner(), value.id(), locvar );
				// unfold anything that became newly available
				value = unAll( value, false, true );
				
				// any unstack occurs in the inner expression
				var e = env.newScope();
				value = unstack( value, e, ast);
				// attempt to make it pure before adding to typing env.
				value = purify( value );

				assert( e.set( ast.id, value ) ||
						("Identifier '" + ast.id + "' already in scope"), ast );
				assert( e.setType( loc, locvar ) ||
						("Type '" + loc + "' already in scope"), ast );
				
				var res = check( ast.exp, e );
				return safelyEndScope( res, e, ast);
			};
			
			case AST.kinds.CASE: 
			return function( ast, env ){
				var val = unAll( check( ast.exp, env ), true, true );
				assert( val.type === types.SumType ||
					("'" + val.type + "' not a SumType"), ast);
				
				// checks only the branches that are listed in the sum type
				var tags = val.tags();
				var initEnv = env.clone();
				var endEnv = null;
				
				var result = undefined;
				for( var t in tags ){
					var tag = tags[t];
					var value = val.inner(tag);
					var branch = undefined;
					// search from branch
					for( var i=0; i<ast.branches.length; ++i ){
						if( ast.branches[i].tag === tag ){
							branch = ast.branches[i];
							break;
						}
					}
					// if still undefined
					assert( branch !== undefined || ('Missing branch for '+tag), ast);

					var e = env;
					if( endEnv !== null ){
						e = initEnv.clone();
					}
					
					e = e.newScope();
					value = purify( unstack( value, e, branch.exp ) );

					assert( e.set( branch.id, value ) ||
						("Identifier '" + branch.id + "' already in scope"), ast );
					
					var res = check( branch.exp, e );
					res = safelyEndScope( res, e, ast.exp );
					
					// check if effects are compatible
					if( endEnv === null ){
						endEnv = e.endScope();
					}else{
						assert( endEnv.isEqual( e.endScope() ) ||
							("Incompatible effects on branch '" + tag + "'"), branch);
					}

					// if first result, remember it
					if( result === undefined )
						result = res;
					else { // else try to merge both
						var tmp = mergeType( result, res );
						assert( tmp !== undefined || ('Incompatible branch results: '+
							result+' vs '+res), ast);
						result = tmp;
					}
				}
				return result;
			};
			
			case AST.kinds.PACK: 
			return function( ast, env ){
				var exp = check(ast.exp, env);
				var packed = check(ast.id, env);

				// CAREFUL 'ast.label' is left as null when unspecified which is
				// used on the constructors below to pick a fresh name.
				var label = ast.label;
				var variable;
				
				switch( packed.type ){
					case types.TypeVariable:
					case types.LocationVariable: {
						// create the new type/location variable with the 
						// given label, even if null for fresh.
						if( isTypeVariableName(packed.name()) ){
							assert( label === null || isTypeVariableName(label) ||
								'TypeVariable is wrongly cased', ast );
							variable = new TypeVariable(label);
						} else {
							assert( label === null || !isTypeVariableName(label) ||
								'LocationVariable is wrongly cased', ast );
							variable = new LocationVariable(label);
						}
						
						break;
					}
					default: {
						assert( label === null || isTypeVariableName(label) ||
							'TypeVariables must be upper-cased', ast );
							
						variable = new TypeVariable(label);
						break;
					}
				}
				
				// This is necessary to avoid capture of the old
				// location/type variables that may occur in exp
				// We cannot ensure capture avoidance because the label
				// may be given, thus committing ourselves to some label
				// from which we may not be able to move without 
				// breaking programmer's expectations.
				assert( isFree(exp,variable) ||
					('Label "'+variable.name()+'" is not free in '+exp), ast );

				exp = substitution( exp , packed, variable );
				return new ExistsType(variable,exp);
			}
			
			case AST.kinds.ALTERNATIVE_OPEN: 
			return function( ast, env ){
				var type = check(ast.type, env);
				assert( type.type === types.LocationVariable ||
					('Cannot alt-open '+type), ast.type );
				
				// FIXME also allow to give a type, not just a location.
				var cap = env.removeNamedCap( type.name() );
				
				assert( cap !== undefined || ('Missing cap: '+cap), ast.type );
					
				assert( cap.type === types.AlternativeType ||
					('Not AlternativeType '+cap), ast.type );
				
				var alts = cap.inner();
				var env_start = env.clone();
				var end_env = null;
				var result = null;
				
				for( var i=0; i<alts.length; ++i ){
					var tmp_env = end_env === null ? env : env_start.clone();
					var alternative = alts[i];
					alternative = unAll(alternative, false, true);
					unstackType( alternative, tmp_env, ast.type );

					var res = check( ast.exp, tmp_env );
					if( result === null )
						result = res;
					else {
						// attempt to merge results
						var tmp = mergeType( result, res );
						assert( tmp !== undefined || ('Incompatible alternative results: '+
							result+' vs '+res), ast);
						result = tmp;
					}
					
					if( end_env === null )
						end_env = tmp_env;
					else{
						assert( end_env.isEqual( tmp_env ) ||
							"Incompatible effects on alternatives", ast.exp);
					}
				}
				return result;
			};
			
			case AST.kinds.SUM_TYPE: 
			return function( ast, env ){
				var sum = new SumType();
				for( var i=0; i<ast.sums.length; ++i ){
					var tag = ast.sums[i].tag;
					assert( sum.add( tag, check( ast.sums[i].exp, env ) ) ||
							"Duplicated tag: "+tag, ast.sums[i]);
				}
				return sum;
			};
			
			case AST.kinds.ALTERNATIVE_TYPE: 
			return function( ast, env ){
				var alt = new AlternativeType();
				for( var i=0; i<ast.types.length; ++i ){
					alt.add( check( ast.types[i], env ) );
				}
				return alt;
			};
			
			case AST.kinds.STAR_TYPE: 
			return function( ast, env ){
				var star = new StarType();
				for( var i=0; i<ast.types.length; ++i ){
					star.add( check( ast.types[i], env ) );
				}
				return star;
			};
			
			case AST.kinds.NAME_TYPE: 
			return function( ast, env ){
				// the typing environment remains unchanged because all type
				// definitions and type/location variables should not interfere
				var label = ast.text;
				var tmp = env.getType( label );
				// if label matches type in environment, but we only allow
				// access to type variables and location variables using this
				// AST.kind --- all other uses are assumed to be recursives.
				if( tmp !== undefined &&
					( tmp.type === types.TypeVariable ||
					  tmp.type === types.LocationVariable ) )
						return tmp;
				
				// look for type definitions
				var lookup = typedefs[label];
				var lookup_args = typedefs_args[label];
		
				// found something
				if( lookup !== undefined && lookup !== null &&
					 lookup_args.length === 0 )
					return lookup;
		
				assert( 'Unknown type '+label, ast);
			};
			
			case AST.kinds.ID:
				// auxiliary function that only removes (i.e. destructive) if linear
				var destructive = function(t) {
					return t.type !== types.BangType;
				};
			return function( ast, env ){
				var id = ast.text;
				var val = env.get( id, destructive );
			
				assert( val !== undefined || ("Identifier '" + id + "' not found"), ast);

				return val;
			};
			
			case AST.kinds.NEW: 
			return function( ast, env ){
				var exp = check(ast.exp, env);
				// 'null' used to get a fresh location variable
				var loc = new LocationVariable(null);
				return new ExistsType( loc,
							new StackedType(
								new ReferenceType( loc ),
								new CapabilityType( loc, purify(exp) ) ) );
			};
			
			case AST.kinds.DEREF: 
			return function( ast, env ){
				var exp = unAll( check( ast.exp, env ), true, true );
				
				assert( exp.type === types.ReferenceType ||
					("Invalid dereference '"+exp+"'"), ast );

				var loc = exp.location().name();
				var cap = env.removeNamedCap( loc );
				
				assert( cap !== undefined || ("No capability to '"+loc+"'"), ast );
				
				if( cap.type === types.DefinitionType )
					cap = unfoldDefinition(cap);
				assert( cap.type === types.CapabilityType ||
					(loc+" is not a capability, "+cap.type), ast );
				
				var old = cap.value();

				var residual;
				
				// see if read must be destructive (i.e. leave unit)
				if( old.type === types.BangType ||
				// we only see if the old can be purified, but do not change it
				// to the potentiallu unfolded type definition.
					 purify(old).type === types.BangType )
					residual = old;
				else {
					residual = new BangType(new RecordType());
				}
				
				cap = new CapabilityType( cap.location(), residual );
				assert( env.setCap( cap ) || 'Failed to re-add cap', ast );
				return old;
			};
			
			case AST.kinds.DELETE: 
			return function( ast, env ){
				var exp = unAll( check( ast.exp, env ), true, true );
				
				if( exp.type === types.ReferenceType ){
					var loc = exp.location().name();
					var cap = env.removeNamedCap( loc );
					
					assert( cap !== undefined || ("No capability to '"+loc+"'"), ast );
					
					assert( cap.type === types.CapabilityType ||
						(loc +" is not a capability, "+cap.type), ast );

					// just return the old contents of 'cap'
					return cap.value();
					
				} else if( exp.type === types.ExistsType ){
					// Luis' delete rule...
					var inner = exp.inner();
					if( inner.type === types.StackedType ){
						var ref = unAll( inner.left(), true, true );
						var cap = inner.right();
						assert( ref.type === types.ReferenceType ||
							("Expecting reference '"+exp+"'"), ast);
						var loc = ref.location();
						assert( cap.type === types.CapabilityType ||
							("Expecting capability '"+exp+"'"), ast);
						assert( loc.name() === exp.id().name() ||
							("Expecting matching location '"+exp+"'"), ast);
						return new ExistsType(exp.id(),cap.value());
					}
					
				} 

				assert( "Invalid delete '"+exp+"'",ast);
			};

			case AST.kinds.ASSIGN: 
			return function( ast, env ){
				var lvalue = unAll( check( ast.lvalue, env ), true, true );
				var value = check( ast.exp, env );
				
				assert( lvalue.type === types.ReferenceType ||
					("Invalid assign '"+lvalue+"' := '"+value+"'"), ast.lvalue);
				
				var loc = lvalue.location().name();
				var cap = env.removeNamedCap( loc );
				
				assert( cap !== undefined || ("Cannot assign, no capability to '"+loc+"'"), ast );
				
				assert( cap.type === types.CapabilityType ||
					(loc+" is not a capability"), ast );
				
				var old = cap.value();
				cap = new CapabilityType( cap.location(), purify(value) );
				env.setCap( cap );
				return old;
			};
			
			case AST.kinds.SELECT: 
			return function( ast, env ){
				var id = ast.right;
				var rec = unAll( check( ast.left, env ), true, true );
				
				assert( rec.type === types.RecordType ||
					("Invalid field selection '"+id+"' for '"+rec+"'"), ast );

				var res = rec.select(id);				
				assert( res !== undefined || ("Invalid field '" + id + "' for '"+rec+"'"), ast );
				return res;
			};
			
			case AST.kinds.CALL: 
			return function( ast, env ){
				var fun = unAll( check( ast.fun, env ), true, true );
				
				assert( fun.type === types.FunctionType ||
					('Type '+fun.toString()+' not a function'), ast.fun );

				var arg = check( ast.arg, env );
				var fun_arg = fun.argument();
				
				// attempts to match given argument with expected one
				// this is necessary since parts of the argument may have been
				// manually stacked and other should be implicitly put there.
				arg = autoStack( arg, fun_arg, env, ast.arg );
						
				assert( subtypeOf( arg, fun_arg ) ||
					("Invalid call: expecting '"+fun_arg+"' got '"+arg+"'"), ast.arg );
				
				// auto-unstack return
				var res = unstack( fun.body(), env, ast );
				assert( res !== undefined || ("Unstack error on " + fun.body()), ast.exp );
				return res;
			};
			
			case AST.kinds.DEFINITION_TYPE:
			return function( ast, env ){
				var id = ast.name;
				var args = ast.args;
				var t_args = typedefs_args[id];
				
				assert( t_args !== undefined || ('Unknown typedef: '+id), ast);
				assert( t_args.length === args.length ||
					('Argument number mismatch: '+args.length+' vs '+t_args.length), ast);

				var arguments = new Array(args.length);
				for(var i=0;i<args.length;++i){					
					var tmp = check( args[i], env );

					if( t_args[i].type === types.LocationVariable ){
						assert( ( tmp.type === types.LocationVariable ) ||
							( 'Argument '+i+' is not LocationVariable: '+tmp.type ), 
							args[i] );
					}
					
					if( t_args[i].type === types.TypeVariable ){
						assert( ( tmp.type !== types.LocationVariable ) ||
							( 'Argument '+i+' should not be LocationVariable' ), 
							args[i] );
					}
					
					arguments[i] = tmp;
				}
				
				return new DefinitionType(id,arguments);
			};
			
			case AST.kinds.TYPE_APP: 
			return function( ast, env ){
				var exp = check( ast.exp, env );
				exp = unAll(exp, true, true);
				assert( exp.type === types.ForallType || 
					('Not a Forall '+exp.toString()), ast.exp );
				
				// FIXME: not checking that it's the correct kind!
				var packed = check(ast.id, env);
				return substitution( exp.inner(), exp.id(), packed );
			};
			
			case AST.kinds.TAGGED: 
			return function( ast, env ){
				var sum = new SumType();
				var tag = ast.tag;
				var exp = check(ast.exp, env);
				sum.add( tag, exp);
				if( exp.type === types.BangType ){
					sum = new BangType(sum);
				}
				return sum;
			};
			
			case AST.kinds.TUPLE_TYPE:
			case AST.kinds.TUPLE: 
			return function( ast, env ){
				// Note that TUPLE cannot move to the auto-bang block
				// because it may contain pure values that are not in the
				// typing environment and therefore, its type is only bang
				// or not as a consequence of each field's type and not just
				// what it consumes from the environment
				var rec = new TupleType();
				var bang = true;
						
				for(var i=0;i<ast.exp.length;++i){
					var value = check( ast.exp[i], env );
					rec.add(value);
					if( value.type !== types.BangType )
						bang = false;
				}
				
				if( bang )
					rec = new BangType(rec);

				return rec;
			};
			
			case AST.kinds.SHARE: 
			return function( ast, env ){
				var cp = check( ast.type, env );
				
				// The following is a convenient idiom to enable both sharing
				// a type, or just giving a location variable that will serve to
				// search the linear typing environment for such capability.
				// This way, there's less to type (and no need for subtype)...
				var cap = undefined;
				if( cp.type === types.LocationVariable ){
					cap = env.removeNamedCap( cp.name() );
				}else{
					cap = env.removeCap(
						function(c){ return subtypeOf(c,cp); } );
				}
				
				assert( cap !== undefined || ("No capability to '"+cp+"'"), ast );
				
				var left = check( ast.a, env );
				var right = check( ast.b, env );
				
				/* Protocol conformance, goes through all possible "alias
				 * interleaving" and ensure all those possibilities are considered
				 * in both protocols.
				 */
				checkProtocolConformance(cap, left, right, ast);
				
				env.setCap( unAll(left, false, true) );
				env.setCap( unAll(right, false, true) );
				// returns unit
				return new BangType(new RecordType());
			};
			
			case AST.kinds.FOCUS: 
			return function( ast, env ){
				var locs = ast.types;
				for( var i=0; i<locs.length ; ++i ){
					var cp = check( locs[i], env );
					
					// same idea as in 'SHARE'
					var cap = undefined;
					if( cp.type === types.LocationVariable ){
						cap = env.removeNamedCap( cp.name() );
					}else{
						cap = env.removeCap(
							function(c){
								if( c.type === types.RelyType ){
									return subtypeOf(c.rely(),cp);
								}
								return false;
							} );
					}
					
					// if failed to find this one, continue to try on the next of
					// the list given on 'focus'.
					if( cap === undefined )
						continue;
				
					env.focus( cap );	
					return new BangType(new RecordType());
				}
				
				assert( cap !== undefined || ("Focus failed to find capability"), ast );
			};
			
			case AST.kinds.DEFOCUS: 
			return function( ast, env ){
				var dg = env.defocus_guarantee();
				
				var res = autoStack( null , dg.guarantee(), env, ast );
				
				assert( subtypeOf( res, dg.guarantee() ) ||
					('Not at Guarantee, expecting "'+dg.guarantee()+'" got '+res),
					ast );
				
				env.defocus();
				
				unstackType(
					unAll( dg.rely(), false, true) 
					, env, ast );
				return new BangType(new RecordType());
			};
			
			// TYPES
			case AST.kinds.RELY_TYPE: 
			return function( ast, env ){
				var rely = check( ast.left, env );
				var guarantee = check( ast.right, env );
				if( guarantee.type !== types.GuaranteeType ){
					guarantee = new GuaranteeType( guarantee, NoneType );
				}
				return new RelyType( rely, guarantee );
			};
			
			case AST.kinds.GUARANTEE_TYPE: 
			return function( ast, env ){
				var guarantee = check( ast.left, env );
				var rely = check( ast.right, env );
				return new GuaranteeType( guarantee, rely );
			};
			
			case AST.kinds.REF_TYPE: 
			return function( ast, env ){
				var id = ast.text;
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast );
				
				return new ReferenceType( loc );
			};
			
			case AST.kinds.EXISTS_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				var variable;
				if( isTypeVariableName(id) )
					variable = new TypeVariable(id);
				else
					variable = new LocationVariable(id);
				
				e.setType( id, variable );

				return new ExistsType( variable, check( ast.type, e ) );
			};
			
			case AST.kinds.FORALL_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				var variable;
				if( isTypeVariableName(id) )
					variable = new TypeVariable(id);
				else
					variable = new LocationVariable(id);

				e.setType( id, variable );

				return new ForallType( variable, check( ast.exp, e ) );
			};
			
			case AST.kinds.RECURSIVE_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var e = env.newScope();
				
				assert( isTypeVariableName(id) ||
					'Type Variables must be upper-cased', ast );
					
				var variable = new TypeVariable(id);
				e.setType( id, variable );
				return new RecursiveType( variable, check( ast.exp, e ) );
			};
						
			case AST.kinds.NONE_TYPE:
			return function( ast, env ){
				return NoneType;
			};
				
			case AST.kinds.BANG_TYPE:
			return function( ast, env ){
				return new BangType( check( ast.type , env ) );
			};
			
			case AST.kinds.FUN_TYPE: 
			return function( ast, env ){
				return new FunctionType( 
					check( ast.arg, env ),
					check( ast.exp, env )
				);
			};
			
			case AST.kinds.CAP_TYPE: 
			return function( ast, env ){
				var id = ast.id;
				var loc = env.getType( id );
				
				assert( (loc !== undefined && loc.type === types.LocationVariable) ||
					('Unknow Location Variable '+id), ast);

				var type = check( ast.type, env );
				type = purify( type );
				return new CapabilityType( loc, type );
			};
			
			case AST.kinds.STACKED_TYPE: 
			return function( ast, env ){
				return new StackedType(
					check( ast.left, env ),
					check( ast.right, env )
				);
			};
			
			case AST.kinds.CAP_STACK: 
			return function( ast, env ){
// FIXME recursive types?
				var exp = check( ast.exp, env );
				var cap = check( ast.type, env );
				
// FIXME broken
				cap = unAll(cap,false,true);
				
				var c = autoStack ( null, cap, env, ast.type );
				// make sure that the capabilities that were extracted from 
				// the typing environment can be used as the written cap.
//debugger
				assert( subtypeOf( c , cap ) ||
					('Incompatible capability "'+c+'" vs "'+cap+'"'), ast.type );
				return new StackedType( exp, cap );
			};
			
			case AST.kinds.RECORD_TYPE: 
			return function( ast, env ){
				var rec = new RecordType();
				for( var i=0; i<ast.exp.length ; ++i ){
					var field = ast.exp[i];
					var id = field.id;
					var value = check( field.exp, env );
					assert( rec.add(id, value) ||
						("Duplicated field '" + id + "' in '"+rec+"'"), field);
				}
				return rec;
			};
			
			case AST.kinds.PRIMITIVE_TYPE:
			return function( ast, env ){
				// any primitive type is acceptable but only ints, booleans
				// and strings have actual values that match a primitive type.
				return new PrimitiveType(ast.text);
			};

			default:
				// Tries to mark it as pure, if it does not use any of the
				// parent environment. This check is done by counting the
				// number of elements of the parent environment (on entry)
				// and comparing with its value on exit. If it is the same
				// then it did not touch it.
				// This only holds true because any use of the linear env
				// will push elements down, never to be recovered in here.
				return function( ast, env ){
					return tryBang( ast, env, setupBangAST(kind) );
				};
		}

	}
	
	// all following should be potentially banged if they don't use environment
	var setupBangAST = function( kind ){

		switch( kind ){
			
			case AST.kinds.FORALL: 
			return function( ast, env ){
				var id = ast.id;							
				var variable;
				if( isTypeVariableName(id) )
					variable = new TypeVariable(id);
				else
					variable = new LocationVariable(id);

				var e = env.newScope();
				assert( e.setType( id, variable ) ||
					("Type '" + id + "' already in scope"), ast );

				return new ForallType( variable, check( ast.exp, e ) );
			};

			case AST.kinds.FUN: 
			return function( ast, env ){
				var id = ast.parms.id;
				var result = null;
				var initial_size = env.size();
				var e = env.newScope();
				var arg_type = check( ast.parms.type, e );
				
				// CAREFUL: only if it is a recursive function
				// can it have a result type attached, otherwise
				// currying of multiple arguments becomes messy
				
				if( ast.rec !== null ){ // recursive function
					result = check( ast.result, e );
					assert( result !== null ||'No result type given on recursive function', ast );								
					// note that all recursive functions must be pure
					var rec_fun = new BangType(
						new FunctionType(arg_type, result)
					);
					assert( e.set( ast.rec, rec_fun ) ||
						("Identifier '" + ast.rec + "' already in scope"), ast );
				}
				
				//var unstacked = unAll(arg_type,ast, false, true); 
				var unstacked = unstack(arg_type,e,ast);
				
				assert( e.set( id, purify(unstacked) ) ||
						("Identifier '" + id + "' already in scope"), ast );

				var res = check( ast.exp, e );
				res = safelyEndScope( res, e, ast.exp );
				
				if( ast.rec !== null ){
					assert( subtypeOf( res, result ) ||
						("Invalid result type '"+res+"' expecting '"+result+"'"), ast);
					// we also need to ensure it is pure so that the
					// previously assumed bang is OK.
					assert( initial_size === env.size() ||
						'Linear recursive function.', ast );
					// use the written return type
					res = result;
				}
				
				return new FunctionType(arg_type, res);
			};
			
			case AST.kinds.RECORD: 
			return function( ast, env ){
				var rec = new RecordType();
				
				var initEnv = env.clone();
				var endEnv = null;

				for(var i=0;i<ast.exp.length;++i){
					var field = ast.exp[i];
					var id = field.id;
					
					var value;
					if( endEnv === null ){
						value = check( field.exp, env );
						endEnv = env;
					}else{
						var tmp_env = initEnv.clone();
						value = check( field.exp, tmp_env );
						assert( endEnv.isEqual(tmp_env) ||
							("Incompatible effects on field '" + id + "'"), field);
					}
					assert( rec.add(id, value) ||
						("Duplicated field '" + id + "' in '"+rec+"'"), field);
				}

				return rec;
			};
			
			case AST.kinds.NUMBER:
			return function( ast, env ){
				return new PrimitiveType('int');
			};
			
			case AST.kinds.BOOLEAN:
			return function( ast, env ){
				return new PrimitiveType('boolean');
			};
			
			case AST.kinds.STRING:
			return function( ast, env ){
				return new PrimitiveType('string');
			};

			default:
			return function( ast, env ){
				error( "Not expecting " + ast.kind );
			};
		}
	};
	
	var visitor = {};
	// setup visitors
	for( var i in AST.kinds ){
		error( !visitor.hasOwnProperty(i) ||
				( 'Error @visitor, duplication: '+i ) );
		// find witch function to call on each AST kind of node
		visitor[i] = setupAST(i);
	}
	
	var check_inner = function( ast, env ){
		if( !visitor.hasOwnProperty( ast.kind ) ){
			error( 'Not expecting '+ast.kind );
		}
		return (visitor[ast.kind])( ast, env );
	}
	
	var type_info;
	var unique_counter;
	var typedefs, typedefs_args;
	
	exports.check = function(ast,typeinfo,loader){
		// This is a hack of some sort to enable testing of the inner components
		// of the type checker... not very pleasant trick, but useful for brevity.
		if( ast instanceof Function ){
			ast(exports,subtypeOf,equals);
			return null;
		}
		
		// stats gathering
		var start = new Date().getTime();
		type_info = [];
		
		try{
			error( (ast.kind === AST.kinds.PROGRAM) || 'Unexpected AST node' );
				
			// reset typechecke's state.
			unique_counter = 0;
			typedefs = {};
			typedefs_args = {};
			var env = new Environment(null);
				
			if( ast.imports !== null ){
			 	// loader does not need to be provided, but all imports are errors
				error( loader !== undefined || 'Missing import loader' );
				
				var libs = ast.imports;
				for( var i=0; i<libs.length; ++i ){
					var lib = libs[i];
					var import_type = loader( lib.id, exports );
					assert( import_type !== undefined || ("Invalid import: "+lib.id), lib );
					assert( env.set( lib.id, import_type ) ||
						('Identifier '+ lib.id +' already in scope'), lib );
				}
			}
				
			if( ast.typedefs !== null ){
				// typedefs[i] - id:id, type:type, pars:pars
				
				// first phase - extract all argument definitions, note that
				// duplication is not checked at this stage
				for(var i=0;i<ast.typedefs.length;++i){
					var it = ast.typedefs[i];
					var args = [];
					var pars = it.pars;

					// only do this if there are any actual definition parameters
					if( pars !== null ){
						args = new Array(pars.length);
						
						for(var j=0;j<pars.length;++j){
							var n = pars[j];
							args[j] = isTypeVariableName(n) ? 
								new TypeVariable(n) : new LocationVariable(n);
						}
					}
					typedefs_args[ast.typedefs[i].id] = args;
				}
				
				// must avoid attempting to unfold what is not yet definied.
				var tmp_unfold = unfoldDefinition;
				unfoldDefinition = function(t){ return t; };

				for(var i=0;i<ast.typedefs.length;++i){
					var type = ast.typedefs[i];
					assert( !typedefs.hasOwnProperty(type.id) ||
						('Duplicated typedef: '+type.id), type )
						
					var tmp_env = env.newScope();
					var args = typedefs_args[type.id];
					
					// sets the variables, if there are any to setup
					if( args !== null ){
						for(var j=0;j<args.length;++j){
							// should be both for LocationVariables and TypeVariables
							tmp_env.setType( args[j].name(), args[j] );
						}
					}
					
					// map of type names to typechecker types.
					typedefs[type.id] = check( type.type, tmp_env );
				}
				
				// ok to allow unfoldings
				unfoldDefinition = tmp_unfold;
				
			}
			return check( ast.exp, env );
		} finally {
			if( typeinfo ){
				typeinfo.diff = (new Date().getTime())-start;
				typeinfo.info = type_info; 
			}
		}

	};
	return exports;
})(AST,assertF); // required globals

