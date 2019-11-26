(*Yes, we're violating our rules by opening Ast...it's okay... *)
open Ast
open Unparse
type location = int
type ('a, 'b) mutable_alist = ('a * 'b ref) list ref
datatype rubevalue = 
	RNIL
|	RINT of int
|	RSTR of string
|	RLOC of int
type id = string
type name = string
type clsname = string
type object = { class: clsname, fields: (id, rubevalue) mutable_alist }
type locals = (name, rubevalue) mutable_alist
type heap = (location, object) mutable_alist
val empty_A : unit -> locals = fn () => ref []
val empty_H : unit -> heap = fn () => ref []
type config = locals * heap * expr
type result = locals * heap * rubevalue

fun defined_class (p:rube_prog) (c:string):bool = 
	let fun class_exists cls c =
		if (#cls_name cls) = c then
			true
		else
			false
	    fun find_class [] c = false
		  | find_class (x::xs) c = 
			if class_exists x c then
				true
			else
				find_class xs c
	in find_class (#prog_clss p) c
	end

fun lookup_meth (p:rube_prog) (c:string) (m:string):meth option = 
	let fun get_class [] c = NONE (* get class from prog_clss*)
		  | get_class (x::xs) c = 
		  	if (#cls_name x) = c then
		  		SOME x
		  	else
		  		get_class xs c

		fun convert NONE = raise Fail "Undefined program class"
		  | convert (SOME x) = x
		
		fun meth_list NONE m = [] (* get methods list from class*)
		  | meth_list (SOME x) m = #cls_meths x

		fun super_meth [] m = NONE
		  | super_meth (x::xs) m = 
		  	if (#meth_name x) = m then
		  		SOME x
		  	else
		  		super_meth xs m
		 (* NONE case: try to find method in superclass *)
		fun meth [] m = super_meth (meth_list (get_class (#prog_clss p) (#cls_super (convert (get_class (#prog_clss p) c)))) m) m 
		  | meth (x::xs) m = 
		  	if (#meth_name x) = m then
		  		SOME x
		  	else
		  		meth xs m
	in meth (meth_list (get_class (#prog_clss p) c) m) m
	end

(* Helper functions for run *)
fun lookup k (ref alist) = 
	let fun find_k [] = NONE
		  | find_k ((k', ref v')::rest) = 
		  	if k = k' then
		  		SOME v'
		  	else
		  		find_k rest
	in find_k alist
	end

fun update (env as ref alist) (k, v) = 
	let fun extend_or_update [] = env := (k, ref v) :: !env
		  | extend_or_update ((k', v') :: rest) = 
		  	if k = k' then
		  		v' := v
		  	else
		  		extend_or_update rest
	in extend_or_update alist
	end

val last_loc = ref ~1
fun fresh_location () = 
	let val () = last_loc := !last_loc + 1
	in !last_loc
	end

fun rubeval e = 
  (case e
	of (A, H, rv) => rv)

fun extract_option opt s =
  (case opt
  	of NONE => raise Halt s
  	 | (SOME v) => v)

fun read_location option_location =
  (case option_location
  	 of NONE => raise Halt "self not bound in A"
	  | (SOME (RLOC n)) => n
	  | (SOME _) => raise Halt "Expects self to be RLOC") 

fun equal x y =
	case x = y
	  of true => RINT 1
	  | false => RNIL

fun printvar x =
 	let val p = 
  	  	  (case x
  	         of RNIL => print "nil"
  	          | (RINT n) => print (Int.toString n)
  	          | (RSTR s) => print s
  	          | (RLOC n) => print "Undefined behavior") 
	in RNIL
	end 

fun eval p (A, H, ENil) = (A, H, RNIL)
  | eval p (A, H, EInt n) = (A, H, RINT n)
  | eval p (A, H, ESelf) = (A, H, extract_option (lookup "self" A) "Self not bound in A")
  | eval p (A, H, EString s) = (A, H, RSTR s)
  | eval p (A, H, ELocRd s) = 
	let val option_var = lookup s A
		val read_var = extract_option option_var "Id not bound in A"
	in (A, H, read_var)
	end

  | eval p (A, H, ELocWr (s, e)) = 
	let val v = eval p (A, H, e)
		val rv = rubeval v
		val () = update A (s, rv)
	in (A, H, rv)
	end

  | eval p (A, H, EFldRd s) = 
  	let val option_location = lookup "self" A
		val location = read_location option_location
		  	  
		val option_object = lookup location H
		val read_object = extract_option option_object "Object not bound in H"

		val {class = _, fields = fs} = read_object
		val option_field = lookup s fs
		val read_field =	
		  (case option_field
		  	 of NONE => RNIL
		  	  | (SOME rv) => rv)
	in (A, H, read_field)
	end 

  | eval p (A, H, EFldWr (s, e)) = 
    let val option_location = lookup "self" A
  		val location = read_location option_location

  		val option_object = lookup location H
  		val read_object = extract_option option_object "Object not bound in H"

  		val {class = _, fields = fs} = read_object
  	    val v = eval p (A, H, e)
  		val rv = rubeval v
  		val () = update fs (s, rv)
  	in (A, H, rv)
  	end 

  | eval p (A, H, EIf (e1, e2, e3)) =
  	let val guard = eval p (A, H, e1)
  		val rv = rubeval guard
  		val evaluate =
  		  (case rv
  		  	 of RNIL => eval p (A, H, e3)
  		  	  | _ => eval p (A, H, e2))
  	in evaluate
  	end

  | eval p (A, H, ESeq (e1, e2)) =
    let val v1 = eval p (A, H, e1)
    	val v2 = eval p (A, H, e2)
    in v2
    end

  | eval p (A, H, ENew s) = (* If class is String or Integer then we need special handling*)
  	let val has_class = 
  		  (case s
  		  	 of "nil" => raise Halt "Cannot instantiate Bot"
  		  	  | _ => defined_class p s)

  		fun instantiate_cls () = 
  		  let val l = fresh_location ()
  		  	  val new_cls = {class = s, fields = ref []}
  		  	  val () = update H (l, new_cls) (*update H with (location, object)*)
  		  	  val return = 
  		  	    (case s
  		  	       of "String" => RSTR ""
  		  	        | "Integer" => RINT 0
  		  	        | _ => RLOC l)
  		  in return
  		  end
  		
  		val rv =
  	      (case (has_class, s)
  	      	 of (true, _) => instantiate_cls ()
  	      	  | (false, "String") => instantiate_cls ()
  	      	  | (false, "Integer") => instantiate_cls ()
  	      	  | (false, _) => raise Halt ("No such class " ^ s))

  	in (A, H, rv)
  	end

  | eval p (A, H, EInvoke (e, s, es)) =
    let val rv = rubeval (eval p (A, H, e))
    	val vs = List.map (fn x => eval p (A, H, x)) es
    	val r_vs = List.map (fn x => rubeval x) vs
    	
		(* Evaluate built in methods*)
		fun built_in receiver meth args =
			let val value = 
		  	  (case (receiver, meth, args)
	  		 	 of (RINT n, "+", [RINT m]) => RINT (n+m)
	   		  	  | (RINT n, "+", _) => raise Halt "Non-Integer passed as argument"
	   		  	  | (RSTR s, "+", [RSTR s']) => RSTR (s ^ s')
	   		  	  | (RSTR s, "+", _) => raise Halt "Non-String passed as argument"
	   		  	  | (RINT n, "-", [RINT m]) => RINT (n-m)
	   		  	  | (RINT n, "-", _) => raise Halt "Non-Integer passed as argument"
	   		  	  | (RINT n, "*", [RINT m]) => RINT (n*m)
	   		  	  | (RINT n, "*", _) => raise Halt "Non-Integer passed as argument"
	   		  	  | (RINT n, "/", [RINT m]) => RINT (n div m)
	   		  	  | (RINT n, "/", _) => raise Halt "Non-Integer passed as argument"
	   		  	  | (RINT n, "equal?", [RINT m]) => equal n m
		  	  	  | (RSTR n, "equal?", [RSTR m]) => equal n m
		  	  	  | (RNIL, "equal?", [RNIL]) => equal RNIL RNIL
		  	  	  | (RLOC n, "equal?", [RLOC m]) => equal n m
		  	  	  | (RINT n, "equal?", _) => RNIL
		  	  	  | (RSTR n, "equal?", _) => RNIL
		  	  	  | (RSTR s, "to_s", []) => RSTR s
		  	  	  | (RINT n, "to_s", []) => RSTR (Int.toString n)
		  	  	  | (RNIL, "to_s", []) => RNIL
		  	  	  | (RNIL, "print", []) => printvar RNIL
		  	  	  | (RSTR s, "print", []) => printvar (RSTR s)
		  	  	  | (RINT n, "print", []) => printvar (RINT n)
		  	  	  | (RSTR s, "length", []) => RINT (size s)
		  	  	  | (_, _, _) => raise Halt "No such method") 
			in value
			end


		fun non_built_in m l = 
			let val meth = extract_option m "No such method"
				val {meth_name = _, meth_args = arg_list, meth_body = body} = meth

				(* bind object to self*)
				val A' = empty_A ()
				val () = update A' ("self", RLOC l)
				val args = ListPair.zipEq (arg_list, r_vs)
				(*adds arguments to env A *)
				val () = List.app (fn x => update A' x) args 

				val value = 
		  	  	  (case eval p (A', H, body)
		  	     	 of (_, _, v) => v)
		  	in value
		  	end

    	fun invoke_meth l =
    		let val option_object = lookup l H (* returns an object *)	
			val object = extract_option option_object "Object not bound in H"

			val {class = cls, fields = _} = object (* get cls name from object*)

			val option_meth = lookup_meth p cls s 
			(* get meth from object*)
			val value = case option_meth
			  			  of NONE => built_in rv s r_vs
			   			   | (SOME m) => non_built_in option_meth l
			in value
			end

    	val value = 
    	  (case rv
    	  	 of (RLOC n) => invoke_meth n
    	  	  | _ => built_in rv s r_vs)
    	
	in (A, H, value)
	end

fun run (p:rube_prog):string = 
	let val {prog_clss=cls, prog_main=e} = p

		fun to_s(RNIL: rubevalue):string = "nil"
		  | to_s(RINT n) = Int.toString n
		  | to_s(RSTR s) = s
		  | to_s _ = raise Fail "not implemented"

		val A = empty_A ()
		val H = empty_H ()

		val l = fresh_location ()
  		val new_cls = {class = "Object", fields = ref []}
  		val () = update H (l, new_cls)
  		val () = update A ("self", RLOC l)

		val (A', H', v) = eval p (A, H, e)
		
 	in to_s v
	end