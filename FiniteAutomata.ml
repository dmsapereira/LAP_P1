(* FiniteAutomata module body *)

(* 
David Pereira: 52890
Pedro Bailao:  53675 

Comment:
We swapped accept2 and generate's position because generate uses accept2
*)

(*
01234567890123456789012345678901234567890123456789012345678901234567890123456789
   80 columns
*)

type symbol = char;;       (* our symbols are represented by chars *)
type word = symbol list;;  (* our words are represented by lists of symbols *)

type state = string;;      (* our states are represented by strings *)
type states = state list;;

type transition =
    state   (* state *)
  * symbol  (* consumed input symbol *)
  * state   (* next state *)
;;
type transitions = transition list;;

type fAutomaton = {
    initialState: state;       (* Initial state *)
    transitions: transitions;  (* Transition relation *)
    acceptStates: states       (* Accept states *)
};;


(* PRIVATE DEFINITIONS *)

let abc = {
    initialState = "START" ;
    transitions = [
            ("START",'a',"A"); ("START",'b',"START"); ("START",'c',"START");
                                                      ("START",'d',"START");
            ("A",'a',"A"); ("A",'b',"AB"); ("A",'c',"START"); ("A",'d',"START"); 
            ("AB",'a',"A"); ("AB",'b',"START"); ("AB",'c',"SUCCESS");
                                                    ("AB",'d',"START");
            ("SUCCESS",'a',"SUCCESS"); ("SUCCESS",'b',"SUCCESS");
                         ("SUCCESS",'c',"SUCCESS"); ("SUCCESS",'d',"SUCCESS")
        ];
    acceptStates = ["SUCCESS"]
};;

let abcND = {
    initialState = abc.initialState ;
    transitions = abc.transitions @ [
            ("SUCCESS",'a',"UNPRODUCTIVE");
            ("UNREACHABLE",'a',"SUCCESS");
            ("SUCCESS",'e',"UNPRODUCTIVE"); ("UNPRODUCTIVE",'a',"UNPRODUCTIVE")
        ];
    acceptStates = abc.acceptStates
};;

let canonical l =
    List.sort_uniq compare l
;;

let addAll symb =
    List.map (fun l -> symb::l)
;;

let flatMap f l =
    List.flatten (List.map f l)
;;

let get1 x=
	match x with (p1,_) -> p1
;;

let get2 x=
	match x with (_,p2) -> p2
;;

(*Evaluates if the state list sl contains at least one accepted state*)	
let rec stateListContainsAcceptedState a_s sl= 
	match a_s with
	[] -> false;
	| x::xs -> if List.mem x sl then true 
			   else stateListContainsAcceptedState xs sl
;;


(* PUBLIC FUNCTIONS *)

(*Creates a list of all the symbols that fa admits,
no repeats and sorted*)
let getAlphabet fa =
	let rec getAlphabetList ts= 
    match ts with
    []-> []
    | x::xs -> 
    	match x with
    	 (_,s,_)-> s::(getAlphabetList xs) in

	canonical(getAlphabetList fa.transitions)
;;

(*Creates a list of the states of an Automata.
 without repeats and sorted*)
let getStates fa =
	let rec getStateList ts= 
    match ts with
    []-> []
    | x::xs -> 
    	match x with
    	 (s1,_,s2)-> [s1;s2]@(getStateList xs) in

	canonical (getStateList fa.transitions)
;;

		(*Given a state s and a transition list ts returns two lists
		 One has all the the transitions that originate from s
		 and the other has the remainder  *)	
let gcut s ts =
	let rec gcutHelper t=
		match t with
		(s1,sy,s2) -> if s1=s then true else false in
    List.partition gcutHelper ts
;;

(*PRIVATE FUNCTIONS*)

(*Given a transition list returns all the states that are "next states"*)
(*We placed it amidst the public functions to avoid repeated code*)
let rec getFinalStatesFromTransitonList tl=
	match tl with
	[]-> []
	| (_,_,s)::xs -> s::getFinalStatesFromTransitonList xs 
;;

(*Returns a list of the states that are reachable from the state s*)
(*We placed it amidst the public functions to avoid repeated code*)
let rec statesReachableFrom sl tl=
	match sl with
	[] -> []
	| x::xs -> (getFinalStatesFromTransitonList (get1(gcut x tl)))@
	(statesReachableFrom (getFinalStatesFromTransitonList
	(get1(gcut x tl))) (get2(gcut x tl)))@(statesReachableFrom xs tl) 
;;

(*BACK TO PUBLIC FUNCTIONS*)

(*Evaluates if a efa is deterministic*)
let determinism fa =
	(*Evaluates if a transition t is deterministic*)
	let rec isTransitionResultDeterministic t ts=
	match t with
	(s1,sy,s2) -> match ts with
	[]-> true
	| (s3,sy2,s4)::xs -> if (s1=s3)&&(sy=sy2)&&(s2<>s4) then false 
					  	 else isTransitionResultDeterministic t xs

		(*Checks if a given FiniteAutomata is deterministic*)
	let rec isDeterministic ts= 
	match ts with
	[] -> true
	| x::xs -> match x with 
	(s1,_,_) -> if isTransitionResultDeterministic x (get1(gcut s1 ts)) 
	then isDeterministic xs else false in

    isDeterministic fa.transitions
	;;

(*Lists all the states that are reachable following a path 
from a the initial state*)
let reachable fa =
	canonical(statesReachableFrom [fa.initialState] fa.transitions)
;;

let productive fa =
		(*Calculates the states that are able to reach an acceptable state*)
	let rec auxProductive sl=
		match sl with 
		[]-> []
		| x::xs-> if (stateListContainsAcceptedState fa.acceptStates 
			(statesReachableFrom [x] fa.transitions)) 
			then x::auxProductive xs else auxProductive xs in

	canonical(auxProductive (getStates fa))
;;
let accept w fa =
		(*Return next state*)
	let rec nextState currentSymbol currentState ts=
		match ts with
		[] -> "FAIL"
		| (s1,sy,s2)::xs -> 
			if (s1=currentState && sy=currentSymbol) then s2
			else nextState currentSymbol currentState xs in 
    	(* Simulates the behavior of the FinitaAutomata *)
    let rec stateMachine wrd currentState=
    	if currentState="FAIL" then false else(*State FAIL is a state that is 
    	never present in a transition, therefore its presence means that 
    	an unexpected case was found*)
    	match wrd with
    	[] -> false
    	| x::xs -> if (List.mem (nextState x currentState 
    				(get1(gcut currentState fa.transitions))) fa.acceptStates) 
    				then true 
    				else stateMachine xs (nextState x currentState 
    				(get1(gcut currentState fa.transitions))) in
    
    stateMachine w fa.initialState
;;

let accept2 w fa = 
		(* Return next state *)
	let rec nextState currentSymbol currentState ts=
		match ts with
		[] -> "FAIL"
		| (s1,sy,s2)::xs -> 
			if (s1=currentState && sy=currentSymbol) then s2
			else nextState currentSymbol currentState xs in 
    	(* Simulates the behavior of the FinitaAutomata *)
    let rec stateMachine wrd currentState=
    	if currentState="FAIL" then "FAIL" else(*State FAIL is a state that is 
    	never present in a transition, therefore its presence means that 
    	an unexpected case was found*)
    	match wrd with
    	[] -> currentState
    	| x::xs -> stateMachine xs (nextState x currentState 
    				(get1(gcut currentState fa.transitions))) in 
    	(*Checks if the the final state is an acceptable state*)
    if  ( List.mem (stateMachine w fa.initialState) fa.acceptStates ) 
    			then true else false  

;;

let generate n fa =
		(*Generates a combination for each symbol in sl with the lists of ll*)
	let rec addAllMachine sl ll=
		match sl with
		[] -> []
		| x::xs -> (addAll x ll)@(addAllMachine xs ll) in
		(*Generates a combination of size n of the symbols in sl*)
	let rec generateHelper n sl=
	if n=0 then [[]] else addAllMachine sl (generateHelper (n-1) sl) in   
		(*Filters the results of generateHelper
		leaving only acceptable words*)
	let rec accept_filter wl=
		match wl with
		[]-> []
		| x::xs -> if accept2 x fa then x::accept_filter xs 
				   else accept_filter xs in

	accept_filter (generateHelper n (getAlphabet fa))
;;