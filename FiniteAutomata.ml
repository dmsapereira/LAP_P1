(* FiniteAutomata module body *)

(* 
Aluno 1: ????? mandatory to fill
Aluno 2: ????? mandatory to fill

Comment:

?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????
?????????????????????????

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

let rec print_list l=
	match l with
	[] ->()
	| x::xs -> print_string x; print_string "\n";print_list xs
;;

let rec print_list_list ll=
	match ll with
	[]->();
	| x::xs -> print_list x; print_string "Next List\n"; print_list_list xs
;;

let rec getAlphabetList ts= (*Creates a list of the symbols of every state. With repeats and not sorted*)
    match ts with
    []-> []
    | x::xs -> 
    	match x with
    	 (_,s,_)-> s::(getAlphabetList xs)
;;

let rec getStateList ts= (*Creates a list of the states of an Automata. Regardless of repeats and order*)
    match ts with
    []-> []
    | x::xs -> 
    	match x with
    	 (s1,_,s2)-> [s1;s2]@(getStateList xs)
;;

let get1 x=
	match x with (p1,_) -> p1
;;

let get2 x=
	match x with (_,p2) -> p2
;;

let rec isTransitionResultDeterministic t ts=(*Evaluates if a transition t is deterministic*)
	match t with
	(s1,sy,s2) -> match ts with
					[]-> true
					| x::xs -> match x with
								(s3,sy2,s4)-> if (s1=s3)&&(sy=sy2)&&(s2<>s4) then false else isTransitionResultDeterministic t xs
;;



let rec statesReachableFrom s ts= (*Returns a list of the states that are reachable from the state s*)
	match ts with 
	[] -> []
	| x::xs -> match x with
				(s1,sy,s2) -> if s1=s then s2::(statesReachableFrom s xs) else statesReachableFrom s xs
;;

let rec stateListContainsAcceptedState a_s sl= (*Evaluates if the state list sl contains at least one accepted state*)
	match a_s with
	[] -> false;
	| x::xs -> if List.mem x sl then true else stateListContainsAcceptedState xs sl
;;

(* PUBLIC FUNCTIONS *)
let getAlphabet fa =
	canonical(getAlphabetList fa.transitions)
;;


let getStates fa =
	canonical (getStateList fa.transitions)
;;

let gcut s ts =
	let rec gcutHelper t=
		match t with
		(s1,sy,s2) -> if s1=s then true else false in
    List.partition gcutHelper ts
;;

let determinism fa =
	let rec isDeterministic ts= (*Evaluates if a efa is deterministic*)
	match ts with
	[] -> true
	| x::xs -> match x with (s1,_,_) -> if isTransitionResultDeterministic x (get1(gcut s1 ts)) then isDeterministic xs else false in
    isDeterministic fa.transitions
;;

let reachable fa =
	canonical (statesReachableFrom fa.initialState (get1(gcut fa.initialState fa.transitions)))
;;

let productive fa =(*Doesn't work*)
(*
	let rec isStateProductive s ts=
	match ts with
	[] -> false
	| x::xs-> if stateListContainsAcceptedState fa.acceptStates ts then true else isStateProductive s xs in

	let rec productiveHelper sl ts=
	match sl with
	[] -> false
	| x::xs -> if isStateProductive x (get1 (gcut x fa.transitions)) in

	productiveHelper (getStates fa) fa.transitions
	*)
	canonical []
;;


let accept w fa = (*Works but can replace thos fa.transitions with smaller lists*)

	let rec nextState currentSymbol currentState ts=
		match ts with
		[] -> (fa.initialState)
		| x::xs -> match x with (s1,sy,s2) -> if (s1=currentState && sy=currentSymbol) then s2 else nextState currentSymbol currentState xs in 
    
    let rec stateMachine wrd currentState=
    	match wrd with
    	[] -> false
    	| x::xs -> if (List.mem (nextState x currentState (get1(gcut currentState fa.transitions))) fa.acceptStates) then true else stateMachine xs (nextState x currentState (get1(gcut currentState fa.transitions))) in 
    
    stateMachine w fa.initialState
;;

let generate n fa =
	(*let rec ins x ll=
	match ll with
		[] -> [[x]]
		| l::ls -> (x::l)::ins x ls
	;;

	let rec power l=
	match l with
		[]-> [[]]
		| x::xs -> power xs @ ins x (power xs)
	;;

	let rec listOfAllCharCombinations c n=
		let rec listOfCharNtimes c n=
			if n=0 then [] else c::(listOfCharNtimes c (n-1)) in

		if n=0 then [] else (listOfCharNtimes c n)::listOfAllCharCombinations c (n-1)
	;;

	let rec listOfRepeated l n=
	match l with
		[]->[[]]
		| x::xs -> (listOfAllCharCombinations x n)@(listOfRepeated xs n) 
	;;

    (power (getStates fa))@(listOfRepeated (getStates fa) (List.length (getStates fa)))
	*)

	(*let rec generateWordCombinations n wl=


	let rec generateWords n wl=(*Gera todas as combinaçoes de wl, em tamanho n*)
	if n=0 then [[]] else
		match wl with
		[]-> [[]]
		| x::xs -> x::

in
	let rec generateHelper n wl=
		if n=0 then [[]] else (generateWords n wl)@(generateHelper (n-1) wl)
in
*)
	canonical [];;
;;

let accept2 w fa =
    false
;;