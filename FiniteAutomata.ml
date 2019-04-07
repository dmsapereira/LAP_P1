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

let rec getAlphabetList t=
    match t with
    []-> []
    | x::xs -> 
    	match x with
    	 (_,s,_)-> s::(getAlphabetList xs)
;;

let rec getStateList t=
    match t with
    []-> []
    | x::xs -> 
    	match x with
    	 (s1,_,s2)-> [s1;s2]@(getStateList xs)
;;

(* PUBLIC FUNCTIONS *)
let getAlphabet fa =
	match fa with
     {initialState=i; transitions=t; acceptStates=a}-> canonical(getAlphabetList t)
;;


let getStates fa =
	match fa with
    {initialState=i; transitions=t; acceptStates=a} -> canonical (getStateList t)
;;

let gcut s ts =
	let rec gcutHelper t=
		match t with
		(s1,sy,s2) -> if s1=s then true else false in
    List.partition gcutHelper ts
;;

let determinism fa =
    false
;;

let reachable fa =
    canonical []
;;

let productive fa =
    canonical []
;;

let accept w fa =
    false
;;

let generate n fa =
    canonical []
;;

let accept2 w fa =
    false
;;

(*TESTES*)
getAlphabet abcND;;

