(* The set is represented as a list with no duplicates. *)
module Ls =
struct 
  let member x s = List.mem x s
  
  let rec union s1 s2 = match s1 with
      [] -> s2
    | x :: xs -> if (member x s2) then union xs s2 else [x] @ union xs s2 

end ;;                                                                                                                  
(* end of Ls module *)


(* The representation for the predicate*)
type atom = V of variable | Node of symbol * (atom list)
and
  variable = string
and
  symbol = string*int;;
  

(* data type to represent the structure of a legitimate Propositional Horn
   Clause program.  *)
type clause = Rule of atom * atom list
            | Fact of atom;;

type goal = Empty | Goal of atom;;

type program = clause list;;


(* Distinct Variables of the tree
   Time Complexity = O(size of tree / term)
   Space Complexity = O(size of tree) *)
let rec vars tree = match tree with
    V s -> [s] 
  | Node ((sym, arity), terms) -> List.fold_left (fun x y -> Ls.union x y)
                                    [] (List.map (fun ele -> vars ele) terms);; 


(* The substitution s is represented in a hash table of type (variable, term)*)

(*  Give a term tree and a substitution sub, 
    applies the (Unique Homomorphic Extension of) sub to tree  
    Time Complexity: O(size of tree)
    Space Complexity: O(size of tree)  *)
let rec subst tree sub = match tree with
    V s -> if  Hashtbl.mem sub (s) then Hashtbl.find sub (s) else V s
  | Node ((sym, arity), terms) -> 
      Node ((sym, arity), List.map (fun ele -> subst ele sub) terms);;



let subst_all body sub = 
  List.fold_left (fun x y -> y::x) [] 
    (List.map (fun ele -> subst ele sub) body)
;; 


let rec beautify results variables = match results with
    [] -> []
  | (decision, assignment) :: resultst ->
      if decision
      then 
        [(decision, Hashtbl.fold 
            (fun k v acc -> 
               if Ls.member k variables 
               then (k, v) :: acc 
               else acc) assignment [])] @ beautify resultst variables
      else
        beautify resultst variables;;


(* Raise below exception in case term t1 and t2 are not
unifiable *)
exception NOT_UNIFIABLE

(*  Give a term tree and a substitution sub, 
    applies the (Unique Homomorphic Extension of) sub to tree  
    Time Complexity: O((size of tree)^2 * number of variables)
    Space Complexity: O(size of tree * number of variables)  *)

let mgu term1 term2 = 
  (* Get the substitution which maps the variables with itself*)
  let id variables = let sub = Hashtbl.create 100 in
    begin
      (List.map
         (fun ele -> Hashtbl.add sub ele (V ele))
         variables);
      sub
    end
  in
  let occurs_check var term = if Ls.member var (vars term) then true else false
  in
  let rec zip paired_lists =  match paired_lists with
    | [], [] -> []
    | x1::y1, x2::y2 -> (x1, x2)::(zip (y1, y2))
    | _, _ -> failwith "The two terms are not of same arity" 
  in 
  (* Give two substitution sub1 and sub2, 
     Compose sub1 and sub2 by applying sub2 on the binds of sub1
     and return sub1
     Time Complexity: O(vars of tree * size of tree) *)
  let compose sub1 sub2 = Hashtbl.iter 
      (fun k v -> Hashtbl.replace sub1 k (subst v sub2)) sub1; sub1
  in
  let rec mgu_helper term1 term2 unif = match term1, term2 with
      V t1, V t2 -> if t1 = t2 then unif
        else begin Hashtbl.add unif t1 (V t2); unif end
    | V t1, Node((sym, 0), []) -> Hashtbl.add unif t1 (Node((sym, 0), [])); 
        unif
    | V t1, t2 -> if occurs_check t1 t2 
        then raise NOT_UNIFIABLE
        else Hashtbl.add unif t1 t2; unif
    | Node((sym1, 0), []), Node((sym2, 0), []) -> if sym1 = sym2 then unif
        else raise NOT_UNIFIABLE
    | Node((sym1, 0), []), Node((sym2, arity), terms) -> 
        raise NOT_UNIFIABLE
    | Node((sym1, arity1), terms1),  Node((sym2, arity2), terms2) ->
        if sym1 = sym2 && arity1 = arity2 then
          let make_pairs = zip(terms1, terms2) in
          List.fold_left (fun unif (t11, t12) -> 
              compose unif 
                (mgu_helper (subst t11 unif) (subst t12 unif)unif)) 
            unif make_pairs
        else
          raise NOT_UNIFIABLE
    | Node ((sym, arity), terms), V t2 -> 
        mgu_helper (V t2) (Node ((sym, arity), terms)) unif
  in
  let unifier = id (Ls.union (vars term1) (vars term2)) in
  mgu_helper term1 term2 unifier ;;

let resolution test_program test_goal =
  let rec make_goal g = match g with
      Goal x -> x
  in
  let id variables = 
    let sub = Hashtbl.create 100 in
    begin
      (List.map
         (fun ele -> Hashtbl.add sub ele (V ele))
         variables);
      sub
    end
  in
  let rec preprocess_program prog = match prog with
      [] -> []
    | Rule(x, y) :: xs -> (x, y) :: preprocess_program xs
    | Fact(x) :: xs -> (x, []) :: preprocess_program xs
  in
  let compose sub1 sub2 = Hashtbl.iter 
      (fun k v -> Hashtbl.replace sub1 k (subst v sub2)) sub1; sub1
  in
  let rec resolvant prog test_goal rest_goal = match prog with
      [] -> []
    | (head, body) :: progt ->
        try
          let unifier_sub = mgu head test_goal in
          [(
            (subst_all (Ls.union body rest_goal) unifier_sub),
            unifier_sub )] @ resolvant progt test_goal rest_goal
        with
          NOT_UNIFIABLE -> resolvant progt test_goal rest_goal
  in
  let rec resolution_engine prog goals visited result =
    match prog, goals with
      _, ([], sub) -> 
        (true, Hashtbl.fold 
           (fun k v acc -> (k, v) :: acc) sub []) :: result
    | [], (_, sub) -> result
    | prog, (x::xs, sub) ->
        successors prog 
          (List.map 
             (fun (x, y) ->
                let sub_copy = Hashtbl.copy(sub) in
                (x, compose sub_copy y)) 
             (resolvant prog x xs)) visited result
  and
    successors prog goals visited result =
    match goals with
      [] -> result
    | (goalh, sub) :: goalt ->
        let new_visited = goalh :: visited in
        if Ls.member goalh visited
        then successors prog goalt visited result
        else
          (resolution_engine prog (goalh, sub) new_visited result) @
          (successors prog goalt visited result)
  in
  let input_program = preprocess_program test_program in
  let processed_goal = make_goal test_goal in
  let goal = ([processed_goal], id (vars processed_goal)) in
  resolution_engine input_program goal [] [];;