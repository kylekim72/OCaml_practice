type id = string

(* Base Types (B) *)
type base_type =
  | Int
  | Bool

(* Constants (c) *)
type const =
  | Int of int
  | Bool of bool

(* Liquid Refinements (Q) *)
type simple_expr = 
  | Ident of string
  | NumConst of int
  | BoolConst of bool
  | Add of simple_expr * simple_expr
  | Sub of simple_expr * simple_expr  
  
type predicate = 
  | BoolConst of bool
  | Eq of simple_expr * simple_expr
  | Lt of simple_expr * simple_expr
  | Gt of simple_expr * simple_expr
  | And of predicate * predicate
  | Or of predicate * predicate
  | Not of predicate

type type_refinement = predicate

  (* Type Skeletons (T(B)) *)
type typ =
  | TBase of id * base_type * type_refinement         (* {v: B | r} *)
  | TFun  of id *  typ * typ        (* x: T1 -> T2 *)


(* Expressions (e) without polymorphism *)
type expr =
  | Var    of id                           (* x *)
  | Const  of const                        (* c *)
  | Fun    of id * typ * expr      (* lambda x.e , assume the type of the function is given*)
  | App    of expr * expr                  (* e e *)
  | ITE of expr * expr * expr * typ          (* if e then e else e *)
  | Let    of id * expr * expr             (* let x = e in e *)
  | LetRec of id * id * typ * typ * expr * expr (* let rec f = lambda x.e in e, assume the type of the function is given *)

type env = {
  bindings : (id * typ) list;  (* mapping for identifier: type *)
  guards   : expr list;                (* guard predicates *)
}

(* Return a type information of given variable in given type environment *)
let lookup_var (x : id) (gamma : env) : typ option =
  List.assoc_opt x gamma.bindings

(* 2. Add new bindings to type environment *)
let add_binding (x : id) (t : typ) (gamma : env) : env =
  { gamma with bindings = (x, t) :: gamma.bindings }

(* 3. Add a new guard predicate to type environment *)
let add_guard (cond : expr) (gamma : env) : env =
  { gamma with guards = cond :: gamma.guards }

let ty_const (c: const) : typ = 
  match c with
  | Int n -> 
      (* {v: Int | v = n} *)
      TBase ("v", Int, Eq (Ident "v", NumConst n))
  | Bool b -> 
      (* {v: Bool | v = true} or {v: Bool | v = false} *)
      TBase ("v", Bool, Eq (Ident "v", BoolConst b))



(* 1. expr을 predicate에 넣을 수 있는 simple_expr로 변환하는 헬퍼 함수 *)
let expr_to_simple (e: expr) : simple_expr option =
  match e with
  | Var x -> Some (Ident x)
  | Const (Int n) -> Some (NumConst n)
  | Const (Bool b) -> Some (BoolConst b)
  (* 복잡한 수식이나 함수 호출은 조건식(predicate) 안에 들어갈 수 없음! *)
  (* This place needs A-normalization*)
  (* If we do A-normalization, we need to return error here*)
  | _ -> failwith "Compiler Bug: Missing ANF normalization"

(* 2. simple_expr 내부의 변수를 치환하는 함수 *)
let rec substitute_simple (x: id) (s_val: simple_expr) (s: simple_expr) : simple_expr =
  match s with
  | Ident y when y = x -> s_val
  | Add (s1, s2) -> Add (substitute_simple x s_val s1, substitute_simple x s_val s2)
  | Sub (s1, s2) -> Sub (substitute_simple x s_val s1, substitute_simple x s_val s2)
  | _ -> s

(* 3. predicate 내부를 치환하는 함수 (예전의 substitute_ref) *)
let rec substitute_predicate (x: id) (s_val: simple_expr) (p: predicate) : predicate =
  match p with
  | BoolConst _ -> p
  | Eq (s1, s2) -> Eq (substitute_simple x s_val s1, substitute_simple x s_val s2)
  | Lt (s1, s2) -> Lt (substitute_simple x s_val s1, substitute_simple x s_val s2)
  | Gt (s1, s2) -> Gt (substitute_simple x s_val s1, substitute_simple x s_val s2)
  | And (p1, p2) -> And (substitute_predicate x s_val p1, substitute_predicate x s_val p2)
  | Or (p1, p2) -> Or (substitute_predicate x s_val p1, substitute_predicate x s_val p2)
  | Not p1 -> Not (substitute_predicate x s_val p1)

(* 4. 대망의 substitute_type 함수 업데이트 *)
let rec substitute_type (x : id) (e_val : expr) (t : typ) : typ =
  (* e_val을 simple_expr로 변환 시도 *)
  let s_val_opt = expr_to_simple e_val in

  match t with
  | TBase (v, base_t, ref_pred) -> 
      if v = x then
        t (* 변수 가려짐(Shadowing): 치환 중단 *)
      else
        let new_ref = match s_val_opt with
          | Some s_val -> substitute_predicate x s_val ref_pred
          | None -> ref_pred (* 단순 변환이 불가능한 복잡한 expr이면 치환하지 않음 *)
        in
        TBase (v, base_t, new_ref)

  | TFun (y, t_in, t_out) -> 
      let new_t_in = substitute_type x e_val t_in in
      if y = x then
        TFun (y, new_t_in, t_out)
      else
        let new_t_out = substitute_type x e_val t_out in
        TFun (y, new_t_in, new_t_out)

(* 1. simple_expr to smt-lib *)
let rec smt_of_simple (s: simple_expr) : string =
  match s with
  | Ident x -> x
  | NumConst n -> string_of_int n
  | BoolConst b -> if b then "true" else "false"
  | Add (s1, s2) -> Printf.sprintf "(+ %s %s)" (smt_of_simple s1) (smt_of_simple s2)
  | Sub (s1, s2) -> Printf.sprintf "(- %s %s)" (smt_of_simple s1) (smt_of_simple s2)

(* 2. predicate to smt-lib *)
let rec smt_of_pred (p: predicate) : string =
  match p with
  | BoolConst true -> "true"
  | BoolConst false -> "false"
  | Eq (s1, s2) -> Printf.sprintf "(= %s %s)" (smt_of_simple s1) (smt_of_simple s2)
  | Lt (s1, s2) -> Printf.sprintf "(< %s %s)" (smt_of_simple s1) (smt_of_simple s2)
  | Gt (s1, s2) -> Printf.sprintf "(> %s %s)" (smt_of_simple s1) (smt_of_simple s2)
  | And (p1, p2) -> Printf.sprintf "(and %s %s)" (smt_of_pred p1) (smt_of_pred p2)
  | Or (p1, p2) -> Printf.sprintf "(or %s %s)" (smt_of_pred p1) (smt_of_pred p2)
  | Not p1 -> Printf.sprintf "(not %s)" (smt_of_pred p1)

(* 문자열 Set 모듈 생성 *)
module StringSet = Set.Make(String)

(* simple_expr에서 변수 추출 *)
let rec fv_simple (s: simple_expr) : StringSet.t =
  match s with
  | Ident x -> StringSet.singleton x
  | Add (s1, s2) | Sub (s1, s2) -> 
      StringSet.union (fv_simple s1) (fv_simple s2)
  | _ -> StringSet.empty

(* predicate에서 변수 추출 *)
let rec fv_pred (p: predicate) : StringSet.t =
  match p with
  | BoolConst _ -> StringSet.empty
  | Eq (s1, s2) | Lt (s1, s2) | Gt (s1, s2) -> 
      StringSet.union (fv_simple s1) (fv_simple s2)
  | And (p1, p2) | Or (p1, p2) -> 
      StringSet.union (fv_pred p1) (fv_pred p2)
  | Not p1 -> fv_pred p1

(* SMT 솔버를 실행하여 Implication(p1 => p2)이 참인지 확인하는 함수 *)
(* 매개변수 추가: gamma(환경), base_var(기준 변수명), base_t(기준 변수 타입) *)
let check_implication (gamma: env) (base_var: id) (base_t: base_type) 
                      (gamma_preds: predicate list) (p1: predicate) (p2: predicate) : bool =
  
  let all_preds = p1 :: p2 :: gamma_preds in
  let fvs = List.fold_left (fun acc p -> 
      StringSet.union acc (fv_pred p)
    ) StringSet.empty all_preds 
  in

  let script = Buffer.create 512 in

  (* 3. 변수 선언 (Declare) - Int/Bool 완벽 체크 *)
  StringSet.iter (fun v ->
    let z3_type = 
      if v = base_var then
        (* 1) 검사 중인 타입의 기준 변수(v)인 경우 *)
        match base_t with
        | Int -> "Int"
        | Bool -> "Bool"
      else
        (* 2) 환경(gamma)에 등록된 외부 변수인 경우 *)
        match lookup_var v gamma with
        | Some (TBase (_, Int, _)) -> "Int"
        | Some (TBase (_, Bool, _)) -> "Bool"
        | _ -> 
            (* 함수 타입이거나 아예 없는 변수면 일단 Int로 Fallback (혹은 에러 처리) *)
            "Int" 
    in
    Buffer.add_string script (Printf.sprintf "(declare-const %s %s)\n" v z3_type)
  ) fvs;

  (* 4. Assert gamma *)
  List.iter (fun g_pred -> 
    Buffer.add_string script (Printf.sprintf "(assert %s)\n" (smt_of_pred g_pred))
  ) gamma_preds;

  (* 5. Assert p1 *)
  Buffer.add_string script (Printf.sprintf "(assert %s)\n" (smt_of_pred p1));

  (* 6. Assert not p2 *)
  Buffer.add_string script (Printf.sprintf "(assert (not %s))\n" (smt_of_pred p2));

  Buffer.add_string script "(check-sat)\n";

  let smt_query = Buffer.contents script in

  (* 8. Run z3*)
  let ic, oc = Unix.open_process "z3 -smt2 -in" in
  output_string oc smt_query;
  flush oc;
  
  let result = 
    try input_line ic 
    with End_of_file -> "unknown" 
  in
  ignore (Unix.close_process (ic, oc));

  (* 9. unsat 확인 *)
  result = "unsat"

let rec expr_to_pred (e: expr) : predicate =
  match e with
  | Var x -> Eq (Ident x, BoolConst true)
  | App(Var "not", Var x) -> Eq (Ident x, BoolConst false)
  | App(App(Var "<", e1), e2) -> 
      (match expr_to_simple e1, expr_to_simple e2 with
        | Some s1, Some s2 -> Lt (s1, s2) | _ -> failwith "Test Error")
  | App(App(Var ">", e1), e2) -> 
      (match expr_to_simple e1, expr_to_simple e2 with
        | Some s1, Some s2 -> Gt (s1, s2) | _ -> failwith "Test Error")
  | App(Var "not", e') -> Not (expr_to_pred e')
  | _ -> BoolConst true (* 기타 가드는 일단 통과 *)

(* 환경(gamma)에 있는 변수들의 조건식을 predicate 리스트로 추출 *)
let env_to_preds (gamma: env) : predicate list =
  let bind_preds = List.fold_left (fun acc (var_name, typ) ->
    match typ with
    | TBase (v, _, ref_pred) ->
        let actual_pred = substitute_predicate v (Ident var_name) ref_pred in
        actual_pred :: acc
    | TFun _ -> acc
  ) [] gamma.bindings in
  
  (* guards에 있는 expr들도 전부 predicate로 변환해서 합칩니다! *)
  let guard_preds = List.map expr_to_pred gamma.guards in
  bind_preds @ guard_preds

(* Check t1 <: t2 *)
let rec is_subtype (gamma: env) (t1: typ) (t2: typ) : unit =
  match t1, t2 with
  (* 1. 기본 타입의 서브타이핑 *)
  | TBase (v1, base_t1, ref1), TBase (v2, base_t2, ref2) ->
      if base_t1 <> base_t2 then failwith "Base types do not match!"
      else
        let ref2_sub = substitute_predicate v2 (Ident v1) ref2 in
        let gamma_preds = env_to_preds gamma in 
        
        (* 변경됨: gamma, v1, base_t1을 같이 넘겨줍니다! *)
        let is_valid = check_implication gamma v1 base_t1 gamma_preds ref1 ref2_sub in
        
        if not is_valid then 
          failwith "Subtype Error: SMT Solver cannot prove implication!"

  (* 2. 함수 타입의 서브타이핑 *)
  | TFun (x1, t_in1, t_out1), TFun (x2, t_in2, t_out2) ->
      (* 입력 타입은 역방향 (Contravariance) *)
      (* Check input type in opposite way*)
      is_subtype gamma t_in2 t_in1;
      
      (* 출력 타입은 정방향 (Covariance). 
         단, t_out1 안의 매개변수 x1을 x2로 치환해주고 검사해야 합니다! *)
      let new_gamma = add_binding x2 t_in2 gamma in
      let sub_t_out1 = substitute_type x1 (Var x2) t_out1 in
      is_subtype new_gamma sub_t_out1 t_out2

  | _ -> failwith "Subtyping Error: Type structure is different"


let rec type_check (gamma: env) (e: expr) : typ = 
  match e with
    (* LT-CONST *)
  | Const c -> ty_const c
    (* LT-VAR*)
  | Var x -> (match lookup_var x gamma with
       | None -> 
           (* x is not defined yet*)
           failwith ("Unbound variable: " ^ x)
           
       | Some (TBase (v, base_t, old_ref)) -> 
           (* Conjunction with previous refinement *)
           let new_ref = And (old_ref, Eq (Ident v, Ident x)) in
           TBase (v, base_t, new_ref)
           
       | Some (TFun _ as func_type) ->
           (* if it is function type, just return that function type *)
           func_type)
    (* LT-IF*)
  | ITE (e1, e2, e3, target_typ) -> 
      let t1 = type_check gamma e1 in
      (match t1 with 
       | TBase (_, Bool, _) -> 
           let gamma_then = add_guard e1 gamma in
           let t2 = type_check gamma_then e2 in
           
           let not_e1 = App (Var "not", e1) in
           let gamma_else = add_guard not_e1 gamma in
           let t3 = type_check gamma_else e3 in

           (* [핵심 수정] then과 else가 각각 목표 타입(target_typ)의 서브타입인지 독립적으로 검사! *)
           is_subtype gamma_then t2 target_typ;
           is_subtype gamma_else t3 target_typ;

           target_typ
       | _ -> failwith "Type error: Condition need to be boolean.")
    (* LT-FUN *)
  | Fun (x, t_x, e) -> let gamma_body = add_binding x t_x gamma in 
                   let t_body = type_check gamma_body e in
                   TFun (x, t_x, t_body)

    (* LT-LET *)
  | Let (x, e1, e2) -> let t1 = type_check gamma e1 in
                   let new_gamma = add_binding x t1 gamma in
                   let t2 = type_check new_gamma e2 in
                   (match t1, t2 with
                    | TBase (v1, b1, ref1), TBase (v2, b2, ref2) ->
                        (* 1. e1의 결과 타입(ref1)에서 기준 변수 v1을 실제 변수명 x로 치환 *)
                        let ref1_x = substitute_predicate v1 (Ident x) ref1 in
                        
                        (* 2. e2의 최종 결과 타입(ref2)에 x의 제약 조건을 영구적으로 결합! *)
                        let combined_ref = And (ref1_x, ref2) in
                        TBase (v2, b2, combined_ref)
                        
                    | _ -> t2)
    (* LT-APP *)
  | App (e1, e2) -> let t1 = type_check gamma e1 in
                 (match t1 with 
                 | TFun(x, t_x, t_ret) ->
                  let t2 = type_check gamma e2 in
                  (* [e2 / x] *)
                  is_subtype gamma t2 t_x;
                  substitute_type x e2 t_ret
                 | _ -> failwith ("Type error"))

    (* There is no corresponding rule to LetRec in Liquid Type paper(PLDI 2008).
      Therefore, I've implemented typechecking for LetRec as a variant of LT-LET rule*)
  | LetRec (f, x, t_f, t_x, e1, e2) -> 
                  let gamma_f = add_binding f t_f gamma in (* add function's type to type environment*)
                  let gamma_x = add_binding x t_x gamma_f in (* add function & parameter's type to type enviroment*)
                  let t1 = type_check gamma_x e1 in 

                  (match t_f with
                  | TFun (y, _, t_ret) ->
                      (* 팁: t_f에 선언된 매개변수 이름(y)이 실제 구현의 매개변수(x)와 
                          다를 수 있으므로, 반환 타입 내부의 y를 x로 치환한 뒤 검사합니다. *)
                      let expected_ret = substitute_type y (Var x) t_ret in
                      
                      (* 본문 타입(t1)이 기대하는 반환 타입(expected_ret)의 서브타입인가? *)
                      is_subtype gamma_x t1 expected_ret;
                      
                      (* 무사히 통과했다면 나머지 e2를 마저 검사합니다 *)
                      let t2 = type_check gamma_f e2 in 
                      t2
                      
                  | _ -> failwith "Type error: Type of LetRec should be TFun!")


(* Missing parts: substitution, subtype checking, *)

(* 1. 빈 타입 환경 생성 *)
let empty_env = { bindings = []; guards = [] }

(* 2. 양수만 받는 타입 정의: {v: Int | v > 0} *)
let positive_int_type = 
  TBase ("v", Int, Gt (Ident "v", NumConst 0))

(* 3. 테스트할 프로그램 AST 조립 
   코드 의미: (fun (x: positive_int) -> x) 3 
*)
let test_program = 
  App (
    Fun ("x", positive_int_type, Var "x"), (* 양수 x를 받아서 그대로 반환하는 함수 *)
    Const (Int 3)                          (* 인자로 숫자 3을 넘김 *)
  )

(* 4. 실행 및 결과 출력 뼈대 *)
let () =
  print_endline "=== Liquid Type Checker Test Start ===";
  try
    let _ = type_check empty_env test_program in
    print_endline "Success";
    (* OCaml 기본 출력으로 타입 구조 훔쳐보기 (옵션) *)
    (* Printf.printf "최종 타입 구조: ...\n" *)
  with 
  | Failure msg -> 
      Printf.printf "Fail: %s\n" msg
  | e -> 
      Printf.printf "Unknown error: %s\n" (Printexc.to_string e)