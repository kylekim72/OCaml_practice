open Liquid_type_check

(* 공통 뼈대 타입 *)
let t_int = TBase ("v", Int, BoolConst true)
let t_bool = TBase ("v", Bool, BoolConst true)

let iff p q =
  Or (And (p, q), And (Not p, Not q))

let v_is_true = Eq (Ident "v", BoolConst true)
let x_is_true = Eq (Ident "x", BoolConst true)

(* 1. 초기 환경 세팅 (+, -, <, >, not 연산자 등록) *)
let initial_env = {
  bindings = [
    (* 더하기: v = x + y *)
    ("+", TFun ("x", t_int, TFun ("y", t_int, TBase ("v", Int, Eq(Ident "v", Add(Ident "x", Ident "y"))))));
    
    (* 빼기: v = x - y *)
    ("-", TFun ("x", t_int, TFun ("y", t_int, TBase ("v", Int, Eq(Ident "v", Sub(Ident "x", Ident "y"))))));
    
    (* 작다(<): v가 true일 조건은 x < y 와 완전히 같다 *)
    ("<", TFun ("x", t_int, TFun ("y", t_int, TBase ("v", Bool, iff v_is_true (Lt(Ident "x", Ident "y"))))));
    
    (* 크다(>): v가 true일 조건은 x > y 와 완전히 같다 *)
    (">", TFun ("x", t_int, TFun ("y", t_int, TBase ("v", Bool, iff v_is_true (Gt(Ident "x", Ident "y"))))));
    
    (* not: v가 true일 조건은 x가 true가 아님과 같다 *)
    ("not", TFun ("x", t_bool, TBase ("v", Bool, iff v_is_true (Not x_is_true))));

    ("=", TFun ("x", t_int, TFun ("y", t_int, TBase ("v", Bool, iff v_is_true (Eq(Ident "x", Ident "y"))))));
  ];
  guards = []
}

(* ========================================== *)
(* A-Normal Form (ANF) 변환기                 *)
(* ========================================== *)
let anf_counter = ref 0
let fresh_var () =
  incr anf_counter;
  "~t" ^ string_of_int !anf_counter

let rec normalize (e: expr) (k: expr -> expr) : expr =
  match e with
  | Var _ | Const _ -> k e
  | Fun (x, t_x, body) -> k (Fun (x, t_x, anf_transform body))
  | Let (x, e1, e2) -> Let (x, anf_transform e1, normalize e2 k)
  | LetRec (f, x, t_f, t_x, e1, e2) ->
      LetRec (f, x, t_f, t_x, anf_transform e1, normalize e2 k)
  | ITE (e1, e2, e3, target_t) ->
      normalize e1 (fun v1 ->
        let t_name = fresh_var () in
        Let (t_name, ITE (v1, anf_transform e2, anf_transform e3, target_t), k (Var t_name)))
  | App (e1, e2) ->
      normalize e1 (fun v1 ->
        normalize e2 (fun v2 ->
          let t_name = fresh_var () in
          Let (t_name, App (v1, v2), k (Var t_name)))) (* 💡 괄호 하나 추가됨! *)

and anf_transform (e: expr) : expr =
  normalize e (fun x -> x)

(* ==================== 테스트 케이스 AST ==================== *)

(* Test 1: (fun x -> x + 1) 5 *)
let test1_ast = 
  let inc_body = App (App (Var "+", Var "x"), Const (Int 1)) in
  App (Fun ("x", t_int, inc_body), Const (Int 5))

(* Test 2: abs 함수 (if x < 0 then 0 - x else x) *)
(* 목표 타입: {v: Int | v >= 0} *)
let t_pos = TBase ("v", Int, Not (Lt (Ident "v", NumConst 0)))
let test2_ast = 
  Fun ("x", t_int, 
    ITE (
      App(App(Var "<", Var "x"), Const(Int 0)), 
      App(App(Var "-", Const(Int 0)), Var "x"),
      Var "x",
      t_pos
    )
  )

(* Test 3: max 함수 (if x > y then x else y) *)
(* 목표 타입: {v: Int | v >= x && v >= y} *)
let t_max = TBase ("v", Int, And(Not(Lt(Ident "v", Ident "x")), Not(Lt(Ident "v", Ident "y"))))
let test3_ast = 
  Fun ("x", t_int, Fun ("y", t_int, 
    ITE (
      App(App(Var ">", Var "x"), Var "y"), 
      Var "x", 
      Var "y",
      t_max
    )
  ))

(* Test 4: sum 함수 (재귀 불변성 증명) *)
(* sum: k:{v>=0} -> {v>=0} *)
(* let rec sum k = if k = 0 then 0 else k + sum (k-1) *)
let test4_ast = 
  LetRec ("sum", "k", TFun("k", t_pos, t_pos), t_pos,
    ITE (
      App(App(Var "=", Var "k"), Const(Int 0)),
      Const (Int 0),
      
      (* k + sum (k - 1) *)
      App (
        App (Var "+", Var "k"), 
        App (Var "sum", App (App (Var "-", Var "k"), Const (Int 1)))
      ),
      t_pos
    ),
    App (Var "sum", Const (Int 5)) (* 본문 실행: sum 5 *)
  )

(* ==================== 실행기 ==================== *)
let run_test name ast =
  Printf.printf "▶ %s\n" name;
  try 
    (* 💡 타입 체커에 넣기 전에 ANF 변환! *)
    let anf_ast = anf_transform ast in
    
    let _ = type_check initial_env anf_ast in 
    Printf.printf "  Success!\n\n"
  with Failure msg -> Printf.printf " Fail: %s\n\n" msg

let () =
  print_endline "=== Liquid Types Core Test Suite ===";
  run_test "Test 1: Dependent App (inc 5)" test1_ast;
  run_test "Test 2: Path Sensitivity (abs)" test2_ast;
  run_test "Test 3: Complex Path (max)" test3_ast;
  run_test "Test 4: Recursive Invariant (sum)" test4_ast;