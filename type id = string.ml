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
type logical_qualifier = string

type liquid_ref =
  | True
  | Qual of logical_qualifier
  | And of liquid_ref * liquid_ref

  (* Type Skeletons (T(B)) - Type Variable(\alpha) 제거 *)
type 'r typ =
  | TBase of id * base_type * 'r         (* {\nu: B | r} *)
  | TFun  of id * 'r typ * 'r typ        (* x: T1 -> T2 *)

(* Type Schema가 제거되었으므로 바로 타입 별칭을 정의할 수 있습니다. *)

(* 3. Liquid 타입 (\hat{T}) *)
type liquid_type = liquid_ref typ

(* Expressions (e) without polymorphism *)
type expr =
  | Var    of id                           (* x *)
  | Const  of const                        (* c *)
  | Fun    of id * liquid_type * expr      (* lambda x.e , assume a type of the function is given*)
  | App    of expr * expr                  (* e e *)
  | ITE     of expr * expr * expr           (* if e then e else e *)
  | Let    of id * expr * expr             (* let x = e in e *)
  | LetRec of id * id * liquid_type * liquid_type * expr * expr        (* let rec f = lambda x.e in e *)


type env = {
  bindings : (id * liquid_type) list;  (* bindings for identifier -> type *)
  guards   : expr list;                (* guard predicates *)
}

(* 1. 환경에서 변수 찾기 (아까 짠 LT-VAR에서 쓸 함수) *)
let lookup_var (x : id) (gamma : env) : liquid_type option =
  List.assoc_opt x gamma.bindings

(* 2. 환경에 새로운 변수 바인딩 추가하기 (LT-FUN이나 LT-LET에서 씁니다) *)
let add_binding (x : id) (t : liquid_type) (gamma : env) : env =
  (* 'with' 키워드는 gamma를 복사하되, bindings 필드만 새로 업데이트하라는 뜻이야 *)
  { gamma with bindings = (x, t) :: gamma.bindings }

(* 3. 환경에 새로운 가드 조건 추가하기 (LT-IF에서 쓸 핵심 함수!) *)
let add_guard (cond : expr) (gamma : env) : env =
  { gamma with guards = cond :: gamma.guards }

let ty_const (c: const) : liquid_type = 
  match c with
  | Int n -> TBase ("v", Int, Qual ("v = " ^ string_of_int n))
  | Bool true -> TBase ("v", Bool, Qual ("v"))
  | Bool false -> TBase ("v", Bool, Qual ("not v"))


(* Not implemented for simplicity *)
let rec substitute_ref (x: id) (e_val: expr) (ref: liquid_ref) : liquid_ref = 
  ref

let rec substitute_type (x : id) (e_val : expr) (t : liquid_type) : liquid_type =
  match t with
  | TBase (v, base_t, ref) -> 
    if v = x then
      t
    else
      let new_ref = substitute_ref x e_val ref in
      TBase (v, base_t, new_ref)
  | TFun (y, t_in, t_out) -> 
    let new_t_in = substitute_type x e_val t_in in
    if y = x then
      TFun (y, new_t_in, t_out)
    else
      let new_t_out = substitute_type x e_val t_out in
      TFun (y, new_t_in, new_t_out)


let rec type_check (gamma: env) (e: expr) : liquid_type = 
  match e with
  | Const c -> ty_const c
  | Var x -> (match lookup_var x gamma with
       | None -> 
           (* x is not defined yet*)
           failwith ("Unbound variable: " ^ x)
           
       | Some (TBase (v, base_t, _old_ref)) -> 
          (* if it's base type, just change the refinement predicate to v = x*)
           TBase ("v", base_t, Qual ("v = " ^ x))
           
       | Some (TFun _ as func_type) ->
           (* if it is function type, just return that function type *)
           func_type)
  | ITE (e1, e2, e3) -> let t1 = type_check gamma e1 in
        (match t1 with 
        | TBase (_, Bool, _) -> (* first premise*)

            (* second premise*)
            let gamma_then = add_guard e1 gamma in
            let t2 = type_check gamma_then e2 in
            (* third premise*)
            let not_e1 = App (Var "not", e1) in
            let gamma_else = add_guard not_e1 gamma in
            let t3 = type_check gamma_else e3 in
            (* return type is same with t2*)
            t2
            | _ -> failwith ("Type error"))
  | Fun (x, t_x, e) -> let gamma_body = add_binding x t_x gamma in 
                   let t_body = type_check gamma_body e in
                   TFun (x, t_x, t_body)
  | Let (x, e1, e2) -> let s1 = type_check gamma e1 in
                   let new_gamma = add_binding x s1 gamma in
                   let t2 = type_check new_gamma e2 in
                   t2
  | App (e1, e2) -> let t1 = type_check gamma e1 in
                 (match t1 with 
                 | TFun(x, t_x, t_ret) ->
                  let t2 = type_check gamma e2 in
                  (* [e2 / x] *)
                  substitute_type x e2 t_ret
                 | _ -> failwith ("Type error"))
  | LetRec (f, x, t_f, t_x, e1, e2) -> 
                  let gamma_f = add_binding f t_f gamma in
                  let gamma_x = add_binding x t_x gamma_f in
                  let t1 = type_check gamma_x e1 in

                  let t2 = type_check gamma_f e2 in 

                  t2