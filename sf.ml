(* The intrinsically typed second order syntactical framework *)

type _ base = B
  (* Parameter is agnostic *)
  (* Parameter is unconstrained *)

and  _ boxed = Bo
  (* Parameter is agnostic *)
  (* Parameter is unconstrained *)

and  (_,_) arr = A
  (* Both parameters are agnostic *)
  (* Both parameters are unconstrained *)

(* Type level and singleton contexts *)
and  (_,_) cons = Cons [@name "cons_Cons"]
  (* Both parameters are agnostic *)
  (* Both parameters are unconstrained *)
and  nil = Nil

and  _ ctx =
  | Empty : nil ctx
    [@name "ctx_Empty"]
  | Dec :    'a ctx
          *  ('t [@opaque] (* this _must_ be opaque*))
          -> (('a, 't) cons) ctx
  (* Parameter is not relevant *)
  (* Parameter is constrained *)

[@@deriving
  visitors { variety = "iter"; name = "base_iter"; polymorphic = true; nude = true; concrete = true; },
  visitors { variety = "map"; name = "base_map"; polymorphic = true; nude = true; concrete = true; },
  visitors { variety = "reduce"; name = "base_reduce"; polymorphic = true; }
]

(*  iterator visitor method for a (G)ADT constructor of type ('v0, ..., 'v{m}) t

        C : s_0 * ... * s_n -> (u_0, ..., u_m) t

    has signature

        method visit_C :
          'var0 ... 'var{k} .
            u'_0 -> ... -> u'_m -> 'env -> s_0 -> ... -> s_n -> unit

    where:

      - 'var0, ..., 'var{k} correspond to the type variables occurring in the
        constructor

      - u'_i = ('env -> u_i -> unit) if the i_th parameter of t is relevant,
        and u'_i = unit otherwise (if it is not relevant)

    iterator visitor method for a type ('v0, ..., 'v{m}) t has signature

        method visit_t :
          type v0 ... v{m} .
            u_0 -> ... -> u_m -> 'env -> (v0, ..., v{m}) t -> unit

    where:

      - u_i = ('env -> v{i} -> unit) if the i_th parameter of t is relevant,
        and u_i = unit otherwise (if it is not relevant)

    Note that the type 'env of the environment is parameterised at the level
    of the class
*)

class ['self] base_iter = object (self : 'self)
  method visit_B : 'var0 . unit  -> 'env -> unit =
    fun _visit_arg0 env -> ()
  method visit_base : type v0 . unit -> 'env -> v0 base -> unit =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
      | B -> self#visit_B _visit_arg0 env
  method visit_Bo : 'var0 . unit -> 'env -> unit =
    fun _visit_arg0 env -> ()
  method visit_boxed : type v0 . unit -> 'env -> v0 boxed -> unit =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
      | Bo -> self#visit_Bo _visit_arg0 env
  method visit_A : 'var0 'var1 . unit -> unit -> 'env -> unit =
    fun _visit_arg0 _visit_arg1 env -> ()
  method visit_arr :
      type v0 v1 . unit -> unit -> 'env -> (v0, v1) arr -> unit =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | A -> self#visit_A _visit_arg0 _visit_arg1 env
  method visit_cons_Cons : 'var0 'var1 . unit -> unit -> 'env -> unit =
    fun _visit_arg0 _visit_arg1 env -> ()
  method visit_cons :
      type v0 v1 . unit -> unit -> 'env -> (v0, v1) cons -> unit =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | Cons -> self#visit_cons_Cons _visit_arg0 _visit_arg1 env
  method visit_Nil : 'env -> unit =
    fun env -> ()
  method visit_nil : 'env -> nil -> unit =
    fun env _visitors_this ->
      match _visitors_this with
      | Nil -> self#visit_Nil env
  method visit_ctx_Empty : unit -> 'env -> unit =
    fun _visit_arg0 env -> ()
  method visit_Dec : 'v0 'v1 . unit -> 'env -> 'v0 ctx -> 'v1 -> unit =
    fun _visit_arg0 env _visitors_c0 _visitors_c1 ->
      let _visitors_r0 =
        let _visit_arg0 = () in
        self#visit_ctx _visit_arg0 env _visitors_c0 in
      let _visitors_r1 =
        (* This is the auto-generated code for opaque arguments *)
        (fun _visitors_this -> ()) _visitors_c1 in
      ()
  method visit_ctx :
      type v0 . unit -> 'env -> v0 ctx -> unit =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
      | Empty ->
        self#visit_ctx_Empty _visit_arg0 env
      | Dec (_visitors_c0, _visitors_c1) ->
        self#visit_Dec _visit_arg0 env _visitors_c0 _visitors_c1
end

(*  map visitor method for a (G)ADT constructor of type ('v0, ..., 'v{m}) t

        C : s_0 * ... * s_n -> (u_0, ..., u_m) t

    has signature

        method visit_C :
          'var0_in ... 'var{k}_in 'var0_out ... 'var{k}_out .
            u'_0 -> ... -> u'_m -> 'env -> s_0 -> ... -> s_n
              -> (r_0, ..., r_m) t

    where:

      - 'var0_in, ..., 'var{k}_in correspond to the type variables occurring in
        the constructor

      - 'var0_out, ..., 'var{k}_out are fresh variables in one-one
        correspondence with 'var0_in, ..., 'var{k}_in

      - u'_i = ('env -> u_i -> \theta(u_i)) if the i_th parameter of t is
          relevant and unconstrained
            (in which case u_i \in { 'var0_in, ..., 'var{k}_in })
          where \theta is the substitution ['var{i}_out / 'var{i}_in] over all i,
        u'_i = ('env -> u_i -> u_i) if the i_th parameter of t is relevant but constrained,
        and u'_i = unit otherwise
          (if the i_th parameter it is not relevant)

      - r_i = \theta(u_i) if the i_th parameter of t is unconstrained
          (where \theta is the substitution as defined previously),
        and r_i = u_i otherwise (if the i_th parameter is not relevant or else constrained)


    iterator visitor method for a type ('v0, ..., 'v{m}) t has signature

        method visit_t :
          type v0_in ... v{m}_in v0_out ... v{m}_out .
            u_0 -> ... -> u_m -> 'env ->
              (v0_in, ..., v{m}_in) t -> (r_0, ..., r_m) t

    where:

      - u_i = ('env -> v{i}_in -> v{i}_out) if the i_th parameter of t is
          relevant and unconstrained,
        u_i = ('env -> v{i}_in -> v{i}_in) if the i_th parameter of t is relevant
          but constrained,
        and u_i = unit otherwise
          (if the i_th parameter is not relevant)

      - r_i = v{i}_out if the i_th parameter of t is unconstrained,
        and r_i = v{i}_in otherwise (if the i_th parameter is constrained)

    Note that the type 'env of the environment is parameterised at the level
    of the class
*)

class ['self] base_map = object (self : 'self)
  method visit_B :
      'var0_in 'var0_out . unit -> 'env -> 'var0_out base =
    fun _visit_arg0 env -> B
  method visit_base :
    type v0_in v0_out . unit -> 'env -> v0_in base -> v0_out base =
      fun _visit_arg0 env _visitors_this ->
        match _visitors_this with
        | B -> self#visit_B _visit_arg0 env
  method visit_Bo :
      'var0_in 'var0_out .
        unit -> 'env -> 'var0_out boxed =
    fun _visit_arg0 env -> Bo
  method visit_boxed :
      type v0_in v0_out .
        unit -> 'env -> v0_in boxed -> v0_out boxed =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
        | Bo -> self#visit_Bo _visit_arg0 env
  method visit_A :
      'var0_in 'var1_in 'var0_out 'var1_out .
        unit -> unit -> 'env -> ('var0_out, 'var1_out) arr =
    fun _visit_arg0 _visit_arg1 env -> A
  method visit_arr :
      type v0_in v1_in v0_out v1_out .
        unit -> unit -> 'env -> (v0_in, v1_in) arr -> (v0_out, v1_out) arr =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | A -> self#visit_A _visit_arg0 _visit_arg1 env
  method visit_cons_Cons :
      'var0_in 'var1_in 'var0_out 'var1_out .
        unit -> unit ->  'env -> ('var0_out, 'var1_out) cons =
    fun _visit_arg0 _visit_arg1 env -> Cons
  method visit_cons :
      type v0_in v1_in v0_out v1_out .
        unit -> unit -> 'env -> (v0_in, v1_in) cons -> (v0_out, v1_out) cons =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | Cons -> self#visit_cons_Cons _visit_arg0 _visit_arg1 env
  method visit_Nil : 'env -> nil =
    fun env -> Nil
  method visit_nil : 'env -> nil -> nil =
    fun env _visitors_this ->
      match _visitors_this with
      | Nil -> self#visit_Nil env
  method visit_ctx_Empty : unit -> 'env -> nil ctx =
    fun _visit_arg0 env -> Empty
  method visit_Dec :
      'var0_in 'var1_in 'var0_out 'var1_out .
        unit -> 'env -> 'var0_in ctx -> 'var1_in ->
          (('var0_in, 'var1_in) cons) ctx =
    fun _visit_arg0 env _visitors_c0 _visitors_c1 ->
      let _visitors_r0 =
        let _visit_arg0 = () in
        self#visit_ctx _visit_arg0 env _visitors_c0 in
      let _visitors_r1 =
        (* This is the auto-generated code for opaque arguments *)
        (fun _visitors_this -> _visitors_this) _visitors_c1 in
      Dec (_visitors_r0, _visitors_r1)
  method visit_ctx :
      type v0_in v0_out . unit -> 'env -> v0_in ctx -> v0_in ctx =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
      | Empty ->
        self#visit_ctx_Empty _visit_arg0 env
      | Dec (_visitors_c0, _visitors_c1) ->
        self#visit_Dec _visit_arg0 env _visitors_c0 _visitors_c1
end

(*  reduce visitor method for a (G)ADT constructor of type ('v0, ..., 'v{m}) t

        C : s_0 * ... * s_n -> (u_0, ..., u_m) t

    has signature

        method visit_C :
          'var0 ... 'var{k} .
            u'_0 -> ... -> u'_m -> 'env -> s_0 -> ... -> s_n -> 'res

    where:

      - 'var0, ..., 'var{k} correspond to the type variables occurring in the
        constructor

      - u'_i = ('env -> u_i -> 'res) if the i_th parameter of t is relevant,
        and u'_i = unit otherwise (if it is not relevant)

      - 'res is the type variable used in the virtual zero and plus methods
        that denotes the type of the result of the reduction

    iterator visitor method for a type ('v0, ..., 'v{m}) t has signature

        method visit_t :
          type v0 ... v{m} .
            u_0 -> ... -> u_m -> 'env -> (v0, ..., v{m}) t -> 'res

    where:

      - u_i = ('env -> v{i} -> 'res) if the i_th parameter of t is relevant,
        and u_i = unit otherwise (if it is not relevant)

      - 'res is the type variable used in the virtual zero and plus methods
        that denotes the type of the result of the reduction


    Note that the type 'env of the environment is parameterised at the level
    of the class
*)

class virtual ['self] base_reduce = object (self : 'self)
  (* inherit ['res] Visitors.Runtime.monoid
       gives the following two virtual methods *)
  method virtual zero : 'res
  method virtual plus : 'res -> 'res -> 'res
  method visit_B : 'var0 . unit -> 'env -> 'res =
    fun _visit_arg0 env -> self#zero
  method visit_base :
    type v0 . unit -> 'env -> v0 base -> 'res =
      fun _visit_arg0 env _visitors_this ->
        match _visitors_this with
        | B -> self#visit_B _visit_arg0 env
  method visit_Bo : 'var0 . unit -> 'env -> 'res =
    fun _visit_arg0 env -> self#zero
  method visit_boxed :
    type v0 . unit -> 'env -> v0 boxed -> 'res =
      fun _visit_arg0 env _visitors_this ->
        match _visitors_this with
        | Bo -> self#visit_Bo _visit_arg0 env
  method visit_A :
      'var0 'var1 . unit -> unit -> 'env -> 'res =
    fun _visit_arg0 _visit_arg1 env -> self#zero
  method visit_arr :
      type v0 v1 . unit -> unit -> 'env -> (v0, v1) arr -> 'res =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | A -> self#visit_A _visit_arg0 _visit_arg1 env
  method visit_cons_Cons : 'var0 'var1 . unit -> unit -> 'env -> 'res =
    fun _visit_arg0 _visit_arg1 env -> self#zero
  method visit_cons :
      type v0 v1 . unit -> unit -> 'env -> (v0, v1) cons -> 'res =
    fun _visit_arg0 _visit_arg1 env _visitors_this ->
      match _visitors_this with
      | Cons -> self#visit_cons_Cons _visit_arg0 _visit_arg1 env
  method visit_Nil : 'env -> 'res =
    fun env -> self#zero
  method visit_nil : 'env -> nil -> 'res =
    fun env _visitors_this ->
      match _visitors_this with
      | Nil -> self#visit_Nil env
  method visit_ctx_Empty : 'var0 . unit -> 'env -> 'res =
    fun _visit_arg0 env -> self#zero
  method visit_Dec :
      'var0 'var1 . unit -> 'env -> 'var0 ctx -> 'var1 -> 'res =
    fun _visit_arg0 env _visitors_c0 _visitors_c1 ->
      let _visitors_r0 =
        let _visit_arg0 = () in
        self#visit_ctx _visit_arg0 env _visitors_c0 in
      let _visitors_r1 =
        (* This is the auto-generated code for opaque arguments *)
        (fun _visitors_this -> self#zero) _visitors_c1 in
      self#plus _visitors_r0 _visitors_r1
  method visit_ctx :
      type v0 . unit -> 'env -> v0 ctx -> 's =
    fun _visit_arg0 env _visitors_this ->
      match _visitors_this with
      | Empty ->
        self#visit_ctx_Empty _visit_arg0 env
      | Dec (_visitors_c0, _visitors_c1) ->
        self#visit_Dec _visit_arg0 env _visitors_c0 _visitors_c1
end

(* The module for the syntactic framework *)

module SyntacticFramework
  (X : sig
         type _ constructor
         val to_string : 'a constructor -> string
       end) =
struct
    (* Types *)

    type 'a constructor = 'a X.constructor
      [@virtual]
      [@constrained : ('_true) t ]
    (* Terms *)
    and  (_,_) var =
      (* Both parameters must be not relevant *)
      (* Both parameters are constrained *)
      | Top : (('g , 'a base) cons, 'a base) var
      | Pop : ('g, 'a base) var -> (('g, 'b base) cons, 'a base) var
    and  (_,_,_) sp =
      (* All parameters must not be relevant *)
      (* All parameters are constrained *)
      | Empty : ('g, 't, 't) sp
        [@name "sp_Empty"]
        (* Rename visitor methods for the constructor so they don't clash with
           those from the ctx type *)
      | Cons : ('g, 't1) tm * ('g, 't2, 't3) sp -> ('g, ('t1, 't2) arr, 't3) sp
        [@name "sp_Cons"]
    and  (_,_) tm =
      (* Both parameters must be not relevant *)
      (* Both parameters are constrained *)
      | Lam : (('g, 'a base) cons, 't) tm -> ('g, ('a base, 't) arr) tm
      | Box :  (nil, 't) tm -> ('g, 't boxed) tm
      | Var : ('g, 'a base) var -> ('g, 'a base) tm
      | C : 't constructor * ('g, 't, 'a base) sp -> ('g, 'a base) tm
        (* Only occurrences of an existential type, 't *)
    (* Shifts of indices *)
    and  (_,_) shift =
      (* Both parameters must be not relevant *)
      (* Both parameters are constrained *)
      (*   It might seem that the first parameter is unconstrained, but the
           fact that the first parameter must match the second in the type of
           the Id constructor is also a constraint *)
      | Id : ('g, 'g) shift
      | Suc : ('g, 'd) shift  -> ('g, ('d , 'a base) cons) shift
    (* Renamings *)
    and  (_,_) ren =
      (* First parameter must be not relevant *)
      (* Second parameter is agnostic *)
      (* Both parameters are constrained *)
      | ShiftR : ('g, 'd) shift-> ('g, 'd) ren
      | DotR : ('g, 'd) ren * ('d, 'a base) var -> (('g, 'a base) cons, 'd) ren
    (* Substitutions *)
    and  (_,_) sub =
      (* First parameter must be not relevant *)
      (* Second parameter is agnostic *)
      (* Both parameters are constrained *)
      | Shift : ('g, 'd) shift -> ('g, 'd) sub
      | Dot : ('g, 'd) sub * ('d, 't) tm -> (('g, 't) cons, 'd) sub
    [@@deriving
      visitors { variety = "iter"; polymorphic = true; nude = "true"; ancestors = [ "base_iter" ]; },
      visitors { variety = "map"; polymorphic = true; nude = "true"; ancestors = [ "base_map" ]; },
      visitors { variety = "reduce"; polymorphic = true; ancestors = [ "base_reduce" ]; }
    ]

    (* Visitor classes *)

    (* The visitor methods for the above types don't actually need to call the
       visitor methods for the basic types at the top, since they are never
       referred to in the arguments of the constructors. They are only used as
       arguments for the parameters of the return types.

       Nevertheless, these visitors will extend the previous ones, so that all
       the visitor methods can be composed together in one class.
    *)

    class virtual ['self] iter = object (self : 'self)
      inherit [_] base_iter
      method virtual visit_constructor :
       'v0 . unit -> 'env -> 'v0 X.constructor -> unit
      method visit_Top : 'var0 'var1 . unit -> unit -> 'env -> unit =
        fun _visit_arg0 _visit_arg1 env -> ()
      method visit_Pop :
          'var0 'var1 'var2 . unit -> unit -> 'env ->
            ('var0, 'var1 base) var -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_var :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) var -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Top ->
            self#visit_Top _visit_arg0 _visit_arg1 env
          | Pop v ->
            self#visit_Pop _visit_arg0 _visit_arg1 env v
      method visit_sp_Empty :
          'var0 'var1 . unit -> unit -> unit -> 'env -> unit =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env -> ()
      method visit_sp_Cons :
          'var0 'var1 'var2 'var3 .
            unit-> unit -> unit -> 'env -> ('var0, 'var1) tm ->
              ('var0, 'var2, 'var3) sp -> unit =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c0 _visitors_c1 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          ()
      method visit_sp :
          type v0 v1 v2 .
            unit -> unit -> unit -> 'env -> (v0, v1, v2) sp -> unit =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_this ->
          match _visitors_this with
          | Empty ->
            self#visit_sp_Empty _visit_arg0 _visit_arg1 _visit_arg2 env
          | Cons (_visitors_c0, _visitors_c1) ->
            self#visit_sp_Cons _visit_arg0 _visit_arg1 _visit_arg2 env
              _visitors_c0 _visitors_c1
      method visit_Lam :
          'var0 'var1 'var2 .
            unit -> unit -> 'env -> (('var0, 'var1 base) cons, 'var2) tm ->
              unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_Box :
          'var0 'var1 .
            unit -> unit -> 'env -> (nil, 'var0) tm -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_Var :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1 base) var -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_C :
          'var0 'var1 'var2 .
            unit -> unit -> 'env -> 'var0 X.constructor ->
              ('var1, 'var0, 'var2 base) sp -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let () =
            let _visit_arg0 = () in
            self#visit_constructor _visit_arg0 env _visitors_c0 in
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          ()
      method visit_tm :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) tm -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Lam _visitors_c0 ->
            self#visit_Lam _visit_arg0 _visit_arg1 env _visitors_c0
          | Box _visitors_c0 ->
            self#visit_Box _visit_arg0 _visit_arg1 env _visitors_c0
          | Var _visitors_c0 ->
            self#visit_Var _visit_arg0 _visit_arg1 env _visitors_c0
          | C (_visitors_c0, _visitors_c1) ->
            self#visit_C _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Id : 'var0 . unit -> unit -> 'env -> unit =
        fun _visit_arg0 _visit_arg1 env -> ()
      method visit_Suc :
          'var0 'var1 'var2 . unit -> unit -> 'env ->
            ('var0, 'var1) shift -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_shift :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) shift -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Id ->
            self#visit_Id _visit_arg0 _visit_arg1 env
          | Suc _visitors_c0 ->
            self#visit_Suc _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_ShiftR :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1) shift -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_DotR :
          'var0 'var1 'var2 .
            unit -> unit -> 'env -> ('var0, 'var1) ren -> ('var1, 'var2) var ->
              unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_ren _visit_arg0 _visit_arg1 env _visitors_c0 in
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c1 in
          ()
      method visit_ren :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) ren -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | ShiftR _visitors_c0 ->
            self#visit_ShiftR _visit_arg0 _visit_arg1 env _visitors_c0
          | DotR (_visitors_c0, _visitors_c1) ->
            self#visit_DotR _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Shift :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1) shift -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          ()
      method visit_Dot :
          'var0 'var1 'var2 .
            unit -> unit -> 'env -> ('var0, 'var1) sub -> ('var1, 'var2) tm ->
              unit =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_sub _visit_arg0 _visit_arg1 env _visitors_c0 in
          let () =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c1 in
          ()
      method visit_sub :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) sub -> unit =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Shift _visitors_c0 ->
            self#visit_Shift _visit_arg0 _visit_arg1 env _visitors_c0
          | Dot (_visitors_c0, _visitors_c1) ->
            self#visit_Dot _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
    end

    class virtual ['self] map = object (self : 'self)
      inherit [_] base_map
      method virtual visit_constructor :
        'v0_in 'v0_out .
          unit -> 'env -> 'v0_in X.constructor -> 'v0_in X.constructor
      method visit_Top :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> 'env ->
              (('var0_in , 'var1_in base) cons, 'var1_in base) var =
        fun _visit_arg0 _visit_arg1 env -> Top
      method visit_Pop :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env ->
              ('var0_in, 'var1_in base) var ->
                (('var0_in, 'var2_in base) cons, 'var1_in base) var =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0 in
          Pop _visitors_r0
      method visit_var :
          type v0_in v1_in v0_out v1_out .
            unit -> unit -> 'env -> (v0_in, v1_in) var -> (v0_in, v1_in) var =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Top ->
            self#visit_Top _visit_arg0 _visit_arg1 env
          | Pop v ->
            self#visit_Pop _visit_arg0 _visit_arg1 env v
      method visit_sp_Empty :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> unit -> 'env -> ('var0_in, 'var1_in, 'var1_in) sp =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env -> Empty
      method visit_sp_Cons :
          'var0_in  'var1_in  'var2_in  'var3_in
               'var0_out 'var1_out 'var2_out 'var3_out .
            unit-> unit -> unit -> 'env ->
              ('var0_in, 'var1_in) tm -> ('var0_in, 'var2_in, 'var3_in) sp ->
                ('var0_in, ('var1_in, 'var2_in) arr, 'var3_in) sp =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          Cons (_visitors_r0, _visitors_r1)
      method visit_sp :
          type v0_in v1_in v2_in v0_out v1_out v2_out .
            unit -> unit -> unit -> 'env ->
              (v0_in, v1_in, v2_in) sp -> (v0_in, v1_in, v2_in) sp =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_this ->
          match _visitors_this with
          | Empty ->
            self#visit_sp_Empty _visit_arg0 _visit_arg1 _visit_arg2 env
          | Cons (_visitors_c0, _visitors_c1) ->
            self#visit_sp_Cons _visit_arg0 _visit_arg1 _visit_arg2 env
              _visitors_c0 _visitors_c1
      method visit_Lam :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env ->
              (('var0_in, 'var1_in base) cons, 'var2_in) tm ->
                ('var0_in, ('var1_in base, 'var2_in) arr) tm =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          Lam _visitors_r0
      method visit_Box :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> 'env -> (nil, 'var0_in) tm ->
              ('var1_in, 'var0_in boxed) tm =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          Box _visitors_r0
      method visit_Var :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> 'env -> ('var0_in, 'var1_in base) var ->
              ('var0_in, 'var1_in base) tm =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0 in
          Var _visitors_r0
      method visit_C :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env ->
              'var0_in X.constructor ->
                ('var1_in, 'var0_in, 'var2_in base) sp ->
                  ('var1_in, 'var2_in base) tm =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            self#visit_constructor _visit_arg0 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          C (_visitors_r0, _visitors_r1)
      method visit_tm :
          type v0_in v1_in v0_out v1_out .
            unit -> unit -> 'env -> (v0_in, v1_in) tm -> (v0_in, v1_in) tm =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Lam _visitors_c0 ->
            self#visit_Lam _visit_arg0 _visit_arg1 env _visitors_c0
          | Box _visitors_c0 ->
            self#visit_Box _visit_arg0 _visit_arg1 env _visitors_c0
          | Var _visitors_c0 ->
            self#visit_Var _visit_arg0 _visit_arg1 env _visitors_c0
          | C (_visitors_c0, _visitors_c1) ->
            self#visit_C _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Id :
          'var0_in 'var0_out . unit -> unit -> 'env ->
            ('var0_in, 'var0_in) shift =
        fun _visit_arg0 _visit_arg1 env -> Id
      method visit_Suc :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env -> ('var0_in, 'var1_in) shift ->
              ('var0_in, ('var1_in , 'var2_in base) cons) shift =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          Suc _visitors_r0
      method visit_shift :
          type v0_in v1_in v0_out v1_out .
            unit -> unit -> 'env -> (v0_in, v1_in) shift ->
              (v0_in, v1_in) shift =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Id ->
            self#visit_Id _visit_arg0 _visit_arg1 env
          | Suc _visitors_c0 ->
            self#visit_Suc _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_ShiftR :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> 'env -> ('var0_in, 'var1_in) shift ->
              ('var0_in, 'var1_in) ren =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          ShiftR _visitors_r0
      method visit_DotR :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env -> ('var0_in, 'var1_in) ren ->
              ('var1_in, 'var2_in base) var ->
                (('var0_in, 'var2_in base) cons, 'var1_in) ren =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_ren _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c1 in
          DotR (_visitors_r0, _visitors_r1)
      method visit_ren :
          type v0_in v1_in v0_out v1_out .
            unit -> unit -> 'env -> (v0_in, v1_in) ren -> (v0_in, v1_in) ren =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | ShiftR _visitors_c0 ->
            self#visit_ShiftR _visit_arg0 _visit_arg1 env _visitors_c0
          | DotR (_visitors_c0, _visitors_c1) ->
            self#visit_DotR _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Shift :
          'var0_in 'var1_in 'var0_out 'var1_out .
            unit -> unit -> 'env -> ('var0_in, 'var1_in) shift ->
              ('var0_in, 'var1_in) sub =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0 in
          Shift _visitors_r0
      method visit_Dot :
          'var0_in 'var1_in 'var2_in 'var0_out 'var1_out 'var2_out .
            unit -> unit -> 'env ->
              ('var0_in, 'var1_in) sub -> ('var1_in, 'var2_in) tm ->
                (('var0_in, 'var2_in) cons, 'var1_in) sub =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_sub _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c1 in
          Dot (_visitors_r0, _visitors_r1)
      method visit_sub :
          type v0_in v1_in v0_out v1_out .
            unit -> unit -> 'env -> (v0_in, v1_in) sub -> (v0_in, v1_in) sub =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Shift _visitors_c0 ->
            self#visit_Shift _visit_arg0 _visit_arg1 env _visitors_c0
          | Dot (_visitors_c0, _visitors_c1) ->
            self#visit_Dot _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
    end

    class virtual ['self] reduce = object (self : 'self)
      inherit [_] base_reduce
      method virtual visit_constructor :
       'v0 . unit -> 'env -> 'v0 X.constructor -> 'res
      method visit_Top : 'var0 'var1 . unit -> unit -> 'env -> 'res =
        fun _visit_arg0 _visit_arg1 env ->
          self#zero
      method visit_Pop :
          'var0 'var1 'var2 . unit -> unit -> 'env ->
            ('var0, 'var1 base) var -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_var :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) var -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Top ->
            self#visit_Top _visit_arg0 _visit_arg1 env
          | Pop v ->
            self#visit_Pop _visit_arg0 _visit_arg1 env v
      method visit_sp_Empty :
          'var0 'var1 . unit -> unit -> unit -> 'env -> 'res =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env ->
          self#zero
      method visit_sp_Cons :
          'var0 'var1 'var2 'var3 .
            unit-> unit -> unit -> 'env -> ('var0, 'var1) tm ->
              ('var0, 'var2, 'var3) sp -> 'res =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          self#plus _visitors_r0 _visitors_r1
      method visit_sp :
          type v0 v1 v2 .
            unit -> unit -> unit -> 'env -> (v0, v1, v2) sp -> 'res =
        fun _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_this ->
          match _visitors_this with
          | Empty ->
            self#visit_sp_Empty _visit_arg0 _visit_arg1 _visit_arg2 env
          | Cons (_visitors_c0, _visitors_c1) ->
            self#visit_sp_Cons _visit_arg0 _visit_arg1 _visit_arg2 env
              _visitors_c0 _visitors_c1
      method visit_Lam :
          'var0 'var1 'var2 .
            unit -> unit -> 'env ->
              (('var0, 'var1 base) cons, 'var2) tm -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_Box :
          'var0 'var1 .
            unit -> unit -> 'env -> (nil, 'var0) tm -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_Var :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1 base) var -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_var _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_C :
          'var0 'var1 'var2 .
            unit -> unit -> 'env -> 'var0 X.constructor ->
              ('var1, 'var0, 'var2 base) sp -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            self#visit_constructor _visit_arg0 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            let _visit_arg2 = () in
            self#visit_sp _visit_arg0 _visit_arg1 _visit_arg2 env _visitors_c1 in
          self#plus _visitors_r0 _visitors_r1
      method visit_tm :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) tm -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Lam _visitors_c0 ->
            self#visit_Lam _visit_arg0 _visit_arg1 env _visitors_c0
          | Box _visitors_c0 ->
            self#visit_Box _visit_arg0 _visit_arg1 env _visitors_c0
          | Var _visitors_c0 ->
            self#visit_Var _visit_arg0 _visit_arg1 env _visitors_c0
          | C (_visitors_c0, _visitors_c1) ->
            self#visit_C _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Id : 'var0 . unit -> unit -> 'env -> 'res =
        fun _visit_arg0 _visit_arg1 env ->
          self#zero
      method visit_Suc :
          'var0 'var1 'var2 . unit -> unit -> 'env ->
            ('var0, 'var1) shift -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_shift :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) shift -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Id ->
            self#visit_Id _visit_arg0 _visit_arg1 env
          | Suc _visitors_c0 ->
            self#visit_Suc _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_ShiftR :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1) shift -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_DotR :
          'var0 'var1 'var2 .
            unit -> unit -> 'env ->
              ('var0, 'var1) ren -> ('var1, 'var2) var -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_ren _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_var _visit_arg0 _visit_arg1 env _visitors_c1 in
          self#plus _visitors_r0 _visitors_r1
      method visit_ren :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) ren -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | ShiftR _visitors_c0 ->
            self#visit_ShiftR _visit_arg0 _visit_arg1 env _visitors_c0
          | DotR (_visitors_c0, _visitors_c1) ->
            self#visit_DotR _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
      method visit_Shift :
          'var0 'var1 .
            unit -> unit -> 'env -> ('var0, 'var1) shift -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 ->
          let _visit_arg0 = () in
          let _visit_arg1 = () in
          self#visit_shift _visit_arg0 _visit_arg1 env _visitors_c0
      method visit_Dot :
          'var0 'var1 'var2 .
            unit -> unit -> 'env ->
              ('var0, 'var1) sub -> ('var1, 'var2) tm -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1 ->
          let _visitors_r0 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_sub _visit_arg0 _visit_arg1 env _visitors_c0 in
          let _visitors_r1 =
            let _visit_arg0 = () in
            let _visit_arg1 = () in
            self#visit_tm _visit_arg0 _visit_arg1 env _visitors_c1 in
          self#plus _visitors_r0 _visitors_r1
      method visit_sub :
          type v0 v1 . unit -> unit -> 'env -> (v0, v1) sub -> 'res =
        fun _visit_arg0 _visit_arg1 env _visitors_this ->
          match _visitors_this with
          | Shift _visitors_c0 ->
            self#visit_Shift _visit_arg0 _visit_arg1 env _visitors_c0
          | Dot (_visitors_c0, _visitors_c1) ->
            self#visit_Dot _visit_arg0 _visit_arg1 env _visitors_c0 _visitors_c1
    end

    (* Functions *)

    (* Shifts of indices *)

    let rec shift_var : type g d a. (g, d) shift -> (g, a base) var -> (d, a base) var =
      fun sh v -> match sh with
		  | Id -> v
		  | Suc sh -> Pop (shift_var sh v)

    (* Some alternative recursion schemes for defining the shift_var function *)

    let shift_var (type g) (v : (g, 'a base) var) =
      let rec shift_var : type d . (g, d) shift -> (d, 'a base) var =
        function
        | Id -> v
        | Suc sh -> Pop (shift_var sh) in
      shift_var

    let rec shift_var : type g d. (g, d) shift -> (g, 'a base) var -> (d, 'a base) var =
      function
      | Id ->
        (* g = d : need a function (g, 'a basee) var -> (g, 'a base) var *)
        (fun v -> v)
      | Suc sh ->
        (* d = ($0, $1 base) cons *)
        (* sh of type (g, $0) shift *)
        (* Need a function (g, 'a base) var -> (($0, $1 base) cons, 'a base) var *)
        let f = shift_var sh in
        (* f of type (g, 'a base) var -> ($0, 'base) var *)
        (fun v -> Pop (f v))

    (* Dependent reducers for the shift type *)
    module ReduceShift = struct
      module Make (X : sig type ('g, 'd) t end) =
      struct
        class virtual ['self] reduce = object (self : 'self)
          method reduce_Id : type g . (g, g) X.t =
            failwith "Must be overridden"
          method reduce_Suc :
              type g e f . (g, e) X.t -> (g, (e, f base) cons) X.t =
            failwith "Must be overridden"
          method reduce_shift : type g d . (g, d) shift -> (g, d) X.t =
            function
            | Id ->
              self#reduce_Id
            | Suc sh ->
              let f = self#reduce_shift sh in
              self#reduce_Suc f
        end
      end
      module Make1 (X : sig type ('g, 'd, 'v0) t end) =
      struct
        class ['self] reduce = object (self : 'self)
          method reduce_Id : type g v0 . (g, g, v0) X.t =
            failwith "Must be overridden"
          method reduce_Suc :
              type g e f v0 . (g, e, v0) X.t -> (g, (e, f base) cons, v0) X.t =
            failwith "Must be overridden"
          method reduce_shift : type g d v0. (g, d) shift -> (g, d, v0) X.t =
            function
            | Id ->
              self#reduce_Id
            | Suc sh ->
              let f = self#reduce_shift sh in
              self#reduce_Suc f
        end
      end
    end

    let shift_var sh v =
      let module M =
        ReduceShift.Make1
          (struct
            type ('g, 'd, 'a) t = ('g, 'a base) var -> ('d, 'a base) var
          end) in
      let visitor = object (self)
        inherit [_] M.reduce as super
        method! reduce_Id    = (fun v -> v)
        method! reduce_Suc f = (fun v -> Pop (f v))
      end in
      visitor#reduce_shift sh v

    let rec compose_shift : type g d e. (g, d) shift -> (d, e) shift -> (g, e) shift =
      fun sh -> function
	     | Id -> sh
	     | Suc shh -> Suc (compose_shift sh shh)

    (* Renamings *)

    let rec lookup_ren : type g d a. ((g, a base) var * (g, d) ren) -> (d, a base) var =
      function
      | Top, DotR (_, v') -> v'
      | Pop v, DotR (r, _) -> lookup_ren (v, r)
      | v, ShiftR sh -> shift_var sh v

    let rec shift_ren : type g d e. (d, e) shift -> (g, d) ren -> (g , e) ren =
      fun sh -> function
	     | ShiftR sh' -> ShiftR (compose_shift sh' sh)
	     | DotR (r, v) -> DotR(shift_ren sh r, shift_var sh v)

    let wkn_ren : type g d a. (g, d) ren -> ((g, a base) cons, (d, a base) cons) ren =
      fun s -> DotR(shift_ren (Suc Id) s, Top)

    let rec ren_sp : type g d t t'. (g, d) ren -> (g, t, t') sp -> (d, t, t') sp =
      fun r -> function
	    | Empty -> Empty
	    | Cons (m, sp) -> Cons(ren_tm r m, ren_sp r sp)

    and ren_tm : type g d t. (g, d) ren -> (g, t) tm -> (d, t) tm =
      fun r -> function
	    | Lam m -> Lam (ren_tm (wkn_ren r) m)
	    | Box m -> Box m
    	    | Var v -> Var (lookup_ren (v, r))
    	    | C (c, sp) -> C (c, ren_sp r sp)


    let rec shift_sp : type g d t t1. (g, d) shift -> (g, t, t1) sp -> (d, t, t1) sp =
      fun sh -> function
	     | Empty -> Empty
	     | Cons (m, sp) -> Cons (shift_tm sh m, shift_sp sh sp)

    and shift_tm : type g d t. (g, d) shift -> (g, t) tm -> (d, t) tm =
      fun sh -> function
	     | Lam m -> Lam (ren_tm (DotR (ShiftR (Suc sh), Top)) m)
	     | Box m -> Box m
    	     | Var v -> Var (shift_var sh v)
    	     | C (c, sp) -> C (c, shift_sp sh sp)

    (* Substitutions *)

    let rec lookup : type g d a. ((g, a base) var * (g, d) sub) -> (d, a base) tm =
      function
      | Top, Dot (_, n) -> n
      | Pop v, Dot (s, _) -> lookup (v, s)
      | v, Shift sh -> Var (shift_var sh v)

    let rec shift_sub : type g d e. (d, e) shift -> (g, d) sub -> (g , e) sub =
      fun sh -> function
	     | Shift sh' -> Shift (compose_shift sh' sh)
	     | Dot (s, n) -> Dot(shift_sub sh s, shift_tm sh n)

    let wkn_sub : type g d a. (g, d) sub -> ((g, a base) cons, (d, a base) cons) sub =
      fun s -> Dot(shift_sub (Suc Id) s, Var Top)

    let rec sub_sp : type g d t t1. (g, d) sub -> (g, t, t1) sp -> (d, t, t1) sp =
      fun s -> function
	    | Empty -> Empty
	    | Cons (m, sp) -> Cons(sub_tm s m, sub_sp s sp)

    and sub_tm : type g d t. (g, d) sub -> (g, t) tm -> (d, t) tm =
      fun s -> function
	    | Lam m -> Lam (sub_tm (wkn_sub s) m)
	    | Box m -> Box m
    	    | Var v -> lookup (v, s)
    	    | C (c, sp) -> C (c, sub_sp s sp)

    let single_subst : type g d s t. ((g, s) cons, t) tm -> (g, s) tm -> (g, t) tm =
      fun m n -> sub_tm (Dot (Shift Id, n)) m

     (* Pretty printer  *)

    let rec pp_tm : type g t . Format.formatter -> (g, t) tm -> unit =
      fun f t -> match t with
		 | Lam m -> Format.fprintf f "\\x. %a" pp_tm m
		 | Box m -> Format.fprintf f "{%a}" pp_tm m
		 | Var v -> pp_var f v
		 | C (c, sp) -> Format.fprintf f "%s %a" (X.to_string c) pp_sp sp

   and pp_sp : type g s t . Format.formatter -> (g, s, t) sp -> unit =
      fun f sp -> match sp with
		  | Empty -> ()
		  | Cons (m, Empty) -> Format.fprintf f "%a" pp_tm m
		  | Cons (m, sp) -> Format.fprintf f "(%a %a)" pp_tm m pp_sp sp
   and pp_var : type g t . Format.formatter -> (g, t) var -> unit =
      let rec var_to_int : type g t. (g, t) var -> int = function
	| Top -> 0
	| Pop v' -> 1 + var_to_int v'
      in
      fun f v -> Format.fprintf f "%d" (var_to_int v)
  end


(* Examples *)

(** The lambda caluclus **)

module LC =
struct

  (* The 'kind' of lambda terms *)
  type lc = L (* The constructor is not really needed *)

  (* the cosntructors of lambda terms *)
  type 'a lc_constructor =
    | LC : (lc base) lc_constructor
    | LApp : ((lc base, (lc base, lc base) arr) arr) lc_constructor
    | LLam : (((lc base, lc base) arr, lc base) arr) lc_constructor

  let rec lc_to_string : type a. (a lc_constructor) -> string = fun t ->
    match t with
    | LC -> "C"
    | LApp -> "App"
    | LLam -> "Lam"

  (* The syntax of lambda terms *)
  module LCSyn = SyntacticFramework(
    struct
      type 'a constructor = 'a lc_constructor
       let to_string = lc_to_string
    end)

  open LCSyn

  (* Smart constructors for the lambda calculus *)
  let app m n =
    C(LApp, Cons(m, Cons(n, Empty)))

  let lam m =
    C(LLam, Cons(Lam m, Empty))

  let c =
    C(LC, Empty)

  let top =
    Var Top

  (* some sample terms *)
  let tm_lc = c
  let tm_id = 
    C(LLam, Cons(Lam top, Empty))
  (* When we are not constructing terms directly, we have to wrap the result
     in a thunk, since type variables resulting from an application cannot
     be generalised. *)
  let mk_tm_id : 'g . unit -> ('g, lc base) LCSyn.tm = 
    fun () ->
      lam top
    (* C(LLam, Cons(Lam top, Empty)) *)
  let mk_tm_omega : 'g . unit -> ('g, lc base) LCSyn.tm =
    fun () -> lam (app top top)
  let mk_tm_Omega : 'g . unit -> ('g, lc base) LCSyn.tm =
    fun () -> app (mk_tm_omega ()) (mk_tm_omega ())

  (* Can this function be written without dependent types? n -> Fin n  *)
  (* let rec v (n : int) = let open LCSyn in *)
  (*   if n < 0 then failwith "De Bruijn indices have to be natural numbers" *)
  (*   else if n = 0 then Top *)
  (*   else Pop (v (n - 1)) *)

  let count idx tm =
    let rec count : type g a . int -> (g, a) tm -> int =
      fun idx ->
        function
        | Box _ ->
          (* we know that boxed terms are closed *)
          0
        | Var v ->
          begin match v with
          | Top ->
            if (Int.equal idx 0) then 1 else 0
          | Pop v' ->
            count (idx - 1) (Var v')
          end
        | Lam t ->
          (* Shift the variable up when moving under a lambda *)
          count (idx + 1) t
        | C (_, s) ->
          count_sp idx s
    and count_sp : type g a b . int -> (g, a, b) sp -> int =
      fun idx ->
        function
        | Empty ->
          0
        | Cons (t, s) ->
          (count idx t) + (count_sp idx s) in
    if Int.(0 > idx) then 0 else count idx tm

  (* And now for the visitor-based version! *)
  let count idx tm =
    let visitor = object (self)
      inherit [_] reduce as super
      method zero = 0
      method plus m n = Int.(m + n)
      method visit_constructor () _ _ = self#zero
      method! visit_Box () () _ _ = self#zero
      (* We don't need to override visit_Var,
         only the visit methods for Top and Pop  *)
      method! visit_Top () () idx =
        if (Int.equal idx 0) then 1 else 0
      method! visit_Pop () () idx v =
          self#visit_var () () (idx - 1) v
      method! visit_Lam () () idx t =
        (* Shift the variable up when moving under a lambda *)
        self#visit_tm () () (idx + 1) t
      (* Don't need to override visit_C as it uses the default recursion *)
      method! visit_sp_Empty () () () _ = self#zero
      (* Don't need to override visit_sp_Cons as it uses the default recursion *)
    end in
  visitor#visit_tm () () idx tm
  
  ;;

  (* Tests *)

  let tm_omega = mk_tm_omega () in
  assert (Int.equal (count 0 tm_omega) 0) ;;

  let tm_Omega = mk_tm_Omega () in
  assert (Int.equal (count 0 tm_Omega) 0) ;;

  let tm_omega = mk_tm_omega () in
  assert (Int.equal (count 1 tm_omega) 0) ;;
  
  let tm_Omega = mk_tm_Omega () in
  assert (Int.equal (count 1 tm_Omega) 0) ;;

end
