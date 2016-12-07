open Sf

[@@@signature {def|

exp   : type.
value : type.

app   : exp -> exp -> exp.
lam   : (value -> exp) -> value.
ret   : value -> exp.

(* CPS representation *)

contra : type.
cvalue : type.
kont: type.

capp   : cvalue -> cvalue -> kont -> contra.
clam   : (cvalue -> kont -> contra) -> cvalue.

kk: (cvalue -> contra) -> kont.
adm: kont -> cvalue -> contra.

(* Closure conversion *)

ccontra : type.
ccvalue : type.
ckont: type.
bds : type.

e : (cvalue -> kont -> contra) -> bds.
c : (cvalue -> bds) -> bds.

sub: type.
empty : sub.
dot: sub -> cvalue -> sub.


ccapp   : cvalue -> cvalue -> kont -> contra.
cclam   : {bds} -> cvalue.
clo: cvalue -> sub -> cvalue.

ckk: (cvalue -> contra) -> kont.
cadm: kont -> cvalue -> contra.


|def}]

type (_, _) rel
  = Empty : (nil, nil) rel
  | Both : ('g, 'd) rel -> (('g, tp_value base) cons, ('d, tp_cvalue base) cons) rel

let rec lookup [@type "g d . [g |- value] -> (g, d) rel -> [d |- cvalue]"] =
  fun t -> function
	| Empty -> assert false (* cannot lookup in an empty context *)
	| Both r' ->
	   begin match t with
		 | {p| *, x |- x |p} -> {t| *,x |- x |t}
		 | {p| *, x |- ##v |p} ->
		    let v1 =  lookup {t| #v |t} r'
		    in {t|*, x |- 'v1 [^1 ;] |t}
	   end

let rec cps [@type "g d . (g, d) rel -> [g |- value] -> [d |- cvalue]"] =
  fun r -> function
	| {p| #x |p} -> lookup {t| #x |t} r
	| {p| lam (\x. 'e) |p} ->
	   let ce = cpse (Both r) {t|g, x |-  'e  |t} in
	   {t| clam (\cv. \cc. 'ce[^2 ; cv ; cc]) |t}


and cpse [@type "g d. (g, d) rel -> [g |- exp] -> [d, k: kont |- contra]"] =
  fun r -> function
	| {p| ret 'v |p} ->
	   let vv = cps r {t| 'v |t} in
	   {t| *, k |- adm k ('vv[^1 ;]) |t}

	| {p| app 'm 'n |p} ->
	   let mm = cpse r m in
	   let nn = cpse r n in
	   {t| *, k |- 'mm [^1 ; (kk (\f. 'nn [^2 ; (kk (\x. capp f x k))]))] |t}
	| _ -> assert false


(* applies some of the administrative redeces *)
let rec ar [@type "d. [d, k: kont |- contra] -> [d, k: kont |- contra]"] =
  function
  | {p| adm (kk (\vv. 'k1)) 'v |p} -> ar {t|  *, kc|- 'k1 [^1 ; kc ; 'v] |t}
  | {p| adm #k 'v |p} -> (* it doesn't remove these stuck continuations *)
     let vv = arv v in
     {t|adm #k 'vv |t}
  | {p| capp 'm 'n 'k |p} ->
     let mm = arv m in
     let nn = arv n in
     let kk = ark k in
     {t| capp 'mm 'nn 'kk |t}
  | {p| #x |p} -> {t| #x |t}

and arv [@type "d. [d |- cvalue] -> [d |- cvalue]"] =
  function
  | {p| clam (\x.\k. 'm) |p} ->
     let mm = ar m in
     {t| clam (\x.\k. 'mm) |t}
  | {p| #x |p} -> {t| #x |t}

and ark [@type "d. [d, k: kont |- kont] -> [d, k: kont |- kont]"] =
  function
  | {p| kk (\v. 'mv) |p} ->
     let mvv = ar {t| *, k, v |-  'mv [^2 ; v ; k] |t} in
     {t| *, k |- kk (\v. 'mvv[^2 ; v ; k]) |t}

let id_fun = {t| lam (\x. ret x) |t}

let id_fun_k = cps Empty id_fun

let id_fun_k_adm = arv id_fun_k
