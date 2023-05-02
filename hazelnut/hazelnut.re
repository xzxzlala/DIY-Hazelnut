open Sexplib.Std;
open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

[@deriving (sexp, compare)]
type htyp =
  | Arrow(htyp, htyp)
  | Num
  | Hole;

[@deriving (sexp, compare)]
type hexp =
  | Var(string)
  | Lam(string, hexp)
  | Ap(hexp, hexp)
  | Lit(int)
  | Plus(hexp, hexp)
  | Asc(hexp, htyp)
  | EHole
  | NEHole(hexp);

[@deriving (sexp, compare)]
type ztyp =
  | Cursor(htyp)
  | LArrow(ztyp, htyp)
  | RArrow(htyp, ztyp);

[@deriving (sexp, compare)]
type zexp =
  | Cursor(hexp)
  | Lam(string, zexp)
  | LAp(zexp, hexp)
  | RAp(hexp, zexp)
  | LPlus(zexp, hexp)
  | RPlus(hexp, zexp)
  | LAsc(zexp, htyp)
  | RAsc(hexp, ztyp)
  | NEHole(zexp);

[@deriving (sexp, compare)]
type child =
  | One
  | Two;

[@deriving (sexp, compare)]
type dir =
  | Child(child)
  | Parent;

[@deriving (sexp, compare)]
type shape =
  | Arrow
  | Num
  | Asc
  | Var(string)
  | Lam(string)
  | Ap
  | Lit(int)
  | Plus
  | NEHole;

[@deriving (sexp, compare)]
type action =
  | Move(dir)
  | Construct(shape)
  | Del
  | Finish;

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(htyp);

exception Unimplemented;
let rec type_com = (t1: hype, t2: hype): bool => {
  if t1 == Hole then true
  else if t2 == Hole then true
  else if t1 == t2 then true
  else {
    switch (t1, t2) {
    | (Arrow(t11, t12), Arrow(t21, t22)) => (type_com(t11, t21) && type_com(t12, t22))
    | _=> false
    };
  }
}
let type_incom = (t1: hype, t2: hype): bool => {
  switch (t1,t2) {
  | (Num, Arrow(_, _)) => true
  | (Arrow(_,_), Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) => type_incom(t11,t21)
  | (Arrow(t11, t12), Arrow(t21, t22))  => type_incom(t12,t22)
  | _ => false
  };
}
let fun_type_match = (t:hype): option(htyp) => {
  switch (t) {
  | Hole=> Some(Arrow(Hole, Hole))
  | Arrow(t1',t2') => Some(Arrow(t1',t2'))
  | _ => None
  };
}
let rec erase_typ = (ty: ztyp): htyp => {
  // Performs cursor erasure described in Hazelnut Part 3.2
  switch (ty) {
  | Cursor(ty') => ty'
  | LArrow(ty1,ty2) => Arrow(erase_typ(ty1), ty2)
  | RArrow(ty1,ty2) => Arrow(ty1, erase_typ(ty2))
  };
};
let rec erase_exp = (e: zexp): hexp => {
  // Performs cursor erasure described in Hazelnut Part 3.2
  switch (e) {
  | Cursor(e') => e'
  | Lam(x,e') => Lam(x, erase_exp(e'))
  | LAp(e1,e2) => Ap(erase_exp(e1), e2)
  | RAp(e1,e2) => Ap(e1, erase_exp(e2))
  | LPlus(e1,e2) => Plus(erase_exp(e1), e2)
  | RPlus(e1,e2) => Plus(e1, erase_exp(e2))
  | LAsc(e1,t) => Asc(erase_exp(e1), t)
  | RAsc(e1,t) => Asc(e1, erase_typ(t))
  | NEHole(e') => NEHole(erase_exp(e'))
  };
};

let syn = (ctx: typctx, e: hexp): option(htyp) => {
  // Performs synthesis described in Hazelnut Part 3.1. Returns None if the expression cannot sythesize a type.
    switch (e) {
    | Ap(e1,e2) => {
      let+ t1 = syn(ctx, e1);
      let+ Arrow(r1,r2) = fun_type_match(t1);
      ana(ctx, e2, r1);
    }
    | Lit(_) => Some(Num)
    | Var(x) => ctx.find_opt(x)
    | Plus(e1,e2) => (ana(ctx, e1, Num)&&ana(ctx, e2, Num))
    | EHole => Some(Hole)
    | NEHole(e) => {
      let+ t = syn(ctx, e);
      Some(Hole)
    }
    | Asc(e1, ty1) => ana(ctx, e1, ty1)
    | _ => None 
    };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  switch (e) {
    | Lam(x,e') => {
      let+ Arrow(t1,t2) = fun_type_match(t);
      let ctx' = TypCtx.add(x, t1, ctx);
      ana(ctx', e', t2)
    }
    | _ => {
      let+ t' = syn(ctx, e);
      type_com(t, t')
    }
  };
};
let rec type_action = (ty: ztyp, a: action): ztyp => {
  // Performs type movement described in Hazelnut Part 3.3
  switch (ty, a) {
  | (Cursor(Arrow(ty1, ty2)), move(Child(One))) => LArrow(Cursor(ty1), ty2)
  | (Cursor(Arrow(ty1, ty2)), move(Child(Two))) => RArrow(ty1, Cursor(ty2))
  | (LArrow(Cursor(ty1), ty2), move(Parent)) => Cursor(ty)
  | (RArrow(ty1, Cursor(ty2)), move(Parent)) => Cursor(ty)
  | (_, Del) => Cursor(EHole)
  | (Cursor(ty'), Construct(Arrow)) => RArrow(ty',Cursor(EHole))
  | (Cursor(EHole), Construct(Num)) => Cursor(Num)
  | (LArrow(ty1, ty2), a) => LArrow(type_action(ty1, a), ty2)
  | (RArrow(ty1, ty2), a) => RArrow(ty1, type_action(ty2, a))
  }; 
} 
let rec exp_move = (e: zexp, a: action): zexp => {
  // Performs expression movement described in Hazelnut Part 3.3
  switch (e,a) {
  | (Cursor(Asc(e1, t)), move(Child(One))) => LAsc(Cursor(e1), t)
  | (Cursor(Asc(e1, t)), move(Child(Two))) => RAsc(e1, Cursor(t))
  | (LAsc(Cursor(e1), t), move(Parent)) => Cursor(e)
  | (RAsc(e1, Cursor(t)), move(Parent)) => Cursor(e)
  | (Lam(x, Cursor(e)), move(Parent)) => Cursor(e)
  | (Cursor(Lam(x, e)), move(Child(One))) => Lam(x, Cursor(e))
  | (Cursor(Plus(e1, e2)), move(Child(One)) )=> LPlus(Cursor(e1), e2)
  | (Cursor(Plus(e1, e2)), move(Child(Two))) => RPlus(e1, Cursor(e2))
  | (LPlus(Cursor(e1), e2), move(Parent) )=> Cursor(e)
  | (RPlus(e1, Cursor(e2)), move(Parent) )=> Cursor(e)
  | (Cursor(Ap(e1, e2)), move(Child(One))) => LAp(Cursor(e1), e2)
  | (Cursor(Ap(e1, e2)), move(Child(Two)) )=> RAp(e1, Cursor(e2))
  | (LAp(Cursor(e1), e2), move(Parent) )=> Cursor(e)
  | (RAp(e1, Cursor(e2)), move(Parent) )=> Cursor(e)
  | (Cursor(NEHole(e)), move(Child(One)) )=> NEHole(Cursor(e))
  | (NEHole(Cursor(e)), move(Parent) )=> Cursor(e)
  };
}

let syn_action =
    (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Performs a synthetic action described in Hazelnut Part 3.3. Returns None if the action cannot be performed.
  switch (e, t, a) {
  | (e, t, move(a) )=> Some((exp_move(e, a), t))
  | (Cursor(e), _, Del )=> Some((Cursor(EHole), Hole))
  | (Cursor(e), t, Construct(Asc) )=> Some(RAsc(e, Cursor(t)),t)
  | (Cursor(EHole), Hole, Construct(Lam(x)) )=> Some(RAsc(Lam(x,EHole), LArrow(Cursor(Hole),Hole),Arrow(Hole,Hole)))
  | (Cursor(EHole), Hole, Construct(Var(x)) )=> 
    let+ ty=ctx.find_opt(x);
    Some(Cursor(x), ty)
  | (Cursor(e), t, Construct(Ap) )=> 
    switch (fun_type_match(t)) {
    | Arrow(t1,t2) => Some(RAp(e, Cursor(EHole)), t2)
    | _ => if type_incom(t, Arrow(Hole,Hole)) then Some(RAp(NEHole(e), Cursor(EHole)), Hole) else None
    };
  | (Cursor(EHole), Hole, Construct(Lit(n)) )=> Some(Cursor(Lit(n)), Num)
  | (Cursor(e), t, Construct(Plus) )=> if type_com(t, Num) then {Some(RPlus(e, Cursor(EHole)), Num)} else {Some(RPlus(NEHole(e), Cursor(EHole)), Num)}
  | (Cursor(e), t, Construct(NEHole) )=> Some(NEHole(e), Hole)
  | (Cursor(NEHole(e)), Hole, Finish) => Some(Cursor(e), syn(ctx, e))
  | (LAsc(e,t1), t2, a )=> 
    if t1 == t2 then {
      let+ e' = ana_action(ctx, e, a, t1); Some(LAsc(e', t1), t1)
      }
    else {None;}
  | (RAsc(e1,t1), t2, a )=> 
    if t1 == erase_typ(t2) then{
    let+ ty' = type_action(t1, a);
    let+ ty'' = erase_typ(ty');
    if ana(ctx, e1, ty'') then {Some(RAsc(e1, ty'), ty'')}
    else {None;}
    }else {None;}
  | _ => None
  };
}
and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
