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
let rec type_com = (t1: htyp, t2: htyp): bool =>
  if (t1 == Hole) {
    true;
  } else if (t2 == Hole) {
    true;
  } else if (t1 == t2) {
    true;
  } else {
    switch (t1, t2) {
    | (Arrow(t11, t12), Arrow(t21, t22)) =>
      type_com(t11, t21) && type_com(t12, t22)
    | _ => false
    };
  };
let rec type_incom = (t1: htyp, t2: htyp): bool => {
  switch (t1, t2) {
  | (Num, Arrow(_, _)) => true
  | (Arrow(_, _), Num) => true
  | (Arrow(t11, t12), Arrow(t21, t22)) =>
    type_incom(t11, t21) || type_incom(t12, t22)
  | _ => false
  };
};
let fun_type_match = (t: htyp): option(htyp) => {
  switch (t) {
  | Hole => Some(Arrow(Hole, Hole))
  | Arrow(t1', t2') => Some(Arrow(t1', t2'))
  | _ => None
  };
};
let rec erase_typ = (ty: ztyp): htyp => {
  // Performs cursor erasure described in Hazelnut Part 3.2
  switch (ty) {
  | Cursor(ty') => ty'
  | LArrow(ty1, ty2) => Arrow(erase_typ(ty1), ty2)
  | RArrow(ty1, ty2) => Arrow(ty1, erase_typ(ty2))
  };
};
let rec erase_exp = (e: zexp): hexp => {
  // Performs cursor erasure described in Hazelnut Part 3.2
  switch (e) {
  | Cursor(e') => e'
  | Lam(x, e') => Lam(x, erase_exp(e'))
  | LAp(e1, e2) => Ap(erase_exp(e1), e2)
  | RAp(e1, e2) => Ap(e1, erase_exp(e2))
  | LPlus(e1, e2) => Plus(erase_exp(e1), e2)
  | RPlus(e1, e2) => Plus(e1, erase_exp(e2))
  | LAsc(e1, t) => Asc(erase_exp(e1), t)
  | RAsc(e1, t) => Asc(e1, erase_typ(t))
  | NEHole(e') => NEHole(erase_exp(e'))
  };
};

let rec syn = (ctx: typctx, e: hexp): option(htyp) => {
  // Performs synthesis described in Hazelnut Part 3.1. Returns None if the expression cannot sythesize a type.
  switch (e) {
  | Ap(e1, e2) =>
    let* t = syn(ctx, e1);
    let* t = fun_type_match(t);
    switch (t) {
    | Arrow(t2, t') =>
      if (ana(ctx, e2, t2)) {
        Some(t');
      } else {
        None;
      };
    | _ => None
    };
  | Lit(_) => Some(Num)
  | Var(x) => TypCtx.find_opt(x, ctx)
  | Plus(e1, e2) =>
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    };
  | EHole => Some(Hole)
  | NEHole(e) =>
    let* _ = syn(ctx, e);
    Some(Hole);
  | Asc(e1, ty1) =>
    if (ana(ctx, e1, ty1)) {
      Some(ty1);
    } else {
      None;
    };
  | _ => None
  };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  switch (e) {
  | Lam(x, e') =>
    switch (fun_type_match(t)) {
    | Some(Arrow(t1, t2)) =>
      let ctx' = TypCtx.add(x, t1, ctx);
      ana(ctx', e', t2);
    | _ => false
    }
  | _ =>
    switch (syn(ctx, e)) {
    | Some(t') => type_com(t, t')
    | _ => false
    }
  };
};
let rec type_action = (ty: ztyp, a: action): option(ztyp) => {
  // Performs type movement described in Hazelnut Part 3.3
  switch (ty, a) {
  | (Cursor(Arrow(ty1, ty2)), Move(Child(One))) => Some(LArrow(Cursor(ty1), ty2))
  | (Cursor(Arrow(ty1, ty2)), Move(Child(Two))) => Some(RArrow(ty1, Cursor(ty2)))
  | (LArrow(Cursor(ty1), ty2), Move(Parent)) => Some(Cursor(Arrow(ty1, ty2)))
  | (RArrow(ty1, Cursor(ty2)), Move(Parent)) => Some(Cursor(Arrow(ty1, ty2)))
  | (Cursor(_), Del) => Some(Cursor(Hole))
  | (Cursor(ty'), Construct(Arrow)) => Some(RArrow(ty', Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) => Some(Cursor(Num))
  | _ => type_action_zipper(ty, a)
  };
} 
and type_action_zipper = (ty: ztyp, a: action): option(ztyp) => {
    switch (ty, a) {
  | (LArrow(ty1, ty2), a) => 
    let* ty1' = type_action(ty1, a);
    Some(LArrow(ty1', ty2))
  | (RArrow(ty1, ty2), a) => 
    let* ty2' = type_action(ty2, a);
    Some(RArrow(ty1, ty2'))
  | _ => None
  };
}
let exp_move = (e: zexp, a: action): option(zexp) => {
  // Performs expression movement described in Hazelnut Part 3.3
  switch (e, a) {
  | (Cursor(Asc(e1, t)), Move(Child(One))) => Some(LAsc(Cursor(e1), t))
  | (Cursor(Asc(e1, t)), Move(Child(Two))) => Some(RAsc(e1, Cursor(t)))
  | (LAsc(Cursor(e1), t), Move(Parent)) => Some(Cursor(Asc(e1, t)))
  | (RAsc(e1, Cursor(t)), Move(Parent)) => Some(Cursor(Asc(e1, t)))
  | (Lam(x, Cursor(e)), Move(Parent)) => Some(Cursor(Lam(x, e)))
  | (Cursor(Lam(x, e)), Move(Child(One))) => Some(Lam(x, Cursor(e)))
  | (Cursor(Plus(e1, e2)), Move(Child(One))) => Some(LPlus(Cursor(e1), e2))
  | (Cursor(Plus(e1, e2)), Move(Child(Two))) => Some(RPlus(e1, Cursor(e2)))
  | (LPlus(Cursor(e1), e2), Move(Parent)) => Some(Cursor(Plus(e1, e2)))
  | (RPlus(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Plus(e1, e2)))
  | (Cursor(Ap(e1, e2)), Move(Child(One))) => Some(LAp(Cursor(e1), e2))
  | (Cursor(Ap(e1, e2)), Move(Child(Two))) => Some(RAp(e1, Cursor(e2)))
  | (LAp(Cursor(e1), e2), Move(Parent)) => Some(Cursor(Ap(e1, e2)))
  | (RAp(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Ap(e1, e2)))
  | (Cursor(NEHole(e)), Move(Child(One))) => Some(NEHole(Cursor(e)))
  | (NEHole(Cursor(e)), Move(Parent)) => Some(Cursor(NEHole(e)))
  | _ => None
  };
};

let rec syn_action =
        (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Performs a synthetic action described in Hazelnut Part 3.3. Returns None if the action cannot be performed.
  switch (e, t, a) {
  | (e, t, Move(_)) => 
    switch ((exp_move(e, a))) {
      | Some(e') => Some((e', t))
      | _ => syn_zipper(ctx, (e, t), a)
    };
  | (Cursor(_), _, Del) => Some((Cursor(EHole), Hole))
  | (Cursor(e), t, Construct(Asc)) => Some((RAsc(e, Cursor(t)), t))
  | (Cursor(EHole), Hole, Construct(Lam(x))) =>
    Some((
      RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  | (Cursor(EHole), Hole, Construct(Var(x))) =>
    switch (TypCtx.find_opt(x, ctx)) {
    | None => syn_zipper(ctx, (e, t), a);
    | Some(ty) => Some((Cursor(Var(x)), ty));
    };
  | (Cursor(e), t, Construct(Ap)) =>
    switch (fun_type_match(t)) {
    | Some(Arrow(_, t2)) => Some((RAp(e, Cursor(EHole)), t2))
    | _ =>
      if (type_incom(t, Arrow(Hole, Hole))) {
        Some((RAp(NEHole(e), Cursor(EHole)), Hole));
      } else {
        syn_zipper(ctx, (Cursor(e), t), a);
      }
    }
  | (Cursor(EHole), Hole, Construct(Lit(n))) =>
    Some((Cursor(Lit(n)), Num))
  | (Cursor(e), t, Construct(Plus)) =>
    if (type_com(t, Num)) {
      Some((RPlus(e, Cursor(EHole)), Num));
    } else {
      Some((RPlus(NEHole(e), Cursor(EHole)), Num));
    };
  | (Cursor(e), _, Construct(NEHole)) => Some((NEHole(Cursor(e)), Hole))
  | (Cursor(NEHole(e)), Hole, Finish) =>
    switch (syn(ctx, e)) {
      | Some(ty) => Some((Cursor(e), ty))
      | None => syn_zipper(ctx, (Cursor(NEHole(e)), t), a);
    }
  | _ => syn_zipper(ctx, (e, t), a)
  };
}
and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  switch (e, a, t) {
  | (e, Move(_), _) => 
    switch (exp_move(e, a)) {
    | Some(e') => Some(e')
    | _ => ana_zipper(ctx, e, a, t)
    };
  | (Cursor(_), Del, _) => Some(Cursor(EHole))
  | (Cursor(e), Construct(Asc), t) => Some(RAsc(e, Cursor(t)))
  | (Cursor(EHole), Construct(Var(x)), t) =>
    switch (TypCtx.find_opt(x, ctx)) {
    | Some(t') =>
      if (type_incom(t, t')) {
        Some(NEHole(Cursor(Var(x))));
      } else {
        ana_zipper(ctx, e, a, t);
      };
    | _ => ana_zipper(ctx, e, a, t);
    }
  | (Cursor(EHole), Construct(Lam(x)), t) =>
    switch (fun_type_match(t)) {
    | Some(Arrow(_, _)) => Some(Lam(x, Cursor(EHole)))
    | _ => Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))))
    }
  | (Cursor(EHole), Construct(Lit(n)), t) =>
    if (type_incom(t, Num)) {
      Some(NEHole(Cursor(Lit(n))));
    } else {
      ana_zipper(ctx, e, a, t);
    };
  | (Cursor(NEHole(e)), Finish, t) =>
    if (ana(ctx, e, t)) {
      Some(Cursor(e));
    } else {
       ana_zipper(ctx, Cursor(NEHole(e)), a, t);
    };
  //| (Lam(x, e), a, t) => ana_zipper(ctx, (Lam(x, e), t), a);
  | _ => ana_zipper(ctx, e, a, t);
  };
}
and ana_zipper = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
    switch (e, a, t) {
    | (Lam(x, e), a, t) =>
      switch (fun_type_match(t)) {
      | Some(Arrow(t1, t2)) =>
        let ctx' = TypCtx.add(x, t1, ctx);
        switch (ana_action(ctx', e, a, t2)) {
        | Some(e') => Some(Lam(x, e'))
        | _ => 
            let* t' = syn(ctx, erase_exp(e));
            let* (e', t'') = syn_action(ctx, (e, t'), a);
            if (type_com(t, t'')) {Some(e');} else {None;};
        };
      | _ =>     
      let* t' = syn(ctx, erase_exp(e));
      let* (e', t'') = syn_action(ctx, (e, t'), a);
      if (type_com(t, t'')) {Some(e');} else {None;};
      };
    | _ =>    
      let* t' = syn(ctx, erase_exp(e));
      let* (e', t'') = syn_action(ctx, (e, t'), a);
      if (type_com(t, t'')) {Some(e');} else {None;};
    };
}
and syn_zipper = (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  switch (e, t, a) {
  | (LAsc(e, t1), t2, a) =>
    if (t1 == t2) {
      let* e' = ana_action(ctx, e, a, t1);
      Some((LAsc(e', t1), t1));
    } else {
      None;
    };
  | (RAsc(e1, t1), t2, a) =>
    if (t2 == erase_typ(t1)) {
      let* ty' = type_action(t1, a);
      let ty'' = erase_typ(ty');
      if (ana(ctx, e1, ty'')) {
        Some((RAsc(e1, ty'), ty''));
      } else {
        None;
      };
    } else {
      None;
    };
  | (LAp(e1, e2), _, a) =>
    let* t2 = syn(ctx, erase_exp(e1));
    let* (e', t3) = syn_action(ctx, (e1, t2), a);
    switch (fun_type_match(t3)) {
    | Some(Arrow(t4, t5)) =>
      if (ana(ctx, e2, t4)) {
        Some((LAp(e', e2), t5));
      } else {
        None;
      };
    | _ => None
    };
  | (RAp(e1, e2), _, a) =>
    let* t2 = syn(ctx, e1);
    switch (fun_type_match(t2)) {
    | Some(Arrow(t3, t4)) =>
      let* e' = ana_action(ctx, e2, a, t3);
      Some((RAp(e1, e'), t4));
    | _ => None
    };
  | (LPlus(e1, e2), Num, a) =>
    switch (ana_action(ctx, e1, a, Num)) {
    | None => None
    | Some(e') => Some((LPlus(e', e2), Num))
    }
  | (RPlus(e1, e2), Num, a) =>
    switch (ana_action(ctx, e2, a, Num)) {
    | None => None
    | Some(e') => Some((RPlus(e1, e'), Num))
    }
  | (NEHole(e), Hole, a) =>
    switch (syn(ctx, erase_exp(e))) {
    | None => None
    | Some(t') =>
      switch (syn_action(ctx, (e, t'), a)) {
      | None => None
      | Some((e', _)) => Some((NEHole(e'), Hole))
      }
    }
  | _ => None
  };
}