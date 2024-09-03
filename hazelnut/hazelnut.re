open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

let rec type_compatibility = (t: Htyp.t, t1: Htyp.t): bool =>
  // can we declare two in the func definition?
  // base cases
  if (t == t1) {
    true; // if both same type
  } else if (t == Hole) {
    true;
  } else if (t1 == Hole) {
    true;
  } else {
    switch (t, t1) {
    | (Arrow(t, t'), Arrow(t1, t1')) =>
      type_compatibility(t, t1) && type_compatibility(t', t1')
    // if input & output types are both compatible return true?
    | _ => false
    };
  };

// H types
let type_matching = (e: Htyp.t): option(Htyp.t) => {
  switch (e) {
  | Hole => Some(Arrow(Hole, Hole))
  | Arrow(e, e') => Some(Arrow(e, e'))
  | _ => None
  };
};

// let rec syn_ana = (e: )

// Z types
let rec cur_erasure = (e: Ztyp.t): Htyp.t => {
  switch (e) {
  | Cursor(e) => e
  | LArrow(e, e1) => Arrow(cur_erasure(e), e1)
  | RArrow(e, e1) => Arrow(e, cur_erasure(e1))
  };
};

let rec erase_exp = (e: Zexp.t): Hexp.t => {
  // turning to H expressions
  switch (e) {
  | Cursor(eh) => eh
  | Lam(s, eh) => Lam(s, erase_exp(eh))
  | LAp(eh, e1) => Ap(erase_exp(eh), e1)
  | RAp(e1, eh) => Ap(e1, erase_exp(eh))
  | LPlus(eh, e1) => Plus(erase_exp(eh), e1)
  | RPlus(t1, th) => Plus(t1, erase_exp(th))
  | LAsc(eh, th) => Asc(erase_exp(eh), th) // ascend left
  | RAsc(eh, t) => Asc(eh, cur_erasure(t)) // ascend right
  | NEHole(eh) => NEHole(erase_exp(eh))
  };
};

// let erase_exp = (e: Zexp.t): Hexp.t => {
//   // Used to suppress unused variable warnings
//   // Okay to remove
//   let _ = e;

//   raise(Unimplemented);
// };

// let syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
//   // Used to suppress unused variable warnings
//   // Okay to remove
//   let _ = ctx;
//   let _ = e;

//   raise(Unimplemented);
// }

// synthesis => type is returned
let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Asc(e, t) =>
    // let temp = ana(ctx, e, t);
    if (ana(ctx, e, t)) {
      Some(t);
    } else {
      None;
    }
  // do we need to conduct analysis here?
  // Why is the check necessray if we're already given the type assuming Asc
  // means ascryption

  | Var(e) => TypCtx.find_opt(e, ctx)

  | Ap(f, e) =>
    switch (syn(ctx, f)) {
    | Some(t1) =>
      switch (type_matching(t1)) {
      | Some(Arrow(t2, t')) =>
        if (ana(ctx, e, t2)) {
          Some(t');
        } else {
          None;
        }
      | _ => None
      }
    | _ => None
    }
  // let* t1 = type_matching(t1);
  // switch(t1) {
  //   | Some val => val
  //   | _ => None
  // switch(type_matching(t1)) {
  //   | Some(Arrow(t2, t')) =>
  //     if (ana(ctx, e, t2)) {
  //       Some(t')
  //     }
  //     else {
  //       None
  //     };
  //   | _ => None
  // }

  // let* t' = syn(ctx, f);
  // let* t' = type_matching(t);

  // Arrow(e, TypCtx.find_opt(syn(e'), ctx));
  | Lit(_) => Some(Num)

  | Plus(e1, e2) =>
    // let t1 = Some(Num)
    // let t2 = Some(Num)
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }

  // | (t1 == Num && t2 == Num) => Num
  // | _ => None

  | EHole => Some(Hole)
  | NEHole(_) => Some(Hole)
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(x, e1) =>
    switch (type_matching(t)) {
    // context extension is needed here
    | Some(Arrow(t1, t2)) =>
      let newctx = TypCtx.add(x, t1, ctx);
      ana(newctx, e1, t2);
    // first arg should be t1, how do I make the correct recursive call
    // something to do with ctx?
    | _ => false
    }
  | _ =>
    switch (syn(ctx, e)) {
    | Some(t') => type_compatibility(t', t) // is it better to handle the lamda func first?
    | _ => false
    }
  };
};

// and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
//   // Used to suppress unused variable warnings
//   // Okay to remove
//   let _ = ctx;
//   let _ = e;
//   let _ = t;

//   raise(Unimplemented);
// };

let rec type_action = (z: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  print_endline("typeeee");
  switch (z, a) {
  | (Cursor(Arrow(t1, t2)), Move(Child(One))) =>
    Some(LArrow(Cursor(t1), t2))
  | (Cursor(Arrow(t1, t2)), Move(Child(Two))) =>
    Some(RArrow(t1, Cursor(t2)))
  | (LArrow(Cursor(t1), t2), Move(Parent)) => Some(Cursor(Arrow(t1, t2)))
  | (RArrow(t1, Cursor(t2)), Move(Parent)) => Some(Cursor(Arrow(t1, t2)))
  | (Cursor(_), Del) => Some(Cursor(Hole))
  // would we insert empty hole here or not or does it not matter
  | (Cursor(t), Construct(Arrow)) => Some(RArrow(t, Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) => Some(Cursor(Num))
  | _ => zipper_type(z, a)
  };
}

// [@warning "-8"]
and zipper_type = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  print_endline("zipperrr");
  switch (t, a) {
  | (LArrow(th, td), a) =>
    print_endline("left");
    switch (type_action(th, a)) {
    | Some(t1) => Some(LArrow(t1, td))
    | _ => None
    };
  // switch(t1) {
  //   | Some(_) => Some(LArrow(t1, td))
  //   | _ => None
  // th' = Option.get (th')
  // Some(Arrow(th', td))
  // }
  | (RArrow(th, td), a) =>
    print_endline("right");
    switch (type_action(td, a)) {
    | Some(t1) => Some(RArrow(th, t1))
    | _ => None
    };
  //   switch(t1) {
  //     | Some(_) => Some(RArrow(th, td))
  //     | _ => None
  | _ => None
  // }
  };
};

let ex_move = (z: Zexp.t, a: Action.t): option(Zexp.t) => {
  print_endline("Noneeexxxx");
  switch (z, a) {
  | (Cursor(Asc(e, t)), Move(Child(One))) => Some(LAsc(Cursor(e), t))
  | (Cursor(Asc(e, t)), Move(Child(Two))) => Some(RAsc(e, Cursor(t)))
  | (LAsc(Cursor(e), t), Move(Parent)) => Some(Cursor(Asc(e, t)))
  | (RAsc(e, Cursor(t)), Move(Parent)) => Some(Cursor(Asc(e, t)))
  | (Cursor(Lam(s, e)), Move(Child(One))) => Some(Lam(s, Cursor(e)))
  | (Lam(s, Cursor(e)), Move(Parent)) => Some(Cursor(Lam(s, e)))
  | (Cursor(Plus(e1, e2)), Move(Child(One))) =>
    Some(LPlus(Cursor(e1), e2))
  | (Cursor(Plus(e1, e2)), Move(Child(Two))) =>
    Some(RPlus(e1, Cursor(e2)))
  | (LPlus(Cursor(e1), e2), Move(Parent)) => Some(Cursor(Plus(e1, e2)))
  | (RPlus(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Plus(e1, e2)))
  | (Cursor(Ap(e1, e2)), Move(Child(One))) => Some(LAp(Cursor(e1), e2))
  | (Cursor(Ap(e1, e2)), Move(Child(Two))) => Some(RAp(e1, Cursor(e2)))
  | (LAp(Cursor(e1), e2), Move(Parent)) => Some(Cursor(Ap(e1, e2)))
  | (RAp(e1, Cursor(e2)), Move(Parent)) => Some(Cursor(Ap(e1, e2)))
  | (Cursor(NEHole(e)), Move(Child(One))) => Some(NEHole(Cursor(e)))
  | (NEHole(Cursor(e)), Move(Parent)) => Some(Cursor(NEHole(e)))
  | _ =>
    print_endline("Noneeerrrrr");
    None;
  };
};

// let syn_action =
//     (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
//     : option((Zexp.t, Htyp.t)) => {
//   // Used to suppress unused variable warnings
//   // Okay to remove
//   let _ = ctx;
//   let _ = e;
//   let _ = t;
//   let _ = a;

//   raise(Unimplemented);
// }

// let syn_zip = (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
//     : option((Zexp.t, Htyp.t)) => {

//     };

let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  print_endline("Noneee");
  switch ((e, t), a) {
  | ((Cursor(ed), td), Construct(Asc)) => Some((RAsc(ed, Cursor(td)), td))
  // | ((Cursor(ed), _), Construct(Asc)) =>
  //   switch(syn(ctx, ed)) {
  //     | Some(td) => Some((RAsc(ed, Cursor(td)), td))
  //     | _ => None
  //   };
  // syn(ctx, e2, t1)
  | ((Cursor(_), _), Del) => Some((Cursor(EHole), Hole))
  // | ((Cursor(e1), t1), Construct(Asc)) => Some((RAsc(e1, Cursor(t1)), t1))
  | ((Cursor(EHole), Hole), Construct(Var(x))) =>
    switch (TypCtx.find_opt(x, ctx)) {
    | Some(t1) => Some((Cursor(Var(x)), t1))
    | _ => None
    }

  // | ((Cursor(_), _), Construct(Num)) => Some(Cursor(Num))
  // let t1 = Option.get ( TypCtx.find_opt(x, ctx) );
  // Some((Cursor(Var(x)), t1))
  | ((Cursor(EHole), Hole), Construct(Lam(e))) =>
    Some((
      RAsc(Lam(e, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  | ((Cursor(e1), t1), Construct(Ap)) =>
    switch (type_matching(t1)) {
    | Some(Arrow(_, t2)) => Some((RAp(e1, Cursor(EHole)), t2))
    | _ => Some((RAp(NEHole(e1), Cursor(EHole)), Hole))
    }
  | ((Cursor(EHole), Hole), Construct(Lit(n))) =>
    print_endline("LitS");
    Some((Cursor(Lit(n)), Num));
  | ((Cursor(NEHole(e1)), t1), Construct(Plus)) =>
    switch (type_matching(t1)) {
    | Some(Num) => Some((RPlus(e1, Cursor(EHole)), Num))
    | _ => Some((RPlus(NEHole(e1), Cursor(EHole)), Num))
    }
  | ((Cursor(e1), Hole), Construct(NEHole)) =>
    Some((NEHole(Cursor(e1)), Hole))
  // FIX ME
  | ((Cursor(NEHole(e1)), Hole), Finish) =>
    print_endline("Fin");
    switch (syn(ctx, e1)) {
    | Some(t') => Some((Cursor(e1), t'))
    | _ => None
    };
  // | ((LAsc(eh, t1), _), a) =>
  //   print_endline("LAsc");
  //   switch (ana_action(ctx, eh, a, t1)) {
  //   | Some(eh') => Some((LAsc(eh', t1), t1))
  //   | _ => None
  //   };
  // // | ((Cursor(ed), td), Construct(Asc)) => Some((RAsc(ed, Cursor(td)), td))

  // | ((RAsc(e', th), _), a) =>
  //   print_endline("RAsc");
  //   switch (type_action(th, a)) {
  //   | Some(th') =>
  //     print_endline("RAsc1111");
  //     let tc = cur_erasure(th');
  //     // let newt = ana_action(e', a, th')
  //     if (ana(ctx, e', tc)) {
  //       Some((RAsc(e', th'), tc));
  //     } else {
  //       None;
  //     };
  //   | _ => None
  //   };
  | ((LAp(eh, ed), _), a) =>
    switch (syn(ctx, erase_exp(eh))) {
    | Some(t2) =>
      // let eh' = Option.get (ex_move(eh, a) );
      switch (syn_action(ctx, (eh, t2), a)) {
      | Some((eh', t3)) =>
        switch (type_matching(t3)) {
        | Some(Arrow(t4, t5)) =>
          if (ana(ctx, ed, t4)) {
            Some((LAp(eh', ed), t5));
          } else {
            None;
          }
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | ((RAp(ed, eh), _), a) =>
    switch (syn(ctx, ed)) {
    | Some(t2) =>
      switch (type_matching(t2)) {
      | Some(Arrow(t3, t4)) =>
        switch (ana_action(ctx, eh, a, t3)) {
        | Some(eh') => Some((RAp(ed, eh'), t4))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | ((LAsc(eh, t1), _), a) =>
    print_endline("LAsc");
    switch (ana_action(ctx, eh, a, t1)) {
    | Some(eh') => Some((LAsc(eh', t1), t1))
    | _ => None
    };
  // | ((Cursor(ed), td), Construct(Asc)) => Some((RAsc(ed, Cursor(td)), td))

  | ((RAsc(e', th), t1), a) =>
    print_endline("RAsc");
    switch (type_action(th, a)) {
    | Some(th') =>
      print_endline("RAsc1111");
      let tc = cur_erasure(th');
      // let newt = ana_action(e', a, th')
      if (ana(ctx, e', tc)) {
        Some((RAsc(e', th'), tc));
      } else {
        None;
      };
    | _ =>
      switch (ex_move(RAsc(e', th), a)) {
      | Some(e2) => Some((e2, t1))
      | _ => None
      }
    };
  // FIX ME
  | ((Cursor(ed), td), Construct(Plus)) =>
    if (type_compatibility(td, Num)) {
      Some((RPlus(ed, Cursor(EHole)), Num));
    } else {
      Some((NEHole(Cursor(ed)), Hole));
    }
  // switch (ana_action(ctx, eh, Num)) {
  // | Some(eh') => Some((LPlus(eh', ed), Num))
  // | _ => None
  // }
  // FIX ME
  // | ((RPlus(ed, eh), Num), Construct(Plus)) =>
  //   switch (ana_action(ctx, eh, a, Num)) {
  //   | Some(eh') => Some((RPlus(ed, eh'), Num))
  //   | _ => None
  //   }
  | ((NEHole(eh), Hole), Construct(NEHole)) =>
    switch (syn(ctx, erase_exp(eh))) {
    | Some(td) =>
      switch (syn_action(ctx, (eh, td), a)) {
      | Some((eh', _)) => Some((NEHole(eh'), Hole))
      | _ => None
      }
    | _ => None
    }
  | ((e1, t1), Move(_)) =>
    switch (ex_move(e1, a)) {
    | Some(e2) => Some((e2, t1))
    | _ => None
    }
  | _ =>
    print_endline("Oiii");
    None;
  };
}

and subsumption =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch ((e, t), a) {
  | _ =>
    let ehd = erase_exp(e);
    switch (syn(ctx, ehd)) {
    | Some(t') =>
      switch (syn_action(ctx, (e, t'), a)) {
      | Some((e', t'')) =>
        if (type_compatibility(t, t'')) {
          Some(e');
        } else {
          None;
        }
      | _ => None
      }
    | _ => None
    };
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  print_endline("Noneee");
  switch ((e, t), a) {
  | ((Cursor(eh), _), Move(_)) =>
    print_endline("Move");
    switch (ex_move(Cursor(eh), a)) {
    | Some(e') => Some(e')
    | _ =>
      print_endline("None");
      subsumption(ctx, e, a, t);
    };
  // FIX ME
  | ((Cursor(_), _), Del) => Some(Cursor(EHole))
  | ((Cursor(ed), td), Construct(Asc)) => Some(RAsc(ed, Cursor(td)))
  // FIX ME
  | ((Cursor(EHole), td), Construct(Var(x))) =>
    switch (TypCtx.find_opt(x, ctx)) {
    // gives us type of x
    | Some(t') =>
      if (type_compatibility(td, t')) {
        subsumption(ctx, e, a, t);
      } else {
        Some(NEHole(Cursor(Var(x))));
      }
    | _ => subsumption(ctx, e, a, t)
    }
  | ((Cursor(EHole), td), Construct(Lam(x))) =>
    switch (type_matching(td)) {
    | Some(Arrow(_, _)) => Some(Lam(x, Cursor(EHole)))
    | _ => Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))))
    }
  // FIX ME
  | ((Cursor(EHole), td), Construct(Lit(n))) =>
    print_endline("LitA");
    if (type_compatibility(td, Num)) {
      subsumption(ctx, e, a, t);
    } else {
      Some(NEHole(Cursor(Lit(n))));
    };

  // FIX ME
  | ((Cursor(NEHole(ed)), Hole), Finish) =>
    switch (syn(ctx, ed)) {
    | Some(_) => Some(Cursor(ed))
    | _ => None
    }
  | ((Cursor(NEHole(ed)), td), Finish) =>
    if (ana(ctx, ed, td)) {
      Some(Cursor(ed));
    } else {
      subsumption(ctx, Cursor(NEHole(ed)), a, t);
    }
  | ((Lam(x, eh), td), ac) =>
    print_endline("Lamx");
    switch (type_matching(td)) {
    | Some(Arrow(t1, t2)) =>
      let newctx = TypCtx.add(x, t1, ctx);
      switch (ana_action(newctx, eh, ac, t2)) {
      | Some(eh') => Some(Lam(x, eh'))
      | _ => subsumption(ctx, e, a, t)
      };
    | _ => subsumption(ctx, e, a, t)
    };
  | _ =>
    print_endline("Subsum");
    let ehd = erase_exp(e);
    switch (syn(ctx, ehd)) {
    | Some(t') =>
      switch (syn_action(ctx, (e, t'), a)) {
      | Some((e', t'')) =>
        if (type_compatibility(t, t'')) {
          Some(e');
        } else {
          None;
        }
      | _ => None
      }
    | _ => None
    };
  };
};

// and ana_action =
//     (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
//   // Used to suppress unused variable warnings
//   // Okay to remove
//   let _ = ctx;
//   let _ = e;
//   let _ = a;
//   let _ = t;

//   raise(Unimplemented);
// };
