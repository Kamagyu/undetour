type formula =
  | Var of char
  | Bot
  | Imp of formula * formula
  | And of formula * formula
  | Or of formula * formula

module Ctx = Set.Make (struct
  type t = formula
  let compare = Stdlib.compare
end)

type sequent = Ctx.t * formula (* Gamma |- A *)

type rule =
  | Ax
  | ImpIntro | ImpElim 
  | AndIntro | AndElimL | AndElimR
  | OrIntroL | OrIntroR | OrElim
  | BotElim

type proof_tree = {
  sequent : sequent;
  rule : rule;
  subproofs : proof_tree list;
}

(* Example : *)

let _ex = (* proof of A, A->B |- B *)
  let gamma = Ctx.of_list [Var 'A'; Imp (Var 'A', Var 'B')] in
  {
    sequent = (gamma, Var 'B');
    rule = ImpElim;
    subproofs = [
      {
        sequent = (gamma, Var 'A');
        rule = Ax;
        subproofs = []
      };
      {
        sequent = (gamma, Imp (Var 'A', Var 'B'));
        rule = Ax;
        subproofs = []
      }
    ]
}

let rec is_valid (t : proof_tree) : bool =
  let (ctx, goal) = t.sequent in
  match t.rule, t.subproofs with
  | Ax, [] ->
    Ctx.mem goal ctx
  | ImpIntro, [p1] ->
    begin
      match goal with
      | Imp (a,b) ->
        let (ctx1, goal1) = p1.sequent in
        goal1 = b
        && Ctx.equal ctx1 (Ctx.add a ctx)
        && is_valid p1
      | _ -> false
    end
  | ImpElim, [p1; p2] ->
    begin
      match p1.sequent, p2.sequent with
      | (ctx1, a'), (ctx2, Imp (a, b)) ->
        a = a' && b = goal
        && Ctx.equal ctx1 ctx && Ctx.equal ctx2 ctx
        && is_valid p1 && is_valid p2
      | _ -> false
    end
  | AndIntro, [p1; p2] ->
    begin
      match goal with
      | And (a,b) ->
        let (ctx1, goal1) = p1.sequent and (ctx2, goal2) = p2.sequent in
        goal1 = a && goal2 = b
        && Ctx.equal ctx1 ctx && Ctx.equal ctx2 ctx
        && is_valid p1 && is_valid p2
      | _ -> false
    end
  | AndElimL, [p1] ->
    begin
      match p1.sequent with
      | ctx1, And (a,b) ->
        goal = a
        && Ctx.equal ctx1 ctx
        && is_valid p1
      | _ -> false
    end
  | AndElimR, [p1] ->
    begin
      match p1.sequent with
      | ctx1, And (a,b) ->
        goal = b
        && Ctx.equal ctx1 ctx
        && is_valid p1
      | _ -> false
    end
  | OrIntroL, [p1] ->
    begin
      match goal with
      | Or (a,b) ->
        let (ctx1, goal1) = p1.sequent in
        goal1 = a
        && Ctx.equal ctx1 ctx
        && is_valid p1
      | _ -> false
    end
  | OrIntroR, [p1] ->
    begin
      match goal with
      | Or (a,b) ->
        let (ctx1, goal1) = p1.sequent in
        goal1 = b
        && Ctx.equal ctx1 ctx
        && is_valid p1
      | _ -> false
    end
  | OrElim, [p1; p2; p3] ->
    begin
      match p1.sequent with
      | ctx1, Or (a,b) ->
        let (ctx2, goal2) = p2.sequent and (ctx3, goal3) = p3.sequent in
        goal2 = goal && goal3 = goal
        && Ctx.equal ctx1 ctx
        && Ctx.equal ctx2 (Ctx.add a ctx)
        && Ctx.equal ctx3 (Ctx.add b ctx)
        && is_valid p1 && is_valid p2 && is_valid p3
      | _ -> false
    end
  | BotElim, [p1] ->
    begin
      match p1.sequent with
      | (ctx1, Bot) ->
        Ctx.equal ctx1 ctx
        && is_valid p1
      | _ -> false
    end
  | _ -> false
