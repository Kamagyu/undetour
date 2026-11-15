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

let (|-) ctx_list goal = (Ctx.of_list ctx_list, goal)

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

let _ex1 = (* valid proof of A, A->B |- B *)
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

let rec weaken (extra_ctx : Ctx.t) (t : proof_tree) : proof_tree =
  let (ctx, goal) = t.sequent in
  {
    sequent = (Ctx.union extra_ctx ctx, goal);
    rule = t.rule;
    subproofs = List.map (weaken extra_ctx) t.subproofs;
  }

(* Substitute a hypothesis `a` for a proof `p_a` *)
let rec graft (a : formula) (gamma : Ctx.t) (p_a : proof_tree) (t : proof_tree) : proof_tree =
  let (ctx, goal) = t.sequent in
  let new_ctx = Ctx.union gamma (Ctx.remove a ctx) in
  match t.rule, t.subproofs with
  | Ax, [] when goal = a && not (Ctx.mem a gamma) ->
    weaken new_ctx p_a
  | _ ->
    {
      sequent = (new_ctx, goal);
      rule = t.rule;
      subproofs = List.map (graft a gamma p_a) t.subproofs;
    }

let rec step (t : proof_tree) : proof_tree option =
  let (gamma, goal) = t.sequent in
  match t.rule, t.subproofs with
  | ImpElim, [p_a; {rule = ImpIntro; subproofs = [pi_1]; _}] ->
    let (_, a) = p_a.sequent in
    Some (graft a gamma p_a pi_1)
  
  | AndElimL, [{rule = AndIntro; subproofs = [p1; _]; _}] ->
    Some p1
  | AndElimR, [{rule = AndIntro; subproofs = [_; p2]; _}] ->
    Some p2

  | OrElim, [{ rule = OrIntroL; subproofs = [p1]; _}; pi_left; _] ->
    let (_, a) = p1.sequent in
    Some (graft a gamma p1 pi_left)
  | OrElim, [{ rule = OrIntroR; subproofs = [p2]; _}; _; pi_right] ->
    let (_, b) = p2.sequent in
    Some (graft b gamma p2 pi_right)

  | AndElimL, [{ rule = OrElim; subproofs = [p_or; pi_l; pi_r]; _}] ->
    let new_l = {
      sequent = (fst pi_l.sequent, goal);
      rule = AndElimL;
      subproofs = [pi_l]
    } in
    let new_r = {
      sequent = (fst pi_r.sequent, goal);
      rule = AndElimL;
      subproofs = [pi_r]
    } in
    Some {
      sequent = (gamma, goal);
      rule = OrElim;
      subproofs = [p_or; new_l; new_r]
    }
  | AndElimR, [{ rule = OrElim; subproofs = [p_or; pi_l; pi_r]; _}] ->
    let new_l = {
      sequent = (fst pi_l.sequent, goal);
      rule = AndElimR;
      subproofs = [pi_l]
    } in
    let new_r = {
      sequent = (fst pi_r.sequent, goal);
      rule = AndElimR;
      subproofs = [pi_r]
    } in
    Some {
      sequent = (gamma, goal);
      rule = OrElim;
      subproofs = [p_or; new_l; new_r]
    }
  | ImpElim, [p_a; { rule = OrElim; subproofs = [p_or; pi_l; pi_r]; _}] ->
    let (ctx_l, _) = pi_l.sequent and (ctx_r, _) = pi_r.sequent in
    let new_l = {
      sequent = (ctx_l, goal);
      rule = ImpElim;
      subproofs = [weaken ctx_l p_a; pi_l]
    } in
    let new_r = {
      sequent = (ctx_r, goal);
      rule = ImpElim;
      subproofs = [weaken ctx_r p_a; pi_r]
    } in
    Some {
      sequent = (gamma, goal);
      rule = OrElim;
      subproofs = [p_or; new_l; new_r]
    }
  | OrElim, [{ rule = OrElim; subproofs = [p_or; pi_l; pi_r]; _}; br_l; br_r] ->
    let (ctx_l, _) = pi_l.sequent and (ctx_r, _) = pi_r.sequent in
    let new_l = {
      sequent = (ctx_l, goal);
      rule = OrElim;
      subproofs = [pi_l; weaken ctx_l br_l; weaken ctx_l br_r]
    } in
    let new_r = {
      sequent = (ctx_r, goal);
      rule = OrElim;
      subproofs = [pi_r; weaken ctx_r br_l; weaken ctx_r br_r]  
    } in
    Some {
      sequent = (gamma, goal);
      rule = OrElim;
      subproofs = [p_or; new_l; new_r]
    }
  | BotElim, [{ rule = OrElim; subproofs = [p_or; pi_l; pi_r]; _}] ->
    let new_l = {
      sequent = (fst pi_l.sequent, goal);
      rule = BotElim;
      subproofs = [pi_l]
    } in
    let new_r = {
      sequent = (fst pi_r.sequent, goal);
      rule = BotElim;
      subproofs = [pi_r]
    } in
    Some {
      sequent = (gamma, goal);
      rule = OrElim;
      subproofs = [p_or; new_l; new_r]
    }

  | (AndElimL | AndElimR | BotElim), [{ rule = BotElim; subproofs = [p_bot]; _}] ->
    Some {
      sequent = (gamma, goal);
      rule = BotElim;
      subproofs = [p_bot]
    }
  | ImpElim, [_; { rule = BotElim; subproofs = [p_bot]; _}] ->
    Some {
      sequent = (gamma, goal);
      rule = BotElim;
      subproofs = [p_bot]
    }
  | OrElim, [{ rule = BotElim; subproofs = [p_bot]; _}; _; _] ->
    Some {
      sequent = (gamma, goal);
      rule = BotElim;
      subproofs = [p_bot]
    }
    
  | _ ->
    let rec step_list = function
    | [] -> None
    | p :: ps ->
      begin
        match step p with
        | Some p' -> Some (p' :: ps)
        | None -> Option.map (fun ps' -> p :: ps') (step_list ps)
      end
    in
    Option.map (fun sub' -> { t with subproofs = sub' }) (step_list t.subproofs)
