import GreatRSI.Script
import GreatRSI.Winternitz
import GreatRSI.ScriptBuilder

open Classical

theorem merkle_tree_script_builder:
  ∀ (m: Nat) (inctx: ExecCtx),
  (Script.run (merkle_tree_script (m+1)) inctx = some outctx)
  → (merkle_tree_root (inctx.stack.reverse.take (2^(m+1))) = (outctx.stack.pop.2)) := by
  intros m inctx h
  induction m with
  | zero =>
    simp
    unfold Script.run at h
    simp [merkle_tree_script] at h
    split at h
    . contradiction
    case _ _ outctx' h2  =>
      simp [ExecCtx.transition] at h2
      split at h2
      . contradiction
      . contradiction
      . simp at h2
        cases h2 with
          | intro h3 h4 =>
          rw [h4.symm] at h
          simp [Script.run] at h
          split at h
          . contradiction
          case _ h5 =>
            simp [ExecCtx.transition] at h5
            split at h5
            . contradiction
            . contradiction
            . contradiction
            . contradiction
            . simp at h5
              cases h5 with
              | intro h6 h7 =>
                rw [h7.symm] at h
                simp at h
                rw [h.symm]
                simp
                simp [merkle_tree_root]
                split
                case _ h9 =>
                  have h10: List.length inctx.stack = 0 := by
                    simp
                    exact h9
                  rw [h10] at h3
                  contradiction
                case _ h9 =>
                  rw [<- h9.symm] at h3
                  have h10: List.length [] = 0 := by
                    simp [List.length]
                  simp [List.length] at h3
                  simp [Stack.pop]
                  simp [Stack.push]
                  simp [BytArray.append]
                  simp [merkle_tree_root.buildTree]
                  -- it's a partial function
                  -- and also fix reverse, it'll get too hard
                .
                have h8 :
              rw
            . contradiction
      . contradiction
      . contradiction
      . contradiction

    | succ n' ih => sorry

    cases h_stack: inctx.stack
    case nil =>
      unfold Script.run at h
      simp [merkle_tree_script] at h
      simp [ExecCtx.transition] at h
      split at h
      . contradiction
      . contradiction
      . simp [Script.run] at h
      . simp
      . contradiction

      . simp
      simp [merkle_tree_root]
      unfold  at h
      --apply [Script.run] at h
      --apply False.elim
      --simp [List.reverse]
      --contradiction

    split at h
    . contradiction
    . simp

  | succ n' ih =>
  sorry

theorem transition_run_cat: ∀ (inctx: ExecCtx) (outctx: ExecCtx), (inctx.transition OP_CAT = some outctx) → (inctx.stack.length >= 2) := by
  intros inctx outctx
  cases h_stack: inctx.stack
  case nil =>
      intro h
      simp [ExecCtx.transition] at h
      split at h
      . contradiction
      . contradiction
      . simp at h
        cases h with
        | intro h2 h3 =>
          have h_len : List.length inctx.stack = 0 := by
            simp [List.length]
            exact h_stack
          rw [h_len] at h2
          contradiction
      . contradiction
      . contradiction
      . contradiction

  case cons y ys =>
    cases ys
    case nil =>
      intro h
      simp [List.length]
      contradiction
    case cons ys2 ys3 =>
      intro h
      simp [ExecCtx.transition] at h
      split at h
      . split at h
        . contradiction
        . simp
      . contradiction
      . contradiction
      . contradiction

-- Attempt at a proof by contradiction but its much more difficult to follow
theorem transition_run_cat': ∀ (inctx: ExecCtx) (outctx: ExecCtx), (ExecCtx.transition inctx OP_CAT = some outctx) → (inctx.stack.length >= 2) := by
  apply byContradiction
  intro h
  have hr := Classical.not_forall.mp h
  cases hr with
  | intro instack h2 =>
    have hr' := Classical.not_forall.mp h2
    cases hr' with
    | intro res h3 =>
      have hr'' := Classical.not_imp.mp h3
      simp at hr''
      cases instack
      case nil =>
        simp [List.length] at hr''
        contradiction
      case cons y ys =>
        cases ys
        case nil =>
          simp [List.length] at hr''
          contradiction
        case cons ys2 ys3 =>
          simp [Stack.transition] at hr''
          split at hr''
          . sorry
          . sorry
          . sorry
          . sorry

theorem transition_run_cat'': ∀ (inctx: ExecCtx) (outctx: ExecCtx), (ExecCtx.transition inctx OP_CAT = some outctx) → (inctx.stack.length >= 2) := by
  intro instack res
  intro h
  apply by_contra
  intro h2

theorem tapscript_verify_cat: Script.verify [OP_CAT] instack  → instack.length >= 2 := by
  intro h
  simp [Script.verify] at h
  split at h
  . contradiction
  . apply transition_run_cat
    assumption
