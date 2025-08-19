import Init.Data.Nat
import Binary.Def
import Binary.Basic
import Binary.Lemmas
import Binary.AddLemmas
import Binary.DeMorganLemmas
import Binary.AddLogicalLemmas
import Binary.Comparison
import Binary.DozMaxMin

-- Here, we formalize some examples and theorems introduced in chapter 2-3, to show some
-- inequalities' properties. Fair notice that proofs below is simplified to human readable
-- form before rewriting with some other lemmas, which is hard to step-by-step rewriting
-- without any simplification automations.

namespace Binary.InequalityLemmas

variable {n : ℕ} {as bs : Binary (n + 1)}

public section

open Binary.DozMaxMin

-- (x ⊕ y) ≤ᵘ (x | y)
theorem xor_le_or : (as ⊕ bs) ≤ᵘ (as || bs) := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'; cases bs'; cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    have ih' := ih (as := as') (bs := bs')
    simp at ih'
    cases a <;> cases b <;> simp <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih']

-- (x & y) ≤ᵘ (x ≡ y)
theorem and_le_xnor : (as && bs) ≤ᵘ (as ⊙ bs) := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'; cases bs'; cases a <;> cases b <;> simp
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    have ih' := ih (as := as') (bs := bs')
    simp at ih'
    cases a <;> cases b <;> simp <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih']

-- (x | y) ≥ᵘ maxu(x, y)
theorem or_ge_max : (as || bs) ≥ᵘ maxu as bs := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'; cases bs'; cases a <;> cases b <;> simp
  | succ n' ih =>
    have h := DozMaxMin.maxu_eq as bs
    cases h with
    | inl lh =>
      rw [lh]
      exact Comparison.or_unsigned_ge_left
    | inr rh =>
      rw [rh]
      exact Comparison.or_unsigned_ge_right

-- (x & y) ≤ᵘ minu(x, y)
theorem and_le_min : (as && bs) ≤ᵘ minu as bs := by
  induction n with
  | zero =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases as'; cases bs'; cases a <;> cases b <;> simp
  | succ n' ih =>
    have h := DozMaxMin.minu_eq as bs
    cases h with
    | inl lh =>
      rw [lh]
      exact Comparison.and_unsigned_le_left
    | inr rh =>
      rw [rh]
      exact Comparison.and_unsigned_le_right

end
end Binary.InequalityLemmas
