import Binary.Def
import Binary.Basic
import Binary.Lemmas
import Binary.AddLemmas

-- Here, we formalize all theorems introduced from 2-1's "De Morgan’s Laws Extended",
-- to show some useful properties when applying bitwise negation on several different
-- expressions.

namespace Binary.DeMorganLemmas

variable {n : ℕ} {a b c c' : Bit} {as' bs' : Binary n.succ} {as bs cs : Binary n}

public section

open Binary.DeMorganLemmas

-- ¬(x & y) = ¬x | ¬y
theorem bneg_and_eq_bneg_or_bneg : (¬(as ∧ bs)) = (¬as ∨ ¬bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    exact ih

-- ¬(x | y) = ¬x & ¬y
theorem bneg_or_eq_bneg_and_bneg : (¬(as ∨ bs)) = (¬as ∧ ¬bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    exact ih

-- ¬(x + 1) = ¬x - 1
theorem bneg_inc_eq_bneg_dec : bneg (inc as) = dec (bneg as) := by
  induction n with
  | zero => cases as; simp
  | succ n' ih =>
    cases as with | cons a as'
    simp
    cases a
    · simp
    · simp
      exact ih

-- ¬(x - 1) = ¬x + 1
theorem bneg_dec_eq_bneg_inc : bneg (dec as) = inc (bneg as) := by
  induction n with
  | zero => cases as; simp
  | succ n' ih =>
    cases as with | cons a as'
    simp
    cases a
    · simp
      exact ih
    · simp

-- ¬-x = x - 1
theorem bneg_nneg_eq_dec : bneg (nneg as) = dec as := by
  induction n with
  | zero => cases as; simp
  | succ n' ih =>
    cases as with | cons a as'
    cases a
    · simp
      rw [bneg_inc_eq_bneg_dec]
      simp
    · simp

-- ¬(x ⊕ y) = ¬x ⊕ y
theorem bneg_xor_eq_bneg_xor : (¬(as ⊕ bs)) = ((¬as) ⊕ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    exact ih

-- ¬(x ⊕ y) = x ≡ y
theorem bneg_xor_eq_beq : (¬(as ⊕ bs)) = (as ⊙ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    rw [ih]
    simp
    exact rfl

-- ¬(x ≡ y) = ¬x ≡ y
theorem bneg_beq_eq_bneg_beq : (¬(as ⊙ bs)) = ((¬as) ⊙ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    rw [ih]
    cases a
    · simp
    · simp

-- ¬(x ≡ y) = x ⊕ y
theorem bneg_beq_eq_xor : (¬(as ⊙ bs)) = (as ⊕ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    rw [ih]
    cases a
    · simp
    · simp

-- ¬(x + y) = x - y
theorem bneg_add_eq_bneg_sub : (¬(as + bs)) = ((¬as) - bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [ih, Lemmas.nneg_eq_bneg_inc]
    | false, true => simp; rw [ih, AddLemmas.rca_carry_trans_inc_right, Lemmas.nneg_eq_bneg_inc]
    | true, false => simp; rw [ih, Lemmas.nneg_eq_bneg_inc]
    | true, true =>
      simp
      rw [
        AddLemmas.rca_lift_carry,
        bneg_inc_eq_bneg_dec,
        ih,
        Lemmas.nneg_eq_bneg_inc,
        AddLemmas.rca_lift_right_inc,
        Lemmas.of_dec_inc
      ]

-- ¬(x - y) = ¬x + y
theorem bneg_sub_eq_bneg_add : (¬(as - bs)) = ((¬as) + bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    rw [bneg_add_eq_bneg_sub, Lemmas.of_nneg_nneg]

end
end Binary.DeMorganLemmas
