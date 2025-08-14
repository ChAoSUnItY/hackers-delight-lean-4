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
theorem bneg_and_eq_bneg_or_bneg : bneg (as ∧b bs) = ((bneg as) ∨b (bneg bs)) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    exact ih

-- ¬(x | y) = ¬x & ¬y
theorem bneg_or_eq_bneg_and_bneg : bneg (as ∨b bs) = ((bneg as) ∧b (bneg bs)) := by
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
theorem bneg_xor_eq_bneg_xor : bneg (as ^^b bs) = ((bneg as) ^^b bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    simp
    exact ih

-- ¬(x ⊕ y) = x ≡ y
theorem bneg_xor_eq_beq : bneg (as ^^b bs) = beq as bs := by
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
theorem bneg_beq_eq_bneg_beq : bneg (beq as bs) = (beq (bneg as) bs) := by
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
theorem bneg_beq_eq_xor : bneg (beq as bs) = (as ^^b bs) := by
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
theorem bneg_add_eq_bneg_sub : bneg (as +b bs) = ((bneg as) -b bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    rw [@nneg_eq_inc_bneg]
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [ih, nneg_eq_inc_bneg]
    | false, true => simp; rw [ih, AddLemmas.rca_carry_trans_inc_right, nneg_eq_inc_bneg]
    | true, false => simp; rw [ih, nneg_eq_inc_bneg]
    | true, true =>
      simp
      rw [
        AddLemmas.rca_lift_carry,
        bneg_inc_eq_bneg_dec,
        ih,
        nneg_eq_inc_bneg,
        AddLemmas.rca_lift_right_inc,
        Lemmas.of_dec_inc
      ]

-- ¬(x - y) = ¬x + y
theorem bneg_sub_eq_bneg_add : bneg (as -b bs) = ((bneg as) +b bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    rw [bneg_add_eq_bneg_sub, Lemmas.of_nneg_nneg]

end
end Binary.DeMorganLemmas
