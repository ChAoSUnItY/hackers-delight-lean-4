import Binary.Def
import Binary.Basic
import Binary.Lemmas
import Binary.AddLemmas
import Binary.DeMorganLemmas

-- Here, we formalize all theorems introduced from 2-2's "Addition Combined with
-- Logical Operations", to show some useful properties when addition is combined
-- with several different logical operations.

namespace Binary.AddLogicalLemmas

variable {n : ℕ} {a b c c' : Bit} {as' bs' : Binary n.succ} {as bs cs : Binary n}

public section

open Binary.AddLogicalLemmas

-- -x = ~x + 1
-- This is already proved by definition, no need to reason it
theorem nneg_eq_bneg_inc : nneg as = inc (bneg as) := by
  exact Lemmas.nneg_eq_bneg_inc

-- -x = ~(x - 1)
theorem nneg_eq_dec_bneg : nneg as = bneg (dec as) := by
  induction n with
  | zero => cases as; simp
  | succ n' ih =>
    cases as with | cons a as'
    cases a
    · simp
      exact ih
    · simp

-- ~x = -x - 1
theorem bneg_eq_nneg_dec : bneg as = dec (nneg as) := by
  rw [nneg_eq_bneg_inc, Lemmas.of_dec_inc]

-- -~x = x + 1
theorem nneg_bneg_eq_inc : nneg (bneg as) = inc as := by
  rw [nneg_eq_bneg_inc, Lemmas.of_bneg_bneg]

-- ~-x = x - 1
theorem bneg_nneg_eq_dec : bneg (nneg as) = dec as := by
  rw [bneg_eq_nneg_dec, Lemmas.of_nneg_nneg]

-- x + y = x - ~y - 1
theorem add_eq_sub_bneg_dec : as + bs = dec (as - (~bs)) := by
  rw [nneg_eq_bneg_inc, Lemmas.of_bneg_bneg, AddLemmas.rca_lift_right_inc, Lemmas.of_dec_inc]

-- x + y = (x ⊕ y) + 2(x & y)
--       = (x ⊕ y) + (x & y) + (x & y)
theorem add_eq_xor_add_and_add_and : as + bs = (as ⊕ bs) + (as && bs) + (as && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [ih]
    | false, true => simp; rw [ih]
    | true, false => simp; rw [ih]
    | true, true =>
      simp
      rw [AddLemmas.rca_lift_carry, AddLemmas.rca_lift_carry, ih]

-- x + y = (x | y) + (x | y)
theorem add_eq_or_add_and : as + bs = (as || bs) + (as && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [ih]
    | false, true => simp; rw [ih]
    | true, false => simp; rw [ih]
    | true, true =>
      simp
      rw [AddLemmas.rca_lift_carry, AddLemmas.rca_lift_carry, ih]

-- x + y = (x | y) + (x | y) + (x ⊕ y)
theorem add_eq_or_add_or_add_xor : as + bs = (as || bs) + (as || bs) - (as ⊕ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [ih, ← nneg_eq_bneg_inc]
    | false, true =>
      simp
      rw [ih, AddLemmas.rca_lift_carry, AddLemmas.rca_inc_comm, ← nneg_eq_bneg_inc]
    | true, false =>
      simp
      rw [ih, AddLemmas.rca_lift_carry, AddLemmas.rca_inc_comm, ← nneg_eq_bneg_inc]
    | true, true =>
      simp
      rw [
        AddLemmas.rca_lift_carry,
        ih,
        ← nneg_eq_bneg_inc,
        AddLemmas.rca_lift_carry,
        AddLemmas.rca_lift_left_inc
      ]

-- x - y = x + ~y + 1
theorem sub_eq_add_bneg_inc : as - bs = inc (as + ~bs) := by
  rw [nneg_eq_bneg_inc, AddLemmas.rca_lift_right_inc]

-- x - y = (x ⊕ y) - 2(~x & y)
--       = (x ⊕ y) - (~x & y) - (~x & y)
theorem sub_eq_xor_add_and_add_and
  : as - bs = ((as ⊕ bs) - (~as && bs)) - (~as && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]
    | false, true =>
      simp
      rw [AddLemmas.rca_carry_trans_inc_right, ← nneg_eq_bneg_inc, ← Lemmas.inc_inj]
      repeat rw [← AddLemmas.rca_lift_right_inc, ← nneg_eq_bneg_inc]
      exact ih
    | true, false =>
      simp
      repeat rw [← nneg_eq_bneg_inc]
      exact ih
    | true, true =>
      simp
      rw [AddLemmas.rca_carry_trans_inc_right, ← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]

-- x - y = (x & ~y) - (~x & y)
theorem sub_eq_and_bneg_sub_bneg_and
  : as - bs = (as && ~bs) - ((~as) && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]
    | false, true =>
      simp
      rw [← Lemmas.inc_inj, ← AddLemmas.rca_lift_right_inc, ← nneg_eq_bneg_inc, ih]
      rw [← AddLemmas.rca_lift_right_inc, ← nneg_eq_bneg_inc]
    | true, false => simp; rw [← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]
    | true, true =>
      simp
      rw [AddLemmas.rca_carry_trans_inc_right, ← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]

-- x - y = 2(x & ~y) - (x ⊕ ~y)
--       = (x & ~y) + (x & ~y) - (x ⊕ y)
theorem sub_eq_and_bneg_add_and_bneg_sub_xor
  : as - bs = (as && ~bs) + (as && ~bs) - (as ⊕ bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]
    | false, true =>
      simp
      rw [← Lemmas.inc_inj, ← AddLemmas.rca_lift_right_inc, ← nneg_eq_bneg_inc, ih]
      rw [← AddLemmas.rca_lift_right_inc, ← nneg_eq_bneg_inc]
    | true, false =>
      simp
      rw [← nneg_eq_bneg_inc, ih]
      rw [AddLemmas.rca_lift_carry, AddLemmas.rca_inc_comm, ← nneg_eq_bneg_inc]
    | true, true =>
      simp
      rw [AddLemmas.rca_carry_trans_inc_right, ← nneg_eq_bneg_inc, ← nneg_eq_bneg_inc, ih]

-- x ⊕ y = (x | y) - (x & y)
theorem xor_eq_or_sub_and : (as ⊕ bs) = (as || bs) - (as && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> rw [ih]
      <;> (try rw [AddLemmas.rca_carry_trans_inc_right]) <;> rw [← nneg_eq_bneg_inc]

-- x & ~y = (x | y) - y
theorem and_bneg_eq_or_sub : (as && ~bs) = (as || bs) - bs := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← nneg_eq_bneg_inc, ih]

-- x & ~y = x - (x & y)
theorem and_bneg_eq_sub_and : (as && ~bs) = as - (as && bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> (try rw [AddLemmas.rca_carry_trans_inc_right])
      <;> rw [← nneg_eq_bneg_inc, ih]

-- ~(x - y) = y - x - 1
theorem bneg_sub_eq_sub_sub_dec : (~(as - bs)) = dec (bs - as) := by
  rw [DeMorganLemmas.bneg_add_eq_bneg_sub]
  rw [Lemmas.of_nneg_nneg, ← Lemmas.inc_inj, Lemmas.of_inc_dec]
  rw [AddLemmas.add_comm, sub_eq_add_bneg_inc]

-- ~(x - y) = ~x + y
-- We already proved it in De Morgan’s Laws Extended, we'll just use it instead
theorem bneg_sub_eq_bneg_add : (~(as - bs)) = (~as) + bs := by
  exact DeMorganLemmas.bneg_sub_eq_bneg_add

-- (x ≡ y) = (x & y) - (x | y) - 1
theorem xnor_and_sub_or_dec : (as ⊙ bs) = dec ((as && bs) - (as || bs)) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    match a, b with
    | false, false => simp; rw [← Lemmas.nneg_eq_bneg_inc, ih]
    | false, true =>
      simp
      rw [
        ih,
        ← Lemmas.inc_inj,
        ← AddLemmas.rca_lift_right_inc,
        ← Lemmas.nneg_eq_bneg_inc,
        Lemmas.of_inc_dec
      ]
    | true, false =>
      simp
      rw [
        ih,
        ← Lemmas.inc_inj,
        ← AddLemmas.rca_lift_right_inc,
        ← Lemmas.nneg_eq_bneg_inc,
        Lemmas.of_inc_dec
      ]
    | true, true =>
      simp
      rw [
        ih,
        AddLemmas.rca_carry_trans_inc_right,
        ← Lemmas.nneg_eq_bneg_inc
      ]

-- (x ≡ y) = (x & y) + ~(x | y)
theorem xnor_and_add_bneg_or : (as ⊙ bs) = ((as && bs) + ~(as || bs)) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> exact ih

-- (x | y) = (x & ~y) + y
theorem or_eq_and_bneg_add : (as || bs) = ((as && ~bs) + bs) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> exact ih

-- (x & y) = (~x | y) - ~x
theorem and_eq_bneg_or_sub_bneg : (as && bs) = (((~as) || bs) - ~as) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases a <;> cases b <;> simp <;> rw [ih, Lemmas.nneg_eq_bneg_inc, Lemmas.of_bneg_bneg]
      <;> rw [AddLemmas.rca_carry_trans_inc_right]

end
end Binary.AddLogicalLemmas
