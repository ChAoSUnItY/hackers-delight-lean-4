import Binary.Def
import Binary.Basic
import Binary.Lemmas

-- AddLemmas is responsible for ripple carry adder based addition theorems,
-- this including raw boolean algebra level theorems, addition, and subtraction theorems.

namespace Binary.AddLemmas

variable {n : ℕ} {a b c c' : Bit} {as bs cs : Binary n}

public section

open Binary.AddLemmas

-- ripple carry adder properties

theorem rca_no_carry : rca (a ::b as) (b ::b bs) false = (a ^^ b) ::b rca as bs (a && b) := by
  induction a <;> cases b <;> simp

theorem rca_comm : rca as bs c = rca bs as c := by
  induction n generalizing c with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a _
    cases bs with | cons b _
    cases a <;> cases b <;> cases c <;> simp <;> rw [ih]

theorem rca_carry_trans_inc_left : rca as bs true = rca (inc as) bs false := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a _
    cases bs with | cons b _
    cases a <;> cases b <;> simp <;> rw [ih]

theorem rca_carry_trans_inc_right : rca as bs true = rca as (inc bs) false := by
  rw [rca_comm, rca_carry_trans_inc_left, rca_comm]

theorem rca_lift_carry : rca as bs true = inc (rca as bs false) := by
  induction n with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a _
    cases bs with | cons b _
    cases a <;> cases b <;> simp <;> rw [ih]

theorem rca_lift_left_inc : rca (inc as) bs c = inc (rca as bs c) := by
  induction n generalizing c with
  | zero => simp_nil as bs
  | succ n' ih =>
    cases as with | cons a _
    cases bs with | cons b _
    cases a <;> cases b <;> cases c <;> simp
      <;> (try rw [rca_lift_carry]) <;> rw [ih]; rw [rca_lift_carry]

theorem rca_lift_right_inc : rca as (inc bs) c = inc (rca as bs c) := by
  rw [rca_comm, rca_lift_left_inc, rca_comm]

theorem rca_inc_comm : rca (inc as) bs c = rca as (inc bs) c := by
  rw [rca_lift_left_inc, ← rca_lift_right_inc]

theorem rca_carry_left_comm : rca (rca as bs c) cs c' = rca (rca as bs c') cs c := by
  induction n generalizing c c' with
  | zero => simp_nil as bs cs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases cs with | cons c'' cs'
    cases c <;> cases c' <;> cases a <;> cases b <;> cases c''
      <;> (try rfl) <;> (simp; rw [ih])

theorem rca_carry_right_comm : rca as (rca bs cs c) c' = rca as (rca bs cs c') c := by
  rw [rca_comm, rca_carry_left_comm, rca_comm]

-- rca-based addition properties

theorem add_comm : as + bs = bs + as := by
  exact rca_comm

@[simp]
theorem zero_add_eq_id : (zeros n) + as = as := by
  induction n with
  | zero => simp_nil as
  | succ n' ih =>
    cases as
    rw [zeros_cons, rca_no_carry]
    simp
    exact ih

@[simp]
theorem add_zero_eq_id : as + (zeros n) = as := by
  rw [add_comm, zero_add_eq_id]

@[simp]
theorem add_nneg_self_eq_zeros : as + -as = zeros n := by
  induction n with
  | zero => simp_nil as
  | succ n' ih =>
    cases as with | cons a as'
    rw [zeros_cons]
    cases a <;> simp <;> (try rw [rca_carry_trans_inc_right])
      <;> rw [← Lemmas.nneg_eq_bneg_inc, ih]

@[simp]
theorem nneg_self_add_eq_zeros : -as + as = zeros n := by
  rw [add_comm, add_nneg_self_eq_zeros]

theorem add_assoc : as + (bs + cs) = (as + bs) + cs := by
  induction n with
  | zero => simp_nil as bs cs
  | succ n' ih =>
    cases as with | cons a as'
    cases bs with | cons b bs'
    cases cs with | cons c cs'
    match a, b, c with
    | false, false, false => simp; rw [ih]
    | false, false, true  => simp; rw [ih]
    | false, true,  false => simp; rw [ih]
    | false, true,  true  =>
      simp
      rw [rca_carry_right_comm, rca_lift_carry, rca_lift_carry, ih]
    | true,  false, false => simp; rw [ih]
    | true,  false, true  =>
      simp
      rw [rca_lift_carry, rca_lift_carry, ih]
    | true,  true,  false =>
      simp
      rw [rca_carry_left_comm, rca_lift_carry, rca_lift_carry, ih]
    | true,  true,  true  =>
      simp
      rw [rca_carry_left_comm, rca_carry_right_comm, rca_lift_carry, rca_lift_carry, ih]

end
end Binary.AddLemmas
