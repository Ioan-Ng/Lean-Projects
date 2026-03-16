import Mathlib.Algebra.Ring.Basic
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw[add_right_comm,add_assoc,neg_add_cancel,add_zero]
--practice thing
theorem add_left_cancel_calc {a b c : R} (h : a + b = a + c) : b = c :=
  calc
    b = 0 + b        := by rw [zero_add]
    _ = (-a + a) + b := by rw [neg_add_cancel]
    _ = -a +(a + b)  := by rw [add_assoc]
    _ = -a +(a + c)  := by rw [h]
    _ = (-a + a) + c := by rw [← add_assoc]
    _ = c := by rw[neg_add_cancel, add_comm, add_zero]
--have gives us a way to prove a smaller hypothesis and then use this
--proven hypothesis to prove our main goal
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0*a + 0*a = 0*a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw[add_left_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have h1: a+b-a= 0-a :=by
    rw[h]
  rw[add_comm,add_sub_assoc,sub_self, add_zero,zero_sub] at h1
  exact h1.symm


end MyRing
