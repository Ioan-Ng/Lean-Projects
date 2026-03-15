import Mathlib.Algebra.Ring.Basic
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw[add_right_comm,add_assoc,neg_add_cancel,add_zero]
theorem add_left_cancel_calc {a b c : R} (h : a + b = a + c) : b = c :=
  calc
    b = 0 + b        := by rw [zero_add]
    _ = (-a + a) + b := by rw [neg_add_cancel]
    _ = -a +(a + b)  := by rw [add_assoc]
    _ = -a +(a + c)  := by rw [h]
    _ = (-a + a) + c := by rw [← add_assoc]
    _ = c := by rw[neg_add_cancel, add_comm, add_zero]
end MyRing
