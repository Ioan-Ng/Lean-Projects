import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic
variable (R : Type*) [CommRing R]
variable (a b : R)

--axioms
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

example (a b : ℕ) : (a + b) * (a + b) * (a + b) = a*a*a + 3*(a*a*b) + 3*(a*b*b) + b*b*b := by ring
