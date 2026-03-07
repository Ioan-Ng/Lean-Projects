import Mathlib.Data.Real.Basic

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc  b c a]
  rw [mul_comm a c]


example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [ <- mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example (a b : ℕ) : (a + b) * (a + b) * (a + b) = a*a*a + 3*(a*a*b) + 3*(a*b*b) + b*b*b :=
  calc
    (a + b) * (a + b) * (a + b) = (a*(a+b) +b*(a+b)) *(a+b) := by
      rw[add_mul]
    _ = (a*a + a*b + (b*a + b*b)) * (a + b) := by
      rw[mul_add a a b, mul_add b a b]
    _ = (a*a + a*b +a *b + b*b) * (a + b) := by
      rw[<-add_assoc, mul_comm b a]
    _ = (a*a + a*b +(a *b + b*b)) * (a + b) := by
      rw[add_assoc]
    _ = (a*a + (a*b + a*b) + b*b) * (a+b) := by
      rw[← add_assoc, add_assoc (a *  a )]
    _ = (a*a + 2*a*b + b*b) *(a+b) := by
      rw[← two_mul, ← mul_assoc]
    _ = (a * a + 2 * a * b + b * b) * a + (a * a + 2 * a * b + b * b) * b:= by
      rw[mul_add]
    _ = a * a * a + a * 2 * a * b + a * b * b + b * a * a + b * 2 * a * b + b * b * b := by
      rw[mul_comm, mul_comm  (a * a + 2 * a * b + b * b) b, mul_add, mul_add,]
      rw[ mul_add, mul_add,← mul_assoc,← mul_assoc,←mul_assoc,]
      rw[← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← mul_assoc,← add_assoc,← add_assoc]
    _ = a*a*a + 2*a*a*b + a*b*b + b*a*a + 2*b*a*b + b*b*b := by
      rw[mul_comm a 2, mul_comm b 2]
    _ = a*a*a + 2*a*a*b + a*b*b + b*a*a + 2*b*b*a + b*b*b := by
      conv =>
        lhs
        pattern  2*b*a*b
        rw[mul_right_comm]
    _ = a*a*a + 2*a*a*b + a*b*b + a*a*b + 2*b*b*a + b*b*b := by
      conv =>
        lhs
        pattern b*a*a
        rw[mul_comm,mul_comm b a, ← mul_assoc]
    _=  a*a*a + 2*a*a*b + a*a*b + a*b*b + 2*b*b*a + b*b*b := by
        rw[add_assoc (a*a*a + 2*a*a*b) (a*b*b), add_comm (a*b*b) (a*a*b) ,←add_assoc,]
    _= a*a*a + 3*(a*a*b) + a*b*b + 2*b*b*a + b*b*b:= by
      conv =>
        lhs
        rw[add_assoc (a*a*a)]
        pattern 2*a*a*b + a*a*b
        rw[← one_mul  (a*a*b),mul_assoc 2 a a, ]
        rw[mul_assoc 2 (a * a) b,← add_mul 2 1 (a * a * b) ,show 2+ 1 = 3 by rfl]
    _= a*a*a + 3*(a*a*b) + 3*(a*b*b) + b*b*b := by
      conv =>
        lhs
        rw[add_assoc (a*a*a + 3*(a*a*b))]
        pattern a*b*b + 2*b*b*a
        rw[← one_mul (a*b*b), mul_assoc 2 b b, mul_assoc 2 (b*b),]
        rw[mul_comm (b*b), ← mul_assoc a, ← add_mul 1 2 (a*b*b), show 2+1 = 3 by rfl]
