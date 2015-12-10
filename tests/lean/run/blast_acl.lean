import algebra.ordered_ring

universe l
constants (A : Type.{l}) (s : linear_ordered_comm_ring A)
attribute s [instance]

constants (x y z : A)

set_option blast.strategy "acl"

example : 0 < 1 * y + 1 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y + 2 → 0 < (-1) * y + -1 → false := by blast
example : 0 < 2 * y → 0 < (-1) * y → false := by blast
example : 0 < 1 * x + 2 * y →  0 < 2 * y + (-1) * x → 0 < (-1) * y → false := by blast
example : 0 < (-3) * x + ((-7) * y + 4) → 0 < 2 * x + -3 → 0 ≤ 1 * y → false := by blast
