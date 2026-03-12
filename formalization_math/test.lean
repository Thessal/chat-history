import Mathlib.Tactic
class Magma (α : Type _) where
  op : α → α → α
infix:65 " ◇ " => Magma.op
variable {M : Type _} [Magma M]
abbrev S (z x : M) : M := (x ◇ z) ◇ z
abbrev f (x y : M) : M := x ◇ S y x
