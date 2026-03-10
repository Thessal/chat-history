import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M: Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)
abbrev Equation2 (M: Type _) [Magma M] := ∀ x y : M, x = y

variable {M : Type _} [Magma M]

abbrev S (z x : M) : M := (x ◇ z) ◇ z
abbrev f (x y : M) : M := x ◇ S y x

lemma lemma1 (h : Equation1689 M) (a b c : M) : S b a = a ◇ f b c := by
  have h1 : (a ◇ a) ◇ S b a = a := (h a a b).symm
  have h2 : ∀ z : M, S b a = a ◇ S z (S b a) := by
    intro z
    have h2_1 := h (S b a) (a ◇ a) z
    rwa [h1] at h2_1
  have h3 : S b a ◇ S c b = b := (h b (a ◇ b) c).symm
  have h4 : S b a = a ◇ f b c := by
    have h4_1 := h2 (S c b)
    have h4_2 : S (S c b) (S b a) = (S b a ◇ S c b) ◇ S c b := rfl
    rw [h4_2, h3] at h4_1
    exact h4_1
  exact h4
