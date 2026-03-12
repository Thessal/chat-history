import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M: Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

variable {M : Type _} [Magma M]

abbrev S (z x : M) : M := (x ◇ z) ◇ z
abbrev f (x y : M) : M := x ◇ S y x

lemma lemma1_sub (h : Equation1689 M) (a b z : M) : S b a = a ◇ S z (S b a) := by
  have h1 : (a ◇ a) ◇ S b a = a := (h a a b).symm
  have h2 := h (S b a) (a ◇ a) z
  rwa [h1] at h2

lemma lemma1 (h : Equation1689 M) (a b c : M) : S b a = a ◇ f b c := by
  have h2 : ∀ z : M, S b a = a ◇ S z (S b a) := lemma1_sub h a b
  have h3 : S b a ◇ S c b = b := (h b (a ◇ b) c).symm
  have h4 : S b a = a ◇ f b c := by
    have h4_1 := h2 (S c b)
    have h4_2 : S (S c b) (S b a) = (S b a ◇ S c b) ◇ S c b := rfl
    rw [h4_2, h3] at h4_1
    exact h4_1
  exact h4

lemma lemma2 (h : Equation1689 M) (a : M) : ∃ b c d : M, f b c = S d a := by
  have h1 : ∀ x c : M, f (S x a) c = (a ◇ S c (S x a)) ◇ S c (S x a) := by
    intro x c
    have h_sub : S x a = a ◇ S c (S x a) := lemma1_sub h a x c
    exact congrArg (fun p => p ◇ S c (S x a)) h_sub
  use S a a
  use a
  use S a (S a a)
  exact h1 a a
