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

lemma lemma3 (h : Equation1689 M) (a : M) : ∃ e : M, S e a = a := by
  have h_lem2 := lemma2 h a
  rcases h_lem2 with ⟨b, c, d, h_f_eq_S⟩

  have h1 : a = ((a ◇ a) ◇ a) ◇ (a ◇ f b c) := by
    -- main equation: x = (y x) ((x z) z)
    -- a = (a^2 a) ((a b) b) = (a^2 a) S_b(a)
    have h_main : a = ((a ◇ a) ◇ a) ◇ S b a := h a (a ◇ a) b
    have h_lem1 := lemma1 h a b c
    rw [h_lem1] at h_main
    exact h_main

  have h2 : a ◇ f b c = f a d := by
    calc
      a ◇ f b c = a ◇ S d a := by rw [h_f_eq_S]
      _ = f a d := rfl

  have h3 : a = ((a ◇ a) ◇ a) ◇ f a d := by
    rw [h2] at h1
    exact h1

  have h4 : S a a = a ◇ f a d := by
    exact lemma1 h a a d

  have h5 : a = (a ◇ f a d) ◇ f a d := by
    have h_S_eq : S a a = (a ◇ a) ◇ a := rfl
    rw [← h_S_eq] at h3
    rw [h4] at h3
    exact h3

  use f a d
  exact h5.symm
