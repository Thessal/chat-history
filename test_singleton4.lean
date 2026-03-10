import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M: Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)
abbrev Equation2 (M: Type _) [Magma M] := ∀ x y : M, x = y

variable {M : Type _} [Magma M]

abbrev S (z x : M) : M := (x ◇ z) ◇ z
abbrev f (x y : M) : M := x ◇ S y x

lemma lemma3 (h : Equation1689 M) (a : M) : ∃ e : M, S e a = a := sorry
theorem singleton_law (h : Equation1689 M) : Equation2 M := by
  intro a b
  -- wait, rwa fails because S e y = y doesn't exactly match?
  -- Oh, `h_e : S e y = y` and `h1 : y = (x ◇ y) ◇ S e y`.
  -- So `rw [h_e] at h1` gives `y = (x ◇ y) ◇ y`. But our goal is `S y x = y`!
  -- Oh! `S y x = (x ◇ y) ◇ y`. So we need `S y x = y`.
  -- `h1` implies `y = S y x` directly! 
  have h_S : ∀ x : M, ∀ y : M, S y x = y := by
    intro x y
    rcases lemma3 h y with ⟨e, h_e⟩
    have h1 : y = (x ◇ y) ◇ S e y := h y x e
    rw [h_e] at h1
    exact h1.symm

  have h_eq1 : ∀ x y z : M, x = (y ◇ x) ◇ z := by
    intro x y z
    have h_main : x = (y ◇ x) ◇ S z x := h x y z
    rwa [h_S x z] at h_main

  have h_step1 : ∀ a c d : M, (d ◇ a) ◇ c = a := by
    intro a c d
    exact (h_eq1 a d c).symm

  have h_step2 : ∀ a b c d : M, ((d ◇ a) ◇ c) ◇ b = a ◇ b := by
    intro a b c d
    rw [h_step1 a c d]

  have h_step3 : ∀ a b c d : M, ((d ◇ a) ◇ c) ◇ b = c := by
    intro a b c d
    exact (h_eq1 c (d ◇ a) b).symm

  have h_step4 : ∀ a b c d : M, a ◇ b = c := by
    intro a b c d
    calc
      a ◇ b = ((d ◇ a) ◇ c) ◇ b := (h_step2 a b c d).symm
      _ = c := h_step3 a b c d

  have h_step5 : a ◇ b = a := h_step4 a b a a
  have h_step6 : a ◇ b = b := h_step4 a b b a
  exact h_step5.symm.trans h_step6
