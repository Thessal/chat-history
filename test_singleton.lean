import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev Equation1689 (M: Type _) [Magma M] := ∀ x y z : M, x = (y ◇ x) ◇ ((x ◇ z) ◇ z)
abbrev Equation2 (M: Type _) [Magma M] := ∀ x y : M, x = y

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
  have h4 : S a a = a ◇ f a d := lemma1 h a a d
  have h5 : a = (a ◇ f a d) ◇ f a d := by
    have h_S_eq : S a a = (a ◇ a) ◇ a := rfl
    rw [← h_S_eq] at h3
    rw [h4] at h3
    exact h3
  use f a d
  exact h5.symm

theorem singleton_law (h : Equation1689 M) : Equation2 M := by
  intro a b
  have h_lem3 := lemma3 h a
  rcases h_lem3 with ⟨e, h_e⟩

  have h1 : ∀ y : M, (y ◇ a) ◇ a = a := by
    intro y
    -- By main equation: a = (y a) ((a e) e) = (y a) S_e(a)
    have h_main : a = (y ◇ a) ◇ S e a := h a y e
    rwa [h_e] at h_main

  have h2 : ∀ y z : M, y = (z ◇ y) ◇ a := by
    intro y z
    -- main eq: y = (z y) S_a(y) = (z y) ((y a) a)
    have h_main : y = (z ◇ y) ◇ S a y := h y z a
    -- But by h1, S a y = (y ◇ a) ◇ a = a
    have h_S_a_y : S a y = a := by exact (h1 y).symm
    rwa [h_S_a_y] at h_main

  -- Thus ab = ((da)c)b = c
  -- Wait, $$y = (z y) a$$. Letting $y=b$, $z=(d a) c$, we have $b = (((d a) c) b) a$...
  -- Actually let's look at the text: $ab = ((da)c)b = c$. 
  -- From `h3`, we have $y = (z y) a$. Specifically $(z y) a = y$.
  have h3 : ∀ y z : M, (z ◇ y) ◇ a = y := by
    intro y z
    exact (h2 y z).symm

  -- So $(x y) a = y$. To show $a b = c$:
  -- text: `ab = ((da)c)b = c`
  -- Wait, `ab = ((da)c)b` uses `x = (y x) ((x z) z)`? No, it just uses h3 right-to-left.
  
  -- Let's define the steps manually.
  have h4 : ∀ c d : M, a ◇ b = ((d ◇ a) ◇ c) ◇ b := by
    intro c d
    -- By `h2 a d`: `a = (d a) a`.
    -- So $a b = ((d a) a) b$? The text says $ab = ((da)c)b$.
    -- Ah! $a = (c a) a$ by h1? No, `(y a) a = a` so `a = (c a) a`.
    -- Wait. If `y = (z y) a`, then `a = (z a) a` is just the previous result `a = (y a) a` (h1).
    -- Wait, if $y = (zy)a$, then $a = (za)a$. Let $z = c$, so $a = (ca)a$.
    -- So $a b = ((ca)a) b$? Still doesn't match `ab = ((da)c)b`.
    sorry

  have h6 : ∀ c d : M, a ◇ b = c := by
    sorry

  have h7 : a ◇ b = a := h6 a a
  have h8 : a ◇ b = b := h6 b b
  exact h7.symm.trans h8

