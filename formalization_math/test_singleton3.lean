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
  have h_S : ∀ x : M, ∀ y : M, S y x = y := by
    intro x y
    rcases lemma3 h y with ⟨e, h_e⟩
    have h1 : y = (x ◇ y) ◇ S e y := h y x e
    rwa [h_e] at h1

  have h_S_eq : ∀ x y : M, (x ◇ y) ◇ y = y := by
    intro x y
    exact h_S x y

  have h3 : ∀ y z : M, y = (z ◇ y) ◇ y := by
    intro y z
    have h_main : y = (z ◇ y) ◇ S y y := h y z y
    rwa [h_S y y] at h_main

  have h4 : ∀ z c b d : M, (d ◇ a) ◇ c ◇ b = ((d ◇ a) ◇ c) ◇ b := rfl
  
  -- The text says:
  -- "Inserting this back into the main equation gives $$(zy)a=y$$ for any $$a,y,z$$."
  -- Wait! $S_a(y) = a$. Thus $x = (yx) S_z(x) \implies x = (yx) z$.
  -- Let's check that.
  have h_eq1 : ∀ x y z : M, x = (y ◇ x) ◇ z := by
    intro x y z
    have h_main : x = (y ◇ x) ◇ S z x := h x y z
    rwa [h_S x z] at h_main
  
  -- From $x = (y x) z$, substituting $x=y, y=z, z=a$:
  -- $y = (z y) a$.
  have h_eq2 : ∀ y z a : M, y = (z ◇ y) ◇ a := by
    intro y z a
    exact h_eq1 y z a

  -- "Thus ab = ((da)c)b = c"
  -- We have $x = (y x) z$. Let $x = c, y = (d a), z = b$.
  -- So $c = ((d a) c) b$.
  have h_eq3 : ∀ a b c d : M, c = ((d ◇ a) ◇ c) ◇ b := by
    intro a b c d
    exact h_eq1 c (d ◇ a) b

  -- And $a b = ((d a) c) b$?
  -- Wait, $y = (z y) a$ for all $y, z, a$. So swapping variables:
  -- $x = (y x) z$. Thus $(y x) z$ is independent of $y$, it evaluates to $x$.
  -- So $((d a) c) b = c$.
  -- And what is $a b$? Is it $a b = c$?
  -- If $(y x) z = x$ for all $x,y,z$, let $y=a, x=b, z=c$. Wait, no.
  -- $y x$ is not defined as an operation, the operation is $y ◇ x$.
  -- We know $(y ◇ x) ◇ z = x$.
  -- So for any $u$, $u ◇ z$ depends on how $u$ was formed?
  -- Wait, let $u = a ◇ b$. We can rewrite $a$ as $y ◇ a$ for some $y$?
  -- No, $(y ◇ x) ◇ z = x$. Let $y=d$, $x=a$. So $(d ◇ a) ◇ c = a$.
  -- Left side is $a ◇ b$. Right side is $((d ◇ a) ◇ c) ◇ b$. Since $(d ◇ a) ◇ c = a$, this is exactly $a ◇ b$.
  -- Ah! $((d ◇ a) ◇ c) ◇ b$ can be simplified two ways:
  -- 1) $((d ◇ a) ◇ c) ◇ b = c$ (by $(y x) z = x$ with $y=d ◇ a, x=c, z=b$)
  -- 2) $((d ◇ a) ◇ c)$ is $a$ (by $(y x) z = x$ with $y=d, x=a, z=c$). So $((d ◇ a) ◇ c) ◇ b = a ◇ b$.
  -- So $a ◇ b = c$!
  -- This holds for all $c$. Thus $a ◇ b = c$ for all $c$.
  
  have h_step1 : ∀ a c d : M, (d ◇ a) ◇ c = a := by
    intro a c d
    exact h_eq1 a d c

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
