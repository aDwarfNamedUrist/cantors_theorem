import Mathlib.Tactic

def isBijective (A : Type) (B : Type) :=
    ∃ (f : A → B), ∃ (fi : B → A), (f ∘ fi = id) ∧ (fi ∘ f = id)

-- My proof of cantor's theorm.  That |ℵ_0| ≠ |2^ℵ_0|
theorem cantor : ¬ isBijective ℕ (ℕ → Bool) := by
    rw [isBijective]

    -- This tactic pushes negations as far down into the expression as they can go
    -- In this case, that means we can do all the intros in one step
    push_neg

    -- Putting an underscore in an intro allows ignoring the variable
    intro f g hfg _

    -- If you type `simp?` you will see a recommendation for which lemmas to use in the info panel
    -- When using `simp` in the middle of proofs, be sure to use `simp only` to avoid potential breakage
    -- Many tactics can be provided with explicit lemmas to use
    -- In this case, this not only replaces all the funext rewrites, but also the `comp_rewrite` lemma and the `id` rewrite
    simp only [Function.funext_iff, Function.comp_apply, id_eq] at hfg

    -- The `set` tactic allows you to introduce a new function or value, along with a proof that it equals its definition
    set D: ℕ → Bool := fun a ↦ !f a a with hD
    set d : Nat := g D with hd


    apply (f d d).self_ne_not

    have h2 := hfg D d

    --since after the rewrites we have an assumption that solves the goal, we use `rwa`
    rwa [←hd, hD] at h2


-- This version of the proof 
theorem cantor2 : ¬ isBijective ℕ (ℕ → Bool) := by
    rw [isBijective]
    push_neg
    intro f g hfg _
    simp only [Function.funext_iff, Function.comp_apply, id_eq] at hfg
    let D: ℕ → Bool := fun a ↦ !f a a
    let d : Nat := g D
    exact (f d d).self_ne_not (hfg D d)
