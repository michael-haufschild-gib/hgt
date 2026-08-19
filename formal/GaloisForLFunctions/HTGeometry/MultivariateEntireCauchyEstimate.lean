import GaloisForLFunctions.HTGeometry.MultivariateEntirePartialDeriv
import GaloisForLFunctions.HTGeometry.MultivariateJetCompositionLaw
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy's estimate for the jets of a multivariate entire source

A mixed jet of an entire source is an iterated directional derivative, and each directional
derivative is a one-variable derivative along the corresponding complex line.  So the whole jet
calculus inherits Cauchy's estimate one slot at a time: the bound on a directional derivative at a
point is the supremum of the source on a circle in that direction, divided by the radius.
-/

open Metric Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An entire source is differentiable. -/
theorem differentiable_multivariateEntire {d : ℕ} (g : MultivariateEntire d) :
    Differentiable ℂ (g.1 : (Fin d → ℂ) → ℂ) :=
  fun x => ((MultivariateEntire.analyticOnNhd g) x (Set.mem_univ x)).differentiableAt

/-- The complex line through a point in a fixed direction. -/
theorem hasDerivAt_lineThrough {d : ℕ} (x v : Fin d → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => x + s • v) v t := by
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-- The restriction of an entire source to a complex line is differentiable, with the directional
derivative as its derivative. -/
theorem hasDerivAt_multivariateEntire_line {d : ℕ} (v : Fin d → ℂ) (g : MultivariateEntire d)
    (x : Fin d → ℂ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => g.1 (x + s • v))
      (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) (x + t • v) v) t :=
  ((differentiable_multivariateEntire g (x + t • v)).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_lineThrough x v t)

/-- **Cauchy's estimate for a directional derivative of an entire source.** -/
theorem norm_partialDerivEntire_le {d : ℕ} (v : Fin d → ℂ) (g : MultivariateEntire d)
    (x : Fin d → ℂ) {r M : ℝ} (hr : 0 < r)
    (hM : ∀ t : ℂ, ‖t‖ = r → ‖g.1 (x + t • v)‖ ≤ M) :
    ‖(partialDerivEntire v g).1 x‖ ≤ M / r := by
  set f : ℂ → ℂ := fun s => g.1 (x + s • v) with hf
  have hline : ∀ t : ℂ, HasDerivAt f (fderiv ℂ (g.1 : (Fin d → ℂ) → ℂ) (x + t • v) v) t :=
    fun t => hasDerivAt_multivariateEntire_line v g x t
  have hdiff : Differentiable ℂ f := fun t => (hline t).differentiableAt
  have hval : (partialDerivEntire v g).1 x = deriv f 0 := by
    rw [partialDerivEntire_apply, (hline 0).deriv]
    simp
  rw [hval]
  have hcauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (f := f) (c := 0)
    (R := r) (C := M) 1 hr hdiff.diffContOnCl
    (fun w hw => hM w (by simpa using mem_sphere_iff_norm.mp hw))
  rw [iteratedDeriv_one] at hcauchy
  simpa using hcauchy

/-- A coordinate direction is a unit vector, so a scalar multiple of it moves a point by at most the
size of the scalar. -/
theorem norm_smul_coordinateJetDirection_le {d : ℕ} (t : ℂ) (i : Fin d) :
    ‖t • coordinateJetDirection i‖ ≤ ‖t‖ := by
  rw [norm_smul]
  have hle : ‖coordinateJetDirection i‖ ≤ 1 := by
    rw [coordinateJetDirection, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  calc ‖t‖ * ‖coordinateJetDirection i‖ ≤ ‖t‖ * 1 :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg t)
    _ = ‖t‖ := mul_one _

/-- **Cauchy's estimate for an ordered mixed jet.**  A word of length `n` costs one power of the
radius per slot, against the supremum on the ball the whole word can reach. -/
theorem norm_wordPartialDerivEntire_le {d : ℕ} :
    ∀ (n : ℕ) (word : Fin n → Fin d) (g : MultivariateEntire d) (x : Fin d → ℂ) (ρ M : ℝ),
      0 < ρ → (∀ y : Fin d → ℂ, ‖y - x‖ ≤ (n : ℝ) * ρ → ‖g.1 y‖ ≤ M) →
      ‖(wordPartialDerivEntire word g).1 x‖ ≤ M / ρ ^ n := by
  intro n
  induction n with
  | zero =>
      intro word g x ρ M hρ hM
      have hx : ‖g.1 x‖ ≤ M := hM x (by simp)
      simpa [wordPartialDerivEntire] using hx
  | succ n ih =>
      intro word g x ρ M hρ hM
      set i : Fin d := word (Fin.last n) with hi
      set h : MultivariateEntire d := partialDerivEntire (coordinateJetDirection i) g with hh
      have hstep : ∀ y : Fin d → ℂ, ‖y - x‖ ≤ (n : ℝ) * ρ → ‖h.1 y‖ ≤ M / ρ := by
        intro y hy
        refine norm_partialDerivEntire_le (coordinateJetDirection i) g y hρ ?_
        intro t ht
        refine hM (y + t • coordinateJetDirection i) ?_
        have hmove : ‖t • coordinateJetDirection i‖ ≤ ρ := by
          rw [← ht]
          exact norm_smul_coordinateJetDirection_le t i
        have hsplit : y + t • coordinateJetDirection i - x
            = (y - x) + t • coordinateJetDirection i := by ring
        rw [hsplit]
        refine le_trans (norm_add_le _ _) ?_
        push_cast
        linarith
      have hrec : wordPartialDerivEntire word g = wordPartialDerivEntire (Fin.init word) h := rfl
      rw [hrec]
      have hIH := ih (Fin.init word) h x ρ (M / ρ) hρ hstep
      calc ‖(wordPartialDerivEntire (Fin.init word) h).1 x‖ ≤ (M / ρ) / ρ ^ n := hIH
        _ = M / ρ ^ (n + 1) := by
            rw [div_div, ← pow_succ']

/-- **Cauchy's estimate for a multi-index jet.**  The jet of total degree `n` is bounded by the
supremum of the source on the ball of radius `n·ρ`, divided by `ρ^n`. -/
theorem norm_multiIndexJetEvalCLM_le {d : ℕ} (x : Fin d → ℂ) (a : Fin d →₀ ℕ)
    (g : MultivariateEntire d) {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ y : Fin d → ℂ,
      ‖y - x‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * ρ → ‖g.1 y‖ ≤ M) :
    ‖multiIndexJetEvalCLM x a g‖ ≤ M / ρ ^ (Fintype.card (MultiIndexSlot a)) := by
  rw [multiIndexJetEvalCLM_apply, orderedPartialJetEvalCLM_eq_wordPartialDerivEntire]
  exact norm_wordPartialDerivEntire_le _ (multiIndexWord a) g x ρ M hρ hM

end

end GaloisForLFunctions.HTGeometry
