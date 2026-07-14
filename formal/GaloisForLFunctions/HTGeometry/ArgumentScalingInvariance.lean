import GaloisForLFunctions.HTGeometry.SignedGammaHypertranscendental

/-!
# Unconditional argument-scaling invariance of differential algebraicity

`f(c·)` is differentially algebraic iff `f` is, for any `c ≠ 0`, with **no smoothness hypothesis** on
`f`.  The chain rule `iteratedDeriv k (f ∘ (c·)) = cᵏ·(iteratedDeriv k f)∘(c·)` holds unconditionally
here: mathlib's `deriv_comp_mul_left` is stated with the `0`-fallback convention for undefined
derivatives, so non-differentiability transfers through the scaling diffeomorphism `z ↦ cz` and both
sides agree even at singularities.  This removes the `ContDiff` hypothesis of
`differentiallyAlgebraic_comp_const_mul_iff`, which forced the earlier restriction to entire functions.

The payoff is that `Γ` and `ψ = Γ'/Γ` remain hypertranscendental after an **arbitrary positive
rescaling** of the argument: `Γ(c·s + d)` and `ψ(c·s + d)` are hypertranscendental for every `c ≠ 0`.
This is exactly the general commensurable-scale single Gamma/digamma factor of the signed-archimedean
orbit-charge law (§1–§3): the earlier `hypertranscendental_gamma_add_const` handled only unit scale,
because scaling invariance was available only for globally smooth functions, which `Γ` is not.

* `iteratedDeriv_comp_mul_left_uncond` — the unconditional scaled chain rule.
* `DifferentiallyAlgebraic.comp_const_mul_uncond`, `differentiallyAlgebraic_comp_const_mul_iff_uncond`,
  `hypertranscendental_comp_const_mul_iff_uncond` — the invariance, no smoothness hypothesis.
* `hypertranscendental_gamma_affine`, `hypertranscendental_digamma_affine` — the scaled+shifted
  Gamma/digamma factors are hypertranscendental at any scale.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- **Unconditional scaled chain rule.**  `(f(c·))⁽ⁿ⁾(x) = cⁿ·f⁽ⁿ⁾(cx)` with no differentiability
hypothesis, using mathlib's unconditional `deriv_comp_mul_left`. -/
theorem iteratedDeriv_comp_mul_left_uncond (f : ℂ → ℂ) (c : ℂ) (n : ℕ) (x : ℂ) :
    iteratedDeriv n (fun z => f (c * z)) x = c ^ n * iteratedDeriv n f (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    rw [show iteratedDeriv n (fun z => f (c * z))
          = (fun x => c ^ n * iteratedDeriv n f (c * x)) from funext ih]
    rw [deriv_const_mul_field, deriv_comp_mul_left c (iteratedDeriv n f) x, smul_eq_mul,
      ← iteratedDeriv_succ]
    ring

/-- The argument-scaling jet substitution: the point slot scales by `c` (`z ↦ cz`) and the order-`j`
jet slot scales by `c⁻ʲ`, inverting `f⁽ʲ⁾(cz) = c⁻ʲ·(f(c·))⁽ʲ⁾(z)`. -/
def jetArgScaleSub (n : ℕ) (c : ℂ) : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (C c * X 0) (fun j => C (c⁻¹ ^ (j : ℕ)) * X j.succ)

/-- **Argument scaling preserves differential algebraicity, unconditionally.**  If `f` is
differentially algebraic then so is `z ↦ f(cz)` for every `c ≠ 0`, with no smoothness hypothesis. -/
theorem DifferentiallyAlgebraic.comp_const_mul_uncond {f : ℂ → ℂ}
    (hf : DifferentiallyAlgebraic f) {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraic (fun z => f (c * z)) := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  refine ⟨n, bind₁ (jetArgScaleSub n c) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetArgScaleSub n c⁻¹) (bind₁ (jetArgScaleSub n c) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetArgScaleSub n c⁻¹) (jetArgScaleSub n c i))
          = (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetArgScaleSub, Fin.cases_zero, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
        | succ j =>
          simp only [jetArgScaleSub, Fin.cases_succ, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, inv_inv, ← mul_pow, inv_mul_cancel₀ hc, one_pow, map_one,
            one_mul]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (c * w)) z)
          (jetArgScaleSub n c i))
        = Fin.cons (c * z) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (c * z)) := by
      funext i
      induction i using Fin.cases with
      | zero =>
        simp only [jetArgScaleSub, Fin.cases_zero, eval_mul, eval_C, eval_X, Fin.cons_zero]
      | succ j =>
        simp only [jetArgScaleSub, Fin.cases_succ, eval_mul, eval_C, eval_X, Fin.cons_succ]
        rw [iteratedDeriv_comp_mul_left_uncond f c (j : ℕ) z, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hc, one_pow, one_mul]
    rw [hvec]
    exact hPz (c * z)

/-- Argument scaling is a differential-algebraicity equivalence, unconditionally (`c ≠ 0`). -/
theorem differentiallyAlgebraic_comp_const_mul_iff_uncond {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraic (fun z => f (c * z)) ↔ DifferentiallyAlgebraic f := by
  constructor
  · intro h
    have h2 := h.comp_const_mul_uncond (inv_ne_zero hc)
    have hfun : (fun z => (fun w => f (c * w)) (c⁻¹ * z)) = f := by
      funext z
      show f (c * (c⁻¹ * z)) = f z
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rwa [hfun] at h2
  · exact fun h => h.comp_const_mul_uncond hc

/-- **Hypertranscendence is argument-scaling invariant, unconditionally** (`c ≠ 0`, no smoothness). -/
theorem hypertranscendental_comp_const_mul_iff_uncond {f : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) :
    Hypertranscendental (fun z => f (c * z)) ↔ Hypertranscendental f :=
  (differentiallyAlgebraic_comp_const_mul_iff_uncond hc).not

/-- **A rescaled shifted Gamma factor is hypertranscendental at any scale.**  `Γ(c·s + d)` satisfies no
algebraic differential equation for every `c ≠ 0` — the general commensurable-scale single Gamma factor
of the orbit-charge law (§1), now with genuine rescaling, not only the unit scale. -/
theorem hypertranscendental_gamma_affine {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    Hypertranscendental (fun s => Complex.Gamma (c * s + d)) := by
  have h := (hypertranscendental_comp_const_mul_iff_uncond
      (f := fun t => Complex.Gamma (t + d)) hc).mpr
    (HTGeometry.hypertranscendental_gamma_add_const d)
  simpa using h

/-- **A rescaled shifted digamma factor is hypertranscendental at any scale.**  `ψ(c·s + d)` satisfies
no algebraic differential equation for every `c ≠ 0` — the logarithmic-derivative carrier of a single
common-scale Gamma orbit factor `Γ(c·s + d)^m`, at genuine scale. -/
theorem hypertranscendental_digamma_affine {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    Hypertranscendental (fun s => Complex.digamma (c * s + d)) := by
  have h := (hypertranscendental_comp_const_mul_iff_uncond
      (f := fun t => Complex.digamma (t + d)) hc).mpr
    (HTGeometry.hypertranscendental_digamma_add_const d)
  simpa using h

end GaloisForLFunctions

end
