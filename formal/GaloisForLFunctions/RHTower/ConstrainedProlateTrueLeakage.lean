import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer

/-!
# Trial-space upper bounds for the true prolate leakage

The concrete leakage deficits `evenProlateLeakageValue a n = 1 − evenProlateConcentrationValue
a n` are the greedy eigenvalues of the actual concentration operator `Tₐ†Tₐ = Tₐ²`, subtracted
from one.  Nonnegativity and monotonicity in the index are already unconditional; what remains
for the constrained transfer contract is an envelope, whose upper half is a concentration
estimate.

Because the greedy value is by definition a constrained operator norm, the Courant–Fischer
lower bound applies verbatim: a trial subspace of dimension exceeding `n` on which the
concentration operator is bounded below by `M` caps the `n`-th leakage at `1 − M`.  Cauchy–Schwarz
converts the natural *form* estimate on a trial space — the Fourier mass retained inside the
aperture, `‖Tₐ f‖² ≥ M‖f‖²` — into the operator bound the greedy value consumes.

Consequently a concentration estimate on an explicit `(n+1)`-dimensional family of aperture-
supported functions yields a leakage bound with no further operator theory.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The greedy concentration value is a constrained operator norm, so Courant–Fischer applies:
a trial subspace of dimension exceeding `n` on which the concentration operator is bounded below
by `M` forces `M ≤ evenProlateConcentrationValue a n`. -/
theorem le_evenProlateConcentrationValue_of_trial (a : ℝ) (n : ℕ)
    (V : Submodule ℂ evenSubspace) (hV : n < Module.finrank ℂ V)
    {M : ℝ} (hM : ∀ f ∈ V, M * ‖f‖ ≤ ‖evenProlateConcentration a f‖) :
    M ≤ evenProlateConcentrationValue a n :=
  ContinuousLinearMap.le_orthSup_of_trial _ _ n V hV hM

/-- **The trial-space leakage bound.**  A trial subspace of dimension exceeding `n` on which the
concentration operator is bounded below by `M` caps the `n`-th leakage at `1 − M`. -/
theorem evenProlateLeakageValue_le_of_trial (a : ℝ) (n : ℕ)
    (V : Submodule ℂ evenSubspace) (hV : n < Module.finrank ℂ V)
    {M : ℝ} (hM : ∀ f ∈ V, M * ‖f‖ ≤ ‖evenProlateConcentration a f‖) :
    evenProlateLeakageValue a n ≤ 1 - M := by
  have h := le_evenProlateConcentrationValue_of_trial a n V hV hM
  unfold evenProlateLeakageValue
  linarith

/-- The concentration form is exactly the Fourier mass retained inside the aperture. -/
theorem inner_evenProlateConcentration_eq (a : ℝ) (f : evenSubspace) :
    inner ℂ (evenProlateConcentration a f) f
      = ((‖evenTimeBandFourier a f‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have h := evenProlateLeakage_inner_eq a f
  have hsub : evenProlateLeakage a f = f - evenProlateConcentration a f := by
    rw [evenProlateLeakage, _root_.sub_apply, one_apply_eq_self]
  rw [hsub, inner_sub_left, inner_self_eq_norm_sq_to_K] at h
  push_cast at h ⊢
  linear_combination -h

/-- Cauchy–Schwarz turns the retained-Fourier-mass form estimate into the operator bound the
greedy value consumes. -/
theorem norm_evenProlateConcentration_ge_of_form (a : ℝ) {M : ℝ} {f : evenSubspace}
    (hf : M * ‖f‖ ^ (2 : ℕ) ≤ ‖evenTimeBandFourier a f‖ ^ (2 : ℕ)) :
    M * ‖f‖ ≤ ‖evenProlateConcentration a f‖ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · have hfpos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
    have hn := norm_inner_le_norm (𝕜 := ℂ) (evenProlateConcentration a f) f
    rw [inner_evenProlateConcentration_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)] at hn
    have hstep : M * ‖f‖ * ‖f‖ ≤ ‖evenProlateConcentration a f‖ * ‖f‖ := by
      nlinarith [hf, hn]
    exact le_of_mul_le_mul_right hstep hfpos

/-- **The concentration-estimate form of the leakage bound.**  An `(n+1)`-dimensional trial
space of aperture-supported functions retaining a fraction `1 − ε` of their squared norm inside
the aperture caps the `n`-th leakage at `ε`.  This is the exact interface between an analytic
concentration estimate and the constrained transfer contract. -/
theorem evenProlateLeakageValue_le_of_form_trial (a : ℝ) (n : ℕ)
    (V : Submodule ℂ evenSubspace) (hV : n < Module.finrank ℂ V)
    {ε : ℝ} (hV2 : ∀ f ∈ V, (1 - ε) * ‖f‖ ^ (2 : ℕ) ≤ ‖evenTimeBandFourier a f‖ ^ (2 : ℕ)) :
    evenProlateLeakageValue a n ≤ ε := by
  have h := evenProlateLeakageValue_le_of_trial a n V hV
    (M := 1 - ε) fun f hf => norm_evenProlateConcentration_ge_of_form a (hV2 f hf)
  linarith

end RHTower
