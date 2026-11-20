import GaloisForLFunctions.HagedornBootstrap.PolyakovLandau
import GaloisForLFunctions.HagedornBootstrap.LetterCounting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Scheme independence of the quartic coefficient, and the cumulant expansion

The effective action at fixed holonomy is not unique: adding a multiple of the Gauss-law
generator to the dilatation operator changes it by a change of variables, at leading order
`u₂ ↦ u₂ + γ u₁²`. In the two-mode action this shift trades bare quartic for cubic coupling,
`κ ↦ κ + m₂γ`, `b̃ ↦ b̃ + 2κγ + m₂γ²`, and leaves the physical quartic
`b = b̃ − κ²/m₂` invariant. A shift of the two-loop function by a multiple of `1 − z` is invisible
at the Hagedorn point. So the order of the transition does not depend on the scheme.

The perturbative expansion of `−S_eff = log Tr(x^D Û)` is a cumulant expansion. For a finite
ensemble with weights `w_i > 0` and energies `h_i` the generating function
`K(G) = log Σ w_i e^{−G h_i}` has `K'(0) = −⟨h⟩` and `K''(G)` equal to the tilted variance, which is
nonnegative: `K` is convex, and the second-order term is the connected average `⟨h²⟩ − ⟨h⟩²`.
-/

noncomputable section

open Real Finset

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### The shift of the heavy mode -/

/-- Shifting the heavy mode trades bare quartic for cubic coupling. -/
theorem twoModeAction_shift (m1 m2 κ bt γ x w : ℝ) :
    twoModeAction m1 m2 κ bt x (w + γ * x ^ 2) =
      twoModeAction m1 m2 (κ + m2 * γ) (bt + 2 * κ * γ + m2 * γ ^ 2) x w := by
  unfold twoModeAction; ring

/-- **Scheme independence:** the physical quartic `b̃ − κ²/m₂` is invariant under the shift. -/
theorem effectiveQuartic_shift_invariant {m2 : ℝ} (hm2 : m2 ≠ 0) (κ bt γ : ℝ) :
    (bt + 2 * κ * γ + m2 * γ ^ 2) - (κ + m2 * γ) ^ 2 / m2 = bt - κ ^ 2 / m2 := by
  field_simp; ring

/-- The two individual pieces change by equal and opposite amounts. -/
theorem shift_opposite_amounts {m2 : ℝ} (hm2 : m2 ≠ 0) (κ bt γ : ℝ) :
    (bt + 2 * κ * γ + m2 * γ ^ 2) - bt = (κ + m2 * γ) ^ 2 / m2 - κ ^ 2 / m2 := by
  field_simp; ring

/-- A shift of the two-loop function by a multiple of `1 − z` is invisible at the Hagedorn point. -/
theorem hagedorn_shift_invisible (q c : ℝ → ℝ) :
    q hagedornY + c hagedornY * (1 - singleLetterZ hagedornY) = q hagedornY := by
  rw [singleLetterZ_hagedornY]; ring

/-- The sign of `b` is scheme independent: it is negative in one scheme iff in every scheme. -/
theorem effectiveQuartic_neg_shift_iff {m2 : ℝ} (hm2 : 0 < m2) (κ bt γ : ℝ) :
    (bt + 2 * κ * γ + m2 * γ ^ 2) - (κ + m2 * γ) ^ 2 / m2 < 0 ↔ bt - κ ^ 2 / m2 < 0 := by
  rw [effectiveQuartic_shift_invariant hm2.ne']

/-! ### The cumulant expansion -/

variable {ι : Type*} (s : Finset ι) (w h : ι → ℝ)

/-- The finite partition function `Z(G) = Σ w_i e^{−G h_i}`. -/
def finiteZ (G : ℝ) : ℝ := ∑ i ∈ s, w i * Real.exp (-(G * h i))

/-- The tilted moments `Σ w_i h_iᵏ e^{−G h_i}`. -/
def finiteMoment (k : ℕ) (G : ℝ) : ℝ := ∑ i ∈ s, w i * h i ^ k * Real.exp (-(G * h i))

theorem hasDerivAt_finiteMoment (k : ℕ) (G : ℝ) :
    HasDerivAt (finiteMoment s w h k) (-(finiteMoment s w h (k + 1) G)) G := by
  unfold finiteMoment
  rw [show -(∑ i ∈ s, w i * h i ^ (k + 1) * Real.exp (-(G * h i))) =
    ∑ i ∈ s, w i * h i ^ k * (Real.exp (-(G * h i)) * -(h i)) by
      rw [← Finset.sum_neg_distrib]; congr 1; funext i; ring]
  apply HasDerivAt.fun_sum
  intro i _
  refine ((((hasDerivAt_id G).mul_const (h i)).neg).exp.const_mul (w i * h i ^ k)).congr_deriv ?_
  simp

theorem finiteZ_eq_moment_zero (G : ℝ) : finiteZ s w h G = finiteMoment s w h 0 G := by
  unfold finiteZ finiteMoment; simp

theorem finiteZ_pos (hw : ∀ i ∈ s, 0 < w i) (hs : s.Nonempty) (G : ℝ) : 0 < finiteZ s w h G :=
  Finset.sum_pos (fun i hi => mul_pos (hw i hi) (Real.exp_pos _)) hs

/-- **First cumulant:** `(log Z)'(G) = −⟨h⟩_G`. -/
theorem hasDerivAt_log_finiteZ (hw : ∀ i ∈ s, 0 < w i) (hs : s.Nonempty) (G : ℝ) :
    HasDerivAt (fun G => Real.log (finiteZ s w h G))
      (-(finiteMoment s w h 1 G / finiteZ s w h G)) G := by
  have hZ := hasDerivAt_finiteMoment s w h 0 G
  rw [← funext (finiteZ_eq_moment_zero s w h)] at hZ
  refine (hZ.log (finiteZ_pos s w h hw hs G).ne').congr_deriv ?_
  ring

/-- The tilted variance `⟨h²⟩⟨1⟩ − ⟨h⟩² ≥ 0` (Cauchy–Schwarz). -/
theorem moment_variance_nonneg (hw : ∀ i ∈ s, 0 < w i) (G : ℝ) :
    finiteMoment s w h 1 G ^ 2 ≤ finiteMoment s w h 2 G * finiteMoment s w h 0 G := by
  unfold finiteMoment
  have hsq : ∀ i ∈ s, Real.sqrt (w i * Real.exp (-(G * h i))) ^ 2 = w i * Real.exp (-(G * h i)) :=
    fun i hi => Real.sq_sqrt (mul_pos (hw i hi) (Real.exp_pos _)).le
  have e1 : ∑ i ∈ s, Real.sqrt (w i * Real.exp (-(G * h i))) * h i * Real.sqrt (w i * Real.exp (-(G * h i))) =
      ∑ i ∈ s, w i * h i ^ 1 * Real.exp (-(G * h i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hsq i hi
    calc Real.sqrt (w i * Real.exp (-(G * h i))) * h i * Real.sqrt (w i * Real.exp (-(G * h i)))
        = Real.sqrt (w i * Real.exp (-(G * h i))) ^ 2 * h i := by ring
      _ = w i * h i ^ 1 * Real.exp (-(G * h i)) := by rw [this]; ring
  have e2 : ∑ i ∈ s, (Real.sqrt (w i * Real.exp (-(G * h i))) * h i) ^ 2 =
      ∑ i ∈ s, w i * h i ^ 2 * Real.exp (-(G * h i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_pow, hsq i hi]; ring
  have e3 : ∑ i ∈ s, Real.sqrt (w i * Real.exp (-(G * h i))) ^ 2 =
      ∑ i ∈ s, w i * h i ^ 0 * Real.exp (-(G * h i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hsq i hi]; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (w i * Real.exp (-(G * h i))) * h i)
    (fun i => Real.sqrt (w i * Real.exp (-(G * h i))))
  rw [e1, e2, e3] at hcs
  linarith

/-- **Second cumulant:** `(log Z)''` is the tilted variance, hence `log Z` is convex. -/
theorem hasDerivAt_logZ_deriv (hw : ∀ i ∈ s, 0 < w i) (hs : s.Nonempty) (G : ℝ) :
    HasDerivAt (fun G => -(finiteMoment s w h 1 G / finiteZ s w h G))
      ((finiteMoment s w h 2 G * finiteZ s w h G - finiteMoment s w h 1 G ^ 2) /
        finiteZ s w h G ^ 2) G := by
  have hZ := hasDerivAt_finiteMoment s w h 0 G
  rw [← funext (finiteZ_eq_moment_zero s w h)] at hZ
  have h1 := hasDerivAt_finiteMoment s w h 1 G
  have hpos := (finiteZ_pos s w h hw hs G).ne'
  rw [finiteZ_eq_moment_zero] at hpos ⊢
  refine ((h1.div hZ (by rwa [finiteZ_eq_moment_zero])).neg).congr_deriv ?_
  rw [← finiteZ_eq_moment_zero]
  have hZ' : finiteZ s w h G ≠ 0 := by rwa [finiteZ_eq_moment_zero]
  field_simp
  ring

theorem logZ_second_derivative_nonneg (hw : ∀ i ∈ s, 0 < w i) (G : ℝ) :
    0 ≤ (finiteMoment s w h 2 G * finiteZ s w h G - finiteMoment s w h 1 G ^ 2) /
        finiteZ s w h G ^ 2 := by
  have := moment_variance_nonneg s w h hw G
  rw [← finiteZ_eq_moment_zero] at this
  apply div_nonneg _ (by positivity)
  linarith

end GaloisForLFunctions.HagedornBootstrap
