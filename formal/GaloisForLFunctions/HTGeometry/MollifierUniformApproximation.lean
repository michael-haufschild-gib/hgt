import GaloisForLFunctions.HTGeometry.MollifierPositionCommutator

/-!
# Mollification approximates within the modulus of continuity

A unit-mass mollifier supported within `ε` of the origin averages a profile against shifts of size
at most `ε`.  Writing the difference as

`u(x) − (ρ * u)(x) = ∫ ρ(t) [u(x) − u(x−t)] dt`

and using that `ρ` is a probability density supported in `[−ε, ε]`, the difference is bounded by the
profile's modulus of continuity at scale `ε`.  So a profile with a uniform modulus is uniformly
approximated by its mollifications, at a rate set by that modulus alone.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- The mollification kernel against a continuous profile is integrable. -/
theorem integrable_mollifyKernel {ρ u : ℝ → ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (x : ℝ) : Integrable fun t => ρ t * u (x - t) := by
  have hcont : Continuous fun t : ℝ => ρ t * u (x - t) :=
    hρ.mul (hu.comp (continuous_const.sub continuous_id))
  exact hcont.integrable_of_hasCompactSupport hcρ.mul_right

/-- Averaging a constant against a unit-mass density returns the constant. -/
theorem integral_density_mul_const {ρ : ℝ → ℝ}
    (hmass : (∫ t, ρ t) = 1) (c : ℝ) : (∫ t, ρ t * c) = c := by
  rw [MeasureTheory.integral_mul_const, hmass, one_mul]

/-- **Mollification approximates within the modulus of continuity.**  A unit-mass density supported
in `[−ε, ε]` moves a profile by at most its modulus at scale `ε`, uniformly in the base point. -/
theorem abs_sub_mollify_le {ρ u : ℝ → ℝ} {ε M : ℝ} (hρ : Continuous ρ) (hu : Continuous u)
    (hcρ : HasCompactSupport ρ) (hnn : ∀ t, 0 ≤ ρ t) (hint : Integrable ρ)
    (hmass : (∫ t, ρ t) = 1) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hmod : ∀ y t : ℝ, |t| ≤ ε → |u y - u (y - t)| ≤ M) (x : ℝ) :
    |u x - mollify ρ u x| ≤ M := by
  have hik : Integrable fun t => ρ t * u (x - t) := integrable_mollifyKernel hρ hu hcρ x
  have hconst : Integrable fun t => ρ t * u x := hint.mul_const (u x)
  have hsplit : (∫ t, ρ t * (u x - u (x - t)))
      = (∫ t, ρ t * u x) - ∫ t, ρ t * u (x - t) := by
    rw [← MeasureTheory.integral_sub hconst hik]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * (u x - u (x - t)) = ρ t * u x - ρ t * u (x - t)
    ring
  have hrw : u x - mollify ρ u x = ∫ t, ρ t * (u x - u (x - t)) := by
    rw [hsplit, integral_density_mul_const hmass (u x)]
    rfl
  have hptwise : ∀ t : ℝ, ‖ρ t * (u x - u (x - t))‖ ≤ ρ t * M := by
    intro t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn t)]
    rcases le_or_gt |t| ε with ht | ht
    · exact mul_le_mul_of_nonneg_left (hmod x t ht) (hnn t)
    · rw [hsupp t ht]
      simp
  have hdom : Integrable fun t => ρ t * M := hint.mul_const M
  have hsub : Integrable fun t => ρ t * (u x - u (x - t)) := by
    refine (hconst.sub hik).congr (Filter.Eventually.of_forall fun t => ?_)
    show ρ t * u x - ρ t * u (x - t) = ρ t * (u x - u (x - t))
    ring
  have hbound : ‖∫ t, ρ t * (u x - u (x - t))‖ ≤ ∫ t, ρ t * M := by
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
    exact MeasureTheory.integral_mono hsub.norm hdom hptwise
  rw [hrw, ← Real.norm_eq_abs]
  refine le_trans hbound ?_
  rw [integral_density_mul_const hmass M]

/-! ## Weighted bounds survive mollification

Mollification is an average, so a bound holding uniformly across the averaging window passes to the
mollified profile with no loss.  The weight `√L` does not vary over the window, so it factors
straight through the average; the mismatch with the profile's own weight `√(L−s)` is carried by the
hypothesis, which is where the restriction to a terminal half-line lives.
-/

/-- **A weighted bound uniform on the window passes to the mollification.**  If `√L |f(L−s)| ≤ C`
for every shift in the mollifier's support, the same bound holds for the mollified profile. -/
theorem sqrt_mul_abs_mollify_le {ρ f : ℝ → ℝ} {ε L C : ℝ} (hρc : Continuous ρ)
    (hfc : Continuous f) (hcρ : HasCompactSupport ρ) (hnn : ∀ t, 0 ≤ ρ t)
    (hint : Integrable ρ) (hmass : (∫ t, ρ t) = 1) (hsupp : ∀ t, ε < |t| → ρ t = 0)
    (hbd : ∀ s, |s| ≤ ε → Real.sqrt L * |f (L - s)| ≤ C) :
    Real.sqrt L * |mollify ρ f L| ≤ C := by
  have hL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hik : Integrable fun s => ρ s * f (L - s) := integrable_mollifyKernel hρc hfc hcρ L
  have habs : Integrable fun s => ρ s * |f (L - s)| := by
    have hcont : Continuous fun s : ℝ => ρ s * |f (L - s)| :=
      hρc.mul ((hfc.comp (continuous_const.sub continuous_id)).abs)
    exact hcont.integrable_of_hasCompactSupport hcρ.mul_right
  have hstep1 : |mollify ρ f L| ≤ ∫ s, ρ s * |f (L - s)| := by
    unfold mollify
    have h1 : ‖∫ t, ρ t * f (L - t)‖ ≤ ∫ t, ‖ρ t * f (L - t)‖ :=
      norm_integral_le_integral_norm _
    have h2 : (∫ t, ‖ρ t * f (L - t)‖) ≤ ∫ s, ρ s * |f (L - s)| :=
      integral_mono hik.norm habs fun s =>
        le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn s)])
    rw [← Real.norm_eq_abs]
    exact le_trans h1 h2
  have hstep2 : Real.sqrt L * (∫ s, ρ s * |f (L - s)|) ≤ C := by
    rw [← MeasureTheory.integral_const_mul]
    have hmono : (∫ s, Real.sqrt L * (ρ s * |f (L - s)|)) ≤ ∫ s, ρ s * C := by
      refine integral_mono (habs.const_mul _) (hint.mul_const C) fun s => ?_
      rcases le_or_gt |s| ε with hs | hs
      · have := hbd s hs
        nlinarith [hnn s, this]
      · rw [hsupp s hs]
        simp
    rwa [MeasureTheory.integral_mul_const, hmass, one_mul] at hmono
  calc Real.sqrt L * |mollify ρ f L|
      ≤ Real.sqrt L * ∫ s, ρ s * |f (L - s)| := mul_le_mul_of_nonneg_left hstep1 hL
    _ ≤ C := hstep2

end GaloisForLFunctions.HTGeometry
