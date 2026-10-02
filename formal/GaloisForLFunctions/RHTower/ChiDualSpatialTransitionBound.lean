import GaloisForLFunctions.RHTower.ChiDualSpatialProfile
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Uniform bounds across the spatial stationary transitions

The literal logarithmic phase has curvature bounded away from zero on the
complete spatial block. A local second-derivative estimate controls every
Fourier frequency with the actual complex amplitude and its full variation.
Combining this with the complete Poisson reduction and actual chi normalization
gives one compact-uniform bound for the entire dual integer block at every
dyadic physical height, including both endpoint transition bands.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The actual spatial phase has nonzero curvature on the whole block,
including when its saddle is at an endpoint. This bound is uniform in every
real Fourier frequency and retains the entire amplitude variation. -/
theorem exists_chiDualSpatial_all_frequency_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ a b : ℝ, N / 5 - 1 / 2 ≤ a → b ≤ 6 * N / 25 + 1 / 2 → a ≤ b →
      ∀ w : ℝ,
      ‖∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))‖ ≤
          C * N ^ (s.re - 1) * Real.sqrt N := by
  obtain ⟨C, hC, hj⟩ := exists_chiDualSpatialSlowJets_bound c r
  refine ⟨96 * C, by positivity, ?_⟩
  intro s hs N hN t ht a b ha hb hab w
  have hN0 : 0 < N := by linarith
  have hlen : b - a ≤ N := by linarith
  let U := C * N ^ (s.re - 1)
  have hU : 0 ≤ U := mul_nonneg hC.le (Real.rpow_nonneg hN0.le _)
  have hxx (x : ℝ) (hx : x ∈ Icc a b) :
      N / 5 - 1 / 2 ≤ x ∧ x ≤ 6 * N / 25 + 1 / 2 :=
    ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hxdata (x : ℝ) (hx : x ∈ Icc a b) :
      0 < x ∧ x ≤ N / 4 ∧ x / N ∈ Icc (1 / 6 : ℝ) (1 / 3) := by
    obtain ⟨hx0, hxlo, hxhi, _, _⟩ := chiDual_spatial_block_ratio_bounds hN ht (hxx x hx)
    refine ⟨hx0, hxhi, ?_, ?_⟩
    · apply (le_div_iff₀ hN0).mpr
      linarith only [hxlo, hN0]
    · apply (div_le_iff₀ hN0).mpr
      linarith only [hxhi, hN0]
  have hdom : uIcc a b ⊆ Ioi (0 : ℝ) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (hxdata x hx).1
  have hA := (continuousOn_chiDualSpatialSlowJets s hN0).1.mono hdom
  have hA1 := (continuousOn_chiDualSpatialSlowJets s hN0).2.1.mono hdom
  have hamp (x : ℝ) (hx : x ∈ Icc a b) : ‖chiDualSpatialSlowAmplitude s N x‖ ≤ U :=
    (hj s hs N hN0 x (hxdata x hx).2.2).1
  have hderiv (x : ℝ) (hx : x ∈ Icc a b) : ‖chiDualSpatialSlowFirst s N x‖ ≤ U / N :=
    (hj s hs N hN0 x (hxdata x hx).2.2).2.1
  have hvar : (∫ x in a..b, ‖chiDualSpatialSlowFirst s N x‖) ≤ U := by
    have hi := intervalIntegral.integral_mono_on hab hA1.intervalIntegrable.norm
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => U / N) volume a b) hderiv
    have he : (∫ x in a..b, (U / N : ℝ)) = (U / N) * (b - a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [he] at hi
    calc
      _ ≤ (U / N) * (b - a) := hi
      _ ≤ (U / N) * N := mul_le_mul_of_nonneg_left hlen (div_nonneg hU hN0.le)
      _ = U := div_mul_cancel₀ _ hN0.ne'
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y => -chiDualSpatialPhase t w y) (-chiDualSpatialPhaseSlope t w x) x :=
    (hasDerivAt_chiDualSpatialPhase t w (hxdata x hx).1).neg
  have hd' (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y => -chiDualSpatialPhaseSlope t w y) (t / x ^ 2) x := by
    have h := (hasDerivAt_chiDualSpatialPhaseSlope t w (hxdata x hx).1).neg
    have he : -chiDualSpatialPhaseSecond t x = t / x ^ 2 := by
      dsimp only [chiDualSpatialPhaseSecond]
      ring
    exact he ▸ h
  have hc : ContinuousOn (fun x : ℝ => t / x ^ 2) (Icc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun x hx => pow_ne_zero 2 (hxdata x hx).1.ne')
  have hcurv (x : ℝ) (hx : x ∈ Icc a b) : 1 / N ≤ t / x ^ 2 := by
    obtain ⟨hx0, hxhi, _⟩ := hxdata x hx
    apply (div_le_div_iff₀ hN0 (sq_pos_of_pos hx0)).mpr
    have hxN : x ≤ N := by linarith only [hxhi, hN0]
    have hx2 : x ^ 2 ≤ N ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hxN) (add_nonneg hx0.le hN0.le)]
    nlinarith only [hx2, mul_le_mul_of_nonneg_right ht.1 hN0.le]
  have hv (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y => (starRingEnd ℂ) (chiDualSpatialSlowAmplitude s N y))
        ((starRingEnd ℂ) (chiDualSpatialSlowFirst s N x)) x :=
    (hasDerivAt_chiDualSpatialSlowAmplitude s hN0 (hxdata x hx).1).star
  have hvC : ContinuousOn (fun y => (starRingEnd ℂ) (chiDualSpatialSlowFirst s N y)) (Icc a b) := by
    rw [← uIcc_of_le hab]
    exact hA1.star
  have htest := secondDerivTestOn hab (by positivity : 0 < 1 / N) hd hd' hc hv hvC hcurv
  have he (x : ℝ) :
      (starRingEnd ℂ) (chiDualSpatialSlowAmplitude s N x) *
        Complex.exp (I * ((-chiDualSpatialPhase t w x : ℝ) : ℂ)) =
      (starRingEnd ℂ) (chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))) := by
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    congr 1
    push_cast
    ring
  have hi : (∫ x in a..b, (starRingEnd ℂ) (chiDualSpatialSlowAmplitude s N x) *
      Complex.exp (I * ((-chiDualSpatialPhase t w x : ℝ) : ℂ))) =
      (starRingEnd ℂ) (∫ x in a..b, chiDualSpatialSlowAmplitude s N x *
        Complex.exp (I * (chiDualSpatialPhase t w x : ℂ))) := by
    rw [← intervalIntegral.intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun x _ => he x)
  rw [hi, Complex.norm_conj] at htest
  simp only [Complex.norm_conj] at htest
  calc
    _ ≤ 32 * (‖chiDualSpatialSlowAmplitude s N b‖ + ‖chiDualSpatialSlowAmplitude s N a‖ +
        ∫ x in a..b, ‖chiDualSpatialSlowFirst s N x‖) / Real.sqrt (1 / N) := htest
    _ ≤ 32 * (U + U + U) / Real.sqrt (1 / N) := by
      gcongr
      · exact hamp b ⟨hab, le_rfl⟩
      · exact hamp a ⟨le_rfl, hab⟩
    _ = _ := by
      rw [one_div, Real.sqrt_inv, div_inv_eq_mul]
      dsimp only [U]
      ring


/-- The whole literal dual block has a bounded normalized magnitude at every
physical height, including both stationary transition bands. -/
theorem exists_chiDual_integer_block_row_bound (c : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ Metric.closedBall c r, ∀ N : ℝ, 50 ≤ N →
      ∀ t : ℝ, N ≤ t ∧ t ≤ 2 * N →
      ∀ A B : ℕ, N / 5 ≤ (A : ℝ) → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      ‖∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ≤
        C * ‖reflectedCompactGaussianRow s N t‖ := by
  obtain ⟨C₀, hC₀, herr⟩ := exists_chiDual_integer_block_single_mode_error c r
  obtain ⟨C₁, hC₁, hmode⟩ := exists_chiDualSpatial_all_frequency_bound c r
  refine ⟨C₀ + C₁, add_pos hC₀ hC₁, ?_⟩
  intro s hs N hN t ht A B hA hB hAB
  have hN0 : 0 < N := by linarith only [hN]
  have hab : (A : ℝ) - 1 / 2 ≤ (B : ℝ) + 1 / 2 := by
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    linarith only [hABR]
  let q : ℂ := zetaChi (s + (t : ℂ) * I)
  let S : ℂ := ∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t
  let J : ℂ := ∫ x in ((A : ℝ) - 1 / 2)..((B : ℝ) + 1 / 2), chiDualSpatialSlowAmplitude s N x *
    Complex.exp (I * (chiDualSpatialPhase t (-(2 * Real.pi)) x : ℂ))
  have h0 : ‖S - q * J‖ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ := herr s hs N hN t ht A B hA hB hAB
  have h1 : ‖J‖ ≤ C₁ * N ^ (s.re - 1) * Real.sqrt N :=
    hmode s hs N hN t ht ((A : ℝ) - 1 / 2) ((B : ℝ) + 1 / 2)
      (by linarith only [hA]) (by linarith only [hB]) hab (-(2 * Real.pi))
  have hsqrt : 1 ≤ Real.sqrt N := by
    nlinarith only [hN, Real.sq_sqrt hN0.le, Real.sqrt_nonneg N]
  have hp : N ^ (s.re - 1) * Real.sqrt N = N ^ (s.re - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0]
    congr 1
    ring
  have hr : N ^ (s.re - 1) * ‖q‖ * Real.sqrt N = ‖reflectedCompactGaussianRow s N t‖ := by
    rw [norm_reflectedCompactGaussianRow s hN0 t]
    calc
      _ = ‖q‖ * (N ^ (s.re - 1) * Real.sqrt N) := by ring
      _ = _ := by rw [hp]
  have hsmall : N ^ (s.re - 1) * ‖q‖ ≤ ‖reflectedCompactGaussianRow s N t‖ := by
    rw [← hr]
    exact le_mul_of_one_le_right (by positivity) hsqrt
  change ‖S‖ ≤ _
  calc
    _ = ‖(S - q * J) + q * J‖ := by rw [sub_add_cancel]
    _ ≤ ‖S - q * J‖ + ‖q * J‖ := norm_add_le _ _
    _ ≤ C₀ * N ^ (s.re - 1) * ‖q‖ + ‖q‖ * (C₁ * N ^ (s.re - 1) * Real.sqrt N) := by
      rw [norm_mul]
      exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ = C₀ * (N ^ (s.re - 1) * ‖q‖) + C₁ * ‖reflectedCompactGaussianRow s N t‖ := by
      rw [← hr]
      ring
    _ ≤ C₀ * ‖reflectedCompactGaussianRow s N t‖ + C₁ * ‖reflectedCompactGaussianRow s N t‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hsmall hC₀.le) le_rfl
    _ = _ := by ring

/-- A fixed compact disc has one bound for every complete dual integer block
and every dyadic physical height. No stationary endpoint is excluded. -/
theorem exists_chiDual_integer_block_disc_bound
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (N : ℝ) (2 * N),
      ∀ s ∈ Metric.closedBall c r,
      ∀ A B : ℕ, (N : ℝ) / 5 ≤ A → (B : ℝ) ≤ 6 * N / 25 → A ≤ B →
      ‖∑ n ∈ Finset.Icc A B, smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom s n t‖ ≤ C := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_chiDual_integer_block_row_bound c r
  obtain ⟨C₁, hC₁, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0 hc1
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  filter_upwards [hrow, eventually_ge_atTop (50 : ℕ)] with N hrow hN
  have hNR : (50 : ℝ) ≤ N := by exact_mod_cast hN
  intro t ht s hs A B hA hB hAB
  exact (hbound s hs N hNR t ht A B hA hB hAB).trans
    (mul_le_mul_of_nonneg_left (hrow t ht s hs).1 hC₀.le)

end RHTower
