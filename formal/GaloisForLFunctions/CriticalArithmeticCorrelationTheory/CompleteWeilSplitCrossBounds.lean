import GaloisForLFunctions.CompletedArithmeticForms.SplitPrimeCrossBounds
import GaloisForLFunctions.CompletedArithmeticForms.WeightedConductorCrossBounds

/-!
# Complete Weil cross terms paid by separate mass reserves

The prime residual uses distinct prefix and terminal payments. The remaining
operators retain logarithmic coefficient weights; only the separated and upward
operators use their conductor-independent norm bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset
open scoped Classical RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  CriticalScaleArithmeticRigidity ArithmeticElectrostatics

private theorem identity_euclid_apply {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

private theorem two_abs_le_energy_payment {z F γ y : ℝ}
    (hF : 0 ≤ F) (hγ : 0 < γ) (hz : z ^ 2 ≤ F * y ^ 2) :
    2 * |z| ≤ F / γ + γ * y ^ 2 := by
  have he : (F / γ + γ * y ^ 2) ^ 2 =
      4 * F * y ^ 2 + (F / γ - γ * y ^ 2) ^ 2 := by
    field_simp [hγ.ne']
    ring
  have hs : (2 * |z|) ^ 2 ≤ (F / γ + γ * y ^ 2) ^ 2 := by
    rw [he]
    nlinarith only [hz, sq_abs z, sq_nonneg (F / γ - γ * y ^ 2)]
  have hr : 0 ≤ F / γ + γ * y ^ 2 := by positivity
  nlinarith only [hs, hr, abs_nonneg z]

private theorem four_signed_sq (x y z w : ℝ) :
    (x - y + z - w) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by
  nlinarith only [sq_nonneg (x + y), sq_nonneg (x - z), sq_nonneg (x + w),
    sq_nonneg (y + z), sq_nonneg (y - w), sq_nonneg (z + w)]

/-- The complete cross term has separate prime payments and a weighted nonprime payment. -/
theorem exists_completeWeil_cross_le_split_mass_reserves :
    ∃ C_pr C_np : ℝ, 0 < C_pr ∧ 0 < C_np ∧
      ∀ {R M N : ℕ} {c : ℝ}, 2 ≤ R → R ^ 6 ≤ N → M ≤ N →
        18 * (1 + Real.log R) ≤ Real.log N → 1 ≤ c → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R N)ᗮ →
      ∀ s t γ : ℝ, 0 < s → 0 < t → 0 < γ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) ^ 2 * primeAdjunctionMass R a) / (Real.log N * s) +
          C_pr * ((1 + Real.log R) * (∑ m ∈ Icc 1 R, a m ^ 2) +
            (1 + Real.log R) * terminalPacketCost R M N * primeAdjunctionMass R a) /
              (Real.log N * t) +
          C_np * ((c ^ 2 * (1 + Real.log R) / Real.log N +
            c ^ 4 * (1 + Real.log R) * ((1 + Real.log c) / Real.log N +
              (R : ℝ) ^ 2 * (Real.log N / N))) *
                (∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2) +
            (c ^ 4 + c ^ 2 * (1 + Real.log c)) *
              ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) / γ +
          s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
          t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + γ * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, hC_pr, hpr⟩ := exists_prime_cross_le_split_mass_reserves
  obtain ⟨C_near, hC_near, hnear⟩ := exists_overlap_sub_downward_sq_le_logarithmic_weight
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_up, hC_up, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep := 4 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep : 0 ≤ C_sep := by
    have := integral_tiltedUnitSpline_sq_pos
    dsimp only [C_sep]
    positivity
  let C_cen : ℝ := 32 * 288 ^ 2
  let C_np := 4 * (C_cen + C_near + C_sep ^ 2 + C_up ^ 2 + 1)
  have hC_cen : 0 ≤ C_cen := by dsimp only [C_cen]; positivity
  refine ⟨C_pr + 532 + 28, C_np, by positivity, by dsimp only [C_np]; positivity, ?_⟩
  intro R M N c hR hR6 hMN hlog hc1 hw1 hsize_near hsize_up a hu1 w hw s t γ hs ht hγ
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let H := 1 + Real.log R
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let B := terminalPacketCost R M N
  let X := c ^ 2 * H / Real.log N * G
  let Y := c ^ 4 * H * ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N)) * G
  let Z := c ^ 4 * ‖u‖ ^ 2
  let U := c ^ 2 * (1 + Real.log c) * ‖u‖ ^ 2
  let zc := ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫
  let zs := ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫
  let zn := ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
    downwardPrimeVector tiltedUnitSpline c N u, w⟫
  let zu := ⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log N := by linarith only [hlog, Real.log_natCast_nonneg R]
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hA : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG : 0 ≤ G := sum_nonneg fun m _ => by
    have := Real.log_natCast_nonneg m
    positivity
  have hB : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hu : u ∈ conductorSubspace R N := sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R N a
  have hw_one : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R) N hv)
  have huw : ⟪u, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw
  have hpole : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
    exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
  have hcen : zc ^ 2 ≤ C_cen * X * ‖w‖ ^ 2 := by
    have hh := fullWeilCenterMatrix_cross_sq_le_logarithmic_weight
      (completeWeilPoleShift tiltedUnitSpline c) hR hR6 hlog a hu1 hw_one
    have hp : completeWeilPoleShift tiltedUnitSpline c ^ 2 ≤ c ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hpole 2
    have hm := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ C_cen * H / Real.log N * G * ‖w‖ ^ 2 by positivity)
    rw [sq_abs] at hh
    calc
      zc ^ 2 ≤ C_cen * completeWeilPoleShift tiltedUnitSpline c ^ 2 * H /
          Real.log N * G * ‖w‖ ^ 2 := hh
      _ = completeWeilPoleShift tiltedUnitSpline c ^ 2 *
          (C_cen * H / Real.log N * G * ‖w‖ ^ 2) := by ring
      _ ≤ c ^ 2 * (C_cen * H / Real.log N * G * ‖w‖ ^ 2) := hm
      _ = _ := by dsimp only [X]; ring
  have hsep : zs ^ 2 ≤ C_sep ^ 2 * Z * ‖w‖ ^ 2 := by
    have hn := norm_separatedCrossErrorMatrix_le contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u
    have hh := (abs_real_inner_le_norm _ w).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg w))
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs] at hsq
    change zs ^ 2 ≤ _ at hsq
    exact hsq.trans_eq (by dsimp only [C_sep, Z]; ring)
  have hnear_sq : zn ^ 2 ≤ C_near * Y * ‖w‖ ^ 2 := by
    have hn := hnear hR hRR hlog hc1 hw1 hsize_near a
    have hh := pow_le_pow_left₀ (abs_nonneg _)
      (abs_real_inner_le_norm (Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
        downwardPrimeVector tiltedUnitSpline c N u) w) 2
    rw [sq_abs, mul_pow] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_right hn (sq_nonneg ‖w‖)).trans_eq
      (by dsimp only [Y, H, G]; ring))
  have hup_sq : zu ^ 2 ≤ C_up ^ 2 * U * ‖w‖ ^ 2 := by
    have hn := hup hR hlog hc1 hw1 hsize_up hu
    have hh := (abs_real_inner_le_norm _ w).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg w))
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rw [sq_abs] at hsq
    exact hsq.trans_eq (by
      dsimp only [U]
      simp only [mul_pow, Real.sq_sqrt (by linarith only [hlogc] : 0 ≤ 1 + Real.log c)]
      ring)
  have hnonprime : (zc - zs + zn - zu) ^ 2 ≤ C_np * (X + Y + Z + U) * ‖w‖ ^ 2 := by
    have hs := four_signed_sq zc zs zn zu
    have hsum := add_le_add (add_le_add (add_le_add hcen hsep) hnear_sq) hup_sq
    have hcoef : 4 * (C_cen * X + C_sep ^ 2 * Z + C_near * Y + C_up ^ 2 * U) ≤
        C_np * (X + Y + Z + U) := by
      have h1 := mul_nonneg (show 0 ≤ C_near + C_sep ^ 2 + C_up ^ 2 + 1 by positivity) hX
      have h2 := mul_nonneg (show 0 ≤ C_cen + C_sep ^ 2 + C_up ^ 2 + 1 by positivity) hY
      have h3 := mul_nonneg (show 0 ≤ C_cen + C_near + C_up ^ 2 + 1 by positivity) hZ
      have h4 := mul_nonneg (show 0 ≤ C_cen + C_near + C_sep ^ 2 + 1 by positivity) hU
      dsimp only [C_np]
      nlinarith only [h1, h2, h3, h4]
    have hc' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖w‖)
    nlinarith only [hs, hsum, hc']
  have hpay := two_abs_le_energy_payment
    (show 0 ≤ C_np * (X + Y + Z + U) by dsimp only [C_np]; positivity) hγ hnonprime
  have hprime := hpr hR hN2 hMN a hw s t hs ht
  have hprime' : 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      (C_pr + 532 + 28) * (H * A + H ^ 2 * E) / (Real.log N * s) +
      (C_pr + 532 + 28) * (H * A + H * B * E) / (Real.log N * t) +
      s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) := by
    have h1 : C_pr * H * A + 532 * H ^ 2 * E ≤ (C_pr + 532 + 28) * (H * A + H ^ 2 * E) := by
      nlinarith only [mul_nonneg hH hA, mul_nonneg (sq_nonneg H) hE,
        mul_nonneg hC_pr.le (mul_nonneg (sq_nonneg H) hE)]
    have h2 : C_pr * H * A + 28 * H * B * E ≤ (C_pr + 532 + 28) * (H * A + H * B * E) := by
      nlinarith only [mul_nonneg hH hA, mul_nonneg (mul_nonneg hH hB) hE,
        mul_nonneg hC_pr.le (mul_nonneg (mul_nonneg hH hB) hE)]
    have h1' := div_le_div_of_nonneg_right h1 (mul_pos hL hs).le
    have h2' := div_le_div_of_nonneg_right h2 (mul_pos hL ht).le
    change 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      (C_pr * H * A + 532 * H ^ 2 * E) / (Real.log N * s) +
      (C_pr * H * A + 28 * H * B * E) / (Real.log N * t) + _ + _ at hprime
    linarith only [hprime, h1', h2']
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one tiltedUnitSpline c hN2 hu1 hw_one
  change ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline c N) u, w⟫ = 0 at hpole0
  have hdecomp : ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ =
      -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ + (zc - zs + zn - zu) := by
    rw [completeWeilMatrix_eq_decomposition_at_every_overlap contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, identity_euclid_apply,
      fullWeilNonRatioMatrix_eq_downward_add_upward contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u,
      inner_add_left, inner_sub_left, real_inner_smul_left, huw, mul_zero, hpole0]
    dsimp only [zc, zs, zn, zu]
    rw [inner_sub_left]
    ring
  have habs := abs_add_le (-⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫) (zc - zs + zn - zu)
  rw [abs_neg, ← hdecomp] at habs
  have hcost : C_np * (X + Y + Z + U) / γ =
      C_np * ((c ^ 2 * H / Real.log N +
        c ^ 4 * H * ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N))) * G +
        (c ^ 4 + c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / γ := by
    dsimp only [X, Y, Z, U]
    ring
  rw [hcost] at hpay
  change _ ≤ (C_pr + 532 + 28) * (H * A + H ^ 2 * E) / (Real.log N * s) +
    (C_pr + 532 + 28) * (H * A + H * B * E) / (Real.log N * t) +
    C_np * ((c ^ 2 * H / Real.log N +
      c ^ 4 * H * ((1 + Real.log c) / Real.log N + (R : ℝ) ^ 2 * (Real.log N / N))) * G +
      (c ^ 4 + c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / γ +
    s * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
    t * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + γ * ‖w‖ ^ 2
  linarith only [habs, hprime', hpay]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_cross_le_split_mass_reserves
