import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketsHaveAnExactResidualEnergyDensity
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction
import GaloisForLFunctions.BezoutValuationIncidence.TheParityPairAtTheLeadingExponent

/-! An extreme Vaughan cutoff reads the finite Möbius harmonic sum in the residual Gram. -/
open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The unit cutoff has linear density one at every damping. -/
theorem pmPronicVaughanSmallDensity_one (ε : ℝ) :
    pmPronicVaughanSmallDensity ε 1 = 1 := by
  simp [pmPronicVaughanSmallDensity]

/-- Möbius inversion collapses the small-small piece at cutoffs `1,V≥n`. -/
theorem pmPronicVaughanPiece_smallSmall_one_of_le (ε : ℝ) {V n : ℕ}
    (hnV : n ≤ V) : pmPronicVaughanPiece ε 1 V n 2 = -(n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pmPronicVaughanPiece]
  have h0 : pmPronicVaughanPiece ε 1 V n 0 = n := by
    simp [pmPronicVaughanPiece, min_eq_left hn, pmPronicFloorWeight]
  have h3 : pmPronicVaughanPiece ε 1 V n 3 = 0 :=
    pmPronicVaughanPiece_large_eq_zero_of_cover ε (by omega)
  have h14 : pmPronicVaughanPiece ε 1 V n 1 +
      pmPronicVaughanPiece ε 1 V n 4 = pmBezoutInteriorPrefix ε n := by
    have h := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    rw [pmCenteredPrefix_eq_weighted_floor] at h
    change (∑ d ∈ Icc 1 (min V n), (moebius d : ℝ) * pmPronicFloorWeight ε n d) +
      (-(pmPowerDampedDivisorDensity ε).re * n -
        addDiff (pmActiveSawtoothComponent ε) n) = _
    rw [min_eq_right hnV]
    linarith only [h]
  have h := sum_pmPronicVaughanPiece ε 1 V n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change pmPronicVaughanPiece ε 1 V n 0 +
    (pmPronicVaughanPiece ε 1 V n 1 +
      (pmPronicVaughanPiece ε 1 V n 2 +
        (pmPronicVaughanPiece ε 1 V n 3 + pmPronicVaughanPiece ε 1 V n 4))) = _ at h
  linarith only [h, h0, h3, h14]

/-- At an extreme cutoff the centered convolution pieces are exactly proportional. -/
theorem pmPronicVaughanCentredPiece_large_one_eq {ε : ℝ} (hε : 0 < ε)
    {V n : ℕ} (hnV : n ≤ V) :
    pmPronicVaughanCentredPiece ε 1 V n 3 =
      ((pmPowerDampedDivisorDensity ε).re - 1) *
        pmPronicVaughanCentredPiece ε 1 V n 2 := by
  have hρ : (pmPowerDampedDivisorDensity ε).re ≠ 0 :=
    (pmPowerDampedDivisorDensity_re_pos hε).ne'
  have hZ : pmPronicPowerDensity ε * (pmPowerDampedDivisorDensity ε).re = 1 := by
    rw [pmPronicPowerDensity_eq_inv_density hε]
    exact inv_mul_cancel₀ hρ
  have hmean2 : pmPronicVaughanMean ε 1 V 2 =
      -pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε V := by
    change -pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε 1 *
      pmPronicVaughanSmallDensity ε V = _
    rw [pmPronicVaughanSmallDensity_one, mul_one]
  have h2 : pmPronicVaughanCentredPiece ε 1 V n 2 =
      -pmPronicPowerDensity ε *
        ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε V) * n := by
    rw [pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_smallSmall_one_of_le ε hnV, hmean2]
    calc -(n : ℝ) - (-pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε V) * n =
        -(pmPronicPowerDensity ε * (pmPowerDampedDivisorDensity ε).re) * n +
          pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε V * n := by
            rw [hZ]; ring
      _ = _ := by ring
  rw [h2, pmPronicVaughanCentredPiece,
    pmPronicVaughanPiece_large_eq_zero_of_cover ε (by omega),
    pmPronicVaughanMean_large_factorization hε, pmPronicVaughanSmallDensity_one]
  ring

/-- The extreme-cutoff centered Gram retains the same exact proportionality. -/
theorem pmPronicVaughanCentredGram_one_cross_eq {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    pmPronicVaughanCentredGram ε 1 T T 2 3 =
      ((pmPowerDampedDivisorDensity ε).re - 1) *
        pmPronicVaughanCentredGram ε 1 T T 2 2 := by
  unfold pmPronicVaughanCentredGram
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [pmPronicVaughanCentredPiece_large_one_eq hε (mem_Icc.mp hn).2]
  ring

/-- Error after removing the explicit smooth-power Gram term. -/
def pmPronicVaughanResidualGramError (ε : ℝ) (U V T : ℕ) (i j : Fin 5) : ℝ :=
  pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) -
    (subHalfZetaCoeff ε * (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
      (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b)) ^ 2 / (1 - 2 * ε) *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j

/-- A linear combination of two residual Gram errors reads the squared harmonic sum. -/
theorem pmPronicVaughanResidualGramError_harmonic_identity {ε : ℝ}
    (hε : 0 < ε) (T : ℕ) :
    pmPronicVaughanResidualGramError ε 1 T T 2 3 -
      ((pmPowerDampedDivisorDensity ε).re - 1) *
        pmPronicVaughanResidualGramError ε 1 T T 2 2 =
      (pmPowerDampedDivisorDensity ε).re *
        (subHalfZetaCoeff ε * (∑ b ∈ Icc 1 T, (moebius b : ℝ) / b)) ^ 2 /
          (1 - 2 * ε) := by
  simp only [pmPronicVaughanResidualGramError,
    pmPronicVaughanCentredGram_one_cross_eq hε]
  norm_num [pmPronicVaughanSmoothSigns, Fin.ext_iff]
  ring

/-- The harmonic invariant is strictly positive at every positive horizon below half damping. -/
theorem pmPronicVaughanResidualGramError_harmonic_pos {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {T : ℕ} (hT : 1 ≤ T) :
    0 < pmPronicVaughanResidualGramError ε 1 T T 2 3 -
      ((pmPowerDampedDivisorDensity ε).re - 1) *
        pmPronicVaughanResidualGramError ε 1 T T 2 2 := by
  rw [pmPronicVaughanResidualGramError_harmonic_identity hε]
  have hK := mul_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2]))
    (sum_moebius_div_ne_zero hT)
  exact div_pos (mul_pos (pmPowerDampedDivisorDensity_re_pos hε)
    (sq_pos_of_ne_zero hK)) (by linarith only [hε2])

/-- The harmonic invariant has a positive reciprocal-horizon floor cofinally often. -/
theorem frequent_pmPronicVaughanResidualGramError_harmonic_floor {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ T₀ : ℕ, ∃ T : ℕ, T₀ ≤ T ∧
      c ≤ (T : ℝ) * (pmPronicVaughanResidualGramError ε 1 T T 2 3 -
        ((pmPowerDampedDivisorDensity ε).re - 1) *
          pmPronicVaughanResidualGramError ε 1 T T 2 2) := by
  let k := (pmPowerDampedDivisorDensity ε).re * (subHalfZetaCoeff ε) ^ 2 / (1 - 2 * ε)
  have hk : 0 < k := div_pos (mul_pos (pmPowerDampedDivisorDensity_re_pos hε)
    (sq_pos_of_ne_zero (subHalfZetaCoeff_ne_zero hε (by linarith only [hε2]))))
      (by linarith only [hε2])
  obtain ⟨a, ha, hfloor⟩ := frequent_harmonic_energy_floor
  refine ⟨k * a, mul_pos hk ha, fun T₀ => ?_⟩
  obtain ⟨T, hT, hfloorT⟩ := hfloor T₀
  refine ⟨T, hT, ?_⟩
  have h := mul_le_mul_of_nonneg_left hfloorT hk.le
  rw [deningerHarmonicPartial_eq_sum_Icc] at h
  rw [pmPronicVaughanResidualGramError_harmonic_identity hε]
  dsimp only [k] at h
  convert h using 1 <;> ring

/-- The residual contrast cannot be little-o of the reciprocal horizon. -/
theorem not_tendsto_nat_mul_pmPronicVaughanResidualGramError_contrast_zero {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ Tendsto (fun T : ℕ => (T : ℝ) *
      (pmPronicVaughanResidualGramError ε 1 T T 2 3 -
        ((pmPowerDampedDivisorDensity ε).re - 1) *
          pmPronicVaughanResidualGramError ε 1 T T 2 2)) atTop (𝓝 0) := by
  intro hzero
  obtain ⟨c, hc, hfloor⟩ := frequent_pmPronicVaughanResidualGramError_harmonic_floor hε hε2
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hzero.eventually (gt_mem_nhds hc))
  obtain ⟨T, hT, hfloorT⟩ := hfloor T₀
  exact (not_lt_of_ge hfloorT) (hT₀ T hT)

/-- The two extreme-cutoff entries cannot both have reciprocal-horizon little-o errors. -/
theorem not_both_pmPronicVaughanResidualGramErrors_reciprocal_little_o {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ¬ (Tendsto (fun T : ℕ => (T : ℝ) * pmPronicVaughanResidualGramError ε 1 T T 2 3)
      atTop (𝓝 0) ∧
      Tendsto (fun T : ℕ => (T : ℝ) * pmPronicVaughanResidualGramError ε 1 T T 2 2)
        atTop (𝓝 0)) := by
  rintro ⟨h23, h22⟩
  apply not_tendsto_nat_mul_pmPronicVaughanResidualGramError_contrast_zero hε hε2
  have h := h23.sub (h22.const_mul ((pmPowerDampedDivisorDensity ε).re - 1))
  simp only [mul_zero, sub_zero] at h
  convert h using 1
  funext T
  ring

/-- Finite Abel inversion transfers harmonic Möbius power decay back to Mertens sums. -/
theorem abs_sum_moebiusReal_le_of_harmonic_power {η K : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hH : ∀ n : ℕ, 1 ≤ n → |deningerHarmonicPartial n| ≤ K * (n : ℝ) ^ (-η))
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, moebiusReal n| ≤
      (K * (2 + 1 / (1 - η))) * (N : ℝ) ^ (1 - η) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow1 : 1 ≤ (N : ℝ) ^ (1 - η) := Real.one_le_rpow hN1 (by linarith only [hη1])
  have hboundary : |(N : ℝ) * deningerHarmonicPartial N| ≤ K * (N : ℝ) ^ (1 - η) := by
    rw [abs_mul, abs_of_pos hN0]
    calc
      _ ≤ (N : ℝ) * (K * (N : ℝ) ^ (-η)) := mul_le_mul_of_nonneg_left (hH N hN) hN0.le
      _ = _ := by rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]; ring
  have hsum : |∑ n ∈ range N, deningerHarmonicPartial n| ≤
      K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) := by
    have hset : range (N + 1) = insert 0 (Icc 1 N) := by
      ext n
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    have hhead : (∑ n ∈ range N, |deningerHarmonicPartial n|) ≤
        ∑ n ∈ Icc 1 N, |deningerHarmonicPartial n| := by
      have h := sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ N))
        (fun n _ _ => abs_nonneg (deningerHarmonicPartial n))
      rw [hset, sum_insert (by simp)] at h
      have hzero : deningerHarmonicPartial 0 = 0 := by simp [deningerHarmonicPartial]
      simpa only [hzero, abs_zero, zero_add] using h
    calc
      _ ≤ ∑ n ∈ Icc 1 N, |deningerHarmonicPartial n| := (abs_sum_le_sum_abs _ _).trans hhead
      _ ≤ ∑ n ∈ Icc 1 N, K * (n : ℝ) ^ (-η) := sum_le_sum fun n hn => hH n (mem_Icc.mp hn).1
      _ = K * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-η) := (mul_sum _ _ _).symm
      _ ≤ K * ((N : ℝ) ^ (1 - η) / (1 - η) + 1) :=
        mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_rpow_neg_subcritical_le hη hη1 N) hK
      _ ≤ K * ((N : ℝ) ^ (1 - η) / (1 - η) + (N : ℝ) ^ (1 - η)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl ((N : ℝ) ^ (1 - η) / (1 - η))) hpow1) hK
      _ = _ := by ring
  have hM := sieveMertensM_eq_nat_mul_deningerHarmonicPartial_sub_sum N
  rw [Sieve.mertensM, sum_range_moebius_eq_sum_Icc_moebiusReal] at hM
  rw [hM]
  calc
    _ ≤ |(N : ℝ) * deningerHarmonicPartial N| + |∑ n ∈ range N, deningerHarmonicPartial n| := abs_sub _ _
    _ ≤ K * (N : ℝ) ^ (1 - η) + K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) :=
      add_le_add hboundary hsum
    _ = _ := by ring

/-- Any fixed power decay of the harmonic Möbius sums forces a fixed zero-free strip. -/
theorem zetaZeroAbscissa_lt_one_of_harmonic_power {η K : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hH : ∀ n : ℕ, 1 ≤ n → |deningerHarmonicPartial n| ≤ K * (n : ℝ) ^ (-η)) :
    zetaZeroAbscissa < 1 := by
  apply zetaZeroAbscissa_lt_one_iff_moebius_rate.mpr
  refine ⟨K * (2 + 1 / (1 - η)), 1 - η, ?_,
    by linarith only [hη1], by linarith only [hη], ?_⟩
  · have : 0 < 1 - η := by linarith only [hη1]
    positivity
  · exact fun n hn => abs_sum_moebiusReal_le_of_harmonic_power hη hη1 hK hH hn

/-- The two extreme-cutoff convolution errors cannot share an eventual power gain above one. -/
theorem not_both_pmPronicVaughanResidualGramErrors_power_gt_one
    {ε δ : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hδ : 1 < δ) :
    ¬ ∃ C : ℝ, ∀ᶠ T : ℕ in atTop,
      |pmPronicVaughanResidualGramError ε 1 T T 2 3| ≤ C / (T : ℝ) ^ δ ∧
      |pmPronicVaughanResidualGramError ε 1 T T 2 2| ≤ C / (T : ℝ) ^ δ := by
  rintro ⟨C, hbound⟩
  have hzero (i j : Fin 5)
      (hentry : ∀ᶠ T : ℕ in atTop,
        |pmPronicVaughanResidualGramError ε 1 T T i j| ≤ C / (T : ℝ) ^ δ) :
      Tendsto (fun T : ℕ => (T : ℝ) * pmPronicVaughanResidualGramError ε 1 T T i j)
        atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℕ => C / (T : ℝ) ^ (δ - 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop (sub_pos.mpr hδ)).comp tendsto_natCast_atTop_atTop)
    apply squeeze_zero_norm' ?_ hlim
    filter_upwards [hentry, eventually_ge_atTop 1] with T hT hT1
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hT0]
    refine (mul_le_mul_of_nonneg_left hT hT0.le).trans_eq ?_
    rw [Real.rpow_sub hT0, Real.rpow_one]
    field_simp [hT0.ne', (Real.rpow_pos_of_pos hT0 δ).ne'] <;> ring
  exact not_both_pmPronicVaughanResidualGramErrors_reciprocal_little_o hε hε2
    ⟨hzero 2 3 (hbound.mono fun _ h => h.1), hzero 2 2 (hbound.mono fun _ h => h.2)⟩

#print axioms abs_sum_moebiusReal_le_of_harmonic_power
#print axioms zetaZeroAbscissa_lt_one_of_harmonic_power
#print axioms frequent_pmPronicVaughanResidualGramError_harmonic_floor
#print axioms not_tendsto_nat_mul_pmPronicVaughanResidualGramError_contrast_zero
#print axioms not_both_pmPronicVaughanResidualGramErrors_reciprocal_little_o
#print axioms pmPronicVaughanSmallDensity_one
#print axioms pmPronicVaughanPiece_smallSmall_one_of_le
#print axioms pmPronicVaughanCentredPiece_large_one_eq
#print axioms pmPronicVaughanCentredGram_one_cross_eq
#print axioms pmPronicVaughanResidualGramError_harmonic_identity
#print axioms pmPronicVaughanResidualGramError_harmonic_pos
#print axioms not_both_pmPronicVaughanResidualGramErrors_power_gt_one
end GaloisForLFunctions.BezoutValuationIncidence
