import GaloisForLFunctions.TransThresholdPairCorrelation.TotientGridFormFactor
import GaloisForLFunctions.TransThresholdPairCorrelation.PositivityCannotReachTheThreeQuarterThreshold
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Fourier testing of periodized triangles

The positive sinc-square expansion of each grid periodization converts
Fourier testing into a sum of translates. The constant Fourier coefficients
of the totient mixture sum to its origin mass.
-/

open Real Set MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Physical lattice frequency of a cyclic grid's Fourier mode. -/
def gridFourierFrequency (L m : ℕ) (r : ℤ) : ℝ := (L : ℝ) / m * r

theorem gridPeriodicTriangle_expansion {m : ℕ} (hm : 0 < m) (L : ℕ) (α : ℝ) :
    (gridPeriodicTriangle L m α : ℂ) = ∑' r : ℤ,
      ((L : ℝ) * gridSincWeight m r : ℂ) *
        Complex.exp ((2 * π * gridFourierFrequency L m r * α : ℝ) * Complex.I) := by
  rw [gridPeriodicTriangle_fourier hm]
  apply tsum_congr
  intro r
  congr 1
  rw [fourier_coe_apply]
  congr 1
  unfold gridFourierFrequency
  push_cast
  ring

/-- Absolute integral summability permits Fourier transformation term by term. -/
theorem fourier_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {F : ι → ℝ → ℂ} (hF : ∀ i, Integrable (F i))
    (hS : Summable fun i => ∫ x : ℝ, ‖F i x‖) (ξ : ℝ) :
    𝓕 (fun x => ∑' i, F i x) ξ = ∑' i, 𝓕 (F i) ξ := by
  let e : ℝ → ℂ := fun x => Complex.exp ((-2 * π * x * ξ : ℝ) * Complex.I)
  have he (x : ℝ) : ‖e x‖ = 1 := by
    simp only [e, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, Real.exp_zero]
  have hi (i : ι) : Integrable (fun x => e x * F i x) :=
    (hF i).bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall fun x => (he x).le)
  have hsum : Summable fun i => ∫ x : ℝ, ‖e x * F i x‖ := by
    simpa only [norm_mul, he, one_mul] using hS
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  change (∫ x : ℝ, e x * ∑' i, F i x) = ∑' i, ∫ x : ℝ, e x * F i x
  simp_rw [← tsum_mul_left]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm hi hsum).symm

/-- Multiplication by a grid periodization becomes a positive sum of Fourier translates. -/
theorem fourier_mul_gridPeriodicTriangle {m : ℕ} (hm : 0 < m) (L : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f) (ξ : ℝ) :
    𝓕 (fun α => (gridPeriodicTriangle L m α : ℂ) * f α) ξ =
      ∑' r : ℤ, ((L : ℝ) * gridSincWeight m r : ℂ) *
        𝓕 f (ξ - gridFourierFrequency L m r) := by
  let F : ℤ → ℝ → ℂ := fun r α =>
    ((L : ℝ) * gridSincWeight m r : ℂ) *
      (Complex.exp ((2 * π * gridFourierFrequency L m r * α : ℝ) * Complex.I) * f α)
  have hi (r : ℤ) : Integrable (F r) :=
    (integrable_exp_mul hf (gridFourierFrequency L m r)).const_mul _
  have hnorm (r : ℤ) (α : ℝ) : ‖F r α‖ = (L : ℝ) * gridSincWeight m r * ‖f α‖ := by
    have hn : ‖Complex.exp ((2 * π * gridFourierFrequency L m r * α : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    simp only [F, norm_mul, hn, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) L), abs_of_nonneg (gridSincWeight_nonneg m r)]
  have hs : Summable fun r => ∫ α : ℝ, ‖F r α‖ := by
    simp_rw [hnorm, integral_const_mul]
    exact ((summable_gridSincWeight hm).mul_left (L : ℝ)).mul_right (∫ α : ℝ, ‖f α‖)
  have hpoint (α : ℝ) : (gridPeriodicTriangle L m α : ℂ) * f α = ∑' r, F r α := by
    rw [gridPeriodicTriangle_expansion hm, ← tsum_mul_right]
    apply tsum_congr
    intro r
    exact mul_assoc _ _ _
  rw [show (fun α => (gridPeriodicTriangle L m α : ℂ) * f α) = fun α => ∑' r, F r α
    from funext hpoint, fourier_tsum_of_summable_integral_norm hi hs ξ]
  apply tsum_congr
  intro r
  exact (fourierIntegral_const_mul _ _ ξ).trans
    (congrArg (fun z : ℂ => ((L : ℝ) * gridSincWeight m r : ℂ) * z)
      (fourierIntegral_exp_mul f (gridFourierFrequency L m r) ξ))

theorem integral_triangleFn_real {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, triangleFn a x) = a := by
  have h := fourier_triangleFn ha 0
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    sinc_zero, one_pow, mul_one] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem integral_triangle_gridPeriodicTriangle {m : ℕ} (hm : 0 < m) (L : ℕ)
    {lam : ℝ} (hlam : 0 < lam) :
    (∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L m α) =
      ∑' r : ℤ, ((L : ℝ) * gridSincWeight m r) *
        (lam * sinc (π * lam * (0 - gridFourierFrequency L m r)) ^ 2) := by
  have ht : Integrable (fun α : ℝ => (triangleFn lam α : ℂ)) := by
    have h : Integrable (triangleFn lam) := by
      simpa only [sub_zero] using integrable_triangleFn_sub hlam 0
    exact h.ofReal
  apply Complex.ofReal_injective
  calc
    ((∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L m α : ℝ) : ℂ) =
        𝓕 (fun α => (gridPeriodicTriangle L m α : ℂ) * (triangleFn lam α : ℂ)) 0 := by
      rw [Real.fourier_real_eq_integral_exp_smul]
      simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      filter_upwards with α
      push_cast
      ring
    _ = _ := by
      rw [fourier_mul_gridPeriodicTriangle hm L ht 0, Complex.ofReal_tsum]
      apply tsum_congr
      intro r
      rw [fourier_triangleFn hlam]
      push_cast
      ring

/-- A triangular test sees at least the constant mode of each cyclic grid. -/
theorem constant_mode_le_triangle_gridIntegral {m : ℕ} (hm : 0 < m) (L : ℕ)
    {lam : ℝ} (hlam : 0 < lam) :
    lam * ((L : ℝ) / m) ≤ ∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L m α := by
  let t : ℤ → ℝ := fun r => ((L : ℝ) * gridSincWeight m r) *
    (lam * sinc (π * lam * (0 - gridFourierFrequency L m r)) ^ 2)
  have ht (r : ℤ) : 0 ≤ t r := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg L) (gridSincWeight_nonneg m r))
      (mul_nonneg hlam.le (sq_nonneg _))
  have hs : Summable t := by
    apply Summable.of_nonneg_of_le ht
      (fun r => ?_) ((summable_gridSincWeight hm).mul_left ((L : ℝ) * lam))
    have hsin : sinc (π * lam * (0 - gridFourierFrequency L m r)) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
    have hprod := mul_le_mul_of_nonneg_left hsin
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg L) hlam.le) (gridSincWeight_nonneg m r))
    dsimp only [t]
    nlinarith only [hprod]
  have hzero : t 0 = lam * ((L : ℝ) / m) := by
    simp only [t, gridSincWeight_zero, gridFourierFrequency, Int.cast_zero,
      mul_zero, sub_self, sinc_zero, one_pow, mul_one]
    ring
  have h := hs.le_tsum 0 (fun r _ => ht r)
  rw [hzero] at h
  exact h.trans_eq (integral_triangle_gridPeriodicTriangle hm L hlam).symm

theorem triangleFn_one_mul {a : ℝ} (ha : 0 < a) (x : ℝ) :
    triangleFn 1 (a * x) = triangleFn (1 / a) x := by
  simp only [triangleFn, div_one, abs_mul, abs_of_pos ha]
  have he : |x| / (1 / a) = a * |x| := by field_simp
  rw [he]

/-- The removed central triangle has total integral one. -/
theorem integral_gridCentralTriangle {L : ℕ} (hL : 0 < L) :
    (∫ α : ℝ, (L : ℝ) * triangleFn 1 ((L : ℝ) * α)) = 1 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  simp_rw [triangleFn_one_mul hLR]
  rw [integral_const_mul, integral_triangleFn_real (one_div_pos.mpr hLR)]
  field_simp

theorem continuous_gridPeriodicTriangle {m : ℕ} (hm : 0 < m) (L : ℕ) :
    Continuous (gridPeriodicTriangle L m) := by
  rw [show gridPeriodicTriangle L m = fun α => (L : ℝ) *
      integerHatInterpolation (fun k : ℤ => if (m : ℤ) ∣ k then 1 else 0) ((L : ℝ) * α)
    from funext (gridPeriodicTriangle_eq_interpolation hm L)]
  exact continuous_const.mul ((continuous_integerHatInterpolation _).comp (continuous_const.mul continuous_id))

theorem integrable_triangle_mul_continuous {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : Continuous F) : Integrable (fun x => triangleFn a x * F x) := by
  apply ((continuous_triangleFn a).mul hF).integrable_of_hasCompactSupport
  refine HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) (fun x hx => ?_)
  have ht : triangleFn a x = 0 := by
    simpa only [zero_sub, zero_add, sub_zero] using
      (triangleFn_sub_eq_zero (b := 0) ha (by simpa only [zero_sub, zero_add] using hx))
  change triangleFn a x * F x = 0
  rw [ht, zero_mul]

/-- The one-sided Frobenius functional is the normalized full triangular test. -/
theorem frobeniusFormFactor_eq_triangle_integral {F : ℝ → ℝ} (hF : Continuous F)
    (hEven : ∀ x, F (-x) = F x) {lam : ℝ} (hlam : 0 < lam) :
    frobeniusFormFactor F lam = 1 / lam + (1 / lam) * ∫ α : ℝ, triangleFn lam α * F α := by
  have hc : Continuous (fun α => triangleFn lam α * F α) := (continuous_triangleFn lam).mul hF
  have hwhole : (∫ α : ℝ, triangleFn lam α * F α) =
      ∫ α in (-lam)..lam, triangleFn lam α * F α := by
    rw [intervalIntegral.integral_of_le (by linarith only [hlam]), ← integral_Icc_eq_integral_Ioc]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro α hα
    have hz : triangleFn lam α = 0 := by
      simpa only [sub_zero] using triangleFn_sub_eq_zero (b := 0) hlam
        (by simpa only [zero_sub, zero_add] using hα)
    rw [hz, zero_mul]
  have hleft : (∫ α in (-lam)..0, triangleFn lam α * F α) =
      ∫ α in (0 : ℝ)..lam, triangleFn lam α * F α := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := lam)
      (fun α => triangleFn lam α * F α)
    rw [neg_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro α hα
    simp only [triangleFn, abs_neg, hEven]
  have hright : (∫ α in (0 : ℝ)..lam, triangleFn lam α * F α) =
      (1 / lam) * ∫ α in (0 : ℝ)..lam, (lam - α) * F α := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro α hα
    rw [uIcc_of_le hlam.le] at hα
    have htri : triangleFn lam α = 1 - α / lam := by
      rw [triangleFn, abs_of_nonneg hα.1, max_eq_left]
      exact sub_nonneg.mpr ((div_le_one hlam).mpr hα.2)
    change triangleFn lam α * F α = (1 / lam) * ((lam - α) * F α)
    rw [htri]
    field_simp
  rw [hwhole, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-lam) 0) (hc.intervalIntegrable 0 lam), hleft, hright]
  unfold frobeniusFormFactor
  ring

theorem totientGridOriginMass_eq_weighted_modes {L : ℕ} (hL : 0 < L) :
    totientGridOriginMass L =
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * ((L : ℝ) / m)) +
        totientGridRemainder L * ((L : ℝ) / (L + 1)) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 L) :
      totientGridWeight L m * ((L : ℝ) / m) = ((Nat.totient m : ℝ) / m) / L := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
    unfold totientGridWeight
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  unfold totientGridOriginMass
  ring

theorem triangle_integral_totientGridFormFactor_lower {L : ℕ} (hL : 1 ≤ L)
    {lam : ℝ} (hlam : 0 < lam) :
    lam * totientGridOriginMass L - 1 ≤ ∫ α : ℝ, triangleFn lam α * totientGridFormFactor L α := by
  have hLpos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hi (m : ℕ) (hm : m ∈ Finset.Icc 1 L) :
      Integrable (fun α => totientGridWeight L m * (triangleFn lam α * gridPeriodicTriangle L m α)) :=
    (integrable_triangle_mul_continuous hlam
      (continuous_gridPeriodicTriangle (Finset.mem_Icc.mp hm).1 L)).const_mul _
  have hn : Integrable (fun α => totientGridRemainder L *
      (triangleFn lam α * gridPeriodicTriangle L (L + 1) α)) :=
    (integrable_triangle_mul_continuous hlam (continuous_gridPeriodicTriangle (Nat.succ_pos L) L)).const_mul _
  have hccont : Continuous (fun α : ℝ => (L : ℝ) * triangleFn 1 ((L : ℝ) * α)) :=
    continuous_const.mul ((continuous_triangleFn 1).comp (continuous_const.mul continuous_id))
  have hci := integrable_triangle_mul_continuous hlam hccont
  have hsi := integrable_finsetSum (Finset.Icc 1 L) hi
  have hfun : (fun α => triangleFn lam α * totientGridFormFactor L α) = fun α =>
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * (triangleFn lam α * gridPeriodicTriangle L m α)) +
        totientGridRemainder L * (triangleFn lam α * gridPeriodicTriangle L (L + 1) α) -
        triangleFn lam α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) := by
    funext α
    simp only [totientGridFormFactor_eq_mixture, mul_sub, mul_add, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]
  have hdecomp : (∫ α : ℝ, triangleFn lam α * totientGridFormFactor L α) =
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m *
        ∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L m α) +
      totientGridRemainder L * (∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L (L + 1) α) -
      ∫ α : ℝ, triangleFn lam α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) := by
    have hai : Integrable (fun α =>
        (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * (triangleFn lam α * gridPeriodicTriangle L m α)) +
          totientGridRemainder L * (triangleFn lam α * gridPeriodicTriangle L (L + 1) α)) := hsi.add hn
    rw [hfun, integral_sub hai hci, integral_add hsi hn,
      integral_finsetSum (Finset.Icc 1 L) hi]
    simp only [integral_const_mul]
  have hmain : lam * totientGridOriginMass L ≤
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m *
        ∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L m α) +
      totientGridRemainder L * (∫ α : ℝ, triangleFn lam α * gridPeriodicTriangle L (L + 1) α) := by
    have hs := Finset.sum_le_sum (s := Finset.Icc 1 L) (fun m hm =>
      mul_le_mul_of_nonneg_left
        (constant_mode_le_triangle_gridIntegral (Finset.mem_Icc.mp hm).1 L hlam)
        (totientGridWeight_nonneg L m))
    have hn := mul_le_mul_of_nonneg_left
      (constant_mode_le_triangle_gridIntegral (Nat.succ_pos L) L hlam)
      (totientGridRemainder_nonneg hL)
    rw [totientGridOriginMass_eq_weighted_modes hLpos]
    simpa only [mul_add, Finset.mul_sum, Nat.cast_add, Nat.cast_one, Nat.cast_succ, Nat.succ_eq_add_one,
      mul_assoc, mul_left_comm, mul_comm] using add_le_add hs hn
  have hcentral : (∫ α : ℝ, triangleFn lam α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α))) ≤ 1 := by
    have ht : Integrable (triangleFn (1 / (L : ℝ))) := by
      simpa only [sub_zero] using integrable_triangleFn_sub (one_div_pos.mpr hLR) 0
    have hcent : Integrable (fun α : ℝ => (L : ℝ) * triangleFn 1 ((L : ℝ) * α)) := by
      simpa only [triangleFn_one_mul hLR] using ht.const_mul (L : ℝ)
    calc
      _ ≤ ∫ α : ℝ, (L : ℝ) * triangleFn 1 ((L : ℝ) * α) := by
        apply integral_mono hci hcent
        intro α
        change triangleFn lam α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) ≤
          (L : ℝ) * triangleFn 1 ((L : ℝ) * α)
        have h := mul_le_mul_of_nonneg_right (triangleFn_le_one hlam α)
          (mul_nonneg hLR.le (triangleFn_nonneg 1 ((L : ℝ) * α)))
        simpa only [one_mul] using h
      _ = 1 := integral_gridCentralTriangle hLpos
  linarith only [hdecomp, hmain, hcentral]

/-- Every bandwidth sees at least the origin mass of the totient grid law. -/
theorem totientGridOriginMass_le_frobenius {L : ℕ} (hL : 1 ≤ L) {lam : ℝ} (hlam : 0 < lam) :
    totientGridOriginMass L ≤ frobeniusFormFactor (totientGridFormFactor L) lam := by
  rw [frobeniusFormFactor_eq_triangle_integral (continuous_totientGridFormFactor L)
    (totientGridFormFactor_neg L) hlam]
  have h := mul_le_mul_of_nonneg_left (triangle_integral_totientGridFormFactor_lower hL hlam)
    (one_div_nonneg.mpr hlam.le)
  have he : (1 / lam) * (lam * totientGridOriginMass L - 1) = totientGridOriginMass L - 1 / lam := by
    field_simp
  rw [he] at h
  linarith only [h]

end GaloisForLFunctions.TransThresholdPairCorrelation
