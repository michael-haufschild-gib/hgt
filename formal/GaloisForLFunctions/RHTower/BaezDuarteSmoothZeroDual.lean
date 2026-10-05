import GaloisForLFunctions.RHTower.ZetaZeroSmoothedPartialSums
import GaloisForLFunctions.RHTower.BaezDuarteDistanceLogLowerBound
import GaloisForLFunctions.RHTower.MobiusMertensMeanSquareExponentLaw
import GaloisForLFunctions.RHTower.MontgomerySpacedDetectionCore


/-!
# Smoothed zero duals for the Báez-Duarte distances

For a zero `ρ` of `ζ` and a smooth cutoff `ψ = Smooth1 ν ε` (`ν` a bump in `[1/2, 2]`), the
smoothed zero dual is `a_k = k^{−ρ} ψ(k/Y)`.  Its real part is a dual sequence for the discrete
Nyman–Beurling problem (`one_le_bdDistDiscrete_sq_mul_energy`); this file computes its energy and
its defects.

* `smooth1_antitoneOn`, `exists_abs_smooth1_sub_le`: `ψ = ∫_{y ≥ x} δ(y) dy/y` is nonincreasing
  and Lipschitz.
* `exists_norm_sum_natCast_cpow_neg_le`: on `Re z = 1`, `z ≠ 1`, the partial sums `Σ_{k ≤ j} k^{−z}`
  are bounded; `abs_sum_mul_le_of_antitone` is Abel's inequality.
* `exists_bdDualBilin_zeroSmoothDual_le`: for `Re ρ = Re ρ' = ½` the bilinear energy
  `Σ k(k+1) ΔA_k ΔA'_k` of `A = Re a_ρ`, `A' = Re a_ρ'` is the weighted sum of
  `Re(ρρ' k^{−(ρ+ρ')}) + Re(ρρ̄' k^{−(ρ+ρ̄')})` up to a bounded error.
* `exists_bdDualEnergy_re_zeroSmoothDual_le`: the energy is `≤ (|ρ|²/2) log Y + O(1)`
  (`ρ + ρ̄ = 1` gives the harmonic main term; `k^{−2ρ}` oscillates).
* `exists_bdDualBilin_zeroSmoothDual_le_of_ne`: distinct zeros in the upper half-plane give
  asymptotically orthogonal duals.
* `exists_norm_bdModDefect_zeroSmoothDual_le`: at a zero in the strip the defects
  `Σ_{m ∣ k} a_k − (1/m) Σ a_k` are `O(m^A Y^{−A})` for every `A`, by the smoothed partial-sum
  asymptotics `Σ n^{−ρ} ψ(n/X) = c X^{1−ρ} + O(X^{−A})`.
-/

open Complex MeasureTheory Set Filter Topology ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The smoothed cutoff as a tail integral -/

/-- `Smooth1 ν ε x = ∫_{y ≥ x} δ(y) dy/y` with `δ = DeltaSpike ν ε`. -/
theorem smooth1_eq_integral_tail {ν : ℝ → ℝ} {ε x : ℝ} (hx : 0 < x) :
    Smooth1 ν ε x = ∫ y in Ioi (0 : ℝ), DeltaSpike ν ε y * (if x ≤ y then 1 else 0) / y := by
  unfold Smooth1
  rw [MellinConvolutionSymmetric _ _ hx]
  unfold MellinConvolution
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 < y := hy
  congr 2
  have h1 : 0 < x / y := div_pos hx hy0
  show (if 0 < x / y ∧ x / y ≤ 1 then (1 : ℝ) else 0) = if x ≤ y then 1 else 0
  by_cases hxy : x ≤ y
  · rw [if_pos (And.intro h1 ((div_le_one hy0).mpr hxy)), if_pos hxy]
  · rw [if_neg (fun h => hxy ((div_le_one hy0).mp h.2)), if_neg hxy]

theorem integrableOn_deltaSpike_div {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun y : ℝ => DeltaSpike ν ε y / y) (Ioi 0) := by
  have hcont : ContinuousOn (fun y : ℝ => DeltaSpike ν ε y / y) (Icc (2 ^ (-ε)) (2 ^ ε)) := by
    refine ContinuousOn.div (DeltaSpikeContinuous hε
      (hν.1.of_le (by exact_mod_cast le_top))).continuousOn continuousOn_id ?_
    intro y hy
    exact (lt_of_lt_of_le (by positivity) hy.1).ne'
  have h1 : IntegrableOn (fun y : ℝ => DeltaSpike ν ε y / y) (Icc (2 ^ (-ε)) (2 ^ ε)) :=
    hcont.integrableOn_Icc
  refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) ≤ y := le_of_lt hy.1
  rw [DeltaSpikeSupport hε hy0 hν.2 hy.2, zero_div]

theorem integrableOn_deltaSpike_mul_ite_div {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) {ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    IntegrableOn (fun y : ℝ => DeltaSpike ν ε y * (if z ≤ y then 1 else 0) / y) (Ioi 0) := by
  refine (integrableOn_deltaSpike_div hν hε).mono' ?_ ?_
  · refine (((DeltaSpikeContinuous hε (hν.1.of_le (by exact_mod_cast le_top))).measurable.mul
      (Measurable.ite measurableSet_Ici measurable_const measurable_const)).div
      measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := hy
    have hds := DeltaSpikeNonNeg_of_NonNeg νpos hy0 hε
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    split_ifs
    · simp
    · simp only [mul_zero, zero_div]; positivity

/-- `Smooth1 ν ε` is nonincreasing on `(0, ∞)`. -/
theorem smooth1_antitoneOn {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    {ε : ℝ} (hε : 0 < ε) {x x' : ℝ} (hx : 0 < x) (hxx' : x ≤ x') :
    Smooth1 ν ε x' ≤ Smooth1 ν ε x := by
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx'
  rw [smooth1_eq_integral_tail hx, smooth1_eq_integral_tail hx']
  have hmeas := integrableOn_deltaSpike_mul_ite_div hν νpos hε
  refine setIntegral_mono_on (hmeas x') (hmeas x) measurableSet_Ioi fun y hy => ?_
  have hy0 : 0 < y := hy
  have hds := DeltaSpikeNonNeg_of_NonNeg νpos hy0 hε
  by_cases h' : x' ≤ y
  · rw [if_pos h', if_pos (le_trans hxx' h')]
  · rw [if_neg h']
    simp only [mul_zero, zero_div]
    split_ifs <;> positivity

/-- `Smooth1 ν ε` is Lipschitz on `(0, ∞)`. -/
theorem exists_abs_smooth1_sub_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x x' : ℝ, 0 < x → x ≤ x' →
      Smooth1 ν ε x - Smooth1 ν ε x' ≤ L * (x' - x) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hν.1.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 (by norm_num))
  set L : ℝ := M / ε * 2 ^ ε with hL
  refine ⟨L, by positivity, fun x x' hx hxx' => ?_⟩
  have hint := integrableOn_deltaSpike_div hν hε
  have hx' : 0 < x' := lt_of_lt_of_le hx hxx'
  -- the pointwise bound on `δ(y)/y`
  have hbound : ∀ y : ℝ, 0 < y → DeltaSpike ν ε y / y ≤ L := by
    intro y hy
    by_cases hyI : y ∈ Icc (2 ^ (-ε)) (2 ^ ε)
    · unfold DeltaSpike
      have hν1 : ν (y ^ (1 / ε)) ≤ M := by
        by_cases hz : ν (y ^ (1 / ε)) = 0
        · rw [hz]; exact hM0
        · have hmem := hν.2 hz
          exact (le_abs_self _).trans (by simpa using hM _ hmem)
      have hy2 : 2 ^ (-ε) ≤ y := hyI.1
      have hinv : y⁻¹ ≤ 2 ^ ε := by
        rw [inv_le_comm₀ hy (by positivity), ← Real.rpow_neg (by norm_num)]; exact hy2
      rw [hL, div_div, div_eq_mul_inv, mul_inv]
      calc ν (y ^ (1 / ε)) * (ε⁻¹ * y⁻¹) ≤ M * (ε⁻¹ * 2 ^ ε) := by
            gcongr
        _ = M / ε * 2 ^ ε := by ring
    · rw [DeltaSpikeSupport hε hy.le hν.2 hyI, zero_div]; positivity
  rw [smooth1_eq_integral_tail hx, smooth1_eq_integral_tail hx']
  have hmeas := integrableOn_deltaSpike_mul_ite_div hν νpos hε
  rw [← integral_sub (hmeas x) (hmeas x')]
  have hind : Integrable ((Ico x x').indicator (fun _ => L)) :=
    (integrable_indicator_iff measurableSet_Ico).mpr (continuous_const.integrableOn_Icc.mono_set
      Ico_subset_Icc_self)
  have hpt : ∀ y ∈ Ioi (0 : ℝ), DeltaSpike ν ε y * (if x ≤ y then 1 else 0) / y -
      DeltaSpike ν ε y * (if x' ≤ y then 1 else 0) / y ≤ (Ico x x').indicator (fun _ => L) y := by
    intro y hy
    have hy0 : 0 < y := hy
    have hds := DeltaSpikeNonNeg_of_NonNeg νpos hy0 hε
    by_cases h1 : x ≤ y
    · by_cases h2 : x' ≤ y
      · rw [if_pos h1, if_pos h2, sub_self]
        exact Set.indicator_nonneg (fun _ _ => by positivity) y
      · rw [if_pos h1, if_neg h2, Set.indicator_of_mem (show y ∈ Ico x x' from ⟨h1, not_le.mp h2⟩)]
        simpa using hbound y hy0
    · rw [if_neg h1, if_neg (fun h => h1 (le_trans hxx' h))]
      simp only [mul_zero, zero_div, sub_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) y
  calc ∫ y in Ioi (0 : ℝ), (DeltaSpike ν ε y * (if x ≤ y then 1 else 0) / y -
        DeltaSpike ν ε y * (if x' ≤ y then 1 else 0) / y)
      ≤ ∫ y in Ioi (0 : ℝ), (Ico x x').indicator (fun _ => L) y :=
        setIntegral_mono_on ((hmeas x).sub (hmeas x')) hind.integrableOn measurableSet_Ioi hpt
    _ ≤ ∫ y, (Ico x x').indicator (fun _ => L) y :=
        setIntegral_le_integral hind (Eventually.of_forall fun y =>
          Set.indicator_nonneg (fun _ _ => by positivity) y)
    _ = L * (x' - x) := by
        rw [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul,
          Real.volume_real_Ico_of_le hxx']
        ring

/-! ## Oscillatory sums on the line `Re z = 1` -/

/-- **Bounded partial sums on the line `Re z = 1`.**  For `Re z = 1`, `z ≠ 1`, the partial sums
`Σ_{k ≤ j} k^{−z}` are bounded uniformly in `j`: by Euler–Maclaurin they equal
`ζ(z) − j^{1−z}/(z − 1) + O(|z|)`. -/
theorem exists_norm_sum_natCast_cpow_neg_le {z : ℂ} (hzre : z.re = 1) (hz1 : z ≠ 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, ‖∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-z)‖ ≤ B := by
  have hz0 : 0 < z.re := by rw [hzre]; norm_num
  refine ⟨‖riemannZeta z‖ + 1 / ‖z - 1‖ + ‖z‖, by positivity, fun j => ?_⟩
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp; positivity
  have hsum := Sieve.riemannZeta_eq_sum_add_tail hz0 hz1 (N := j) hj
  have htail := Sieve.norm_integral_Ioi_fract_cpow_le hz0 (N := j) hj
  rw [hzre] at htail
  set T := ∫ t in Set.Ioi (j : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(z + 1)) with hT
  have hS : ∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-z) =
      ∑ k ∈ Finset.Icc 1 j, ((k : ℝ) : ℂ) ^ (-z) := by simp
  have hSeq : ∑ k ∈ Finset.Icc 1 j, (k : ℂ) ^ (-z) =
      riemannZeta z - ((j : ℝ) : ℂ) ^ (1 - z) / (z - 1) + z * T := by
    rw [hS]; linear_combination -hsum
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpow : ‖((j : ℝ) : ℂ) ^ (1 - z)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp [hzre]
  have hT1 : ‖T‖ ≤ 1 := by
    refine htail.trans ?_
    rw [div_one, Real.rpow_neg_one]
    exact inv_le_one_of_one_le₀ hj1
  rw [hSeq]
  calc ‖riemannZeta z - ((j : ℝ) : ℂ) ^ (1 - z) / (z - 1) + z * T‖
      ≤ ‖riemannZeta z‖ + ‖((j : ℝ) : ℂ) ^ (1 - z) / (z - 1)‖ + ‖z * T‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ ‖riemannZeta z‖ + 1 / ‖z - 1‖ + ‖z‖ := by
        rw [norm_div, hpow, norm_mul]
        gcongr
        calc ‖z‖ * ‖T‖ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hT1 (norm_nonneg _)
          _ = ‖z‖ := mul_one _

/-- **Abel's inequality.**  If the partial sums of `a` on `[1, j]` are bounded by `B` and `w` is
nonnegative and nonincreasing on `[1, K]`, then `|Σ_{k ≤ K} a_k w_k| ≤ B w_1`. -/
theorem abs_sum_mul_le_of_antitone {a w : ℕ → ℝ} {B : ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hB : ∀ j ≤ K, |∑ k ∈ Finset.Icc 1 j, a k| ≤ B)
    (hw0 : ∀ k, 1 ≤ k → k ≤ K → 0 ≤ w k) (hwanti : ∀ k, 1 ≤ k → k < K → w (k + 1) ≤ w k) :
    |∑ k ∈ Finset.Icc 1 K, a k * w k| ≤ B * w 1 := by
  -- summation by parts
  have hparts : ∀ K' : ℕ, 1 ≤ K' → ∑ k ∈ Finset.Icc 1 K', a k * w k =
      (∑ k ∈ Finset.Icc 1 K', a k) * w K' +
        ∑ k ∈ Finset.Icc 1 (K' - 1), (∑ i ∈ Finset.Icc 1 k, a i) * (w k - w (k + 1)) := by
    intro K' hK'
    induction K' with
    | zero => omega
    | succ K'' ih =>
      rcases Nat.eq_zero_or_pos K'' with h0 | hpos
      · subst h0; simp
      · rw [Finset.sum_Icc_succ_top (by omega), ih hpos, Finset.sum_Icc_succ_top (by omega)]
        have : K'' + 1 - 1 = (K'' - 1) + 1 := by omega
        rw [this, Finset.sum_Icc_succ_top (by omega), show K'' - 1 + 1 = K'' by omega]
        ring
  have htel : ∀ K' : ℕ, ∑ k ∈ Finset.Icc 1 K', (w k - w (k + 1)) = w 1 - w (K' + 1) := by
    intro K'
    induction K' with
    | zero => simp
    | succ K'' ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
  rw [hparts K hK]
  have h1 : |(∑ k ∈ Finset.Icc 1 K, a k) * w K| ≤ B * w K := by
    rw [abs_mul, abs_of_nonneg (hw0 K hK le_rfl)]
    exact mul_le_mul_of_nonneg_right (hB K le_rfl) (hw0 K hK le_rfl)
  have h2 : |∑ k ∈ Finset.Icc 1 (K - 1), (∑ i ∈ Finset.Icc 1 k, a i) * (w k - w (k + 1))| ≤
      B * (w 1 - w K) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ k ∈ Finset.Icc 1 (K - 1),
        |(∑ i ∈ Finset.Icc 1 k, a i) * (w k - w (k + 1))| ≤ B * (w k - w (k + 1)) := by
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have hd : 0 ≤ w k - w (k + 1) := sub_nonneg.mpr (hwanti k hk'.1 (by omega))
      rw [abs_mul, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right (hB k (by omega)) hd
    refine (Finset.sum_le_sum hle).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, htel, show K - 1 + 1 = K by omega]
  calc |(∑ k ∈ Finset.Icc 1 K, a k) * w K +
        ∑ k ∈ Finset.Icc 1 (K - 1), (∑ i ∈ Finset.Icc 1 k, a i) * (w k - w (k + 1))|
      ≤ B * w K + B * (w 1 - w K) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = B * w 1 := by ring

/-! ## Second-order differences of `k^{−ρ}` -/

/-- **Second-order Taylor bound.**  For `Re ρ > 0` and `k ≥ 1`,
`|k^{−ρ} − (k+1)^{−ρ} − ρ k^{−ρ−1}| ≤ |ρ| |ρ+1| k^{−Re ρ − 2}`. -/
theorem norm_natCast_cpow_neg_sub_succ_sub_le {ρ : ℂ} (hρ : 0 < ρ.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖(k : ℂ) ^ (-ρ) - ((k + 1 : ℕ) : ℂ) ^ (-ρ) - ρ * (k : ℂ) ^ (-ρ - 1)‖ ≤
      ‖ρ‖ * ‖ρ + 1‖ * (k : ℝ) ^ (-ρ.re - 2) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρ; simp at hρ
  -- the integral representation
  have hint := integral_cpow (a := (k : ℝ)) (b := (k : ℝ) + 1) (r := -ρ - 1)
    (Or.inr ⟨fun h => by
      have := congrArg Complex.re h; simp at this; linarith,
      by rw [Set.uIcc_of_le (by linarith)]; intro h; linarith [h.1]⟩)
  rw [show -ρ - 1 + 1 = -ρ by ring] at hint
  have hcast1 : (((k : ℝ) + 1 : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast1] at hint
  have hcastk : ((k : ℝ) : ℂ) = (k : ℂ) := by push_cast; rfl
  rw [hcastk] at hint
  have hid : (k : ℂ) ^ (-ρ) - ((k + 1 : ℕ) : ℂ) ^ (-ρ) - ρ * (k : ℂ) ^ (-ρ - 1) =
      ρ * ∫ x in (k : ℝ)..((k : ℝ) + 1), ((x : ℂ) ^ (-ρ - 1) - (k : ℂ) ^ (-ρ - 1)) := by
    rw [intervalIntegral.integral_sub, hint, intervalIntegral.integral_const]
    · simp only [add_sub_cancel_left, one_smul]
      field_simp
      ring
    · refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)] at hx
      have hx0 : 0 < x := by linarith [hx.1]
      exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hx0.ne'))
    · exact intervalIntegrable_const
  rw [hid, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  -- the pointwise bound
  have hρ1 : (ρ + 1).re ≠ 0 := by simp; linarith
  have hpt : ∀ x ∈ Set.uIoc (k : ℝ) ((k : ℝ) + 1),
      ‖(x : ℂ) ^ (-ρ - 1) - (k : ℂ) ^ (-ρ - 1)‖ ≤ ‖ρ + 1‖ * (k : ℝ) ^ (-ρ.re - 2) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have h := norm_cpow_neg_sub_cpow_neg_le hρ1 hk0 hx.1.le
    rw [show -(ρ + 1) = -ρ - 1 by ring, hcastk] at h
    have hre1 : (ρ + 1).re = ρ.re + 1 := by simp
    rw [hre1] at h
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hx1 : (k : ℝ) + 1 ≥ x := hx.2
    have hmono : ((k : ℝ) + 1) ^ (-(ρ.re + 1)) ≤ x ^ (-(ρ.re + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hx1 (by linarith)
    have hstep := rpow_neg_sub_rpow_neg_succ_le (u := (k : ℝ)) (p := ρ.re + 1) hkR (by linarith)
    rw [div_le_iff₀ (by linarith)]
    have : (k : ℝ) ^ (-(ρ.re + 1) - 1) = (k : ℝ) ^ (-ρ.re - 2) := by ring_nf
    rw [this] at hstep
    nlinarith [hmono, hstep]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [show |(k : ℝ) + 1 - k| = 1 by norm_num, mul_one] at this
  exact this


/-! ## Bilinear energies -/

/-- The bilinear weighted energy `Σ_{k ≤ K} k(k+1)(A_k − A_{k+1})(A'_k − A'_{k+1})`. -/
def bdDualBilin (A A' : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, ((n : ℝ) + 1) * ((n : ℝ) + 2) *
    ((A (n + 1) - A (n + 2)) * (A' (n + 1) - A' (n + 2)))

theorem bdDualEnergy_eq_bdDualBilin (A : ℕ → ℝ) (K : ℕ) :
    bdDualEnergy A K = bdDualBilin A A K := by
  unfold bdDualEnergy bdDualBilin
  exact Finset.sum_congr rfl fun n _ => by ring

theorem bdDualBilin_eq_sum_Icc (A A' : ℕ → ℝ) (K : ℕ) :
    bdDualBilin A A' K = ∑ k ∈ Finset.Icc 1 K,
      (k : ℝ) * ((k : ℝ) + 1) * ((A k - A (k + 1)) * (A' k - A' (k + 1))) := by
  unfold bdDualBilin
  rw [Finset.range_eq_Ico]
  have h := Finset.sum_Ico_add' (fun k : ℕ =>
    (k : ℝ) * ((k : ℝ) + 1) * ((A k - A (k + 1)) * (A' k - A' (k + 1)))) 0 K 1
  simp only [zero_add] at h
  rw [← Finset.Ico_add_one_right_eq_Icc, ← h]
  refine Finset.sum_congr rfl fun n _ => ?_
  push_cast
  ring_nf

theorem succ_mul_div_pow_succ_le {kk X : ℝ} (hk : 1 ≤ kk) (hX : 0 ≤ X) (n : ℕ) :
    (kk + 1) * (X / kk ^ (n + 1)) ≤ 2 * X / kk ^ n := by
  have hk0 : 0 < kk := by linarith
  rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hk0 _) (pow_pos hk0 _), pow_succ]
  have h := mul_le_mul_of_nonneg_left (show kk + 1 ≤ 2 * kk by linarith)
    (mul_nonneg hX (pow_nonneg hk0.le n))
  linarith

/-- The cross-term inequality behind the energy bounds. -/
theorem mul_add_mul_add_le_of_abs_le {kk s P Q P' Q' d x e x' e' : ℝ} (hk : 1 ≤ kk)
    (hs0 : 0 ≤ s) (hs : kk * s ^ 2 = 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hP' : 0 ≤ P') (hQ' : 0 ≤ Q')
    (hd : 0 ≤ d) (hx : |x| ≤ P * s / kk) (he : |e| ≤ Q * s / kk ^ 2 + s * d)
    (hx' : |x'| ≤ P' * s / kk) (he' : |e'| ≤ Q' * s / kk ^ 2 + s * d) :
    kk * (kk + 1) * ((x + e) * (x' + e')) ≤ kk * (kk + 1) * (x * x') +
      2 * (P * Q' + P' * Q + Q * Q') / kk ^ 2 + 2 * (P + P' + Q + Q') * d +
        (kk + 1) * d ^ 2 := by
  have hk0 : 0 < kk := by linarith
  have h1 : |x * e'| ≤ s ^ 2 * (P * Q' / kk ^ 3 + P * d / kk) := by
    rw [abs_mul]
    calc |x| * |e'| ≤ (P * s / kk) * (Q' * s / kk ^ 2 + s * d) :=
          mul_le_mul hx he' (abs_nonneg _) (by positivity)
      _ = s ^ 2 * (P * Q' / kk ^ 3 + P * d / kk) := by field_simp
  have h2 : |e * x'| ≤ s ^ 2 * (P' * Q / kk ^ 3 + P' * d / kk) := by
    rw [abs_mul]
    calc |e| * |x'| ≤ (Q * s / kk ^ 2 + s * d) * (P' * s / kk) :=
          mul_le_mul he hx' (abs_nonneg _) (by positivity)
      _ = s ^ 2 * (P' * Q / kk ^ 3 + P' * d / kk) := by field_simp
  have h3 : |e * e'| ≤ s ^ 2 * (Q * Q' / kk ^ 4 + (Q + Q') * d / kk ^ 2 + d ^ 2) := by
    rw [abs_mul]
    calc |e| * |e'| ≤ (Q * s / kk ^ 2 + s * d) * (Q' * s / kk ^ 2 + s * d) :=
          mul_le_mul he he' (abs_nonneg _) (by positivity)
      _ = s ^ 2 * (Q * Q' / kk ^ 4 + (Q + Q') * d / kk ^ 2 + d ^ 2) := by field_simp; ring
  set T : ℝ := (P * Q' + P' * Q) / kk ^ 3 + (P + P') * d / kk + Q * Q' / kk ^ 4 +
    (Q + Q') * d / kk ^ 2 + d ^ 2 with hT
  have hsum : (x + e) * (x' + e') - x * x' ≤ s ^ 2 * T := by
    have a1 := le_abs_self (x * e')
    have a2 := le_abs_self (e * x')
    have a3 := le_abs_self (e * e')
    have e0 : (x + e) * (x' + e') - x * x' = x * e' + e * x' + e * e' := by ring
    have e1 : s ^ 2 * T = s ^ 2 * (P * Q' / kk ^ 3 + P * d / kk) +
        s ^ 2 * (P' * Q / kk ^ 3 + P' * d / kk) +
        s ^ 2 * (Q * Q' / kk ^ 4 + (Q + Q') * d / kk ^ 2 + d ^ 2) := by rw [hT]; ring
    linarith
  have hw : 0 ≤ kk * (kk + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hw
  have hid : kk * (kk + 1) * (s ^ 2 * T) = (kk + 1) * T := by
    rw [show kk * (kk + 1) * (s ^ 2 * T) = (kk * s ^ 2) * ((kk + 1) * T) by ring, hs, one_mul]
  have t1 := succ_mul_div_pow_succ_le hk (X := P * Q' + P' * Q) (by positivity) 2
  have t2 := succ_mul_div_pow_succ_le hk (X := (P + P') * d) (by positivity) 0
  have t3 := succ_mul_div_pow_succ_le hk (X := Q * Q') (by positivity) 3
  have t4 := succ_mul_div_pow_succ_le hk (X := (Q + Q') * d) (by positivity) 1
  norm_num at t1 t2 t3 t4
  have t3' : 2 * (Q * Q') / kk ^ 3 ≤ 2 * (Q * Q') / kk ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hk (by norm_num))
  have t4' : 2 * ((Q + Q') * d) / kk ≤ 2 * ((Q + Q') * d) := div_le_self (by positivity) hk
  have eT : (kk + 1) * T = (kk + 1) * ((P * Q' + P' * Q) / kk ^ 3) +
      (kk + 1) * ((P + P') * d / kk) + (kk + 1) * (Q * Q' / kk ^ 4) +
      (kk + 1) * ((Q + Q') * d / kk ^ 2) + (kk + 1) * d ^ 2 := by rw [hT]; ring
  calc kk * (kk + 1) * ((x + e) * (x' + e'))
      = kk * (kk + 1) * (x * x') + kk * (kk + 1) * ((x + e) * (x' + e') - x * x') := by ring
    _ ≤ kk * (kk + 1) * (x * x') + (kk + 1) * T := by rw [← hid]; linarith
    _ ≤ _ := by
        rw [eT]
        have e2 : 2 * (P * Q' + P' * Q + Q * Q') / kk ^ 2 =
            2 * (P * Q' + P' * Q) / kk ^ 2 + 2 * (Q * Q') / kk ^ 2 := by ring
        have e3 : 2 * (P + P' + Q + Q') * d = 2 * ((P + P') * d) + 2 * ((Q + Q') * d) := by ring
        linarith

/-! ## The smoothed zero dual -/

/-- The smoothed zero dual `a_k = k^{−ρ} ψ(k/Y)`, `ψ = Smooth1 ν ε`. -/
def zeroSmoothDual (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) (k : ℕ) : ℂ :=
  zeroCoeff ρ k * (Smooth1 ν ε (k / Y) : ℂ)

theorem re_zeroSmoothDual (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    (zeroSmoothDual ν ε ρ Y k).re = ((k : ℂ) ^ (-ρ)).re * Smooth1 ν ε (k / Y) := by
  unfold zeroSmoothDual zeroCoeff
  rw [if_neg (by omega), Complex.mul_re]
  simp

theorem smooth1_eq_zero_of_three_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {x : ℝ} (hx : 3 ≤ x) : Smooth1 ν ε x = 0 := by
  obtain ⟨c, _, hc, h⟩ := Smooth1Properties_above hν.2
  refine h ε x ⟨hε0, hε1⟩ ?_
  rw [hc]
  have := Real.log_two_lt_d9
  nlinarith

theorem re_mul_re_eq (a b : ℂ) : a.re * b.re = ((a * b).re + (a * conj b).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **First-order decomposition of the increments.**  For `Re ρ = ½`, `k ≥ 1` and cutoff values
`0 ≤ w' ≤ w ≤ 1` at `k + 1` and `k`, `Re a_k − Re a_{k+1} = w Re(ρ k^{−ρ}/k) + e` with
`|e| ≤ |ρ||ρ+1| k^{−5/2} + k^{−1/2}(w − w')`. -/
theorem exists_re_zeroSmoothDual_sub_succ_eq (ν : ℝ → ℝ) (ε : ℝ) {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (Y : ℝ) {k : ℕ} (hk : 1 ≤ k) (hw0 : 0 ≤ Smooth1 ν ε ((k : ℝ) / Y))
    (hw1 : Smooth1 ν ε ((k : ℝ) / Y) ≤ 1)
    (hanti : Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) ≤ Smooth1 ν ε ((k : ℝ) / Y)) :
    ∃ e : ℝ, (zeroSmoothDual ν ε ρ Y k).re - (zeroSmoothDual ν ε ρ Y (k + 1)).re =
        Smooth1 ν ε ((k : ℝ) / Y) * (ρ * (k : ℂ) ^ (-ρ) / k).re + e ∧
      |e| ≤ ‖ρ‖ * ‖ρ + 1‖ * (Real.sqrt k)⁻¹ / (k : ℝ) ^ 2 +
        (Real.sqrt k)⁻¹ * (Smooth1 ν ε ((k : ℝ) / Y) - Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y)) := by
  have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkk0 : (0 : ℝ) < k := by linarith
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  set w := Smooth1 ν ε ((k : ℝ) / Y) with hw
  set w' := Smooth1 ν ε (((k + 1 : ℕ) : ℝ) / Y) with hw'
  set z : ℂ := (k : ℂ) ^ (-ρ) with hzdef
  set z' : ℂ := ((k + 1 : ℕ) : ℂ) ^ (-ρ) with hz'def
  set s : ℝ := (Real.sqrt k)⁻¹ with hsdef
  have hz'n : ‖z'‖ ≤ s := by
    rw [hz'def, norm_natCast_cpow_neg_of_re hre (by omega)]
    exact inv_anti₀ (Real.sqrt_pos.mpr hkk0) (Real.sqrt_le_sqrt (by push_cast; linarith))
  have hcpow1 : (k : ℂ) ^ (-ρ - 1) = z / (k : ℂ) := by
    rw [Complex.cpow_sub _ _ hkne, Complex.cpow_one]
  set R : ℂ := z - z' - ρ * (k : ℂ) ^ (-ρ - 1) with hRdef
  have hR : ‖R‖ ≤ ‖ρ‖ * ‖ρ + 1‖ * s / (k : ℝ) ^ 2 := by
    have h := norm_natCast_cpow_neg_sub_succ_sub_le (ρ := ρ) (by rw [hre]; norm_num) hk
    refine h.trans (le_of_eq ?_)
    rw [hre, show -(1 / 2 : ℝ) - 2 = -(1 / 2) + (-2 : ℤ) by norm_num,
      Real.rpow_add hkk0, rpow_neg_one_half_eq_inv_sqrt _ hkk0.le, Real.rpow_intCast,
      zpow_neg, zpow_two, hsdef]
    field_simp
  have hd0 : 0 ≤ w - w' := sub_nonneg.mpr hanti
  refine ⟨w * R.re + z'.re * (w - w'), ?_, ?_⟩
  · rw [re_zeroSmoothDual ν ε ρ Y hk, re_zeroSmoothDual ν ε ρ Y (by omega : 1 ≤ k + 1)]
    have hsplit : z - z' = ρ * z / k + R := by rw [hRdef, hcpow1]; ring
    have hre' : z.re - z'.re = (ρ * z / k).re + R.re := by
      rw [← Complex.sub_re, hsplit, Complex.add_re]
    rw [← hw, ← hw']
    linear_combination w * hre'
  · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hw0]
      calc w * |R.re| ≤ 1 * ‖R‖ :=
            mul_le_mul hw1 (Complex.abs_re_le_norm R) (abs_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact hR
    · rw [abs_mul, abs_of_nonneg hd0]
      exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm z').trans hz'n) hd0
/-! ## The defects of the smoothed zero dual -/

theorem zeroSmoothDual_eq_zero {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (ρ : ℂ) {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : 3 * Y ≤ k) :
    zeroSmoothDual ν ε ρ Y k = 0 := by
  unfold zeroSmoothDual
  rw [smooth1_eq_zero_of_three_le hν hε0 hε1 (by rw [le_div_iff₀ hY]; linarith)]
  simp

theorem zeroSmoothDual_zero (ν : ℝ → ℝ) (ε : ℝ) (ρ : ℂ) (Y : ℝ) : zeroSmoothDual ν ε ρ Y 0 = 0 := by
  simp [zeroSmoothDual, zeroCoeff]

theorem tsum_zeroSmoothDual_eq_sum {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (ρ : ℂ) {Y : ℝ} (hY : 0 < Y) {K : ℕ} (hYK : 3 * Y ≤ K) :
    ∑' n, zeroSmoothDual ν ε ρ Y n = ∑ k ∈ Finset.Icc 1 K, zeroSmoothDual ν ε ρ Y k := by
  refine tsum_eq_sum fun n hn => ?_
  simp only [Finset.mem_Icc, not_and_or, not_le] at hn
  rcases hn with h | h
  · have : n = 0 := by omega
    subst this; exact zeroSmoothDual_zero ν ε ρ Y
  · refine zeroSmoothDual_eq_zero hν hε0 hε1 ρ hY ?_
    have : (K : ℝ) + 1 ≤ n := by exact_mod_cast h
    linarith

theorem zeroSmoothDual_mul {ν : ℝ → ℝ} {ε : ℝ} (ρ : ℂ) {Y : ℝ} {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    zeroSmoothDual ν ε ρ Y (m * j) = (m : ℂ) ^ (-ρ) * zeroSmoothDual ν ε ρ (Y / m) j := by
  unfold zeroSmoothDual zeroCoeff
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp
  rw [if_neg (by positivity), if_neg (by omega)]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have harg : ((m * j : ℕ) : ℝ) / Y = (j : ℝ) / (Y / m) := by
    push_cast; field_simp
  rw [harg]
  push_cast
  rw [Complex.natCast_mul_natCast_cpow]
  ring

/-- Sums over multiples: `Σ_{m ∣ k ≤ K} a_k = m^{−ρ} Φ(Y/m)`. -/
theorem sum_filter_dvd_zeroSmoothDual {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) (ρ : ℂ) {Y : ℝ} (hY : 0 < Y) {K : ℕ} (hYK : 3 * Y ≤ K) {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ (Finset.Icc 1 K).filter (fun k => m ∣ k), zeroSmoothDual ν ε ρ Y k =
      (m : ℂ) ^ (-ρ) * ∑' j, zeroSmoothDual ν ε ρ (Y / m) j := by
  set F : ℕ → ℂ := fun k => if m ∣ k then zeroSmoothDual ν ε ρ Y k else 0 with hF
  have h1 : ∑ k ∈ (Finset.Icc 1 K).filter (fun k => m ∣ k), zeroSmoothDual ν ε ρ Y k =
      ∑' k, F k := by
    rw [Finset.sum_filter]
    refine (tsum_eq_sum fun n hn => ?_).symm
    show (if m ∣ n then zeroSmoothDual ν ε ρ Y n else 0) = 0
    split_ifs
    · simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with h | h
      · have : n = 0 := by omega
        subst this; exact zeroSmoothDual_zero ν ε ρ Y
      · refine zeroSmoothDual_eq_zero hν hε0 hε1 ρ hY ?_
        have : (K : ℝ) + 1 ≤ n := by exact_mod_cast h
        linarith
    · rfl
  have hinj : Function.Injective (fun j : ℕ => m * j) := fun a b h => by
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hsupp : Function.support F ⊆ Set.range (fun j : ℕ => m * j) := by
    intro k hk
    simp only [Function.mem_support, hF, ne_eq, ite_eq_right_iff, not_forall] at hk
    obtain ⟨⟨i, rfl⟩, _⟩ := hk
    exact ⟨i, rfl⟩
  rw [h1, ← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  simp only [hF, dvd_mul_right, if_true]
  exact zeroSmoothDual_mul ρ hm j

/-- **The defects of the smoothed zero dual.**  For a zero `ρ` in the strip and every `A > 0`,
`|Σ_{m ∣ k} a_k − (1/m) Σ a_k| ≤ 2C m^A Y^{−A}`: the main terms
`m^{−ρ} c (Y/m)^{1−ρ}` and `c Y^{1−ρ}/m` coincide. -/
theorem exists_norm_bdModDefect_zeroSmoothDual_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) {A : ℝ}
    (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ K : ℕ, 3 * Y ≤ K → ∀ m : ℕ, 1 ≤ m →
      ‖bdModDefect (zeroSmoothDual ν ε ρ Y) K m‖ ≤ 2 * C * (m : ℝ) ^ A * Y ^ (-A) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_tsum_smooth1_zeroCoeff_sub_le hν νpos mass_one hε0 hε1 hρ hρ0 hρ1 hA
  refine ⟨C, hC0, fun Y hY K hYK m hm => ?_⟩
  set c : ℂ := (1 - ρ)⁻¹ * mellin (fun x : ℝ => (ν x : ℂ)) (ε * (1 - ρ)) with hc
  set Φ : ℝ → ℂ := fun X => ∑' n, zeroSmoothDual ν ε ρ X n with hΦ
  have hΦE : ∀ X : ℝ, 0 < X → ‖Φ X - c * (X : ℂ) ^ (1 - ρ)‖ ≤ C * X ^ (-A) := by
    intro X hX
    have := hC X hX
    simpa [hΦ, zeroSmoothDual, hc, mul_assoc] using this
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hYm : 0 < Y / m := div_pos hY hm0
  -- the defect in terms of `Φ`
  have hall : ∑ k ∈ Finset.Icc 1 K, zeroSmoothDual ν ε ρ Y k = Φ Y :=
    (tsum_zeroSmoothDual_eq_sum hν hε0 hε1 ρ hY hYK).symm
  have hdef : bdModDefect (zeroSmoothDual ν ε ρ Y) K m =
      (m : ℂ) ^ (-ρ) * Φ (Y / m) - Φ Y / m := by
    unfold bdModDefect
    rw [sum_filter_dvd_zeroSmoothDual hν hε0 hε1 ρ hY hYK hm, hall]
    simp only [hΦ]
    ring
  -- the main terms cancel
  have hmain : (m : ℂ) ^ (-ρ) * (c * (((Y / m : ℝ)) : ℂ) ^ (1 - ρ)) -
      c * (Y : ℂ) ^ (1 - ρ) / m = 0 := by
    have hsplit : ((Y : ℝ) : ℂ) ^ (1 - ρ) =
        (((Y / m : ℝ)) : ℂ) ^ (1 - ρ) * ((m : ℝ) : ℂ) ^ (1 - ρ) := by
      rw [← Complex.mul_cpow_ofReal_nonneg hYm.le hm0.le]
      congr 1
      push_cast
      field_simp
    have hm1 : ((m : ℝ) : ℂ) ^ (1 - ρ) = (m : ℂ) * (m : ℂ) ^ (-ρ) := by
      rw [Complex.ofReal_natCast, sub_eq_add_neg, Complex.cpow_add _ _ hmC, Complex.cpow_one]
    rw [hsplit, hm1]
    field_simp
    ring
  rw [hdef]
  have hsplit2 : (m : ℂ) ^ (-ρ) * Φ (Y / m) - Φ Y / m =
      (m : ℂ) ^ (-ρ) * (Φ (Y / m) - c * (((Y / m : ℝ)) : ℂ) ^ (1 - ρ)) -
        (Φ Y - c * (Y : ℂ) ^ (1 - ρ)) / m := by
    linear_combination hmain
  rw [hsplit2]
  have hnm : ‖(m : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by linarith)
  have hE1 := hΦE (Y / m) hYm
  have hE2 := hΦE Y hY
  have hYmA : (Y / m) ^ (-A) = (m : ℝ) ^ A * Y ^ (-A) := by
    rw [Real.div_rpow hY.le hm0.le, Real.rpow_neg hm0.le, div_inv_eq_mul, mul_comm]
  have hmA : 1 ≤ (m : ℝ) ^ A := Real.one_le_rpow (by exact_mod_cast hm) hA.le
  have hYA : 0 ≤ Y ^ (-A) := Real.rpow_nonneg hY.le _
  calc ‖(m : ℂ) ^ (-ρ) * (Φ (Y / m) - c * (((Y / m : ℝ)) : ℂ) ^ (1 - ρ)) -
        (Φ Y - c * (Y : ℂ) ^ (1 - ρ)) / m‖
      ≤ ‖(m : ℂ) ^ (-ρ)‖ * ‖Φ (Y / m) - c * (((Y / m : ℝ)) : ℂ) ^ (1 - ρ)‖ +
          ‖Φ Y - c * (Y : ℂ) ^ (1 - ρ)‖ / m := by
        refine (norm_sub_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_div, Complex.norm_natCast]
    _ ≤ 1 * (C * ((m : ℝ) ^ A * Y ^ (-A))) + C * Y ^ (-A) / 1 := by
        gcongr
        · rw [← hYmA]; exact hE1
        · exact_mod_cast hm
    _ ≤ 2 * C * (m : ℝ) ^ A * Y ^ (-A) := by
        have : C * Y ^ (-A) ≤ C * ((m : ℝ) ^ A * Y ^ (-A)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          nlinarith
        nlinarith


/-! ## The bilinear energy of two smoothed zero duals -/

/-- **The bilinear energy of two smoothed zero duals.**  For `Re ρ = Re ρ' = ½` there is `K₂`
with `Σ_{k ≤ K} k(k+1) ΔA_k ΔA'_k ≤ Σ_k (ψ_k²/2)(1 + 1/k)(Re(ρρ' k^{−(ρ+ρ')}) +
Re(ρρ̄' k^{−(ρ+ρ̄')})) + K₂` for all `Y ≥ 1`, where `A = Re a_ρ`, `A' = Re a_ρ'`,
`ψ_k = ψ(k/Y)`. -/
theorem exists_bdDualBilin_zeroSmoothDual_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ ρ' : ℂ} (hre : ρ.re = 1 / 2) (hre' : ρ'.re = 1 / 2) :
    ∃ K₂ : ℝ, ∀ Y : ℝ, 1 ≤ Y → ∀ K : ℕ,
      bdDualBilin (fun k => (zeroSmoothDual ν ε ρ Y k).re)
          (fun k => (zeroSmoothDual ν ε ρ' Y k).re) K ≤
        ∑ k ∈ Finset.Icc 1 K, Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) *
          ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
            (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) + K₂ := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_smooth1_sub_le hν νpos hε0
  set P : ℝ := ‖ρ‖ with hP
  set Q : ℝ := ‖ρ‖ * ‖ρ + 1‖ with hQ
  set P' : ℝ := ‖ρ'‖ with hP'
  set Q' : ℝ := ‖ρ'‖ * ‖ρ' + 1‖ with hQ'
  set C₁ : ℝ := 2 * (P * Q' + P' * Q + Q * Q') with hC₁
  set C₂ : ℝ := 2 * (P + P' + Q + Q') + 4 * L with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨2 * C₁ + C₂, fun Y hY K => ?_⟩
  have hY0 : 0 < Y := by linarith
  set w : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) with hw
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  have hwnn : ∀ k, 1 ≤ k → 0 ≤ w k := fun k hk =>
    Smooth1Nonneg νpos (div_pos (by exact_mod_cast hk) hY0) hε0
  have hwle : ∀ k, 1 ≤ k → w k ≤ 1 := fun k hk =>
    Smooth1LeOne νpos mass_one hε0 (div_pos (by exact_mod_cast hk) hY0)
  have hwanti : ∀ k, 1 ≤ k → w (k + 1) ≤ w k := fun k hk =>
    smooth1_antitoneOn hν νpos hε0 (div_pos (by exact_mod_cast hk) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hY0.le)
  have hwzero : ∀ k, M < k → w k = 0 := by
    intro k hk
    have h3 : 3 * Y < k := (Nat.floor_lt (by positivity)).mp hk
    exact smooth1_eq_zero_of_three_le hν hε0 hε1 (by rw [le_div_iff₀ hY0]; linarith)
  have hwlip : ∀ k, 1 ≤ k → w k - w (k + 1) ≤ L / Y := by
    intro k hk
    have := hL ((k : ℝ) / Y) (((k + 1 : ℕ) : ℝ) / Y) (div_pos (by exact_mod_cast hk) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hY0.le)
    refine this.trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  -- the term bound
  have hterm : ∀ k ∈ Finset.Icc 1 K, (k : ℝ) * ((k : ℝ) + 1) *
      (((zeroSmoothDual ν ε ρ Y k).re - (zeroSmoothDual ν ε ρ Y (k + 1)).re) *
        ((zeroSmoothDual ν ε ρ' Y k).re - (zeroSmoothDual ν ε ρ' Y (k + 1)).re)) ≤
      w k ^ 2 / 2 * (1 + 1 / (k : ℝ)) * ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
        (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) + C₁ / (k : ℝ) ^ 2 +
        C₂ * (w k - w (k + 1)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkk0 : (0 : ℝ) < k := by linarith
    have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    obtain ⟨e, he1, he2⟩ := exists_re_zeroSmoothDual_sub_succ_eq ν ε hre Y hk1 (hwnn k hk1)
      (hwle k hk1) (hwanti k hk1)
    obtain ⟨e', he1', he2'⟩ := exists_re_zeroSmoothDual_sub_succ_eq ν ε hre' Y hk1
      (hwnn k hk1) (hwle k hk1) (hwanti k hk1)
    set s : ℝ := (Real.sqrt k)⁻¹ with hsdef
    have hs0 : 0 ≤ s := by positivity
    have hs : (k : ℝ) * s ^ 2 = 1 := by
      rw [hsdef, inv_pow, Real.sq_sqrt hkk0.le]; field_simp
    set z : ℂ := (k : ℂ) ^ (-ρ) with hzdef
    set z' : ℂ := (k : ℂ) ^ (-ρ') with hz'def
    have hzn : ‖z‖ = s := norm_natCast_cpow_neg_of_re hre hk1
    have hz'n : ‖z'‖ = s := norm_natCast_cpow_neg_of_re hre' hk1
    set v : ℂ := ρ * z / k with hvdef
    set v' : ℂ := ρ' * z' / k with hv'def
    set d : ℝ := w k - w (k + 1) with hddef
    have hd0 : 0 ≤ d := sub_nonneg.mpr (hwanti k hk1)
    have hxb : ∀ (u : ℂ) (p : ℝ), ‖u‖ = p * s / k → |w k * u.re| ≤ p * s / k := by
      intro u p hu
      rw [abs_mul, abs_of_nonneg (hwnn k hk1), ← hu]
      calc w k * |u.re| ≤ 1 * ‖u‖ :=
            mul_le_mul (hwle k hk1) (Complex.abs_re_le_norm u) (abs_nonneg _) zero_le_one
        _ = ‖u‖ := one_mul _
    have hx := hxb v P (by rw [hvdef, norm_div, norm_mul, hzn, Complex.norm_natCast])
    have hx' := hxb v' P' (by rw [hv'def, norm_div, norm_mul, hz'n, Complex.norm_natCast])
    have hmain := mul_add_mul_add_le_of_abs_le hkk hs0 hs (norm_nonneg ρ) (by positivity)
      (norm_nonneg ρ') (by positivity) hd0 hx he2 hx' he2'
    have hA : (zeroSmoothDual ν ε ρ Y k).re - (zeroSmoothDual ν ε ρ Y (k + 1)).re =
        w k * v.re + e := he1
    have hA' : (zeroSmoothDual ν ε ρ' Y k).re - (zeroSmoothDual ν ε ρ' Y (k + 1)).re =
        w k * v'.re + e' := he1'
    rw [hA, hA']
    -- the main product
    have hzz : z * z' = (k : ℂ) ^ (-(ρ + ρ')) := by
      rw [hzdef, hz'def, ← Complex.cpow_add _ _ hkne, neg_add]
    have hzc : z * conj z' = (k : ℂ) ^ (-(ρ + conj ρ')) := by
      rw [hz'def, ← natCast_cpow_conj, hzdef, ← Complex.cpow_add _ _ hkne, map_neg, neg_add]
    have hk2 : ((k : ℂ) ^ 2) = (((k : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have hvv : (v * v').re = (ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re / (k : ℝ) ^ 2 := by
      rw [show v * v' = ρ * ρ' * (z * z') / (k : ℂ) ^ 2 by rw [hvdef, hv'def]; ring, hzz, hk2,
        Complex.div_ofReal_re]
    have hvc : (v * conj v').re = (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re / (k : ℝ) ^ 2 := by
      have : conj v' = conj ρ' * conj z' / k := by
        rw [hv'def, map_div₀, map_mul, Complex.conj_natCast]
      rw [show v * conj v' = ρ * conj ρ' * (z * conj z') / (k : ℂ) ^ 2 by rw [this, hvdef]; ring,
        hzc, hk2, Complex.div_ofReal_re]
    have hxx : (k : ℝ) * ((k : ℝ) + 1) * (w k * v.re * (w k * v'.re)) =
        w k ^ 2 / 2 * (1 + 1 / (k : ℝ)) * ((ρ * ρ' * (k : ℂ) ^ (-(ρ + ρ'))).re +
          (ρ * conj ρ' * (k : ℂ) ^ (-(ρ + conj ρ'))).re) := by
      rw [show w k * v.re * (w k * v'.re) = w k ^ 2 * (v.re * v'.re) by ring, re_mul_re_eq, hvv,
        hvc]
      field_simp
    have hd2 : ((k : ℝ) + 1) * d ^ 2 ≤ 4 * L * d := by
      by_cases hkM : k ≤ M
      · have hk3 : (k : ℝ) ≤ 3 * Y := (Nat.le_floor_iff (by positivity)).mp hkM
        have hdl : d ≤ L / Y := hwlip k hk1
        have hkd : ((k : ℝ) + 1) * d ≤ 4 * L := by
          calc ((k : ℝ) + 1) * d ≤ (4 * Y) * (L / Y) :=
                mul_le_mul (by linarith only [hk3, hY]) hdl hd0 (by positivity)
            _ = 4 * L := by field_simp
        calc ((k : ℝ) + 1) * d ^ 2 = (((k : ℝ) + 1) * d) * d := by ring
          _ ≤ (4 * L) * d := mul_le_mul_of_nonneg_right hkd hd0
      · rw [hddef, hwzero k (by omega), hwzero (k + 1) (by omega)]; simp
    have hC : 2 * (P * Q' + P' * Q + Q * Q') / (k : ℝ) ^ 2 = C₁ / (k : ℝ) ^ 2 := by rw [hC₁]
    have hC' : 2 * (P + P' + Q + Q') * d + 4 * L * d = C₂ * d := by rw [hC₂]; ring
    rw [hxx] at hmain
    linarith only [hmain, hd2, hC, hC']
  rw [bdDualBilin_eq_sum_Icc]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hS3 : ∑ k ∈ Finset.Icc 1 K, C₁ / (k : ℝ) ^ 2 ≤ 2 * C₁ := by
    calc ∑ k ∈ Finset.Icc 1 K, C₁ / (k : ℝ) ^ 2 =
          C₁ * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ C₁ * 2 := mul_le_mul_of_nonneg_left (by simpa only [one_div] using sum_Icc_inv_sq_le_two K) hC₁0
      _ = 2 * C₁ := by ring
  have hS4 : ∑ k ∈ Finset.Icc 1 K, C₂ * (w k - w (k + 1)) ≤ C₂ := by
    have htel : ∀ K' : ℕ, ∑ k ∈ Finset.Icc 1 K', (w k - w (k + 1)) = w 1 - w (K' + 1) := by
      intro K'
      induction K' with
      | zero => simp
      | succ K'' ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
    rw [← Finset.mul_sum, htel]
    have h1 := hwle 1 le_rfl
    have h2 := hwnn (K + 1) (by omega)
    calc C₂ * (w 1 - w (K + 1)) ≤ C₂ * 1 := mul_le_mul_of_nonneg_left (by linarith) hC₂0
      _ = C₂ := mul_one _
  linarith only [hS3, hS4]

/-! ## Weighted main and oscillatory sums -/

theorem smooth1_div_mem_Icc {ν : ℝ → ℝ} (νpos : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε) {Y : ℝ} (hY : 0 < Y) {k : ℕ}
    (hk : 1 ≤ k) : 0 ≤ Smooth1 ν ε ((k : ℝ) / Y) ∧ Smooth1 ν ε ((k : ℝ) / Y) ≤ 1 :=
  ⟨Smooth1Nonneg νpos (div_pos (by exact_mod_cast hk) hY) hε0,
    Smooth1LeOne νpos mass_one hε0 (div_pos (by exact_mod_cast hk) hY)⟩

/-- **Weighted oscillatory sums.**  For `Re s = 1`, `s ≠ 1` and `c ∈ ℂ`, the sums
`Σ_{k ≤ K} (ψ(k/Y)²/2)(1 + 1/k) Re(c k^{−s})` are bounded above uniformly in `Y ≥ 1`, `K`. -/
theorem exists_sum_smooth1_sq_mul_re_cpow_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (c s : ℂ) (hs : s.re = 1) (hs1 : s ≠ 1) :
    ∃ B : ℝ, ∀ Y : ℝ, 1 ≤ Y → ∀ K : ℕ,
      ∑ k ∈ Finset.Icc 1 K, Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) *
        (c * (k : ℂ) ^ (-s)).re ≤ B := by
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_norm_sum_natCast_cpow_neg_le hs hs1
  refine ⟨‖c‖ * B₀ / 2 + ‖c‖, fun Y hY K => ?_⟩
  have hY0 : 0 < Y := by linarith
  set w : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) with hw
  have hwI := fun k (hk : 1 ≤ k) => smooth1_div_mem_Icc νpos mass_one hε0 hY0 hk
  have hwanti : ∀ k, 1 ≤ k → w (k + 1) ≤ w k := fun k hk =>
    smooth1_antitoneOn hν νpos hε0 (div_pos (by exact_mod_cast hk) hY0)
      (div_le_div_of_nonneg_right (by push_cast; linarith) hY0.le)
  have hnorm : ∀ k : ℕ, 1 ≤ k → |(c * (k : ℂ) ^ (-s)).re| ≤ ‖c‖ / k := by
    intro k hk
    refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, hs,
      Real.rpow_neg_one, div_eq_mul_inv]
  have hsplit : ∀ k ∈ Finset.Icc 1 K, w k ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (c * (k : ℂ) ^ (-s)).re =
      (c * (k : ℂ) ^ (-s)).re * w k ^ 2 / 2 + w k ^ 2 * (c * (k : ℂ) ^ (-s)).re / (2 * k) := by
    intro k _; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_div]
  have hosc : ∑ k ∈ Finset.Icc 1 K, (c * (k : ℂ) ^ (-s)).re * w k ^ 2 ≤ ‖c‖ * B₀ := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp; positivity
    have habel := abs_sum_mul_le_of_antitone (a := fun k => (c * (k : ℂ) ^ (-s)).re)
      (w := fun k => w k ^ 2) (B := ‖c‖ * B₀) hK
      (fun j _ => by
        rw [← Complex.re_sum, ← Finset.mul_sum]
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB₀ j) (norm_nonneg _))
      (fun k _ _ => sq_nonneg _)
      (fun k hk _ => pow_le_pow_left₀ (hwI (k + 1) (by omega)).1 (hwanti k hk) 2)
    have hw1 : w 1 ^ 2 ≤ 1 := pow_le_one₀ (hwI 1 le_rfl).1 (hwI 1 le_rfl).2
    calc _ ≤ |∑ k ∈ Finset.Icc 1 K, (c * (k : ℂ) ^ (-s)).re * w k ^ 2| := le_abs_self _
      _ ≤ ‖c‖ * B₀ * w 1 ^ 2 := habel
      _ ≤ ‖c‖ * B₀ * 1 := mul_le_mul_of_nonneg_left hw1 (by positivity)
      _ = ‖c‖ * B₀ := mul_one _
  have htail : ∑ k ∈ Finset.Icc 1 K, w k ^ 2 * (c * (k : ℂ) ^ (-s)).re / (2 * k) ≤ ‖c‖ := by
    have hle : ∀ k ∈ Finset.Icc 1 K,
        w k ^ 2 * (c * (k : ℂ) ^ (-s)).re / (2 * k) ≤ ‖c‖ / 2 * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hkk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      have hw2 : w k ^ 2 ≤ 1 := pow_le_one₀ (hwI k hk1).1 (hwI k hk1).2
      have h1 : w k ^ 2 * (c * (k : ℂ) ^ (-s)).re ≤ ‖c‖ / k :=
        calc w k ^ 2 * (c * (k : ℂ) ^ (-s)).re ≤ w k ^ 2 * |(c * (k : ℂ) ^ (-s)).re| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
          _ ≤ 1 * (‖c‖ / k) := mul_le_mul hw2 (hnorm k hk1) (abs_nonneg _) zero_le_one
          _ = ‖c‖ / k := one_mul _
      calc w k ^ 2 * (c * (k : ℂ) ^ (-s)).re / (2 * k) ≤ ‖c‖ / k / (2 * k) :=
            div_le_div_of_nonneg_right h1 (by positivity)
        _ = ‖c‖ / 2 * (1 / (k : ℝ) ^ 2) := by field_simp
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.mul_sum]
    calc ‖c‖ / 2 * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 ≤ ‖c‖ / 2 * 2 :=
          mul_le_mul_of_nonneg_left (by simpa only [one_div] using sum_Icc_inv_sq_le_two K) (by positivity)
      _ = ‖c‖ := by ring
  have : (∑ k ∈ Finset.Icc 1 K, (c * (k : ℂ) ^ (-s)).re * w k ^ 2) / 2 ≤ ‖c‖ * B₀ / 2 :=
    div_le_div_of_nonneg_right hosc (by norm_num)
  linarith

/-- **The weighted main sum.**  `Σ_{k ≤ K} (ψ(k/Y)²/2)(1 + 1/k)/k ≤ (log Y + 3 + log 3)/2`. -/
theorem sum_smooth1_sq_mul_inv_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν) (νpos : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {Y : ℝ}
    (hY : 1 ≤ Y) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ)) ≤
      (Real.log Y + 3 + Real.log 3) / 2 := by
  have hY0 : 0 < Y := by linarith
  set w : ℕ → ℝ := fun k => Smooth1 ν ε ((k : ℝ) / Y) with hw
  set M : ℕ := ⌊3 * Y⌋₊ with hM
  have hwI := fun k (hk : 1 ≤ k) => smooth1_div_mem_Icc νpos mass_one hε0 hY0 hk
  have hwzero : ∀ k, M < k → w k = 0 := by
    intro k hk
    have h3 : 3 * Y < k := (Nat.floor_lt (by positivity)).mp hk
    exact smooth1_eq_zero_of_three_le hν hε0 hε1 (by rw [le_div_iff₀ hY0]; linarith)
  have hle : ∀ k ∈ Finset.Icc 1 K, w k ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ)) ≤
      (if k ≤ M then 1 / (k : ℝ) else 0) / 2 + 1 / 2 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hkk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hw2 : w k ^ 2 ≤ 1 := pow_le_one₀ (hwI k hk1).1 (hwI k hk1).2
    have e : w k ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ)) =
        w k ^ 2 * (1 / (k : ℝ)) / 2 + w k ^ 2 / 2 * (1 / (k : ℝ) ^ 2) := by field_simp
    rw [e]
    have h2 : w k ^ 2 / 2 * (1 / (k : ℝ) ^ 2) ≤ 1 / 2 * (1 / (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [hw2]) (by positivity)
    have h1 : w k ^ 2 * (1 / (k : ℝ)) / 2 ≤ (if k ≤ M then 1 / (k : ℝ) else 0) / 2 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      split_ifs with hkM
      · calc w k ^ 2 * (1 / (k : ℝ)) ≤ 1 * (1 / (k : ℝ)) :=
              mul_le_mul_of_nonneg_right hw2 (by positivity)
          _ = 1 / (k : ℝ) := one_mul _
      · rw [hwzero k (by omega)]; simp
    linarith only [h1, h2]
  refine (Finset.sum_le_sum hle).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  have hS1 : ∑ k ∈ Finset.Icc 1 K, (if k ≤ M then 1 / (k : ℝ) else 0) ≤
      1 + Real.log 3 + Real.log Y := by
    rw [← Finset.sum_filter]
    have hsub : (Finset.Icc 1 K).filter (fun k => k ≤ M) ⊆ Finset.Icc 1 M := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
      omega
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    have hH : ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) = (harmonic M : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast; ring
    rw [hH]
    refine (harmonic_le_one_add_log M).trans ?_
    have hM3 : (3 : ℝ) ≤ M := by
      have : (3 : ℕ) ≤ M := (Nat.le_floor_iff (by positivity)).mpr (by push_cast; linarith)
      exact_mod_cast this
    have hMY : (M : ℝ) ≤ 3 * Y := Nat.floor_le (by positivity)
    have := Real.log_le_log (by linarith) hMY
    rw [Real.log_mul (by norm_num) hY0.ne'] at this
    linarith
  have hS2 : ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 ≤ 2 := by
    simpa only [one_div] using sum_Icc_inv_sq_le_two K
  have : 1 / 2 * ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) ^ 2 ≤ 1 / 2 * 2 :=
    mul_le_mul_of_nonneg_left hS2 (by norm_num)
  linarith

/-! ## Diagonal and off-diagonal energies -/

/-- **Energy of the smoothed zero dual.**  For a zero ordinate `Re ρ = ½`, `Im ρ ≠ 0`, the real
dual `A_k = Re(k^{−ρ}) ψ(k/Y)` has `Σ k(k+1)(A_k − A_{k+1})² ≤ (|ρ|²/2) log Y + K₀` for all
`Y ≥ 1`. -/
theorem exists_bdDualEnergy_re_zeroSmoothDual_le {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ∃ K₀ : ℝ, ∀ Y : ℝ, 1 ≤ Y → ∀ K : ℕ,
      bdDualEnergy (fun k => (zeroSmoothDual ν ε ρ Y k).re) K ≤
        ‖ρ‖ ^ 2 / 2 * Real.log Y + K₀ := by
  obtain ⟨K₂, hK₂⟩ := exists_bdDualBilin_zeroSmoothDual_le hν νpos mass_one hε0 hε1 hre hre
  have hs : (ρ + ρ).re = 1 := by simp [hre]; norm_num
  have hs1 : ρ + ρ ≠ 1 := fun h => him (by
    have := congrArg Complex.im h
    simp at this
    linarith)
  obtain ⟨B, hB⟩ := exists_sum_smooth1_sq_mul_re_cpow_le hν νpos mass_one hε0 (ρ * ρ) (ρ + ρ) hs hs1
  refine ⟨B + ‖ρ‖ ^ 2 * (3 + Real.log 3) / 2 + K₂, fun Y hY K => ?_⟩
  rw [bdDualEnergy_eq_bdDualBilin]
  refine (hK₂ Y hY K).trans ?_
  have hconj : ∀ k : ℕ, (ρ * conj ρ * (k : ℂ) ^ (-(ρ + conj ρ))).re = ‖ρ‖ ^ 2 * (1 / (k : ℝ)) := by
    intro k
    have h1 : ρ + conj ρ = 1 := by
      rw [Complex.add_conj, hre]; push_cast; ring
    rw [h1, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.cpow_neg_one]
    rw [show ((‖ρ‖ ^ 2 : ℝ) : ℂ) * (k : ℂ)⁻¹ = ((‖ρ‖ ^ 2 * (1 / (k : ℝ)) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  have hsplit : ∀ k ∈ Finset.Icc 1 K, Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) *
      ((ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re + (ρ * conj ρ * (k : ℂ) ^ (-(ρ + conj ρ))).re) =
      Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (ρ * ρ * (k : ℂ) ^ (-(ρ + ρ))).re +
      ‖ρ‖ ^ 2 * (Smooth1 ν ε ((k : ℝ) / Y) ^ 2 / 2 * (1 + 1 / (k : ℝ)) * (1 / (k : ℝ))) := by
    intro k _; rw [hconj]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := hB Y hY K
  have h2 := mul_le_mul_of_nonneg_left (sum_smooth1_sq_mul_inv_le hν νpos mass_one hε0 hε1 hY K)
    (sq_nonneg ‖ρ‖)
  have e : ‖ρ‖ ^ 2 * ((Real.log Y + 3 + Real.log 3) / 2) =
      ‖ρ‖ ^ 2 / 2 * Real.log Y + ‖ρ‖ ^ 2 * (3 + Real.log 3) / 2 := by ring
  linarith

/-- **Asymptotic orthogonality of the zero duals.**  For distinct zero ordinates
`Re ρ = Re ρ' = ½`, `Im ρ, Im ρ' > 0`, the bilinear energy of their real duals is bounded above
uniformly in `Y ≥ 1`: both phases `k^{−(ρ+ρ')}` and `k^{−(ρ+ρ̄')}` oscillate. -/
theorem exists_bdDualBilin_zeroSmoothDual_le_of_ne {ν : ℝ → ℝ} (hν : IsHalfTwoBump ν)
    (νpos : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Ioi 0, ν x / x = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) {ρ ρ' : ℂ} (hre : ρ.re = 1 / 2) (hre' : ρ'.re = 1 / 2) (him : 0 < ρ.im)
    (him' : 0 < ρ'.im) (hne : ρ ≠ ρ') :
    ∃ K₃ : ℝ, ∀ Y : ℝ, 1 ≤ Y → ∀ K : ℕ,
      bdDualBilin (fun k => (zeroSmoothDual ν ε ρ Y k).re)
        (fun k => (zeroSmoothDual ν ε ρ' Y k).re) K ≤ K₃ := by
  obtain ⟨K₂, hK₂⟩ := exists_bdDualBilin_zeroSmoothDual_le hν νpos mass_one hε0 hε1 hre hre'
  have hs : (ρ + ρ').re = 1 := by simp [hre, hre']; norm_num
  have hs1 : ρ + ρ' ≠ 1 := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hs' : (ρ + conj ρ').re = 1 := by simp [hre, hre']; norm_num
  have hs1' : ρ + conj ρ' ≠ 1 := fun h => hne (by
    have := congrArg Complex.im h
    simp at this
    exact Complex.ext (by rw [hre, hre']) (by linarith))
  obtain ⟨B, hB⟩ := exists_sum_smooth1_sq_mul_re_cpow_le hν νpos mass_one hε0 (ρ * ρ') _ hs hs1
  obtain ⟨B', hB'⟩ :=
    exists_sum_smooth1_sq_mul_re_cpow_le hν νpos mass_one hε0 (ρ * conj ρ') _ hs' hs1'
  refine ⟨B + B' + K₂, fun Y hY K => (hK₂ Y hY K).trans ?_⟩
  rw [Finset.sum_congr rfl (fun k _ => mul_add _ _ _), Finset.sum_add_distrib]
  linarith [hB Y hY K, hB' Y hY K]

end

end RHTower
