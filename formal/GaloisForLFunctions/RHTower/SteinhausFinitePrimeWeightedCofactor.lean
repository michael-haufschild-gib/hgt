import GaloisForLFunctions.RHTower.SteinhausFinitePrimeCofactorMean
import GaloisForLFunctions.RHTower.EulerDeletionDilationPowerGrowth
import GaloisForLFunctions.HTGeometry.OperatorTailDirichletMatroid

/-!
# Complex weighted cofactor modes from finite prime-phase extensions

The exact finite-prefix divisor correction is absolutely summable after division by its index.
The ordinary power-sum asymptotic bounds every normalized cofactor row by the same reciprocal
majorant. Tannery therefore proves the complex weighted mean for the literal prefix function.

A coherent logarithmic extension preserving all old prime phases then realizes the explicit
Cauchy node vector `A / (s + i*t)`, with the nonzero scalar `A` supplied by its finite prefix.
This is a source asymptotic for the BAG covariance construction; it does not assume a weighted
mean theorem and does not conclude a target event or a deterministic return.
-/

open ArithmeticFunction Filter Topology Finset
open GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.zeta
namespace RHTower
noncomputable section

private def powerCofactorSum (z : ℂ) (N : ℕ) : ℂ :=
  arithmeticSummatory (dirichletShift (1 - z) (ζ : ArithmeticFunction ℂ)) N

private theorem powerCofactorSum_eq_rawPrefix (z : ℂ) (N : ℕ) :
    powerCofactorSum z N = DeletionMixedRefinement.rawPrefix (1 - z) N := by
  induction N with
  | zero => simp [powerCofactorSum, arithmeticSummatory, DeletionMixedRefinement.rawPrefix]
  | succ N ih =>
    unfold powerCofactorSum arithmeticSummatory at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), DeletionMixedRefinement.rawPrefix,
      Finset.sum_range_succ, ih]
    congr 1
    simp [dirichletShift_apply, cpowWeight, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, DeletionMixedRefinement.kernel]

private theorem tendsto_powerCofactorSum_normalized {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    Tendsto (fun N : ℕ => powerCofactorSum z N * (N : ℂ) ^ (-z)) atTop (𝓝 (1 / z)) := by
  have h := DeletionDilationGrowth.rawPrefix_mul_cpow_tendsto
    (s := 1 - z) (by simp; linarith) (by simp; linarith)
  simpa only [powerCofactorSum_eq_rawPrefix, sub_sub_cancel,
    show 1 - z - 1 = -z by ring] using h

private theorem exists_norm_powerCofactorSum_le {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ‖powerCofactorSum z N‖ ≤ C * (N : ℝ) ^ z.re := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_powerCofactorSum_normalized hz hz1)).exists_norm_le
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [powerCofactorSum, arithmeticSummatory]
    positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hb := hC _ ⟨N, rfl⟩
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re,
    Real.rpow_neg hNR.le, ← div_eq_mul_inv] at hb
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos hNR z.re)).mp hb
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C])
    (Real.rpow_nonneg hNR.le _))

private theorem natRatio_cpow (M N : ℕ) (z : ℂ) :
    (((M : ℝ) / N : ℝ) : ℂ) ^ z = (M : ℂ) ^ z / (N : ℂ) ^ z := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg M) (inv_nonneg.mpr (Nat.cast_nonneg N))]
  simp only [Complex.ofReal_natCast, Complex.ofReal_inv,
    Complex.inv_cpow (N : ℂ) z (by simpa only [Complex.natCast_arg] using Real.pi_pos.ne), div_eq_mul_inv]

private theorem weightedCorrectionRow_tendsto
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1)
    {d : ℕ} (hd : d ≠ 0) :
    Tendsto (fun N : ℕ =>
      dirichletShift (1 - z) (finitePrimePhaseCorrection S omega) d *
        powerCofactorSum z (N / d) * (N : ℂ) ^ (-z)) atTop
      (𝓝 (finitePrimePhaseCorrection S omega d / (d : ℂ) * (1 / z))) := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hdpow : (d : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hdC]
    exact Complex.exp_ne_zero _
  have hmain := (tendsto_powerCofactorSum_normalized hz hz1).comp
    (GaloisForLFunctions.HTGeometry.tendsto_natDiv_atTop hdpos)
  have hratio := (Complex.continuousAt_ofReal_cpow_const (1 / (d : ℝ)) z
    (Or.inl hz)).tendsto.comp
    (GaloisForLFunctions.HTGeometry.tendsto_natDiv_div_self hdpos)
  have h := ((tendsto_const_nhds (x := (d : ℂ) ^ (z - 1) *
    finitePrimePhaseCorrection S omega d)).mul hmain).mul hratio
  have hvalue : ((d : ℂ) ^ (z - 1) * finitePrimePhaseCorrection S omega d) *
      (1 / z) * (((1 / (d : ℝ) : ℝ) : ℂ) ^ z) =
      finitePrimePhaseCorrection S omega d / (d : ℂ) * (1 / z) := by
    have hr := natRatio_cpow 1 d z
    simp only [Nat.cast_one, Complex.one_cpow] at hr
    rw [hr, Complex.cpow_sub _ _ hdC, Complex.cpow_one]
    field_simp
  rw [hvalue] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hM : 0 < N / d := Nat.div_pos hN hdpos
  have hMC : ((N / d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMpow : ((N / d : ℕ) : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hMC]
    exact Complex.exp_ne_zero _
  simp only [Function.comp_apply]
  rw [natRatio_cpow]
  simp only [ dirichletShift_apply, cpowWeight,
    show -(1 - z) = z - 1 by ring, Complex.cpow_neg]
  field_simp

private theorem weightedCorrectionRow_norm_le
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {z : ℂ} (hz : 0 < z.re)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ M : ℕ, ‖powerCofactorSum z M‖ ≤ C * (M : ℝ) ^ z.re)
    {N d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    ‖dirichletShift (1 - z) (finitePrimePhaseCorrection S omega) d *
      powerCofactorSum z (N / d) * (N : ℂ) ^ (-z)‖ ≤
      C * ‖finitePrimePhaseCorrection S omega d / (d : ℂ)‖ := by
  have hdN := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := hdN.1
  have hNpos : 0 < N := hdN.1.trans hdN.2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  simp only [dirichletShift_apply, cpowWeight, show -(1 - z) = z - 1 by ring,
    norm_mul, Complex.norm_natCast_cpow_of_pos hdpos,
    Complex.norm_natCast_cpow_of_pos hNpos, Complex.sub_re, Complex.one_re, Complex.neg_re]
  calc
    (d : ℝ) ^ (z.re - 1) * ‖finitePrimePhaseCorrection S omega d‖ *
        ‖powerCofactorSum z (N / d)‖ * (N : ℝ) ^ (-z.re) ≤
      (d : ℝ) ^ (z.re - 1) * ‖finitePrimePhaseCorrection S omega d‖ *
        (C * ((N : ℝ) / d) ^ z.re) * (N : ℝ) ^ (-z.re) := by
      gcongr
      exact (hbound (N / d)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hz.le) hC.le)
    _ = C * ‖finitePrimePhaseCorrection S omega d / (d : ℂ)‖ := by
      rw [Real.rpow_sub hdR, Real.rpow_one, Real.div_rpow hNR.le hdR.le,
        Real.rpow_neg hNR.le, norm_div, Complex.norm_natCast]
      field_simp [(Real.rpow_pos_of_pos hdR z.re).ne', (Real.rpow_pos_of_pos hNR z.re).ne']

/-- A finite prime-phase prefix has its literal complex-power weighted mean throughout the
open strip. The reciprocal divisor correction supplies the summable majorant. -/
theorem tendsto_finitePrimePhase_weighted_mean
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {z : ℂ} (hz : 0 < z.re) (hz1 : z.re < 1) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, finitePrimePhase S omega n * (n : ℂ) ^ (z - 1)) *
        (N : ℂ) ^ (-z)) atTop (𝓝 (finitePrimePhaseMean S omega / z)) := by
  let corr := finitePrimePhaseCorrection S omega
  let row : ℕ → ℕ → ℂ := fun N d => if d ∈ Finset.Icc 1 N then
    dirichletShift (1 - z) corr d * powerCofactorSum z (N / d) * (N : ℂ) ^ (-z) else 0
  let limit : ℕ → ℂ := fun d => corr d / (d : ℂ) * (1 / z)
  obtain ⟨C, hC, hbound⟩ := exists_norm_powerCofactorSum_le hz hz1
  have hseries := hasSum_finitePrimePhaseCorrection_div S omega
  have hrowLimit : ∀ d : ℕ, Tendsto (fun N => row N d) atTop (𝓝 (limit d)) := by
    intro d
    by_cases hd : d = 0
    · subst d
      simp [row, limit]
    · apply (weightedCorrectionRow_tendsto S omega hz hz1 hd).congr'
      filter_upwards [eventually_ge_atTop d] with N hN
      have hmem : d ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd, hN⟩
      simp only [row, hmem, if_true, corr]
  have hrowBound : ∀ᶠ N : ℕ in atTop, ∀ d, ‖row N d‖ ≤ C * ‖corr d / (d : ℂ)‖ := by
    filter_upwards with N d
    by_cases hd : d ∈ Finset.Icc 1 N
    · simp only [row, hd, if_true]
      exact weightedCorrectionRow_norm_le S omega hz hC hbound hd
    · simp only [row, hd, if_false, norm_zero]
      positivity
  have h := tendsto_tsum_of_dominated_convergence
    (hseries.summable.norm.mul_left C) hrowLimit hrowBound
  have hlimit : (∑' d, limit d) = finitePrimePhaseMean S omega / z := by
    unfold limit
    rw [tsum_mul_right, hseries.tsum_eq]
    ring
  rw [hlimit] at h
  apply h.congr'
  filter_upwards with N
  have hfinite : (∑' d, row N d) =
      ∑ d ∈ Finset.Icc 1 N,
        dirichletShift (1 - z) corr d * powerCofactorSum z (N / d) * (N : ℂ) ^ (-z) := by
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [row, hd, if_true]
    · intro d hd
      simp only [row, hd, if_false]
  rw [hfinite, ← Finset.sum_mul]
  congr 1
  have hconv : dirichletShift (1 - z) corr * dirichletShift (1 - z) (ζ : ArithmeticFunction ℂ) =
      dirichletShift (1 - z) (finitePrimePhase S omega) := by
    rw [← dirichletShift_mul]
    dsimp only [corr]
    rw [finitePrimePhaseCorrection_mul_zeta]
  have hsum := arithmeticSummatory_mul (dirichletShift (1 - z) corr)
    (dirichletShift (1 - z) (ζ : ArithmeticFunction ℂ)) N
  rw [hconv] at hsum
  simp only [powerCofactorSum]
  rw [← hsum]
  unfold arithmeticSummatory
  apply Finset.sum_congr rfl
  intro n _
  simp only [dirichletShift_apply, cpowWeight, show -(1 - z) = z - 1 by ring]
  exact mul_comm _ _

/-- A coherent extension realizes its Cauchy mode at every fixed node in the open strip.
The scalar is the explicit nonzero finite-prefix mean, common to all nodes. -/
theorem tendsto_finitePrimeTwistExtension_weighted_mean
    (S : Finset ℕ) (omega : SteinhausModel.Omega) (t : ℝ)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, SteinhausModel.X n (finitePrimeTwistExtension S omega t) *
        (n : ℂ) ^ (s - 1)) * (N : ℂ) ^ (-(s + (t : ℂ) * Complex.I))) atTop
      (𝓝 (finitePrimePhaseMean S (fun p => omega p - t * Real.log p / (2 * Real.pi)) /
        (s + (t : ℂ) * Complex.I))) := by
  have h := tendsto_finitePrimePhase_weighted_mean S
    (fun p => omega p - t * Real.log p / (2 * Real.pi))
    (z := s + (t : ℂ) * Complex.I) (by simpa using hs) (by simpa using hs1)
  convert h using 1
  funext N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  rw [X_finitePrimeTwistExtension_factor S omega t hn0, mul_assoc,
    ← Complex.cpow_add _ _ (by exact_mod_cast hn0)]
  congr 2
  ring

end
end RHTower
