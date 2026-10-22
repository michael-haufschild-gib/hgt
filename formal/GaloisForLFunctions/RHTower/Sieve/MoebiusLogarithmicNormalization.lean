import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicLogRate
import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift
import GaloisForLFunctions.RHTower.Deninger.DeningerAbelianLimit
import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.HTGeometry.DiscreteAbelRing
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.VonMangoldtAdditiveLogJetDirichlet

/-!
# The logarithmic Möbius normalization
-/

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient `-μ(n) log n / n`. -/
def moebiusLogHarmonicTerm (n : ℕ) : ℝ :=
  -((moebius n : ℤ) : ℝ) * Real.log (n : ℝ) * (n : ℝ) ^ (-1 : ℝ)

/-- Partial sums of `-μ(n) log n / n`. -/
def moebiusLogHarmonicPartial (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), moebiusLogHarmonicTerm n

@[simp] theorem moebiusLogHarmonicTerm_zero : moebiusLogHarmonicTerm 0 = 0 := by
  simp [moebiusLogHarmonicTerm]

private theorem deningerPartialSum_moebiusHarmonic (N : ℕ) :
    RHTower.deningerPartialSum
        (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ)) N =
      RHTower.deningerHarmonicPartial N := rfl

private theorem summable_deningerHarmonic_logIncrement :
    Summable fun n : ℕ => RHTower.deningerHarmonicPartial n *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  obtain ⟨B, hB, hpartial⟩ := exists_abs_deningerHarmonicPartial_log_rate
  rw [Filter.eventually_atTop] at hpartial
  obtain ⟨K, hK⟩ := hpartial
  have hevent : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨L, hL⟩ := hevent
  let M := max K L
  have hMe : Real.exp 1 ≤ (M : ℝ) := hL M (le_max_right K L)
  let C : ℝ := 2 * B + B / 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmajor : Summable fun i : ℕ =>
      C / (((M : ℝ) + ((i : ℝ) + 1)) *
        (Real.log ((M : ℝ) + ((i : ℝ) + 1))) ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (summable_one_div_mul_log_three hMe).mul_left C
  have hshift : Summable fun i : ℕ =>
      RHTower.deningerHarmonicPartial (i + (M + 1)) *
        (Real.log (((i + (M + 1) : ℕ) : ℝ) + 1) -
          Real.log ((i + (M + 1) : ℕ) : ℝ)) := by
    refine Summable.of_norm_bounded hmajor fun i => ?_
    let n := i + (M + 1)
    have hnM : M ≤ n := by dsimp [n]; omega
    have hnK : K ≤ n := le_trans (le_max_left K L) hnM
    have hne : Real.exp 1 ≤ (n : ℝ) := le_trans hMe (by exact_mod_cast hnM)
    have hlog : 1 ≤ Real.log (n : ℝ) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hne
    have hlogpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog
    have hpart := hK n hnK
    have hcollapse :
        2 * B / (Real.log (n : ℝ)) ^ 4 + B / (3 * (Real.log (n : ℝ)) ^ 3)
          ≤ C / (Real.log (n : ℝ)) ^ 3 := by
      have hp3 : 0 < (Real.log (n : ℝ)) ^ 3 := pow_pos hlogpos 3
      have hp34 : (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 4 := by
        calc
          (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 * Real.log (n : ℝ) :=
            le_mul_of_one_le_right (pow_nonneg hlogpos.le 3) hlog
          _ = (Real.log (n : ℝ)) ^ 4 := by ring
      have hfirst : 2 * B / (Real.log (n : ℝ)) ^ 4 ≤
          2 * B / (Real.log (n : ℝ)) ^ 3 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using one_div_le_one_div_of_le hp3 hp34)
          (mul_nonneg (by norm_num) hB)
      calc
        2 * B / (Real.log (n : ℝ)) ^ 4 + B / (3 * (Real.log (n : ℝ)) ^ 3)
            ≤ 2 * B / (Real.log (n : ℝ)) ^ 3 +
                B / (3 * (Real.log (n : ℝ)) ^ 3) := add_le_add hfirst le_rfl
        _ = C / (Real.log (n : ℝ)) ^ 3 := by dsimp [C]; ring
    have hpart' : |RHTower.deningerHarmonicPartial n| ≤
        C / (Real.log (n : ℝ)) ^ 3 := le_trans hpart hcollapse
    have hdiff0 : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
      exact sub_nonneg.mpr (Real.log_le_log (by positivity) (by linarith))
    have hdiff := log_natCast_succ_sub_log_natCast_le_inv n (by
      have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
      exact_mod_cast (show (1 : ℝ) ≤ n by linarith))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdiff0]
    calc
      |RHTower.deningerHarmonicPartial n| *
          (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
        ≤ (C / (Real.log (n : ℝ)) ^ 3) * (1 / (n : ℝ)) :=
          mul_le_mul hpart' hdiff hdiff0 (by positivity)
      _ = C / (((M : ℝ) + ((i : ℝ) + 1)) *
          (Real.log ((M : ℝ) + ((i : ℝ) + 1))) ^ 3) := by
        dsimp [n]
        push_cast
        have harg : (i : ℝ) + ((M : ℝ) + 1) = (M : ℝ) + ((i : ℝ) + 1) := by ring
        rw [harg]
        field_simp [hlogpos.ne']
  exact (summable_nat_add_iff (M + 1)).mp (by
    simpa only [Nat.add_comm] using hshift)

/-- The logarithmic Möbius partial sums have a finite limit. -/
theorem exists_tendsto_moebiusLogHarmonicPartial :
    ∃ S : ℝ, Tendsto moebiusLogHarmonicPartial atTop (𝓝 S) := by
  let t : ℕ → ℝ := fun n => RHTower.deningerHarmonicPartial n *
    (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ))
  have ht : Summable t := summable_deningerHarmonic_logIncrement
  refine ⟨∑' n : ℕ, t n, ?_⟩
  have hboundary : Tendsto (fun N : ℕ =>
      RHTower.deningerHarmonicPartial N * (-Real.log (N : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_log_mul_deningerHarmonicPartial_zero.neg
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hseries := ht.hasSum.tendsto_sum_nat
  have hadd := hboundary.add hseries
  rw [zero_add] at hadd
  refine hadd.congr fun N => ?_
  have habel := RHTower.deningerAbelSummation
    (fun n : ℕ => ((moebius n : ℤ) : ℝ) / (n : ℝ))
    (fun n : ℕ => -Real.log (n : ℝ)) N
  rw [deningerPartialSum_moebiusHarmonic] at habel
  calc
    RHTower.deningerHarmonicPartial N * -Real.log (N : ℝ) +
        ∑ i ∈ Finset.range N, t i =
      RHTower.deningerHarmonicPartial N * -Real.log (N : ℝ) +
        ∑ i ∈ Finset.range N, RHTower.deningerHarmonicPartial i *
          (-Real.log (i : ℝ) - -Real.log ((i + 1 : ℕ) : ℝ)) := by
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            dsimp [t]
            push_cast
            ring
    _ = ∑ n ∈ Finset.range (N + 1),
        ((moebius n : ℤ) : ℝ) / (n : ℝ) * -Real.log (n : ℝ) := habel.symm
    _ = moebiusLogHarmonicPartial N := by
      simp only [moebiusLogHarmonicPartial, moebiusLogHarmonicTerm]
      refine Finset.sum_congr rfl fun n hn => ?_
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
        rw [Real.rpow_neg_one]
        field_simp

/-- The limit of `-∑_{n≤N} μ(n) log n / n`. -/
def moebiusLogHarmonicLimit : ℝ := Classical.choose exists_tendsto_moebiusLogHarmonicPartial

theorem tendsto_moebiusLogHarmonicPartial :
    Tendsto moebiusLogHarmonicPartial atTop (𝓝 moebiusLogHarmonicLimit) :=
  Classical.choose_spec exists_tendsto_moebiusLogHarmonicPartial

private theorem moebiusLogHarmonicAbel_eq {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, moebiusLogHarmonicTerm n * (n : ℝ) ^ (-σ)) =
      ∑' m : ℕ, moebiusLogHarmonicPartial (m + 1) * RHTower.deningerAbelWeight σ m := by
  have hleftSumm : Summable fun n : ℕ =>
      moebiusLogHarmonicTerm n * (n : ℝ) ^ (-σ) := by
    let c : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
    have hbase : LSeriesSummable c (((1 + σ / 2 : ℝ) : ℂ)) := by
      apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      · intro n hn
        dsimp [c]
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      · simp
        linarith
    have habs : LSeries.abscissaOfAbsConv c <
        ((((1 + σ : ℝ) : ℂ)).re : EReal) := by
      refine lt_of_le_of_lt hbase.abscissaOfAbsConv_le (EReal.coe_lt_coe_iff.mpr ?_)
      simp
      linarith
    have hlog := LSeriesSummable_logMul_of_lt_re habs
    have hcoef : LSeries.logMul c = fun n : ℕ =>
        ((((moebius n : ℤ) : ℝ) * Real.log n : ℝ) : ℂ) := by
      funext n
      dsimp [c, LSeries.logMul]
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
      push_cast
      ring
    rw [hcoef] at hlog
    have hreal : Summable fun n : ℕ =>
        (((moebius n : ℤ) : ℝ) * Real.log n) * (n : ℝ) ^ (-(1 + σ)) :=
      summable_real_of_lseriesSummable (by simp) hlog
    exact hreal.neg.congr fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [moebiusLogHarmonicTerm]
      · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hexp : -(1 + σ) = (-1 : ℝ) + (-σ) := by ring
        rw [moebiusLogHarmonicTerm, hexp, Real.rpow_add hnR]
        ring
  obtain ⟨D, hD⟩ := RHTower.deningerBounded_of_tendsto
    tendsto_moebiusLogHarmonicPartial
  have hrightSumm : Summable fun m : ℕ =>
      moebiusLogHarmonicPartial (m + 1) * RHTower.deningerAbelWeight σ m :=
    RHTower.deningerAbelAverage_summable (fun m => hD (m + 1)) hσ
  have hleft := hleftSumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
  have hboundary : Tendsto (fun N : ℕ =>
      moebiusLogHarmonicPartial (N + 1) * ((N : ℝ) + 1) ^ (-σ)) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-σ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hσ).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj := hb.norm.const_mul D
    rw [norm_zero, mul_zero] at hmaj
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hmaj
    filter_upwards with N
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hD (N + 1)) (norm_nonneg _)
  have hright := hrightSumm.hasSum.tendsto_sum_nat
  have hcomb := hboundary.add hright
  rw [zero_add] at hcomb
  refine tendsto_nhds_unique hleft (hcomb.congr fun N => ?_)
  have habel := RHTower.deningerAbelSummation moebiusLogHarmonicTerm
    (fun n : ℕ => (n : ℝ) ^ (-σ)) (N + 1)
  have hpartial : RHTower.deningerPartialSum moebiusLogHarmonicTerm =
      moebiusLogHarmonicPartial := by rfl
  rw [hpartial] at habel
  change moebiusLogHarmonicPartial (N + 1) * ((N : ℝ) + 1) ^ (-σ) +
      ∑ i ∈ Finset.range N,
        moebiusLogHarmonicPartial (i + 1) * RHTower.deningerAbelWeight σ i =
    ∑ i ∈ Finset.range (N + 2), moebiusLogHarmonicTerm i * (i : ℝ) ^ (-σ)
  rw [show N + 2 = N + 1 + 1 by omega, habel]
  push_cast
  congr 1
  rw [Finset.sum_range_succ']
  have hzero : moebiusLogHarmonicPartial 0 = 0 := by
    simp [moebiusLogHarmonicPartial]
  rw [hzero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [RHTower.deningerAbelWeight]
  congr 2 <;> push_cast <;> ring

private theorem analyticAt_invZeta_one : AnalyticAt ℂ invZeta 1 := by
  change AnalyticAt ℂ (fun s : ℂ => (s - 1) * (zetaResidueUnit s)⁻¹) 1
  exact (analyticAt_id.sub analyticAt_const).mul
    ((analyticAt_zetaResidueUnit 1).inv (by rw [zetaResidueUnit_one]; norm_num))

theorem deriv_invZeta_one : deriv invZeta 1 = 1 := by
  unfold invZeta
  have hsub : DifferentiableAt ℂ (fun s : ℂ => s - 1) 1 :=
    differentiableAt_id.sub_const 1
  have hinv : DifferentiableAt ℂ (fun s : ℂ => (zetaResidueUnit s)⁻¹) 1 :=
    (analyticAt_zetaResidueUnit 1).differentiableAt.inv
      (by rw [zetaResidueUnit_one]; norm_num)
  have hfun : (fun s : ℂ => (s - 1) * (zetaResidueUnit s)⁻¹) =
      (fun s : ℂ => s - 1) * (fun s : ℂ => (zetaResidueUnit s)⁻¹) := by
    funext s
    rfl
  rw [hfun, deriv_mul hsub hinv]
  have hsubderiv : deriv (fun s : ℂ => s - 1) 1 = 1 :=
    ((hasDerivAt_id (𝕜 := ℂ) 1).sub_const 1).deriv
  rw [hsubderiv, zetaResidueUnit_one]
  ring

private theorem moebiusLogWeighted_eq_re_deriv_invZeta {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, moebiusLogHarmonicTerm n * (n : ℝ) ^ (-σ)) =
      (deriv invZeta (((1 + σ : ℝ) : ℂ))).re := by
  let c : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  let f : ℕ → ℝ := fun n => -((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)
  have hbase : LSeriesSummable c (((1 + σ / 2 : ℝ) : ℂ)) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      dsimp [c]
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    · simp
      linarith
  have habs : LSeries.abscissaOfAbsConv c <
      ((((1 + σ : ℝ) : ℂ)).re : EReal) := by
    refine lt_of_le_of_lt hbase.abscissaOfAbsConv_le (EReal.coe_lt_coe_iff.mpr ?_)
    simp
    linarith
  have hterms : (∑' n : ℕ, moebiusLogHarmonicTerm n * (n : ℝ) ^ (-σ)) =
      ∑' n : ℕ, f n * (n : ℝ) ^ (-(1 + σ)) := by
    apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [moebiusLogHarmonicTerm, f]
    · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hexp : -(1 + σ) = (-1 : ℝ) + (-σ) := by ring
      rw [moebiusLogHarmonicTerm, hexp, Real.rpow_add hnR]
      dsimp [f]
      ring
  have hcoef : (fun n : ℕ => ((f n : ℝ) : ℂ)) = -LSeries.logMul c := by
    funext n
    dsimp [f, c, LSeries.logMul]
    have hlogn : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hlogn]
    push_cast
    ring
  have hLderiv :
      ((∑' n : ℕ, f n * (n : ℝ) ^ (-(1 + σ)) : ℝ) : ℂ) =
        deriv (LSeries c) (((1 + σ : ℝ) : ℂ)) := by
    rw [ofReal_tsum_eq_lseries (f := f) (by simp [f]), hcoef, LSeries_neg,
      LSeries_deriv habs]
  have heq : LSeries c =ᶠ[𝓝 (((1 + σ : ℝ) : ℂ))] invZeta := by
    have hopen : {z : ℂ | 1 < z.re} ∈ 𝓝 (((1 + σ : ℝ) : ℂ)) := by
      exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) (by simp; linarith)
    filter_upwards [hopen] with z hz
    dsimp [c]
    rw [← tsum_cpow_neg_eq_LSeries (by simp)]
    exact tsum_moebius_cpow_eq_invZeta hz
  rw [hterms]
  have hcomplex :
      ((∑' n : ℕ, f n * (n : ℝ) ^ (-(1 + σ)) : ℝ) : ℂ) =
        deriv invZeta (((1 + σ : ℝ) : ℂ)) := by
    rw [hLderiv, heq.deriv_eq]
  exact Complex.ofReal_injective (by simpa using congrArg Complex.re hcomplex)

/-- The logarithmic Möbius sum has its classical value `1`. -/
theorem moebiusLogHarmonicLimit_eq_one : moebiusLogHarmonicLimit = 1 := by
  have hAbel := RHTower.deningerAbelian_tendsto
    (tendsto_moebiusLogHarmonicPartial.comp (tendsto_add_atTop_nat 1))
  have hderivComplex : Tendsto
      (fun σ : ℝ => deriv invZeta (((1 + σ : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
    have hcont : ContinuousAt (deriv invZeta) 1 := analyticAt_invZeta_one.deriv.continuousAt
    have harg : Tendsto (fun σ : ℝ => (((1 + σ : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
      have hc : Continuous fun σ : ℝ => (((1 + σ : ℝ) : ℂ)) := by fun_prop
      simpa only [add_zero, Complex.ofReal_one] using
        (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    have hcomp := hcont.tendsto.comp harg
    rw [deriv_invZeta_one] at hcomp
    exact hcomp.congr' (Eventually.of_forall fun _ => rfl)
  have hderiv : Tendsto
      (fun σ : ℝ => (deriv invZeta (((1 + σ : ℝ) : ℂ))).re) (𝓝[>] 0) (𝓝 1) := by
    exact (Complex.continuous_re.continuousAt.tendsto.comp hderivComplex).congr'
      (Eventually.of_forall fun _ => rfl)
  have hsame : (fun σ : ℝ => ∑' m : ℕ,
      moebiusLogHarmonicPartial (m + 1) * RHTower.deningerAbelWeight σ m)
      =ᶠ[𝓝[>] 0] fun σ : ℝ => (deriv invZeta (((1 + σ : ℝ) : ℂ))).re := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [← moebiusLogWeighted_eq_re_deriv_invZeta hσ,
      moebiusLogHarmonicAbel_eq hσ]
  exact tendsto_nhds_unique hAbel (hderiv.congr' hsame.symm)

/-- The partial sums of `-μ(n) log n / n` converge to `1`. -/
theorem tendsto_moebiusLogHarmonicPartial_one :
    Tendsto moebiusLogHarmonicPartial atTop (𝓝 1) := by
  rw [← moebiusLogHarmonicLimit_eq_one]
  exact tendsto_moebiusLogHarmonicPartial

/-- The linear logarithmic Möbius kernel is normalized to one. -/
theorem tendsto_sum_moebius_log_div_one :
    Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
      ((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log ((N : ℝ) / (d : ℝ)))
      atTop (𝓝 1) := by
  have hadd := tendsto_log_mul_deningerHarmonicPartial_zero.add
    tendsto_moebiusLogHarmonicPartial_one
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpartial : RHTower.deningerHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N, ((moebius d : ℤ) : ℝ) / (d : ℝ) := by
    rw [RHTower.deningerHarmonicPartial, Finset.sum_range_succ']
    simp
    convert RHTower.sum_range_succ_eq_sum_Icc
      (fun d : ℕ => ((moebius d : ℤ) : ℝ) / (d : ℝ)) N using 1 <;>
        push_cast <;> ring
  rw [hpartial]
  have hlogsum : moebiusLogHarmonicPartial N =
      ∑ d ∈ Finset.Icc 1 N,
        -(((moebius d : ℤ) : ℝ) / (d : ℝ) * Real.log (d : ℝ)) := by
    rw [moebiusLogHarmonicPartial, Finset.sum_range_succ']
    simp only [moebiusLogHarmonicTerm_zero, add_zero]
    rw [RHTower.sum_range_succ_eq_sum_Icc moebiusLogHarmonicTerm N]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by
      simp only [Finset.mem_Icc] at hd
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
    rw [moebiusLogHarmonicTerm, Real.rpow_neg_one]
    field_simp
  rw [hlogsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdR : (0 : ℝ) < (d : ℝ) := by
    simp only [Finset.mem_Icc] at hd
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
  rw [Real.log_div hNR.ne' hdR.ne']
  ring

end

end RHTower.Sieve
