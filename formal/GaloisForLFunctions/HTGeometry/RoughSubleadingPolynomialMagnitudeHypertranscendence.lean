import GaloisForLFunctions.HTGeometry.PolynomialPowerADEResonance
import GaloisForLFunctions.HTGeometry.PolynomialPowerExplicitConfinement
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Analysis.PSeries

/-!
# Rough subleading polynomial magnitudes

This module formalizes the almost-sure, phase-uniform hypertranscendence theorem for
`b n = n ^ β + n ^ α * u n`, where `3 < β`, `1 < α < β - 2`, and the coordinates
`u n` are independently uniform on `[1, 2]`.

It supplies the product-measure small-ball and Borel--Cantelli argument, deterministic
polynomial confinement and ADE-resonance reduction, the explicit entire phase family,
and the leading profile, first-difference, and second-difference asymptotics.
-/

open Filter Finset Set MeasureTheory PowerSeries MvPolynomial Asymptotics
open scoped ENNReal Topology

namespace GaloisForLFunctions

noncomputable section

def intervalUnitProbability : Measure ℝ :=
  volume.restrict (Set.Icc 1 2)

instance : IsProbabilityMeasure intervalUnitProbability where
  measure_univ := by
    rw [intervalUnitProbability, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc]
    norm_num

theorem volume_abs_mul_add_le (a c R : ℝ) (ha : a ≠ 0) (_hR : 0 ≤ R) :
    volume {x : ℝ | |a * x + c| ≤ R} = ENNReal.ofReal (2 * R / |a|) := by
  have hset : {x : ℝ | |a * x + c| ≤ R} =
      (fun x : ℝ => c + a * x) ⁻¹' Set.Icc (-R) R := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
    rw [add_comm]
    exact abs_le
  rw [hset]
  change volume ((fun x : ℝ => a * x) ⁻¹' ((fun y : ℝ => c + y) ⁻¹' Set.Icc (-R) R)) = _
  rw [Real.volume_preimage_mul_left ha, measure_preimage_add, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (abs_nonneg (a⁻¹))]
  congr 1
  rw [abs_inv]
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  field_simp
  ring

theorem intervalUnitProbability_abs_mul_add_le (a c R : ℝ)
    (ha : a ≠ 0) (hR : 0 ≤ R) :
    intervalUnitProbability {x : ℝ | |a * x + c| ≤ R} ≤
      ENNReal.ofReal (2 * R / |a|) := by
  calc
    intervalUnitProbability {x : ℝ | |a * x + c| ≤ R}
        ≤ volume {x : ℝ | |a * x + c| ≤ R} :=
          Measure.restrict_le_self _
    _ = _ := volume_abs_mul_add_le a c R ha hR

theorem measure_pi_abs_affine_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (i₀ : ι) (ha : a i₀ ≠ 0) (c R : ℝ) (hR : 0 ≤ R) :
    Measure.pi (fun _ : ι => intervalUnitProbability)
        {x : ι → ℝ | |c + ∑ i, a i * x i| ≤ R} ≤
      ENNReal.ofReal (2 * R / |a i₀|) := by
  let E : Set (ι → ℝ) := {x | |c + ∑ i, a i * x i| ≤ R}
  have hE : MeasurableSet E := by
    dsimp [E]
    change MeasurableSet ((fun x : ι → ℝ => |c + ∑ i, a i * x i|) ⁻¹' Set.Iic R)
    exact measurableSet_Iic.preimage (by fun_prop)
  rw [← lintegral_indicator_one hE]
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * R / |a i₀|)
  have hconst :
      ∫⁻ _x : ι → ℝ, B ∂Measure.pi (fun _ : ι => intervalUnitProbability) = B := by
    simp
  change (∫⁻ x, E.indicator 1 x ∂Measure.pi
    (fun _ : ι => intervalUnitProbability)) ≤ B
  rw [← hconst]
  apply lintegral_le_of_lmarginal_le {i₀}
  · exact Measurable.indicator measurable_const hE
  · fun_prop
  · rw [lmarginal_singleton, lmarginal_singleton]
    intro x
    have hsum (y : ℝ) :
        (∑ i, a i * Function.update x i₀ y i) =
          a i₀ * y + ∑ i ∈ Finset.univ.erase i₀, a i * x i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      simp only [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    let c' : ℝ := c + ∑ i ∈ Finset.univ.erase i₀, a i * x i
    have hsection :
        (fun y : ℝ => E.indicator (1 : (ι → ℝ) → ℝ≥0∞) (Function.update x i₀ y)) =
          {y : ℝ | |a i₀ * y + c'| ≤ R}.indicator 1 := by
      funext y
      by_cases hy : |a i₀ * y + c'| ≤ R
      · have hyE : Function.update x i₀ y ∈ E := by
          dsimp [E, c']
          rw [hsum]
          simpa only [c', add_assoc, add_comm, add_left_comm] using hy
        simp [hy, hyE]
      · have hyE : Function.update x i₀ y ∉ E := by
          dsimp [E, c']
          rw [hsum]
          simpa only [c', add_assoc, add_comm, add_left_comm] using hy
        simp [hy, hyE]
    change (∫⁻ y : ℝ, E.indicator 1 (Function.update x i₀ y)
      ∂intervalUnitProbability) ≤ ∫⁻ _y : ℝ, B ∂intervalUnitProbability
    have hsectionMeas : MeasurableSet {y : ℝ | |a i₀ * y + c'| ≤ R} := by
      change MeasurableSet ((fun y : ℝ => |a i₀ * y + c'|) ⁻¹' Set.Iic R)
      exact measurableSet_Iic.preimage (by fun_prop)
    rw [hsection, lintegral_indicator_one hsectionMeas]
    simp only [lintegral_const, MeasureTheory.measure_univ, mul_one]
    exact intervalUnitProbability_abs_mul_add_le (a i₀) c' R ha hR

def intervalUnitProductProbability : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => intervalUnitProbability)

theorem intervalUnitProductProbability_finsupp_smallBall
    (a : ℕ →₀ ℝ) {i₀ : ℕ} (ha : a i₀ ≠ 0) (c R : ℝ) (hR : 0 ≤ R) :
    intervalUnitProductProbability
        {x : ℕ → ℝ | |c + a.sum (fun i ai => ai * x i)| ≤ R} ≤
      ENNReal.ofReal (2 * R / |a i₀|) := by
  classical
  let E : Set (a.support → ℝ) :=
    {x | |c + ∑ i : a.support, a i * x i| ≤ R}
  have hE : MeasurableSet E := by
    dsimp [E]
    change MeasurableSet
      ((fun x : a.support → ℝ => |c + ∑ i : a.support, a i * x i|) ⁻¹' Set.Iic R)
    exact measurableSet_Iic.preimage (by fun_prop)
  have hset : {x : ℕ → ℝ | |c + a.sum (fun i ai => ai * x i)| ≤ R} =
      cylinder a.support E := by
    ext x
    simp only [mem_setOf_eq, mem_cylinder]
    dsimp [E]
    rw [Finsupp.sum]
    rw [Finset.sum_attach a.support (fun i => a i * x i)]
  rw [hset, intervalUnitProductProbability,
    Measure.infinitePi_cylinder (fun _ : ℕ => intervalUnitProbability) hE]
  let i₀' : a.support := ⟨i₀, Finsupp.mem_support_iff.mpr ha⟩
  exact measure_pi_abs_affine_sum_le
    (fun i : a.support => a i) i₀' (by simpa [i₀']) c R hR

def roughPolynomialProfile (β α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ β + (n : ℝ) ^ α * u n

def roughPolynomialStencil (Q : Polynomial ℤ) (α : ℝ) (n : ℕ) : ℕ →₀ ℝ :=
  ∑ j ∈ Finset.range (Q.natDegree + 1),
    Finsupp.single (n + j) ((Q.coeff j : ℝ) * ((n + j : ℕ) : ℝ) ^ α)

theorem roughPolynomialStencil_sum (Q : Polynomial ℤ) (α : ℝ) (n : ℕ)
    (u : ℕ → ℝ) :
    (roughPolynomialStencil Q α n).sum (fun i ai => ai * u i) =
      ∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * ((n + j : ℕ) : ℝ) ^ α * u (n + j) := by
  classical
  rw [roughPolynomialStencil, ← Finsupp.sum_finsetSum_index
    (s := Finset.range (Q.natDegree + 1))
    (g := fun j => Finsupp.single (n + j)
      ((Q.coeff j : ℝ) * ((n + j : ℕ) : ℝ) ^ α))
    (h := fun i ai => ai * u i)]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finsupp.sum_single_index]
    simp
  · intro i
    simp
  · intro i x y
    ring

theorem roughPolynomialStencil_apply_top
    (Q : Polynomial ℤ) (α : ℝ) (n : ℕ) :
    roughPolynomialStencil Q α n (n + Q.natDegree) =
      (Q.coeff Q.natDegree : ℝ) *
        (((n + Q.natDegree : ℕ) : ℝ) ^ α) := by
  classical
  rw [roughPolynomialStencil, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single Q.natDegree]
  · simp
  · intro j hj hne
    rw [if_neg]
    omega
  · intro hnot
    simp at hnot

theorem roughPolynomialShift_eq_pure_add_stencil
    (Q : Polynomial ℤ) (β α : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + j)) =
      (∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * (((n + j : ℕ) : ℝ) ^ β)) +
      (roughPolynomialStencil Q α n).sum (fun i ai => ai * u i) := by
  rw [roughPolynomialStencil_sum]
  simp_rw [roughPolynomialProfile]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem intervalUnitProductProbability_roughPolynomial_smallBall
    {Q : Polynomial ℤ} (hQ : Q ≠ 0) {α : ℝ} (hα : 0 < α)
    (β : ℝ) (M : ℕ) (n : ℕ) :
    intervalUnitProductProbability
        {u : ℕ → ℝ |
          |∑ j ∈ Finset.range (Q.natDegree + 1),
            (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + 1 + j)| ≤
              (M : ℝ) * Real.log ((n : ℝ) + 3)} ≤
      ENNReal.ofReal
        (2 * (M : ℝ) * Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) ^ α) := by
  let a := roughPolynomialStencil Q α (n + 1)
  let c := ∑ j ∈ Finset.range (Q.natDegree + 1),
    (Q.coeff j : ℝ) * ((((n + 1 + j : ℕ) : ℝ) ^ β))
  let R := (M : ℝ) * Real.log ((n : ℝ) + 3)
  have hR : 0 ≤ R := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hcoeff : Q.coeff Q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hcoeffReal : (Q.coeff Q.natDegree : ℝ) ≠ 0 := by exact_mod_cast hcoeff
  have hbase : 0 < (((n + 1 + Q.natDegree : ℕ) : ℝ)) := by positivity
  have ha : a (n + 1 + Q.natDegree) ≠ 0 := by
    dsimp [a]
    rw [roughPolynomialStencil_apply_top]
    exact mul_ne_zero hcoeffReal (ne_of_gt (Real.rpow_pos_of_pos hbase α))
  have hsmall := intervalUnitProductProbability_finsupp_smallBall
    a ha c R hR
  have hset :
      {u : ℕ → ℝ |
          |∑ j ∈ Finset.range (Q.natDegree + 1),
            (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + 1 + j)| ≤ R} =
        {u : ℕ → ℝ | |c + a.sum (fun i ai => ai * u i)| ≤ R} := by
    ext u
    simp only [Set.mem_setOf_eq]
    rw [roughPolynomialShift_eq_pure_add_stencil]
  rw [hset]
  refine hsmall.trans (ENNReal.ofReal_le_ofReal ?_)
  have hcoeffOne : (1 : ℝ) ≤ |(Q.coeff Q.natDegree : ℝ)| := by
    have hnat : 1 ≤ (Q.coeff Q.natDegree).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcoeff)
    have hnatR : (1 : ℝ) ≤ ((Q.coeff Q.natDegree).natAbs : ℝ) := by
      exact_mod_cast hnat
    calc
      (1 : ℝ) ≤ ((Q.coeff Q.natDegree).natAbs : ℝ) := hnatR
      _ = ((|(Q.coeff Q.natDegree)| : ℤ) : ℝ) := by
        rw [← Int.natCast_natAbs, Int.cast_natCast]
      _ = |(Q.coeff Q.natDegree : ℝ)| := Int.cast_abs
  have hbaseMono : ((n : ℝ) + 1) ^ α ≤
      (((n + 1 + Q.natDegree : ℕ) : ℝ)) ^ α := by
    apply Real.rpow_le_rpow (by positivity) (by push_cast; linarith) hα.le
  have haLower : ((n : ℝ) + 1) ^ α ≤ |a (n + 1 + Q.natDegree)| := by
    dsimp [a]
    rw [roughPolynomialStencil_apply_top, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hbase.le α)]
    exact hbaseMono.trans (le_mul_of_one_le_left
      (Real.rpow_nonneg hbase.le α) hcoeffOne)
  have hdenPos : 0 < ((n : ℝ) + 1) ^ α := Real.rpow_pos_of_pos (by positivity) α
  have hnum : 0 ≤ 2 * R := by positivity
  have hdiv := div_le_div_of_nonneg_left hnum hdenPos haLower
  simpa [R, mul_assoc] using hdiv

theorem summable_log_nat_add_three_div_rpow {α : ℝ} (hα : 1 < α) :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) ^ α) := by
  let δ := (α - 1) / 2
  let s := α - δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hs : 1 < s := by dsimp [s, δ]; linarith
  have hlim : Tendsto
      (fun n : ℕ => Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) ^ δ)
      atTop (𝓝 0) := by
    convert (tendsto_log_nat_add_two_div_rpow hδ).comp
      (tendsto_add_atTop_nat 1) using 1
    funext n
    dsimp only [Function.comp_apply]
    push_cast
    congr 2
    ring
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) ^ δ ≤ 1 := by
    exact hlim.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hmajor : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    refine ((Real.summable_one_div_nat_add_rpow 1 s).mpr hs).congr fun n => ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hbound] with n hn
  have hbase : 0 < (n : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.log ((n : ℝ) + 3) := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog (Real.rpow_nonneg hbase.le α))]
  have hδpow : 0 < ((n : ℝ) + 1) ^ δ := Real.rpow_pos_of_pos hbase δ
  have hspow : 0 < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos hbase s
  have hαeq : α = δ + s := by dsimp [s]; ring
  rw [hαeq, Real.rpow_add hbase]
  field_simp [hδpow.ne', hspow.ne'] at hn ⊢
  nlinarith

theorem ae_eventually_roughPolynomialShift_gt
    {Q : Polynomial ℤ} (hQ : Q ≠ 0) {α : ℝ} (hα : 1 < α)
    (β : ℝ) (M : ℕ) :
    ∀ᵐ u ∂intervalUnitProductProbability, ∀ᶠ n : ℕ in atTop,
      (M : ℝ) * Real.log ((n : ℝ) + 3) <
        |∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + 1 + j)| := by
  let E : ℕ → Set (ℕ → ℝ) := fun n =>
    {u |
      |∑ j ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + 1 + j)| ≤
          (M : ℝ) * Real.log ((n : ℝ) + 3)}
  let g : ℕ → ℝ := fun n =>
    2 * (M : ℝ) * Real.log ((n : ℝ) + 3) / ((n : ℝ) + 1) ^ α
  have hg : Summable g := by
    have h := (summable_log_nat_add_three_div_rpow hα).mul_left (2 * (M : ℝ))
    refine h.congr fun n => ?_
    dsimp [g]
    ring
  have hbound : ∀ n, intervalUnitProductProbability (E n) ≤ ENNReal.ofReal (g n) := by
    intro n
    exact intervalUnitProductProbability_roughPolynomial_smallBall hQ (by linarith) β M n
  have htsumLe : (∑' n, intervalUnitProductProbability (E n)) ≤
      ∑' n, ENNReal.ofReal (g n) := ENNReal.tsum_le_tsum hbound
  have hfinite : (∑' n, intervalUnitProductProbability (E n)) ≠ ∞ :=
    ne_top_of_le_ne_top hg.tsum_ofReal_ne_top htsumLe
  filter_upwards [MeasureTheory.ae_eventually_notMem hfinite] with u hu
  filter_upwards [hu] with n hn
  simpa only [E, Set.mem_setOf_eq, not_le] using hn

theorem ae_logarithmicallyShiftSeparated_roughPolynomialProfile
    {α : ℝ} (hα : 1 < α) (β : ℝ) :
    ∀ᵐ u ∂intervalUnitProductProbability,
      LogarithmicallyShiftSeparated (roughPolynomialProfile β α u) := by
  let encode : Polynomial ℤ → (ℕ →₀ ℤ) := fun Q => Q.toFinsupp
  letI : Countable (Polynomial ℤ) :=
    (show Function.Injective encode from Polynomial.toFinsupp_injective).countable
  simp only [LogarithmicallyShiftSeparated]
  rw [ae_all_iff]
  intro Q
  by_cases hQ : Q = 0
  · exact ae_of_all _ fun _u hQne => (hQne hQ).elim
  have hM : ∀ M : ℕ, ∀ᵐ u ∂intervalUnitProductProbability,
      ∀ᶠ n : ℕ in atTop,
        (M : ℝ) * Real.log ((n : ℝ) + 3) <
          |∑ j ∈ Finset.range (Q.natDegree + 1),
            (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + 1 + j)| :=
    fun M => ae_eventually_roughPolynomialShift_gt hQ hα β M
  filter_upwards [ae_all_iff.2 hM] with u hu
  intro _hQ
  let v : ℕ → ℝ := fun n =>
    |∑ j ∈ Finset.range (Q.natDegree + 1),
      (Q.coeff j : ℝ) * roughPolynomialProfile β α u (n + j)| /
        Real.log ((n : ℝ) + 2)
  have hshift : Tendsto (fun n : ℕ => v (n + 1)) atTop atTop := by
    rw [tendsto_atTop]
    intro A
    obtain ⟨M : ℕ, hMgt : A < M⟩ := exists_nat_gt A
    filter_upwards [hu M] with n hn
    have hlogpos : 0 < Real.log ((n : ℝ) + 3) := Real.log_pos (by linarith)
    have hratio : (M : ℝ) < v (n + 1) := by
      change (M : ℝ) <
        |∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u ((n + 1) + j)| /
            Real.log ((((n + 1 : ℕ) : ℝ)) + 2)
      rw [show (((n + 1 : ℕ) : ℝ)) + 2 = (n : ℝ) + 3 by push_cast; ring]
      simpa only [Nat.add_assoc] using (lt_div_iff₀ hlogpos).2 hn
    exact hMgt.le.trans hratio.le
  rw [tendsto_atTop] at hshift ⊢
  intro A
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hshift A)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hNm : N ≤ n - 1 := by omega
  have hv := hN (n - 1) hNm
  have hnpos : 1 ≤ n := by omega
  simpa [v, Nat.sub_add_cancel hnpos] using hv

theorem eventually_const_mul_natCast_add_rpow_add_log_lt_const_mul_natCast_rpow
    {α γ A C c : ℝ} (hα : 0 ≤ α) (hαγ : α < γ)
    (hc : 0 < c) (B : ℕ) :
    ∀ᶠ q : ℕ in atTop,
      A * (((q + B : ℕ) : ℝ) ^ α) + C * Real.log ((q : ℝ) + 2) <
        c * (q : ℝ) ^ γ := by
  have hγ : 0 < γ := hα.trans_lt hαγ
  have hsame := tendsto_natCast_add_rpow_div_rpow (β := α) B
  have hpowRatio : Tendsto (fun q : ℕ => (q : ℝ) ^ α / (q : ℝ) ^ γ)
      atTop (𝓝 0) := by
    have hneg := tendsto_rpow_neg_atTop (sub_pos.mpr hαγ)
    have hcomp := hneg.comp tendsto_natCast_atTop_atTop
    convert hcomp using 1
    funext q
    by_cases hq : q = 0
    · subst q
      simp [hγ.ne', Real.zero_rpow (by linarith : α - γ ≠ 0)]
    · have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.pos_iff_ne_zero.mpr hq)
      rw [← Real.rpow_sub hqpos]
      congr 1
      ring
  have hshiftRatio : Tendsto
      (fun q : ℕ => (((q + B : ℕ) : ℝ) ^ α) / (q : ℝ) ^ γ)
      atTop (𝓝 0) := by
    have hmul := hsame.mul hpowRatio
    have hmul' : Tendsto
        (fun q : ℕ => (((q + B : ℕ) : ℝ) ^ α / (q : ℝ) ^ α) *
          ((q : ℝ) ^ α / (q : ℝ) ^ γ)) atTop (𝓝 0) := by
      simpa using hmul
    refine hmul'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with q hq
    have hqpowα : (q : ℝ) ^ α ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < q by omega)) α)
    field_simp
  have hlogRatio := tendsto_log_nat_add_two_div_rpow hγ
  have htotal : Tendsto (fun q : ℕ =>
      (A * (((q + B : ℕ) : ℝ) ^ α) + C * Real.log ((q : ℝ) + 2)) /
        (q : ℝ) ^ γ) atTop (𝓝 0) := by
    have h := (hshiftRatio.const_mul A).add (hlogRatio.const_mul C)
    have h' : Tendsto (fun q : ℕ =>
        A * ((((q + B : ℕ) : ℝ) ^ α) / (q : ℝ) ^ γ) +
          C * (Real.log ((q : ℝ) + 2) / (q : ℝ) ^ γ)) atTop (𝓝 0) := by
      simpa using h
    refine h'.congr' ?_
    filter_upwards with q
    ring
  have hsmall := htotal.eventually_lt_const hc
  filter_upwards [hsmall, eventually_ge_atTop 1] with q hq hqone
  have hqpow : 0 < (q : ℝ) ^ γ :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < q by omega)) γ
  exact (div_lt_iff₀ hqpow).mp hq

theorem finsupp_purePowerValuation_le_roughPolynomialProfile
    {β α : ℝ} {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i)
    (ν : ℕ →₀ ℕ) :
    ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) ≤
      ν.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) := by
  apply Finsupp.sum_le_sum
  intro i hi
  dsimp [roughPolynomialProfile]
  have hrough : 0 ≤ (i : ℝ) ^ α * u i :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg i) α) (hu i)
  nlinarith [show (0 : ℝ) ≤ ν i by positivity]

theorem key_roughPolynomialProfileValuation
    (β α : ℝ) (u : ℕ → ℝ) {D : ℕ} (t : Fin D → ℕ) :
    (key t).sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) =
      tuplePowerValuation β t + ∑ i, (t i : ℝ) ^ α * u (t i) := by
  rw [valuation_eq_key_sum, tuplePowerValuation]
  simp_rw [roughPolynomialProfile]
  rw [Finset.sum_add_distrib]

theorem roughTupleValuation_le_two_mul
    {α : ℝ} (hα : 0 ≤ α) {u : ℕ → ℝ}
    (hu2 : ∀ i, u i ≤ 2) {D q B : ℕ} (t : Fin D → ℕ)
    (ht : ∀ i, t i ≤ q + B) :
    (∑ i, (t i : ℝ) ^ α * u (t i)) ≤
      2 * (D : ℝ) * (((q + B : ℕ) : ℝ) ^ α) := by
  calc
    (∑ i, (t i : ℝ) ^ α * u (t i)) ≤
        ∑ _i : Fin D, 2 * (((q + B : ℕ) : ℝ) ^ α) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpow : (t i : ℝ) ^ α ≤ (((q + B : ℕ) : ℝ)) ^ α := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast ht i) hα
      calc
        (t i : ℝ) ^ α * u (t i) ≤ (t i : ℝ) ^ α * 2 :=
          mul_le_mul_of_nonneg_left (hu2 (t i))
            (Real.rpow_nonneg (Nat.cast_nonneg _) α)
        _ ≤ (((q + B : ℕ) : ℝ)) ^ α * 2 :=
          mul_le_mul_of_nonneg_right hpow (by norm_num)
        _ = 2 * (((q + B : ℕ) : ℝ)) ^ α := by ring
    _ = 2 * (D : ℝ) * (((q + B : ℕ) : ℝ) ^ α) := by simp; ring

set_option maxHeartbeats 800000 in
theorem exists_eventually_roughPolynomial_bend_pair_of_positiveJetDegree
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (hu2 : ∀ i, u i ≤ 2)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-roughPolynomialProfile β α u i))
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hrel : aeval (formalJets n F) Q = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ D K C Q₀ : ℕ,
      D = magnitudeMaxJetDegree n Q ∧ 0 < D ∧ 0 < C ∧ ∀ q ≥ Q₀,
      ∃ ν₀ ν₁ : ℕ →₀ ℕ,
        ν₀ ≠ ν₁ ∧
        ν₀.sum (fun _ k => k) = D ∧ ν₁.sum (fun _ k => k) = D ∧
        (∀ i, ν₀ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        (∀ i, ν₁ i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∧
        0 ≤ ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) -
          ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) ∧
        ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) -
            ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
          (C : ℝ) * Real.log ((q : ℝ) + 2) := by
  classical
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  obtain ⟨anchor, ha, haD, haMax⟩ :=
    exists_maxShiftCode_topDegree_anchor Q hDpos
  let D := jetMonomialDegree n anchor
  have hDmax : D = magnitudeMaxJetDegree n Q := by simpa [D] using haD
  have hD : 0 < D := by rw [hDmax]; exact hDpos
  have haPos : 0 < jetMonomialDegree n anchor := by simpa [D] using hD
  obtain ⟨δ, _hδinj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  let J := jetMonomialOrder n anchor
  let Boff := magnitudeOffsetMax δ
  let E := D + O
  let C := E + 1
  let Csum := magnitudeShiftCode n Q anchor
  let Amass : ℝ := magnitudeCoefficientMass Q * (((O + 1) ^ O : ℕ) : ℝ)
  have hCoeffMass : 0 < magnitudeCoefficientMass Q := by
    rw [magnitudeCoefficientMass]
    exact Finset.sum_pos' (fun _ _ => norm_nonneg _)
      ⟨anchor, ha, norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp ha)⟩
  have hAmass : 0 < Amass := by
    dsimp [Amass]
    exact mul_pos hCoeffMass (by positivity)
  obtain ⟨cdeg, hcdeg, hdegEv⟩ :=
    eventually_lowerDegree_tuplePower_rpow_gap
      (by linarith : 1 < β) hD δ (J + Z)
  obtain ⟨K, cconf, hcconf, hconfEv⟩ :=
    exists_eventually_bounded_powerGap (by linarith : 2 < β) hD δ Csum
  let Arough : ℝ := 2 * D
  have hdomDeg : ∀ᶠ q : ℕ in atTop,
      Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
          (C : ℝ) * Real.log ((q : ℝ) + 2) <
        cdeg * (q : ℝ) ^ β := by
    exact eventually_const_mul_natCast_add_rpow_add_log_lt_const_mul_natCast_rpow
      (by linarith : 0 ≤ α) (by linarith : α < β)
        hcdeg Boff
  have hdomConf : ∀ᶠ q : ℕ in atTop,
      Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
          (C : ℝ) * Real.log ((q : ℝ) + 2) <
        cconf * (q : ℝ) ^ (β - 2) := by
    exact eventually_const_mul_natCast_add_rpow_add_log_lt_const_mul_natCast_rpow
      (by linarith : 0 ≤ α) hαcurv hcconf Boff
  obtain ⟨Qdeg, hQdeg⟩ := Filter.eventually_atTop.mp hdegEv
  obtain ⟨Qconf, hQconf⟩ := Filter.eventually_atTop.mp hconfEv
  obtain ⟨QdomDeg, hQdomDeg⟩ := Filter.eventually_atTop.mp hdomDeg
  obtain ⟨QdomConf, hQdomConf⟩ := Filter.eventually_atTop.mp hdomConf
  let Llevel := D * (Boff + 1) + anchor 0 + 1
  have hLlevel : 0 < Llevel := by dsimp [Llevel]; omega
  have hlargeEv : ∀ᶠ q : ℕ in atTop,
      Amass * (Llevel : ℝ) ^ E + 1 ≤ (q : ℝ) + 2 :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop
      (Amass * (Llevel : ℝ) ^ E + 1)
  obtain ⟨Qlarge, hQlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  let Q₀ := max Qbal (max Qdeg (max Qconf (max QdomDeg (max QdomConf
    (max Qlarge (max (2 * (J + Z) + 2) 2))))))
  refine ⟨D, K, C, Q₀, hDmax, hD, by dsimp [C, E]; omega, fun q hq => ?_⟩
  have hqbal : Qbal ≤ q := by dsimp [Q₀] at hq; omega
  have hqdeg : Qdeg ≤ q := by dsimp [Q₀] at hq; omega
  have hqconf : Qconf ≤ q := by dsimp [Q₀] at hq; omega
  have hqdomDeg : QdomDeg ≤ q := by dsimp [Q₀] at hq; omega
  have hqdomConf : QdomConf ≤ q := by dsimp [Q₀] at hq; omega
  have hqlarge : Qlarge ≤ q := by dsimp [Q₀] at hq; omega
  have hqthreshold : 2 * (J + Z) + 2 ≤ q := by dsimp [Q₀] at hq; omega
  have hq2 : 2 ≤ q := by dsimp [Q₀] at hq; omega
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hqJ : J ≤ q := by omega
  have hqsum : q ≤ ∑ i, s i := by
    obtain ⟨i₀⟩ : Nonempty (Fin (jetMonomialDegree n anchor)) :=
      Fin.pos_iff_nonempty.mp haPos
    calc
      q ≤ s i₀ := by simp [s]
      _ ≤ ∑ i, s i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i₀)
  have hJsum : J ≤ (∑ i, s i) + anchor 0 :=
    hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hDqN : D * q ≤ N + J := by
    rw [hNadd]
    have hsLower : D * q ≤ ∑ i, s i := by
      calc
        D * q = ∑ _i : Fin (jetMonomialDegree n anchor), q := by simp [D]
        _ ≤ ∑ i, s i := by
          apply Finset.sum_le_sum
          intro i _
          simp [s]
    omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by omega
    have hqD : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    dsimp [Z]
    change magnitudeMaxXDegree Q < N
    omega
  obtain ⟨hνw, hww, _hgroup⟩ :
      key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q (key s) ≠ 0 ∧
        balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
          topShiftJetGroup n Q anchor := by
    simpa only [s, N, J] using hbalanced q hqbal
  let P : ℝ := Amass * (((N + 1) ^ E : ℕ) : ℝ)
  have hsUpper : (∑ i, s i) ≤ D * (q + Boff) := by
    calc
      ∑ i : Fin (jetMonomialDegree n anchor), s i ≤
          ∑ _i : Fin (jetMonomialDegree n anchor), (q + Boff) := by
            apply Finset.sum_le_sum
            intro i _
            dsimp [s]
            exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
      _ = D * (q + Boff) := by simp [D]
  have hNupper : N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := by
    dsimp [N]
    omega
  have hlevel : N + 1 ≤ Llevel * (q + 1) := by
    have hbaseNat : q + Boff ≤ (Boff + 1) * (q + 1) := by
      calc
        q + Boff ≤ q + Boff + (Boff * q + 1) := Nat.le_add_right _ _
        _ = (Boff + 1) * (q + 1) := by ring
    have hjet : D * (q + Boff) ≤ D * (Boff + 1) * (q + 1) := by
      calc
        D * (q + Boff) ≤ D * ((Boff + 1) * (q + 1)) :=
          Nat.mul_le_mul_left D hbaseNat
        _ = D * (Boff + 1) * (q + 1) := by ring
    have hconst : anchor 0 + 1 ≤ (anchor 0 + 1) * (q + 1) := by
      calc
        anchor 0 + 1 ≤ (anchor 0 + 1) + (anchor 0 + 1) * q := Nat.le_add_right _ _
        _ = (anchor 0 + 1) * (q + 1) := by ring
    calc
      N + 1 ≤ D * (q + Boff) + anchor 0 + 1 := hNupper
      _ ≤ D * (Boff + 1) * (q + 1) + (anchor 0 + 1) * (q + 1) := by omega
      _ = Llevel * (q + 1) := by dsimp [Llevel]; ring
  have hP0 : 0 < P := by dsimp [P]; positivity
  obtain ⟨ν₀, ν₁, hν₀, hw₀, hmin, hν₁, hw₁, hne, hgap⟩ :=
    exists_near_min_nonzero_aevalWeight_of_relation F Q hb hQint hrel hνw hww
  have hgapP : ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
      ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) +
        Real.log (P + 1) := by
    simpa [P, Amass, E, O, hDmax] using hgap
  have hlogpos : 0 < Real.log (P + 1) := Real.log_pos (by linarith)
  have hν₀near : ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
      (key s).sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) +
        Real.log (P + 1) :=
    (hmin (key s) hνw hww).trans_lt (lt_add_of_pos_right _ hlogpos)
  have hν₁near : ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
      (key s).sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) +
        Real.log (P + 1) :=
    hgapP.trans_le (add_le_add (hmin (key s) hνw hww) le_rfl)
  have hlogBound : Real.log (P + 1) ≤ (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have := log_polynomial_mass_le_mul_log hAmass.le hlevel (hQlarge q hqlarge)
    simpa [P, C, Amass, E] using this
  have hsOffset : ∀ i, s i ≤ q + Boff := by
    intro i
    dsimp [s]
    exact Nat.add_le_add_left (offset_le_magnitudeOffsetMax δ i) q
  have hroughWit : (∑ i, (s i : ℝ) ^ α * u (s i)) ≤
      Arough * (((q + Boff : ℕ) : ℝ) ^ α) := by
    simpa [Arough, D] using roughTupleValuation_le_two_mul
      (by linarith : 0 ≤ α) hu2 s hsOffset
  have hwitVal :
      (key s).sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) =
        tuplePowerValuation β s + ∑ i, (s i : ℝ) ^ α * u (s i) :=
    key_roughPolynomialProfileValuation β α u s
  have hν₀pure := finsupp_purePowerValuation_le_roughPolynomialProfile
    (β := β) (α := α)
      (fun i => (zero_le_one.trans (hu1 i))) ν₀
  have hν₁pure := finsupp_purePowerValuation_le_roughPolynomialProfile
    (β := β) (α := α)
      (fun i => (zero_le_one.trans (hu1 i))) ν₁
  have hν₀nearPure :
      ν₀.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) <
        tuplePowerValuation β s +
          Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
            (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    rw [hwitVal] at hν₀near
    linarith
  have hν₁nearPure :
      ν₁.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) <
        tuplePowerValuation β s +
          Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
            (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    rw [hwitVal] at hν₁near
    linarith
  have count_eq_top (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hnear : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) <
        tuplePowerValuation β s + Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
          (C : ℝ) * Real.log ((q : ℝ) + 2)) :
      ν.sum (fun _ k => k) = D := by
    have hcountle := appearing_atom_count_le Q hν
    change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
    rw [← hDmax] at hcountle
    rcases hcountle.eq_or_lt with heq | hlt
    · exact heq
    · let d := ν.sum (fun _ k => k)
      have hdD : d < D := by simpa [d] using hlt
      have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level Q hν
        (by simpa [Z] using hNZ)
      have hd : 0 < d := by
        by_contra hd0
        have hdEq : d = 0 := Nat.eq_zero_of_not_pos hd0
        obtain ⟨i, hi⟩ := hsupport
        have hiBound := finsupp_apply_le_count ν i
        have hiNe : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
        apply hiNe
        apply Nat.eq_zero_of_le_zero
        rw [← hdEq]
        simpa [d] using hiBound
      let t : Fin d → ℕ := tupleOfFinsupp ν d (by rfl)
      have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
      change N - Z ≤ ν.sum (fun i k => i * k) at hweightLower
      have hsumt := sum_tupleOfFinsupp ν d (by rfl)
      have hmass : D * q ≤ (∑ i, t i) + (J + Z) := by
        rw [show (∑ i, t i) = ν.sum (fun i k => i * k) by simpa [t] using hsumt]
        have hNsplit : N - Z + Z = N := Nat.sub_add_cancel hNZ.le
        omega
      have hνval : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
          tuplePowerValuation β t := by
        rw [valuation_tupleOfFinsupp ν d (by rfl)]
        rfl
      have hsep := hQdeg q hqdeg d hd hdD t hmass
      rw [hνval] at hnear
      have hdom := hQdomDeg q hqdomDeg
      exact False.elim (by linarith)
  have hν₀count := count_eq_top ν₀ hν₀ hν₀nearPure
  have hν₁count := count_eq_top ν₁ hν₁ hν₁nearPure
  have tuple_bounds (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hcount : ν.sum (fun _ k => k) = D) :
      let t := tupleOfFinsupp ν D hcount
      D * q + (∑ i, δ i) ≤ ∑ i, t i ∧
        (∑ i, t i) ≤ D * q + (∑ i, δ i) + Csum := by
    dsimp only
    obtain ⟨m, hm, hmD, hinv⟩ := appearing_atom_sum_add_shiftCode Q hν
    have hmTop : jetMonomialDegree n m = magnitudeMaxJetDegree n Q := by
      rw [hmD, hcount]
      exact hDmax
    have hcodele := haMax m hm hmTop
    have hwitinv := witness_sum_add_shiftCode Q ha δ N rfl (hqJ.trans hqsum)
    have hsumt := sum_tupleOfFinsupp ν D hcount
    have hsEq : (∑ i, s i) = D * q + ∑ i, δ i := by
      simp [s, D, Finset.sum_add_distrib]
    change ν.sum (fun i k => i * k) + magnitudeShiftCode n Q m = N + O at hinv
    change (∑ i, s i) + Csum = N + O at hwitinv
    change magnitudeShiftCode n Q m ≤ Csum at hcodele
    constructor <;> rw [hsumt] <;> omega
  have confined (ν : ℕ →₀ ℕ)
      (hν : ν ∈ (sigmaIdx n N Q).image (atomKeyOf n))
      (hcount : ν.sum (fun _ k => k) = D)
      (hnear : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) <
        tuplePowerValuation β s + Arough * (((q + Boff : ℕ) : ℝ) ^ α) +
          (C : ℝ) * Real.log ((q : ℝ) + 2)) :
      ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
    let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
    have hνval : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
        tuplePowerValuation β t := by
      rw [valuation_tupleOfFinsupp ν D hcount]
      rfl
    have hsval : tuplePowerValuation β s =
        tuplePowerValuation β (fun i => q + δ i) := by rfl
    have hbounds := tuple_bounds ν hν hcount
    have hwindow : tupleInWindow q K t := by
      by_contra hout
      have hgap := hQconf q hqconf t hbounds hout
      have hdom := hQdomConf q hqdomConf
      rw [hνval, hsval] at hnear
      linarith
    exact support_window_of_key_tupleInWindow t hwindow
      (key_tupleOfFinsupp ν D hcount)
  have hν₀window := confined ν₀ hν₀ hν₀count hν₀nearPure
  have hν₁window := confined ν₁ hν₁ hν₁count hν₁nearPure
  have hdiff0 : 0 ≤
      ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) -
        ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) :=
    sub_nonneg.mpr (hmin ν₁ hν₁ hw₁)
  have hdiff :
      ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) -
          ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
        (C : ℝ) * Real.log ((q : ℝ) + 2) := by
    have : ν₁.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) -
        ν₀.sum (fun i k => (k : ℝ) * roughPolynomialProfile β α u i) <
          Real.log (P + 1) := by
      linarith
    exact this.trans_le hlogBound
  exact ⟨ν₀, ν₁, hne.symm, hν₀count, hν₁count,
    hν₀window, hν₁window, hdiff0, hdiff⟩

theorem exists_roughPolynomial_resonancePolynomial_of_positiveJetDegree_relation
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (hu2 : ∀ i, u i ≤ 2)
    {n : ℕ} (F : PowerSeries ℂ)
    (hb : ∀ i, ‖PowerSeries.coeff i F‖ =
      Real.exp (-roughPolynomialProfile β α u i))
    (R : MvPolynomial (Fin (n + 2)) ℂ)
    (hRint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m R = (z : ℂ))
    (hrel : aeval (formalJets n F) R = 0)
    (hDpos : 0 < magnitudeMaxJetDegree n R) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u (q k + j) ∧
        (∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u (q k + j)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨D, K, C, Q₀, hDmax, hD, hC, hpairs⟩ :=
    exists_eventually_roughPolynomial_bend_pair_of_positiveJetDegree
      hα1 hαcurv hu1 hu2 F hb R hRint hrel hDpos
  obtain ⟨p₀, p₁, hpne, hsum₀, hsum₁, q, hq, hdefect⟩ :=
    exists_persistent_atomWindow_resonance hpairs
  let Q : Polynomial ℤ := atomPatternDifferencePolynomial p₀ p₁
  have hQ : Q ≠ 0 := atomPatternDifferencePolynomial_ne_zero hpne
  have hQone : Q.eval 1 = 0 :=
    atomPatternDifferencePolynomial_eval_one p₀ p₁ (hsum₀.trans hsum₁.symm)
  refine ⟨Q, C, K, q, hQ, hQone, hq, fun k => ?_⟩
  have hsum := sum_range_atomPatternDifferencePolynomial (M := 2 * K + 1)
    (by omega) p₀ p₁ (roughPolynomialProfile β α u) (q k)
  constructor
  · rw [hsum]
    exact (hdefect k).1
  · rw [hsum]
    exact (hdefect k).2

theorem exists_roughPolynomial_resonancePolynomial_of_differentiallyAlgebraic
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (hu2 : ∀ i, u i ≤ 2)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-roughPolynomialProfile β α u i))
    (hDA : DifferentiallyAlgebraic f) :
    ∃ Q : Polynomial ℤ, ∃ C K : ℕ, ∃ q : ℕ → ℕ,
      Q ≠ 0 ∧ Q.eval 1 = 0 ∧ Tendsto q atTop atTop ∧ ∀ k,
        0 ≤ ∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u (q k + j) ∧
        (∑ j ∈ Finset.range (Q.natDegree + 1),
          (Q.coeff j : ℝ) * roughPolynomialProfile β α u (q k + j)) <
          (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := by
  obtain ⟨n, P, hP, hPfun⟩ := hDA
  have hjz : jetFun f n P = 0 := by
    funext z
    exact hPfun z
  have hformal : aeval (formalJets n (taylorPS f)) P = 0 := by
    rw [← taylorPS_jetFun f n hf P, hjz,
      show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl, taylorPS_const, map_zero]
  obtain ⟨n', R, hR, hRint, hrel⟩ := formal_mahler_integer_normalization hP hformal
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    (taylorPS f) hb R hR hRint hrel
  exact exists_roughPolynomial_resonancePolynomial_of_positiveJetDegree_relation
    hα1 hαcurv hu1 hu2 (taylorPS f) hb R hRint hrel hDpos

theorem hypertranscendental_of_roughPolynomial_logarithmicallyShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (hu2 : ∀ i, u i ≤ 2)
    (hb : ∀ i, ‖PowerSeries.coeff i (taylorPS f)‖ =
      Real.exp (-roughPolynomialProfile β α u i))
    (hsep : LogarithmicallyShiftSeparated (roughPolynomialProfile β α u)) :
    Hypertranscendental f := by
  intro hDA
  obtain ⟨Q, C, K, q, hQ, _hQone, hq, hdefect⟩ :=
    exists_roughPolynomial_resonancePolynomial_of_differentiallyAlgebraic
      hf hα1 hαcurv hu1 hu2 hb hDA
  have hsepq := (hsep Q hQ).comp hq
  have hlarge := hsepq.eventually_gt_atTop ((2 : ℝ) * C + 1)
  obtain ⟨k, hk, hqK⟩ := (hlarge.and (hq.eventually_ge_atTop K)).exists
  let S : ℝ := ∑ j ∈ Finset.range (Q.natDegree + 1),
    (Q.coeff j : ℝ) * roughPolynomialProfile β α u (q k + j)
  have hS0 : 0 ≤ S := (hdefect k).1
  have hSupper : S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) :=
    (hdefect k).2
  have hlogBound := log_nat_add_shift_le_two_mul_log hqK
  have hlogPos : 0 < Real.log ((q k : ℝ) + 2) := Real.log_pos (by
    have : (0 : ℝ) ≤ q k := by positivity
    linarith)
  have hratioUpper : |S| / Real.log ((q k : ℝ) + 2) < (2 : ℝ) * C := by
    rw [abs_of_nonneg hS0]
    rw [div_lt_iff₀ hlogPos]
    calc
      S < (C : ℝ) * Real.log (((q k + K : ℕ) : ℝ) + 2) := hSupper
      _ ≤ (C : ℝ) * (2 * Real.log ((q k : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogBound (by positivity)
      _ = (2 : ℝ) * C * Real.log ((q k : ℝ) + 2) := by ring
  change (2 : ℝ) * C + 1 < |S| / Real.log ((q k : ℝ) + 2) at hk
  linarith

def roughPolynomialFiniteCorrection (F : PowerSeries ℂ) (T : ℕ)
    (β α : ℝ) (u : ℕ → ℝ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range T,
    Polynomial.monomial i
      ((Real.exp (-roughPolynomialProfile β α u i) : ℂ) - PowerSeries.coeff i F)

@[simp]
theorem coeff_roughPolynomialFiniteCorrection (F : PowerSeries ℂ) (T : ℕ)
    (β α : ℝ) (u : ℕ → ℝ) (i : ℕ) :
    Polynomial.coeff (roughPolynomialFiniteCorrection F T β α u) i =
      if i < T then
        (Real.exp (-roughPolynomialProfile β α u i) : ℂ) - PowerSeries.coeff i F
      else 0 := by
  classical
  by_cases hi : i < T
  · simp [roughPolynomialFiniteCorrection, Polynomial.coeff_monomial, eq_comm, hi]
  · simp [roughPolynomialFiniteCorrection, Polynomial.coeff_monomial, eq_comm, hi]

theorem hypertranscendental_of_eventually_roughPolynomial_logarithmicallyShiftSeparated
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (hu2 : ∀ i, u i ≤ 2)
    (hb : ∀ᶠ i : ℕ in atTop,
      ‖PowerSeries.coeff i (taylorPS f)‖ =
        Real.exp (-roughPolynomialProfile β α u i))
    (hsep : LogarithmicallyShiftSeparated (roughPolynomialProfile β α u)) :
    Hypertranscendental f := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hb
  let F := taylorPS f
  let p := roughPolynomialFiniteCorrection F T β α u
  let g : ℂ → ℂ := fun z => f z + p.eval z
  have hp : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => p.eval z) :=
    contDiff_polynomial_eval p
  have hgsm : ContDiff ℂ (⊤ : ℕ∞) g := hf.add hp
  have htaylor : taylorPS g = F + (p : PowerSeries ℂ) := by
    change taylorPS (fun z => f z + p.eval z) = _
    rw [show (fun z => f z + p.eval z) = f + (fun z => p.eval z) from rfl,
      taylorPS_add hf hp, taylorPS_polynomial_eval]
  have hb' : ∀ i, ‖PowerSeries.coeff i (taylorPS g)‖ =
      Real.exp (-roughPolynomialProfile β α u i) := by
    intro i
    rw [htaylor, map_add, Polynomial.coeff_coe,
      coeff_roughPolynomialFiniteCorrection]
    by_cases hi : i < T
    · simp only [if_pos hi]
      rw [show PowerSeries.coeff i F +
          ((Real.exp (-roughPolynomialProfile β α u i) : ℂ) - PowerSeries.coeff i F) =
            (Real.exp (-roughPolynomialProfile β α u i) : ℂ) by ring]
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    · have hiT : T ≤ i := Nat.le_of_not_gt hi
      simp only [if_neg hi, add_zero]
      change ‖PowerSeries.coeff i F‖ = Real.exp (-roughPolynomialProfile β α u i)
      simpa only [F] using hT i hiT
  have hg := hypertranscendental_of_roughPolynomial_logarithmicallyShiftSeparated
    hgsm hα1 hαcurv hu1 hu2 hb' hsep
  exact (hypertranscendental_add_polynomial_iff hf p).mp hg

theorem ae_intervalUnitProductProbability_mem_Icc :
    ∀ᵐ u ∂intervalUnitProductProbability, ∀ i : ℕ, u i ∈ Set.Icc (1 : ℝ) 2 := by
  rw [ae_all_iff]
  intro i
  have hi : ∀ᵐ x : ℝ ∂intervalUnitProbability, x ∈ Set.Icc (1 : ℝ) 2 :=
    ae_restrict_mem measurableSet_Icc
  have heval := measurePreserving_eval_infinitePi
    (fun _ : ℕ => intervalUnitProbability) i
  exact heval.quasiMeasurePreserving.tendsto_ae.eventually hi

theorem ae_phaseUniform_hypertranscendental_roughPolynomialMagnitude
    {β α : ℝ} (hα1 : 1 < α) (hαcurv : α < β - 2) :
    ∀ᵐ u ∂intervalUnitProductProbability,
      ∀ (f : ℂ → ℂ), ContDiff ℂ (⊤ : ℕ∞) f →
        (∀ᶠ i : ℕ in atTop,
          ‖PowerSeries.coeff i (taylorPS f)‖ =
            Real.exp (-roughPolynomialProfile β α u i)) →
        Hypertranscendental f := by
  filter_upwards [ae_intervalUnitProductProbability_mem_Icc,
    ae_logarithmicallyShiftSeparated_roughPolynomialProfile hα1 β] with u hu hsep
  intro f hf hb
  exact hypertranscendental_of_eventually_roughPolynomial_logarithmicallyShiftSeparated
    hf hα1 hαcurv (fun i => (hu i).1) (fun i => (hu i).2) hb hsep

def roughPolynomialPhaseCoeff (β α : ℝ) (u θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  (Real.exp (-roughPolynomialProfile β α u n) : ℂ) *
    Complex.exp (Complex.I * (θ n : ℂ))

theorem norm_roughPolynomialPhaseCoeff (β α : ℝ) (u θ : ℕ → ℝ) (n : ℕ) :
    ‖roughPolynomialPhaseCoeff β α u θ n‖ =
      Real.exp (-roughPolynomialProfile β α u n) := by
  simp [roughPolynomialPhaseCoeff, Complex.norm_exp]

theorem roughPolynomialPhaseCoeff_ne_zero (β α : ℝ) (u θ : ℕ → ℝ) (n : ℕ) :
    roughPolynomialPhaseCoeff β α u θ n ≠ 0 := by
  simp [roughPolynomialPhaseCoeff, Complex.exp_ne_zero]

theorem purePower_le_roughPolynomialProfile
    {β α : ℝ} {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (n : ℕ) :
    (n : ℝ) ^ β ≤ roughPolynomialProfile β α u n := by
  dsimp [roughPolynomialProfile]
  exact le_add_of_nonneg_right
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α) (hu n))

theorem roughPolynomialPhaseSeries_radius_eq_top
    {β α : ℝ} (hβ : 3 < β)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (θ : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℂ
      (roughPolynomialPhaseCoeff β α u θ)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hpowT : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < β - 1)).comp tendsto_natCast_atTop_atTop
  let A : ℝ := Real.log ((r : ℝ) + 1) + 1
  have hpowLarge : ∀ᶠ n : ℕ in atTop, A ≤ (n : ℝ) ^ (β - 1) :=
    hpowT.eventually_ge_atTop A
  apply Real.summable_exp_neg_nat.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hpowLarge, eventually_ge_atTop 1] with n hn hn1
  rw [FormalMultilinearSeries.ofScalars_norm]
  rw [norm_roughPolynomialPhaseCoeff]
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (by positivity))]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr0 : 0 ≤ (r : ℝ) := NNReal.coe_nonneg r
  have hrplus : 0 < (r : ℝ) + 1 := by positivity
  have hrpow : (r : ℝ) ^ n ≤
      Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
    calc
      (r : ℝ) ^ n ≤ ((r : ℝ) + 1) ^ n :=
        pow_le_pow_left₀ hr0 (by linarith) n
      _ = Real.exp (Real.log ((r : ℝ) + 1)) ^ n := by
        rw [Real.exp_log hrplus]
      _ = Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) := by
        rw [Real.exp_nat_mul]
  have hpower : (n : ℝ) * (Real.log ((r : ℝ) + 1) + 1) ≤ (n : ℝ) ^ β := by
    have hmul := mul_le_mul_of_nonneg_left hn hnpos.le
    have hpowEq : (n : ℝ) ^ β = (n : ℝ) * (n : ℝ) ^ (β - 1) := by
      calc
        (n : ℝ) ^ β = (n : ℝ) ^ (1 + (β - 1)) := by congr 1; ring
        _ = (n : ℝ) ^ 1 * (n : ℝ) ^ (β - 1) := Real.rpow_add hnpos 1 (β - 1)
        _ = (n : ℝ) * (n : ℝ) ^ (β - 1) := by rw [Real.rpow_one]
    rw [hpowEq]
    simpa [A] using hmul
  have hprofile := purePower_le_roughPolynomialProfile
    (β := β) (α := α)
      (fun i => zero_le_one.trans (hu1 i)) n
  calc
    Real.exp (-roughPolynomialProfile β α u n) * (r : ℝ) ^ n
        ≤ Real.exp (-roughPolynomialProfile β α u n) *
            Real.exp ((n : ℝ) * Real.log ((r : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hrpow (Real.exp_pos _).le
    _ = Real.exp (-roughPolynomialProfile β α u n +
        (n : ℝ) * Real.log ((r : ℝ) + 1)) := by rw [Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by linarith)

def roughPolynomialPhaseFunction (β α : ℝ) (u θ : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (roughPolynomialPhaseCoeff β α u θ)

theorem roughPolynomialPhaseFunction_eq_tsum
    (β α : ℝ) (u θ : ℕ → ℝ) (z : ℂ) :
    roughPolynomialPhaseFunction β α u θ z =
      ∑' n, roughPolynomialPhaseCoeff β α u θ n * z ^ n := by
  simpa [roughPolynomialPhaseFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq
      (roughPolynomialPhaseCoeff β α u θ) z)

theorem contDiff_roughPolynomialPhaseFunction
    {β α : ℝ} (hβ : 3 < β)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (θ : ℕ → ℝ) :
    ContDiff ℂ (⊤ : ℕ∞) (roughPolynomialPhaseFunction β α u θ) := by
  let p := FormalMultilinearSeries.ofScalars ℂ
    (roughPolynomialPhaseCoeff β α u θ)
  have hr : p.radius = ⊤ := roughPolynomialPhaseSeries_radius_eq_top hβ hu1 θ
  have hp : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ p.sum Set.univ := by
    simpa [hr] using hp.analyticOnNhd
  exact ha.contDiff

theorem taylorPS_roughPolynomialPhaseFunction
    {β α : ℝ} (hβ : 3 < β)
    {u : ℕ → ℝ} (hu1 : ∀ i, 1 ≤ u i) (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (roughPolynomialPhaseFunction β α u θ)) =
      roughPolynomialPhaseCoeff β α u θ n := by
  exact taylorPS_ofScalarsSum_of_radius_eq_top
    (roughPolynomialPhaseCoeff β α u θ)
    (roughPolynomialPhaseSeries_radius_eq_top hβ hu1 θ) n

theorem ae_forall_phase_hypertranscendental_roughPolynomialPhaseFunction
    {β α : ℝ} (hβ : 3 < β) (hα1 : 1 < α) (hαcurv : α < β - 2) :
    ∀ᵐ u ∂intervalUnitProductProbability, ∀ θ : ℕ → ℝ,
      Hypertranscendental (roughPolynomialPhaseFunction β α u θ) := by
  filter_upwards [ae_intervalUnitProductProbability_mem_Icc,
    ae_logarithmicallyShiftSeparated_roughPolynomialProfile hα1 β] with u hu hsep
  intro θ
  apply hypertranscendental_of_roughPolynomial_logarithmicallyShiftSeparated
    (contDiff_roughPolynomialPhaseFunction hβ (fun i => (hu i).1) θ)
    hα1 hαcurv (fun i => (hu i).1) (fun i => (hu i).2) ?_ hsep
  intro i
  rw [taylorPS_roughPolynomialPhaseFunction hβ (fun i => (hu i).1),
    norm_roughPolynomialPhaseCoeff]

def firstDifferenceStencil : ℕ →₀ ℝ :=
  tupleDifference (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 0)

def secondDifferenceStencil : ℕ →₀ ℝ :=
  tupleDifference (fun i : Fin 2 => if (i : ℕ) = 0 then 2 else 0)
    (fun _ : Fin 2 => 1)

theorem polynomialPowerFiniteDifference_firstDifferenceStencil (β x : ℝ) :
    polynomialPowerFiniteDifference β firstDifferenceStencil x =
      (x + 1) ^ β - x ^ β := by
  rw [firstDifferenceStencil, polynomialPowerFiniteDifference_tupleDifference]
  simp

theorem polynomialPowerFiniteDifference_secondDifferenceStencil (β x : ℝ) :
    polynomialPowerFiniteDifference β secondDifferenceStencil x =
      (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β := by
  rw [secondDifferenceStencil, polynomialPowerFiniteDifference_tupleDifference]
  simp [Fin.sum_univ_two]
  ring

theorem polynomialPower_firstDifference_isEquivalent {β : ℝ} (hβ : 1 < β) :
    (fun x : ℝ => (x + 1) ^ β - x ^ β) ~[atTop]
      fun x => β * x ^ (β - 1) := by
  have h := polynomialPowerFiniteDifference_isEquivalent
    (β := β) firstDifferenceStencil 1
    (by
      intro k hk
      interval_cases k
      rw [firstDifferenceStencil, stretchedMoment_tupleDifference]
      simp)
    (by
      rw [firstDifferenceStencil, stretchedMoment_tupleDifference]
      norm_num)
    (descPochhammer_eval_ne_zero_of_natCast_lt (by exact_mod_cast hβ))
  have hc : polynomialPowerDifferenceCoefficient β firstDifferenceStencil 1 = β := by
    rw [polynomialPowerDifferenceCoefficient, firstDifferenceStencil,
      stretchedMoment_tupleDifference]
    norm_num [descPochhammer]
  rw [hc] at h
  simpa only [Nat.cast_one] using h.congr_left (Eventually.of_forall fun x =>
    polynomialPowerFiniteDifference_firstDifferenceStencil β x)

theorem polynomialPower_secondDifference_isEquivalent {β : ℝ} (hβ : 2 < β) :
    (fun x : ℝ => (x + 2) ^ β - 2 * (x + 1) ^ β + x ^ β) ~[atTop]
      fun x => (β * (β - 1)) * x ^ (β - 2) := by
  have h := polynomialPowerFiniteDifference_isEquivalent
    (β := β) secondDifferenceStencil 2
    (by
      intro k hk
      rw [secondDifferenceStencil, stretchedMoment_tupleDifference]
      interval_cases k <;> simp)
    (by
      rw [secondDifferenceStencil, stretchedMoment_tupleDifference]
      norm_num [Fin.sum_univ_two])
    (descPochhammer_eval_ne_zero_of_natCast_lt (by exact_mod_cast hβ))
  have hc : polynomialPowerDifferenceCoefficient β secondDifferenceStencil 2 =
      β * (β - 1) := by
    rw [polynomialPowerDifferenceCoefficient, secondDifferenceStencil,
      stretchedMoment_tupleDifference]
    norm_num [Fin.sum_univ_two, descPochhammer]
  rw [hc] at h
  simpa only [Nat.cast_ofNat] using h.congr_left (Eventually.of_forall fun x =>
    polynomialPowerFiniteDifference_secondDifferenceStencil β x)

theorem tendsto_natCast_rpow_div_rpow_of_lt
    {α γ : ℝ} (hαγ : α < γ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ α / (n : ℝ) ^ γ) atTop (𝓝 0) := by
  have hneg := tendsto_rpow_neg_atTop (sub_pos.mpr hαγ)
  have hcomp := hneg.comp tendsto_natCast_atTop_atTop
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  change (n : ℝ) ^ (-(γ - α)) = (n : ℝ) ^ α / (n : ℝ) ^ γ
  rw [← Real.rpow_sub hnpos]
  congr 1
  ring

theorem tendsto_natCast_add_rpow_div_rpow_of_lt
    {α γ : ℝ} (hαγ : α < γ) (B : ℕ) :
    Tendsto (fun n : ℕ => (((n + B : ℕ) : ℝ) ^ α) / (n : ℝ) ^ γ)
      atTop (𝓝 0) := by
  have hsame := tendsto_natCast_add_rpow_div_rpow (β := α) B
  have hratio := tendsto_natCast_rpow_div_rpow_of_lt hαγ
  have hmul := hsame.mul hratio
  have hmul' : Tendsto
      (fun n : ℕ => ((((n + B : ℕ) : ℝ) ^ α) / (n : ℝ) ^ α) *
        ((n : ℝ) ^ α / (n : ℝ) ^ γ)) atTop (𝓝 0) := by
    simpa using hmul
  refine hmul'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpow : (n : ℝ) ^ α ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) α)
  field_simp

def roughPolynomialPerturbation (α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ α * u n

theorem roughPolynomialProfile_eq_pure_add_perturbation
    (β α : ℝ) (u : ℕ → ℝ) (n : ℕ) :
    roughPolynomialProfile β α u n =
      (n : ℝ) ^ β + roughPolynomialPerturbation α u n := rfl

theorem roughPolynomialPerturbation_nonneg
    {α : ℝ} {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (n : ℕ) :
    0 ≤ roughPolynomialPerturbation α u n :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) α) (hu0 n)

theorem roughPolynomialPerturbation_le_two_rpow
    {α : ℝ} {u : ℕ → ℝ} (hu2 : ∀ n, u n ≤ 2) (n : ℕ) :
    roughPolynomialPerturbation α u n ≤ 2 * (n : ℝ) ^ α := by
  simpa [roughPolynomialPerturbation, mul_comm] using
    mul_le_mul_of_nonneg_left (hu2 n) (Real.rpow_nonneg (Nat.cast_nonneg n) α)

theorem tendsto_roughPolynomialPerturbation_div_rpow
    {α γ : ℝ} (hαγ : α < γ)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    Tendsto (fun n : ℕ => roughPolynomialPerturbation α u n / (n : ℝ) ^ γ)
      atTop (𝓝 0) := by
  have hupper := (tendsto_natCast_rpow_div_rpow_of_lt hαγ).const_mul 2
  apply squeeze_zero'
  · filter_upwards with n
    exact div_nonneg (roughPolynomialPerturbation_nonneg (α := α) hu0 n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) γ)
  · filter_upwards with n
    have hden : 0 ≤ (n : ℝ) ^ γ := Real.rpow_nonneg (Nat.cast_nonneg n) γ
    have hle := div_le_div_of_nonneg_right
      (roughPolynomialPerturbation_le_two_rpow (α := α) hu2 n) hden
    simpa [mul_div_assoc] using hle
  · simpa using hupper

theorem tendsto_roughPolynomialProfile_div_purePower
    {β α : ℝ} (hαβ : α < β)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    Tendsto (fun n : ℕ => roughPolynomialProfile β α u n / (n : ℝ) ^ β)
      atTop (𝓝 1) := by
  have hpert := tendsto_roughPolynomialPerturbation_div_rpow hαβ hu0 hu2
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := hone.add hpert
  have hfun : Tendsto
      (fun n : ℕ => roughPolynomialProfile β α u n / (n : ℝ) ^ β)
      atTop (𝓝 (1 + 0)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hden : (n : ℝ) ^ β ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) β)
    rw [roughPolynomialProfile_eq_pure_add_perturbation, add_div, div_self hden]
  simpa using hfun

def roughPolynomialFirstDifferenceError (α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  roughPolynomialPerturbation α u (n + 1) - roughPolynomialPerturbation α u n

def roughPolynomialSecondDifferenceError (α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  roughPolynomialPerturbation α u (n + 2) -
    2 * roughPolynomialPerturbation α u (n + 1) +
      roughPolynomialPerturbation α u n

theorem abs_roughPolynomialFirstDifferenceError_le
    {α : ℝ} (hα : 0 ≤ α) {u : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) (n : ℕ) :
    |roughPolynomialFirstDifferenceError α u n| ≤
      4 * (((n + 1 : ℕ) : ℝ) ^ α) := by
  have hn0 := roughPolynomialPerturbation_nonneg (α := α) hu0 n
  have hn1 := roughPolynomialPerturbation_nonneg (α := α) hu0 (n + 1)
  have hnle := roughPolynomialPerturbation_le_two_rpow (α := α) hu2 n
  have hn1le := roughPolynomialPerturbation_le_two_rpow (α := α) hu2 (n + 1)
  have hpow : (n : ℝ) ^ α ≤ (((n + 1 : ℕ) : ℝ)) ^ α := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n) hα
  calc
    |roughPolynomialFirstDifferenceError α u n| ≤
        |roughPolynomialPerturbation α u (n + 1)| +
          |roughPolynomialPerturbation α u n| := abs_sub _ _
    _ = roughPolynomialPerturbation α u (n + 1) +
        roughPolynomialPerturbation α u n := by
      rw [abs_of_nonneg hn1, abs_of_nonneg hn0]
    _ ≤ 2 * (((n + 1 : ℕ) : ℝ) ^ α) + 2 * (n : ℝ) ^ α :=
      add_le_add hn1le hnle
    _ ≤ 4 * (((n + 1 : ℕ) : ℝ) ^ α) := by nlinarith

theorem abs_roughPolynomialSecondDifferenceError_le
    {α : ℝ} (hα : 0 ≤ α) {u : ℕ → ℝ}
    (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) (n : ℕ) :
    |roughPolynomialSecondDifferenceError α u n| ≤
      8 * (((n + 2 : ℕ) : ℝ) ^ α) := by
  let r := roughPolynomialPerturbation α u
  have hr0 : ∀ k, 0 ≤ r k := roughPolynomialPerturbation_nonneg (α := α) hu0
  have hrle : ∀ k, r k ≤ 2 * (k : ℝ) ^ α :=
    roughPolynomialPerturbation_le_two_rpow (α := α) hu2
  have hpow1 : (((n + 1 : ℕ) : ℝ)) ^ α ≤ (((n + 2 : ℕ) : ℝ)) ^ α := by
    apply Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ (n + 1)) hα
  have hpow0 : (n : ℝ) ^ α ≤ (((n + 2 : ℕ) : ℝ)) ^ α := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast (show n ≤ n + 2 by omega)) hα
  calc
    |roughPolynomialSecondDifferenceError α u n| = |r (n + 2) - 2 * r (n + 1) + r n| := rfl
    _ ≤ |r (n + 2)| + |2 * r (n + 1)| + |r n| := by
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) (le_refl _))
    _ = r (n + 2) + 2 * r (n + 1) + r n := by
      rw [abs_of_nonneg (hr0 _), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (hr0 _), abs_of_nonneg (hr0 _)]
    _ ≤ 2 * (((n + 2 : ℕ) : ℝ) ^ α) +
        4 * (((n + 1 : ℕ) : ℝ) ^ α) + 2 * (n : ℝ) ^ α := by
      nlinarith [hrle (n + 2), hrle (n + 1), hrle n]
    _ ≤ 8 * (((n + 2 : ℕ) : ℝ) ^ α) := by nlinarith

theorem isLittleO_of_abs_le_const_natCast_add_rpow
    {α γ c C : ℝ} (hαγ : α < γ) (hc : c ≠ 0)
    (B : ℕ) {e : ℕ → ℝ}
    (he : ∀ n, |e n| ≤ C * (((n + B : ℕ) : ℝ) ^ α)) :
    e =o[atTop] fun n : ℕ => c * (n : ℝ) ^ γ := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hupper :=
      (tendsto_natCast_add_rpow_div_rpow_of_lt hαγ B).const_mul (C / |c|)
    refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hupper)
    · filter_upwards with n
      positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpow : 0 < (n : ℝ) ^ γ :=
        Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) γ
      have hcabs : 0 < |c| := abs_pos.mpr hc
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hnpow]
      calc
        |e n| / (|c| * (n : ℝ) ^ γ)
            ≤ (C * (((n + B : ℕ) : ℝ) ^ α)) /
                (|c| * (n : ℝ) ^ γ) :=
              div_le_div_of_nonneg_right (he n) (mul_nonneg hcabs.le hnpow.le)
        _ = (C / |c|) *
            ((((n + B : ℕ) : ℝ) ^ α) / (n : ℝ) ^ γ) := by field_simp
  · filter_upwards [eventually_ge_atTop 1] with n hn hzero
    exfalso
    apply hc
    have hnpow : (n : ℝ) ^ γ ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) γ)
    exact (mul_eq_zero.mp hzero).resolve_right hnpow

def roughPolynomialFirstDifference
    (β α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  roughPolynomialProfile β α u (n + 1) - roughPolynomialProfile β α u n

def roughPolynomialSecondDifference
    (β α : ℝ) (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  roughPolynomialProfile β α u (n + 2) -
    2 * roughPolynomialProfile β α u (n + 1) +
      roughPolynomialProfile β α u n

theorem roughPolynomialFirstDifference_isEquivalent
    {β α : ℝ} (hβ : 3 < β) (hα : 0 ≤ α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    (fun n : ℕ => roughPolynomialFirstDifference β α u n) ~[atTop]
      fun n : ℕ => β * (n : ℝ) ^ (β - 1) := by
  have hpure : (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ β - (n : ℝ) ^ β)) ~[atTop]
      (fun n : ℕ => β * (n : ℝ) ^ (β - 1)) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (polynomialPower_firstDifference_isEquivalent (show 1 < β by linarith)).comp_tendsto
        tendsto_natCast_atTop_atTop
  have herr : roughPolynomialFirstDifferenceError α u =o[atTop]
      (fun n : ℕ => β * (n : ℝ) ^ (β - 1)) := by
    apply isLittleO_of_abs_le_const_natCast_add_rpow (by linarith)
      (ne_of_gt (by linarith : 0 < β)) 1
    exact abs_roughPolynomialFirstDifferenceError_le hα hu0 hu2
  refine (hpure.add_isLittleO herr).congr_left ?_
  filter_upwards with n
  simp only [Pi.add_apply, roughPolynomialFirstDifference, roughPolynomialProfile,
    roughPolynomialFirstDifferenceError, roughPolynomialPerturbation, Nat.cast_add,
    Nat.cast_one]
  ring

theorem roughPolynomialSecondDifference_isEquivalent
    {β α : ℝ} (hβ : 3 < β) (hα : 0 ≤ α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    (fun n : ℕ => roughPolynomialSecondDifference β α u n) ~[atTop]
      fun n : ℕ => (β * (β - 1)) * (n : ℝ) ^ (β - 2) := by
  have hpure : (fun n : ℕ =>
      (((n + 2 : ℕ) : ℝ) ^ β - 2 * (((n + 1 : ℕ) : ℝ) ^ β) +
        (n : ℝ) ^ β)) ~[atTop]
      (fun n : ℕ => (β * (β - 1)) * (n : ℝ) ^ (β - 2)) := by
    simpa [Function.comp_def, Nat.cast_add] using
      (polynomialPower_secondDifference_isEquivalent (show 2 < β by linarith)).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hc : β * (β - 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt (by linarith : 0 < β)) (ne_of_gt (by linarith : 0 < β - 1))
  have herr : roughPolynomialSecondDifferenceError α u =o[atTop]
      (fun n : ℕ => (β * (β - 1)) * (n : ℝ) ^ (β - 2)) := by
    apply isLittleO_of_abs_le_const_natCast_add_rpow hαcurv hc 2
    exact abs_roughPolynomialSecondDifferenceError_le hα hu0 hu2
  refine (hpure.add_isLittleO herr).congr_left ?_
  filter_upwards with n
  simp only [Pi.add_apply, roughPolynomialSecondDifference, roughPolynomialProfile,
    roughPolynomialSecondDifferenceError, roughPolynomialPerturbation, Nat.cast_add,
    Nat.cast_ofNat]
  ring

theorem tendsto_roughPolynomialFirstDifference_ratio
    {β α : ℝ} (hβ : 3 < β) (hα : 0 ≤ α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    Tendsto
      (fun n : ℕ => roughPolynomialFirstDifference β α u n /
        (β * (n : ℝ) ^ (β - 1))) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one (v := fun n : ℕ =>
    β * (n : ℝ) ^ (β - 1)) ?_).mp
  · exact roughPolynomialFirstDifference_isEquivalent hβ hα hαcurv hu0 hu2
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_ne_zero (ne_of_gt (by linarith : 0 < β))
      (ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _))

theorem tendsto_roughPolynomialSecondDifference_ratio
    {β α : ℝ} (hβ : 3 < β) (hα : 0 ≤ α) (hαcurv : α < β - 2)
    {u : ℕ → ℝ} (hu0 : ∀ n, 0 ≤ u n) (hu2 : ∀ n, u n ≤ 2) :
    Tendsto
      (fun n : ℕ => roughPolynomialSecondDifference β α u n /
        ((β * (β - 1)) * (n : ℝ) ^ (β - 2))) atTop (𝓝 1) := by
  apply (isEquivalent_iff_tendsto_one (v := fun n : ℕ =>
    (β * (β - 1)) * (n : ℝ) ^ (β - 2)) ?_).mp
  · exact roughPolynomialSecondDifference_isEquivalent hβ hα hαcurv hu0 hu2
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_ne_zero
      (mul_ne_zero (ne_of_gt (by linarith : 0 < β))
        (ne_of_gt (by linarith : 0 < β - 1)))
      (ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _))

end
end GaloisForLFunctions
