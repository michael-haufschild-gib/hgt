import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsHaveGeneralCharts
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelDivergesAtContact

/-!
# Uniform bounds in the Weil charts

A forcing in chart form has readout bounded by its sup norm at scale `V(ρ)` plus its `L¹` norm at
scale `1/ρ`. The prime translations are the only part of the forcing whose sup norm is not controlled
by the `L¹` norm of the source; they carry the small factor `V(ρ)`. Absorbing them bounds every
Riesz source, every chart forcing and every endpoint trace uniformly on compact precontact
intervals. Near each endpoint the source obeys the uniform edge law `|s(t) − τV(t)| ≤ 2A V(t)²`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

local notation "v" => logarithmicCausalKernel
local notation "V" => logarithmicRenewalMass

theorem criticalMellinAtomWeight_nonneg_chart (n : ℕ) : 0 ≤ criticalMellinAtomWeight n :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) ArithmeticFunction.vonMangoldt_nonneg

/-- The split bound with a pointwise majorant. -/
theorem norm_logarithmicBackwardConvolution_le_of_majorant {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f volume) {g : ℝ → ℝ} (hgm : Measurable g) (hg : Integrable g)
    (hg0 : ∀ y, 0 ≤ g y) {A B ρ : ℝ} (hA : 0 ≤ A) (hgA : ∀ y, g y ≤ A) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hb : ∀ᵐ y ∂volume, ‖f y‖ ≤ g y + B) (x : ℝ) :
    ‖logarithmicBackwardConvolution f x‖ ≤ A * V ρ + (∫ y, g y) / ρ + B := by
  have hgC : AEStronglyMeasurable (fun y => (g y : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp hgm).aestronglyMeasurable
  have hsplit := norm_logarithmicBackwardConvolution_le_split hgC hA hρ
    (Eventually.of_forall fun y => by
      rw [Complex.norm_real, Real.norm_of_nonneg (hg0 y)]
      exact hgA y) (Complex.ofRealCLM.integrable_comp hg) x
  have hnorm : (∫ y, ‖((g y : ℝ) : ℂ)‖) = ∫ y, g y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [Complex.norm_real, Real.norm_of_nonneg (hg0 y)]
  rw [hnorm] at hsplit
  have hk : Integrable (fun y : ℝ => v (y - x)) := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-x)).integrable_comp_of_integrable
        logarithmicCausalKernel_mass_one.1
  have hkg : Integrable (fun y : ℝ => v (y - x) * g y) :=
    hk.mul_bdd hgm.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hg0 y)]
      exact hgA y)
  have hval : ‖logarithmicBackwardConvolution (fun y => (g y : ℂ)) x‖ = ∫ y, v (y - x) * g y := by
    have he : logarithmicBackwardConvolution (fun y => (g y : ℂ)) x =
        ((∫ y, v (y - x) * g y : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      unfold logarithmicBackwardConvolution
      apply integral_congr_ae
      filter_upwards with y
      push_cast
      rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg
      (integral_nonneg fun y => mul_nonneg (logarithmicCausalKernel_nonneg _) (hg0 y))]
  rw [hval] at hsplit
  have hmass : ∫ y : ℝ, v (y - x) = 1 := by
    rw [integral_sub_right_eq_self, logarithmicCausalKernel_mass_one.2]
  calc
    _ ≤ ∫ y : ℝ, (v (y - x) * g y + v (y - x) * B) := by
      apply norm_integral_le_of_norm_le (hkg.add (hk.mul_const B))
      filter_upwards [hb] with y hy
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (logarithmicCausalKernel_nonneg _)]
      change _ ≤ v (y - x) * g y + v (y - x) * B
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hy (logarithmicCausalKernel_nonneg _)
    _ = (∫ y : ℝ, v (y - x) * g y) + B := by
      rw [integral_add hkg (hk.mul_const B), integral_mul_const, hmass, one_mul]
    _ ≤ _ := by linarith only [hsplit]

namespace ChartCutoff

/-- The cutoff commutator of a source is bounded by the `L¹` norm of the source. -/
theorem norm_commutatorIntegral_le (C : ChartCutoff) {S : ℝ → ℂ} (hS : Integrable S) (y : ℝ) :
    ‖C.commutatorIntegral S y‖ ≤ C.lip / 2 * ∫ t, ‖S t‖ := by
  have hk (t : ℝ) : ‖logarithmicCutoffKernel C.toFun y t‖ ≤ C.lip / 2 := by
    refine (norm_logarithmicCutoffKernel_le C.lip_nonneg C.lipschitz y t).trans ?_
    have h1 : Real.exp (-|y - t|) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
    have h2 : 0 ≤ C.lip / 2 := div_nonneg C.lip_nonneg (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_left h1 h2]
  unfold commutatorIntegral
  calc
    _ ≤ ∫ t, C.lip / 2 * ‖S t‖ := by
      apply norm_integral_le_of_norm_le (hS.norm.const_mul _)
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hk t) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The endpoint cutoff attached to an aperture. -/
def endpoint (a : ℝ) (ha : 0 < a) : ChartCutoff where
  toFun := logarithmicEndpointCutoff a
  continuous' := continuous_logarithmicEndpointCutoff a
  abs_le := logarithmicEndpointCutoff_abs_le a
  lip := 2 / a
  lip_nonneg := div_nonneg (by norm_num) ha.le
  lipschitz := logarithmicEndpointCutoff_lipschitz ha

/-- The linear cutoff equal to one up to `c` and vanishing from `d`. -/
def linear (c d : ℝ) (hcd : c < d) : ChartCutoff where
  toFun x := min (max ((d - x) / (d - c)) 0) 1
  continuous' := by
    have hne : d - c ≠ 0 := (sub_pos.mpr hcd).ne'
    fun_prop
  abs_le x := by
    rw [abs_of_nonneg (le_min (le_max_right _ _) zero_le_one)]
    exact min_le_right _ _
  lip := 1 / (d - c)
  lip_nonneg := (one_div_pos.mpr (sub_pos.mpr hcd)).le
  lipschitz x y := by
    have hc : LipschitzWith 1 (fun x : ℝ => min (max x 0) 1) :=
      (LipschitzWith.id.max_const 0).min_const 1
    have h := hc.dist_le_mul ((d - x) / (d - c)) ((d - y) / (d - c))
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    refine h.trans_eq ?_
    have hpos : 0 < d - c := sub_pos.mpr hcd
    rw [show (d - x) / (d - c) - (d - y) / (d - c) = -(x - y) / (d - c) by ring, abs_div, abs_neg,
      abs_of_pos hpos]
    ring

theorem linear_eq_one {c d : ℝ} (hcd : c < d) {x : ℝ} (hx : x ≤ c) :
    (linear c d hcd).toFun x = 1 := by
  have hpos : 0 < d - c := sub_pos.mpr hcd
  have h1 : 1 ≤ (d - x) / (d - c) := (one_le_div hpos).mpr (by linarith only [hx])
  exact min_eq_right (h1.trans (le_max_left _ _))

theorem linear_eq_zero {c d : ℝ} (hcd : c < d) {x : ℝ} (hx : d ≤ x) :
    (linear c d hcd).toFun x = 0 := by
  have hpos : 0 < d - c := sub_pos.mpr hcd
  have h1 : (d - x) / (d - c) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hx]) hpos.le
  change min (max ((d - x) / (d - c)) 0) 1 = 0
  rw [max_eq_right h1, min_eq_left zero_le_one]

end ChartCutoff

/-- The sup constant of the bounded convolution and polar terms. -/
def chartBoundedConstant (R T : ℝ) : ℝ := 3 / 4 + Real.exp (R / 2) + Real.exp (T / 2)

theorem chartBoundedConstant_nonneg (R T : ℝ) : 0 ≤ chartBoundedConstant R T := by
  unfold chartBoundedConstant
  positivity

private theorem integrable_exp_mul {S : ℝ → ℂ} (hS : Continuous S) (hc : HasCompactSupport S)
    (σ : ℝ) : Integrable (fun t : ℝ => (Real.exp (σ * t) : ℂ) * S t) :=
  (Continuous.mul (by fun_prop) hS).integrable_of_hasCompactSupport (hc.mul_left)

/-- The bounded terms of the forcing are controlled by the `L¹` norm of the source. -/
theorem norm_chartBounded_le {S : ℝ → ℂ} (hS : Continuous S) (hc : HasCompactSupport S) {R T y : ℝ}
    (hy0 : 0 ≤ y) (hyR : y ≤ R) (hS0 : ∀ t, t ≤ 0 → S t = 0) (hST : ∀ t, T ≤ t → S t = 0) :
    ‖chartBounded S y‖ ≤ chartBoundedConstant R T * ∫ t, ‖S t‖ := by
  have hi : Integrable S := hS.integrable_of_hasCompactSupport hc
  have hL : 0 ≤ ∫ t, ‖S t‖ := integral_nonneg fun _ => norm_nonneg _
  have h1 : ‖∫ t : ℝ, (archLogRemainder |y - t| : ℂ) * S t‖ ≤ 3 / 4 * ∫ t, ‖S t‖ := by
    calc
      _ ≤ ∫ t, 3 / 4 * ‖S t‖ := by
        apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
        refine Eventually.of_forall fun t => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLogRemainder_abs_nonneg _)]
        exact mul_le_mul_of_nonneg_right (archLogRemainder_abs_le _) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have h2 : ‖∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) * S t‖ ≤ ∫ t, ‖S t‖ := by
    apply norm_integral_le_of_norm_le hi.norm
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases ht : t ≤ 0
    · rw [hS0 t ht, norm_zero, mul_zero]
    · have he : Real.exp ((-1 / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
        linarith only [not_le.mp ht])
      nlinarith only [mul_le_mul_of_nonneg_right he (norm_nonneg (S t))]
  have h3 : ‖∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) * S t‖ ≤ Real.exp (T / 2) * ∫ t, ‖S t‖ := by
    calc
      _ ≤ ∫ t, Real.exp (T / 2) * ‖S t‖ := by
        apply norm_integral_le_of_norm_le (hi.norm.const_mul _)
        refine Eventually.of_forall fun t => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        by_cases ht : T ≤ t
        · rw [hST t ht, norm_zero, mul_zero, mul_zero]
        · exact mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (by linarith only [not_le.mp ht])) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have he1 : ‖((Real.exp ((1 / 2) * y) : ℝ) : ℂ)‖ ≤ Real.exp (R / 2) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (by linarith only [hyR])
  have he2 : ‖((Real.exp ((-1 / 2) * y) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith only [hy0])
  unfold chartBounded chartBoundedConstant
  refine (norm_sub_le _ _).trans ?_
  have h4 := norm_add_le ((Real.exp ((1 / 2) * y) : ℂ) * ∫ t : ℝ, (Real.exp ((-1 / 2) * t) : ℂ) * S t)
    ((Real.exp ((-1 / 2) * y) : ℂ) * ∫ t : ℝ, (Real.exp ((1 / 2) * t) : ℂ) * S t)
  rw [norm_mul, norm_mul] at h4
  have h5 := mul_le_mul he1 h2 (norm_nonneg _) (Real.exp_pos _).le
  have h6 := mul_le_mul he2 h3 (norm_nonneg _) zero_le_one
  nlinarith only [h1, h4, h5, h6, hL]

/-- The total mass of the prime translations over a finite set. -/
def chartPrimeMass (N : Finset ℕ) : ℝ := ∑ n ∈ N, criticalMellinAtomWeight n

theorem chartPrimeMass_nonneg (N : Finset ℕ) : 0 ≤ chartPrimeMass N :=
  Finset.sum_nonneg fun n _ => criticalMellinAtomWeight_nonneg_chart n

/-- The sup coefficient of the mass and prime terms. -/
def chartSupConstant (N : Finset ℕ) : ℝ := ‖chartMass‖ + 2 * chartPrimeMass N

theorem chartSupConstant_nonneg (N : Finset ℕ) : 0 ≤ chartSupConstant N :=
  add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (chartPrimeMass_nonneg N))

/-- The pointwise majorant of the mass and prime terms. -/
def chartMajorant (N : Finset ℕ) (S : ℝ → ℂ) (y : ℝ) : ℝ :=
  ‖chartMass‖ * ‖S y‖ + ∑ n ∈ N, criticalMellinAtomWeight n *
    (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖)

theorem continuous_chartMajorant (N : Finset ℕ) {S : ℝ → ℂ} (hS : Continuous S) :
    Continuous (chartMajorant N S) := by
  unfold chartMajorant
  fun_prop

theorem chartMajorant_nonneg (N : Finset ℕ) (S : ℝ → ℂ) (y : ℝ) : 0 ≤ chartMajorant N S y := by
  unfold chartMajorant
  exact add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Finset.sum_nonneg fun n _ =>
    mul_nonneg (criticalMellinAtomWeight_nonneg_chart n)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem norm_mass_add_prime_le (N : Finset ℕ) (S : ℝ → ℂ) (y : ℝ) :
    ‖chartMass * S y + chartPrime N S y‖ ≤ chartMajorant N S y := by
  refine (norm_add_le _ _).trans (add_le_add (by rw [norm_mul]) ?_)
  unfold chartPrime
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (criticalMellinAtomWeight_nonneg_chart n)]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (criticalMellinAtomWeight_nonneg_chart n)

theorem chartMajorant_le (N : Finset ℕ) {S : ℝ → ℂ} {M : ℝ} (hM : ∀ t, ‖S t‖ ≤ M) (y : ℝ) :
    chartMajorant N S y ≤ chartSupConstant N * M := by
  unfold chartMajorant chartSupConstant chartPrimeMass
  have h1 : ∑ n ∈ N, criticalMellinAtomWeight n * (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖) ≤
      ∑ n ∈ N, criticalMellinAtomWeight n * (2 * M) :=
    Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left
      (by linarith only [hM (y + Real.log n), hM (y - Real.log n)])
      (criticalMellinAtomWeight_nonneg_chart n)
  rw [← Finset.sum_mul] at h1
  nlinarith only [h1, mul_le_mul_of_nonneg_left (hM y) (norm_nonneg chartMass)]

theorem integral_chartMajorant_le (N : Finset ℕ) {S : ℝ → ℂ} (hi : Integrable S) {R : ℝ}
    (hR : 0 ≤ R) (hS : Continuous S) :
    (∫ y in Ico (0 : ℝ) R, chartMajorant N S y) ≤ chartSupConstant N * ∫ t, ‖S t‖ := by
  have hn : Integrable (fun t => ‖S t‖) := hi.norm
  have hshift (τ : ℝ) : Integrable (fun y => ‖S (y + τ)‖) := by
    simpa only [Function.comp_def] using
      (measurePreserving_add_right (volume : Measure ℝ) τ).integrable_comp_of_integrable hn
  have hminus (τ : ℝ) : Integrable (fun y => ‖S (y - τ)‖) := by
    simpa only [sub_eq_add_neg] using hshift (-τ)
  have hterm (n : ℕ) : Integrable (fun y => criticalMellinAtomWeight n *
      (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖)) :=
    ((hshift _).add (hminus _)).const_mul _
  have hsum : Integrable (fun y => ∑ n ∈ N, criticalMellinAtomWeight n *
      (‖S (y + Real.log n)‖ + ‖S (y - Real.log n)‖)) :=
    integrable_finsetSum _ fun n _ => hterm n
  have hmaj : Integrable (chartMajorant N S) := (hn.const_mul _).add hsum
  have hL : 0 ≤ ∫ t, ‖S t‖ := integral_nonneg fun _ => norm_nonneg _
  have _ := hR
  have _ := hS
  calc
    _ ≤ ∫ y, chartMajorant N S y :=
      setIntegral_le_integral hmaj (Eventually.of_forall (chartMajorant_nonneg N S))
    _ = ‖chartMass‖ * (∫ t, ‖S t‖) + ∑ n ∈ N, criticalMellinAtomWeight n *
        ((∫ t, ‖S t‖) + ∫ t, ‖S t‖) := by
      unfold chartMajorant
      rw [integral_add (hn.const_mul _) hsum, integral_const_mul,
        integral_finsetSum _ fun n _ => hterm n]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul, integral_add (hshift _) (hminus _),
        integral_add_right_eq_self (fun y => ‖S y‖),
        integral_sub_right_eq_self (fun y => ‖S y‖)]
    _ = _ := by
      unfold chartSupConstant chartPrimeMass
      rw [add_mul]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring

/-- **The readout of a forcing in chart form.** The sup norm of the source enters with the small
factor `V(ρ)`, its `L¹` norm with `1/ρ`. -/
theorem norm_readout_le_of_chart_form {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    {S E : ℝ → ℂ} (hS : Continuous S) (hc : HasCompactSupport S) (C : ChartCutoff) (N : Finset ℕ)
    {R T e M L ρ : ℝ} (hR0 : 0 ≤ R) (hC : ∀ x, R ≤ x → C.toFun x = 0)
    (hS0 : ∀ t, t ≤ 0 → S t = 0) (hST : ∀ t, T ≤ t → S t = 0) (he0 : 0 ≤ e)
    (he : ∀ y ∈ Ico (0 : ℝ) R, ‖E y‖ ≤ e) (hM : ∀ t, ‖S t‖ ≤ M) (hL : ∫ t, ‖S t‖ ≤ L) (hρ : 0 < ρ)
    (hf0 : ∀ᵐ y ∂volume, y < 0 → f y = 0)
    (hf1 : ∀ᵐ y ∂volume, 0 ≤ y → f y = (C.toFun y : ℂ) * (E y + chartMass * S y +
      chartBounded S y + chartPrime N S y) + C.commutatorIntegral S y) (x : ℝ) :
    ‖logarithmicBackwardConvolution f x‖ ≤
      (e + chartSupConstant N * M + chartBoundedConstant R T * L) * V ρ +
        (R * e + chartSupConstant N * L + R * (chartBoundedConstant R T * L)) / ρ +
        C.lip / 2 * L := by
  have hi : Integrable S := hS.integrable_of_hasCompactSupport hc
  have hL0 : 0 ≤ ∫ t, ‖S t‖ := integral_nonneg fun _ => norm_nonneg _
  have hLL : 0 ≤ L := hL0.trans hL
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB := chartBoundedConstant_nonneg R T
  have hK := chartSupConstant_nonneg N
  -- The compactly supported majorant.
  let h : ℝ → ℝ := fun y => e + chartBoundedConstant R T * L + chartMajorant N S y
  let g : ℝ → ℝ := (Ico (0 : ℝ) R).indicator h
  have hhc : Continuous h := continuous_const.add (continuous_chartMajorant N hS)
  have hgm : Measurable g := hhc.measurable.indicator measurableSet_Ico
  have hgi : Integrable g :=
    ((hhc.integrableOn_Icc (a := 0) (b := R)).mono_set Ico_subset_Icc_self).integrable_indicator
      measurableSet_Ico
  have hh0 (y : ℝ) : 0 ≤ h y :=
    add_nonneg (add_nonneg he0 (mul_nonneg hB hLL)) (chartMajorant_nonneg N S y)
  have hg0 (y : ℝ) : 0 ≤ g y := indicator_nonneg (fun y _ => hh0 y) y
  have hA : 0 ≤ e + chartSupConstant N * M + chartBoundedConstant R T * L :=
    add_nonneg (add_nonneg he0 (mul_nonneg hK hM0)) (mul_nonneg hB hLL)
  have hgA (y : ℝ) : g y ≤ e + chartSupConstant N * M + chartBoundedConstant R T * L := by
    by_cases hy : y ∈ Ico (0 : ℝ) R
    · change (Ico (0 : ℝ) R).indicator h y ≤ _
      rw [indicator_of_mem hy]
      dsimp only [h]
      linarith only [chartMajorant_le N hM y]
    · change (Ico (0 : ℝ) R).indicator h y ≤ _
      rw [indicator_of_notMem hy]
      exact hA
  have hBL : 0 ≤ C.lip / 2 * L := mul_nonneg (div_nonneg C.lip_nonneg (by norm_num)) hLL
  have hcomm (y : ℝ) : ‖C.commutatorIntegral S y‖ ≤ C.lip / 2 * L :=
    (C.norm_commutatorIntegral_le hi y).trans
      (mul_le_mul_of_nonneg_left hL (div_nonneg C.lip_nonneg (by norm_num)))
  have hmain := norm_logarithmicBackwardConvolution_le_of_majorant hf hgm hgi hg0 hA hgA hBL hρ
    (by
      filter_upwards [hf0, hf1] with y h0 h1
      by_cases hy : y < 0
      · rw [h0 hy, norm_zero]
        exact add_nonneg (hg0 y) hBL
      push Not at hy
      rw [h1 hy]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hcomm y))
      by_cases hyR : y < R
      · have hmem : y ∈ Ico (0 : ℝ) R := ⟨hy, hyR⟩
        change _ ≤ (Ico (0 : ℝ) R).indicator h y
        rw [indicator_of_mem hmem, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hb1 := norm_chartBounded_le hS hc hy hyR.le hS0 hST
        have hb2 : ‖chartBounded S y‖ ≤ chartBoundedConstant R T * L :=
          hb1.trans (mul_le_mul_of_nonneg_left hL hB)
        have hsum : ‖E y + chartMass * S y + chartBounded S y + chartPrime N S y‖ ≤ h y := by
          have heq : E y + chartMass * S y + chartBounded S y + chartPrime N S y =
              E y + chartBounded S y + (chartMass * S y + chartPrime N S y) := by ring
          rw [heq]
          exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add (he y hmem) hb2)) (norm_mass_add_prime_le N S y))
        calc
          _ ≤ 1 * h y := mul_le_mul (C.abs_le y) hsum (norm_nonneg _) zero_le_one
          _ = h y := one_mul _
      · rw [hC y (not_lt.mp hyR), Complex.ofReal_zero, zero_mul, norm_zero]
        exact hg0 y) x
  have hgint : (∫ y, g y) ≤ R * e + chartSupConstant N * L + R * (chartBoundedConstant R T * L) := by
    rw [integral_indicator measurableSet_Ico]
    have hmajI : IntegrableOn (chartMajorant N S) (Ico (0 : ℝ) R) :=
      ((continuous_chartMajorant N hS).integrableOn_Icc (a := 0) (b := R)).mono_set
        Ico_subset_Icc_self
    have hconstI : IntegrableOn (fun _ : ℝ => e + chartBoundedConstant R T * L) (Ico (0 : ℝ) R) :=
      (continuous_const.integrableOn_Icc (a := 0) (b := R)).mono_set Ico_subset_Icc_self
    have hsplit : (∫ y in Ico (0 : ℝ) R, h y) =
        (∫ _ in Ico (0 : ℝ) R, e + chartBoundedConstant R T * L) +
          ∫ y in Ico (0 : ℝ) R, chartMajorant N S y := integral_add hconstI hmajI
    have hconst : (∫ _ in Ico (0 : ℝ) R, e + chartBoundedConstant R T * L) =
        R * (e + chartBoundedConstant R T * L) := by
      rw [setIntegral_const, Real.volume_real_Ico_of_le hR0, smul_eq_mul, sub_zero]
    have hm := integral_chartMajorant_le N hi hR0 hS
    have hm' := mul_le_mul_of_nonneg_left hL hK
    change (∫ y in Ico (0 : ℝ) R, h y) ≤ _
    rw [hsplit, hconst]
    nlinarith only [hm, hm']
  have hdiv := div_le_div_of_nonneg_right hgint hρ.le
  linarith only [hmain, hdiv]

namespace WeilHilbertBeforeContact

/-- The chart forcing vanishes on the negative half-line. -/
theorem chartForcing_negative (C : ChartCutoff) (a : PrecontactAperture) (z : ℂ) :
    ∀ᵐ y ∂volume, y < 0 → ((chartForcing C a z : LogarithmicHalfLineL2) : RealLineL2) y = 0 :=
  (mem_halfLineL2_iff _).mp (chartForcing C a z).property

/-- Expressed in the source coordinate, the `L¹` norm is the physical `L¹` norm. -/
private theorem integral_norm_chartSource (a : PrecontactAperture) (z : ℂ) :
    (∫ t, ‖chartSource a z t‖) = ∫ x, ‖evalVectorContinuousRepresentative a z x‖ :=
  integral_sub_right_eq_self (fun x => ‖evalVectorContinuousRepresentative a z x‖) a.1.1

theorem hasCompactSupport_chartSource (a : PrecontactAperture) (z : ℂ) :
    HasCompactSupport (chartSource a z) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := 0) (b := 2 * a.1.1))
  intro t ht
  apply chartSource_eq_zero
  have hs : ¬(0 ≤ t ∧ t ≤ 2 * a.1.1) := ht
  rcases not_and_or.mp hs with h | h
  · exact Or.inl (lt_of_not_ge h).le
  · exact Or.inr (lt_of_not_ge h).le

/-- The mass of a Riesz source is controlled by the top kernel and ground energy. -/
theorem groundEnergy_mul_physical_mass_le {a c : PrecontactAperture} (hac : a.1.1 ≤ c.1.1) (z : ℂ) :
    ccmRestrictedWeilGroundEnergy c.1 *
        ∫ x, ‖evalVectorContinuousRepresentative a z x‖ ^ 2 ≤ ‖evalVector c z‖ ^ 2 := by
  let w := evalVector a z
  have hphysical :
      ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hac w)) =
        ccmArchimedeanFormEmbedding a.1 (toForm a w) := by
    rw [toForm_inclusion]
    exact ccmArchimedeanFormToAperture_coe_eq_of_val_eq
      (ArithmeticContinuationAndCriticalEnergy.apertureExt_val hac (toForm a w))
  have hf := groundEnergy_mul_mass_le c (inclusion hac w)
  rw [(inclusion hac).norm_map] at hf
  change ccmRestrictedWeilGroundEnergy c.1 *
    ‖ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hac w))‖ ^ 2 ≤ _ at hf
  rw [hphysical, Lp_two_norm_sq_eq_integral] at hf
  have hint : (∫ x, ‖ccmArchimedeanFormEmbedding a.1 (toForm a w) x‖ ^ 2) =
      ∫ x, ‖evalVectorContinuousRepresentative a z x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [evalVectorContinuousRepresentative_ae a z] with x hx
    rw [hx]
  rw [hint] at hf
  exact hf.trans (norm_evalVector_sq_mono hac z)

/-- A uniform bound for the physical `L¹` mass on compact precontact intervals. -/
theorem integral_norm_chartSource_le {a c : PrecontactAperture} (hac : a.1.1 ≤ c.1.1) (z : ℂ) :
    (∫ t, ‖chartSource a z t‖) ≤
      c.1.1 + ‖evalVector c z‖ ^ 2 / (2 * ccmRestrictedWeilGroundEnergy c.1) := by
  rw [integral_norm_chartSource]
  let U := evalVectorContinuousRepresentative a z
  have hUc : Continuous U := continuous_evalVectorContinuousRepresentative a z
  have hUs : HasCompactSupport U := hasCompactSupport_evalVectorContinuousRepresentative a z
  have hU : Integrable U := hUc.integrable_of_hasCompactSupport hUs
  have hμ := precontact_groundEnergy_pos c
  have hzero (x : ℝ) (hx : x ∉ Icc (-a.1.1) a.1.1) : U x = 0 := by
    apply evalVectorContinuousRepresentative_eq_zero
    have hs : ¬(-a.1.1 ≤ x ∧ x ≤ a.1.1) := hx
    rcases not_and_or.mp hs with h | h
    · exact Or.inl (lt_of_not_ge h).le
    · exact Or.inr (lt_of_not_ge h).le
  have hsq : Integrable (fun x => ‖U x‖ ^ 2) :=
    (hUc.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -a.1.1) (b := a.1.1)) fun x hx => by
        simp only [hzero x hx, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])
  have hle : ∫ x, ‖U x‖ ≤ ∫ x, ((Icc (-a.1.1) a.1.1).indicator (fun _ => (1 : ℝ) / 2) x +
      ‖U x‖ ^ 2 / 2) := by
    apply integral_mono hU.norm
      (((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc).add
        (hsq.div_const 2))
    intro x
    by_cases hx : x ∈ Icc (-a.1.1) a.1.1
    · change ‖U x‖ ≤ (Icc (-a.1.1) a.1.1).indicator (fun _ => (1 : ℝ) / 2) x + ‖U x‖ ^ 2 / 2
      rw [indicator_of_mem hx]
      nlinarith only [sq_nonneg (‖U x‖ - 1)]
    · change ‖U x‖ ≤ (Icc (-a.1.1) a.1.1).indicator (fun _ => (1 : ℝ) / 2) x + ‖U x‖ ^ 2 / 2
      rw [indicator_of_notMem hx, hzero x hx, norm_zero]
      norm_num
  rw [integral_add ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
    (hsq.div_const 2), integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc_of_le (by linarith only [a.1.2]), smul_eq_mul, integral_div] at hle
  have hmass := groundEnergy_mul_physical_mass_le hac z
  have hdiv : (∫ x, ‖U x‖ ^ 2) / 2 ≤ ‖evalVector c z‖ ^ 2 / (2 * ccmRestrictedWeilGroundEnergy c.1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    change ccmRestrictedWeilGroundEnergy c.1 * ∫ x, ‖U x‖ ^ 2 ≤ _ at hmass
    nlinarith only [hmass]
  have hac' : a.1.1 ≤ c.1.1 := hac
  refine hle.trans ?_
  linarith only [hdiv, hac']


/-- Two prime-power windows are compatible below the top of an interval. -/
theorem chartPrimeWindow_subset {a c : ℝ} (hac : a ≤ c) :
    Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ⊆ Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊ :=
  Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith only [hac])))

theorem chartPrimeWindow_beyond {a c : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊)
    (hn' : n ∉ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) : 2 * a ≤ Real.log n := by
  have h2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hlt : ⌊Real.exp (2 * a)⌋₊ < n := by
    by_contra hle
    exact hn' (Finset.mem_Icc.mpr ⟨h2, not_lt.mp hle⟩)
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact (Real.le_log_iff_exp_le hpos).mpr (Nat.lt_of_floor_lt hlt).le

theorem norm_exp_forcing_le (z : ℂ) {x R : ℝ} (hx : |x| ≤ R) :
    ‖Complex.exp (-I * star z * (x : ℂ))‖ ≤ Real.exp (R * |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (-I * star z * (x : ℂ)).re = -(z.im * x) := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, RCLike.star_def, Complex.conj_re, Complex.conj_im,
      Complex.mul_im]
    ring
  rw [hre]
  calc
    _ ≤ |z.im * x| := neg_le_abs _
    _ = |x| * |z.im| := by rw [abs_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- Reflection in the chart coordinate. -/
theorem chartSource_reflect (a : PrecontactAperture) (z : ℂ) (t : ℝ) :
    chartSource a z t = chartSource a (-z) (2 * a.1.1 - t) := by
  rw [chartSource, chartSource, evalVectorContinuousRepresentative_neg]
  congr 1
  ring

/-- **Uniform bounds in the Weil charts.** On a compact precontact interval, both `s^{±z}` are bounded
by one constant. The prime terms are absorbed by the small factor `V(ρ)`. -/
theorem exists_uniform_chartSource_bound (a₁ a₂ : PrecontactAperture) (z : ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : PrecontactAperture, a₁.1.1 ≤ a.1.1 → a.1.1 ≤ a₂.1.1 → ∀ t,
      ‖chartSource a z t‖ ≤ M ∧ ‖chartSource a (-z) t‖ ≤ M := by
  let N := Finset.Icc 2 ⌊Real.exp (2 * a₂.1.1)⌋₊
  let K := chartSupConstant N
  have hK : 0 ≤ K := chartSupConstant_nonneg N
  let R := 2 * a₂.1.1
  have hR : 0 ≤ R := mul_nonneg (by norm_num) a₂.1.2.le
  let B := chartBoundedConstant R R
  have hB : 0 ≤ B := chartBoundedConstant_nonneg R R
  let e := Real.exp (R * |z.im|)
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hμ := precontact_groundEnergy_pos a₂
  let L := a₂.1.1 + (‖evalVector a₂ z‖ ^ 2 + ‖evalVector a₂ (-z)‖ ^ 2) /
    (2 * ccmRestrictedWeilGroundEnergy a₂.1)
  have hL0 : 0 ≤ L := add_nonneg a₂.1.2.le (by positivity)
  -- A scale where the prime terms are absorbed.
  obtain ⟨ρ, hρ, hsmall⟩ : ∃ ρ : ℝ, 0 < ρ ∧ K * V ρ ≤ 1 / 2 := by
    have ht := (tendsto_logarithmicRenewalMass_zero.const_mul K)
    rw [mul_zero] at ht
    have hev := ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    obtain ⟨ρ, hb, hp⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨ρ, hp, (show K * V ρ < 1 / 2 from hb).le⟩
  let c₀ := (e + B * L) + (R * e + K * L + R * (B * L)) / ρ + (1 / a₁.1.1) * L
  have hc₀ : 0 ≤ c₀ := by
    have ha₁ := a₁.1.2
    dsimp only [c₀]
    positivity
  refine ⟨2 * c₀, by positivity, fun a ha₁ ha₂ => ?_⟩
  have hap : 0 < a.1.1 := a.1.2
  let C := ChartCutoff.endpoint a.1.1 hap
  have hCz : ∀ x, 2 * a.1.1 ≤ x → C.toFun x = 0 := fun x hx =>
    logarithmicEndpointCutoff_eq_zero hap (by linarith only [hx, hap])
  have hCone : ∀ x, x ≤ a.1.1 → C.toFun x = 1 := fun x hx => logarithmicEndpointCutoff_eq_one hap hx
  have hCR : ∀ x, R ≤ x → C.toFun x = 0 := fun x hx => hCz x (by
    have : 2 * a.1.1 ≤ R := by dsimp only [R]; linarith only [ha₂]
    linarith only [this, hx])
  -- The readout bound in terms of a sup bound `M` for the source.
  have hread (ζ : ℂ) (hζ : |ζ.im| = |z.im|) (hLζ : ∫ t, ‖chartSource a ζ t‖ ≤ L) (M : ℝ)
      (hM : ∀ t, ‖chartSource a ζ t‖ ≤ M) (r : ℝ) :
      ‖logarithmicBackwardConvolution
        (((chartForcing C a ζ : LogarithmicHalfLineL2) : RealLineL2) : ℝ → ℂ) r‖ ≤
        (e + K * M + B * L) * V ρ + (R * e + K * L + R * (B * L)) / ρ + C.lip / 2 * L := by
    refine norm_readout_le_of_chart_form
      (S := chartSource a ζ) (E := fun y => Complex.exp (-I * star ζ * ((y - a.1.1 : ℝ) : ℂ)))
      (Lp.stronglyMeasurable _).aestronglyMeasurable (continuous_chartSource a ζ)
      (hasCompactSupport_chartSource a ζ) C N (T := R) hR hCR
      (fun t ht => chartSource_eq_zero a ζ (Or.inl ht))
      (fun t ht => chartSource_eq_zero a ζ (Or.inr (by
        have : 2 * a.1.1 ≤ R := by dsimp only [R]; linarith only [ha₂]
        linarith only [this, ht]))) he0 ?_ hM hLζ hρ (chartForcing_negative C a ζ)
      (chartForcing_ae C a hCz ζ (chartPrimeWindow_subset ha₂) fun n hn hn' =>
        chartPrimeWindow_beyond hn hn') r
    intro y hy
    have hbd : |y - a.1.1| ≤ R := by
      apply abs_le.mpr
      have ha2 : a.1.1 ≤ a₂.1.1 := ha₂
      dsimp only [R]
      constructor <;> linarith only [hy.1, hy.2.le, hap, ha2]
    have h := norm_exp_forcing_le ζ hbd
    rwa [hζ] at h
  have hLz : ∫ t, ‖chartSource a z t‖ ≤ L := by
    refine (integral_norm_chartSource_le ha₂ z).trans ?_
    dsimp only [L]
    have hnn := sq_nonneg ‖evalVector a₂ (-z)‖
    gcongr
    linarith only [hnn]
  have hLn : ∫ t, ‖chartSource a (-z) t‖ ≤ L := by
    refine (integral_norm_chartSource_le ha₂ (-z)).trans ?_
    dsimp only [L]
    have hnn := sq_nonneg ‖evalVector a₂ z‖
    gcongr
    linarith only [hnn]
  have hzn : |(-z).im| = |z.im| := by rw [Complex.neg_im, abs_neg]
  -- The two suprema.
  have hbdd (ζ : ℂ) : BddAbove (range fun t => ‖chartSource a ζ t‖) := by
    obtain ⟨c, hc⟩ := (hasCompactSupport_chartSource a ζ).exists_bound_of_continuous
      (continuous_chartSource a ζ)
    exact ⟨c, by rintro _ ⟨t, rfl⟩; exact hc t⟩
  let Mz := ⨆ t, ‖chartSource a z t‖
  let Mn := ⨆ t, ‖chartSource a (-z) t‖
  let M := max Mz Mn
  have hMz (t : ℝ) : ‖chartSource a z t‖ ≤ M := (le_ciSup (hbdd z) t).trans (le_max_left _ _)
  have hMn (t : ℝ) : ‖chartSource a (-z) t‖ ≤ M := (le_ciSup (hbdd (-z)) t).trans (le_max_right _ _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMz 0)
  let bnd := (e + K * M + B * L) * V ρ + (R * e + K * L + R * (B * L)) / ρ + C.lip / 2 * L
  -- Every value on the left half is a Green value of the endpoint chart.
  have hleft (ζ : ℂ) (hζ : |ζ.im| = |z.im|) (hLζ : ∫ t, ‖chartSource a ζ t‖ ≤ L)
      (hMζ : ∀ t, ‖chartSource a ζ t‖ ≤ M) {t : ℝ} (ht : t ≤ a.1.1) :
      ‖chartSource a ζ t‖ ≤ bnd := by
    have hG := logarithmicGreenRepresentative_chartForcing C a hCz ζ t
    rw [hCone t ht, Complex.ofReal_one, one_mul] at hG
    rw [← hG]
    have hbn := norm_logarithmicGreenRepresentative_le (chartForcing C a ζ) (B := bnd) (x := t)
      (fun r _ => hread ζ hζ hLζ M hMζ r)
    have hb0 : 0 ≤ bnd := (norm_nonneg _).trans (hread ζ hζ hLζ M hMζ 0)
    exact hbn.trans (by
      have hV := logarithmicRenewalMass_le_one t
      nlinarith only [mul_le_mul_of_nonneg_left hV hb0])
  have hall (t : ℝ) : ‖chartSource a z t‖ ≤ bnd ∧ ‖chartSource a (-z) t‖ ≤ bnd := by
    rcases le_total t a.1.1 with ht | ht
    · exact ⟨hleft z rfl hLz hMz ht, hleft (-z) hzn hLn hMn ht⟩
    · have ht' : 2 * a.1.1 - t ≤ a.1.1 := by linarith only [ht]
      constructor
      · rw [chartSource_reflect]
        exact hleft (-z) hzn hLn hMn ht'
      · rw [chartSource_reflect, neg_neg]
        exact hleft z rfl hLz hMz ht'
  have hMle : M ≤ bnd := max_le (ciSup_le fun t => (hall t).1) (ciSup_le fun t => (hall t).2)
  -- Absorption.
  have hV := logarithmicRenewalMass_le_one ρ
  have hV0 := logarithmicRenewalMass_nonneg ρ
  have hlip : C.lip / 2 * L ≤ (1 / a₁.1.1) * L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    change (2 / a.1.1) / 2 ≤ _
    rw [show (2 / a.1.1) / 2 = 1 / a.1.1 by field_simp]
    exact one_div_le_one_div_of_le a₁.1.2 ha₁
  have hbnd : bnd ≤ M / 2 + c₀ := by
    dsimp only [bnd, c₀]
    have h1 : (e + B * L) * V ρ ≤ e + B * L :=
      mul_le_of_le_one_right (add_nonneg he0 (mul_nonneg hB hL0)) hV
    have h2 : K * M * V ρ ≤ M / 2 := by nlinarith only [hsmall, hM0]
    nlinarith only [h1, h2, hlip]
  have hfinal : M ≤ 2 * c₀ := by linarith only [hMle, hbnd]
  intro t
  exact ⟨(hMz t).trans hfinal, (hMn t).trans hfinal⟩

end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
