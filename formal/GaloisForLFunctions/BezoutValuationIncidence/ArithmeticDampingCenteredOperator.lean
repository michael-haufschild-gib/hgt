import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingEntranceLaw
import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingTransitionKernel
import GaloisForLFunctions.HTGeometry.ScheffeCounting
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The centered arithmetic transition is compact on `c₀`

Positive states are indexed by `n + 1`. Coordinate convergence of the stochastic
rows upgrades to absolute row convergence by the owned counting Scheffé theorem.
The centered operator has norm at most two, and truncating its output coordinates
converges in operator norm. This controls `c₀`, not the critical pronic energy.
-/

open Finset Filter Topology
open scoped BigOperators ZeroAtInfty

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Centered rows on the positive states, indexed from zero. -/
def arithmeticDampingCenteredRow (η : ℝ) (n k : ℕ) : ℝ :=
  arithmeticDampingTransition η (n + 1) (k + 1) - arithmeticDampingEntrance η (k + 1)

private theorem adc_row_hasSum (η : ℝ) (n : ℕ) :
    HasSum (fun k => arithmeticDampingTransition η (n + 1) (k + 1)) 1 := by
  have hs : HasSum (arithmeticDampingTransition η (n + 1))
      (∑ k ∈ Icc 1 (n + 1), arithmeticDampingTransition η (n + 1) k) := by
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · apply arithmeticDampingTransition_eq_zero_of_lt
      simp only [mem_Icc] at hk
      omega
  rw [arithmeticDampingTransition_sum η (by omega)] at hs
  apply (hasSum_nat_add_iff 1).2
  simpa using hs

private theorem adc_abs_summable {η : ℝ} (hη : 0 < η) (n : ℕ) :
    Summable (fun k => |arithmeticDampingCenteredRow η n k|) :=
  GaloisForLFunctions.HTGeometry.summable_abs_sub
    (fun k => arithmeticDampingTransition_nonneg hη.le (n + 1) (k + 1))
    (fun k => arithmeticDampingEntrance_nonneg hη (k + 1))
    (adc_row_hasSum η n).summable (hasSum_arithmeticDampingEntrance hη).summable

/-- Actual stochastic rows converge to the entrance law in absolute sum. -/
theorem tendsto_tsum_abs_arithmeticDampingCenteredRow {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n => ∑' k, |arithmeticDampingCenteredRow η n k|) atTop (𝓝 0) := by
  exact GaloisForLFunctions.HTGeometry.tendsto_tsum_abs_sub_of_tendsto
    (fun n k => arithmeticDampingTransition_nonneg hη.le _ _)
    (adc_row_hasSum η) (hasSum_arithmeticDampingEntrance hη)
    (fun k => (tendsto_arithmeticDampingTransition hη (k + 1)).comp
      (tendsto_add_atTop_nat 1))

private theorem adc_abs_tsum_le_two {η : ℝ} (hη : 0 < η) (n : ℕ) :
    (∑' k, |arithmeticDampingCenteredRow η n k|) ≤ 2 := by
  calc
    (∑' k, |arithmeticDampingCenteredRow η n k|) ≤
        ∑' k, (arithmeticDampingTransition η (n + 1) (k + 1) +
          arithmeticDampingEntrance η (k + 1)) := by
      apply (adc_abs_summable hη n).tsum_le_tsum _
        ((adc_row_hasSum η n).summable.add (hasSum_arithmeticDampingEntrance hη).summable)
      intro k
      simpa only [arithmeticDampingCenteredRow,
        abs_of_nonneg (arithmeticDampingTransition_nonneg hη.le _ _),
        abs_of_nonneg (arithmeticDampingEntrance_nonneg hη _)] using
        abs_sub (arithmeticDampingTransition η (n + 1) (k + 1))
          (arithmeticDampingEntrance η (k + 1))
    _ = 2 := by
      rw [(adc_row_hasSum η n).summable.tsum_add
        (hasSum_arithmeticDampingEntrance hη).summable,
        (adc_row_hasSum η n).tsum_eq, (hasSum_arithmeticDampingEntrance hη).tsum_eq]
      ring

private def adcOfTendsto (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : C₀(ℕ, ℝ) :=
  ⟨⟨f, continuous_of_discreteTopology⟩, by
    rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]⟩

private theorem adc_abs_apply_le_norm (b : C₀(ℕ, ℝ)) (k : ℕ) : |b k| ≤ ‖b‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact b.toBCF.norm_coe_le_norm k

private theorem adc_norm_le {b : C₀(ℕ, ℝ)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k, |b k| ≤ C) : ‖b‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 fun k => by
    rw [Real.norm_eq_abs]
    exact h k

private theorem adc_pair_norm_summable {η : ℝ} (hη : 0 < η) (n : ℕ)
    (b : C₀(ℕ, ℝ)) :
    Summable (fun k => ‖arithmeticDampingCenteredRow η n k * b k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((adc_abs_summable hη n).mul_right ‖b‖)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (adc_abs_apply_le_norm b k) (abs_nonneg _)

private theorem adc_pair_bound {η : ℝ} (hη : 0 < η) (n : ℕ) (b : C₀(ℕ, ℝ)) :
    |∑' k, arithmeticDampingCenteredRow η n k * b k| ≤
      (∑' k, |arithmeticDampingCenteredRow η n k|) * ‖b‖ := by
  have hs := adc_pair_norm_summable hη n b
  calc
    |∑' k, arithmeticDampingCenteredRow η n k * b k| ≤
        ∑' k, ‖arithmeticDampingCenteredRow η n k * b k‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k, |arithmeticDampingCenteredRow η n k| * ‖b‖ := by
      apply hs.tsum_le_tsum _ ((adc_abs_summable hη n).mul_right ‖b‖)
      intro k
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (adc_abs_apply_le_norm b k) (abs_nonneg _)
    _ = (∑' k, |arithmeticDampingCenteredRow η n k|) * ‖b‖ :=
      (adc_abs_summable hη n).tsum_mul_right ‖b‖

/-- The actual centered positive-state transition on sequences vanishing at infinity. -/
def arithmeticDampingCenteredOperator {η : ℝ} (hη : 0 < η) :
    C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun b => adcOfTendsto
        (fun n => ∑' k, arithmeticDampingCenteredRow η n k * b k) (by
          refine squeeze_zero_norm (fun n => ?_)
            (by simpa only [zero_mul] using
              (tendsto_tsum_abs_arithmeticDampingCenteredRow hη).mul_const ‖b‖)
          rw [Real.norm_eq_abs]
          exact adc_pair_bound hη n b)
      map_add' := fun b c => ZeroAtInftyContinuousMap.ext fun n => by
        change (∑' k, arithmeticDampingCenteredRow η n k * (b k + c k)) =
          (∑' k, arithmeticDampingCenteredRow η n k * b k) +
            ∑' k, arithmeticDampingCenteredRow η n k * c k
        simp_rw [mul_add]
        exact (adc_pair_norm_summable hη n b).of_norm.tsum_add
          (adc_pair_norm_summable hη n c).of_norm
      map_smul' := fun a b => ZeroAtInftyContinuousMap.ext fun n => by
        change (∑' k, arithmeticDampingCenteredRow η n k * (a * b k)) =
          a * ∑' k, arithmeticDampingCenteredRow η n k * b k
        calc
          _ = ∑' k, a * (arithmeticDampingCenteredRow η n k * b k) :=
            tsum_congr fun k => by ring
          _ = _ := (adc_pair_norm_summable hη n b).of_norm.tsum_mul_left a }
    2 fun b => by
      refine adc_norm_le (by positivity) fun n => ?_
      exact (adc_pair_bound hη n b).trans
        (mul_le_mul_of_nonneg_right (adc_abs_tsum_le_two hη n) (norm_nonneg b))

@[simp] theorem arithmeticDampingCenteredOperator_apply {η : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (n : ℕ) :
    arithmeticDampingCenteredOperator hη b n =
      ∑' k, arithmeticDampingCenteredRow η n k * b k := rfl

/-- The norm bound uses only positivity and the exact two unit masses. -/
theorem norm_arithmeticDampingCenteredOperator_le {η : ℝ} (hη : 0 < η) :
    ‖arithmeticDampingCenteredOperator hη‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  refine adc_norm_le (by positivity) fun n => ?_
  rw [arithmeticDampingCenteredOperator_apply]
  exact (adc_pair_bound hη n b).trans
    (mul_le_mul_of_nonneg_right (adc_abs_tsum_le_two hη n) (norm_nonneg b))

private def adcHead (N : ℕ) : C₀(ℕ, ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => LinearMap.mkContinuous
    { toFun := fun b : C₀(ℕ, ℝ) => b i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 fun b => by
      rw [one_mul, Real.norm_eq_abs]
      exact adc_abs_apply_le_norm b i

private def adcEmbed (N : ℕ) : (Fin N → ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun c => adcOfTendsto (fun k => if h : k < N then c ⟨k, h⟩ else 0)
        (tendsto_const_nhds.congr' (by
          filter_upwards [eventually_ge_atTop N] with k hk
          simp [not_lt.2 hk]))
      map_add' := fun c d => ZeroAtInftyContinuousMap.ext fun k => by
        change (if h : k < N then (c + d) ⟨k, h⟩ else 0) =
          (if h : k < N then c ⟨k, h⟩ else 0) +
            (if h : k < N then d ⟨k, h⟩ else 0)
        split_ifs <;> simp
      map_smul' := fun a c => ZeroAtInftyContinuousMap.ext fun k => by
        change (if h : k < N then (a • c) ⟨k, h⟩ else 0) =
          a * (if h : k < N then c ⟨k, h⟩ else 0)
        split_ifs <;> simp }
    1 fun c => by
      rw [one_mul]
      refine adc_norm_le (norm_nonneg c) fun k => ?_
      change |if h : k < N then c ⟨k, h⟩ else 0| ≤ ‖c‖
      split_ifs with hk
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm c ⟨k, hk⟩
      · simp

private def adcTrunc {η : ℝ} (hη : 0 < η) (N : ℕ) : C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ) :=
  (adcEmbed N).comp ((adcHead N).comp (arithmeticDampingCenteredOperator hη))

private theorem adcTrunc_apply {η : ℝ} (hη : 0 < η) (N : ℕ) (b : C₀(ℕ, ℝ)) (n : ℕ) :
    adcTrunc hη N b n = if n < N then arithmeticDampingCenteredOperator hη b n else 0 := by
  change (if h : n < N then (adcHead N (arithmeticDampingCenteredOperator hη b)) ⟨n, h⟩
    else 0) = _
  split_ifs <;> rfl

private theorem adcTrunc_compact {η : ℝ} (hη : 0 < η) (N : ℕ) :
    IsCompactOperator (adcTrunc hη N) :=
  (isCompactOperator_of_locallyCompactSpace_rng (adcEmbed N)).comp_clm
    ((adcHead N).comp (arithmeticDampingCenteredOperator hη))

private theorem adcTrunc_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (adcTrunc hη) atTop (𝓝 (arithmeticDampingCenteredOperator hη)) := by
  refine (NormedAddCommGroup.tendsto_atTop
    (β := C₀(ℕ, ℝ) →L[ℝ] C₀(ℕ, ℝ))).2 fun ε hε => ?_
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1
    (tendsto_tsum_abs_arithmeticDampingCenteredRow hη) (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN => ?_⟩
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_)
    (half_lt_self hε)
  refine adc_norm_le (by positivity) fun n => ?_
  change |adcTrunc hη N b n - arithmeticDampingCenteredOperator hη b n| ≤ (ε / 2) * ‖b‖
  rw [adcTrunc_apply]
  split_ifs with hn
  · simp only [sub_self, abs_zero]
    positivity
  · rw [zero_sub, abs_neg, arithmeticDampingCenteredOperator_apply]
    have hd := hN₀ n (by omega)
    rw [Real.dist_eq, sub_zero] at hd
    have hd' : (∑' k, |arithmeticDampingCenteredRow η n k|) ≤ ε / 2 :=
      (abs_lt.mp hd).2.le
    exact (adc_pair_bound hη n b).trans (mul_le_mul_of_nonneg_right hd' (norm_nonneg b))

/-- Every actual positive-damping centered operator is compact on `c₀`. -/
theorem isCompactOperator_arithmeticDampingCenteredOperator {η : ℝ} (hη : 0 < η) :
    IsCompactOperator (arithmeticDampingCenteredOperator hη) :=
  isCompactOperator_of_tendsto (adcTrunc_tendsto hη)
    (Eventually.of_forall (adcTrunc_compact hη))

end
end GaloisForLFunctions.BezoutValuationIncidence
