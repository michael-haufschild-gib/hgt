import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier
import Mathlib.MeasureTheory.Function.Holder

/-!
# Products of one-sided Hardy Riesz--Fischer reconstructions

The product of two reconstructed `H²` boundary functions is integrable.  Its nonnegative Fourier
coefficients are the finite convolutions of the two input sequences, while every negative Fourier
coefficient vanishes.  The proof uses `L²` convergence of analytic partial sums and continuous
Hölder pairing into `L¹`.
-/

open MeasureTheory Complex Filter Topology Set Finset
open scoped ENNReal NNReal lp ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private theorem circle_pow_mul_conj_pow_eq_conj_zpow_sub
    (z : Circle) (i n : ℕ) :
    (z : ℂ) ^ i * (starRingEnd ℂ) ((z : ℂ) ^ n) =
      (starRingEnd ℂ) ((z : ℂ) ^ ((n : ℤ) - (i : ℤ))) := by
  have hne : (z : ℂ) ≠ 0 := by
    intro hz
    have := congrArg norm hz
    rw [Circle.norm_coe] at this
    norm_num at this
  rw [map_pow, ← Complex.inv_eq_conj (Circle.norm_coe z)]
  rw [inv_pow]
  rw [← div_eq_mul_inv, ← zpow_natCast_sub_natCast₀ hne]
  rw [map_zpow₀]
  rw [← Complex.inv_eq_conj (Circle.norm_coe z), inv_zpow]
  rw [← zpow_neg]
  congr 1
  omega

private theorem circle_pow_mul_conj_zpow_eq_conj_zpow_sub
    (z : Circle) (i : ℕ) (k : ℤ) :
    (z : ℂ) ^ i * (starRingEnd ℂ) ((z : ℂ) ^ k) =
      (starRingEnd ℂ) ((z : ℂ) ^ (k - (i : ℤ))) := by
  have hne : (z : ℂ) ≠ 0 := by
    intro hz
    have := congrArg norm hz
    rw [Circle.norm_coe] at this
    norm_num at this
  rw [map_zpow₀, ← Complex.inv_eq_conj (Circle.norm_coe z), inv_zpow]
  rw [← zpow_natCast]
  rw [← div_eq_mul_inv, ← zpow_sub₀ hne]
  rw [map_zpow₀]
  rw [← Complex.inv_eq_conj (Circle.norm_coe z), inv_zpow]
  rw [← zpow_neg]
  congr 1
  omega

private theorem conj_circle_pow_memLp_top (n : ℕ) :
    MemLp (fun z : Circle => (starRingEnd ℂ) ((z : ℂ) ^ n)) ∞ circleLebesgue := by
  have hcont : Continuous (fun z : Circle => (starRingEnd ℂ) ((z : ℂ) ^ n)) := by
    fun_prop
  apply MemLp.of_bound hcont.aestronglyMeasurable 1
  filter_upwards with z
  rw [norm_conj, norm_pow, Circle.norm_coe, one_pow]

private theorem conj_circle_zpow_memLp_top (k : ℤ) :
    MemLp (fun z : Circle => (starRingEnd ℂ) ((z : ℂ) ^ k)) ∞ circleLebesgue := by
  have hpow : Continuous (fun z : Circle => (z : ℂ) ^ k) :=
    (continuousOn_zpow₀ k).comp_continuous continuous_subtype_val (fun z => by simp)
  apply MemLp.of_bound
    ((RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).continuous.comp hpow).aestronglyMeasurable 1
  filter_upwards with z
  change ‖(starRingEnd ℂ) ((z : ℂ) ^ k)‖ ≤ 1
  rw [norm_conj, norm_zpow, Circle.norm_coe, one_zpow]

private noncomputable def hardyZMomentFunctional
    (G : Lp ℂ 2 circleLebesgue) (k : ℤ) :
    Lp ℂ 2 circleLebesgue →L[ℂ] ℂ :=
  let q : Circle → ℂ := fun z =>
    (starRingEnd ℂ) ((z : ℂ) ^ k) * G z
  let hq : MemLp q 2 circleLebesgue := (Lp.memLp G).mul' (conj_circle_zpow_memLp_top k)
  (((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ)).lpPairing
    circleLebesgue 2 2).flip (hq.toLp q)

private theorem hardyZMomentFunctional_apply
    (G F : Lp ℂ 2 circleLebesgue) (k : ℤ) :
    hardyZMomentFunctional G k F =
      ∫ z : Circle, F z * ((starRingEnd ℂ) ((z : ℂ) ^ k) * G z) ∂circleLebesgue := by
  let q : Circle → ℂ := fun z =>
    (starRingEnd ℂ) ((z : ℂ) ^ k) * G z
  let hq : MemLp q 2 circleLebesgue := (Lp.memLp G).mul' (conj_circle_zpow_memLp_top k)
  change ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).lpPairing
    circleLebesgue 2 2 F (hq.toLp q)) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hq.coeFn_toLp] with z hz
  rw [hz]
  rfl

private theorem hardyZMomentFunctional_circleMonomial
    (B : ℕ → ℂ) (hB : Memℓp B 2) (k : ℤ) (i : ℕ) :
    hardyZMomentFunctional (circleRieszFischerOfNat B hB) k
        (circleMonomialLp circleLebesgue i) =
      nonnegativeIntExtension B (k - (i : ℤ)) := by
  rw [hardyZMomentFunctional_apply]
  rw [← circleZMonomialLp_inner_circleRieszFischerOfNat B hB (k - (i : ℤ))]
  rw [circleZMonomialLp_inner]
  apply integral_congr_ae
  filter_upwards [circleMonomialLp_coeFn_ae circleLebesgue i] with z hz
  rw [hz]
  rw [show (z : ℂ) ^ i * ((starRingEnd ℂ) ((z : ℂ) ^ k) *
      (circleRieszFischerOfNat B hB) z) =
      ((z : ℂ) ^ i * (starRingEnd ℂ) ((z : ℂ) ^ k)) *
        (circleRieszFischerOfNat B hB) z by ring]
  rw [circle_pow_mul_conj_zpow_eq_conj_zpow_sub]
  ring

private noncomputable def hardyMomentFunctional
    (G : Lp ℂ 2 circleLebesgue) (n : ℕ) :
    Lp ℂ 2 circleLebesgue →L[ℂ] ℂ :=
  let q : Circle → ℂ := fun z =>
    (starRingEnd ℂ) ((z : ℂ) ^ n) * G z
  let hq : MemLp q 2 circleLebesgue := (Lp.memLp G).mul' (conj_circle_pow_memLp_top n)
  (((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ)).lpPairing
    circleLebesgue 2 2).flip (hq.toLp q)

private theorem hardyMomentFunctional_apply
    (G F : Lp ℂ 2 circleLebesgue) (n : ℕ) :
    hardyMomentFunctional G n F =
      ∫ z : Circle, F z * ((starRingEnd ℂ) ((z : ℂ) ^ n) * G z) ∂circleLebesgue := by
  let q : Circle → ℂ := fun z =>
    (starRingEnd ℂ) ((z : ℂ) ^ n) * G z
  let hq : MemLp q 2 circleLebesgue := (Lp.memLp G).mul' (conj_circle_pow_memLp_top n)
  change ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ).lpPairing
    circleLebesgue 2 2 F (hq.toLp q)) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hq.coeFn_toLp] with z hz
  rw [hz]
  rfl

private theorem hardyMomentFunctional_circleMonomial
    (B : ℕ → ℂ) (hB : Memℓp B 2) (n i : ℕ) :
    hardyMomentFunctional (circleRieszFischerOfNat B hB) n
        (circleMonomialLp circleLebesgue i) =
      nonnegativeIntExtension B ((n : ℤ) - (i : ℤ)) := by
  rw [hardyMomentFunctional_apply]
  rw [← circleZMonomialLp_inner_circleRieszFischerOfNat B hB
    ((n : ℤ) - (i : ℤ))]
  rw [circleZMonomialLp_inner]
  apply integral_congr_ae
  filter_upwards [circleMonomialLp_coeFn_ae circleLebesgue i] with z hz
  rw [hz]
  rw [show (z : ℂ) ^ i * ((starRingEnd ℂ) ((z : ℂ) ^ n) *
      (circleRieszFischerOfNat B hB) z) =
      ((z : ℂ) ^ i * (starRingEnd ℂ) ((z : ℂ) ^ n)) *
        (circleRieszFischerOfNat B hB) z by ring]
  rw [circle_pow_mul_conj_pow_eq_conj_zpow_sub]
  ring

private theorem nonnegativeIntExtension_nat_sub_nat
    (B : ℕ → ℂ) {n i : ℕ} (hi : i ≤ n) :
    nonnegativeIntExtension B ((n : ℤ) - (i : ℤ)) = B (n - i) := by
  rw [nonnegativeIntExtension, if_pos (by omega)]
  congr 1
  omega

private theorem nonnegativeIntExtension_nat_sub_nat_eq_zero
    (B : ℕ → ℂ) {n i : ℕ} (hi : n < i) :
    nonnegativeIntExtension B ((n : ℤ) - (i : ℤ)) = 0 := by
  rw [nonnegativeIntExtension, if_neg (by omega)]

/-- The `n`th nonnegative Fourier coefficient of the product of two one-sided Riesz--Fischer
reconstructions is the finite convolution of their input sequences. -/
theorem hardyProduct_moment_convolution
    (A B : ℕ → ℂ) (hA : Memℓp A 2) (hB : Memℓp B 2) (n : ℕ) :
    (∫ z : Circle,
      (circleRieszFischerOfNat A hA) z * (circleRieszFischerOfNat B hB) z *
        (starRingEnd ℂ) ((z : ℂ) ^ n) ∂circleLebesgue) =
      ∑ i ∈ Finset.range (n + 1), A i * B (n - i) := by
  let F : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat A hA
  let G : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat B hB
  let S : ℕ → Lp ℂ 2 circleLebesgue := fun N =>
    ∑ i ∈ Finset.range N, A i • circleMonomialLp circleLebesgue i
  have hS : Tendsto S atTop (nhds F) := by
    simpa only [S, F] using
      (hasSum_circleMonomial_smul_circleRieszFischerOfNat A hA).tendsto_sum_nat
  have hpair : Tendsto (fun N => hardyMomentFunctional G n (S N)) atTop
      (nhds (hardyMomentFunctional G n F)) :=
    (hardyMomentFunctional G n).continuous.continuousAt.tendsto.comp hS
  have hevent : ∀ᶠ N in atTop, hardyMomentFunctional G n (S N) =
      ∑ i ∈ Finset.range (n + 1), A i * B (n - i) := by
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    change hardyMomentFunctional G n
      (∑ i ∈ Finset.range N, A i • circleMonomialLp circleLebesgue i) = _
    rw [map_sum]
    have hterm (i : ℕ) : hardyMomentFunctional G n
        (A i • circleMonomialLp circleLebesgue i) =
        A i * nonnegativeIntExtension B ((n : ℤ) - (i : ℤ)) := by
      rw [map_smul, hardyMomentFunctional_circleMonomial B hB n i]
      rfl
    simp_rw [hterm]
    calc
      (∑ i ∈ Finset.range N,
          A i * nonnegativeIntExtension B ((n : ℤ) - (i : ℤ))) =
          ∑ i ∈ Finset.range (n + 1),
            A i * nonnegativeIntExtension B ((n : ℤ) - (i : ℤ)) := by
        symm
        apply Finset.sum_subset
        · intro i hi
          rw [Finset.mem_range] at hi ⊢
          omega
        · intro i hiN hiSmall
          rw [Finset.mem_range] at hiN
          rw [Finset.mem_range] at hiSmall
          rw [nonnegativeIntExtension_nat_sub_nat_eq_zero B (by omega), mul_zero]
      _ = ∑ i ∈ Finset.range (n + 1), A i * B (n - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [nonnegativeIntExtension_nat_sub_nat B (by omega)]
  have hpair' : Tendsto (fun N => hardyMomentFunctional G n (S N)) atTop
      (nhds (∑ i ∈ Finset.range (n + 1), A i * B (n - i))) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  have hvalue : hardyMomentFunctional G n F =
      ∑ i ∈ Finset.range (n + 1), A i * B (n - i) :=
    tendsto_nhds_unique hpair hpair'
  rw [hardyMomentFunctional_apply] at hvalue
  rw [← hvalue]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [F, G]
  ring

/-- Every negative Fourier coefficient of the Hardy product vanishes. -/
theorem hardyProduct_moment_eq_zero_of_neg
    (A B : ℕ → ℂ) (hA : Memℓp A 2) (hB : Memℓp B 2)
    (k : ℤ) (hk : k < 0) :
    (∫ z : Circle,
      (circleRieszFischerOfNat A hA) z * (circleRieszFischerOfNat B hB) z *
        (starRingEnd ℂ) ((z : ℂ) ^ k) ∂circleLebesgue) = 0 := by
  let F : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat A hA
  let G : Lp ℂ 2 circleLebesgue := circleRieszFischerOfNat B hB
  let S : ℕ → Lp ℂ 2 circleLebesgue := fun N =>
    ∑ i ∈ Finset.range N, A i • circleMonomialLp circleLebesgue i
  have hS : Tendsto S atTop (nhds F) := by
    simpa only [S, F] using
      (hasSum_circleMonomial_smul_circleRieszFischerOfNat A hA).tendsto_sum_nat
  have hpair : Tendsto (fun N => hardyZMomentFunctional G k (S N)) atTop
      (nhds (hardyZMomentFunctional G k F)) :=
    (hardyZMomentFunctional G k).continuous.continuousAt.tendsto.comp hS
  have heval : ∀ N, hardyZMomentFunctional G k (S N) = 0 := by
    intro N
    change hardyZMomentFunctional G k
      (∑ i ∈ Finset.range N, A i • circleMonomialLp circleLebesgue i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul, hardyZMomentFunctional_circleMonomial B hB k i]
    rw [nonnegativeIntExtension, if_neg (by omega)]
    simp
  have hpair' : Tendsto (fun N => hardyZMomentFunctional G k (S N)) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (Eventually.of_forall fun N => (heval N).symm)
  have hvalue : hardyZMomentFunctional G k F = 0 := tendsto_nhds_unique hpair hpair'
  rw [hardyZMomentFunctional_apply] at hvalue
  rw [← hvalue]
  apply integral_congr_ae
  filter_upwards with z
  dsimp only [F, G]
  ring

/-- The product of two one-sided Riesz--Fischer reconstructions is integrable. -/
theorem integrable_hardyProduct
    (A B : ℕ → ℂ) (hA : Memℓp A 2) (hB : Memℓp B 2) :
    Integrable (fun z : Circle =>
      (circleRieszFischerOfNat A hA) z * (circleRieszFischerOfNat B hB) z)
      circleLebesgue := by
  exact (Lp.memLp (circleRieszFischerOfNat A hA)).integrable_mul
    (Lp.memLp (circleRieszFischerOfNat B hB))

end

end GaloisForLFunctions.HTGeometry
