import GaloisForLFunctions.RHTower.BandEndpointPhase
import GaloisForLFunctions.RHTower.ProlateTwoModeRadialLeakage

/-!
# The band phase separates two apertures by a logarithm

The phases of two apertures at a common band point differ by an amount that is elementary from
below.  Writing the difference of the integrands as a quotient,

```text
sqrt(sin²θ - s_m) - sqrt(sin²θ - s_n) = (s_n - s_m) / (sqrt(sin²θ - s_m) + sqrt(sin²θ - s_n)) ,
```

the denominator is at most `2 sin θ ≤ 2θ`, so

```text
Ξ_{s_m}(y) - Ξ_{s_n}(y)  ≥  (s_n - s_m)/2 · ∫_{arcsin y}^{π/2} dθ/θ
                          =  (s_n - s_m)/2 · log( (π/2) / arcsin y )
                          ≥  (s_n - s_m)/2 · log(1/y) ,
```

the last step by Jordan's inequality in the form `arcsin y ≤ (π/2) y`.

At the rescaled anchor `y = x₀/sqrt c` this reads `Ξ_{s_m} - Ξ_{s_n} ≥ (s_n - s_m)(log c)/4 + O(1/c)`,
and since `c(s_n - s_m) → 4(n - m)` the exponential separation of two rungs is

```text
exp( 2c (Ξ_{s_n}(y) - Ξ_{s_m}(y)) )  ≤  C · c^(-2(n-m)) ,
```

which is the rate the ladder consumes.  Only this one direction of the comparison is needed, and it
uses only the trivial side `sqrt(sin²θ - s) ≤ sin θ`.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

/-- **The phase difference of two apertures is at least a logarithm.** -/
theorem bandEndpointPhase_sub_ge {sm sn y : ℝ} (hsm : 0 ≤ sm) (hmn : sm ≤ sn)
    (hsy : sn < y ^ 2) (hy0 : 0 < y) (hy1 : y < 1) :
    (sn - sm) / 2 * Real.log (1 / y)
      ≤ bandEndpointPhase sm y - bandEndpointPhase sn y := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have harc0 : 0 < Real.arcsin y := Real.arcsin_pos.2 hy0
  have harcle : Real.arcsin y ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two y
  have hcontm : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - sm) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hcontn : Continuous fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - sn) :=
    Real.continuous_sqrt.comp ((Real.continuous_sin.pow 2).sub continuous_const)
  have hcontq : ContinuousOn (fun θ : ℝ => (sn - sm) / (2 * θ))
      (uIcc (Real.arcsin y) (Real.pi / 2)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun θ hθ => ?_
    rw [uIcc_of_le harcle] at hθ
    have : 0 < θ := lt_of_lt_of_le harc0 hθ.1
    positivity
  -- the pointwise comparison
  have hpt : ∀ θ ∈ uIcc (Real.arcsin y) (Real.pi / 2),
      (sn - sm) / (2 * θ) ≤ Real.sqrt (Real.sin θ ^ 2 - sm) - Real.sqrt (Real.sin θ ^ 2 - sn) := by
    intro θ hθ
    rw [uIcc_of_le harcle] at hθ
    obtain ⟨hy, _⟩ := sin_mem_of_mem_arcsin hy0.le hy1.le hθ
    have hθ0 : 0 < θ := lt_of_lt_of_le harc0 hθ.1
    have hsin0 : 0 < Real.sin θ := lt_of_lt_of_le hy0 hy
    have hsq : y ^ 2 ≤ Real.sin θ ^ 2 := by nlinarith
    have hBnn : (0 : ℝ) ≤ Real.sin θ ^ 2 - sn := by linarith
    have hAnn : (0 : ℝ) ≤ Real.sin θ ^ 2 - sm := by linarith
    set A : ℝ := Real.sqrt (Real.sin θ ^ 2 - sm) with hA
    set B : ℝ := Real.sqrt (Real.sin θ ^ 2 - sn) with hB
    have hA2 : A ^ 2 = Real.sin θ ^ 2 - sm := Real.sq_sqrt hAnn
    have hB2 : B ^ 2 = Real.sin θ ^ 2 - sn := Real.sq_sqrt hBnn
    have hAB : B ≤ A := by
      rw [hA, hB]
      exact Real.sqrt_le_sqrt (by linarith)
    have hAle : A ≤ Real.sin θ := by
      rw [hA]
      have : Real.sqrt (Real.sin θ ^ 2 - sm) ≤ Real.sqrt (Real.sin θ ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq hsin0.le] at this
    have hBle : B ≤ Real.sin θ := by
      rw [hB]
      have : Real.sqrt (Real.sin θ ^ 2 - sn) ≤ Real.sqrt (Real.sin θ ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq hsin0.le] at this
    have hsinθ : Real.sin θ ≤ θ := Real.sin_le hθ0.le
    have hsum : A + B ≤ 2 * θ := by linarith
    have hdiff : (A - B) * (A + B) = sn - sm := by
      have : A ^ 2 - B ^ 2 = sn - sm := by rw [hA2, hB2]; ring
      nlinarith [this]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * θ)]
    nlinarith [hdiff, hsum, hAB, hθ0]
  -- integrate the comparison
  have hintm : IntervalIntegrable (fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - sm)) volume
      (Real.arcsin y) (Real.pi / 2) := hcontm.intervalIntegrable _ _
  have hintn : IntervalIntegrable (fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 - sn)) volume
      (Real.arcsin y) (Real.pi / 2) := hcontn.intervalIntegrable _ _
  have hintq : IntervalIntegrable (fun θ : ℝ => (sn - sm) / (2 * θ)) volume
      (Real.arcsin y) (Real.pi / 2) := hcontq.intervalIntegrable
  have hmono : (∫ θ in Real.arcsin y..(Real.pi / 2), (sn - sm) / (2 * θ))
      ≤ ∫ θ in Real.arcsin y..(Real.pi / 2),
          (Real.sqrt (Real.sin θ ^ 2 - sm) - Real.sqrt (Real.sin θ ^ 2 - sn)) := by
    refine intervalIntegral.integral_mono_on harcle hintq (hintm.sub hintn) fun θ hθ => ?_
    exact hpt θ (by rw [uIcc_of_le harcle]; exact hθ)
  rw [intervalIntegral.integral_sub hintm hintn] at hmono
  -- evaluate the elementary integral
  have hval : (∫ θ in Real.arcsin y..(Real.pi / 2), (sn - sm) / (2 * θ))
      = (sn - sm) / 2 * Real.log (Real.pi / 2 / Real.arcsin y) := by
    have hrw : ∀ θ : ℝ, (sn - sm) / (2 * θ) = (sn - sm) / 2 * θ⁻¹ := by
      intro θ
      rw [inv_eq_one_div]
      ring
    calc (∫ θ in Real.arcsin y..(Real.pi / 2), (sn - sm) / (2 * θ))
        = ∫ θ in Real.arcsin y..(Real.pi / 2), (sn - sm) / 2 * θ⁻¹ := by
          exact intervalIntegral.integral_congr fun θ _ => hrw θ
      _ = (sn - sm) / 2 * ∫ θ in Real.arcsin y..(Real.pi / 2), θ⁻¹ :=
          intervalIntegral.integral_const_mul _ _
      _ = (sn - sm) / 2 * Real.log (Real.pi / 2 / Real.arcsin y) := by
          rw [integral_inv_of_pos harc0 (by linarith)]
  rw [hval] at hmono
  refine le_trans ?_ hmono
  -- compare the two logarithms
  have hchord : Real.arcsin y ≤ Real.pi / 2 * y := arcsin_le_pi_div_two_mul hy0.le hy1.le
  have hlog : Real.log (1 / y) ≤ Real.log (Real.pi / 2 / Real.arcsin y) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hy0 harc0]
    nlinarith [hchord, hpi]
  have hcoef : (0 : ℝ) ≤ (sn - sm) / 2 := by linarith
  exact mul_le_mul_of_nonneg_left hlog hcoef


/-- **The exponential separation of two apertures at a common band point.**  The phase difference
exponentiates to a negative power of the reciprocal band point. -/
theorem exp_two_mul_bandPhase_sub_le {c sm sn y : ℝ} (hc : 0 < c) (hsm : 0 ≤ sm) (hmn : sm ≤ sn)
    (hsy : sn < y ^ 2) (hy0 : 0 < y) (hy1 : y < 1) :
    Real.exp (2 * c * (bandEndpointPhase sn y - bandEndpointPhase sm y))
      ≤ Real.exp (-(c * (sn - sm) * Real.log (1 / y))) := by
  refine Real.exp_le_exp.2 ?_
  have hbase := bandEndpointPhase_sub_ge hsm hmn hsy hy0 hy1
  have hmul := mul_le_mul_of_nonneg_left hbase (by positivity : (0 : ℝ) ≤ 2 * c)
  nlinarith [hmul]

end GaloisForLFunctions.RHTower

end
