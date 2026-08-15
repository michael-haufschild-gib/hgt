import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets

/-!
# Ordinary jets through Euler jets

The Euler operator `θ = z d/dz` and the ordinary derivative generate the same jets, because

```text
z^{m+1} f^{(m+1)} = (θ − m)(z^m f^{(m)}) .
```

Iterating that identity writes `z^m f^{(m)}` as a fixed **integer** combination of `f, θf, …, θ^m f`,
with the coefficient of `θ^m f` equal to `1`.  The combination is unitriangular, so a polynomial
relation among the ordinary jets becomes a polynomial relation among the Euler jets and back.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The Euler operator on a complex function. -/
noncomputable def cEulerDeriv (F : ℂ → ℂ) : ℂ → ℂ := fun z => z * deriv F z

/-- The integer coefficients writing `z^m f^{(m)}` through the Euler jets. -/
def eulerJetCoeff : ℕ → ℕ → ℤ
  | 0, 0 => 1
  | 0, (_ + 1) => 0
  | (m + 1), 0 => -(m : ℤ) * eulerJetCoeff m 0
  | (m + 1), (k + 1) => eulerJetCoeff m k - (m : ℤ) * eulerJetCoeff m (k + 1)

@[simp] theorem eulerJetCoeff_zero_zero : eulerJetCoeff 0 0 = 1 := rfl

@[simp] theorem eulerJetCoeff_zero_succ (k : ℕ) : eulerJetCoeff 0 (k + 1) = 0 := rfl

theorem eulerJetCoeff_succ_zero (m : ℕ) :
    eulerJetCoeff (m + 1) 0 = -(m : ℤ) * eulerJetCoeff m 0 := rfl

theorem eulerJetCoeff_succ_succ (m k : ℕ) :
    eulerJetCoeff (m + 1) (k + 1) = eulerJetCoeff m k - (m : ℤ) * eulerJetCoeff m (k + 1) := rfl

theorem eulerJetCoeff_eq_zero_of_lt : ∀ {m k : ℕ}, m < k → eulerJetCoeff m k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, (_ + 1), _ => rfl
  | (m + 1), 0, h => absurd h (by omega)
  | (m + 1), (k + 1), h => by
      rw [eulerJetCoeff_succ_succ, eulerJetCoeff_eq_zero_of_lt (by omega),
        eulerJetCoeff_eq_zero_of_lt (by omega)]
      ring

theorem eulerJetCoeff_self : ∀ m : ℕ, eulerJetCoeff m m = 1
  | 0 => rfl
  | (m + 1) => by
      rw [eulerJetCoeff_succ_succ, eulerJetCoeff_self m,
        eulerJetCoeff_eq_zero_of_lt (by omega)]
      ring

/-! ### Analyticity of the Euler jets -/

theorem analyticOnNhd_cEulerDeriv {U : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) : AnalyticOnNhd ℂ (cEulerDeriv F) U := by
  have hid : AnalyticOnNhd ℂ (fun z : ℂ => z) U := fun z _ => analyticAt_id
  exact hid.mul hF.deriv

theorem analyticOnNhd_cEulerDeriv_iterate {U : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) : ∀ k : ℕ, AnalyticOnNhd ℂ (cEulerDeriv^[k] F) U
  | 0 => by simpa using hF
  | (k + 1) => by
      rw [Function.iterate_succ_apply']
      exact analyticOnNhd_cEulerDeriv (analyticOnNhd_cEulerDeriv_iterate hF k)

/-! ### The identity -/

/-- The weighted ordinary jet `z^m f^{(m)}`. -/
noncomputable def weightedJet (F : ℂ → ℂ) (m : ℕ) : ℂ → ℂ :=
  fun z => z ^ m * iteratedDeriv m F z

theorem analyticOnNhd_weightedJet {U : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (m : ℕ) : AnalyticOnNhd ℂ (weightedJet F m) U := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => z ^ m) U := fun z _ => analyticAt_id.pow m
  exact hpow.mul (analyticOnNhd_iteratedDeriv hF m)

/-- **The step of the ladder.**  `z^{m+1} f^{(m+1)} = (θ − m)(z^m f^{(m)})`. -/
theorem weightedJet_succ {U : Set ℂ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (m : ℕ) {z : ℂ} (hz : z ∈ U) :
    weightedJet F (m + 1) z = cEulerDeriv (weightedJet F m) z - (m : ℂ) * weightedJet F m z := by
  have hder : DifferentiableAt ℂ (iteratedDeriv m F) z :=
    (analyticOnNhd_iteratedDeriv hF m z hz).differentiableAt
  have hpow : HasDerivAt (fun w : ℂ => w ^ m) ((m : ℂ) * z ^ (m - 1)) z := by
    simpa using (hasDerivAt_pow m z)
  have hprod : HasDerivAt (fun w : ℂ => w ^ m * iteratedDeriv m F w)
      ((m : ℂ) * z ^ (m - 1) * iteratedDeriv m F z + z ^ m * deriv (iteratedDeriv m F) z) z :=
    hpow.mul hder.hasDerivAt
  have hd : deriv (weightedJet F m) z
      = (m : ℂ) * z ^ (m - 1) * iteratedDeriv m F z + z ^ m * iteratedDeriv (m + 1) F z := by
    have hfun : weightedJet F m = fun w : ℂ => w ^ m * iteratedDeriv m F w := rfl
    rw [hfun, iteratedDeriv_succ]
    exact hprod.deriv
  simp only [cEulerDeriv, weightedJet, hd]
  cases m with
  | zero => simp
  | succ p =>
      push_cast
      ring

/-- **The ordinary jets are integer combinations of the Euler jets.** -/
theorem weightedJet_eq_sum {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) : ∀ (m : ℕ) {z : ℂ}, z ∈ U →
      weightedJet F m z
        = ∑ k ∈ Finset.range (m + 1),
            ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F z
  | 0, z, _ => by
      rw [weightedJet, iteratedDeriv_zero]
      simp
  | (m + 1), z, hz => by
      have hstep := weightedJet_succ hF m hz
      have hIH : ∀ w ∈ U, weightedJet F m w
          = ∑ k ∈ Finset.range (m + 1),
              ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F w :=
        fun w hw => weightedJet_eq_sum hU hF m hw
      have heq : Set.EqOn (weightedJet F m)
          (fun w => ∑ k ∈ Finset.range (m + 1),
            ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F w) U := hIH
      have hderiv : deriv (weightedJet F m) z
          = deriv (fun w => ∑ k ∈ Finset.range (m + 1),
              ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F w) z :=
        Filter.EventuallyEq.deriv_eq (heq.eventuallyEq_of_mem (hU.mem_nhds hz))
      have hsumderiv : deriv (fun w => ∑ k ∈ Finset.range (m + 1),
            ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F w) z
          = ∑ k ∈ Finset.range (m + 1),
              ((eulerJetCoeff m k : ℤ) : ℂ) * deriv (cEulerDeriv^[k] F) z := by
        rw [deriv_fun_sum (fun k _ =>
          ((analyticOnNhd_cEulerDeriv_iterate hF k z hz).differentiableAt).const_mul _)]
        exact Finset.sum_congr rfl fun k _ => deriv_const_mul _
          ((analyticOnNhd_cEulerDeriv_iterate hF k z hz).differentiableAt)
      have hEuler : cEulerDeriv (weightedJet F m) z
          = ∑ k ∈ Finset.range (m + 1),
              ((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k + 1] F z := by
        rw [cEulerDeriv, hderiv, hsumderiv, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Function.iterate_succ_apply', cEulerDeriv]
        ring
      rw [hstep, hEuler, hIH z hz, Finset.mul_sum]
      rw [Finset.sum_range_succ' (fun k => ((eulerJetCoeff (m + 1) k : ℤ) : ℂ) * cEulerDeriv^[k] F z)]
      have hshift : ∑ k ∈ Finset.range (m + 1),
            ((eulerJetCoeff (m + 1) (k + 1) : ℤ) : ℂ) * cEulerDeriv^[k + 1] F z
          = ∑ k ∈ Finset.range (m + 1),
              (((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k + 1] F z
                - (m : ℂ) * (((eulerJetCoeff m (k + 1) : ℤ) : ℂ) * cEulerDeriv^[k + 1] F z)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [eulerJetCoeff_succ_succ]
        push_cast
        ring
      rw [hshift, Finset.sum_sub_distrib, eulerJetCoeff_succ_zero]
      have hlast : ∑ k ∈ Finset.range (m + 1),
            (m : ℂ) * (((eulerJetCoeff m (k + 1) : ℤ) : ℂ) * cEulerDeriv^[k + 1] F z)
          = ∑ k ∈ Finset.range (m + 1),
              (m : ℂ) * (((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F z)
            - (m : ℂ) * (((eulerJetCoeff m 0 : ℤ) : ℂ) * cEulerDeriv^[0] F z) := by
        rw [Finset.sum_range_succ'
          (fun k => (m : ℂ) * (((eulerJetCoeff m k : ℤ) : ℂ) * cEulerDeriv^[k] F z))]
        have hzero : (m : ℂ) * (((eulerJetCoeff m (m + 1) : ℤ) : ℂ) * cEulerDeriv^[m + 1] F z) = 0 := by
          rw [eulerJetCoeff_eq_zero_of_lt (by omega)]
          push_cast
          ring
        rw [Finset.sum_range_succ, hzero, add_zero]
        ring
      rw [hlast]
      push_cast
      ring

end GaloisForLFunctions.HTGeometry
