import GaloisForLFunctions.RHTower.MassBesselDyadicRadiation

/-!
# The prime mass of a Poincaré coefficient polynomial

Each Poincaré coefficient is a polynomial of degree at most its own order in the squared logarithm,
so its dyadic prime mass is a finite combination of logarithmically weighted masses.  The top
coefficient dominates: after dividing by `√X (log X)^{2m}` the combination converges to the extremal
coefficient times the dyadic prime constant.
-/

open Filter ArithmeticFunction HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The prime mass of a coefficient polynomial is a combination of logarithmic masses. -/
theorem dyadicPoincareMass_eq (a : ℝ) (n' M j : ℕ) (X : ℝ) :
    dyadicPoincareMass a n' M j X
      = ∑ d ∈ Finset.range (j + 1),
          (poincareCoeffPoly a n' M j).coeff d
            * ((dyadicSqrtVonMangoldtLogMass d X : ℝ) : ℂ) := by
  classical
  have hdeg : (poincareCoeffPoly a n' M j).natDegree < j + 1 :=
    Nat.lt_succ_of_le (natDegree_poincareCoeffPoly_le a n' M j)
  have hstep : ∀ k ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      (((vonMangoldt k : ℝ) / Real.sqrt k : ℝ) : ℂ)
        * (poincareCoeffPoly a n' M j).eval (((Real.log k : ℝ) : ℂ) ^ 2)
      = ∑ d ∈ Finset.range (j + 1),
          (poincareCoeffPoly a n' M j).coeff d
            * ((((vonMangoldt k : ℝ) / Real.sqrt k * Real.log k ^ (2 * d) : ℝ)) : ℂ) := by
    intro k _
    rw [Polynomial.eval_eq_sum_range' hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    rw [← pow_mul]
    ring
  rw [dyadicPoincareMass, Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [dyadicSqrtVonMangoldtLogMass, Complex.ofReal_sum, Finset.mul_sum]

theorem tendsto_logPow_inv (p : ℕ) (hp : 0 < p) :
    Tendsto (fun X : ℝ => (Real.log X ^ p)⁻¹) atTop (𝓝 0) := by
  have hlog : Tendsto (fun X : ℝ => Real.log X ^ p) atTop atTop :=
    (tendsto_pow_atTop (ne_of_gt hp)).comp Real.tendsto_log_atTop
  exact hlog.inv_tendsto_atTop

/-- The lower-order logarithmic masses are negligible against the top order. -/
theorem tendsto_logMass_div_top {d m : ℕ} (hdm : d < m) :
    Tendsto (fun X : ℝ =>
        dyadicSqrtVonMangoldtLogMass d X / (Real.sqrt X * Real.log X ^ (2 * m)))
      atTop (𝓝 0) := by
  have hbase := tendsto_dyadicSqrtVonMangoldtLogMass d
  have hpow : Tendsto (fun X : ℝ => (Real.log X ^ (2 * (m - d)))⁻¹) atTop (𝓝 0) :=
    tendsto_logPow_inv (2 * (m - d)) (by omega)
  have hmul := hbase.mul hpow
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℝ)] with X hL hX
  have hLne : Real.log X ≠ 0 := ne_of_gt hL
  have hsplit : Real.log X ^ (2 * m) = Real.log X ^ (2 * d) * Real.log X ^ (2 * (m - d)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  field_simp

/-- **The dyadic prime mass of the `m`-th Poincaré coefficient.** -/
theorem tendsto_dyadicPoincareMass (a : ℝ) (n' M m : ℕ) :
    Tendsto (fun X : ℝ => dyadicPoincareMass a n' M m X
        / ((Real.sqrt X * Real.log X ^ (2 * m) : ℝ) : ℂ))
      atTop (𝓝 ((poincareCoeffPoly a n' M m).coeff m * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ))) := by
  classical
  have hrewrite : ∀ X : ℝ, dyadicPoincareMass a n' M m X
      / ((Real.sqrt X * Real.log X ^ (2 * m) : ℝ) : ℂ)
      = ∑ d ∈ Finset.range (m + 1),
          (poincareCoeffPoly a n' M m).coeff d
            * ((dyadicSqrtVonMangoldtLogMass d X
                / (Real.sqrt X * Real.log X ^ (2 * m)) : ℝ) : ℂ) := by
    intro X
    rw [dyadicPoincareMass_eq, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    push_cast
    ring
  refine Tendsto.congr (fun X => (hrewrite X).symm) ?_
  have hterm : ∀ d ∈ Finset.range (m + 1),
      Tendsto (fun X : ℝ => (poincareCoeffPoly a n' M m).coeff d
          * ((dyadicSqrtVonMangoldtLogMass d X
              / (Real.sqrt X * Real.log X ^ (2 * m)) : ℝ) : ℂ))
        atTop (𝓝 (if d = m then
          (poincareCoeffPoly a n' M m).coeff m * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ) else 0)) := by
    intro d hd
    rcases eq_or_ne d m with rfl | hne
    · rw [if_pos rfl]
      have hbase := tendsto_dyadicSqrtVonMangoldtLogMass d
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hbase).const_mul _
    · rw [if_neg hne]
      have hdm : d < m := by
        have := Finset.mem_range.mp hd
        omega
      have hzero := tendsto_logMass_div_top hdm
      have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hzero
      simpa using hc.const_mul ((poincareCoeffPoly a n' M m).coeff d)
  have hsum := tendsto_finsetSum (Finset.range (m + 1)) hterm
  have hval : (∑ d ∈ Finset.range (m + 1), if d = m then
      (poincareCoeffPoly a n' M m).coeff m * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ) else 0)
      = (poincareCoeffPoly a n' M m).coeff m * ((2 * (Real.sqrt 2 - 1) : ℝ) : ℂ) := by
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) m]
    rw [if_pos (Finset.self_mem_range_succ m)]
  rwa [hval] at hsum

end

end RHTower
