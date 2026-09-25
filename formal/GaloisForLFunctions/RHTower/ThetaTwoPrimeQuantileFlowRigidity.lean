import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric
import GaloisForLFunctions.RHTower.HedenmalmQuantileRootMode

/-!
# Two-prime quantile-flow rigidity

The two CDF-conjugated translations by `log 2` and `log 3` determine a positive
density's normalized CDF once its median is fixed.  This is an all-scale source
fidelity theorem; it does not orient the Xi spectrum.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower

open HedenmalmQuantile

private theorem two_pow_ne_three_pow (m n : ℕ) (hm : 0 < m) (_hn : 0 < n) :
    2 ^ m ≠ 3 ^ n := by
  intro heq
  have hdiv : 2 ∣ 3 ^ n := by
    rw [← heq]
    exact dvd_pow_self 2 hm.ne'
  have h23 : 2 ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdiv
  norm_num at h23

/-- Two incommensurate flow conjugacies determine the anchored CDF coordinate. -/
theorem two_prime_flow_rigidity
    (F₁ F₂ Q₂ : ℝ → ℝ)
    (hF₂Q₂ : ∀ x, Q₂ (F₂ x) = x)
    (hQ₂F₂ : ∀ x, F₂ (Q₂ (F₁ x)) = F₁ x)
    (hH : Continuous fun x => Q₂ (F₁ x))
    (hmedian : F₁ 0 = F₂ 0)
    (h₂ : ∀ x, F₁ (x + Real.log 2) = F₂ (Q₂ (F₁ x) + Real.log 2))
    (h₃ : ∀ x, F₁ (x + Real.log 3) = F₂ (Q₂ (F₁ x) + Real.log 3)) :
    F₁ = F₂ := by
  let h : ℝ → ℂ := fun x => ((Q₂ (F₁ x) - x : ℝ) : ℂ)
  have hcont : Continuous h := by
    dsimp [h]
    exact Complex.continuous_ofReal.comp (hH.sub continuous_id)
  have hperiod (n : ℕ)
      (hn : ∀ x, F₁ (x + Real.log n) = F₂ (Q₂ (F₁ x) + Real.log n))
      (x : ℝ) : h (x + Real.log n) = h x := by
    have harg := hn x
    have hq : Q₂ (F₁ (x + Real.log n)) = Q₂ (F₁ x) + Real.log n := by
      rw [harg, hF₂Q₂]
    dsimp [h]
    rw [hq]
    congr 1
    ring
  have hperiod₂ : ∀ x, h (x + Real.log 2) = h x := hperiod 2 h₂
  have hperiod₃ : ∀ x, h (x + Real.log 3) = h x := hperiod 3 h₃
  have hzero : h 0 = 0 := by
    dsimp [h]
    rw [hmedian, hF₂Q₂]
    norm_num
  funext x
  have hx : h x = h 0 :=
    eq_of_two_dilation_invariance hcont (by norm_num) (by norm_num)
      (fun m n hm hn => two_pow_ne_three_pow m n hm hn)
      hperiod₂ hperiod₃ x 0
  rw [hzero] at hx
  have hq : Q₂ (F₁ x) = x := by
    dsimp [h] at hx
    exact sub_eq_zero.mp (Complex.ofReal_injective (by simpa using hx))
  calc
    F₁ x = F₂ (Q₂ (F₁ x)) := (hQ₂F₂ x).symm
    _ = F₂ x := by rw [hq]

/-- Equal `2`- and `3`-quantile flows and equal median force equality of normalized CDFs. -/
theorem positive_density_two_prime_flow_rigidity
    (S₁ S₂ : PositiveDensitySource)
    (hmedian : S₁.cdfFun 0 = S₂.cdfFun 0)
    (h₂ : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      S₁.cdfFun (S₁.quantileFun t + Real.log 2) =
        S₂.cdfFun (S₂.quantileFun t + Real.log 2))
    (h₃ : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      S₁.cdfFun (S₁.quantileFun t + Real.log 3) =
        S₂.cdfFun (S₂.quantileFun t + Real.log 3)) :
    S₁.cdfFun = S₂.cdfFun := by
  apply two_prime_flow_rigidity S₁.cdfFun S₂.cdfFun S₂.quantileFun
  · exact S₂.quantile_cdfFun
  · intro x
    exact S₂.cdfFun_quantile (S₁.cdfFun_mem_Ioo x)
  · exact (continuousOn_quantileFun S₂).comp_continuous S₁.continuous_cdfFun
      (fun x => S₁.cdfFun_mem_Ioo x)
  · exact hmedian
  · intro x
    simpa [S₁.quantile_cdfFun x] using h₂ (S₁.cdfFun x) (S₁.cdfFun_mem_Ioo x)
  · intro x
    simpa [S₁.quantile_cdfFun x] using h₃ (S₁.cdfFun x) (S₁.cdfFun_mem_Ioo x)

end RHTower
