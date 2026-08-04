import GaloisForLFunctions.RHTower.ProlateEndpointLowerBound
import GaloisForLFunctions.HTGeometry.DifferentialInequalityComparison

/-!
# The Riccati equation of a prolate solution

The logarithmic derivative `v = -psi'/psi` of a nonvanishing solution of

```text
(1-y²) psi'' - 2y psi' - c² y² psi = chi psi
```

satisfies the Riccati equation

```text
v' = v² + (2y/(1-y²)) v - (chi + c² y²)/(1-y²),
```

which is the form every comparison estimate for the decay of `psi` uses: an explicit supersolution of that
equation bounds `v` from above, and `psi(1) = psi(y_0) exp(-∫ v)` turns the bound on `v` into a lower bound
at the endpoint.  Together with the variable-coefficient comparison lemma this is the engine of the
endpoint asymptotics: the crude bound of the previous step is the constant supersolution
`(chi + c²)/(1+y)`, and any sharper supersolution improves the exponent directly.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set intervalIntegral MeasureTheory

open _root_.RHTower

/-- The (sign-normalized) logarithmic derivative of a solution: `v = -psi'/psi`. -/
def prolateLogDeriv (Φ : ℝ → ℝ) (y : ℝ) : ℝ := -(deriv Φ y / Φ y)

/-- **The Riccati equation of a prolate solution.** -/
theorem hasDerivAt_prolateLogDeriv {c χ : ℝ} {Φ : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = χ * Φ y)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) (hΦ : Φ y ≠ 0) :
    HasDerivAt (prolateLogDeriv Φ)
      ((prolateLogDeriv Φ y) ^ 2 + (2 * y / (1 - y ^ 2)) * prolateLogDeriv Φ y
        - (χ + c ^ 2 * y ^ 2) / (1 - y ^ 2)) y := by
  have hd1 : Differentiable ℝ Φ := (contDiff_infty_iff_deriv.mp hsm).1
  have hd2 : Differentiable ℝ (deriv Φ) :=
    (contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hsm).2)).1
  have hymem : y ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hw : (1 : ℝ) - y ^ 2 ≠ 0 := by
    have h1 : -1 < y := hy.1
    have h2 : y < 1 := hy.2
    nlinarith
  have h := heig y hymem
  rw [prolateSLAction] at h
  have hquot : HasDerivAt (fun t => deriv Φ t / Φ t)
      ((deriv (deriv Φ) y * Φ y - deriv Φ y * deriv Φ y) / (Φ y) ^ 2) y :=
    (hd2 y).hasDerivAt.div (hd1 y).hasDerivAt hΦ
  have hsecond : deriv (deriv Φ) y
      = (χ * Φ y + 2 * y * deriv Φ y + c ^ 2 * y ^ 2 * Φ y) / (1 - y ^ 2) := by
    field_simp
    linear_combination h
  have hv := hquot.neg
  refine hv.congr_deriv ?_
  rw [prolateLogDeriv, hsecond]
  field_simp
  ring

/-- **The endpoint value from a bound on the logarithmic derivative.**  If `v = -psi'/psi` is bounded
above by `V` on `[y_0, y_1]` then the solution decays at most like `exp(-∫ V)`. -/
theorem le_endpoint_of_logDeriv_le {y₀ y₁ : ℝ} {Φ V : ℝ → ℝ} (hab : y₀ ≤ y₁)
    (hd1 : Differentiable ℝ Φ) (hVc : ContinuousOn V (Icc y₀ y₁))
    (hpos : ∀ y ∈ Icc y₀ y₁, 0 < Φ y)
    (hle : ∀ y ∈ Ioo y₀ y₁, prolateLogDeriv Φ y ≤ V y) :
    Φ y₀ * Real.exp (-∫ t in y₀..y₁, V t) ≤ Φ y₁ := by
  -- the comparison is applied to `log Φ + ∫ V`
  set L : ℝ → ℝ := Set.IccExtend hab (fun x : Icc y₀ y₁ => V x) with hL
  have hLcont : Continuous L := by
    rw [hL]
    exact (continuous_IccExtend_iff (h := hab)).mpr hVc.restrict
  have hLeq : ∀ y ∈ Icc y₀ y₁, L y = V y := by
    intro y hy
    rw [hL]
    exact Set.IccExtend_val hab (fun x : Icc y₀ y₁ => V x) ⟨y, hy⟩
  set F : ℝ → ℝ := fun y => ∫ t in y₀..y, L t with hF
  have hFderiv : ∀ y : ℝ, HasDerivAt F (L y) y := by
    intro y
    exact intervalIntegral.integral_hasDerivAt_right (hLcont.intervalIntegrable y₀ y)
      (hLcont.stronglyMeasurableAtFilter _ _) hLcont.continuousAt
  -- the auxiliary function `Φ (y) exp (F y)` is monotone
  set G : ℝ → ℝ := fun y => Φ y * Real.exp (F y) with hG
  have hGderiv : ∀ y : ℝ, HasDerivAt G
      (deriv Φ y * Real.exp (F y) + Φ y * (L y * Real.exp (F y))) y := by
    intro y
    have hexp := (hFderiv y).exp
    have hprod := (hd1 y).hasDerivAt.mul hexp
    refine hprod.congr_deriv ?_
    ring
  have hGmono : MonotoneOn G (Icc y₀ y₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ fun y hy => ?_
    · refine hd1.continuous.continuousOn.mul ?_
      exact (Real.continuous_exp.comp
        (continuous_iff_continuousAt.mpr fun y => (hFderiv y).continuousAt)).continuousOn
    · exact fun y _ => (hGderiv y).differentiableAt.differentiableWithinAt
    · rw [interior_Icc] at hy
      rw [(hGderiv y).deriv]
      have hymem : y ∈ Icc y₀ y₁ := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
      have hΦpos : 0 < Φ y := hpos y hymem
      have hvle : prolateLogDeriv Φ y ≤ V y := hle y hy
      have hLV : L y = V y := hLeq y hymem
      -- `-Φ'/Φ ≤ V` means `Φ' + V Φ ≥ 0`
      have hkey : 0 ≤ deriv Φ y + V y * Φ y := by
        rw [prolateLogDeriv] at hvle
        have h1 : -(deriv Φ y) / Φ y ≤ V y := by
          rw [neg_div]
          exact hvle
        rw [div_le_iff₀ hΦpos] at h1
        linarith
      have hexppos : 0 < Real.exp (F y) := Real.exp_pos _
      have hfactor : deriv Φ y * Real.exp (F y) + Φ y * (L y * Real.exp (F y))
          = (deriv Φ y + V y * Φ y) * Real.exp (F y) := by
        rw [hLV]
        ring
      rw [hfactor]
      exact mul_nonneg hkey (le_of_lt hexppos)
  -- compare the endpoints and solve for `Φ y₁`
  have hcmp : G y₀ ≤ G y₁ :=
    hGmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hG0 : G y₀ = Φ y₀ := by
    rw [hG, hF]
    simp
  have hFy₁ : F y₁ = ∫ t in y₀..y₁, V t := by
    show (∫ t in y₀..y₁, L t) = ∫ t in y₀..y₁, V t
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    exact hLeq t ht
  have hGy₁ : G y₁ = Φ y₁ * Real.exp (∫ t in y₀..y₁, V t) := by
    show Φ y₁ * Real.exp (F y₁) = Φ y₁ * Real.exp (∫ t in y₀..y₁, V t)
    rw [hFy₁]
  rw [hG0, hGy₁] at hcmp
  -- rearrange
  have hexppos : 0 < Real.exp (∫ t in y₀..y₁, V t) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexppos]
  exact hcmp

end GaloisForLFunctions.RHTower

end
