import GaloisForLFunctions.RHTower.SuzukiModelSpaceOrthogonal
import GaloisForLFunctions.HTGeometry.EntireMultiplicityFactor

/-!
# Suzuki eq. (4.1): the inner function has a simple zero of slope `-i/m` at every Xi zero

Suzuki, arXiv:2301.00421v3, Proposition 4.1, first displayed formula: `Theta'(gamma)/2 = -i/m_gamma`.

Stated here for `A/E = (1 + Theta)/2` rather than for `Theta` itself, which is the form every later
computation consumes and which avoids a junk-value trap: at a zero of order `m >= 2` the
denominator `E` also vanishes, so `Theta = E^sharp/E` is `0/0` in Lean at exactly the point where the
derivative is wanted, whereas `A/E` takes the correct value `0` there.

The proof peels the zero (`exists_entire_factor_of_analyticOrderAt_eq`): with `A = (z-gamma)^m h`
and `h(gamma) != 0`,

`E = A + iA' = (z-gamma)^{m-1} * P`,   `P = (z-gamma)h + i(m h + (z-gamma)h')`,   `P(gamma) = i m h(gamma) != 0`,

so `A/E = (z-gamma) h / P` on a neighbourhood of `gamma` — including at `gamma` itself, where both
sides are `0` — and the quotient rule at a point where the numerator vanishes gives
`h(gamma)/P(gamma) = 1/(i m) = -i/m`.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Suzuki eq. (4.1): the derivative of the inner function at a zero -/

/-- `(1 + Θ_ξ)/2 = A/E`, the factor that appears in every `F_γ`. -/
def suzukiHalfInner (z : ℂ) : ℂ := XiC z / xiHedenmalmDeBrangesE z

/-- **Suzuki eq. (4.1).**  At a zero of `A = ξ(1/2-iz)` of exact order `m`, the function
`(1+Θ_ξ)/2 = A/E` has a *simple* zero with derivative `-i/m`; equivalently `Θ'(γ)/2 = -i/m`. -/
theorem hasDerivAt_suzukiHalfInner {γ : ℂ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC γ = (m : ℕ∞)) :
    HasDerivAt suzukiHalfInner (-I / (m : ℂ)) γ := by
  obtain ⟨h, hh, hhγ, hfac⟩ :=
    exists_entire_factor_of_analyticOrderAt_eq (fun z => XiC_analytic z (Set.mem_univ z)) γ m hord
  have hmC : ((m : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  -- the derivative of `XiC`
  have hfun : XiC = fun z => (z - γ) ^ m * h z := funext hfac
  have hderiv : ∀ z, HasDerivAt XiC
      ((m : ℂ) * (z - γ) ^ (m - 1) * h z + (z - γ) ^ m * deriv h z) z := by
    intro z
    rw [hfun]
    have h1 : HasDerivAt (fun w : ℂ => (w - γ) ^ m) ((m : ℂ) * (z - γ) ^ (m - 1)) z := by
      have hb : HasDerivAt (fun w : ℂ => w - γ) 1 z := (hasDerivAt_id z).sub_const γ
      simpa [Pi.pow_def] using hb.pow m
    exact h1.mul ((hh z).differentiableAt.hasDerivAt)
  have hderivEq : ∀ z, deriv XiC z
      = (m : ℂ) * (z - γ) ^ (m - 1) * h z + (z - γ) ^ m * deriv h z :=
    fun z => (hderiv z).deriv
  -- the peeled factor of `E`
  set P : ℂ → ℂ := fun z => (z - γ) * h z + I * ((m : ℂ) * h z + (z - γ) * deriv h z) with hP
  have hPγ : P γ = I * (m : ℂ) * h γ := by
    rw [hP]
    simp
    ring
  have hPne : P γ ≠ 0 := by
    rw [hPγ]
    exact mul_ne_zero (mul_ne_zero Complex.I_ne_zero hmC) hhγ
  have hEfac : ∀ z, xiHedenmalmDeBrangesE z = (z - γ) ^ (m - 1) * P z := by
    intro z
    rw [xiHedenmalmDeBrangesE, hfac z, hderivEq z, hP]
    have hpow : (z - γ) ^ m = (z - γ) ^ (m - 1) * (z - γ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    ring
  -- analyticity of `P` and a neighbourhood where it is nonzero
  have hPan : AnalyticAt ℂ P γ := by
    have hd : AnalyticAt ℂ (deriv h) γ := (hh γ).deriv
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - γ) γ := (analyticAt_id).sub analyticAt_const
    exact (h1.mul (hh γ)).add (analyticAt_const.mul
      ((analyticAt_const.mul (hh γ)).add (h1.mul hd)))
  have hPnhds : ∀ᶠ z in 𝓝 γ, P z ≠ 0 := hPan.continuousAt.eventually_ne hPne
  -- the quotient agrees with the peeled quotient near `γ`
  have hcongr : suzukiHalfInner =ᶠ[𝓝 γ] fun z => (z - γ) * h z / P z := by
    filter_upwards [hPnhds] with z hz
    rw [suzukiHalfInner, hfac z, hEfac z]
    rcases eq_or_ne z γ with rfl | hzγ
    · simp [zero_pow (show m ≠ 0 by omega)]
    · have hsub : (z - γ) ≠ 0 := sub_ne_zero.mpr hzγ
      have hpowne : (z - γ) ^ (m - 1) ≠ 0 := pow_ne_zero _ hsub
      have hpow : (z - γ) ^ m = (z - γ) ^ (m - 1) * (z - γ) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      field_simp
  -- differentiate the peeled quotient
  have hN : HasDerivAt (fun z : ℂ => (z - γ) * h z) (h γ) γ := by
    have hb : HasDerivAt (fun w : ℂ => w - γ) 1 γ := (hasDerivAt_id γ).sub_const γ
    have hmul := hb.mul ((hh γ).differentiableAt.hasDerivAt)
    simpa [Pi.mul_def] using hmul
  have hPd : HasDerivAt P (deriv P γ) γ := hPan.differentiableAt.hasDerivAt
  have hq := hN.div hPd hPne
  have hval : (h γ * P γ - (γ - γ) * h γ * deriv P γ) / P γ ^ (2 : ℕ) = -I / (m : ℂ) := by
    rw [hPγ]
    have hI : I ≠ 0 := Complex.I_ne_zero
    field_simp
    linear_combination (h γ * I * (m:ℂ)) * Complex.I_sq
  rw [hval] at hq
  exact hq.congr_of_eventuallyEq hcongr

end
end RHTower

