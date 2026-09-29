import GaloisForLFunctions.HTGeometry.RittLinearizerRittForm
import GaloisForLFunctions.HTGeometry.RittDichotomy
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicPropagation

/-!
# Ritt's theorem for the Poincaré function

Let `R` be a rational map of degree at least two with a fixed point `0` whose multiplier `λ` is
nonzero and not a root of unity, `κ` an analytic linearizer on an open set `U ∋ 0`
(`κ(R(t)) = λκ(t)`, `κ(0) = 0`) and `Φ` its analytic inverse on an open connected set `V`.

**Ritt's implication.**  If the Poincaré function `Φ` satisfies an algebraic differential equation
on `V`, then near `0`

`Φ'(z)^r = z^j·A(Φ(z))`

for some `r ≥ 1`, `j ∈ ℤ` and a nonzero rational `A`.  Local inversion transfers differential
algebraicity from `Φ` to `κ`, the linearizer satisfies `κ'^r = B·κ^i`, and substituting `t = Φ(z)`
with `κ'(Φ z)·Φ'(z) = 1` and `κ(Φ z) = z` gives the relation for `Φ`.
-/

open Filter Topology Polynomial Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Inversion commutes with evaluation off finitely many points. -/
theorem ratValue_inv_eventually (Q : RatFunc ℂ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), ratValue Q⁻¹ t = (ratValue Q t)⁻¹ := by
  have h : algebraMap (RatFunc ℂ) MeroGerm Q⁻¹ = (algebraMap (RatFunc ℂ) MeroGerm Q)⁻¹ :=
    map_inv₀ _ _
  rw [algebraMap_ratFunc_meroGerm, algebraMap_ratFunc_meroGerm, ofMero_inv, ofMero_eq_iff] at h
  exact h

variable {R : RatFunc ℂ}

/-- **The eigenvalue of a linearizer is the multiplier.** -/
theorem eq_multiplier_of_linearizer (h0 : 0 ≤ ratOrder R 0) (hR0 : ratValue R 0 = 0) {κ : ℂ → ℂ}
    (hκ : AnalyticAt ℂ κ 0) (hκ' : deriv κ 0 ≠ 0) {q : ℂ}
    (hfe : ∀ᶠ z in 𝓝 (0 : ℂ), κ (ratValue R z) = q * κ z) :
    q = ratValue (ratFuncDeriv R) 0 := by
  have hg := analyticAt_ratValue_zero h0
  have hd := Filter.EventuallyEq.deriv_eq (f₁ := fun z => κ (ratValue R z))
    (f := fun z => q * κ z) hfe
  have hκg : DifferentiableAt ℂ κ (ratValue R 0) := by rw [hR0]; exact hκ.differentiableAt
  rw [show (fun z => κ (ratValue R z)) = κ ∘ fun z => ratValue R z from rfl,
    deriv_comp 0 hκg hg.differentiableAt, deriv_const_mul _ hκ.differentiableAt, hR0,
    deriv_ratValue_zero h0] at hd
  exact (mul_right_cancel₀ hκ' (by rw [mul_comm] at hd; exact hd)).symm

/-- **Ritt's implication for the Poincaré function.** -/
theorem rittForm_of_differentiallyAlgebraicOn_poincare (hR : ¬ ∃ c : ℂ, R = RatFunc.C c)
    (hd : 2 ≤ ratFuncDegree R) (hfix : IsLinearizableFixedPoint R) {U V : Set ℂ}
    (hUo : IsOpen U) (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty)
    (hVinf : V.Infinite) {Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U)
    (hκV : MapsTo κ U V) (hΦU : MapsTo Φ V U) (hΦκ : ∀ t ∈ U, Φ (κ t) = t)
    (hκΦ : ∀ z ∈ V, κ (Φ z) = z) (h0U : (0 : ℂ) ∈ U) (hκ0 : κ 0 = 0) {q : ℂ}
    (hfe : ∀ᶠ t in 𝓝 (0 : ℂ), κ (ratValue R t) = q * κ t)
    (hDA : DifferentiallyAlgebraicOn Φ V) :
    ∃ r : ℕ, 0 < r ∧ ∃ j : ℤ, ∃ A : RatFunc ℂ, A ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv Φ z ^ r = z ^ j * ratValue A (Φ z) := by
  have hκDA : DifferentiallyAlgebraicOn κ U :=
    differentiallyAlgebraicOn_of_localInverse hVo hVc hVne hVinf hκ hΦ hΦU hκV hκΦ hΦκ hDA
  have h0V : (0 : ℂ) ∈ V := by have := hκV h0U; rwa [hκ0] at this
  have hΦ0 : Φ 0 = 0 := by have := hΦκ 0 h0U; rwa [hκ0] at this
  -- the chain rule for the inverse pair
  have hchainV : ∀ z ∈ V, deriv κ (Φ z) * deriv Φ z = 1 := by
    intro z hz
    have hev : (κ ∘ Φ) =ᶠ[𝓝 z] id := by
      filter_upwards [hVo.mem_nhds hz] with w hw using hκΦ w hw
    have h1 := Filter.EventuallyEq.deriv_eq hev
    rw [deriv_comp z (hκ _ (hΦU hz)).differentiableAt (hΦ z hz).differentiableAt, deriv_id] at h1
    exact h1
  have hκ' : deriv κ 0 ≠ 0 := by
    intro h
    have := hchainV 0 h0V
    rw [hΦ0, h, zero_mul] at this
    exact zero_ne_one this
  have hΦ' : deriv Φ 0 ≠ 0 := by
    intro h
    have := hchainV 0 h0V
    rw [h, mul_zero] at this
    exact zero_ne_one this
  have hq := eq_multiplier_of_linearizer hfix.regular hfix.fixed (hκ 0 h0U) hκ' hfe
  subst hq
  obtain ⟨N, hN, j, A, hA, hrel⟩ := rittForm_of_differentiallyAlgebraicOn_linearizer hR hd hfix
    (hκ 0 h0U) hκ' hfe (hUo.mem_nhds h0U) hκDA
  have htend := tendsto_nhdsNE_of_deriv_ne_zero (hΦ 0 h0V) hΦ0 hΦ'
  refine ⟨N, hN, -j, A⁻¹, inv_ne_zero hA, ?_⟩
  filter_upwards [htend.eventually hrel, htend.eventually (ratValue_inv_eventually A),
    nhdsWithin_le_nhds (hVo.mem_nhds h0V)] with z hz hinv hzV
  have hc := hchainV z hzV
  rw [hκΦ z hzV] at hz
  have hΦz : deriv Φ z = (deriv κ (Φ z))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hc)
  rw [hΦz, inv_pow, hz, hinv, mul_inv, zpow_neg, mul_comm]

end

end GaloisForLFunctions.HTGeometry
