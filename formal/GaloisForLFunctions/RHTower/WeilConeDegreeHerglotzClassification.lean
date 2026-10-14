import GaloisForLFunctions.RHTower.WeilConeDegreeTwinRigidity
import GaloisForLFunctions.RHTower.WeilPoleWeightAtMostOne

/-!
# Herglotz data with the gamma factor `Γ_ℝ(s)^d` are `ζ^d`

Let `d > 0`, `κ` real, and weights `lam`.  The degree-`d` Weil function with pole order `κ`,

`(1/d) [κ (1/s + 1/(s − 1)) + d (½ψ(s/2) − ½ log π) − Σ_{n≥2} lam(n) n^{−s}]`,

is `poleWeightFunction (κ/d) (lam/d)`.  For a Dirichlet series `T` whose completed function
`Ξ_T(s) = (s(s−1))^κ Γ_ℝ(s)^d T(s)` is entire of order one with `Ξ_T(1 − s) = Ξ_T(s)`, it is
`Ξ_T′/(d Ξ_T)` with `lam = −T′/T`'s coefficients, and the Hadamard product gives it nonnegative
real part on `Re s > ½` exactly when every zero of `T` is critical.

**Theorem** (`pole_order_eq_and_eq_smul_vonMangoldt_of_herglotz`).  Suppose this function has a
holomorphic continuation with nonnegative real part to `Re s > ½`, the weights satisfy
`Σ |lam(n)/d| n^{−σ} < ∞` for `σ > 1`, and `lam/d − Λ` has linearly bounded partial sums.  Then
`κ = d`, the Riemann hypothesis holds, and `lam(n) = d Λ(n)` for every `n ≥ 2`.

Proof.
* `κ ≤ d`: the Herglotz continuation caps the pole weight at the residue of `ζ`
  (`WeilPoleWeight.le_one_of_herglotz_poleWeightFunction`, a multiplicative Toeplitz density
  ceiling).
* `κ ≥ d`: the Herglotz continuation makes the pole-weight-`κ/d` functional nonnegative on every
  autocorrelation (`WeilPoleWeight.re_weilPoleWeightFunctional_nonneg_of_herglotz`), hence the
  degree functional with pole order `κ` too (`weilDegreePoleFunctional_eq_mul`).  For `κ < d` this
  contradicts the twisted-arc null tests (`not_forall_re_weilDegreePoleFunctional_nonneg`).
* `κ = d`: the degree functional is then nonnegative on every autocorrelation, so degree-`d` Weil
  positivity gives RH and `lam = d Λ` (`weilPositiveDegree_iff`).

So, given Weil's explicit formula and the Hadamard product for `T`, a Dirichlet series with real
coefficients, gamma factor `Γ_ℝ(s)^d`, conductor `1`, leading coefficient `1` and only critical
zeros is `ζ^d`, whatever its pole order.
-/

open Complex Zeta23

noncomputable section

namespace RHTower

/-- **Herglotz data with the gamma factor `Γ_ℝ^d` are `d Λ`, with pole order `d`, and RH holds.** -/
theorem pole_order_eq_and_eq_smul_vonMangoldt_of_herglotz {d κ : ℝ} (hd : 0 < d)
    {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n / d| / (n : ℝ) ^ σ)
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, 1 < s.re → Φ s = WeilPoleWeight.poleWeightFunction (κ / d) (fun n => lam n / d) s)
    {A : ℝ}
    (hA : ∀ N : ℕ, |WeilSpectral.primeWeightPartialSum
      (fun n => lam n / d - ArithmeticFunction.vonMangoldt n) N| ≤ A * (N + 1)) :
    κ = d ∧ RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = d * (ArithmeticFunction.vonMangoldt n : ℝ) := by
  -- positivity of the pole-weight functional from the Herglotz continuation
  have hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (WeilPoleWeight.weilPoleWeightFunctional (κ / d) (fun n => lam n / d)
        (EF.weilTest f f)).re :=
    fun f hf hfc => WeilPoleWeight.re_weilPoleWeightFunctional_nonneg_of_herglotz hsl hΦd hΦre hΦ
      hf hfc
  have hdeg : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilDegreePoleFunctional d κ lam (EF.weilTest f f)).re := fun f hf hfc => by
    rw [weilDegreePoleFunctional_eq_mul hd.ne', re_ofReal_mul]
    exact mul_nonneg hd.le (hpos f hf hfc)
  -- κ ≤ d
  have hle : κ ≤ d := by
    have h := WeilPoleWeight.le_one_of_herglotz_poleWeightFunction hsl hΦd hΦre hΦ
    rwa [div_le_one hd] at h
  -- κ ≥ d
  have hge : d ≤ κ := by
    by_contra hlt
    exact not_forall_re_weilDegreePoleFunctional_nonneg hd (not_le.mp hlt) hA
      fun F hF hFc => hdeg (fun u => (F u : ℂ)) hF (hFc.comp_left Complex.ofReal_zero)
  have hκ : κ = d := le_antisymm hle hge
  -- degree-d Weil positivity
  have hW : WeilPositiveDegree d lam := fun f hf hfc => by
    have h := hdeg f hf hfc
    unfold weilDegreePoleFunctional at h
    rwa [hκ, sub_self, Complex.ofReal_zero, zero_mul, add_zero] at h
  exact ⟨hκ, ((weilPositiveDegree_iff hd).mp hW).1, ((weilPositiveDegree_iff hd).mp hW).2⟩

end RHTower
