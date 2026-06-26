/-
# τ-derivatives of the Jacobi theta nullwerte θ₂, θ₃, θ₄

The theta constants (nullwerte) `θ₃ = Θ(0,·)`, `θ₄ = Θ(1/2,·)`, `θ₂ = exp(πiτ/4)·Θ(τ/2,·)` carry the
modular `λ = (θ₂/θ₃)⁴`. Their `τ`-derivatives are the first ingredient of the *theta differential
equations* — the system the nullwerte satisfy via the heat equation `∂_z²Θ = 4πi ∂_τΘ`
(`ThetaHeat.lean`), and the route by which the heat layer reaches the Jacobi quartic identity
`θ₃⁴ = θ₂⁴ + θ₄⁴` (⟹ `λ` omits `1`).

* `hasDerivAt_thetaThree`, `hasDerivAt_thetaFour` — `z` fixed, direct specializations of
  `hasDerivAt_jacobiTheta₂_snd`.
* `hasDerivAt_thetaTwo` — both factors `τ`-dependent (the `z`-slot is `τ/2`); product rule on the
  exponential prefactor and the chain rule `Θ∘(τ ↦ (τ/2,τ))` via the joint Fréchet derivative
  `jacobiTheta₂_fderiv` evaluated on the tangent `(1/2,1)`.

Consumes `ThetaHeat` + `ModularLambda`. Mathlib only otherwise.
-/
import GaloisForLFunctions.Bottcher.ThetaHeat
import GaloisForLFunctions.Bottcher.ModularLambda
open Complex Real Filter
open scoped Real Topology
namespace Bottcher

/-- **τ-derivative of the nullwert `θ₃`** (`= Θ(0,·)`): `θ₃′(τ) = ∑ πin²·term n 0 τ`. -/
theorem hasDerivAt_thetaThree {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt thetaThree (∑' n, jacobiTheta₂_snd_term n 0 τ) τ :=
  hasDerivAt_jacobiTheta₂_snd 0 hτ

/-- **τ-derivative of the nullwert `θ₄`** (`= Θ(1/2,·)`): `θ₄′(τ) = ∑ πin²·term n (1/2) τ`. -/
theorem hasDerivAt_thetaFour {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt thetaFour (∑' n, jacobiTheta₂_snd_term n (1/2) τ) τ :=
  hasDerivAt_jacobiTheta₂_snd (1/2) hτ

/-- **τ-derivative of the nullwert `θ₂`** (`= exp(πiτ/4)·Θ(τ/2,·)`). Product rule on the exponential
prefactor and `Θ(τ/2,τ)`; the inner factor is `Θ∘(τ ↦ (τ/2,τ))`, differentiated by the joint Fréchet
derivative `jacobiTheta₂_fderiv` evaluated on the tangent `(1/2,1)`. -/
theorem hasDerivAt_thetaTwo {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt thetaTwo
      ((π : ℂ) * I / 4 * Complex.exp ((π : ℂ) * I * τ / 4) * jacobiTheta₂ (τ/2) τ
        + Complex.exp ((π : ℂ) * I * τ / 4) * (jacobiTheta₂_fderiv (τ/2) τ) (1/2, 1)) τ := by
  have hexp : HasDerivAt (fun s : ℂ => Complex.exp ((π : ℂ) * I * s / 4))
      ((π : ℂ) * I / 4 * Complex.exp ((π : ℂ) * I * τ / 4)) τ := by
    have h0 : HasDerivAt (fun s : ℂ => (π : ℂ) * I * s / 4) ((π : ℂ) * I / 4) τ := by
      simpa using (((hasDerivAt_id τ).const_mul ((π : ℂ) * I)).div_const 4)
    simpa [mul_comm] using h0.cexp
  have hφ : HasDerivAt (fun s : ℂ => ((s / 2, s) : ℂ × ℂ)) ((1/2, 1) : ℂ × ℂ) τ :=
    ((hasDerivAt_id τ).div_const 2).prodMk (hasDerivAt_id τ)
  have hcomp : HasDerivAt (fun s => jacobiTheta₂ (s/2) s)
      ((jacobiTheta₂_fderiv (τ/2) τ) (1/2, 1)) τ := by
    have h := (hasFDerivAt_jacobiTheta₂ (τ/2) hτ).comp_hasDerivAt
      (f := fun s : ℂ => ((s / 2, s) : ℂ × ℂ)) τ hφ
    convert h using 1
  have hmul := hexp.mul hcomp
  unfold thetaTwo
  convert hmul using 1

end Bottcher
