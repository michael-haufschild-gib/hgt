import GaloisForLFunctions.PrimeTorusTheory.TheNaturalBoundaryOverOrderTwoPoints

/-!
# The natural boundary is Liouville-odd

For two completely multiplicative unimodular functions `f`, `g` with `g(p) = −f(p)` at every prime
(a point and its Liouville translate), the local factors multiply to
`(1 − f(p)p^{−s})^{−1}(1 + f(p)p^{−s})^{−1} = (1 − f(p)²p^{−2s})^{−1}`. At an order-two point
`f(p)² = 1`, so

* **the twin product** (`tsum_mul_tsum_twin`): `L_f(s) L_g(s) = ζ(2s)` on `Re s > 1`.

The antipode `ω ↦ ½ − ω` of the coin space preserves the coin measure and flips every sign
(`measurePreserving_flip`, `X_prime_flip`). Combined with the natural boundary of a typical
order-two fibre (`ae_sign_natural_boundary`):

* **the natural boundary is Liouville-odd** (`ae_twin_natural_boundary`). For almost every
  order-two point `ω`, the fibres over `ω` and over its antipode both extend zero-free to
  `Re s > ½` and both have the critical line as natural boundary, while their product is `ζ(2s)` on
  all of `Re s > ½`: meromorphic in the whole plane, with its only pole at `s = ½`.

So the boundary is carried by the odd part `Σ_p Σ_{k odd} f(p)^k p^{−ks}/k` of the logarithm, which the
antipode reverses; the even part is the fixed function `log ζ(2s)`. Wherever a typical fibre blows up
along a ray to the line, its antipode tends to zero at the reciprocal rate.
-/

open MeasureTheory Filter Topology Metric Complex
open _root_.RHTower.SteinhausModel

noncomputable section

namespace GaloisForLFunctions.PrimeTorusTheory

open GaloisForLFunctions.RHTower

/-! ### The twin product -/

/-- **The twin product.** If `f(p) = ±1` and `g(p) = −f(p)` at every prime, then
`(Σ f(n) n^{−s})(Σ g(n) n^{−s}) = ζ(2s)` on `Re s > 1`. -/
theorem tsum_mul_tsum_twin {f g : ℕ →*₀ ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (hsign : ∀ p, p.Prime → f p ^ 2 = 1) (hfg : ∀ p, p.Prime → g p = -f p) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' n, f n * (n : ℂ) ^ (-s)) * (∑' n, g n * (n : ℂ) ^ (-s)) = riemannZeta (2 * s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs; linarith
  have hs2 : 1 < (2 * s).re := by rw [show (2 * s).re = 2 * s.re by simp]; linarith
  have hF := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (summable_norm_twistedHom hf hs hs0)
  have hG := EulerProduct.eulerProduct_completely_multiplicative_hasProd
    (summable_norm_twistedHom hg hs hs0)
  have hprod := hF.mul hG
  have hfac : (fun p : Nat.Primes => (1 - twistedHom f hs0 p)⁻¹ * (1 - twistedHom g hs0 p)⁻¹) =
      fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by
    funext p
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    have hpow : ((p : ℕ) : ℂ) ^ (-(2 * s)) = ((p : ℕ) : ℂ) ^ (-s) * ((p : ℕ) : ℂ) ^ (-s) := by
      rw [← Complex.cpow_add _ _ hp0]; ring_nf
    rw [twistedHom_apply, twistedHom_apply, hfg p p.prop, ← mul_inv, hpow]
    congr 1
    linear_combination (-(((p : ℕ) : ℂ) ^ (-s)) ^ 2) * hsign p p.prop
  rw [hfac] at hprod
  have h := hprod.unique (riemannZeta_eulerProduct_hasProd hs2)
  simpa only [twistedHom_apply] using h

/-! ### The antipode of the coin space -/

/-- The antipode `ω ↦ ½ − ω` exchanges the two phases of every coin. -/
def flip (ω : Omega) : Omega := fun n => 1 / 2 - ω n

theorem measurePreserving_flip : MeasurePreserving flip signMeasure signMeasure := by
  have hcoin : coin.map (fun r : ℝ => 1 / 2 - r) = coin := by
    have hm : Measurable fun r : ℝ => 1 / 2 - r := by fun_prop
    rw [coin, Measure.map_smul, Measure.map_add _ _ hm, Measure.map_dirac' hm, Measure.map_dirac' hm]
    norm_num
    rw [add_comm]
  refine ⟨by unfold flip; fun_prop, ?_⟩
  unfold signMeasure flip
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => coin) (f := fun (_ : ℕ) (r : ℝ) => 1 / 2 - r)
    (fun _ => by fun_prop)
  simp only [hcoin] at h
  exact h

/-- At an order-two point the antipode flips every prime sign. -/
theorem X_prime_flip {ω : Omega} {p : ℕ} (hp : p.Prime) (h : X p ω = 1 ∨ X p ω = -1) :
    X p (flip ω) = -X p ω := by
  have hconj : X p (flip ω) = -(X p ω)⁻¹ := by
    rw [X_prime_eq hp, X_prime_eq hp, flip, ← Complex.exp_neg]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (((1 / 2 - ω p : ℝ)) : ℂ) =
      Real.pi * Complex.I + -(((2 * Real.pi : ℝ) : ℂ) * Complex.I * ((ω p : ℝ) : ℂ)) by
        push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [hconj]
  rcases h with h | h <;> rw [h] <;> norm_num

/-! ### The natural boundary is Liouville-odd -/

/-- The data of a fibre with the critical line as natural boundary. -/
def HasNaturalBoundary (ω : Omega) (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F rightHalf ∧ (∀ s, 1 < s.re → F s = ∑' n, signHom ω n * (n : ℂ) ^ (-s)) ∧
    (∀ s ∈ rightHalf, F s ≠ 0) ∧
    ∀ (τ₀ r : ℝ) (H : ℂ → ℂ), 0 < r → AnalyticOnNhd ℂ H (ball (⟨1 / 2, τ₀⟩ : ℂ) r) →
      ¬ ∀ s ∈ ball (⟨1 / 2, τ₀⟩ : ℂ) r, s ∈ rightHalf → H s = F s

/-- **The natural boundary is Liouville-odd.** For almost every order-two point `ω`, the fibres over
`ω` and over its antipode both have the critical line as natural boundary, and their product is
`ζ(2s)` throughout `Re s > ½`. -/
theorem ae_twin_natural_boundary :
    ∀ᵐ ω ∂signMeasure, ∃ F F' : ℂ → ℂ, HasNaturalBoundary ω F ∧ HasNaturalBoundary (flip ω) F' ∧
      ∀ s ∈ rightHalf, F s * F' s = riemannZeta (2 * s) := by
  have h₁ := ae_sign_natural_boundary
  have h₂ : ∀ᵐ ω ∂signMeasure, (∀ p, p.Prime → X p (flip ω) = 1 ∨ X p (flip ω) = -1) ∧
      ∃ F : ℂ → ℂ, HasNaturalBoundary (flip ω) F :=
    measurePreserving_flip.quasiMeasurePreserving.ae h₁
  filter_upwards [h₁, h₂] with ω ⟨hsign, F, hFa, hFeq, hF0, hFb⟩ ⟨_, F', hF'⟩
  refine ⟨F, F', ⟨hFa, hFeq, hF0, hFb⟩, hF', ?_⟩
  obtain ⟨hF'a, hF'eq, -, -⟩ := hF'
  -- Twin product on `Re s > 1`.
  have hf2 : ∀ p, p.Prime → signHom ω p ^ 2 = 1 := by
    intro p hp
    rw [signHom_apply, if_neg hp.ne_zero]
    rcases hsign p hp with h | h <;> rw [h] <;> norm_num
  have hfg : ∀ p, p.Prime → signHom (flip ω) p = -signHom ω p := by
    intro p hp
    rw [signHom_apply, signHom_apply, if_neg hp.ne_zero, if_neg hp.ne_zero]
    exact X_prime_flip hp (hsign p hp)
  have hright : ∀ s : ℂ, 1 < s.re → F s * F' s = riemannZeta (2 * s) := by
    intro s hs
    rw [hFeq s hs, hF'eq s hs]
    exact tsum_mul_tsum_twin (norm_signHom_le ω) (norm_signHom_le (flip ω)) hf2 hfg hs
  -- Identity theorem on the connected half-plane `Re s > ½`.
  have hU : IsOpen rightHalf := isOpen_lt continuous_const Complex.continuous_re
  have hZ : AnalyticOnNhd ℂ (fun s => riemannZeta (2 * s)) rightHalf := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hU
    have hs' : 1 / 2 < s.re := hs
    have hne : 2 * s ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    exact ((differentiableAt_riemannZeta hne).comp s
      ((differentiable_id.const_mul 2) s)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ rightHalf := by show (1 / 2 : ℝ) < (2 : ℂ).re; simp; norm_num
  have hev : (fun s => F s * F' s) =ᶠ[𝓝 (2 : ℂ)] fun s => riemannZeta (2 * s) := by
    have hopen1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen1.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)] with s hs
    exact hright s hs
  exact (hFa.mul hF'a).eqOn_of_preconnected_of_eventuallyEq hZ
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2 hev

end GaloisForLFunctions.PrimeTorusTheory

end
