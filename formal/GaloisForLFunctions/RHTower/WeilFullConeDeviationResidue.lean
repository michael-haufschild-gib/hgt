import GaloisForLFunctions.RHTower.WeilFullConeHorizontalPotential
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiDivisorContour

/-!
# The deviation of a Weil-positive system carries every zero right of the critical line

Let `lam` be full-cone Weil-positive with Herglotz continuation `Φ_lam` (`weilContinuation`).  On
`Re s > 1` the difference `ξ'/ξ − Φ_lam` is the deviation series
`Σ_{n≥2} (lam(n) − Λ(n)) n^{−s}` (`logDeriv_xi_sub_weilContinuation_eq`).

**Theorem** (`tendsto_sub_mul_logDeriv_xi_sub_weilContinuation`).  At every point `s₀` with
`Re s₀ > 1/2`, `(s − s₀)(ξ'/ξ − Φ_lam)(s) → ord_{s₀} ξ`.

So the continued deviation series has a simple pole of residue exactly the multiplicity at every
zero of `ξ` off the critical line, and is regular elsewhere on `Re s > 1/2`.  Every producer
carries the complete off-line divisor of `ξ` in its deviation from `Λ`: positivity of `Φ_lam`
leaves no room to absorb any part of it.

**Proof.**  `Φ_lam` is holomorphic on `Re s > 1/2`, so `(s − s₀)Φ_lam(s) → 0`; and
`(s − s₀)ξ'/ξ(s) → ord_{s₀} ξ` because `ξ` is entire and not identically zero.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- On `Re s > 1`, `ξ'/ξ − Φ_lam` is the Dirichlet series of the deviation `lam − Λ`. -/
theorem logDeriv_xi_sub_weilContinuation_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv xi s - weilContinuation hW s =
      LSeries (lamC lam) s - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [weilContinuation_eq hW hs, logDeriv_xi_eq_datum hs, weilFunction, zetaArchimedeanDatum]
  ring

/-- **Every producer's deviation has residue `ord ξ` at every point right of the line.** -/
theorem tendsto_sub_mul_logDeriv_xi_sub_weilContinuation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s₀ : ℂ} (hs₀ : 1 / 2 < s₀.re) :
    Tendsto (fun s => (s - s₀) * (logDeriv xi s - weilContinuation hW s)) (𝓝[≠] s₀)
      (𝓝 (analyticOrderNatAt xi s₀ : ℂ)) := by
  have hxi := RiemannGaussian.AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (xi_differentiable.analyticAt s₀) (xi_orderAt_ne_top s₀)
  have hH : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 s₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs₀
  have hΦ : ContinuousAt (weilContinuation hW) s₀ :=
    ((differentiableOn_weilContinuation hW).differentiableAt hH).continuousAt
  have hlin : Tendsto (fun s : ℂ => (s - s₀) * weilContinuation hW s) (𝓝[≠] s₀) (𝓝 0) := by
    have h1 : ContinuousAt (fun s : ℂ => s - s₀) s₀ := by fun_prop
    have h : Tendsto (fun s : ℂ => (s - s₀) * weilContinuation hW s) (𝓝 s₀)
        (𝓝 ((s₀ - s₀) * weilContinuation hW s₀)) := (h1.mul hΦ).tendsto
    rw [sub_self, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := hxi.sub hlin
  rw [sub_zero] at h
  refine h.congr fun s => ?_
  ring

end RHTower.WeilSpectral

end
