import GaloisForLFunctions.HTGeometry.LaguerreShiftRealRootCount
import GaloisForLFunctions.RHTower.XiLaguerrePolyaRiemannHypothesis

/-!
# First-order Laguerre–Pólya preimages of Ξ force the Riemann hypothesis

The operator `1 − cD` (`c` real) maps the Laguerre–Pólya class into itself: on real-rooted
polynomials `p − c p′` loses no real root and has the degree of `p`, so it is again real-rooted,
and locally uniform limits pass to derivatives.

* `splits_sub_C_mul_derivative`: `p` real-rooted ⇒ `p − c p′` real-rooted;
* `laguerrePolya_sub_smul_deriv`: `F ∈ LP` ⇒ `F − c F′ ∈ LP`;
* `riemannHypothesis_of_XiC_eq_sub_smul_deriv`: if `XiC = ψ − c ψ′` for some `ψ ∈ LP`, then RH.

This is the reduction step of the Laguerre–Pólya maximality theorem for Ξ: any first-order
Laguerre–Pólya preimage of Ξ may be studied under the Riemann hypothesis.
-/

open Polynomial Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- `p − c p′` is real-rooted whenever `p` is. -/
theorem splits_sub_C_mul_derivative {p : ℝ[X]} (hp : p.Splits) (c : ℝ) :
    (p - C c * derivative p).Splits := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  have hq0 := sub_C_mul_derivative_ne_zero hp0 c
  have hcard := card_roots_le_sub_C_mul_derivative p hc
  have hdeg := natDegree_sub_C_mul_derivative p c
  rw [splits_iff_card_roots] at hp ⊢
  refine le_antisymm (card_roots' _) ?_
  rw [hdeg, ← hp]
  exact hcard

/-- **The Laguerre–Pólya class is closed under `1 − cD`.** -/
theorem laguerrePolya_sub_smul_deriv {F : ℂ → ℂ}
    (hF : GaloisForLFunctions.HTGeometry.LaguerrePolya F) (c : ℝ) :
    GaloisForLFunctions.HTGeometry.LaguerrePolya (fun z => F z - (c : ℂ) * deriv F z) := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  refine ⟨fun m => p m - C c * derivative (p m), fun m => splits_sub_C_mul_derivative (hsplit m) c,
    ?_⟩
  have hd := tendstoLocallyUniformly_iterate_deriv hconv (fun m => differentiable_polyEvalC (p m)) 1
  simp only [Function.iterate_one] at hd
  have hfun : (fun m => polyEvalC (p m - C c * derivative (p m))) =
      fun m z => polyEvalC (p m) z - (c : ℂ) * deriv (polyEvalC (p m)) z := by
    funext m z
    rw [deriv_polyEvalC]
    simp [polyEvalC, map_sub, map_mul]
  rw [hfun]
  have hd' : TendstoLocallyUniformly (fun m z => (c : ℂ) * deriv (polyEvalC (p m)) z)
      (fun z => (c : ℂ) * deriv F z) atTop :=
    (uniformContinuous_const_smul (c : ℂ)).comp_tendstoLocallyUniformly hd
  exact hconv.sub hd'

/-- **WLOG RH for first-order preimages.** If `XiC = ψ − c ψ′` with `ψ` in the Laguerre–Pólya
class, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_XiC_eq_sub_smul_deriv {ψ : ℂ → ℂ}
    (hψ : GaloisForLFunctions.HTGeometry.LaguerrePolya ψ) (c : ℝ)
    (h : ∀ z, XiC z = ψ z - (c : ℂ) * deriv ψ z) : RiemannHypothesis := by
  apply riemannHypothesis_of_laguerrePolya_XiC
  have hfun : XiC = fun z => ψ z - (c : ℂ) * deriv ψ z := funext h
  rw [hfun]
  exact laguerrePolya_sub_smul_deriv hψ c

end

end RHTower
