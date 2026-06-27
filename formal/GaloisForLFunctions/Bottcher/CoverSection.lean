/-
# The `z`-section of the dyadic cover: single-valued inverse branches of `f^[k]`

The disconnected close (`noRelation_of_precompMap` / `precompMeroMap_ratfuncToMeroVia`) needs the cover's
`z`-PROJECTION `p₀` with `p₀∘ι = z`: a single-valued inverse branch of `f^[k]`.  `f^[k]` is `2^k`-to-1,
so this branch exists only where `f^[k]` is injective (a cover sheet); there it is analytic by the
inverse function theorem.  This file builds those branches — the section side of the cover, dual to the
`bc`-coordinate charts of `CoverChart`.  On a domain where `f^[k]` is injective AND `bc` is univalent,
both the coordinate `bc` and the projection `ι` are single-valued: that is one sheet of the connected
dyadic cover.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Set Filter Topology

namespace Bottcher

/-- **Local analytic inverse of `f^[k]` off critical points.**  Where `(f^[k])'(z) = ∏_{j<k} 2·f^[j]z ≠
0`, `f^[k]` is a local biholomorphism, so there is a local holomorphic inverse `ι` (analytic at `f^[k]
z`) with `ι(f^[k] x) = x` near `z` and `f^[k](ι w) = w` near `f^[k] z` — the local `z`-section.  Built
from `hasStrictDerivAt_quadratic_iterate` and the analytic inverse function theorem
(`AnalyticAt.analyticAt_localInverse`), mirroring `exists_localInverse_bottcherCoord`. -/
theorem exists_localInverse_iterate (c : ℂ) (k : ℕ) {z : ℂ}
    (hz : (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z) ≠ 0) :
    ∃ ι : ℂ → ℂ, AnalyticAt ℂ ι ((quadratic c)^[k] z) ∧
      (∀ᶠ x in 𝓝 z, ι ((quadratic c)^[k] x) = x) ∧
      (∀ᶠ w in 𝓝 ((quadratic c)^[k] z), (quadratic c)^[k] (ι w) = w) := by
  have han : AnalyticAt ℂ (fun y => (quadratic c)^[k] y) z :=
    (analyticOnNhd_quadratic_iterate c k) z (mem_univ _)
  have hderiv : deriv (fun y => (quadratic c)^[k] y) z
      = ∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z :=
    (hasStrictDerivAt_quadratic_iterate c k z).hasDerivAt.deriv
  have hd0 : deriv (fun y => (quadratic c)^[k] y) z ≠ 0 := by rw [hderiv]; exact hz
  have hsd : HasStrictDerivAt (fun y => (quadratic c)^[k] y)
      (deriv (fun y => (quadratic c)^[k] y) z) z := han.hasStrictDerivAt
  exact ⟨hsd.localInverse _ _ _ hd0, han.analyticAt_localInverse hd0,
    hsd.eventually_left_inverse hd0, hsd.eventually_right_inverse hd0⟩

/-- **Global `z`-section: `f^[k]` is a biholomorphism onto its image on any critical-free univalent
domain.**  For open `A` on which `(f^[k])' ≠ 0` and `f^[k]` is injective, the inverse `ι = invFunOn
(f^[k]) A` left-inverts `f^[k]` on `A`, is analytic at every `f^[k] z`, and right-inverts on the image —
so `f^[k] : A → f^[k](A)` is a biholomorphism.  `ι` is the single-valued `z`-section of the dyadic cover
sheet `A` (`ι∘f^[k] = id`), the projection `p₀` the descent `noRelation_of_precompMap` needs.  Same
`invFunOn` + local-inverse argument as `CoverChart.exists_analytic_inverse_bottcher_of_injOn`. -/
theorem exists_analytic_inverse_iterate_of_injOn (c : ℂ) (k : ℕ) {A : Set ℂ}
    (hAo : IsOpen A) (hAcrit : ∀ z ∈ A, (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] z) ≠ 0)
    (hinj : Set.InjOn ((quadratic c)^[k]) A) :
    ∃ ι : ℂ → ℂ,
      (∀ z ∈ A, ι ((quadratic c)^[k] z) = z) ∧
      (∀ z ∈ A, AnalyticAt ℂ ι ((quadratic c)^[k] z)) ∧
      (∀ z ∈ A, ∀ᶠ w in 𝓝 ((quadratic c)^[k] z), (quadratic c)^[k] (ι w) = w) := by
  classical
  set ι : ℂ → ℂ := Function.invFunOn ((quadratic c)^[k]) A with hιdef
  have hleft : ∀ z ∈ A, ι ((quadratic c)^[k] z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  refine ⟨ι, hleft, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_iterate c k (hAcrit z₀ hz₀)
    have hlocAtz₀ : loc ((quadratic c)^[k] z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 ((quadratic c)^[k] z₀), loc w ∈ A :=
      hlocAn.continuousAt.preimage_mem_nhds (by rw [hlocAtz₀]; exact hAo.mem_nhds hz₀)
    have hagree : ι =ᶠ[𝓝 ((quadratic c)^[k] z₀)] loc := by
      filter_upwards [hlocInA, hlocRight] with w hwA hwRight
      have hex : ∃ a ∈ A, (quadratic c)^[k] a = w := ⟨loc w, hwA, hwRight⟩
      exact hinj (Function.invFunOn_mem hex) hwA (by rw [Function.invFunOn_eq hex, hwRight])
    exact hlocAn.congr hagree.symm
  · intro z₀ hz₀
    obtain ⟨loc, hlocAn, hlocLeft, hlocRight⟩ := exists_localInverse_iterate c k (hAcrit z₀ hz₀)
    have hlocAtz₀ : loc ((quadratic c)^[k] z₀) = z₀ := hlocLeft.self_of_nhds
    have hlocInA : ∀ᶠ w in 𝓝 ((quadratic c)^[k] z₀), loc w ∈ A :=
      hlocAn.continuousAt.preimage_mem_nhds (by rw [hlocAtz₀]; exact hAo.mem_nhds hz₀)
    filter_upwards [hlocInA, hlocRight] with w hwA hwRight
    exact Function.invFunOn_eq ⟨loc w, hwA, hwRight⟩

end Bottcher

namespace Bottcher
open Set Filter Topology

/-- **The deep `z`-section `p₀ = ι_f ∘ ψ_bc` of the dyadic cover.**  Composing the `bc`-inverse chart
`ψbc` (`CoverChart`, `ψbc∘bc = id` on `B`) with the `f^[k]`-inverse `z`-section `ιf`
(`exists_analytic_inverse_iterate_of_injOn`, `ιf∘f^[k] = id` on `A`): along the cover coordinate
`ι = bc∘f^[k] : z ↦ bc(f^[k] z)` (`= φc₁^{2^k}` by `bottcherCoord_iterate`), the composite `p₀ = ιf∘ψbc`
recovers `z`: `p₀(bc(f^[k] z)) = z` on `A` (given `f^[k](A) ⊆ B`).  So `p₀∘ι = id` — exactly the
single-valued projection `noRelation_of_precompMap` / `ratfuncToMeroVia` consume to make the descent
`ℂ(z)`-linear, built from the two single-valued inverse charts.  The cover field `B = meroField(image)`
with `bc` non-square (`SquareFree.bottcherGerm_not_isSquare`) and this `p₀` feeds the DONE Kummer close. -/
theorem deep_section_composition {c : ℂ} (k : ℕ) {ψbc ιf : ℂ → ℂ} {A B : Set ℂ}
    (hψ : ∀ z ∈ B, ψbc (bottcherCoord c z) = z)
    (hι : ∀ z ∈ A, ιf ((quadratic c)^[k] z) = z)
    (hAB : ∀ z ∈ A, (quadratic c)^[k] z ∈ B) :
    ∀ z ∈ A, (ιf ∘ ψbc) (bottcherCoord c ((quadratic c)^[k] z)) = z := by
  intro z hz
  show ιf (ψbc (bottcherCoord c ((quadratic c)^[k] z))) = z
  rw [hψ ((quadratic c)^[k] z) (hAB z hz), hι z hz]

end Bottcher
