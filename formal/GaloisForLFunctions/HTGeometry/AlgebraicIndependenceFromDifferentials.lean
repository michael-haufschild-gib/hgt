import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Independent differentials give algebraic independence

A polynomial vanishing on a nonempty open subset of `ℂ^r` is zero: polynomial
functions are entire, `ℂ^r` is connected, and the identity theorem propagates
the vanishing to the whole space.

Consequently a family of `r` functions whose assembled differential at a point
is injective satisfies no nonzero polynomial relation near that point: the map
is open at the point, so the polynomial would vanish on an open set of the
target.

This is the mechanism that converts a differential-rank statement into an
algebraic-independence statement.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Polynomials vanishing on an open set -/

/-- **A polynomial vanishing on a nonempty open set is zero.** -/
theorem mvPolynomial_eq_zero_of_eqOn_zero_isOpen {ι : Type*} [Fintype ι]
    {P : MvPolynomial ι ℂ} {U : Set (ι → ℂ)} (hU : IsOpen U) {z₀ : ι → ℂ}
    (hz₀ : z₀ ∈ U) (h : ∀ z ∈ U, MvPolynomial.eval z P = 0) : P = 0 := by
  have hana : AnalyticOnNhd ℂ (fun z : ι → ℂ => MvPolynomial.eval z P) Set.univ :=
    AnalyticOnNhd.eval_mvPolynomial P
  have hev : (fun z : ι → ℂ => MvPolynomial.eval z P) =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hU.mem_nhds hz₀] with w hw
    exact h w hw
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z₀) hev
  refine MvPolynomial.funext fun x => ?_
  have := hzero (Set.mem_univ x)
  simpa using this

/-! ### Algebraic independence from an invertible differential -/

/-- **No polynomial relation near a point of invertible differential.** -/
theorem mvPolynomial_eq_zero_of_hasStrictFDerivAt_equiv {ι : Type*} [Fintype ι]
    {G : (ι → ℂ) → (ι → ℂ)} {z₀ : ι → ℂ} {G' : (ι → ℂ) ≃L[ℂ] (ι → ℂ)}
    (hG : HasStrictFDerivAt G (G' : (ι → ℂ) →L[ℂ] (ι → ℂ)) z₀)
    {U : Set (ι → ℂ)} (hU : U ∈ 𝓝 z₀) {P : MvPolynomial ι ℂ}
    (h : ∀ z ∈ U, MvPolynomial.eval (G z) P = 0) : P = 0 := by
  have hmap : Filter.map G (𝓝 z₀) = 𝓝 (G z₀) := hG.map_nhds_eq_of_equiv
  have himg : G '' U ∈ 𝓝 (G z₀) := by
    rw [← hmap]
    exact Filter.image_mem_map hU
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.1 himg
  refine mvPolynomial_eq_zero_of_eqOn_zero_isOpen hVopen hVmem fun w hw => ?_
  obtain ⟨z, hz, rfl⟩ := hVsub hw
  exact h z hz

/-- **No polynomial relation near a point of injective differential.**  In
finitely many variables an injective differential is invertible. -/
theorem mvPolynomial_eq_zero_of_hasStrictFDerivAt_injective {ι : Type*}
    [Fintype ι] {G : (ι → ℂ) → (ι → ℂ)} {z₀ : ι → ℂ}
    {L : (ι → ℂ) →L[ℂ] (ι → ℂ)} (hG : HasStrictFDerivAt G L z₀)
    (hinj : Function.Injective L) {U : Set (ι → ℂ)} (hU : U ∈ 𝓝 z₀)
    {P : MvPolynomial ι ℂ} (h : ∀ z ∈ U, MvPolynomial.eval (G z) P = 0) :
    P = 0 := by
  classical
  have hlin : Function.Injective (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) := hinj
  let eL : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ) :=
    LinearMap.linearEquivOfInjective (L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) hlin rfl
  let e : (ι → ℂ) ≃L[ℂ] (ι → ℂ) := eL.toContinuousLinearEquiv
  have hcoe : (e : (ι → ℂ) →L[ℂ] (ι → ℂ)) = L := by
    ext z
    rfl
  refine mvPolynomial_eq_zero_of_hasStrictFDerivAt_equiv (G' := e) ?_ hU h
  rw [hcoe]
  exact hG

/-- The assembled map of a finite family of scalar functions. -/
def assembleFamily {ι : Type*} (G : ι → (ι → ℂ) → ℂ) : (ι → ℂ) → (ι → ℂ) :=
  fun z i => G i z

/-- **Algebraic independence from independent differentials.**  If the
assembled differential of a finite family of functions is injective at a point,
then no nonzero polynomial annihilates the family near that point. -/
theorem mvPolynomial_eq_zero_of_family_hasStrictFDerivAt {ι : Type*} [Fintype ι]
    {G : ι → (ι → ℂ) → ℂ} {z₀ : ι → ℂ} {L : (ι → ℂ) →L[ℂ] (ι → ℂ)}
    (hG : HasStrictFDerivAt (assembleFamily G) L z₀)
    (hinj : Function.Injective L) {U : Set (ι → ℂ)} (hU : U ∈ 𝓝 z₀)
    {P : MvPolynomial ι ℂ}
    (h : ∀ z ∈ U, MvPolynomial.eval (fun i => G i z) P = 0) : P = 0 :=
  mvPolynomial_eq_zero_of_hasStrictFDerivAt_injective hG hinj hU h

end

end GaloisForLFunctions.HTGeometry
