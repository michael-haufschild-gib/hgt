import GaloisForLFunctions.RHTower.DeningerPoincareOneForm
import GaloisForLFunctions.RHTower.DeningerContractionIdentity

/-!
# The Poincaré lemma in every degree

A closed holomorphic form on a finite-dimensional complex vector space is exact, with the primitive
given by contracting against the base point along the segment to the origin.  The derivative of the
integrand splits into the contraction of the form itself and the contraction of its derivative;
antisymmetrizing turns the first into a multiple of the form and, by the contraction identity for
closed forms, the second into the derivative at the base point.  Together they are the derivative
in the segment parameter of the scaled form, so the integral telescopes.

* `deningerHomotopyKernel` : the integrand of the homotopy operator.
* `deningerHomotopyKDeriv` : its derivative in the base point.
* `deningerAlternatize_homotopyKDeriv` : antisymmetrizing the derivative of the integrand.
-/

namespace RHTower

open ContinuousAlternatingMap

section HomotopyKernel

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The integrand of the homotopy operator: the form at the scaled point, contracted against the
base point, weighted by the power of the segment parameter. -/
noncomputable def deningerHomotopyKernel (ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (t : ℝ) (y : E) :
    E [⋀^Fin n]→L[ℂ] ℂ :=
  ((t : ℂ) ^ n) • (ContinuousAlternatingMap.curryLeft (ω (deningerScale t y)) y)

/-- The derivative in the base point of the integrand of the homotopy operator. -/
noncomputable def deningerHomotopyKDeriv (ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ) (x : E) (t : ℝ) :
    E →L[ℂ] (E [⋀^Fin n]→L[ℂ] ℂ) :=
  ((t : ℂ) ^ n) • ((ContinuousAlternatingMap.curryLeft (ω (deningerScale t x))).comp
      (ContinuousLinearMap.id ℂ E) +
    (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.comp
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t))).flip x))

/-- The integrand of the homotopy operator is differentiable in the base point. -/
theorem deningerHomotopyKernel_hasFDerivAt {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hana : AnalyticOnNhd ℂ ω Set.univ) (x : E) (t : ℝ) :
    HasFDerivAt (deningerHomotopyKernel ω t) (deningerHomotopyKDeriv ω x t) x := by
  have hω : HasFDerivAt ω (fderiv ℂ ω (deningerScale t x)) (deningerScale t x) :=
    (hana _ (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hscale : HasFDerivAt (fun y : E => deningerScale t y) (deningerScale t) x :=
    (deningerScale t).hasFDerivAt
  have hcomp : HasFDerivAt (fun y : E => ω (deningerScale t y))
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t)) x := hω.comp x hscale
  have hcurry : HasFDerivAt (fun y : E => ContinuousAlternatingMap.curryLeft (ω (deningerScale t y)))
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.comp
        ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t))) x :=
    HasFDerivAt.comp (g := ⇑(ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
      (n := n)).toContinuousLinearMap) x
      ((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.hasFDerivAt) hcomp
  have happ := hcurry.clm_apply (hasFDerivAt_id x)
  exact happ.const_smul ((t : ℂ) ^ n)

end HomotopyKernel

section AlternatizeIdentity

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The flipped contraction of a derivative, evaluated. -/
theorem deningerFlip_contract_eq {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ} (x : E) (t : ℝ) :
    (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℂ) (E := E) (F := ℂ)
        (n := n)).toContinuousLinearMap.comp
      ((fderiv ℂ ω (deningerScale t x)).comp (deningerScale t))).flip x) =
      (t : ℂ) • ((deningerContractCLM x).comp (fderiv ℂ ω (deningerScale t x))) := by
  refine ContinuousLinearMap.ext fun u => ?_
  show ContinuousAlternatingMap.curryLeft
      ((fderiv ℂ ω (deningerScale t x)) ((t : ℂ) • u)) x =
    (t : ℂ) • (deningerContractCLM x ((fderiv ℂ ω (deningerScale t x)) u))
  rw [map_smul]
  ext v
  show ((t : ℂ) • (fderiv ℂ ω (deningerScale t x)) u) (Fin.cons x v) =
    (t : ℂ) • ((fderiv ℂ ω (deningerScale t x)) u) (Fin.cons x v)
  rfl

/-- **Antisymmetrizing the derivative of the integrand** of the homotopy operator: the contraction
of the form contributes a multiple of the form, and the contraction of its derivative contributes
the derivative at the base point. -/
theorem deningerAlternatize_homotopyKDeriv {ω : E → E [⋀^Fin (n + 1)]→L[ℂ] ℂ}
    (hclosed : ∀ y : E, extDeriv ω y = 0) (x : E) (t : ℝ) :
    alternatizeUncurryFin (deningerHomotopyKDeriv ω x t) =
      ((n + 1 : ℕ) • ((t : ℂ) ^ n • ω (deningerScale t x))) +
        ((t : ℂ) ^ (n + 1)) • ((fderiv ℂ ω (deningerScale t x)) x) := by
  rw [deningerHomotopyKDeriv, alternatizeUncurryFin_smul, deningerFlip_contract_eq,
    ContinuousLinearMap.comp_id, alternatizeUncurryFin_add, alternatizeUncurryFin_curryLeft,
    alternatizeUncurryFin_smul]
  have hB : alternatizeUncurryFin (fderiv ℂ ω (deningerScale t x)) = 0 := hclosed _
  rw [deningerAlternatize_contract _ hB]
  rw [smul_add, smul_comm ((t : ℂ) ^ n) (n + 1 : ℕ), smul_smul, ← pow_succ]

end AlternatizeIdentity

end RHTower
