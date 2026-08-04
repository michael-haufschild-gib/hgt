import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Complete drives and separating readouts determine a clock response

The two-mass calibration theorems consume the *complete* measured response operators. What a
laboratory produces instead is a family of numbers: one readout value per probe drive.

This file proves that the numbers determine the operator. If the drives span a dense subspace of the
source domain and the readouts separate responses, then two response operators with the same data
are equal; if in addition the unknown endpoint gains are injective on the readout side and
surjective on the drive side, the *hidden* response operator behind them is determined as well.

Invertible endpoints are not needed: a *family* of couplings that jointly separates responses, and
drives whose images under the family span a dense subspace, determine the response just as well.

This is the identifiability half of the operational bridge; the quantitative half is the stability
estimate of the companion file.
-/

namespace GaloisForLFunctions.HTGeometry

section Determination

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {D E F G : Type*}
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {ι ι' : Type*}

/-- A family of readouts separates responses when the only response invisible to every readout is
the zero response. -/
def SeparatingReadouts (readout : ι → F →L[𝕜] 𝕜) : Prop :=
  ∀ y : F, (∀ i, readout i y = 0) → y = 0

/-- Separating readouts distinguish responses. -/
theorem eq_of_separatingReadouts {readout : ι → F →L[𝕜] 𝕜} (hsep : SeparatingReadouts readout)
    {y z : F} (h : ∀ i, readout i y = readout i z) : y = z := by
  have hzero : ∀ i, readout i (y - z) = 0 := by
    intro i
    rw [map_sub, h i, sub_self]
  have := hsep (y - z) hzero
  rwa [sub_eq_zero] at this

/-- **A complete family of drives and a separating family of readouts determine the response
operator.** -/
theorem responseOperator_eq_of_data {T S : E →L[𝕜] F} {drive : ι' → E}
    (hdense : Dense (Submodule.span 𝕜 (Set.range drive) : Set E))
    {readout : ι → F →L[𝕜] 𝕜} (hsep : SeparatingReadouts readout)
    (hdata : ∀ (i : ι) (j : ι'), readout i (T (drive j)) = readout i (S (drive j))) :
    T = S := by
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro x ⟨j, rfl⟩
  exact eq_of_separatingReadouts hsep fun i => hdata i j

/-- **The hidden response behind unknown endpoint gains is determined by the measured data.**
The readout side of the apparatus need only be injective and the drive side surjective; no
calibration of either is used. -/
theorem hiddenResponse_eq_of_data {T S : E →L[𝕜] F} (receiver : F →L[𝕜] G) (source : D →L[𝕜] E)
    (hreceiver : Function.Injective receiver) (hsource : Function.Surjective source)
    {drive : ι' → D} (hdense : Dense (Submodule.span 𝕜 (Set.range drive) : Set D))
    {readout : ι → G →L[𝕜] 𝕜} (hsep : SeparatingReadouts readout)
    (hdata : ∀ (i : ι) (j : ι'),
      readout i (receiver (T (source (drive j)))) = readout i (receiver (S (source (drive j))))) :
    T = S := by
  have hcomp : (receiver.comp (T.comp source)) = (receiver.comp (S.comp source)) :=
    responseOperator_eq_of_data hdense hsep hdata
  have hpt : ∀ v : D, receiver (T (source v)) = receiver (S (source v)) := by
    intro v
    exact congrArg (fun L : D →L[𝕜] G => L v) hcomp
  ext x
  obtain ⟨v, rfl⟩ := hsource x
  exact congrArg (fun y : F => y) (hreceiver (hpt v))

/-- **Separating families replace invertible couplings.** The apparatus need not implement a single
invertible endpoint pair: a family of couplings that jointly separates responses, together with
drives whose images span a dense subspace, determines the hidden response operator. -/
theorem hiddenResponse_eq_of_family_data {κ μ : Type*} {T S : E →L[𝕜] F}
    (receiver : κ → F →L[𝕜] G) (source : μ → D →L[𝕜] E) (drive : ι' → D)
    (hsep : ∀ y : F, (∀ k, receiver k y = 0) → y = 0)
    (hdense : Dense (Submodule.span 𝕜
      (⋃ m : μ, Set.range fun j : ι' => source m (drive j)) : Set E))
    {readout : ι → G →L[𝕜] 𝕜} (hread : SeparatingReadouts readout)
    (hdata : ∀ (i : ι) (k : κ) (m : μ) (j : ι'),
      readout i (receiver k (T (source m (drive j)))) =
        readout i (receiver k (S (source m (drive j))))) :
    T = S := by
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨m, j, rfl⟩ := hx
  have hdiff : ∀ k : κ, receiver k (T (source m (drive j)) - S (source m (drive j))) = 0 := by
    intro k
    rw [map_sub, sub_eq_zero]
    exact eq_of_separatingReadouts hread fun i => hdata i k m j
  have := hsep _ hdiff
  rwa [sub_eq_zero] at this

end Determination

section Dual

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The full family of continuous readouts always separates: a response invisible to every
continuous functional is the zero response. -/
theorem separatingReadouts_dual : SeparatingReadouts (fun φ : F →L[𝕜] 𝕜 => φ) := by
  intro y hy
  obtain ⟨g, _, hg⟩ := exists_dual_vector'' 𝕜 y
  have hzero : ((‖y‖ : ℝ) : 𝕜) = 0 := by
    rw [← hg]
    exact hy g
  have hnorm : ‖y‖ = 0 := by exact_mod_cast hzero
  exact norm_eq_zero.mp hnorm

end Dual

end GaloisForLFunctions.HTGeometry
