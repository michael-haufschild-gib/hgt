import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothSubrepresentation
import Mathlib.RepresentationTheory.Coinduced

/-! Smooth induction is the smooth subrepresentation of the
equivariant function space, with right translations. The maps on
inducing representations act by postcomposition. -/

noncomputable section

namespace Representation

variable {G H V W : Type*} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (f : H →* G) (ρ : Representation ℂ H V)

/-- Smooth left-equivariant functions with the right translation action. -/
def smoothInduction : Representation ℂ G ((coind f ρ).smoothVectors) :=
  (coind f ρ).smoothPart

theorem smooth_smoothInduction (v : (coind f ρ).smoothVectors) :
    IsOpen {g : G | smoothInduction f ρ g v = v} :=
  (coind f ρ).smooth_smoothPart v

@[simp] theorem smoothInduction_apply (g : G) (u : (coind f ρ).smoothVectors) (x : G) :
    (smoothInduction f ρ g u).val.val x = u.val.val (x * g) := rfl

theorem smoothInduction_equivariance (u : (coind f ρ).smoothVectors) (h : H) (g : G) :
    u.val.val (f h * g) = ρ h (u.val.val g) :=
  u.val.2 h g

variable {ρ}

private theorem intertwining_map_mem_smoothVectors {π : Representation ℂ G V} {τ : Representation ℂ G W}
    (e : π.IntertwiningMap τ) (v : π.smoothVectors) : e v.val ∈ τ.smoothVectors := by
  rw [mem_smoothVectors]
  apply τ.isOpen_vectorStabilizer_of_open_subgroup (H := π.vectorStabilizer v.val)
    ((π.mem_smoothVectors v.val).mp v.2)
  intro g hg
  change π g v.val = v.val at hg
  rw [← IntertwiningMap.isIntertwining π τ e, hg]

def smoothInductionMap {τ : Representation ℂ H W} (e : ρ.IntertwiningMap τ) :
    (smoothInduction f ρ).IntertwiningMap (smoothInduction f τ) where
  toLinearMap := ((coindMap f e).toLinearMap.comp (coind f ρ).smoothVectors.subtype).codRestrict
    (coind f τ).smoothVectors (intertwining_map_mem_smoothVectors (coindMap f e))
  isIntertwining' g := LinearMap.ext fun v => Subtype.ext
    (IntertwiningMap.isIntertwining (coind f ρ) (coind f τ) (coindMap f e) g v.val)

theorem smoothInductionMap_injective {τ : Representation ℂ H W} (e : ρ.IntertwiningMap τ)
    (he : Function.Injective e) : Function.Injective (smoothInductionMap f e) := by
  intro v w hvw
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply he
  exact congrArg (fun x : (coind f τ).smoothVectors => x.val.val g) hvw

end Representation

#print axioms Representation.smooth_smoothInduction
#print axioms Representation.smoothInductionMap_injective
