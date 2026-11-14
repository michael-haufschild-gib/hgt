import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.LinearAlgebra.Prod

/-!+# A canonical self-extension of a three-term complex

For a complex `U → V → W`, its total differential is `d(u,v,w) = (0,f(u),g(v))`.
The even-degree projection `h` satisfies `dh + hd = d`, and the grading sign `S`
anticommutes with `d`. On the doubled total module, multiplication by the dual-number
parameter is `z(x,y) = (0,x)`.

The maps `i(v) = (-dSv,Sv)`, `π(x,y) = x+dy`, and `Φ(v) = (hdv,hv)` form an exact
self-extension, commute with the respective square-zero operators, and satisfy `πΦ = d`.
This is the extension construction in the proof of Scavia's Lemma 6.3, applied directly
to arbitrary module complexes. All differential and grading identities follow from the
given complex; no splitting or vanishing of its homology is required.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

variable {R : Type*} [CommRing R] (X : ShortComplex (ModuleCat R))

/-- The three chain degrees, regarded as a single module. -/
abbrev ChainTotal := X.X₁ × X.X₂ × X.X₃

/-- The original boundary on the total module. -/
def chainDifferential : Module.End R (ChainTotal X) where
  toFun v := (0, X.f.hom v.1, X.g.hom v.2.1)
  map_add' v w := by simp
  map_smul' a v := by simp

/-- The sign of the chain degree. -/
def chainSign : Module.End R (ChainTotal X) where
  toFun v := (v.1, -v.2.1, v.2.2)
  map_add' v w := by simp [add_comm]
  map_smul' a v := by simp

/-- Projection onto the first and third chain degrees. -/
def chainEven : Module.End R (ChainTotal X) where
  toFun v := (v.1, 0, v.2.2)
  map_add' v w := by simp
  map_smul' a v := by simp

theorem chainDifferential_sq (v : ChainTotal X) :
    chainDifferential X (chainDifferential X v) = 0 := by
  have hz : X.g.hom (X.f.hom v.1) = 0 := by
    have h := congrArg (fun u : X.X₁ ⟶ X.X₃ => u.hom v.1) X.zero
    exact h
  simp [chainDifferential, hz]

theorem chainSign_sq (v : ChainTotal X) : chainSign X (chainSign X v) = v := by
  simp [chainSign]

theorem chainSign_anticommutes (v : ChainTotal X) :
    chainSign X (chainDifferential X v) = -chainDifferential X (chainSign X v) := by
  simp [chainSign, chainDifferential]

theorem chainEven_grading (v : ChainTotal X) :
    chainDifferential X (chainEven X v) + chainEven X (chainDifferential X v) =
      chainDifferential X v := by
  simp [chainDifferential, chainEven]

/-- A free dual-number module on the underlying total module. -/
abbrev ChainDetector := ChainTotal X × ChainTotal X

/-- Multiplication by the square-zero dual-number parameter. -/
def detectorDifferential : Module.End R (ChainDetector X) where
  toFun p := (0, p.1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Inclusion of the kernel of the extension projection, with the grading sign. -/
def detectorInclusion : ChainTotal X →ₗ[R] ChainDetector X where
  toFun v := (-chainDifferential X (chainSign X v), chainSign X v)
  map_add' v w := by simp [add_comm]
  map_smul' a v := by simp

/-- Evaluation of the dual-number parameter at the chain differential. -/
def detectorProjection : ChainDetector X →ₗ[R] ChainTotal X where
  toFun p := p.1 + chainDifferential X p.2
  map_add' p q := by simp [add_add_add_comm]
  map_smul' a p := by simp [smul_add]

/-- The grading supplies an equivariant lift of the differential through the extension. -/
def detectorLift : ChainTotal X →ₗ[R] ChainDetector X where
  toFun v := (chainEven X (chainDifferential X v), chainEven X v)
  map_add' v w := by simp
  map_smul' a v := by simp

/-- Projecting the canonical lift recovers the original boundary. -/
theorem detectorProjection_lift (v : ChainTotal X) :
    detectorProjection X (detectorLift X v) = chainDifferential X v := by
  change chainEven X (chainDifferential X v) + chainDifferential X (chainEven X v) = _
  rw [add_comm, chainEven_grading]

/-- The canonical sequence is exact over every commutative coefficient ring. -/
theorem detector_exact :
    Function.Injective (detectorInclusion X) ∧
      LinearMap.range (detectorInclusion X) = LinearMap.ker (detectorProjection X) ∧
      Function.Surjective (detectorProjection X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w h
    have hs : chainSign X v = chainSign X w := congrArg Prod.snd h
    have := congrArg (chainSign X) hs
    simpa only [chainSign_sq] using this
  · ext p
    constructor
    · rintro ⟨v, rfl⟩
      change -chainDifferential X (chainSign X v) + chainDifferential X (chainSign X v) = 0
      exact neg_add_cancel _
    · intro hp
      have hv : p.1 + chainDifferential X p.2 = 0 := hp
      refine ⟨chainSign X p.2, ?_⟩
      apply Prod.ext
      · change -chainDifferential X (chainSign X (chainSign X p.2)) = p.1
        rw [chainSign_sq]
        exact (eq_neg_of_add_eq_zero_left hv).symm
      · exact chainSign_sq X p.2
  · intro v
    exact ⟨(v, 0), by simp [detectorProjection]⟩

theorem detectorInclusion_intertwines (v : ChainTotal X) :
    detectorDifferential X (detectorInclusion X v) =
      detectorInclusion X (chainDifferential X v) := by
  apply Prod.ext
  · change 0 = -chainDifferential X (chainSign X (chainDifferential X v))
    rw [chainSign_anticommutes, map_neg, chainDifferential_sq, neg_zero, neg_zero]
  · exact (chainSign_anticommutes X v).symm

theorem detectorProjection_intertwines (p : ChainDetector X) :
    detectorProjection X (detectorDifferential X p) =
      chainDifferential X (detectorProjection X p) := by
  change 0 + chainDifferential X p.1 = chainDifferential X (p.1 + chainDifferential X p.2)
  rw [map_add, chainDifferential_sq, zero_add, add_zero]

theorem detectorLift_intertwines (v : ChainTotal X) :
    detectorDifferential X (detectorLift X v) =
      detectorLift X (chainDifferential X v) := by
  apply Prod.ext
  · change 0 = chainEven X (chainDifferential X (chainDifferential X v))
    rw [chainDifferential_sq, map_zero]
  · rfl

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.detector_exact
#print axioms GaloisForLFunctions.RepresentationLifting.detectorProjection_lift
#print axioms GaloisForLFunctions.RepresentationLifting.detectorLift_intertwines
