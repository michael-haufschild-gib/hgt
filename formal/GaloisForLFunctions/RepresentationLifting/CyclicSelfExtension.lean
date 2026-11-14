import GaloisForLFunctions.RepresentationLifting.CyclicProductRepresentation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# The equivariant self-extension of the cyclic norm module

Let `d(x,y) = (Ny,Δx)`, `S(x,y) = (x,-y)`, and `h(x,y) = (x,0)` on two
copies of the regular module. On its double, the additive coefficient group acts
by `(x,y) ↦ (x,y+ax)`. The maps
`i(v) = (-dSv,Sv)`, `π(x,y) = x+dy`, and `Φ(v) = (hdv,hv)` are equivariant,
form a short exact self-extension, and satisfy `πΦ = d`.

This is the construction of Scavia's Lemma 6.3, over every commutative coefficient
ring and every finite cyclic group. Specializing to `F_p` gives a `4p`-dimensional
extension of the `2p`-dimensional representation of `C_p × C_p`.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

variable (k G : Type u) [CommRing k] [CommGroup G] [Fintype G] [IsCyclic G]

/-- The grading sign on the two copies of the regular module. -/
def cyclicSign : Module.End k (CyclicDetector k G) where
  toFun v := (v.1, -v.2)
  map_add' _ _ := by simp [add_comm]
  map_smul' _ _ := by simp

omit [Fintype G] [IsCyclic G] in
theorem cyclicSign_sq (v : CyclicDetector k G) : cyclicSign k G (cyclicSign k G v) = v := by
  simp [cyclicSign]

theorem cyclicSign_anticommutes (v : CyclicDetector k G) :
    cyclicSign k G (cyclicDifferential k G v) = -cyclicDifferential k G (cyclicSign k G v) := by
  simp [cyclicSign, cyclicDifferential]

omit [Fintype G] [IsCyclic G] in
theorem cyclicSign_equivariant (g : G) (v : CyclicDetector k G) :
    cyclicSign k G (cyclicRegularPairRepresentation k G g v) =
      cyclicRegularPairRepresentation k G g (cyclicSign k G v) := by
  apply Prod.ext
  · rfl
  · change -((Rep.leftRegular k G).ρ g v.2) = (Rep.leftRegular k G).ρ g (-v.2)
    rw [map_neg]

omit [Fintype G] [IsCyclic G] in
theorem cyclicEven_equivariant (g : G) (v : CyclicDetector k G) :
    cyclicEven k G (cyclicRegularPairRepresentation k G g v) =
      cyclicRegularPairRepresentation k G g (cyclicEven k G v) := by
  apply Prod.ext
  · rfl
  · exact (map_zero ((Rep.leftRegular k G).ρ g)).symm

/-- The module and its copy multiplied by the square-zero extension parameter. -/
abbrev CyclicExtensionSpace := CyclicDetector k G × CyclicDetector k G

/-- Simultaneous regular translation and a scalar multiple of the square-zero shift. -/
def cyclicExtensionAction (g : G) (a : k) : Module.End k (CyclicExtensionSpace k G) :=
  ((cyclicRegularPairRepresentation k G g).comp (LinearMap.fst k _ _)).prod
    ((cyclicRegularPairRepresentation k G g).comp
      (LinearMap.snd k _ _ + a • LinearMap.fst k _ _))

/-- The regular and square-zero shift actions form a representation of the product group. -/
def cyclicExtensionRepresentation :
    Representation k (G × Multiplicative k) (CyclicExtensionSpace k G) where
  toFun q := cyclicExtensionAction k G q.1 q.2.toAdd
  map_one' := by
    apply LinearMap.ext
    intro p
    change (cyclicRegularPairRepresentation k G 1 p.1,
      cyclicRegularPairRepresentation k G 1 (p.2 + (0 : k) • p.1)) = p
    simp only [map_one, Module.End.one_apply, zero_smul, add_zero]
  map_mul' q r := by
    apply LinearMap.ext
    intro p
    change (cyclicRegularPairRepresentation k G (q.1 * r.1) p.1,
      cyclicRegularPairRepresentation k G (q.1 * r.1) (p.2 + (q.2.toAdd + r.2.toAdd) • p.1)) =
      (cyclicRegularPairRepresentation k G q.1 (cyclicRegularPairRepresentation k G r.1 p.1),
        cyclicRegularPairRepresentation k G q.1
          (cyclicRegularPairRepresentation k G r.1 (p.2 + r.2.toAdd • p.1) +
            q.2.toAdd • cyclicRegularPairRepresentation k G r.1 p.1))
    apply Prod.ext
    · rw [map_mul]; rfl
    · simp only [map_mul, Module.End.mul_apply, map_add, map_smul, add_smul]
      abel

/-- The second group factor acts by the standard square-zero shift. -/
@[simp] theorem cyclicExtensionRepresentation_unipotent (a : k) (p : CyclicExtensionSpace k G) :
    cyclicExtensionRepresentation k G (1, Multiplicative.ofAdd a) p = (p.1, p.2 + a • p.1) := by
  change (cyclicRegularPairRepresentation k G 1 p.1,
    cyclicRegularPairRepresentation k G 1 (p.2 + a • p.1)) = _
  rw [map_one]
  rfl

/-- The grading sign identifies the kernel of the extension projection. -/
def cyclicExtensionInclusion : CyclicDetector k G →ₗ[k] CyclicExtensionSpace k G where
  toFun v := (-cyclicDifferential k G (cyclicSign k G v), cyclicSign k G v)
  map_add' _ _ := by simp [add_comm]
  map_smul' _ _ := by simp

/-- Evaluation of the extension parameter at the cyclic differential. -/
def cyclicExtensionProjection : CyclicExtensionSpace k G →ₗ[k] CyclicDetector k G where
  toFun p := p.1 + cyclicDifferential k G p.2
  map_add' _ _ := by simp [add_add_add_comm]
  map_smul' _ _ := by simp [smul_add]

/-- The even projection supplies a lift of the differential through the extension. -/
def cyclicExtensionLift : CyclicDetector k G →ₗ[k] CyclicExtensionSpace k G where
  toFun v := (cyclicEven k G (cyclicDifferential k G v), cyclicEven k G v)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem cyclicExtensionProjection_lift (v : CyclicDetector k G) :
    cyclicExtensionProjection k G (cyclicExtensionLift k G v) = cyclicDifferential k G v := by
  change cyclicEven k G (cyclicDifferential k G v) +
    cyclicDifferential k G (cyclicEven k G v) = _
  rw [add_comm, cyclicEven_grading]

theorem cyclicExtensionInclusion_d (v : CyclicDetector k G) :
    cyclicExtensionInclusion k G (cyclicDifferential k G v) =
      (0, (cyclicExtensionInclusion k G v).1) := by
  apply Prod.ext
  · change -cyclicDifferential k G (cyclicSign k G (cyclicDifferential k G v)) = 0
    rw [cyclicSign_anticommutes, map_neg, cyclicDifferential_sq, neg_zero, neg_zero]
  · exact cyclicSign_anticommutes k G v

theorem cyclicExtensionLift_d (v : CyclicDetector k G) :
    cyclicExtensionLift k G (cyclicDifferential k G v) =
      (0, (cyclicExtensionLift k G v).1) := by
  apply Prod.ext
  · change cyclicEven k G (cyclicDifferential k G (cyclicDifferential k G v)) = 0
    rw [cyclicDifferential_sq, map_zero]
  · rfl

theorem cyclicExtensionInclusion_regular (g : G) (v : CyclicDetector k G) :
    cyclicExtensionInclusion k G (cyclicRegularPairRepresentation k G g v) =
      (cyclicRegularPairRepresentation k G g (cyclicExtensionInclusion k G v).1,
        cyclicRegularPairRepresentation k G g (cyclicExtensionInclusion k G v).2) := by
  apply Prod.ext
  · change -cyclicDifferential k G (cyclicSign k G (cyclicRegularPairRepresentation k G g v)) =
      cyclicRegularPairRepresentation k G g (-cyclicDifferential k G (cyclicSign k G v))
    rw [cyclicSign_equivariant, cyclicDifferential_equivariant, map_neg]
  · exact cyclicSign_equivariant k G g v

theorem cyclicExtensionLift_regular (g : G) (v : CyclicDetector k G) :
    cyclicExtensionLift k G (cyclicRegularPairRepresentation k G g v) =
      (cyclicRegularPairRepresentation k G g (cyclicExtensionLift k G v).1,
        cyclicRegularPairRepresentation k G g (cyclicExtensionLift k G v).2) := by
  apply Prod.ext
  · change cyclicEven k G (cyclicDifferential k G (cyclicRegularPairRepresentation k G g v)) =
      cyclicRegularPairRepresentation k G g (cyclicEven k G (cyclicDifferential k G v))
    rw [cyclicDifferential_equivariant, cyclicEven_equivariant]
  · exact cyclicEven_equivariant k G g v

/-- The kernel inclusion is equivariant for both group factors. -/
def cyclicSelfExtensionInclusion :
    Rep.of (cyclicProductRepresentation k G) ⟶ Rep.of (cyclicExtensionRepresentation k G) :=
  Rep.ofHom ⟨cyclicExtensionInclusion k G, fun q => by
    apply LinearMap.ext
    intro v
    change cyclicExtensionInclusion k G
        (cyclicRegularPairRepresentation k G q.1 (v + q.2.toAdd • cyclicDifferential k G v)) =
      (cyclicRegularPairRepresentation k G q.1 (cyclicExtensionInclusion k G v).1,
        cyclicRegularPairRepresentation k G q.1
          ((cyclicExtensionInclusion k G v).2 + q.2.toAdd • (cyclicExtensionInclusion k G v).1))
    rw [cyclicExtensionInclusion_regular, map_add, map_smul, cyclicExtensionInclusion_d]
    change (cyclicRegularPairRepresentation k G q.1
        ((cyclicExtensionInclusion k G v).1 + q.2.toAdd • 0), _) = _
    rw [smul_zero, add_zero]
    rfl⟩

/-- The extension projection is equivariant for both group factors. -/
def cyclicSelfExtensionProjection :
    Rep.of (cyclicExtensionRepresentation k G) ⟶ Rep.of (cyclicProductRepresentation k G) :=
  Rep.ofHom ⟨cyclicExtensionProjection k G, fun q => by
    apply LinearMap.ext
    intro p
    change cyclicRegularPairRepresentation k G q.1 p.1 +
        cyclicDifferential k G (cyclicRegularPairRepresentation k G q.1 (p.2 + q.2.toAdd • p.1)) =
      cyclicRegularPairRepresentation k G q.1
        ((p.1 + cyclicDifferential k G p.2) +
          q.2.toAdd • cyclicDifferential k G (p.1 + cyclicDifferential k G p.2))
    simp only [cyclicDifferential_equivariant, map_add, map_smul, cyclicDifferential_sq,
      add_zero]
    abel⟩

/-- The lifted differential is equivariant for both group factors. -/
def cyclicSelfExtensionLift :
    Rep.of (cyclicProductRepresentation k G) ⟶ Rep.of (cyclicExtensionRepresentation k G) :=
  Rep.ofHom ⟨cyclicExtensionLift k G, fun q => by
    apply LinearMap.ext
    intro v
    change cyclicExtensionLift k G
        (cyclicRegularPairRepresentation k G q.1 (v + q.2.toAdd • cyclicDifferential k G v)) =
      (cyclicRegularPairRepresentation k G q.1 (cyclicExtensionLift k G v).1,
        cyclicRegularPairRepresentation k G q.1
          ((cyclicExtensionLift k G v).2 + q.2.toAdd • (cyclicExtensionLift k G v).1))
    rw [cyclicExtensionLift_regular, map_add, map_smul, cyclicExtensionLift_d]
    change (cyclicRegularPairRepresentation k G q.1
        ((cyclicExtensionLift k G v).1 + q.2.toAdd • 0), _) = _
    rw [smul_zero, add_zero]
    rfl⟩

/-- Exactness follows directly from the grading involution and the projection formula. -/
theorem cyclicExtension_exact :
    Function.Injective (cyclicExtensionInclusion k G) ∧
      LinearMap.range (cyclicExtensionInclusion k G) = LinearMap.ker (cyclicExtensionProjection k G) ∧
      Function.Surjective (cyclicExtensionProjection k G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w hvw
    have hs : cyclicSign k G v = cyclicSign k G w := congrArg Prod.snd hvw
    have h := congrArg (cyclicSign k G) hs
    simpa only [cyclicSign_sq] using h
  · ext p
    constructor
    · rintro ⟨v, rfl⟩
      change -cyclicDifferential k G (cyclicSign k G v) +
        cyclicDifferential k G (cyclicSign k G v) = 0
      exact neg_add_cancel _
    · intro hp
      have hv : p.1 + cyclicDifferential k G p.2 = 0 := hp
      refine ⟨cyclicSign k G p.2, ?_⟩
      apply Prod.ext
      · change -cyclicDifferential k G (cyclicSign k G (cyclicSign k G p.2)) = p.1
        rw [cyclicSign_sq]
        exact (eq_neg_of_add_eq_zero_left hv).symm
      · exact cyclicSign_sq k G p.2
  · intro v
    exact ⟨(v, 0), by simp [cyclicExtensionProjection]⟩

/-- The self-extension as a short complex of product-group representations. -/
def cyclicSelfExtension : ShortComplex (Rep k (G × Multiplicative k)) :=
  ShortComplex.mk (cyclicSelfExtensionInclusion k G) (cyclicSelfExtensionProjection k G) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change -cyclicDifferential k G (cyclicSign k G v) +
      cyclicDifferential k G (cyclicSign k G v) = 0
    exact neg_add_cancel _)

/-- The cyclic self-extension is short exact over every commutative coefficient ring. -/
theorem cyclicSelfExtension_shortExact : (cyclicSelfExtension k G).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (forget₂ (Rep k (G × Multiplicative k)) (ModuleCat k)).reflects_exact_of_faithful
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (cyclicExtension_exact k G).2.1
  · rw [Rep.mono_iff_injective]
    exact (cyclicExtension_exact k G).1
  · rw [Rep.epi_iff_surjective]
    exact (cyclicExtension_exact k G).2.2

/-- The cyclic differential commutes with the full product-group action. -/
def cyclicDifferentialHom :
    Rep.of (cyclicProductRepresentation k G) ⟶ Rep.of (cyclicProductRepresentation k G) :=
  Rep.ofHom ⟨cyclicDifferential k G, fun q => by
    apply LinearMap.ext
    intro v
    change cyclicDifferential k G
        (cyclicRegularPairRepresentation k G q.1 (v + q.2.toAdd • cyclicDifferential k G v)) =
      cyclicRegularPairRepresentation k G q.1
        (cyclicDifferential k G v + q.2.toAdd • cyclicDifferential k G (cyclicDifferential k G v))
    rw [cyclicDifferential_equivariant, map_add, map_smul]⟩

/-- The equivariant lift projects to the original cyclic differential. -/
theorem cyclicSelfExtension_lift_projection :
    cyclicSelfExtensionLift k G ≫ cyclicSelfExtensionProjection k G = cyclicDifferentialHom k G := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  exact cyclicExtensionProjection_lift k G v

variable {k G}

/-- The self-extension attached to the prime-plane representation. -/
abbrev primePlaneSelfExtension (p : ℕ) [Fact p.Prime] :=
  cyclicSelfExtension (ZMod p) (Multiplicative (ZMod p))

/-- The prime-plane self-extension is short exact for every prime. -/
theorem primePlaneSelfExtension_shortExact (p : ℕ) [Fact p.Prime] :
    (primePlaneSelfExtension p).ShortExact :=
  cyclicSelfExtension_shortExact (ZMod p) (Multiplicative (ZMod p))

/-- The middle representation of the prime-plane self-extension has dimension `4p`. -/
theorem primePlaneSelfExtension_finrank (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (primePlaneSelfExtension p).X₂ = 4 * p := by
  change Module.finrank (ZMod p)
    (CyclicDetector (ZMod p) (Multiplicative (ZMod p)) ×
      CyclicDetector (ZMod p) (Multiplicative (ZMod p))) = _
  rw [Module.finrank_prod, cyclicDetector_finrank]
  simp only [Fintype.card_multiplicative, ZMod.card]
  ring

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_shortExact
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtensionLift
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicSelfExtension_lift_projection
#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneSelfExtension_finrank
