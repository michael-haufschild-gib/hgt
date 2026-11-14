import GaloisForLFunctions.RepresentationLifting.CyclicNormDifferential
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Field.ZMod

/-!
# Commuting cyclic and unipotent actions

The cyclic norm-difference differential commutes with the regular group action.
Its square-zero identity makes `a ↦ 1 + ad` a representation of the additive
coefficient group. Combining the two actions gives a representation of `G × (k,+)`.

For `G = C_p` and `k = F_p`, these are the two actions in Scavia's Lemma 6.2.
In characteristic two every representation endomorphism is traceless, since
equivariance forces it to commute with the acyclic differential.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

section Ring

variable (k G : Type u) [CommRing k] [CommGroup G] [Fintype G] [IsCyclic G]

/-- Two copies of the regular representation. -/
abbrev cyclicRegularPairRepresentation : Representation k G (CyclicDetector k G) :=
  (Rep.leftRegular k G).ρ.prod (Rep.leftRegular k G).ρ

theorem cyclicDifferential_equivariant (g : G) (v : CyclicDetector k G) :
    cyclicDifferential k G (cyclicRegularPairRepresentation k G g v) =
      cyclicRegularPairRepresentation k G g (cyclicDifferential k G v) := by
  apply Prod.ext
  · exact Rep.hom_comm_apply (Rep.leftRegular k G).norm g v.2
  · exact Rep.hom_comm_apply
      (Rep.applyAsHom (Rep.leftRegular k G) (cyclicRegularGenerator G) - 𝟙 _) g v.1

/-- The unipotent action supplied by the norm-difference differential. -/
def cyclicUnipotent (a : k) : Module.End k (CyclicDetector k G) :=
  1 + a • cyclicDifferential k G

@[simp] theorem cyclicUnipotent_apply (a : k) (v : CyclicDetector k G) :
    cyclicUnipotent k G a v = v + a • cyclicDifferential k G v := rfl

theorem cyclicUnipotent_add (a b : k) :
    cyclicUnipotent k G (a + b) = cyclicUnipotent k G a * cyclicUnipotent k G b := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, cyclicUnipotent_apply, map_add, map_smul,
    cyclicDifferential_sq, smul_zero, add_zero, add_smul]
  abel

/-- Addition of coefficients becomes composition of unipotent operators. -/
def cyclicUnipotentRepresentation : Representation k (Multiplicative k) (CyclicDetector k G) where
  toFun a := cyclicUnipotent k G a.toAdd
  map_one' := by
    apply LinearMap.ext
    intro v
    simp
  map_mul' a b := cyclicUnipotent_add k G a.toAdd b.toAdd

theorem cyclicRegular_unipotent_commute (g : G) (a : Multiplicative k) :
    cyclicRegularPairRepresentation k G g * cyclicUnipotentRepresentation k G a =
      cyclicUnipotentRepresentation k G a * cyclicRegularPairRepresentation k G g := by
  apply LinearMap.ext
  intro v
  change cyclicRegularPairRepresentation k G g (v + a.toAdd • cyclicDifferential k G v) =
    cyclicRegularPairRepresentation k G g v +
      a.toAdd • cyclicDifferential k G (cyclicRegularPairRepresentation k G g v)
  rw [map_add, map_smul, cyclicDifferential_equivariant]

/-- The product of the commuting cyclic and additive unipotent actions. -/
def cyclicProductRepresentation : Representation k (G × Multiplicative k) (CyclicDetector k G) where
  toFun p := cyclicRegularPairRepresentation k G p.1 * cyclicUnipotentRepresentation k G p.2
  map_one' := by simp
  map_mul' p q := by
    change cyclicRegularPairRepresentation k G (p.1 * q.1) *
      cyclicUnipotentRepresentation k G (p.2 * q.2) = _
    rw [map_mul, map_mul]
    calc
      _ = cyclicRegularPairRepresentation k G p.1 *
          (cyclicRegularPairRepresentation k G q.1 * cyclicUnipotentRepresentation k G p.2) *
          cyclicUnipotentRepresentation k G q.2 := by simp only [mul_assoc]
      _ = cyclicRegularPairRepresentation k G p.1 *
          (cyclicUnipotentRepresentation k G p.2 * cyclicRegularPairRepresentation k G q.1) *
          cyclicUnipotentRepresentation k G q.2 := by rw [cyclicRegular_unipotent_commute]
      _ = _ := by simp only [mul_assoc]

@[simp] theorem cyclicProductRepresentation_unipotent (a : k) (v : CyclicDetector k G) :
    cyclicProductRepresentation k G (1, Multiplicative.ofAdd a) v =
      v + a • cyclicDifferential k G v := by
  change (cyclicRegularPairRepresentation k G 1 * cyclicUnipotentRepresentation k G (.ofAdd a)) v = _
  rw [map_one, one_mul]
  rfl

end Ring

section Field

variable (k G : Type u) [Field k] [CommGroup G] [Fintype G] [IsCyclic G]

omit [IsCyclic G] in
/-- The underlying dimension is twice the cyclic group order. -/
theorem cyclicDetector_finrank :
    Module.finrank k (CyclicDetector k G) = 2 * Fintype.card G := by
  change Module.finrank k (MonoidAlgebra k G × MonoidAlgebra k G) = _
  simp only [Module.finrank_prod, Module.finrank_eq_card_basis (MonoidAlgebra.basis G k), two_mul]

variable [CharP k 2]

/-- Equivariance alone makes every endomorphism traceless in characteristic two. -/
theorem cyclicProductRepresentation_endomorphism_trace
    (T : Rep.of (cyclicProductRepresentation k G) ⟶ Rep.of (cyclicProductRepresentation k G)) :
    LinearMap.trace k (CyclicDetector k G) T.hom.toLinearMap = 0 := by
  apply cyclicDifferential_trace_zero k G
  apply LinearMap.ext
  intro v
  change T.hom (cyclicDifferential k G v) = cyclicDifferential k G (T.hom v)
  have h := Rep.hom_comm_apply T (1, Multiplicative.ofAdd (1 : k)) v
  change T.hom (cyclicProductRepresentation k G (1, Multiplicative.ofAdd (1 : k)) v) =
    cyclicProductRepresentation k G (1, Multiplicative.ofAdd (1 : k)) (T.hom v) at h
  simpa only [cyclicProductRepresentation_unipotent, one_smul, map_add, add_right_inj] using h

end Field

/-- The `2p`-dimensional representation of `C_p × C_p` supplied by the norm-difference operator. -/
def primePlaneRepresentation (p : ℕ) [Fact p.Prime] :
    Representation (ZMod p) (Multiplicative (ZMod p) × Multiplicative (ZMod p))
      (CyclicDetector (ZMod p) (Multiplicative (ZMod p))) :=
  cyclicProductRepresentation (ZMod p) (Multiplicative (ZMod p))

/-- The prime-plane construction has dimension `2p` over `F_p`. -/
theorem primePlaneRepresentation_finrank (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod p) (Rep.of (primePlaneRepresentation p)) = 2 * p := by
  change Module.finrank (ZMod p) (CyclicDetector (ZMod p) (Multiplicative (ZMod p))) = _
  simpa only [Fintype.card_multiplicative, ZMod.card] using
    cyclicDetector_finrank (ZMod p) (Multiplicative (ZMod p))

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicProductRepresentation
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicProductRepresentation_endomorphism_trace
#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneRepresentation_finrank
