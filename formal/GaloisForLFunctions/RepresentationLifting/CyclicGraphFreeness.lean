import GaloisForLFunctions.RepresentationLifting.CyclicRegularCoordinates
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Explicit regular-module conjugacies on cyclic graphs

For an additive character `χ : G → (k,+)`, weight the regular basis vector `g`
by `χ(g)`. The resulting operator satisfies `E g = g E + χ(g) g`.
On the doubled norm module, `F = 1 + dE` intertwines regular translation with
`g(1 + χ(g)d)`. Inversion in the group gives `∑ χ(g) = 0` away from
characteristic two; the rank-one norm identity then gives `(dE)^4 = 0`.
Thus `F` is an explicit equivalence with two regular representations.

For every odd prime, this proves finite-slope freeness in Scavia's Lemma 6.2.
The graph theorem also applies to every finite cyclic group and every coefficient
field of characteristic other than two.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u
section Ring
variable (k G : Type u) [CommRing k] [CommGroup G] [Fintype G]


omit [Fintype G] in
/-- The commutator of character weights with translation is scalar translation. -/
theorem cyclicWeight_regular (χ : G →* Multiplicative k) (g : G) :
    cyclicWeight k G (fun x => (χ x).toAdd) * (Rep.leftRegular k G).ρ g =
      (Rep.leftRegular k G).ρ g * cyclicWeight k G (fun x => (χ x).toAdd) +
        (χ g).toAdd • (Rep.leftRegular k G).ρ g := by
  apply (MonoidAlgebra.basis G k).ext
  intro x
  change cyclicWeight k G (fun x => (χ x).toAdd)
      (Representation.leftRegular k G g (MonoidAlgebra.single x 1)) =
    Representation.leftRegular k G g
      (cyclicWeight k G (fun x => (χ x).toAdd) (MonoidAlgebra.single x 1)) +
        (χ g).toAdd • Representation.leftRegular k G g (MonoidAlgebra.single x 1)
  rw [Representation.ofMulAction_single]
  change cyclicWeight k G (fun x => (χ x).toAdd) (MonoidAlgebra.single (g * x) 1) = _
  rw [cyclicWeight_single, cyclicWeight_single,
    map_smul (Representation.leftRegular k G g), Representation.ofMulAction_single]
  change (χ (g * x)).toAdd • MonoidAlgebra.single (g * x) 1 = _
  rw [map_mul]
  change ((χ g).toAdd + (χ x).toAdd) • MonoidAlgebra.single (g * x) 1 = _
  rw [add_smul, add_comm]
  rfl

/-- Group inversion negates the sum of an additive character. -/
theorem cyclicCharacter_sum_eq_neg (χ : G →* Multiplicative k) :
    (∑ g : G, (χ g).toAdd) = -(∑ g : G, (χ g).toAdd) := by
  classical
  calc
    (∑ g : G, (χ g).toAdd) = ∑ g : G, (χ g⁻¹).toAdd :=
      (Fintype.sum_bijective (fun g : G => g⁻¹)
        (Function.Involutive.bijective (fun x : G => inv_inv x))
        (fun g => (χ g⁻¹).toAdd) (fun g => (χ g).toAdd) (fun _ => rfl)).symm
    _ = -(∑ g : G, (χ g).toAdd) := by
      simp only [map_inv]
      change (∑ g : G, -(χ g).toAdd) = -(∑ g : G, (χ g).toAdd)
      rw [Finset.sum_neg_distrib]

variable [IsCyclic G]

theorem cyclicRegularNorm_delta (v : CyclicRegular k G) :
    cyclicRegularNorm k G (cyclicRegularDelta k G v) = 0 := by
  have h : cyclicRegularDelta k G v ∈ LinearMap.range (cyclicRegularDelta k G) := ⟨v, rfl⟩
  rw [cyclicRegular_delta_norm_exact] at h
  exact h

theorem cyclicRegularDelta_norm (v : CyclicRegular k G) :
    cyclicRegularDelta k G (cyclicRegularNorm k G v) = 0 := by
  have h : cyclicRegularNorm k G v ∈ LinearMap.range (cyclicRegularNorm k G) := ⟨v, rfl⟩
  rw [cyclicRegular_norm_delta_exact] at h
  exact h

omit [Fintype G] in
/-- The commutator with the generator difference is its character weight times translation. -/
theorem cyclicWeight_delta (χ : G →* Multiplicative k) (v : CyclicRegular k G) :
    cyclicWeight k G (fun x => (χ x).toAdd) (cyclicRegularDelta k G v) =
      cyclicRegularDelta k G (cyclicWeight k G (fun x => (χ x).toAdd) v) +
        (χ (cyclicRegularGenerator G)).toAdd •
          (Rep.leftRegular k G).ρ (cyclicRegularGenerator G) v := by
  have h := LinearMap.congr_fun (cyclicWeight_regular k G χ (cyclicRegularGenerator G)) v
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  change cyclicWeight k G (fun x => (χ x).toAdd)
      ((Rep.leftRegular k G).ρ (cyclicRegularGenerator G) v - v) =
    ((Rep.leftRegular k G).ρ (cyclicRegularGenerator G)
      (cyclicWeight k G (fun x => (χ x).toAdd) v) -
        cyclicWeight k G (fun x => (χ x).toAdd) v) + _
  rw [map_sub, h]
  abel

/-- The weighted norm-difference composite is a scalar multiple of the norm. -/
theorem cyclicNorm_weight_delta (χ : G →* Multiplicative k) (v : CyclicRegular k G) :
    cyclicRegularNorm k G (cyclicWeight k G (fun x => (χ x).toAdd) (cyclicRegularDelta k G v)) =
      (χ (cyclicRegularGenerator G)).toAdd • cyclicRegularNorm k G v := by
  rw [cyclicWeight_delta, map_add, cyclicRegularNorm_delta, zero_add, map_smul]
  congr 1
  exact Representation.norm_self_apply _ _ _

/-- Reversing norm and difference changes the sign of the character weight. -/
theorem cyclicDelta_weight_norm (χ : G →* Multiplicative k) (v : CyclicRegular k G) :
    cyclicRegularDelta k G (cyclicWeight k G (fun x => (χ x).toAdd) (cyclicRegularNorm k G v)) =
      -(χ (cyclicRegularGenerator G)).toAdd • cyclicRegularNorm k G v := by
  have h := cyclicWeight_delta k G χ (cyclicRegularNorm k G v)
  rw [cyclicRegularDelta_norm, map_zero] at h
  have hfix : (Rep.leftRegular k G).ρ (cyclicRegularGenerator G) (cyclicRegularNorm k G v) =
      cyclicRegularNorm k G v := Representation.self_norm_apply _ _ _
  rw [hfix] at h
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The character weight operator on both regular summands. -/
def cyclicWeightPair (χ : G →* Multiplicative k) : Module.End k (CyclicDetector k G) :=
  (cyclicWeight k G (fun x => (χ x).toAdd)).prodMap
    (cyclicWeight k G (fun x => (χ x).toAdd))

/-- The square of the weighted differential is diagonal, with opposite norm-weight blocks. -/
theorem cyclicWeightedDifferential_sq (χ : G →* Multiplicative k) (v : CyclicDetector k G) :
    (cyclicDifferential k G * cyclicWeightPair k G χ)
        ((cyclicDifferential k G * cyclicWeightPair k G χ) v) =
      ((χ (cyclicRegularGenerator G)).toAdd •
        cyclicRegularNorm k G (cyclicWeight k G (fun x => (χ x).toAdd) v.1),
       -(χ (cyclicRegularGenerator G)).toAdd •
        cyclicRegularNorm k G (cyclicWeight k G (fun x => (χ x).toAdd) v.2)) := by
  apply Prod.ext
  · exact cyclicNorm_weight_delta k G χ _
  · exact cyclicDelta_weight_norm k G χ _

/-- A zero sum of character weights makes the weighted differential fourth-power nilpotent. -/
theorem cyclicWeightedDifferential_pow_four (χ : G →* Multiplicative k)
    (hχ : (∑ g : G, (χ g).toAdd) = 0) :
    (cyclicDifferential k G * cyclicWeightPair k G χ) ^ 4 = 0 := by
  have hNN : ∀ v : CyclicRegular k G,
      cyclicRegularNorm k G (cyclicWeight k G (fun x => (χ x).toAdd) (cyclicRegularNorm k G v)) = 0 := by
    intro v
    have h := cyclicRegularNorm_weight_norm k G (fun x => (χ x).toAdd)
    rw [hχ, zero_smul] at h
    exact LinearMap.congr_fun h v
  apply LinearMap.ext
  intro v
  change (cyclicDifferential k G * cyclicWeightPair k G χ)
    ((cyclicDifferential k G * cyclicWeightPair k G χ)
      ((cyclicDifferential k G * cyclicWeightPair k G χ)
        ((cyclicDifferential k G * cyclicWeightPair k G χ) v))) = 0
  rw [cyclicWeightedDifferential_sq, cyclicWeightedDifferential_sq]
  simp only [map_smul, hNN, smul_zero, Prod.mk_zero_zero]

/-- The embedding of the graph of an additive character into the product group. -/
def cyclicGraphHom (χ : G →* Multiplicative k) : G →* G × Multiplicative k where
  toFun g := (g, χ g)
  map_one' := by simp
  map_mul' g h := by simp

omit [Fintype G] [IsCyclic G] in
/-- Character weights have the same translation commutator on the doubled module. -/
theorem cyclicWeightPair_regular (χ : G →* Multiplicative k) (g : G) (v : CyclicDetector k G) :
    cyclicWeightPair k G χ (cyclicRegularPairRepresentation k G g v) =
      cyclicRegularPairRepresentation k G g (cyclicWeightPair k G χ v) +
        (χ g).toAdd • cyclicRegularPairRepresentation k G g v := by
  have h (x : CyclicRegular k G) := LinearMap.congr_fun (cyclicWeight_regular k G χ g) x
  apply Prod.ext
  · exact h v.1
  · exact h v.2

/-- The explicit change of basis from the regular pair to its graph restriction. -/
def cyclicGraphConjugator (χ : G →* Multiplicative k) : Module.End k (CyclicDetector k G) :=
  1 + cyclicDifferential k G * cyclicWeightPair k G χ

/-- The weighted change of basis intertwines the two actions over every coefficient ring. -/
theorem cyclicGraphConjugator_intertwines (χ : G →* Multiplicative k) (g : G) (v : CyclicDetector k G) :
    cyclicGraphConjugator k G χ (cyclicRegularPairRepresentation k G g v) =
      cyclicProductRepresentation k G (cyclicGraphHom k G χ g) (cyclicGraphConjugator k G χ v) := by
  change cyclicRegularPairRepresentation k G g v +
      cyclicDifferential k G (cyclicWeightPair k G χ (cyclicRegularPairRepresentation k G g v)) =
    cyclicRegularPairRepresentation k G g
      ((v + cyclicDifferential k G (cyclicWeightPair k G χ v)) +
        (χ g).toAdd • cyclicDifferential k G (v + cyclicDifferential k G (cyclicWeightPair k G χ v)))
  simp only [cyclicWeightPair_regular, map_add, map_smul, cyclicDifferential_equivariant,
    cyclicDifferential_sq, add_zero]
  abel

/-- Nilpotence makes the graph intertwiner invertible when the character weights sum to zero. -/
theorem cyclicGraphConjugator_bijective (χ : G →* Multiplicative k)
    (hχ : (∑ g : G, (χ g).toAdd) = 0) : Function.Bijective (cyclicGraphConjugator k G χ) := by
  apply (Module.End.isUnit_iff _).mp
  exact IsNilpotent.isUnit_one_add ⟨4, cyclicWeightedDifferential_pow_four k G χ hχ⟩

/-- Multiplication by the slope, viewed as an additive-group character. -/
def cyclicSlopeCharacter (a : k) : Multiplicative k →* Multiplicative k where
  toFun g := Multiplicative.ofAdd (a * g.toAdd)
  map_one' := by
    change Multiplicative.ofAdd (a * 0) = Multiplicative.ofAdd 0
    rw [mul_zero]
  map_mul' g h := by
    change Multiplicative.ofAdd (a * (g.toAdd + h.toAdd)) =
      Multiplicative.ofAdd (a * g.toAdd + a * h.toAdd)
    rw [mul_add]

end Ring

section Field
variable (k G : Type u) [Field k] [CommGroup G] [Fintype G]

/-- An additive character on a finite group sums to zero away from characteristic two. -/
theorem cyclicCharacter_sum_zero (h2 : (2 : k) ≠ 0) (χ : G →* Multiplicative k) :
    (∑ g : G, (χ g).toAdd) = 0 := by
  have h : (2 : k) * (∑ g : G, (χ g).toAdd) = 0 := by
    rw [two_mul]
    calc
      _ = (∑ g : G, (χ g).toAdd) + -(∑ g : G, (χ g).toAdd) :=
        congrArg ((∑ g : G, (χ g).toAdd) + ·) (cyclicCharacter_sum_eq_neg k G χ)
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp h).resolve_left h2

variable [IsCyclic G]

/-- Every additive graph restriction is equivalent to two regular representations. -/
def cyclicGraphEquiv (h2 : (2 : k) ≠ 0) (χ : G →* Multiplicative k) :
    (cyclicRegularPairRepresentation k G).Equiv
      (Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G))).ρ :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (cyclicGraphConjugator k G χ)
      (cyclicGraphConjugator_bijective k G χ (cyclicCharacter_sum_zero k G h2 χ)))
    (fun g => by
      apply LinearMap.ext
      intro v
      exact cyclicGraphConjugator_intertwines k G χ g v)

/-- The graph equivalence as an isomorphism in the category of representations. -/
def cyclicGraphIso (h2 : (2 : k) ≠ 0) (χ : G →* Multiplicative k) :
    Rep.of (cyclicRegularPairRepresentation k G) ≅
      Rep.res (cyclicGraphHom k G χ) (Rep.of (cyclicProductRepresentation k G)) :=
  Rep.mkIso (cyclicGraphEquiv k G h2 χ)

end Field

/-- Two is nonzero in every odd prime field. -/
theorem primeField_two_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  apply hp
  apply (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
  exact (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h

/-- Every finite-slope restriction of the odd-prime plane module is a regular pair. -/
def primePlaneSlopeIso (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) :
    Rep.of (cyclicRegularPairRepresentation (ZMod p) (Multiplicative (ZMod p))) ≅
      Rep.res (cyclicGraphHom (ZMod p) (Multiplicative (ZMod p)) (cyclicSlopeCharacter (ZMod p) a))
        (Rep.of (primePlaneRepresentation p)) :=
  cyclicGraphIso (ZMod p) (Multiplicative (ZMod p)) (primeField_two_ne_zero p hp)
    (cyclicSlopeCharacter (ZMod p) a)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.primePlaneSlopeIso

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicWeightedDifferential_pow_four
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicGraphEquiv
