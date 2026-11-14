import GaloisForLFunctions.RepresentationLifting.CyclicProductRepresentation

/-!
# Coordinates of the cyclic norm and weighted regular operators

The regular norm is the rank-one map sending a vector to its augmentation times
sum of the regular basis. A diagonal weight operator `E` therefore satisfies
`NEN = (∑ g, w g) N`. These identities determine the trace on the distinguished
line of the doubled cyclic norm module and control its weighted conjugacies.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.RepresentationLifting
universe u
variable (k G : Type u) [CommRing k] [CommGroup G] [Fintype G]

/-- Sum of the coefficients in the regular basis. -/
def cyclicAugmentation : CyclicRegular k G →ₗ[k] k where
  toFun v := ∑ g : G, v.coeff g
  map_add' v w := by
    change (∑ g, ((v : MonoidAlgebra k G) + w).coeff g) = _
    rw [MonoidAlgebra.coeff_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  map_smul' a v := by
    change (∑ g, (a • (v : MonoidAlgebra k G)).coeff g) = _
    rw [MonoidAlgebra.coeff_smul]
    simp only [Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

/-- The invariant vector with every regular coefficient equal to one. -/
def cyclicNormVector : CyclicRegular k G := ∑ g : G, MonoidAlgebra.single g (1 : k)

theorem cyclicAugmentation_single (g : G) (a : k) :
    cyclicAugmentation k G (MonoidAlgebra.single g a) = a := by
  classical
  simp [cyclicAugmentation, MonoidAlgebra.coeff_single]

theorem cyclicNormVector_coeff (g : G) : (cyclicNormVector k G).coeff g = 1 := by
  classical
  change (∑ g : G, MonoidAlgebra.single g (1 : k)).coeff g = 1
  rw [MonoidAlgebra.coeff_sum]
  simp [MonoidAlgebra.coeff_single]

/-- The norm factors through augmentation and the invariant norm vector. -/
theorem cyclicRegularNorm_eq_smul (v : CyclicRegular k G) :
    cyclicRegularNorm k G v = cyclicAugmentation k G v • cyclicNormVector k G := by
  classical
  have h : cyclicRegularNorm k G = (cyclicAugmentation k G).smulRight (cyclicNormVector k G) := by
    apply (MonoidAlgebra.basis G k).ext
    intro x
    rw [MonoidAlgebra.basis_apply, LinearMap.smulRight_apply, cyclicAugmentation_single, one_smul]
    change (Representation.leftRegular k G).norm (MonoidAlgebra.single x 1) = _
    simp only [Representation.norm, LinearMap.sum_apply, Representation.ofMulAction_single]
    exact Fintype.sum_bijective (fun g : G => g * x) (Group.mulRight_bijective x)
      (fun g => MonoidAlgebra.single (g * x) (1 : k)) (fun g => MonoidAlgebra.single g (1 : k))
      (fun _ => rfl)
  exact LinearMap.congr_fun h v

/-- A diagonal operator in the regular basis, with prescribed weights. -/
def cyclicWeight (w : G → k) : Module.End k (CyclicRegular k G) :=
  (MonoidAlgebra.basis G k).constr k (fun g => w g • (MonoidAlgebra.basis G k) g)

omit [Fintype G] in
theorem cyclicWeight_single (w : G → k) (g : G) :
    cyclicWeight k G w (MonoidAlgebra.single g 1) = w g • MonoidAlgebra.single g 1 := by
  change ((MonoidAlgebra.basis G k).constr k (fun x => w x • (MonoidAlgebra.basis G k) x))
    ((MonoidAlgebra.basis G k) g) = _
  rw [Module.Basis.constr_basis]
  rfl

theorem cyclicWeight_normVector (w : G → k) :
    cyclicWeight k G w (cyclicNormVector k G) =
      ∑ g : G, w g • MonoidAlgebra.single g 1 := by
  simp only [cyclicNormVector, map_sum, cyclicWeight_single]

theorem cyclicAugmentation_weight_normVector (w : G → k) :
    cyclicAugmentation k G (cyclicWeight k G w (cyclicNormVector k G)) = ∑ g : G, w g := by
  rw [cyclicWeight_normVector, map_sum]
  simp only [map_smul, cyclicAugmentation_single, smul_eq_mul, mul_one]

/-- Sandwiching a diagonal weight by norms retains only the sum of its weights. -/
theorem cyclicRegularNorm_weight_norm (w : G → k) :
    cyclicRegularNorm k G * cyclicWeight k G w * cyclicRegularNorm k G =
      (∑ g : G, w g) • cyclicRegularNorm k G := by
  apply LinearMap.ext
  intro v
  change cyclicRegularNorm k G (cyclicWeight k G w (cyclicRegularNorm k G v)) =
    (∑ g : G, w g) • cyclicRegularNorm k G v
  rw [cyclicRegularNorm_eq_smul k G v, map_smul, map_smul, cyclicRegularNorm_eq_smul,
    cyclicAugmentation_weight_normVector]
  exact smul_comm _ _ _

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicRegularNorm_eq_smul
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicRegularNorm_weight_norm
