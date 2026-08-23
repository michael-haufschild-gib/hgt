import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure

/-!
# Opposites of quadratic cyclic Galois algebras

A quadratic cyclic algebra admits an explicit anti-automorphism: it sends a coefficient through
the nontrivial Galois involution and fixes the cyclic generator.  This module packages that
anti-automorphism as an algebra equivalence to the opposite algebra.  Consequently, every
quadratic cyclic Brauer class is self-inverse and has exponent dividing two.

This is the degree-two inverse law needed before the full tensor-product formula for cyclic
algebras can make the cohomology-to-Brauer construction additive.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Coefficients for the quadratic cyclic anti-homomorphism, viewed as a homomorphism into the
opposite algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraOppositeCoefficient (a : K) :
    L →+* (cyclicGaloisAlgebra K L a)ᵐᵒᵖ := by
  let f : L →+* cyclicGaloisAlgebra K L a :=
    (cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a)).comp (cyclicGaloisGenerator K L).toRingHom
  apply RingHom.toOpposite f
  intro x y
  change f x * f y = f y * f x
  rw [← f.map_mul, ← f.map_mul, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The opposite-coefficient map applies the quadratic Galois involution. -/
theorem quadraticCyclicGaloisAlgebraOppositeCoefficient_apply (a : K) (x : L) :
    quadraticCyclicGaloisAlgebraOppositeCoefficient K L a x =
      MulOpposite.op (cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L x)) := rfl

/-- The Galois generator of a quadratic cyclic extension is an involution. -/
theorem quadraticCyclicGaloisGenerator_sq (hdeg : Module.finrank K L = 2) :
    cyclicGaloisGenerator K L ^ 2 = 1 := by
  rw [← hdeg]
  exact cyclicGaloisGenerator_pow_finrank K L

/-- The opposite coefficients and opposite cyclic generator obey the full skew-commutation
family required by the universal cyclic-algebra lift. -/
theorem quadraticCyclicGaloisAlgebraOpposite_actions_commute
    (hdeg : Module.finrank K L = 2) (a : K)
    (m : Multiplicative ℕ) (x : L) :
    quadraticCyclicGaloisAlgebraOppositeCoefficient K L a
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) x) *
      cyclicPowerMonoidHom (MulOpposite.op (cyclicGaloisAlgebraX K L a)) m =
    cyclicPowerMonoidHom (MulOpposite.op (cyclicGaloisAlgebraX K L a)) m *
      quadraticCyclicGaloisAlgebraOppositeCoefficient K L a x := by
  rw [quadraticCyclicGaloisAlgebraOppositeCoefficient_apply,
    quadraticCyclicGaloisAlgebraOppositeCoefficient_apply]
  dsimp [cyclicPowerRingAut, cyclicPowerMonoidHom]
  change MulOpposite.op (cyclicGaloisAlgebraC K L a
      ((cyclicGaloisGenerator K L) (((cyclicGaloisGenerator K L).toRingEquiv ^ toAdd m) x))) *
        MulOpposite.op (cyclicGaloisAlgebraX K L a) ^ toAdd m =
      MulOpposite.op (cyclicGaloisAlgebraX K L a) ^ toAdd m *
        MulOpposite.op (cyclicGaloisAlgebraC K L a ((cyclicGaloisGenerator K L) x))
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_pow, MulOpposite.unop_op]
  rw [cyclicAlgebraX_pow_mul_C]
  let sigma := (cyclicGaloisGenerator K L).toRingEquiv
  have hsq : sigma ^ 2 = 1 := by
    ext y
    change (cyclicGaloisGenerator K L ^ 2) y = y
    rw [quadraticCyclicGaloisGenerator_sq K L hdeg]
    rfl
  have hpower : (sigma ^ toAdd m) (sigma ((sigma ^ toAdd m) x)) = sigma x := by
    calc
      (sigma ^ toAdd m) (sigma ((sigma ^ toAdd m) x)) =
          (sigma ^ toAdd m * sigma * sigma ^ toAdd m) x := rfl
      _ = (sigma ^ (toAdd m + 1 + toAdd m)) x := by
            rw [← pow_succ, ← pow_add]
      _ = (sigma ^ (2 * toAdd m + 1)) x := by
            congr 2
            omega
      _ = ((sigma ^ 2) ^ toAdd m * sigma) x := by
            rw [pow_succ, ← pow_mul]
      _ = sigma x := by rw [hsq]; simp
  dsimp [sigma] at hpower
  rw [hpower]

/-- The explicit quadratic cyclic anti-homomorphism, expressed as a ring homomorphism to the
opposite algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraOppositeRingHom
    (hdeg : Module.finrank K L = 2) (a : K) :
    cyclicGaloisAlgebra K L a →+* (cyclicGaloisAlgebra K L a)ᵐᵒᵖ :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (quadraticCyclicGaloisAlgebraOppositeCoefficient K L a)
    (MulOpposite.op (cyclicGaloisAlgebraX K L a))
    (quadraticCyclicGaloisAlgebraOpposite_actions_commute K L hdeg a) (by
      apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_pow, MulOpposite.unop_op]
      rw [cyclicGaloisAlgebraX_pow]
      change cyclicGaloisAlgebraC K L a (algebraMap K L a) =
        cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L (algebraMap K L a))
      rw [(cyclicGaloisGenerator K L).commutes])

/-- The quadratic cyclic anti-homomorphism applies the Galois involution to coefficients. -/
theorem quadraticCyclicGaloisAlgebraOppositeRingHom_C
    (hdeg : Module.finrank K L = 2) (a : K) (x : L) :
    quadraticCyclicGaloisAlgebraOppositeRingHom K L hdeg a
      (cyclicGaloisAlgebraC K L a x) =
        MulOpposite.op (cyclicGaloisAlgebraC K L a (cyclicGaloisGenerator K L x)) := by
  exact cyclicAlgebraLift_C _ _ _ _ _ _ _ x

/-- The quadratic cyclic anti-homomorphism fixes the cyclic generator. -/
theorem quadraticCyclicGaloisAlgebraOppositeRingHom_X
    (hdeg : Module.finrank K L = 2) (a : K) :
    quadraticCyclicGaloisAlgebraOppositeRingHom K L hdeg a
      (cyclicGaloisAlgebraX K L a) = MulOpposite.op (cyclicGaloisAlgebraX K L a) := by
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

/-- The quadratic cyclic anti-homomorphism respects the base field and is therefore an algebra
homomorphism to the opposite algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraOppositeAlgHom
    (hdeg : Module.finrank K L = 2) (a : K) :
    cyclicGaloisAlgebra K L a →ₐ[K] (cyclicGaloisAlgebra K L a)ᵐᵒᵖ where
  __ := quadraticCyclicGaloisAlgebraOppositeRingHom K L hdeg a
  commutes' b := by
    change quadraticCyclicGaloisAlgebraOppositeRingHom K L hdeg a
      (cyclicGaloisAlgebraC K L a (algebraMap K L b)) = _
    rw [quadraticCyclicGaloisAlgebraOppositeRingHom_C K L hdeg a]
    change MulOpposite.op (cyclicGaloisAlgebraC K L a
      (cyclicGaloisGenerator K L (algebraMap K L b))) =
        MulOpposite.op (cyclicGaloisAlgebraC K L a (algebraMap K L b))
    rw [(cyclicGaloisGenerator K L).commutes]

/-- Nonzero quadratic cyclic algebras are simple, so their nonzero anti-homomorphism is
injective. -/
theorem quadraticCyclicGaloisAlgebraOppositeAlgHom_injective
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    Function.Injective (quadraticCyclicGaloisAlgebraOppositeAlgHom K L hdeg a) := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (quadraticCyclicGaloisAlgebra_one_ne_zero K L hdeg a).symm⟩
  letI : IsSimpleRing (cyclicGaloisAlgebra K L a) :=
    isSimpleRing_cyclicGaloisAlgebra_of_finrank_eq_two K L hdeg a ha
  apply RingHom.injective

/-- Equal finite dimensions turn injectivity of the quadratic cyclic anti-homomorphism into
surjectivity. -/
theorem quadraticCyclicGaloisAlgebraOppositeAlgHom_surjective
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    Function.Surjective (quadraticCyclicGaloisAlgebraOppositeAlgHom K L hdeg a) := by
  have hfin : Module.finrank K (cyclicGaloisAlgebra K L a) =
      Module.finrank K (cyclicGaloisAlgebra K L a)ᵐᵒᵖ :=
    (MulOpposite.opLinearEquiv K).finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (quadraticCyclicGaloisAlgebraOppositeAlgHom K L hdeg a).toLinearMap)).mp
      (quadraticCyclicGaloisAlgebraOppositeAlgHom_injective K L hdeg a ha)

/-- Every nonzero quadratic cyclic Galois algebra is isomorphic to its opposite algebra. -/
noncomputable def quadraticCyclicGaloisAlgebraOppositeAlgEquiv
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    cyclicGaloisAlgebra K L a ≃ₐ[K] (cyclicGaloisAlgebra K L a)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (quadraticCyclicGaloisAlgebraOppositeAlgHom K L hdeg a) ⟨
    quadraticCyclicGaloisAlgebraOppositeAlgHom_injective K L hdeg a ha,
    quadraticCyclicGaloisAlgebraOppositeAlgHom_surjective K L hdeg a ha⟩

/-- The Brauer class of a nonzero quadratic cyclic algebra equals its opposite class. -/
theorem quadraticCyclicGaloisAlgebra_brauerClass_opposite
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    brauerClass (oppositeCSA (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) =
      brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) := by
  exact (brauerClass_eq_of_algEquiv _ _
    (quadraticCyclicGaloisAlgebraOppositeAlgEquiv K L hdeg a ha)).symm

/-- The Brauer inverse of a nonzero quadratic cyclic algebra is its own class. -/
theorem quadraticCyclicGaloisAlgebra_brauerTensorNeg
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    brauerTensorNeg K (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) =
      brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) := by
  rw [brauerTensorNeg_brauerClass]
  exact quadraticCyclicGaloisAlgebra_brauerClass_opposite K L hdeg a ha

/-- The Brauer class of a nonzero quadratic cyclic algebra has additive order dividing two. -/
theorem quadraticCyclicGaloisAlgebra_brauerClass_add_self
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    brauerTensorAdd K (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha))
        (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = brauerSplitClass K := by
  calc
    brauerTensorAdd K (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha))
        (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) =
      brauerTensorAdd K
        (brauerTensorNeg K (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)))
        (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) := by
          exact congrArg (fun z => brauerTensorAdd K z
            (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)))
              (quadraticCyclicGaloisAlgebra_brauerTensorNeg K L hdeg a ha).symm
    _ = brauerSplitClass K := brauerTensorNeg_add_self K _

/-- The two-fold integer multiple of every nonzero quadratic cyclic Brauer class vanishes. -/
theorem two_zsmul_quadraticCyclicGaloisAlgebra_brauerClass_eq_zero
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    (2 : ℤ) • brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) = 0 := by
  calc
    (2 : ℤ) • brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) =
        (1 : ℤ) • brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) +
          (1 : ℤ) • brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) := by
            rw [← add_zsmul]
            norm_num
    _ = brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) +
          brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha) := by simp
    _ = 0 := quadraticCyclicGaloisAlgebra_brauerClass_add_self K L hdeg a ha

end GaloisForLFunctions.HTGeometry.ABHN
