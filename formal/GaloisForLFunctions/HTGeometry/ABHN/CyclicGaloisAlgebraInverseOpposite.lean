import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.BrauerGroupStructure

/-!
# Parameter inversion and opposites of cyclic Galois algebras

For every nonzero finite cyclic Galois algebra, the algebra with inverse parameter is the
opposite algebra.  The explicit equivalence sends coefficients identically to the opposite and
sends the cyclic generator to the inverse cyclic generator.  Consequently parameter inversion
models additive inverse on the Brauer group in every cyclic degree.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Multiplicative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
/-- Inverse powers of the cyclic unit transport coefficient action in the opposite direction. -/
theorem cyclicGaloisAlgebraXUnit_inv_pow_mul_C
    (a : K) (ha : a ≠ 0) (m : ℕ) (x : L) :
    let U := cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha)
    (↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) *
      cyclicGaloisAlgebraC K L a⁻¹ ((cyclicGaloisGenerator K L ^ m) x) =
    cyclicGaloisAlgebraC K L a⁻¹ x *
      (↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) := by
  let U := cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha)
  change (↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) *
      cyclicGaloisAlgebraC K L a⁻¹ ((cyclicGaloisGenerator K L ^ m) x) =
    cyclicGaloisAlgebraC K L a⁻¹ x *
      (↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹)
  have hstep (y : L) :
      (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) *
        cyclicGaloisAlgebraC K L a⁻¹ (cyclicGaloisGenerator K L y) =
      cyclicGaloisAlgebraC K L a⁻¹ y * (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) := by
    have hconj := cyclicGaloisAlgebraXUnit_conj_C K L a⁻¹ (inv_ne_zero ha) y
    calc
      (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) *
          cyclicGaloisAlgebraC K L a⁻¹ (cyclicGaloisGenerator K L y) =
        (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) *
          ((↑U : cyclicGaloisAlgebra K L a⁻¹) *
            cyclicGaloisAlgebraC K L a⁻¹ y * (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹)) := by
          rw [hconj]
      _ = cyclicGaloisAlgebraC K L a⁻¹ y * (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) := by
        simp only [← mul_assoc]
        change (↑(U⁻¹ * U) : cyclicGaloisAlgebra K L a⁻¹) *
            cyclicGaloisAlgebraC K L a⁻¹ y * (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) = _
        simp
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [show (U⁻¹) ^ (m + 1) = U⁻¹ * (U⁻¹) ^ m by rw [pow_succ']]
    rw [pow_succ]
    rw [show (↑(U⁻¹ * (U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) =
      (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) *
        (↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) by rfl]
    rw [mul_assoc]
    change (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) *
        ((↑((U⁻¹) ^ m) : cyclicGaloisAlgebra K L a⁻¹) *
          cyclicGaloisAlgebraC K L a⁻¹
            ((cyclicGaloisGenerator K L ^ m) (cyclicGaloisGenerator K L x))) = _
    rw [ih]
    rw [← mul_assoc, hstep]
    rw [mul_assoc]

omit [IsGalois K L] in
/-- The inverse cyclic unit has the original parameter as its degree power. -/
theorem cyclicGaloisAlgebraXUnit_inv_pow
    (a : K) (ha : a ≠ 0) :
    let U := cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha)
    (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) ^ Module.finrank K L =
      cyclicGaloisAlgebraC K L a⁻¹ (algebraMap K L a) := by
  let U := cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha)
  change (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) ^ Module.finrank K L =
    cyclicGaloisAlgebraC K L a⁻¹ (algebraMap K L a)
  let C : L →+* cyclicGaloisAlgebra K L a⁻¹ :=
    cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a⁻¹)
  let w : Lˣ := Units.map (algebraMap K L).toMonoidHom (Units.mk0 a ha)
  let v : (cyclicGaloisAlgebra K L a⁻¹)ˣ := Units.map C.toMonoidHom w
  have hU : U ^ Module.finrank K L = v⁻¹ := by
    apply Units.ext
    change cyclicGaloisAlgebraX K L a⁻¹ ^ Module.finrank K L =
      (↑v⁻¹ : cyclicGaloisAlgebra K L a⁻¹)
    rw [cyclicGaloisAlgebraX_pow]
    dsimp [v]
    have hw : (↑w⁻¹ : L) = (algebraMap K L a)⁻¹ := by
      simp [w]
    change C (algebraMap K L a⁻¹) = C (↑w⁻¹ : L)
    rw [hw]
    exact congrArg C (map_inv₀ (algebraMap K L) a)
  have hUinv : (U⁻¹) ^ Module.finrank K L = v := by
    calc
      (U⁻¹) ^ Module.finrank K L = (U ^ Module.finrank K L)⁻¹ := by rw [inv_pow]
      _ = (v⁻¹)⁻¹ := by rw [hU]
      _ = v := inv_inv _
  calc
    (↑U⁻¹ : cyclicGaloisAlgebra K L a⁻¹) ^ Module.finrank K L =
        ↑((U⁻¹) ^ Module.finrank K L) := rfl
    _ = ↑v := congrArg Units.val hUinv
    _ = cyclicGaloisAlgebraC K L a⁻¹ (algebraMap K L a) := by
      change C (↑w : L) = cyclicGaloisAlgebraC K L a⁻¹ (algebraMap K L a)
      have hw : (↑w : L) = algebraMap K L a := by
        simp [w]
      rw [hw]
      rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The coefficient map for the inverse-parameter opposite presentation. -/
noncomputable def cyclicGaloisAlgebraInverseOppositeCoefficient (a : K) :
    L →+* (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ := by
  let f : L →+* cyclicGaloisAlgebra K L a⁻¹ :=
    cyclicAlgebraCRingHom L (cyclicGaloisGenerator K L).toRingEquiv
      (Module.finrank K L) (algebraMap K L a⁻¹)
  apply RingHom.toOpposite f
  intro x y
  change f x * f y = f y * f x
  rw [← f.map_mul, ← f.map_mul, mul_comm]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The inverse-parameter opposite coefficient map is the ordinary coefficient inclusion. -/
theorem cyclicGaloisAlgebraInverseOppositeCoefficient_apply (a : K) (x : L) :
    cyclicGaloisAlgebraInverseOppositeCoefficient K L a x =
      MulOpposite.op (cyclicGaloisAlgebraC K L a⁻¹ x) := by
  unfold cyclicGaloisAlgebraInverseOppositeCoefficient
  rw [RingHom.toOpposite_apply]
  rfl

omit [IsGalois K L] in
/-- The inverse parameter's opposite generator obeys the cyclic-algebra action relation. -/
theorem cyclicGaloisAlgebraInverseOpposite_actions_commute
    (a : K) (ha : a ≠ 0) (m : Multiplicative ℕ) (x : L) :
    cyclicGaloisAlgebraInverseOppositeCoefficient K L a
        ((cyclicPowerRingAut (cyclicGaloisGenerator K L).toRingEquiv m) x) *
      cyclicPowerMonoidHom
        (MulOpposite.op (↑((cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha))⁻¹) :
          cyclicGaloisAlgebra K L a⁻¹)) m =
    cyclicPowerMonoidHom
        (MulOpposite.op (↑((cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha))⁻¹) :
          cyclicGaloisAlgebra K L a⁻¹)) m *
      cyclicGaloisAlgebraInverseOppositeCoefficient K L a x := by
  rw [cyclicGaloisAlgebraInverseOppositeCoefficient_apply,
    cyclicGaloisAlgebraInverseOppositeCoefficient_apply]
  dsimp [cyclicPowerRingAut, cyclicPowerMonoidHom]
  apply MulOpposite.unop_injective
  simp only [MulOpposite.unop_mul, MulOpposite.unop_pow, MulOpposite.unop_op]
  rw [← Units.val_pow_eq_pow_val]
  have hpow (n : ℕ) (y : L) :
      ((cyclicGaloisGenerator K L).toRingEquiv ^ n) y =
        (cyclicGaloisGenerator K L ^ n) y := by
    induction n with
    | zero => rfl
    | succ n _ => simp [pow_succ]
  rw [hpow]
  simpa only using cyclicGaloisAlgebraXUnit_inv_pow_mul_C K L a ha (toAdd m) x

omit [IsGalois K L] in
/-- Explicit anti-homomorphism from a cyclic Galois algebra to the opposite inverse-parameter
algebra. -/
noncomputable def cyclicGaloisAlgebraInverseOppositeRingHom
    (a : K) (ha : a ≠ 0) :
    cyclicGaloisAlgebra K L a →+* (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ :=
  cyclicAlgebraLift (cyclicGaloisGenerator K L).toRingEquiv (Module.finrank K L)
    (algebraMap K L a) (cyclicGaloisAlgebraInverseOppositeCoefficient K L a)
    (MulOpposite.op (↑((cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha))⁻¹) :
      cyclicGaloisAlgebra K L a⁻¹))
    (cyclicGaloisAlgebraInverseOpposite_actions_commute K L a ha) (by
      apply MulOpposite.unop_injective
      simp only [MulOpposite.unop_pow, MulOpposite.unop_op]
      rw [← Units.val_pow_eq_pow_val]
      exact cyclicGaloisAlgebraXUnit_inv_pow K L a ha)

omit [IsGalois K L] in
/-- Formula for the anti-homomorphism on coefficients. -/
theorem cyclicGaloisAlgebraInverseOppositeRingHom_C
    (a : K) (ha : a ≠ 0) (x : L) :
    cyclicGaloisAlgebraInverseOppositeRingHom K L a ha
      (cyclicGaloisAlgebraC K L a x) =
        MulOpposite.op (cyclicGaloisAlgebraC K L a⁻¹ x) := by
  rw [show cyclicGaloisAlgebraInverseOppositeRingHom K L a ha
      (cyclicGaloisAlgebraC K L a x) =
    cyclicGaloisAlgebraInverseOppositeCoefficient K L a x from
      cyclicAlgebraLift_C _ _ _ _ _ _ _ x]
  exact cyclicGaloisAlgebraInverseOppositeCoefficient_apply K L a x

omit [IsGalois K L] in
/-- Formula for the anti-homomorphism on the cyclic generator. -/
theorem cyclicGaloisAlgebraInverseOppositeRingHom_X
    (a : K) (ha : a ≠ 0) :
    cyclicGaloisAlgebraInverseOppositeRingHom K L a ha
      (cyclicGaloisAlgebraX K L a) =
        MulOpposite.op (↑((cyclicGaloisAlgebraXUnit K L a⁻¹ (inv_ne_zero ha))⁻¹) :
          cyclicGaloisAlgebra K L a⁻¹) := by
  exact cyclicAlgebraLift_X _ _ _ _ _ _ _

omit [IsGalois K L] in
/-- The inverse-parameter anti-homomorphism fixes the base field, hence is a `K`-algebra map. -/
noncomputable def cyclicGaloisAlgebraInverseOppositeAlgHom
    (a : K) (ha : a ≠ 0) :
    cyclicGaloisAlgebra K L a →ₐ[K] (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ where
  __ := cyclicGaloisAlgebraInverseOppositeRingHom K L a ha
  commutes' b := by
    change cyclicGaloisAlgebraInverseOppositeRingHom K L a ha
      (cyclicGaloisAlgebraC K L a (algebraMap K L b)) = _
    rw [cyclicGaloisAlgebraInverseOppositeRingHom_C K L a ha]
    rfl

/-- Simplicity makes the inverse-parameter anti-homomorphism injective. -/
theorem cyclicGaloisAlgebraInverseOppositeAlgHom_injective
    (a : K) (ha : a ≠ 0) :
    Function.Injective (cyclicGaloisAlgebraInverseOppositeAlgHom K L a ha) := by
  letI : Nontrivial (cyclicGaloisAlgebra K L a) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a).symm⟩
  letI : Nontrivial (cyclicGaloisAlgebra K L a⁻¹) :=
    ⟨0, 1, (cyclicGaloisAlgebra_one_ne_zero K L a⁻¹).symm⟩
  letI : IsSimpleRing (cyclicGaloisAlgebra K L a) :=
    isSimpleRing_cyclicGaloisAlgebra_of_nonzero K L a ha
  apply RingHom.injective

/-- Equal cyclic normal-form dimensions make the inverse-parameter anti-homomorphism
surjective. -/
theorem cyclicGaloisAlgebraInverseOppositeAlgHom_surjective
    (a : K) (ha : a ≠ 0) :
    Function.Surjective (cyclicGaloisAlgebraInverseOppositeAlgHom K L a ha) := by
  have hfin : Module.finrank K (cyclicGaloisAlgebra K L a) =
      Module.finrank K (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ := by
    calc
      Module.finrank K (cyclicGaloisAlgebra K L a) = Module.finrank K L ^ 2 :=
        cyclicGaloisAlgebra_finrank_eq_square K L a
      _ = Module.finrank K (cyclicGaloisAlgebra K L a⁻¹) :=
        (cyclicGaloisAlgebra_finrank_eq_square K L a⁻¹).symm
      _ = Module.finrank K (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ :=
        (MulOpposite.opLinearEquiv K).finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
    (f := (cyclicGaloisAlgebraInverseOppositeAlgHom K L a ha).toLinearMap)).mp
      (cyclicGaloisAlgebraInverseOppositeAlgHom_injective K L a ha)

/-- A nonzero cyclic Galois algebra is the opposite of the cyclic algebra with inverse
parameter. -/
noncomputable def cyclicGaloisAlgebraInverseOppositeAlgEquiv
    (a : K) (ha : a ≠ 0) :
    cyclicGaloisAlgebra K L a ≃ₐ[K] (cyclicGaloisAlgebra K L a⁻¹)ᵐᵒᵖ :=
  AlgEquiv.ofBijective (cyclicGaloisAlgebraInverseOppositeAlgHom K L a ha) ⟨
    cyclicGaloisAlgebraInverseOppositeAlgHom_injective K L a ha,
    cyclicGaloisAlgebraInverseOppositeAlgHom_surjective K L a ha⟩

/-- The opposite class of the inverse-parameter cyclic algebra is the original cyclic class. -/
theorem cyclicGaloisAlgebraInverse_brauerClass_opposite
    (a : K) (ha : a ≠ 0) :
    brauerClass (oppositeCSA (cyclicGaloisAlgebraCSA K L a⁻¹ (inv_ne_zero ha))) =
      brauerClass (cyclicGaloisAlgebraCSA K L a ha) := by
  exact (brauerClass_eq_of_algEquiv _ _
    (cyclicGaloisAlgebraInverseOppositeAlgEquiv K L a ha)).symm

/-- The Brauer inverse of the inverse-parameter cyclic algebra is the original cyclic class. -/
theorem cyclicGaloisAlgebraInverse_brauerTensorNeg
    (a : K) (ha : a ≠ 0) :
    brauerTensorNeg K (brauerClass (cyclicGaloisAlgebraCSA K L a⁻¹ (inv_ne_zero ha))) =
      brauerClass (cyclicGaloisAlgebraCSA K L a ha) := by
  rw [brauerTensorNeg_brauerClass]
  exact cyclicGaloisAlgebraInverse_brauerClass_opposite K L a ha

/-- Parameter inversion is Brauer inversion for every nonzero finite cyclic Galois algebra. -/
theorem cyclicGaloisAlgebra_brauerTensorNeg
    (a : K) (ha : a ≠ 0) :
    brauerTensorNeg K (brauerClass (cyclicGaloisAlgebraCSA K L a ha)) =
      brauerClass (cyclicGaloisAlgebraCSA K L a⁻¹ (inv_ne_zero ha)) := by
  simpa only [inv_inv] using
    cyclicGaloisAlgebraInverse_brauerTensorNeg K L a⁻¹ (inv_ne_zero ha)

end GaloisForLFunctions.HTGeometry.ABHN
