import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentMonomialTorus
import GaloisForLFunctions.HTGeometry.LoopEisenstein.SL2WeylConjugation

/-!
# Affine Weyl conjugation on the extended Cartan torus

The central, finite-coroot, and degree factors are independent in the
semidirect product. Monomial translation acts by the quadratic central
shift prescribed by the affine Cartan action.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

namespace LoopSL2

theorem centralEmbedding_mul_comm (c : Fˣ) (g : LoopSL2 F) :
    centralEmbedding F c * g = g * centralEmbedding F c :=
  SL2SymbolExtension.centralEmbedding_commute
    (Multiplicative.ofAdd (Additive.ofMul c)) g

private theorem conj_central_mul (g h : LoopSL2 F) (c : Fˣ) :
    g * (centralEmbedding F c * h) * g⁻¹ =
      centralEmbedding F c * (g * h * g⁻¹) := by
  rw [← mul_assoc g, ← centralEmbedding_mul_comm]
  simp only [mul_assoc]

/-- The canonical finite Weyl representative, built from the two root groups. -/
def finiteWeylLift : LoopSL2 F := SL2SymbolExtension.weylLower (laurentTameHom F) 1

theorem finiteWeylLift_conj_finiteCoroot (a : Fˣ) :
    finiteWeylLift F * finiteCoroot F a * (finiteWeylLift F)⁻¹ = finiteCoroot F a⁻¹ := by
  rw [finiteCoroot_apply, finiteCoroot_apply, laurentConstantUnit_inv]
  exact SL2SymbolExtension.weylLower_one_conj_diagonal (laurentTameHom F) _

@[simp] theorem rotation_finiteWeylLift (q : Fˣ) :
    rotation q (finiteWeylLift F) = finiteWeylLift F := by
  apply SL2SymbolExtension.ext
  · change sl2Rotation q (sl2WeylLower 1) = sl2WeylLower 1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Rotation_apply, sl2WeylLower]
  · rfl

@[simp] theorem rotation_cartanEmbedding (q : Fˣ) (p : Fˣ × Fˣ) :
    rotation q (cartanEmbedding F p) = cartanEmbedding F p := by
  change rotation q (centralEmbedding F p.1 * finiteCoroot F p.2) =
    centralEmbedding F p.1 * finiteCoroot F p.2
  rw [map_mul, rotation_centralEmbedding, rotation_finiteCoroot]

theorem finiteWeylLift_conj_cartan (c a : Fˣ) :
    finiteWeylLift F * cartanEmbedding F (c, a) * (finiteWeylLift F)⁻¹ =
      cartanEmbedding F (c, a⁻¹) := by
  change finiteWeylLift F * (centralEmbedding F c * finiteCoroot F a) *
    (finiteWeylLift F)⁻¹ = centralEmbedding F c * finiteCoroot F a⁻¹
  rw [conj_central_mul, finiteWeylLift_conj_finiteCoroot]

theorem translationLift_conj_cartan (m : ℤ) (c a : Fˣ) :
    translationLift F m * cartanEmbedding F (c, a) * (translationLift F m)⁻¹ =
      cartanEmbedding F (c * a ^ (-2 * m), a) := by
  change translationLift F m * (centralEmbedding F c * finiteCoroot F a) *
    (translationLift F m)⁻¹ = centralEmbedding F (c * a ^ (-2 * m)) * finiteCoroot F a
  rw [conj_central_mul, translationLift_conj_finiteCoroot, ← mul_assoc, ← map_mul]

/-- The discrepancy between a translation and its rotation is an explicit Cartan element. -/
theorem translationLift_mul_rotation_inv (q : Fˣ) (m : ℤ) :
    translationLift F m * rotation q (translationLift F m)⁻¹ =
      cartanEmbedding F (q ^ (-(m * m)), q ^ m) := by
  have hh : (finiteCoroot F (q ^ (-m)))⁻¹ = finiteCoroot F (q ^ m) := by
    rw [← map_inv, ← zpow_neg, neg_neg]
  have hz : (centralEmbedding F (q ^ (m * m)))⁻¹ =
      centralEmbedding F (q ^ (-(m * m))) := by rw [← map_inv, zpow_neg]
  calc
    _ = translationLift F m * (rotation q (translationLift F m))⁻¹ := by rw [map_inv]
    _ = finiteCoroot F (q ^ m) * centralEmbedding F (q ^ (-(m * m))) := by
      rw [rotation_translationLift, mul_inv_rev, mul_inv_rev, hh, hz]
      group
    _ = cartanEmbedding F (q ^ (-(m * m)), q ^ m) :=
      (centralEmbedding_mul_comm F _ _).symm

end LoopSL2

/-- The central, finite-coroot, and degree factors form an actual split torus. -/
def extendedCartanEmbedding : ((Fˣ × Fˣ) × Fˣ) →* ExtendedLoopSL2 F where
  toFun p := ⟨LoopSL2.cartanEmbedding F p.1, p.2⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact map_one (LoopSL2.cartanEmbedding F)
    · rfl
  map_mul' p r := by
    apply SemidirectProduct.ext
    · change LoopSL2.cartanEmbedding F (p.1 * r.1) =
        LoopSL2.cartanEmbedding F p.1 * LoopSL2.rotation p.2 (LoopSL2.cartanEmbedding F r.1)
      rw [LoopSL2.rotation_cartanEmbedding, map_mul]
    · rfl

theorem extendedCartanEmbedding_injective : Function.Injective (extendedCartanEmbedding F) := by
  intro p r h
  have hc : p.1 = r.1 := LoopSL2.cartanEmbedding_injective F
    (congrArg SemidirectProduct.left h)
  have hq : p.2 = r.2 := congrArg SemidirectProduct.right h
  exact Prod.ext hc hq

/-- Evaluate central, finite, and degree coordinates in the actual extended group. -/
def extendedCartanElement (c a q : Fˣ) : ExtendedLoopSL2 F :=
  extendedCartanEmbedding F ((c, a), q)

theorem extendedCartanElement_eq (c a q : Fˣ) :
    extendedCartanElement F c a q =
      SemidirectProduct.inl (LoopSL2.cartanEmbedding F (c, a)) * SemidirectProduct.inr q :=
  SemidirectProduct.mk_eq_inl_mul_inr q _

/-- Actual conjugation produces the affine quadratic central shift. -/
theorem translation_conj_extendedCartan (m : ℤ) (c a q : Fˣ) :
    SemidirectProduct.inl (LoopSL2.translationLift F m) * extendedCartanElement F c a q *
      (SemidirectProduct.inl (LoopSL2.translationLift F m))⁻¹ =
        extendedCartanElement F (c * a ^ (-2 * m) * q ^ (-(m * m))) (a * q ^ m) q := by
  rw [← map_inv]
  apply SemidirectProduct.ext
  · change (LoopSL2.translationLift F m *
        (LoopSL2.rotationAction (1 : Fˣ)) (LoopSL2.cartanEmbedding F (c, a))) *
        (LoopSL2.rotationAction q) (LoopSL2.translationLift F m)⁻¹ = _
    rw [map_one, MulAut.one_apply]
    change (LoopSL2.translationLift F m * LoopSL2.cartanEmbedding F (c, a)) *
      LoopSL2.rotation q (LoopSL2.translationLift F m)⁻¹ = _
    calc
      _ = (LoopSL2.translationLift F m * LoopSL2.cartanEmbedding F (c, a) *
          (LoopSL2.translationLift F m)⁻¹) *
          (LoopSL2.translationLift F m * LoopSL2.rotation q (LoopSL2.translationLift F m)⁻¹) := by
        group
      _ = LoopSL2.cartanEmbedding F
          (c * a ^ (-2 * m) * q ^ (-(m * m)), a * q ^ m) := by
        rw [LoopSL2.translationLift_conj_cartan, LoopSL2.translationLift_mul_rotation_inv, ← map_mul]
        rfl
  · change (1 * q) * 1 = q
    rw [one_mul, mul_one]

/-- The finite Weyl representative inverts the finite coordinate and fixes center and degree. -/
theorem finiteWeyl_conj_extendedCartan (c a q : Fˣ) :
    SemidirectProduct.inl (LoopSL2.finiteWeylLift F) * extendedCartanElement F c a q *
      (SemidirectProduct.inl (LoopSL2.finiteWeylLift F))⁻¹ =
        extendedCartanElement F c a⁻¹ q := by
  rw [← map_inv]
  apply SemidirectProduct.ext
  · change (LoopSL2.finiteWeylLift F *
        (LoopSL2.rotationAction (1 : Fˣ)) (LoopSL2.cartanEmbedding F (c, a))) *
        (LoopSL2.rotationAction q) (LoopSL2.finiteWeylLift F)⁻¹ = _
    rw [map_one, MulAut.one_apply]
    change (LoopSL2.finiteWeylLift F * LoopSL2.cartanEmbedding F (c, a)) *
      LoopSL2.rotation q (LoopSL2.finiteWeylLift F)⁻¹ = _
    rw [map_inv, LoopSL2.rotation_finiteWeylLift]
    exact LoopSL2.finiteWeylLift_conj_cartan F c a
  · change (1 * q) * 1 = q
    rw [one_mul, mul_one]

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
