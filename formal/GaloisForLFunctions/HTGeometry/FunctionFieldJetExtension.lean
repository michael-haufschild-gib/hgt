import GaloisForLFunctions.HTGeometry.FunctionFieldJetBasis

/-!
# Extending field maps to the jet field

Let `φ : F → F` be a `C`-algebra map such that `φ(t)` is again a transcendence basis (every
automorphism, and every pullback along a dominant endomorphism of a variety).  Since the positive
jets of `φ(t)` are algebraically independent over `F`, the assignment

`a ↦ φ(a)`,  `y_(i,k) = t_i^(k+1) ↦ δ^(k+1)(φ t_i)`

extends to an injective ring map `φ̃ : K → K`.  It commutes with the derivation: the difference
`δ ∘ φ̃ - φ̃ ∘ δ` is a derivation along `φ̃`; it kills `C` and every `t_i`, hence the algebraic
extension `F`, and it kills every `y_(i,k)`, hence all of `K`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] {d : ℕ} {C : Type*} [Field C] [CharZero C] [Algebra C F]
variable {t : Fin d → F} (ht : IsTranscendenceBasis C t)

/-- The extension of `φ` to the jet polynomials. -/
def jetPolyExtension (φ : F →ₐ[C] F) : FunctionJetPoly F d →+* FunctionJetField F d :=
  eval₂Hom ((algebraMap F (FunctionJetField F d)).comp φ.toRingHom)
    (fun q => basisJets ht (φ ∘ t) (q.2, q.1))

theorem jetPolyExtension_injective (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t)) :
    Function.Injective (jetPolyExtension ht φ) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hind := algebraicIndependent_basisJets ht hφ
  have hsw : jetPolyExtension ht φ P =
      aeval (fun q : Fin d × ℕ => basisJets ht (φ ∘ t) (q.2, q.1)) (P.map φ.toRingHom) := by
    rw [jetPolyExtension, coe_eval₂Hom, aeval_def, eval₂_map]
    rfl
  have hind' : AlgebraicIndependent F
      (fun q : Fin d × ℕ => basisJets ht (φ ∘ t) (q.2, q.1)) :=
    hind.comp (fun q : Fin d × ℕ => (q.2, q.1)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1)
  have hmap : P.map φ.toRingHom = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp hind') (by rw [← hsw, hP, map_zero])
  exact (MvPolynomial.map_injective _ φ.toRingHom.injective) (by rw [hmap, map_zero])

/-- **The extension `φ̃` of `φ` to the jet field.** -/
def jetFieldExtension (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t)) :
    FunctionJetField F d →+* FunctionJetField F d :=
  IsFractionRing.lift (jetPolyExtension_injective ht φ hφ)

theorem jetFieldExtension_algebraMap (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t))
    (a : F) : jetFieldExtension ht φ hφ (algebraMap F (FunctionJetField F d) a) =
      algebraMap F (FunctionJetField F d) (φ a) := by
  rw [IsScalarTower.algebraMap_apply F (FunctionJetPoly F d) (FunctionJetField F d),
    jetFieldExtension, IsFractionRing.lift_algebraMap, MvPolynomial.algebraMap_eq,
    jetPolyExtension, eval₂Hom_C]
  rfl

theorem jetFieldExtension_functionJet (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t))
    (q : Fin d × ℕ) :
    jetFieldExtension ht φ hφ (functionJet q) = basisJets ht (φ ∘ t) (q.2, q.1) := by
  rw [functionJet, jetFieldExtension, IsFractionRing.lift_algebraMap, jetPolyExtension,
    eval₂Hom_X']

theorem jetFieldExtension_algebraMap_C (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t))
    (c : C) : jetFieldExtension ht φ hφ (algebraMap C (FunctionJetField F d) c) =
      algebraMap C (FunctionJetField F d) c := by
  rw [IsScalarTower.algebraMap_apply C F (FunctionJetField F d), jetFieldExtension_algebraMap,
    AlgHom.commutes]

/-- **`φ̃` is differential.** -/
theorem jetFieldExtension_deriv (φ : F →ₐ[C] F) (hφ : IsTranscendenceBasis C (φ ∘ t))
    (x : FunctionJetField F d) :
    jetFieldDerivation ht (jetFieldExtension ht φ hφ x) =
      jetFieldExtension ht φ hφ (jetFieldDerivation ht x) := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  set ψ := jetFieldExtension ht φ hφ
  set δ := jetFieldDerivation ht
  let E : FunctionJetField F d → FunctionJetField F d := fun x => δ (ψ x) - ψ (δ x)
  have hadd : ∀ x y, E (x + y) = E x + E y := by
    intro x y
    simp only [E, map_add]
    ring
  have hmul : ∀ x y, E (x * y) = ψ x * E y + ψ y * E x := by
    intro x y
    simp only [E, map_mul, Derivation.leibniz, smul_eq_mul, map_add]
    ring
  -- `E` kills `C(t)`, hence the algebraic extension `F`
  let ι : F →+* FunctionJetField F d := ψ.comp (algebraMap F (FunctionJetField F d))
  let EF : F → FunctionJetField F d := fun a => E (algebraMap F (FunctionJetField F d) a)
  have haddF : ∀ a b, EF (a + b) = EF a + EF b := fun a b => by
    simp only [EF, map_add, hadd]
  have hmulF : ∀ a b, EF (a * b) = ι a * EF b + ι b * EF a := fun a b => by
    simp only [EF, map_mul, hmul, ι, RingHom.comp_apply]
  let KI : IntermediateField C F :=
    (twistedKernel ι EF haddF hmulF).toIntermediateField fun c => by
      change δ (ψ (algebraMap F (FunctionJetField F d) (algebraMap C F c))) -
        ψ (δ (algebraMap F (FunctionJetField F d) (algebraMap C F c))) = 0
      rw [← IsScalarTower.algebraMap_apply, jetFieldExtension_algebraMap_C,
        Derivation.map_algebraMap, map_zero, sub_zero]
  have hle : IntermediateField.adjoin C (Set.range t) ≤ KI := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    change δ (ψ (algebraMap F (FunctionJetField F d) (t i))) -
      ψ (δ (algebraMap F (FunctionJetField F d) (t i))) = 0
    rw [jetFieldExtension_algebraMap, jetFieldDerivation_basis, jetFieldExtension_functionJet,
      sub_eq_zero]
    rfl
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin C (Set.range t)) F := ht.isAlgebraic_field
  have hF : ∀ a, EF a = 0 := fun a =>
    twisted_eq_zero_of_isIntegral ι EF haddF hmulF
      (S' := IntermediateField.adjoin C (Set.range t)) (fun b => hle b.2)
      (Algebra.IsIntegral.isIntegral a)
  -- `E` kills every jet, hence the whole jet field
  let KJ : IntermediateField F (FunctionJetField F d) :=
    (twistedKernel ψ E hadd hmul).toIntermediateField hF
  have hJ : IntermediateField.adjoin F (Set.range (functionJet : Fin d × ℕ → _)) ≤ KJ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    change δ (ψ (functionJet q)) - ψ (δ (functionJet q)) = 0
    rw [jetFieldDerivation_functionJet, jetFieldExtension_functionJet,
      jetFieldExtension_functionJet, sub_eq_zero, basisJets, basisJets,
      Function.iterate_succ_apply' (f := (δ : FunctionJetField F d → FunctionJetField F d))]
  rw [adjoin_functionJet_eq_top] at hJ
  exact sub_eq_zero.mp (hJ (IntermediateField.mem_top (x := x)))

end

end GaloisForLFunctions.HTGeometry
