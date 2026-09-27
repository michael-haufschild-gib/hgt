import GaloisForLFunctions.HTGeometry.FunctionFieldJetBasis

/-!
# Extending field maps to the jet field

Let `φ : F → F` be a `C`-algebra map.  Since `F` has finite transcendence degree, `φ(t)` is again a
transcendence basis, so the positive jets of `φ(t)` are algebraically independent over `F` and the
assignment

`a ↦ φ(a)`,  `y_(i,k) = t_i^(k+1) ↦ δ^(k+1)(φ t_i)`

extends to an injective ring map `φ̃ : K → K`.  It commutes with the derivation: the difference
`δ ∘ φ̃ - φ̃ ∘ δ` is a derivation along `φ̃`; it kills `C` and every `t_i`, hence the algebraic
extension `F`, and it kills every `y_(i,k)`, hence all of `K`.  A differential ring map of `K` is
determined by its restriction to `F`, so the extension is functorial.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {F : Type*} [Field F] {d : ℕ} {C : Type*} [Field C] [CharZero C] [Algebra C F]
variable {t : Fin d → F} (ht : IsTranscendenceBasis C t)

omit [CharZero C] in
include ht in
/-- A `C`-algebra endomorphism carries a finite transcendence basis to a transcendence basis. -/
theorem isTranscendenceBasis_comp_algHom (φ : F →ₐ[C] F) : IsTranscendenceBasis C (φ ∘ t) :=
  (ht.1.map' φ.toRingHom.injective).isTranscendenceBasis_of_lift_trdeg_le_of_finite
    ht.lift_cardinalMk_eq_trdeg.ge

/-- The extension of `φ` to the jet polynomials. -/
def jetPolyExtension (φ : F →ₐ[C] F) : FunctionJetPoly F d →+* FunctionJetField F d :=
  eval₂Hom ((algebraMap F (FunctionJetField F d)).comp φ.toRingHom)
    (fun q => basisJets ht (φ ∘ t) (q.2, q.1))

theorem jetPolyExtension_injective (φ : F →ₐ[C] F) :
    Function.Injective (jetPolyExtension ht φ) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  have hind := algebraicIndependent_basisJets ht (isTranscendenceBasis_comp_algHom ht φ)
  have hsw : jetPolyExtension ht φ P =
      aeval (fun q : Fin d × ℕ => basisJets ht (φ ∘ t) (q.2, q.1)) (P.map φ.toRingHom) := by
    rw [jetPolyExtension, coe_eval₂Hom, aeval_def, eval₂_map]
  have hind' : AlgebraicIndependent F
      (fun q : Fin d × ℕ => basisJets ht (φ ∘ t) (q.2, q.1)) :=
    hind.comp (fun q : Fin d × ℕ => (q.2, q.1)) (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1)
  have hmap : P.map φ.toRingHom = 0 :=
    (algebraicIndependent_iff_injective_aeval.mp hind') (by rw [← hsw, hP, map_zero])
  exact (MvPolynomial.map_injective _ φ.toRingHom.injective) (by rw [hmap, map_zero])

/-- **The extension `φ̃` of `φ` to the jet field.** -/
def jetFieldExtension (φ : F →ₐ[C] F) :
    FunctionJetField F d →+* FunctionJetField F d :=
  IsFractionRing.lift (jetPolyExtension_injective ht φ)

theorem jetFieldExtension_algebraMap (φ : F →ₐ[C] F)
    (a : F) : jetFieldExtension ht φ (algebraMap F (FunctionJetField F d) a) =
      algebraMap F (FunctionJetField F d) (φ a) := by
  rw [IsScalarTower.algebraMap_apply F (FunctionJetPoly F d) (FunctionJetField F d),
    jetFieldExtension, IsFractionRing.lift_algebraMap, MvPolynomial.algebraMap_eq,
    jetPolyExtension, eval₂Hom_C]
  rfl

theorem jetFieldExtension_functionJet (φ : F →ₐ[C] F)
    (q : Fin d × ℕ) :
    jetFieldExtension ht φ (functionJet q) = basisJets ht (φ ∘ t) (q.2, q.1) := by
  rw [functionJet, jetFieldExtension, IsFractionRing.lift_algebraMap, jetPolyExtension,
    eval₂Hom_X']

theorem jetFieldExtension_algebraMap_C (φ : F →ₐ[C] F)
    (c : C) : jetFieldExtension ht φ (algebraMap C (FunctionJetField F d) c) =
      algebraMap C (FunctionJetField F d) c := by
  rw [IsScalarTower.algebraMap_apply C F (FunctionJetField F d), jetFieldExtension_algebraMap,
    AlgHom.commutes]

/-- **`φ̃` is differential.** -/
theorem jetFieldExtension_deriv (φ : F →ₐ[C] F)
    (x : FunctionJetField F d) :
    jetFieldDerivation ht (jetFieldExtension ht φ x) =
      jetFieldExtension ht φ (jetFieldDerivation ht x) := by
  classical
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  set ψ := jetFieldExtension ht φ
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
      jetFieldExtension_functionJet, sub_eq_zero, basisJets, basisJets]
    simp only [Function.iterate_succ_apply']
    rfl
  rw [adjoin_functionJet_eq_top] at hJ
  exact sub_eq_zero.mp (hJ (IntermediateField.mem_top (x := x)))

/-- **A differential ring map of the jet field is determined by its restriction to `F`.** -/
theorem jetField_ringHom_ext {f₁ f₂ : FunctionJetField F d →+* FunctionJetField F d}
    (hF : ∀ a, f₁ (algebraMap F (FunctionJetField F d) a) =
      f₂ (algebraMap F (FunctionJetField F d) a))
    (h₁ : ∀ x, jetFieldDerivation ht (f₁ x) = f₁ (jetFieldDerivation ht x))
    (h₂ : ∀ x, jetFieldDerivation ht (f₂ x) = f₂ (jetFieldDerivation ht x)) : f₁ = f₂ := by
  let S : IntermediateField F (FunctionJetField F d) :=
    (RingHom.eqLocusField f₁ f₂).toIntermediateField hF
  have hiter : ∀ (f : FunctionJetField F d →+* FunctionJetField F d),
      (∀ x, jetFieldDerivation ht (f x) = f (jetFieldDerivation ht x)) → ∀ n x,
      f (((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[n]) x) =
        ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[n]) (f x) := by
    intro f hf n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hf, ih]
  have hjet : ∀ q : Fin d × ℕ, (functionJet q : FunctionJetField F d) =
      ((jetFieldDerivation ht : FunctionJetField F d → FunctionJetField F d)^[q.2 + 1])
        (algebraMap F (FunctionJetField F d) (t q.1)) := by
    rintro ⟨i, k⟩
    induction k with
    | zero => rw [Function.iterate_one, jetFieldDerivation_basis]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ← ih, jetFieldDerivation_functionJet]
  have hle : IntermediateField.adjoin F (Set.range (functionJet : Fin d × ℕ → _)) ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    change f₁ (functionJet q) = f₂ (functionJet q)
    rw [hjet, hiter f₁ h₁, hiter f₂ h₂, hF]
  rw [adjoin_functionJet_eq_top, top_le_iff] at hle
  ext x
  have hx : x ∈ S := by rw [hle]; exact IntermediateField.mem_top
  exact hx

theorem jetFieldExtension_id :
    jetFieldExtension ht (AlgHom.id C F) = RingHom.id (FunctionJetField F d) :=
  jetField_ringHom_ext ht (fun a => by rw [jetFieldExtension_algebraMap]; rfl)
    (jetFieldExtension_deriv ht _) (fun _ => rfl)

theorem jetFieldExtension_comp (φ ψ : F →ₐ[C] F) :
    jetFieldExtension ht (φ.comp ψ) = (jetFieldExtension ht φ).comp (jetFieldExtension ht ψ) :=
  jetField_ringHom_ext ht
    (fun a => by
      rw [RingHom.comp_apply, jetFieldExtension_algebraMap, jetFieldExtension_algebraMap,
        jetFieldExtension_algebraMap, AlgHom.comp_apply])
    (jetFieldExtension_deriv ht _)
    (fun x => by
      rw [RingHom.comp_apply, RingHom.comp_apply, jetFieldExtension_deriv,
        jetFieldExtension_deriv])

theorem jetFieldExtension_pow (φ : F →ₐ[C] F) (n : ℕ) (x : FunctionJetField F d) :
    jetFieldExtension ht (φ ^ n) x = (⇑(jetFieldExtension ht φ))^[n] x := by
  induction n generalizing x with
  | zero =>
      rw [pow_zero, Function.iterate_zero_apply]
      exact congrArg (fun f : FunctionJetField F d →+* FunctionJetField F d => f x)
        (jetFieldExtension_id ht)
  | succ n ih =>
      rw [pow_succ, Function.iterate_succ_apply, ← ih]
      exact congrArg (fun f : FunctionJetField F d →+* FunctionJetField F d => f x)
        (jetFieldExtension_comp ht _ _)

/-- The extension of an automorphism is an automorphism. -/
def jetFieldExtensionEquiv (σ : F ≃ₐ[C] F) : FunctionJetField F d ≃+* FunctionJetField F d :=
  RingEquiv.ofRingHom (jetFieldExtension ht σ.toAlgHom) (jetFieldExtension ht σ.symm.toAlgHom)
    (by
      rw [← jetFieldExtension_comp, ← jetFieldExtension_id ht]
      congr 1
      ext a
      exact σ.apply_symm_apply a)
    (by
      rw [← jetFieldExtension_comp, ← jetFieldExtension_id ht]
      congr 1
      ext a
      exact σ.symm_apply_apply a)

theorem jetFieldExtensionEquiv_apply (σ : F ≃ₐ[C] F) (x : FunctionJetField F d) :
    jetFieldExtensionEquiv ht σ x = jetFieldExtension ht σ.toAlgHom x := rfl

end

end GaloisForLFunctions.HTGeometry
