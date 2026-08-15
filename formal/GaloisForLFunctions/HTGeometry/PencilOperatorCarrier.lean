import GaloisForLFunctions.HTGeometry.PencilTranslationExpansion
import GaloisForLFunctions.HTGeometry.PencilFacetRestriction
import GaloisForLFunctions.HTGeometry.SeveralVariableDirectionalDifferential

/-!
# A difference operator with derivation coefficients, applied to a source

Evaluating a polynomial at the difference operators `T_v - 1` is the same as expanding it in
translation variables and reading each monomial as one translation.  Allowing the coefficients to be
polynomials in the derivation gives the action of the full operator ring `ℂ[δ][t_v]` on a source:
each translation monomial contributes its coefficient polynomial applied to the derivation.

The resulting carrier is additive in the operator, turns multiplication by a vertex variable into the
difference operator of that vertex, and turns multiplication by the derivation variable into the
derivation.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-! ### The translation expansion of the difference carrier -/

variable {α : Type*} [DecidableEq α] {E : Type*} [AddCommMonoid E]

/-- The translation attached to a monomial exponent. -/
def translationAddHom (ω : α → E) : (α →₀ ℕ) →+ E :=
  Finsupp.liftAddHom fun v => (smulAddHom ℕ E).flip (ω v)

omit [DecidableEq α] in
@[simp] theorem translationAddHom_single (ω : α → E) (v : α) (n : ℕ) :
    translationAddHom ω (Finsupp.single v n) = n • ω v := by
  rw [translationAddHom, Finsupp.liftAddHom_apply_single]
  rfl

omit [DecidableEq α] in
/-- **The difference operators are the translation expansion.** -/
theorem polyShift_eq_mapDomain (ω : α → E) :
    polyShift ω = (AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (translationAddHom ω)).comp
      (differenceToTranslationHom : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial α ℂ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [polyShift_X, stepVar]
  show _ = AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (translationAddHom ω)
    (differenceToTranslationHom (MvPolynomial.X v))
  rw [differenceToTranslationHom, MvPolynomial.aeval_X, map_sub, map_one]
  congr 1
  show AddMonoidAlgebra.single (ω v) (1 : ℂ)
    = AddMonoidAlgebra.mapDomain (translationAddHom ω) (MvPolynomial.X v)
  rw [show (MvPolynomial.X v : MvPolynomial α ℂ)
      = AddMonoidAlgebra.single (Finsupp.single v 1) 1 from rfl,
    AddMonoidAlgebra.mapDomain_single, translationAddHom_single, one_smul]

omit [DecidableEq α] in
/-- **The carrier in translation coordinates.** -/
theorem seedCarrierPoly_apply_translation (ω : α → E) (F : E → ℂ) (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly ω F P z
      = ∑ e ∈ (differenceToTranslationHom P).support,
          MvPolynomial.coeff e (differenceToTranslationHom P) * F (z + translationAddHom ω e) := by
  rw [seedCarrierPoly, shiftAlgHom_apply, polyShift_eq_mapDomain]
  have hcoeff : AddMonoidAlgebra.coeff
      ((AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (translationAddHom ω)).comp
        (differenceToTranslationHom : MvPolynomial α ℂ →ₐ[ℂ] MvPolynomial α ℂ) P)
      = Finsupp.mapDomain (translationAddHom ω)
        (AddMonoidAlgebra.coeff (differenceToTranslationHom P)) :=
    AddMonoidAlgebra.coeff_mapDomain _ _
  rw [hcoeff]
  exact Finsupp.sum_mapDomain_index (h := fun t c => c * F (z + t))
    (h_zero := fun t => zero_mul _) (h_add := fun t c c' => add_mul c c' _)

/-! ### The derivation commutes with translation -/

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem dirDerivFun_comp_add_const (w τ : E') (f : E' → ℂ) :
    dirDerivFun w (fun z => f (z + τ)) = fun z => dirDerivFun w f (z + τ) := by
  funext z
  rw [dirDerivFun, dirDerivFun, fderiv_comp_add_right τ]

/-- **A constant directional derivative commutes with translation.** -/
theorem dirDerivFun_iterate_comp_add_const (w τ : E') (f : E' → ℂ) (r : ℕ) :
    (dirDerivFun w)^[r] (fun z => f (z + τ)) = fun z => ((dirDerivFun w)^[r] f) (z + τ) := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, dirDerivFun_comp_add_const, ih]
      funext z
      rw [Function.iterate_succ_apply]

/-! ### An operator with derivation coefficients -/

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem facetRestrict_C (A : Finset α) (r : R) :
    facetRestrict A (MvPolynomial.C r) = MvPolynomial.C r := by
  rw [facetRestrict, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

omit [DecidableEq α] in
@[simp] theorem differenceToTranslationHom_C (r : R) :
    differenceToTranslationHom (MvPolynomial.C r : MvPolynomial α R) = MvPolynomial.C r := by
  rw [differenceToTranslationHom, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

theorem facetRestrict_map (φ : R →+* S) (A : Finset α) (P : MvPolynomial α R) :
    facetRestrict A (MvPolynomial.map φ P) = MvPolynomial.map φ (facetRestrict A P) := by
  have hhom : ((facetRestrict (R := S) A).toRingHom).comp (MvPolynomial.map φ)
      = (MvPolynomial.map φ).comp ((facetRestrict (R := R) A).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show facetRestrict A (MvPolynomial.map φ (MvPolynomial.C r))
        = MvPolynomial.map φ (facetRestrict A (MvPolynomial.C r))
      rw [MvPolynomial.map_C, facetRestrict_C, facetRestrict_C, MvPolynomial.map_C]
    · intro v
      show facetRestrict A (MvPolynomial.map φ (MvPolynomial.X v))
        = MvPolynomial.map φ (facetRestrict A (MvPolynomial.X v))
      rw [MvPolynomial.map_X]
      by_cases hv : v ∈ A
      · rw [facetRestrict_X_mem hv, facetRestrict_X_mem hv, MvPolynomial.map_X]
      · rw [facetRestrict_X_notMem hv, facetRestrict_X_notMem hv, map_zero]
  exact congrArg (fun f : MvPolynomial α R →+* MvPolynomial α S => f P) hhom

omit [DecidableEq α] in
theorem differenceToTranslationHom_map (φ : R →+* S) (P : MvPolynomial α R) :
    differenceToTranslationHom (MvPolynomial.map φ P)
      = MvPolynomial.map φ (differenceToTranslationHom P) := by
  have hhom : ((differenceToTranslationHom (R := S) (α := α)).toRingHom).comp
        (MvPolynomial.map φ)
      = (MvPolynomial.map φ).comp
        ((differenceToTranslationHom (R := R) (α := α)).toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show differenceToTranslationHom (MvPolynomial.map φ (MvPolynomial.C r))
        = MvPolynomial.map φ (differenceToTranslationHom (MvPolynomial.C r))
      rw [MvPolynomial.map_C, differenceToTranslationHom_C, differenceToTranslationHom_C,
        MvPolynomial.map_C]
    · intro v
      show differenceToTranslationHom (MvPolynomial.map φ (MvPolynomial.X v))
        = MvPolynomial.map φ (differenceToTranslationHom (MvPolynomial.X v))
      simp only [MvPolynomial.map_X, differenceToTranslationHom, MvPolynomial.aeval_X, map_sub,
        MvPolynomial.map_X, map_one]
  exact congrArg (fun f : MvPolynomial α R →+* MvPolynomial α S => f P) hhom

variable {d : ℕ}

/-- The operator `∑_r δ^r Q_r` as an element of the Stanley--Reisner operator ring. -/
def opPoly (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) : MvPolynomial α (Polynomial ℂ) :=
  ∑ r ∈ Finset.range n,
    MvPolynomial.C (Polynomial.X ^ r) * MvPolynomial.map (Polynomial.C) (Q r)

/-- The carrier of that operator on a source: each difference-operator coefficient acts on the
corresponding jet. -/
def opCarrier (w : Fin d → ℂ) (ω : α → (Fin d → ℂ)) (F : (Fin d → ℂ) → ℂ)
    (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) : (Fin d → ℂ) → ℂ :=
  fun z => ∑ r ∈ Finset.range n,
    seedCarrierPoly ω ((dirDerivFun w)^[r] F) (Q r) z

/-- The derivation of a finite combination of translates. -/
theorem dirDerivFun_translation_sum (w : E') {f : E' → ℂ} (hf : Differentiable ℂ f)
    {κ : Type*} (s : Finset κ) (c : κ → ℂ) (τ : κ → E') :
    dirDerivFun w (fun z => ∑ i ∈ s, c i * f (z + τ i))
      = fun z => ∑ i ∈ s, c i * dirDerivFun w f (z + τ i) := by
  funext z
  have hd : ∀ i ∈ s, DifferentiableAt ℂ (fun y : E' => c i * f (y + τ i)) z := by
    intro i _
    exact ((hf (z + τ i)).comp z ((differentiable_id.add_const (τ i)) z)).const_mul (c i)
  show fderiv ℂ (fun y : E' => ∑ i ∈ s, c i * f (y + τ i)) z w = _
  rw [fderiv_fun_sum hd]
  rw [show (∑ i ∈ s, fderiv ℂ (fun y : E' => c i * f (y + τ i)) z) w
      = ∑ i ∈ s, fderiv ℂ (fun y : E' => c i * f (y + τ i)) z w from
    sum_apply _ _ w]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi : DifferentiableAt ℂ (fun y : E' => f (y + τ i)) z :=
    (hf (z + τ i)).comp z ((differentiable_id.add_const (τ i)) z)
  rw [fderiv_const_mul hdi, smul_apply, smul_eq_mul, fderiv_comp_add_right]
  rfl

/-- **The iterated derivation of a finite combination of translates.** -/
theorem dirDerivFun_iterate_translation_sum (w : E') (r : ℕ) {f : E' → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {κ : Type*} (s : Finset κ) (c : κ → ℂ) (τ : κ → E') :
    (dirDerivFun w)^[r] (fun z => ∑ i ∈ s, c i * f (z + τ i))
      = fun z => ∑ i ∈ s, c i * ((dirDerivFun w)^[r] f) (z + τ i) := by
  induction r generalizing f with
  | zero => simp
  | succ r ih =>
      have hdiff : Differentiable ℂ f := fun x => (hf x (Set.mem_univ x)).differentiableAt
      rw [Function.iterate_succ_apply, dirDerivFun_translation_sum w hdiff s c τ,
        ih (analyticOnNhd_dirDerivFun w hf)]
      funext z
      rw [Function.iterate_succ_apply]

omit [DecidableEq α] in
/-- **The carrier is the operator applied to the source.**  The derivation may equivalently be
applied after the difference operator, because a constant derivation commutes with translation. -/
theorem opCarrier_eq (w : Fin d → ℂ) (ω : α → (Fin d → ℂ)) {F : (Fin d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) :
    opCarrier w ω F n Q
      = fun z => ∑ r ∈ Finset.range n,
        ((dirDerivFun w)^[r] (seedCarrierPoly ω F (Q r))) z := by
  funext z
  refine Finset.sum_congr rfl fun r _ => ?_
  have hcarrier : seedCarrierPoly ω F (Q r)
      = fun y => ∑ e ∈ (differenceToTranslationHom (Q r)).support,
        MvPolynomial.coeff e (differenceToTranslationHom (Q r))
          * F (y + translationAddHom ω e) := by
    funext y
    exact seedCarrierPoly_apply_translation ω F (Q r) y
  rw [hcarrier, dirDerivFun_iterate_translation_sum w r hF]
  show seedCarrierPoly ω ((dirDerivFun w)^[r] F) (Q r) z
      = ∑ e ∈ (differenceToTranslationHom (Q r)).support,
        MvPolynomial.coeff e (differenceToTranslationHom (Q r))
          * ((dirDerivFun w)^[r] F) (z + translationAddHom ω e)
  exact seedCarrierPoly_apply_translation ω ((dirDerivFun w)^[r] F) (Q r) z

/-! ### Coefficients of an operator -/

theorem facetRestrict_opPoly (A : Finset α) (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) :
    facetRestrict A (opPoly n Q) = opPoly n (fun r => facetRestrict A (Q r)) := by
  rw [opPoly, map_sum, opPoly]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, facetRestrict_C, facetRestrict_map]

omit [DecidableEq α] in
theorem differenceToTranslationHom_opPoly (n : ℕ) (Q : ℕ → MvPolynomial α ℂ) :
    differenceToTranslationHom (opPoly n Q)
      = ∑ r ∈ Finset.range n, MvPolynomial.C (Polynomial.X ^ r) *
        MvPolynomial.map Polynomial.C (differenceToTranslationHom (Q r)) := by
  rw [opPoly, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, differenceToTranslationHom_C, differenceToTranslationHom_map]

omit [DecidableEq α] in
/-- **The derivation coefficients of an operator are its difference-operator coefficients.** -/
theorem coeff_differenceToTranslationHom_opPoly (n : ℕ) (Q : ℕ → MvPolynomial α ℂ)
    (e : α →₀ ℕ) (s : ℕ) :
    Polynomial.coeff (MvPolynomial.coeff e (differenceToTranslationHom (opPoly n Q))) s
      = if s ∈ Finset.range n then
          MvPolynomial.coeff e (differenceToTranslationHom (Q s)) else 0 := by
  classical
  rw [differenceToTranslationHom_opPoly, MvPolynomial.coeff_sum, Polynomial.finsetSum_coeff]
  rw [← Finset.sum_ite_eq' (Finset.range n) s
    (fun r => MvPolynomial.coeff e (differenceToTranslationHom (Q r)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
    show (Polynomial.X : Polynomial ℂ) ^ r
      * Polynomial.C (MvPolynomial.coeff e (differenceToTranslationHom (Q r)))
      = Polynomial.monomial r (MvPolynomial.coeff e (differenceToTranslationHom (Q r))) by
      rw [Polynomial.X_pow_mul, Polynomial.C_mul_X_pow_eq_monomial],
    Polynomial.coeff_monomial]

/-! ### The facet expansion of a carrier -/

variable {facets : Finset (Finset α)}

omit [DecidableEq α] in
/-- A source periodic under every step outside its facet is annihilated by the corresponding
difference operator. -/
theorem shiftAlgHom_stepVar_eq_zero_of_periodic {ω : α → E} {G : E → ℂ} {v : α}
    (hG : ∀ z, G (z + ω v) = G z) : shiftAlgHom (stepVar ω v) G = 0 := by
  funext z
  rw [shiftAlgHom_stepVar]
  show G (z + ω v) - G z = 0
  rw [hG z, sub_self]

/-- **On a source periodic outside its facet, only the facet variables act.** -/
theorem seedCarrierPoly_facetRestrict_of_periodic (ω : α → E) {A : Finset α} {G : E → ℂ}
    (hG : ∀ v ∉ A, ∀ z, G (z + ω v) = G z) (P : MvPolynomial α ℂ) :
    seedCarrierPoly ω G P = seedCarrierPoly ω G (facetRestrict A P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [facetRestrict_C]
  | add p q hp hq =>
      rw [seedCarrierPoly_add, hp, hq, map_add, seedCarrierPoly_add]
  | mul_X p v hp =>
      by_cases hv : v ∈ A
      · rw [map_mul, facetRestrict_X_mem hv]
        rw [show p * MvPolynomial.X v = MvPolynomial.X v * p from mul_comm _ _,
          show facetRestrict A p * MvPolynomial.X v
            = MvPolynomial.X v * facetRestrict A p from mul_comm _ _,
          seedCarrierPoly_X_mul, seedCarrierPoly_X_mul, hp]
      · rw [map_mul, facetRestrict_X_notMem hv, mul_zero]
        have hzero : seedCarrierPoly ω G (MvPolynomial.X v) = 0 := by
          show shiftAlgHom (polyShift ω (MvPolynomial.X v)) G = 0
          rw [polyShift_X]
          exact shiftAlgHom_stepVar_eq_zero_of_periodic (hG v hv)
        have hR : seedCarrierPoly ω G 0 = 0 := map_zero (seedCarrierPolyₗ ω G)
        rw [hR, seedCarrierPoly_mul, hzero, map_zero]

/-- **The facet expansion of a carrier.**  The carrier of a difference operator on a sum of facet
sources is the sum of the carriers of its facet restrictions. -/
theorem seedCarrierPoly_sum_facetRestrict (ω : α → E) (Y : facets → E → ℂ)
    (hY : ∀ (A : facets) (v : α), v ∉ A.1 → ∀ z, Y A (z + ω v) = Y A z)
    (P : MvPolynomial α ℂ) (z : E) :
    seedCarrierPoly ω (fun y => ∑ A : facets, Y A y) P z
      = ∑ A : facets, seedCarrierPoly ω (Y A) (facetRestrict A.1 P) z := by
  classical
  have hfun : (fun y => ∑ A : facets, Y A y)
      = fun y => ∑ A ∈ (Finset.univ : Finset facets), Y A y := rfl
  rw [hfun, seedCarrierPoly_sum]
  exact Finset.sum_congr rfl fun A _ =>
    congrFun (seedCarrierPoly_facetRestrict_of_periodic ω (hY A) P) z

end

end GaloisForLFunctions.HTGeometry
