import GaloisForLFunctions.HTGeometry.ShiftedGammaMultiplicativeCoboundary
import GaloisForLFunctions.HTGeometry.MultiplicativeShiftIndependence

/-!
# Theorem B: the Gamma translates are free over the shifted digamma field

Let `L_E` be the field generated over `ℂ(X)` by the jets of the shifted digammas.  The unit shift
maps `L_E` into itself, because each generator moves by a rational increment, and it multiplies each
Gamma translate by its shift factor.  A minimal-support descent then reduces algebraic dependence of
the Gamma translates over `L_E` to a multiplicative coboundary equation inside `L_E`, which the
orbit obstruction excludes.

So the Gamma translates are algebraically independent over the field their logarithmic derivatives
generate.
-/

open Filter Set Topology Function MvPolynomial MonomialOrder

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions RationalIncrementHolder Bottcher

noncomputable section

local instance shiftedGammaFieldDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance shiftedGammaFieldIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring (Set.univ : Set ℂ)) := Ring.toIntAlgebra _

local instance shiftedGammaFieldIntAlgebraMero :
    Algebra ℤ (meroField (Set.univ : Set ℂ)) := Ring.toIntAlgebra _

local instance shiftedGammaFieldIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance shiftedGammaFieldDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance shiftedGammaFieldRatDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance shiftedGammaFieldRatAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

variable {r : ℕ}

/-- The field generated over `ℂ(X)` by the jets of the shifted digammas. -/
def digammaField (lam : Fin r → ℂ) :
    IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  IntermediateField.adjoin (RatFunc ℂ) (Set.range (digammaJet lam))

theorem digammaJet_mem_digammaField (lam : Fin r → ℂ) (p : Fin r × ℕ) :
    digammaJet lam p ∈ digammaField lam :=
  IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩

/-- The unit shift maps the digamma field into itself. -/
theorem shift_mem_digammaField (lam : Fin r → ℂ) {u : meroField (Set.univ : Set ℂ)}
    (hu : u ∈ digammaField lam) : addTranslationMeroEquiv 1 u ∈ digammaField lam := by
  have hle : (digammaField lam).toSubfield ≤
      (digammaField lam).toSubfield.comap
        ((addTranslationMeroEquiv 1 : meroField (Set.univ : Set ℂ) ≃+*
          meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) →+*
            meroField (Set.univ : Set ℂ)) := by
    rw [digammaField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨q, rfl⟩ | ⟨p, rfl⟩)
    · show addTranslationMeroEquiv 1
        (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) q) ∈ digammaField lam
      rw [show addTranslationMeroEquiv 1
          (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) q)
          = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (ratShift q) from
        addTranslationMeroEquiv_ratfuncToMero q]
      exact (digammaField lam).algebraMap_mem _
    · show addTranslationMeroEquiv 1 (digammaJet lam p) ∈ digammaField lam
      rw [addTranslationMeroEquiv_digammaJet]
      exact add_mem (digammaJet_mem_digammaField lam p) ((digammaField lam).algebraMap_mem _)
  exact hle hu

/-- The unit shift restricted to the digamma field. -/
def digammaFieldShift (lam : Fin r → ℂ) : digammaField lam →+* digammaField lam where
  toFun u := ⟨addTranslationMeroEquiv 1 u.1, shift_mem_digammaField lam u.2⟩
  map_one' := Subtype.ext (addTranslationMeroEquiv 1).map_one
  map_mul' a b := Subtype.ext ((addTranslationMeroEquiv 1).map_mul a.1 b.1)
  map_zero' := Subtype.ext (addTranslationMeroEquiv 1).map_zero
  map_add' a b := Subtype.ext ((addTranslationMeroEquiv 1).map_add a.1 b.1)

@[simp] theorem digammaFieldShift_coe (lam : Fin r → ℂ) (u : digammaField lam) :
    ((digammaFieldShift lam u : digammaField lam) : meroField (Set.univ : Set ℂ))
      = addTranslationMeroEquiv 1 (u : meroField (Set.univ : Set ℂ)) := rfl

theorem digammaFieldShift_injective (lam : Fin r → ℂ) :
    Function.Injective (digammaFieldShift lam) := by
  intro a b hab
  have h := congrArg (fun u : digammaField lam => (u : meroField (Set.univ : Set ℂ))) hab
  simp only [digammaFieldShift_coe] at h
  exact Subtype.ext ((addTranslationMeroEquiv 1).injective h)

/-- The shift factor of one Gamma translate, as an element of the digamma field. -/
def gammaFactor (lam : Fin r → ℂ) (i : Fin r) : digammaField lam :=
  ⟨algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (RatFunc.X + RatFunc.C (lam i)),
    (digammaField lam).algebraMap_mem _⟩

theorem gammaFactor_ne_zero (lam : Fin r → ℂ) (i : Fin r) : gammaFactor lam i ≠ 0 := by
  intro h0
  have hval : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
      (RatFunc.X + RatFunc.C (lam i)) = 0 := congrArg Subtype.val h0
  have hne : (RatFunc.X + RatFunc.C (lam i)) ≠ 0 := by
    rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_add]
    exact RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero (lam i))
  exact hne ((algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
    (by rw [hval, map_zero]))


/-- Two polynomials in possibly infinitely many variables live in a common finite variable set,
indexed by `Fin n`. -/
theorem exists_fin_rename₂ {σ R : Type*} [CommSemiring R] (p q : MvPolynomial σ R) :
    ∃ (n : ℕ) (f : Fin n → σ) (_hf : Function.Injective f) (p' q' : MvPolynomial (Fin n) R),
      p = rename f p' ∧ q = rename f q' := by
  classical
  obtain ⟨s, p', q', hp, hq⟩ := MvPolynomial.exists_finset_rename₂ p q
  let n := Fintype.card { x // x ∈ s }
  let e := Fintype.equivFin { x // x ∈ s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective,
    rename e p', rename e q', ?_, ?_⟩
  · rw [hp, ← rename_rename, rename_rename e]
    simp
  · rw [hq, ← rename_rename, rename_rename e]
    simp

/-- **No Gamma-type multiplicative coboundary in the digamma field.** -/
theorem no_multiplicative_coboundary_digammaField (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    (u : digammaField lam) (hu : u ≠ 0) (mm : Fin r → ℤ) (i₀ : Fin r) (hmm : mm i₀ ≠ 0) :
    digammaFieldShift lam u ≠ u * ∏ i : Fin r, (gammaFactor lam i) ^ (mm i) := by
  classical
  intro heq
  set uu : meroField (Set.univ : Set ℂ) := (u : meroField (Set.univ : Set ℂ)) with huu
  have huune : uu ≠ 0 := by
    intro h0
    exact hu (Subtype.ext h0)
  -- the equation in the big field
  set iota : digammaField lam →+* meroField (Set.univ : Set ℂ) :=
    (digammaField lam).val.toRingHom with hiota
  have hcoeProd : iota (∏ i : Fin r, (gammaFactor lam i) ^ (mm i))
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (mm i)) := by
    rw [map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, map_zpow₀]
    rfl
  have hbig : addTranslationMeroEquiv 1 uu
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          (∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (mm i)) * uu := by
    have hval := congrArg iota heq
    rw [map_mul, hcoeProd] at hval
    rw [show addTranslationMeroEquiv 1 uu = iota (digammaFieldShift lam u) from rfl, hval,
      mul_comm]
    rfl
  -- present the element as a quotient of polynomials in the jets
  have humem : uu ∈ IntermediateField.adjoin (RatFunc ℂ) (Set.range (digammaJet lam)) := u.2
  obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp humem
  rw [Algebra.adjoin_range_eq_range_aeval] at ha hb
  obtain ⟨P, hP⟩ := ha
  obtain ⟨Q, hQ⟩ := hb
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hab
    exact huune hab
  have hane : a ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hab
    exact huune hab
  obtain ⟨M, idx, hinj, P', Q', hPP, hQQ⟩ := exists_fin_rename₂ P Q
  have hrenP : MvPolynomial.aeval (digammaJet lam) (rename idx P')
      = MvPolynomial.aeval (fun k => digammaJet lam (idx k)) P' := by
    rw [MvPolynomial.aeval_rename]
    rfl
  have hrenQ : MvPolynomial.aeval (digammaJet lam) (rename idx Q')
      = MvPolynomial.aeval (fun k => digammaJet lam (idx k)) Q' := by
    rw [MvPolynomial.aeval_rename]
    rfl
  have hPval : MvPolynomial.aeval (fun k => digammaJet lam (idx k)) P' = a := by
    rw [← hrenP, ← hPP]
    exact hP
  have hQval : MvPolynomial.aeval (fun k => digammaJet lam (idx k)) Q' = b := by
    rw [← hrenQ, ← hQQ]
    exact hQ
  have hP'ne : P' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPval
    exact hane hPval.symm
  have hQ'ne : Q' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQval
    exact hbne hQval.symm
  refine no_multiplicative_coboundary_digammaJets lam hincong idx hinj hP'ne hQ'ne mm i₀ hmm ?_
  rw [hPval, hQval, ← hab]
  exact hbig

/-- **Theorem B.**  The Gamma translates are algebraically independent over the field generated by
their logarithmic derivatives. -/
theorem algebraicIndependent_gammaShiftMero (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ)) :
    AlgebraicIndependent (digammaField lam) (fun i => gammaShiftMero (lam i)) := by
  classical
  refine algebraicIndependent_of_multiplicativeShift
    ((addTranslationMeroEquiv 1 : meroField (Set.univ : Set ℂ) ≃+*
      meroField (Set.univ : Set ℂ)) : meroField (Set.univ : Set ℂ) →+*
        meroField (Set.univ : Set ℂ))
    (digammaFieldShift lam) (digammaFieldShift_injective lam) (fun k => rfl)
    (fun i => gammaShiftMero (lam i)) (gammaFactor lam)
    (fun i => gammaShiftMero_ne_zero (lam i)) (gammaFactor_ne_zero lam) ?_ ?_
  · intro i
    exact addTranslationMeroEquiv_gammaShiftMero (lam i)
  · intro w mmv hw hmm
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin r, mmv i₀ ≠ 0 := by
      by_contra hnot
      refine hmm (funext fun i => ?_)
      by_contra hne
      exact hnot ⟨i, hne⟩
    exact no_multiplicative_coboundary_digammaField lam hincong w hw mmv i₀ hi₀

end

end GaloisForLFunctions.HTGeometry
