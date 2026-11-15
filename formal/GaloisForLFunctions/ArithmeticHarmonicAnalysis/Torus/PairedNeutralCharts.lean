import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralLaurent

/-!
# All oriented Laurent charts jointly detect a paired neutral quotient

Choose, independently for each pair, whether `zᵢ` or `wᵢ` is represented
by an invertible Laurent variable. The other variable carries the neutral
coefficient `hᵢ`. Each choice defines a ring map from the actual paired
quotient into the Laurent ring over the neutral quotient.

At weight `q`, choose the orientation matching its signs. The forced neutral
factor is then one, so that chart recovers the exact relative weight
coefficient. Consequently the product of all oriented chart maps is injective
for every neutral ideal, including nonreduced quotients and the unit ideal.
Individual charts need not be injective.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open scoped PairedNeutral
variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- In each pair, exactly one variable carries the neutral coefficient. -/
def pairedChartCoordinates (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    (ι ⊕ ι) → NeutralLaurent K J :=
  Sum.elim (fun i => AddMonoidAlgebra.single (Pi.single i 1)
      (if ε i then 1 else Ideal.Quotient.mk J (X i)))
    (fun i => AddMonoidAlgebra.single (-Pi.single i 1)
      (if ε i then Ideal.Quotient.mk J (X i) else 1))

/-- Laurent substitution for a specified orientation of every coordinate pair. -/
def pairedChartMap (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    MvPolynomial (ι ⊕ ι) K →+* NeutralLaurent K J :=
  eval₂Hom (pairedLaurentConstant K J) (pairedChartCoordinates K J ε)

private theorem prod_chart_single {κ A G : Type*} [CommRing A] [AddCommMonoid G]
    (s : Finset κ) (q : κ → G) (c : κ → A) :
    ∏ i ∈ s, AddMonoidAlgebra.single (q i) (c i) =
      AddMonoidAlgebra.single (∑ i ∈ s, q i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, AddMonoidAlgebra.single_mul_single]

/-- An oriented chart preserves the weight and records the unchosen variable powers in its coefficient. -/
theorem pairedChartMap_monomial (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (d : (ι ⊕ ι) →₀ ℕ) (c : K) :
    pairedChartMap K J ε (monomial d c) = AddMonoidAlgebra.single (pairedWeight d)
      (Ideal.Quotient.mk J (C c) *
        ((∏ i, (if ε i then 1 else Ideal.Quotient.mk J (X i)) ^ d (Sum.inl i)) *
          ∏ i, (if ε i then Ideal.Quotient.mk J (X i) else 1) ^ d (Sum.inr i))) := by
  rw [pairedChartMap, eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (by intro i; exact pow_zero _), Fintype.prod_sum_type]
  simp only [pairedChartCoordinates, Sum.elim_inl, Sum.elim_inr, AddMonoidAlgebra.single_pow]
  rw [prod_chart_single, prod_chart_single]
  change AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J (C c)) * _ = _
  rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single, zero_add]
  congr 1
  funext i
  simp [pairedWeight, Pi.single_apply, Finset.sum_apply, nsmul_eq_mul, mul_ite, sub_eq_add_neg]

/-- The neutral powers forced by the weight and the chosen orientation. -/
def orientedNeutralFactor (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) (q : ι → ℤ) :
    MvPolynomial ι K ⧸ J :=
  (∏ i, (if ε i then 1 else Ideal.Quotient.mk J (X i)) ^ (q i).toNat) *
    ∏ i, (if ε i then Ideal.Quotient.mk J (X i) else 1) ^ (-q i).toNat

/-- A minimal weight monomial has one explicitly determined Laurent coefficient. -/
theorem pairedChartMap_minimal (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) (q : ι → ℤ) :
    pairedChartMap K J ε (minimalPairedMonomial K q) =
      AddMonoidAlgebra.single q (orientedNeutralFactor K J ε q) := by
  rw [minimalPairedMonomial, pairedChartMap_monomial, pairedWeight_normal]
  simp [orientedNeutralFactor]

omit [Fintype ι] in
/-- Every orientation sends neutral polynomials to the same quotient constants. -/
theorem pairedChartMap_invariant (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (f : MvPolynomial ι K) :
    pairedChartMap K J ε (invariantSubstitution K f) =
      AddMonoidAlgebra.single 0 (Ideal.Quotient.mk J f) := by
  have he : (pairedChartMap K J ε).comp (invariantSubstitution K) =
      AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk J) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [pairedChartMap, invariantSubstitution, pairedLaurentConstant]
    · intro i
      cases h : ε i <;>
        simp [pairedChartMap, invariantSubstitution, pairedChartCoordinates, h,
          AddMonoidAlgebra.single_mul_single]
  exact DFunLike.congr_fun he f

/-- The chart acts diagonally on the relative weight expansion. -/
theorem pairedChartMap_assembly_coeff (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (c : (ι → ℤ) →₀ MvPolynomial ι K) (q : ι → ℤ) :
    (pairedChartMap K J ε (pairedNeutralAssembly K c)).coeff q =
      Ideal.Quotient.mk J (c q) * orientedNeutralFactor K J ε q := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, hc, hd, Finsupp.add_apply, add_mul]
  | single r f =>
    rw [pairedNeutralAssembly, Finsupp.linearCombination_single, pairedNeutral_smul,
      map_mul, pairedChartMap_invariant, pairedChartMap_minimal,
      AddMonoidAlgebra.single_mul_single, zero_add]
    by_cases h : r = q <;> simp [h, AddMonoidAlgebra.coeff_single]

/-- Every chart coefficient is the extracted neutral coefficient times its orientation factor. -/
theorem pairedChartMap_coeff (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (P : MvPolynomial (ι ⊕ ι) K) (q : ι → ℤ) :
    (pairedChartMap K J ε P).coeff q =
      Ideal.Quotient.mk J (pairedWeightExtraction K q P) * orientedNeutralFactor K J ε q := by
  have h := pairedChartMap_assembly_coeff K J ε (pairedNeutralEquiv K P) q
  have he : pairedNeutralAssembly K (pairedNeutralEquiv K P) = P :=
    (pairedNeutralEquiv K).symm_apply_apply P
  rw [he, pairedNeutralEquiv_apply] at h
  exact h

/-- All substituted neutral relations vanish in every oriented chart. -/
theorem pairedChartMap_annihilates (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (P : MvPolynomial (ι ⊕ ι) K) (hP : P ∈ J.map (invariantSubstitution K)) :
    pairedChartMap K J ε P = 0 := by
  ext q
  rw [pairedChartMap_coeff, AddMonoidAlgebra.coeff_zero,
    (Ideal.Quotient.eq_zero_iff_mem).mpr (pairedWeightExtraction_mem K q J hP), zero_mul]
  rfl

/-- The oriented chart on the actual paired ideal quotient. -/
def pairedQuotientChartMap (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool) :
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) →+* NeutralLaurent K J :=
  Ideal.Quotient.lift _ (pairedChartMap K J ε) (pairedChartMap_annihilates K J ε)

/-- Chart coefficients are the relative quotient coordinates multiplied by the forced factor. -/
theorem pairedQuotientChartMap_coeff (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) (q : ι → ℤ) :
    (pairedQuotientChartMap K J ε x).coeff q =
      pairedNeutralQuotientEquiv K J x q * orientedNeutralFactor K J ε q := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [pairedNeutralQuotientEquiv_mk]
  exact pairedChartMap_coeff K J ε P q

/-- Orient each pair toward the sign of the requested weight. -/
def weightOrientation (q : ι → ℤ) : ι → Bool := fun i => decide (0 ≤ q i)

/-- The orientation matching a weight introduces no neutral factor. -/
theorem orientedNeutralFactor_weightOrientation (J : Ideal (MvPolynomial ι K)) (q : ι → ℤ) :
    orientedNeutralFactor K J (weightOrientation q) q = 1 := by
  have hp : (∏ i, (if weightOrientation q i then 1 else Ideal.Quotient.mk J (X i)) ^
      (q i).toNat) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    by_cases h : 0 ≤ q i
    · simp [weightOrientation, h]
    · have hz : (q i).toNat = 0 := by omega
      simp [weightOrientation, h, hz]
  have hn : (∏ i, (if weightOrientation q i then Ideal.Quotient.mk J (X i) else 1) ^
      (-q i).toNat) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    by_cases h : 0 ≤ q i
    · have hz : (-q i).toNat = 0 := by omega
      simp [weightOrientation, h, hz]
    · simp [weightOrientation, h]
  exact (congrArg₂ (· * ·) hp hn).trans (one_mul 1)

/-- A chart matching the signs recovers an arbitrary weight coefficient exactly. -/
theorem pairedQuotientChartMap_recovers (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) (q : ι → ℤ) :
    (pairedQuotientChartMap K J (weightOrientation q) x).coeff q =
      pairedNeutralQuotientEquiv K J x q := by
  rw [pairedQuotientChartMap_coeff, orientedNeutralFactor_weightOrientation, mul_one]

/-- Map the quotient to the product of all oriented Laurent rings. -/
def pairedChartFamilyMap (J : Ideal (MvPolynomial ι K)) :
    (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) →+*
      ((ι → Bool) → NeutralLaurent K J) := RingHom.pi (pairedQuotientChartMap K J)

/-- The full family of oriented Laurent charts is faithful for every neutral ideal. -/
theorem pairedChartFamilyMap_injective (J : Ideal (MvPolynomial ι K)) :
    Function.Injective (pairedChartFamilyMap K J) := by
  intro x y h
  apply (pairedNeutralQuotientEquiv K J).injective
  ext q
  have he := congrArg (fun f : (ι → Bool) → NeutralLaurent K J =>
    (f (weightOrientation q)).coeff q) h
  change (pairedQuotientChartMap K J (weightOrientation q) x).coeff q =
    (pairedQuotientChartMap K J (weightOrientation q) y).coeff q at he
  simpa only [pairedQuotientChartMap_recovers] using he

/-- An element vanishes precisely when every oriented Laurent image vanishes. -/
theorem pairedQuotient_eq_zero_iff_charts (J : Ideal (MvPolynomial ι K))
    (x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :
    x = 0 ↔ ∀ ε, pairedQuotientChartMap K J ε x = 0 := by
  constructor
  · rintro rfl ε
    exact map_zero _
  · intro h
    apply pairedChartFamilyMap_injective K J
    ext ε q
    change (pairedQuotientChartMap K J ε x).coeff q =
      (pairedQuotientChartMap K J ε 0).coeff q
    rw [h ε, map_zero]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedQuotientChartMap_recovers
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedChartFamilyMap_injective
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedQuotient_eq_zero_iff_charts
