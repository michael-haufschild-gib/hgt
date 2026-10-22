import GaloisForLFunctions.RHTower.Deninger.DeningerFrobeniusColimitSpace
import GaloisForLFunctions.RHTower.Deninger.DeningerGeneralizedDivisorSupport

/-!
# Generalized divisors on the `Spec ℤ` Frobenius colimit

This is the concrete, premise-free `Spec ℤ` specialization of Deninger's Proposition 11.7.
Integer residue evaluation is extended by zero on the character space. Its zero predicate is
proved invariant under every Frobenius transition, hence descends to the actual Frobenius colimit.
The descended zero locus is exactly the inverse image of the ordinary divisor on `Spec ℤ`.

For a rational prime, the theorem is connected to the existing Kummer infrastructure: the
generalized divisor is the inverse image of the prime's closed point and the stalk support of the
pulled-back residue sheaf. No `DeningerGeneralizedDivisorLaw` premise is used.
-/

open scoped SpecOfNotation

namespace RHTower

open AlgebraicGeometry
open DeningerCharacterSpace

abbrev DeningerSpecZCharacterSpace := DeningerCharacterSpace Spec(ℤ)

/-- Residue of an integer at a character point of `Spec ℤ`. -/
noncomputable def deningerSpecZCharacterResidue
    (n : ℤ) (P : DeningerSpecZCharacterSpace) :
    Spec(ℤ).residueField P.point :=
  (Scheme.Spec.residueFieldIso (.of ℤ) P.point).inv
    (algebraMap ℤ P.point.asIdeal.ResidueField n)

/-- Character evaluation extended by zero at zero. -/
noncomputable def deningerSpecZCharacterEvaluate
    (n : ℤ) (P : DeningerSpecZCharacterSpace) : ℂ := by
  classical
  exact if h : deningerSpecZCharacterResidue n P = 0 then 0
    else ((P.char (Units.mk0 (deningerSpecZCharacterResidue n P) h) : ℂˣ) : ℂ)

theorem deningerSpecZCharacterResidue_eq_zero_iff
    (n : ℤ) (P : DeningerSpecZCharacterSpace) :
    deningerSpecZCharacterResidue n P = 0 ↔ n ∈ P.point.asIdeal := by
  rw [deningerSpecZCharacterResidue]
  constructor
  · intro h
    apply (Ideal.algebraMap_residueField_eq_zero (I := P.point.asIdeal)).1
    apply (Scheme.Spec.residueFieldIso (.of ℤ) P.point).symm.commRingCatIsoToRingEquiv.injective
    simpa using h
  · intro h
    have hz : algebraMap ℤ P.point.asIdeal.ResidueField n = 0 :=
      (Ideal.algebraMap_residueField_eq_zero (I := P.point.asIdeal)).2 h
    simp [hz]

theorem deningerSpecZCharacterEvaluate_eq_zero_iff
    (n : ℤ) (P : DeningerSpecZCharacterSpace) :
    deningerSpecZCharacterEvaluate n P = 0 ↔ n ∈ P.point.asIdeal := by
  classical
  rw [deningerSpecZCharacterEvaluate]
  split_ifs with h
  · simpa [h] using deningerSpecZCharacterResidue_eq_zero_iff n P
  · constructor
    · intro hz
      exact False.elim ((Units.ne_zero _) hz)
    · intro hn
      exact False.elim (h ((deningerSpecZCharacterResidue_eq_zero_iff n P).2 hn))

theorem deningerSpecZCharacterEvaluate_frobenius_eq_zero_iff
    (n : ℤ) (q : ℕ) (P : DeningerSpecZCharacterSpace) :
    deningerSpecZCharacterEvaluate n (deningerCharacterFrobenius q P) = 0 ↔
      deningerSpecZCharacterEvaluate n P = 0 := by
  rw [deningerSpecZCharacterEvaluate_eq_zero_iff]
  rw [deningerSpecZCharacterEvaluate_eq_zero_iff]
  change n ∈ P.point.asIdeal ↔ n ∈ P.point.asIdeal
  rfl

/-- Evaluation vanishing on a staged source point. -/
def deningerSpecZStagedEvaluateZero
    (n : ℤ) (P : DeningerStagedCharacter Spec(ℤ)) : Prop :=
  deningerSpecZCharacterEvaluate n P.2 = 0

theorem deningerSpecZStagedEvaluateZero_respects
    (n : ℤ) {P Q : DeningerStagedCharacter Spec(ℤ)}
    (h : deningerFrobeniusRel P Q) :
    deningerSpecZStagedEvaluateZero n P = deningerSpecZStagedEvaluateZero n Q := by
  apply propext
  rw [deningerSpecZStagedEvaluateZero, deningerSpecZStagedEvaluateZero]
  rw [deningerSpecZCharacterEvaluate_eq_zero_iff]
  rw [deningerSpecZCharacterEvaluate_eq_zero_iff]
  obtain ⟨k, l, _, hF⟩ := h
  have hpoint : P.2.point = Q.2.point := by
    simpa [deningerCharacterFrobenius] using congrArg DeningerCharacterSpace.point hF
  rw [hpoint]

/-- Vanishing of the extended character evaluation on Deninger's exact Frobenius colimit. -/
def deningerSpecZFrobeniusColimitEvaluateZero
    (n : ℤ) : DeningerFrobeniusColimit Spec(ℤ) → Prop :=
  Quotient.lift (deningerSpecZStagedEvaluateZero n)
    (by
      intro P Q h
      exact deningerSpecZStagedEvaluateZero_respects n h)

@[simp]
theorem deningerSpecZFrobeniusColimitEvaluateZero_chart
    (n : ℤ) (q : ℕ+) (P : DeningerSpecZCharacterSpace) :
    deningerSpecZFrobeniusColimitEvaluateZero n (deningerColimitChart q P) ↔
      deningerSpecZCharacterEvaluate n P = 0 := by
  rfl

theorem deningerSpecZFrobeniusColimitEvaluateZero_iff
    (n : ℤ) (P : DeningerFrobeniusColimit Spec(ℤ)) :
    deningerSpecZFrobeniusColimitEvaluateZero n P ↔
      n ∈ (deningerColimitPr P).asIdeal := by
  obtain ⟨Q, rfl⟩ := deningerColimitChart_surjective P
  exact deningerSpecZCharacterEvaluate_eq_zero_iff n Q.2

/-- Generalized divisor defined from the actual descended character zero locus. -/
def deningerSpecZFrobeniusColimitGeneralizedDivisor (n : ℤ) :
    Set (DeningerFrobeniusColimit Spec(ℤ)) :=
  {P | deningerSpecZFrobeniusColimitEvaluateZero n P}

/-- Ordinary zero divisor of an integer on `Spec ℤ`. -/
def deningerSpecZIntegerZeroDivisor (n : ℤ) : Set Spec(ℤ) :=
  {x | n ∈ x.asIdeal}

/-- Arithmetic specialization of Deninger Proposition 11.7 on the exact Frobenius colimit. -/
theorem deningerSpecZFrobeniusColimitGeneralizedDivisor_eq_preimage
    (n : ℤ) :
    deningerSpecZFrobeniusColimitGeneralizedDivisor n =
      deningerColimitPr ⁻¹' deningerSpecZIntegerZeroDivisor n := by
  ext P
  exact deningerSpecZFrobeniusColimitEvaluateZero_iff n P

/-- The exact Frobenius colimit, regarded as a topological source. -/
noncomputable abbrev DeningerSpecZFrobeniusColimitTop : TopCat :=
  TopCat.of (DeningerFrobeniusColimit Spec(ℤ))

theorem continuous_deningerSpecZFrobeniusColimitPr :
    Continuous (deningerColimitPr (X := Spec(ℤ))) := by
  rw [(isQuotientMap_quotient_mk'
    (s := deningerFrobeniusSetoid Spec(ℤ))).continuous_iff]
  exact continuous_sigma fun _ => continuous_deningerCharacterPr

/-- Continuous arithmetic projection from the exact Frobenius colimit. -/
noncomputable def deningerSpecZFrobeniusColimitPrTop :
    DeningerSpecZFrobeniusColimitTop ⟶ deningerArithBase :=
  TopCat.ofHom
    ⟨deningerColimitPr, continuous_deningerSpecZFrobeniusColimitPr⟩

/-- The ordinary zero divisor of a rational prime is its unique closed point. -/
theorem deningerSpecZIntegerZeroDivisor_prime (p : Nat.Primes) :
    deningerSpecZIntegerZeroDivisor ((p : ℕ) : ℤ) = {deningerClosedPt p} := by
  have hp : Prime ((p : ℕ) : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using p.2
  letI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := hp.isMaximal_span_singleton
  rw [deningerSpecZIntegerZeroDivisor]
  have hzero := PrimeSpectrum.zeroLocus_eq_singleton
    (Ideal.span {((p : ℕ) : ℤ)})
  have hpt :
      (⟨Ideal.span {((p : ℕ) : ℤ)}, inferInstance⟩ : PrimeSpectrum ℤ) =
        deningerClosedPt p :=
    PrimeSpectrum.ext rfl
  calc
    {x : PrimeSpectrum ℤ | ((p : ℕ) : ℤ) ∈ x.asIdeal} =
        PrimeSpectrum.zeroLocus (Ideal.span {((p : ℕ) : ℤ)}) := by
      ext x
      simp [PrimeSpectrum.mem_zeroLocus]
    _ = {⟨Ideal.span {((p : ℕ) : ℤ)}, inferInstance⟩} := hzero
    _ = {deningerClosedPt p} := congrArg (fun x => ({x} : Set (PrimeSpectrum ℤ))) hpt

/-- Proposition 11.7 for a prime, with no generalized-divisor-law premise. -/
theorem deningerSpecZFrobeniusColimitGeneralizedDivisor_prime
    (p : Nat.Primes) :
    deningerSpecZFrobeniusColimitGeneralizedDivisor ((p : ℕ) : ℤ) =
      deningerPullbackSupport deningerSpecZFrobeniusColimitPrTop p := by
  rw [deningerSpecZFrobeniusColimitGeneralizedDivisor_eq_preimage]
  rw [deningerSpecZIntegerZeroDivisor_prime]
  rfl

/-- The prime generalized divisor is exactly support of the pulled-back Kummer residue sheaf,
unconditionally for the concrete Frobenius-colimit source. -/
theorem deningerSpecZFrobeniusColimitGeneralizedDivisor_prime_eq_stalkSupport
    (p : Nat.Primes) :
    deningerSpecZFrobeniusColimitGeneralizedDivisor ((p : ℕ) : ℤ) =
      deningerStalkSupport
        ((TopCat.Sheaf.pullback AddCommGrpCat.{0} deningerSpecZFrobeniusColimitPrTop).obj
          (deningerResidueAddSheaf {p} ℤ)) := by
  rw [deningerSpecZFrobeniusColimitGeneralizedDivisor_prime]
  exact (deningerPullbackResidue_stalkSupport deningerSpecZFrobeniusColimitPrTop p).symm

end RHTower
