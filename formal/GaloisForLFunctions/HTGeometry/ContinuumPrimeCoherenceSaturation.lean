import GaloisForLFunctions.HTGeometry.PrimeSparseCoherenceSaturation
import GaloisForLFunctions.HTGeometry.DifferentialIndependentFieldUniversality
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Continuum prime coherence saturation

The same sparse prime embedding supports the entire family indexed by infinite
Boolean sequences.  Finiteness of polynomial support reduces global
differential independence to the already proved finite tail matroid.  The
generated differential field is the rational function field on the complete
jet family, so its transcendence degree is exactly the continuum.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The continuum prefix family transported to sparse prime coordinates around
an arbitrary common base orientation. -/
def continuumSparsePrimeOrientation (base : Nat.Primes → Bool)
    (e : PrefixFunctionCoordinate ↪ Nat.Primes) (x : ℕ → Bool) :
    Nat.Primes → Bool :=
  basedSparsePrefixOrientation base e x

/-- The entire continuum family, with every nonnegative-integer shift, is
differentially independent over the finite-prime rational coefficient field. -/
theorem continuumSparsePrimeNaturalShiftPalette_differentialIndependent
    (base : Nat.Primes → Bool) (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun xa : (ℕ → Bool) × ℕ =>
        signedPrimeNaturalShiftPalette
          (continuumSparsePrimeOrientation base e xa.1) xa.2) := by
  classical
  unfold GaloisForLFunctions.DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let S : Set (ℕ → Bool) :=
    (fun z : ((ℕ → Bool) × ℕ) × ℕ => z.1.1) '' t
  have hS : S.Finite := ht.image _
  letI : Fintype S := hS.fintype
  cases isEmpty_or_nonempty S with
  | inl hEmpty =>
      letI : IsEmpty S := hEmpty
      have htEmpty : IsEmpty t := ⟨fun z => by
        have hzS : z.1.1.1 ∈ S := ⟨z.1, z.2, rfl⟩
        exact isEmptyElim (⟨z.1.1.1, hzS⟩ : S)⟩
      letI : IsEmpty t := htEmpty
      exact algebraicIndependent_empty_type
  | inr hNonempty =>
      letI : Nonempty S := hNonempty
      let epsilon : S → Nat.Primes → Bool :=
        fun s => continuumSparsePrimeOrientation base e s.1
      have htail : PrimeOrientationTailIndependent epsilon := by
        apply basedSparsePrefixOrientation_tailIndependent base e
          (fun s : S => s.1)
        exact Subtype.val_injective
      have hdiff :=
        (signedPrimeNaturalShiftPalette_differentialIndependent_iff epsilon).2 htail
      unfold GaloisForLFunctions.DifferentialIndependent at hdiff
      let f : t → (S × ℕ) × ℕ := fun z =>
        ((⟨z.1.1.1, ⟨z.1, z.2, rfl⟩⟩, z.1.1.2), z.1.2)
      have hf : Function.Injective f := by
        intro z w hzw
        apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext
          · exact congrArg (fun u : (S × ℕ) × ℕ => u.1.1.1) hzw
          · exact congrArg (fun u : (S × ℕ) × ℕ => u.1.2) hzw
        · exact congrArg (fun u : (S × ℕ) × ℕ => u.2) hzw
      have hsub := hdiff.comp f hf
      simpa only [Function.comp_apply, f, epsilon,
        continuumSparsePrimeOrientation] using! hsub

/-- Infinite Boolean sequences have exactly continuum cardinality. -/
theorem mk_boolSequence_eq_continuum :
    Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat]
  rw [Cardinal.lift_id, Cardinal.lift_id]
  rfl

/-- The unshifted continuum family is already differentially independent. -/
theorem continuumSparsePrimeUnshifted_differentialIndependent
    (base : Nat.Primes → Bool) (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun x : ℕ → Bool =>
        signedPrimeNaturalShiftPalette (continuumSparsePrimeOrientation base e x) 0) := by
  have h := continuumSparsePrimeNaturalShiftPalette_differentialIndependent base e
  exact h.comp (fun x : ℕ → Bool => (x, 0)) (by
    intro x y hxy
    exact congrArg Prod.fst hxy)

/-- The rational function field on a Boolean-sequence-by-jet family has
transcendence degree continuum. -/
theorem trdeg_fractionRing_mvPolynomial_boolSequence_nat :
    Algebra.trdeg finitePrimeRationalCoefficientField
      (FractionRing (MvPolynomial ((ℕ → Bool) × ℕ)
        finitePrimeRationalCoefficientField)) = Cardinal.continuum := by
  let P := MvPolynomial ((ℕ → Bool) × ℕ)
    finitePrimeRationalCoefficientField
  let L := FractionRing P
  haveI : Algebra.IsAlgebraic P L :=
    IsLocalization.isAlgebraic L (nonZeroDivisors P)
  have h := trdeg_add_eq finitePrimeRationalCoefficientField P (A := L)
  have hzero : Algebra.trdeg P L = 0 := trdeg_eq_zero
  rw [hzero, add_zero] at h
  change Algebra.trdeg finitePrimeRationalCoefficientField L = Cardinal.continuum
  rw [← h]
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_prod,
    mk_boolSequence_eq_continuum, Cardinal.mk_nat, Cardinal.lift_id,
    Cardinal.lift_id, Cardinal.continuum_mul_aleph0]

/-- The differential field generated by the unshifted continuum family has
exact differential-transcendence degree continuum, computed as the ordinary
transcendence degree of its complete jet field. -/
theorem continuumSparsePrimeUnshifted_differentialAdjoin_trdeg
    (base : Nat.Primes → Bool) (e : PrefixFunctionCoordinate ↪ Nat.Primes) :
    Algebra.trdeg finitePrimeRationalCoefficientField
      (GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range fun x : ℕ → Bool =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation base e x) 0)) = Cardinal.continuum := by
  let x : (ℕ → Bool) → arithmeticFunctionRationalCoordinateField := fun z =>
    signedPrimeNaturalShiftPalette (continuumSparsePrimeOrientation base e z) 0
  have hx : GaloisForLFunctions.DifferentialIndependent
      finitePrimeRationalCoefficientField x :=
    continuumSparsePrimeUnshifted_differentialIndependent base e
  let E := GaloisForLFunctions.differentialIndependentAdjoinParametrization x hx
  change Algebra.trdeg finitePrimeRationalCoefficientField
      (GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
        (Set.range x)) = Cardinal.continuum
  rw [← E.trdeg_eq]
  exact trdeg_fractionRing_mvPolynomial_boolSequence_nat

/-- **Continuum-rank prime coherence saturation.**  One sparse embedding works
simultaneously for every infinite Boolean sequence.  The full natural-shift
palette is differentially independent, the unshifted differential compositum
has transcendence degree continuum, and every member and pair lies inside the
requested coherence budget. -/
theorem exists_continuumPrimeCoherenceLocalDifferentialSaturation
    (sigma eta : ℝ) (hsigma : 0 < sigma) (heta : 0 < eta)
    (base : Nat.Primes → Bool) :
    ∃ e : PrefixFunctionCoordinate ↪ Nat.Primes,
      GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (fun xa : (ℕ → Bool) × ℕ =>
          signedPrimeNaturalShiftPalette
            (continuumSparsePrimeOrientation base e xa.1) xa.2) ∧
      Algebra.trdeg finitePrimeRationalCoefficientField
        (GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range fun x : ℕ → Bool =>
            signedPrimeNaturalShiftPalette
              (continuumSparsePrimeOrientation base e x) 0)) = Cardinal.continuum ∧
      (∀ x, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation base e x) base < eta ^ (2 : ℕ)) ∧
      ∀ x y, weightedOrientationDistanceSq (primeCoherenceWeight sigma)
        (continuumSparsePrimeOrientation base e x)
        (continuumSparsePrimeOrientation base e y) < eta ^ (2 : ℕ) := by
  have hB : 0 < eta ^ (2 : ℕ) := sq_pos_of_pos heta
  obtain ⟨e, hsum, hbudget⟩ :=
    exists_sparsePrefixEmbedding_of_cofinally_small
      (primeCoherenceWeight sigma) (eta ^ (2 : ℕ)) hB
      (primeCoherenceWeight_cofinally_small sigma hsigma)
  refine ⟨e, continuumSparsePrimeNaturalShiftPalette_differentialIndependent base e,
    continuumSparsePrimeUnshifted_differentialAdjoin_trdeg base e, ?_, ?_⟩
  · intro x
    exact basedSparsePrefixOrientation_distance_base_lt base e
      (primeCoherenceWeight sigma) x (eta ^ (2 : ℕ)) hsum hbudget
  · intro x y
    exact basedSparsePrefixOrientation_pair_distance_lt base e
      (primeCoherenceWeight sigma) x y (eta ^ (2 : ℕ)) hsum hbudget

end

end GaloisForLFunctions.HTGeometry
