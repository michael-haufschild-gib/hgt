import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PadicAlgebraicResidue
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The residue field above a finite place in an algebraic closure of a
number field is an algebraic closure of the prime field. -/

noncomputable section

open IsLocalRing Polynomial

namespace GlobalTheory.TeichPlace

private theorem isAlgebraic_residue_of_isAlgebraic_rat {Ω : Type*} [Field Ω]
    [CharZero Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    [Algebra (ZMod p) (ResidueField A)] : Algebra.IsAlgebraic (ZMod p) (ResidueField A) := by
  constructor
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective z
  have ha : IsAlgebraic ℤ (a : Ω) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic (a : Ω))
  obtain ⟨f, hf, hfa⟩ := ha
  have hroot : aeval (a : Ω) f.primPart = 0 := aeval_primPart_eq_zero hf hfa
  have hA : aeval a f.primPart = 0 := by
    apply (IsFractionRing.injective A Ω)
    rw [map_zero]
    exact (aeval_algHom_apply (algebraMap A Ω).toIntAlgHom a f.primPart).symm.trans hroot
  refine ⟨f.primPart.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
  · intro he
    have hdvd : C (p : ℤ) ∣ f.primPart := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have h := congrArg (fun q : (ZMod p)[X] => q.coeff i) he
      simp only [coeff_map, coeff_zero, eq_intCast] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
    have hu := isPrimitive_primPart f _ hdvd
    rw [Int.isUnit_iff] at hu
    have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  · have hφ : (algebraMap (ZMod p) (ResidueField A)).comp (Int.castRingHom (ZMod p)) =
        algebraMap ℤ (ResidueField A) := RingHom.ext_int _ _
    have hred := aeval_algHom_apply (residue A).toIntAlgHom a f.primPart
    rw [hA, map_zero] at hred
    rw [aeval_def, eval₂_map, hφ]
    exact hred

/-- A valuation in residue characteristic p on an algebraically closed algebraic
extension of the rationals has residue field an algebraic closure of the prime field. -/
theorem nonempty_fbar_residueField_of_valuation {Ω : Type*} [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω)
    (p : ℕ) [Fact p.Prime] (hp : A.valuation (p : Ω) < 1) :
    Nonempty (ResidueField A ≃+* AlgebraicClosure (ZMod p)) := by
  have hzero : (p : ResidueField A) = 0 := by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff _).mpr (by simpa only [SubringClass.coe_natCast] using hp)
  letI : CharP (ResidueField A) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hzero
  letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ p
  letI : IsAlgClosure (ZMod p) (ResidueField A) :=
    ⟨isAlgClosed_residueField_valuationSubring A, isAlgebraic_residue_of_isAlgebraic_rat A p⟩
  exact ⟨(IsAlgClosure.equiv (ZMod p) (ResidueField A) (AlgebraicClosure (ZMod p))).toRingEquiv⟩

end GlobalTheory.TeichPlace
