import GaloisForLFunctions.RHTower.CCMRationalAdelicHaarMellinBoundaryLaw
import GaloisForLFunctions.RHTower.CCMRationalAdelicClosedNonunitalStrongRealLefschetz

/-!
# Literal closed CCM parity obstruction and Clifford comparison

The exact Definition 4.10 recipient is nonzero by the Haar--Mellin boundary
law.  Its descended Lefschetz translations are Real-even and invertible.
Consequently no anti-Real realized Chern character can equal an untwisted
CCM Lefschetz correspondence.  The maximal type-correct comparison is the
literal equality with its Clifford transgression, `i L`.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection
private abbrev Relative :=
  CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule
private abbrev RelativeKReal :=
  ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal

/-- Arithmetic nonzero class used to detect every descended Lefschetz
translation. -/
def ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness :
    Relative.simplicial.degree 0 :=
  (CCMRationalAdelicClosedNonunitalStrongRestrictionRange 0).mkQ
    ccmRationalNonunitalLogGaussianStrongChain

theorem ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness_ne_zero :
    ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness ≠ 0 :=
  ccmRationalAdelicClosedNonunitalStrong_logGaussian_ne_zero

/-- Every literal closed CCM Lefschetz translation is nonzero. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_degreeZero_nonzero
    (c : Section) :
    (ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
        (.op (.mk 0))
        ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness ≠ 0 := by
  intro hzero
  have hleft :=
    ccmRationalAdelicClosedNonunitalStrongLefschetz_leftInverse_degree
      c 0 ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness
  rw [hzero, map_zero] at hleft
  exact ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness_ne_zero
    hleft.symm

/-- **Exact-recipient parity no-go.** No nonzero literal closed CCM
Lefschetz correspondence has anti-Real naturality. -/
theorem ccmRationalAdelicClosedNonunitalStrongLefschetz_not_antiReal
    (c : Section) :
    ¬ ∀ n (x : Relative.simplicial.degree n),
      (RelativeKReal.real n).sigma
          ((ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
            (.op (.mk n)) x) =
        -(ccmRationalAdelicClosedNonunitalStrongLefschetz c).simplicial.app
          (.op (.mk n)) ((RelativeKReal.real n).sigma x) := by
  intro hanti
  have hzero := CyclicModule.KRealHom.degree_eq_zero_of_anti
    (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal c)
    hanti 0 ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness
  exact
    ccmRationalAdelicClosedNonunitalStrongLefschetz_degreeZero_nonzero c hzero

/-- Scalar classification on the actual closed CCM recipient: `z L_c` is
anti-Real exactly when `conj z = -z`. -/
theorem
    ccmRationalAdelicClosedNonunitalStrongLefschetz_smul_isAnti_iff_star_eq_neg
    (c : Section) (z : ℂ) :
    (∀ n (x : Relative.simplicial.degree n),
      (RelativeKReal.real n).sigma
          (((ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul z).simplicial.app
            (.op (.mk n)) x) =
        -(((ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul z).simplicial.app
          (.op (.mk n)) ((RelativeKReal.real n).sigma x))) ↔
      (starRingEnd ℂ) z = -z := by
  exact CyclicModule.KRealHom.smul_isAnti_iff_star_eq_neg
    (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal c)
    ⟨0, ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness,
      ccmRationalAdelicClosedNonunitalStrongLefschetz_degreeZero_nonzero c⟩ z

/-- No anti-Real realized character can equal the untwisted, Real-even CCM
Lefschetz correspondence on the literal closed quotient. -/
theorem ccmRationalAdelicClosedNonunitalStrong_no_antiRealCharacter_eq_lefschetz
    (c : Section)
    (χ : CyclicModule.KRealAntiHom RelativeKReal RelativeKReal) :
    χ.toHom ≠ ccmRationalAdelicClosedNonunitalStrongLefschetz c := by
  intro hχ
  apply ccmRationalAdelicClosedNonunitalStrongLefschetz_not_antiReal c
  intro n x
  rw [← hχ]
  exact χ.real_antinaturality n x

/-- Theory-independent negative P2 statement.  For any candidate bivariant
theory whose realized Chern characters are anti-Real cyclic morphisms, no
class realizes to the untwisted CCM Lefschetz correspondence. -/
theorem
    ccmRationalAdelicClosedNonunitalStrong_no_bivariantChernRealization_eq_lefschetz
    {BivariantClass : Type*}
    (realizedChern : BivariantClass →
      CyclicModule.KRealAntiHom RelativeKReal RelativeKReal)
    (c : Section) :
    ¬∃ κ : BivariantClass,
      (realizedChern κ).toHom =
        ccmRationalAdelicClosedNonunitalStrongLefschetz c := by
  rintro ⟨κ, hκ⟩
  exact
    ccmRationalAdelicClosedNonunitalStrong_no_antiRealCharacter_eq_lefschetz
      c (realizedChern κ) hκ

/-- The surviving comparison is literal equality: the closed CCM Clifford
transgression is `i` times the descended Lefschetz correspondence. -/
theorem
    ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_eq_i_lefschetz
    (c : Section) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordTransgression c).toHom =
      (ccmRationalAdelicClosedNonunitalStrongLefschetz c).smul Complex.I :=
  rfl

/-- At identity, the exact-recipient survivor is a genuine nonzero
Clifford generator. -/
theorem
    ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_one_nonzero :
    (ccmRationalAdelicClosedNonunitalStrongCliffordTransgression 1).toHom.simplicial.app
        (.op (.mk 0))
        ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness ≠ 0 := by
  change Complex.I •
      (ccmRationalAdelicClosedNonunitalStrongLefschetz 1).simplicial.app
        (.op (.mk 0))
          ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness ≠ 0
  rw [ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree]
  exact smul_ne_zero Complex.I_ne_zero
    ccmRationalAdelicClosedNonunitalStrongCyclicNonzeroWitness_ne_zero

end GaloisForLFunctions.RHTower
