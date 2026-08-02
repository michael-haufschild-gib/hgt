import GaloisForLFunctions.RHTower.BVCoPoissonHellingerBetaResonanceTransmutation
import GaloisForLFunctions.RHTower.DeningerCalderonWittCompletedXiGreenIncidenceComparison
import GaloisForLFunctions.RHTower.DeningerCalderonWittGammaCoPoissonHodgeBoundaryComparison
import GaloisForLFunctions.RHTower.EulerPrimitivePolarizedHodgeBetaTransgression

/-!
# Hellinger--Beta residues in the Calderón--Witt relative boundary

The scalar Hellinger correction creates a nonzero reflected residue at every
half-lattice point `3/2 + 2 n`.  This file computes the class of that residue
on the actual Calderón--Witt source rather than declaring an abstract vector
landing.

There are two separate conclusions.

* The existing vector-valued Gamma transport is still diagonal in its
  head/tail polarization before Haar orientation.  In contrast, the
  odd-Hodge image of the elementary head source is genuinely transverse.
* Multiplying the canonical cross-prime incidence by a Hellinger residue
  gives a nonzero, source-readable actual incidence, but its relative
  Gamma/Hardy boundary class vanishes exactly at zero modular displacement.

Thus a fixed-witness vector lift does not repair the scalar resonance.  Any
successful source lift must leave both every fixed cross-prime line and, by
the independent finite-cell rigidity theorem, every finite canonical cell
span before taking a graph limit.
-/

namespace RHTower

noncomputable section

/-! ## Diagonal-polarization obstruction -/

/--
Before Haar orientation, the present Calderón--Witt Gamma transport has
equal head and tail profiles.  Its vector value lies in the diagonal
polarization even though its suspension-center coefficient is vector-valued.
-/
theorem deningerCalderonWittGammaPolarizedVectorTransport_head_eq_tail
    (a : ℝ)
    (s : deningerCalderonWittGlobalMilnorIncidence)
    (p q : Nat.Primes) (e f : ℕ) :
    (deningerCalderonWittGammaPolarizedVectorTransport
        a s p q e f).1 =
      (deningerCalderonWittGammaPolarizedVectorTransport
        a s p q e f).2 := by
  funext t
  change
    deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).1 t)
        p q s.1 =
      deningerCalderonWittWeightedNonlocalExterior
        ((xiGammaEulerPrimitivePolarizedExteriorFeature
          a (p, e) (q, f)).2 t)
        p q s.1
  rw [xiGammaEulerPrimitivePolarizedExteriorFeature_eq_smul_test]
  rfl

/--
The Hellinger--Beta source is not diagonal: at every positive source time,
the odd-Hodge image of the elementary head seed has unequal channels.
-/
theorem eulerPrimitiveBoundaryOddHodge_unitSeed_head_ne_tail
    {t : ℝ} (ht : 0 < t) :
    (eulerPrimitiveBoundaryOddHodge
        eulerPrimitiveBoundaryPolarizedUnitSeed).1 t ≠
      (eulerPrimitiveBoundaryOddHodge
        eulerPrimitiveBoundaryPolarizedUnitSeed).2 t := by
  simp only [eulerPrimitiveBoundaryOddHodge,
    eulerPrimitiveBoundaryPolarizedUnitSeed]
  have hq : (eulerPrimitiveBoundaryHodgeScale t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (eulerPrimitiveBoundaryHodgeScale_pos ht).ne'
  simp only [mul_zero, neg_div]
  exact (neg_ne_zero.mpr (div_ne_zero one_ne_zero hq)).symm

/-! ## Canonical incidence lift of every half-lattice residue -/

/--
Canonical fixed-cross-prime lift of the `n`th reflected Hellinger/co-Poisson
residue into the actual all-prime Milnor-incidence source.
-/
def hellingerBetaCalderonWittCrossPrimeResidue
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    deningerCalderonWittGlobalMilnorIncidence :=
  hellingerBetaReflectedResidue n •
    deningerCalderonWittCrossPrimeGammaWitness hpq

/-- The source-native normalized incidence coordinate recovers the analytic
Hellinger residue exactly. -/
@[simp]
theorem
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_hellingerBetaResidue
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate
        p q hpq (hellingerBetaCalderonWittCrossPrimeResidue hpq n) =
      hellingerBetaReflectedResidue n := by
  rw [hellingerBetaCalderonWittCrossPrimeResidue, map_smul,
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_witness]
  simp

/-- Every residue lift is a nonzero actual Calderón--Witt incidence. -/
theorem hellingerBetaCalderonWittCrossPrimeResidue_ne_zero
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) :
    hellingerBetaCalderonWittCrossPrimeResidue hpq n ≠ 0 := by
  intro hzero
  have hread := congrArg
    (deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate p q hpq)
    hzero
  rw [
    deningerCalderonWittCrossPrimeNormalizedIncidenceCoordinate_hellingerBetaResidue,
    map_zero] at hread
  exact hellingerBetaReflectedResidue_ne_zero n hread

/-!
## Exact admitted-sector and relative-boundary classification
-/

/--
The fixed-witness Hellinger residue is admitted exactly at zero modular
displacement.  Nonzero residue scaling cannot change submodule membership.
-/
theorem hellingerBetaCalderonWittCrossPrimeResidue_mem_admittedHodgeSector_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) (a : ℝ) :
    hellingerBetaCalderonWittCrossPrimeResidue hpq n ∈
        deningerCalderonWittGammaAdmittedHodgeSector a ↔
      a = 0 := by
  constructor
  · intro hmem
    have hinv :=
      (deningerCalderonWittGammaAdmittedHodgeSector a).smul_mem
        (hellingerBetaReflectedResidue n)⁻¹ hmem
    have hw :
        deningerCalderonWittCrossPrimeGammaWitness hpq ∈
          deningerCalderonWittGammaAdmittedHodgeSector a := by
      simpa only [hellingerBetaCalderonWittCrossPrimeResidue, smul_smul,
        inv_mul_cancel₀ (hellingerBetaReflectedResidue_ne_zero n), one_smul]
        using hinv
    exact
      (deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
        hpq a 0).mp hw
  · intro ha
    have hw :=
      (deningerCalderonWittCrossPrimeGammaWitness_mem_admittedHodgeSector_sameDepth_iff
        hpq a 0).mpr ha
    exact
      (deningerCalderonWittGammaAdmittedHodgeSector a).smul_mem
        (hellingerBetaReflectedResidue n) hw

/--
Exact degree-two relative-class computation: the canonical Gamma relative
boundary class of every Hellinger residue lift vanishes exactly at zero
modular displacement.
-/
theorem
    deningerCalderonWittGammaRelativeBoundaryClass_hellingerBetaResidue_eq_zero_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) (a : ℝ) :
    deningerCalderonWittGammaRelativeBoundaryClass a
        (hellingerBetaCalderonWittCrossPrimeResidue hpq n).1 = 0 ↔
      a = 0 := by
  rw [deningerCalderonWittGammaRelativeBoundaryClass_eq_zero_iff
    a (hellingerBetaCalderonWittCrossPrimeResidue hpq n).1
      (hellingerBetaCalderonWittCrossPrimeResidue hpq n).2]
  rw [deningerCalderonWittGlobalMilnorGreenRetraction_incidence]
  change hellingerBetaCalderonWittCrossPrimeResidue hpq n ∈
      deningerCalderonWittGammaAdmittedHodgeSector a ↔ a = 0
  exact
    hellingerBetaCalderonWittCrossPrimeResidue_mem_admittedHodgeSector_iff
      hpq n a

/--
The actual Gamma/Hardy reflection-odd coordinate of a residue lift is the
analytic residue times the physical reflection defect.
-/
theorem
    deningerCalderonWittGammaReflectionOddScalarTransport_hellingerBetaResidue
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) (a : ℝ) (e : ℕ) :
    deningerCalderonWittGammaReflectionOddScalarTransport a
        (hellingerBetaCalderonWittCrossPrimeResidue hpq n) p q e e =
      hellingerBetaReflectedResidue n *
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, e) (q, e) : ℂ) := by
  rw [hellingerBetaCalderonWittCrossPrimeResidue, map_smul]
  change hellingerBetaReflectedResidue n *
      deningerCalderonWittGammaReflectionOddScalarTransport a
        (deningerCalderonWittCrossPrimeGammaWitness hpq) p q e e = _
  rw [deningerCalderonWittGammaReflectionOddScalarTransport_crossPrimeWitness]

/--
The actual boundary coordinate of the residue lift vanishes exactly at zero
modular displacement; every off-critical displacement is detected.
-/
theorem
    deningerCalderonWittGammaReflectionOddScalarTransport_hellingerBetaResidue_eq_zero_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (n : ℕ) (a : ℝ) (e : ℕ) :
    deningerCalderonWittGammaReflectionOddScalarTransport a
        (hellingerBetaCalderonWittCrossPrimeResidue hpq n) p q e e = 0 ↔
      a = 0 := by
  rw [
    deningerCalderonWittGammaReflectionOddScalarTransport_hellingerBetaResidue
      hpq n a e]
  constructor
  · intro hzero
    have hfactor :
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, e) (q, e) : ℂ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left
        (hellingerBetaReflectedResidue_ne_zero n)
    have hreal :
        xiGammaEulerPrimitiveReflectionOddExterior
          a (p, e) (q, e) = 0 := by
      exact_mod_cast hfactor
    exact
      (xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
        a (p, e) (q, e)
          (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq e)).mp
        hreal
  · rintro rfl
    simp [xiGammaEulerPrimitiveReflectionOddExterior_zero]

end

end RHTower
