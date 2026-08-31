import GaloisForLFunctions.RHTower.SourceGammaChannelResolvedNaturalityNoGo
import GaloisForLFunctions.HTGeometry.HermitianConeStrictConvexity

/-!
# Positive Hermitian scalarization cannot select the shared Ward wall

The channel-resolved prime--Gamma source reporter has genuine prime-two and prime-three boundary
outputs `(0,d(t))` and `(-d(t),0)`, where `d(t)=2^(-t)-3^(-t)`.  This file classifies every fixed
positive-semidefinite Hermitian scalarization of those two channels.

For an arbitrary complex `2 x 2` positive-semidefinite matrix `A`, the sum of its two literal
source-boundary energies is exactly

`(Re A_00 + Re A_11) * |d(t)|^2`.

Off-diagonal channel mixing drops out because the two genuine source boundaries occupy opposite
coordinate axes.  If `A` is nonzero, positivity makes its diagonal trace strictly positive, so the
energy vanishes exactly at `t=0`.  If `A=0`, the scalarization is blind at every grade.

On actual Xi support, universal zero energy for every nonzero fixed positive channel metric is
therefore equivalent both to RH and to the already unified HB/FZZ-P/PW-B/RBH Ward endpoint.  Thus
fixed positive finite-channel postprocessing is a receiver, not an upstream producer.  The sharp
survivor is source dynamics forcing the cross-prime leak itself to vanish.

`[NEW] [SHARED-WARD ROUTE-CLASS NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Matrix
open scoped BigOperators Matrix ComplexOrder

namespace RHTower

noncomputable section

/-- Coordinate vector of the two retained prime-labelled channels. -/
def primeGammaTwoChannelVector (z : PrimeGammaTwoChannel) : Fin 2 → ℂ :=
  ![z.1, z.2]

/-- Real Hermitian energy of one resolved two-channel source output. -/
def primeGammaTwoChannelHermitianEnergy
    (A : Matrix (Fin 2) (Fin 2) ℂ) (z : PrimeGammaTwoChannel) : ℝ :=
  (star (primeGammaTwoChannelVector z) ⬝ᵥ
    A *ᵥ primeGammaTwoChannelVector z).re

/-- A positive Hermitian scalarizer restricted to the first coordinate axis. -/
theorem primeGammaTwoChannelHermitianEnergy_left
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (z : ℂ) :
    primeGammaTwoChannelHermitianEnergy A (z, 0) =
      (A 0 0).re * Complex.normSq z := by
  rw [show primeGammaTwoChannelHermitianEnergy A (z, 0) =
      (star z * (A 0 0 * z)).re by
    rw [primeGammaTwoChannelHermitianEnergy]
    have hv : primeGammaTwoChannelVector (z, 0) = ![z, 0] := rfl
    have hs : star (![z, 0] : Fin 2 → ℂ) = ![star z, 0] := by
      funext i
      fin_cases i <;> simp
    rw [hv, hs]
    simp]
  have hdiag :=
    GaloisForLFunctions.HTGeometry.posSemidef_diag_nonneg hA (0 : Fin 2)
  have him : (A 0 0).im = 0 := by
    simpa using (Complex.le_def.1 hdiag).2.symm
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, him]
  ring

/-- A positive Hermitian scalarizer restricted to the second coordinate axis. -/
theorem primeGammaTwoChannelHermitianEnergy_right
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (z : ℂ) :
    primeGammaTwoChannelHermitianEnergy A (0, z) =
      (A 1 1).re * Complex.normSq z := by
  rw [show primeGammaTwoChannelHermitianEnergy A (0, z) =
      (star z * (A 1 1 * z)).re by
    rw [primeGammaTwoChannelHermitianEnergy]
    have hv : primeGammaTwoChannelVector (0, z) = ![0, z] := rfl
    have hs : star (![0, z] : Fin 2 → ℂ) = ![0, star z] := by
      funext i
      fin_cases i <;> simp
    rw [hv, hs]
    simp]
  have hdiag :=
    GaloisForLFunctions.HTGeometry.posSemidef_diag_nonneg hA (1 : Fin 2)
  have him : (A 1 1).im = 0 := by
    simpa using (Complex.le_def.1 hdiag).2.symm
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, him]
  ring

/-- A nonzero positive-semidefinite `2 x 2` matrix has positive real diagonal trace.  The proof is
elementary kernel rigidity: a zero diagonal quadratic value kills the corresponding column. -/
theorem posSemidef_two_diag_re_sum_pos_of_ne_zero
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < (A 0 0).re + (A 1 1).re := by
  have h00 :=
    GaloisForLFunctions.HTGeometry.posSemidef_diag_nonneg hA (0 : Fin 2)
  have h11 :=
    GaloisForLFunctions.HTGeometry.posSemidef_diag_nonneg hA (1 : Fin 2)
  have h00re : 0 ≤ (A 0 0).re := (Complex.le_def.1 h00).1
  have h11re : 0 ≤ (A 1 1).re := (Complex.le_def.1 h11).1
  by_contra hnot
  have hsum : (A 0 0).re + (A 1 1).re = 0 := by linarith
  have h00r : (A 0 0).re = 0 := by linarith
  have h11r : (A 1 1).re = 0 := by linarith
  have h00i : (A 0 0).im = 0 := by
    simpa using (Complex.le_def.1 h00).2.symm
  have h11i : (A 1 1).im = 0 := by
    simpa using (Complex.le_def.1 h11).2.symm
  have h00c : A 0 0 = 0 := Complex.ext h00r h00i
  have h11c : A 1 1 = 0 := Complex.ext h11r h11i
  have hcol0 : A *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = 0 := by
    apply (hA.dotProduct_mulVec_zero_iff _).1
    simpa [Matrix.mulVec_single] using h00c
  have hcol1 : A *ᵥ Pi.single (1 : Fin 2) (1 : ℂ) = 0 := by
    apply (hA.dotProduct_mulVec_zero_iff _).1
    simpa [Matrix.mulVec_single] using h11c
  apply hA0
  ext i j
  fin_cases j
  · have h := congrFun hcol0 i
    simpa [Matrix.mulVec_single] using h
  · have h := congrFun hcol1 i
    simpa [Matrix.mulVec_single] using h

/-- Cross-prime leak retained by the two genuine source boundaries. -/
def primeGammaTwoThreeChannelGhostMismatch (t : ℝ) : ℂ :=
  (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo : ℂ) -
    primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree

/-- Sum of Hermitian energies on the literal prime-two and prime-three source boundaries. -/
def primeGammaTwoThreeChannelHermitianBoundaryEnergy
    (A : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : ℝ :=
  primeGammaTwoChannelHermitianEnergy A
      (deningerCalderonWittChannelResolvedInverseGammaReporter t
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeTwo))) +
    primeGammaTwoChannelHermitianEnergy A
      (deningerCalderonWittChannelResolvedInverseGammaReporter t
        (deningerCalderonWittGlobalOrientedBoundary
          (deningerCalderonWittPrimeArchOrientationGreenBoundaryWitness
            deningerCalderonWittPrimeThree)))

/-- Exact classification formula: every off-diagonal channel coupling disappears on the two
literal source-boundary axes. -/
theorem primeGammaTwoThreeChannelHermitianBoundaryEnergy_eq
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (t : ℝ) :
    primeGammaTwoThreeChannelHermitianBoundaryEnergy A t =
      ((A 0 0).re + (A 1 1).re) *
        Complex.normSq (primeGammaTwoThreeChannelGhostMismatch t) := by
  rw [primeGammaTwoThreeChannelHermitianBoundaryEnergy,
    deningerCalderonWittChannelResolvedInverseGammaReporter_twoBoundary,
    deningerCalderonWittChannelResolvedInverseGammaReporter_threeBoundary,
    primeGammaTwoChannelHermitianEnergy_right hA,
    primeGammaTwoChannelHermitianEnergy_left hA]
  have hneg :
      (primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree : ℂ) -
          primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo =
        -primeGammaTwoThreeChannelGhostMismatch t := by
    rw [primeGammaTwoThreeChannelGhostMismatch]
    ring
  rw [hneg]
  change (A 1 1).re * Complex.normSq (primeGammaTwoThreeChannelGhostMismatch t) +
      (A 0 0).re * Complex.normSq (-primeGammaTwoThreeChannelGhostMismatch t) = _
  simp only [Complex.normSq_neg]
  ring

/-- The cross-prime leak vanishes exactly at neutral horizontal grade. -/
theorem primeGammaTwoThreeChannelGhostMismatch_eq_zero_iff (t : ℝ) :
    primeGammaTwoThreeChannelGhostMismatch t = 0 ↔ t = 0 := by
  constructor
  · intro h
    have hEq :
        primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo =
          primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeThree := by
      exact_mod_cast sub_eq_zero.mp h
    have hshared : PrimeGammaTwoThreeSharedInverseOrientedGhostWard t := by
      refine ⟨primeGammaLocalInverseOrientedGhost t deningerCalderonWittPrimeTwo,
        primeGammaLocalInverseOrientedGhost_pos t deningerCalderonWittPrimeTwo,
        primeGammaLocalInverseOrientedGhost_ward t deningerCalderonWittPrimeTwo, ?_⟩
      rw [hEq]
      exact primeGammaLocalInverseOrientedGhost_ward t deningerCalderonWittPrimeThree
    exact (primeGammaTwoThreeSharedInverseOrientedGhostWard_iff t).mp hshared
  · rintro rfl
    norm_num [primeGammaTwoThreeChannelGhostMismatch,
      primeGammaLocalInverseOrientedGhost]

/-- Every nonblind positive Hermitian channel scalarizer preserves the exact critical-wall zero
locus. -/
theorem primeGammaTwoThreeChannelHermitianBoundaryEnergy_eq_zero_iff
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0) (t : ℝ) :
    primeGammaTwoThreeChannelHermitianBoundaryEnergy A t = 0 ↔ t = 0 := by
  rw [primeGammaTwoThreeChannelHermitianBoundaryEnergy_eq hA]
  have htrace := posSemidef_two_diag_re_sum_pos_of_ne_zero hA hA0
  constructor
  · intro h
    have hnorm : Complex.normSq (primeGammaTwoThreeChannelGhostMismatch t) = 0 :=
      (mul_eq_zero.mp h).resolve_left htrace.ne'
    exact (primeGammaTwoThreeChannelGhostMismatch_eq_zero_iff t).mp
      (Complex.normSq_eq_zero.mp hnorm)
  · intro ht
    rw [ht]
    norm_num [primeGammaTwoThreeChannelGhostMismatch,
      primeGammaLocalInverseOrientedGhost]

/-- Universal zero boundary energy over actual Xi support. -/
def EveryFrankensteinPositiveHermitianChannelBoundaryEnergyZero
    (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ rho : XiDivisorSupport,
    primeGammaTwoThreeChannelHermitianBoundaryEnergy A
      (2 * (rho : ℂ).re - 1) = 0

/-- Any fixed nonzero PSD channel metric turns universal source-boundary darkness into exactly RH. -/
theorem everyFrankensteinPositiveHermitianChannelBoundaryEnergyZero_iff_riemannHypothesis
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    EveryFrankensteinPositiveHermitianChannelBoundaryEnergyZero A ↔
      RiemannHypothesis := by
  constructor
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      have ht := (primeGammaTwoThreeChannelHermitianBoundaryEnergy_eq_zero_iff
        hA hA0 (2 * (rho : ℂ).re - 1)).mp (h rho)
      linarith
  · intro h rho
    apply (primeGammaTwoThreeChannelHermitianBoundaryEnergy_eq_zero_iff
      hA hA0 (2 * (rho : ℂ).re - 1)).mpr
    have hr := xi_divisor_support_re_eq_half_of_rh h rho
    linarith

/-- The same universal energy law is precisely the common HB/FZZ-P/PW-B/RBH Ward endpoint. -/
theorem everyFrankensteinPositiveHermitianChannelBoundaryEnergyZero_iff_sharedFourRouteWardEndpoint
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    EveryFrankensteinPositiveHermitianChannelBoundaryEnergyZero A ↔
      SharedFourRouteWardEndpoint := by
  have hshared : SharedFourRouteWardEndpoint ↔ RiemannHypothesis :=
    everyFrankensteinChannelResolvedGammaJointNaturality_iff_sharedFourRouteWardEndpoint.symm.trans
      everyFrankensteinChannelResolvedGammaJointNaturality_iff_riemannHypothesis
  exact (everyFrankensteinPositiveHermitianChannelBoundaryEnergyZero_iff_riemannHypothesis
    hA hA0).trans hshared.symm

/-- Closed route certificate: every fixed PSD Hermitian scalarizer is either zero and blind at all
grades, or nonzero and an exact shared-four-route/RH receiver. -/
def SharedWardPositiveHermitianChannelScalarizationRouteKilled : Prop :=
  ∀ A : Matrix (Fin 2) (Fin 2) ℂ, A.PosSemidef →
    ((A = 0 ∧
        ∀ t : ℝ, primeGammaTwoThreeChannelHermitianBoundaryEnergy A t = 0) ∨
      (A ≠ 0 ∧
        (EveryFrankensteinPositiveHermitianChannelBoundaryEnergyZero A ↔
          SharedFourRouteWardEndpoint) ∧
        (EveryFrankensteinPositiveHermitianChannelBoundaryEnergyZero A ↔
          RiemannHypothesis)))

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Arbitrary fixed positive Hermitian mixing of the resolved
prime channels cannot manufacture the missing source law: it is blind or preserves the exact
HB/FZZ-P/PW-B/RBH Ward/RH wall. -/
theorem sharedWardPositiveHermitianChannelScalarizationRouteKilled :
    SharedWardPositiveHermitianChannelScalarizationRouteKilled := by
  intro A hA
  by_cases hA0 : A = 0
  · left
    refine ⟨hA0, ?_⟩
    intro t
    rw [hA0]
    simp [primeGammaTwoThreeChannelHermitianBoundaryEnergy,
      primeGammaTwoChannelHermitianEnergy]
  · right
    exact ⟨hA0,
      everyFrankensteinPositiveHermitianChannelBoundaryEnergyZero_iff_sharedFourRouteWardEndpoint
        hA hA0,
      everyFrankensteinPositiveHermitianChannelBoundaryEnergyZero_iff_riemannHypothesis hA hA0⟩

end

end RHTower
