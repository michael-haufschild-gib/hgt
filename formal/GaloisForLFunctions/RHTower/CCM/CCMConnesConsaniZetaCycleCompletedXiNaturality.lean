import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniArithmeticJacobianPrimeFibre
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniZetaCycles
import GaloisForLFunctions.RHTower.Deninger.DeningerBigWittCenteredPrimeMarkXiFiberComparison

/-!
# Arithmetic-Jacobian / zeta-cycle / completed-Xi naturality

This module joins two exact Connes--Consani literature frontiers already
formalized separately:

* the 2026 arithmetic-Jacobian universal prime fibre, whose deck generator is
  diagonal Frobenius together with one `log p` period;
* the Scaling-Site zeta-cycle spectral realization, whose character `m` at
  length `L` sees `zeta(1/2 - 2*pi*i*m/L)`.

The first new theorem identifies character survival exactly with inhabitation
of the completed-Xi theta spectral fibre at the same centered label.  The
second proves the source-first cross-fibre law: a prime cover sends
`(L,m)` to `(pL,pm)` and therefore fixes, rather than dilates, the centered
Xi spectral label.  This gives an actual equivalence of completed-Xi fibres
before any zero is selected.

At `p=2`, the arithmetic-Jacobian deck relation and canonical Big-Witt
Frobenius form one closed naturality statement.  Frobenius changes the
arithmetic reporter base, while the Scaling-Site cover retains the same Xi
spectral fibre.  No RH premise, zero premise, extra assumption, or spectral
preperiodicity is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Centered completed-Xi label of Fourier character `m` on a zeta circle of
length `L`. -/
def ccmZetaCircleCompletedXiSpectralLabel
    (L : CCMZetaCircleLength) (m : ℤ) : ℂ :=
  ((-2 * Real.pi * (m : ℝ) / (L : ℝ) : ℝ) : ℂ)

/-- The Connes--Consani critical point is the completed-Xi affine coordinate
of the same centered label. -/
theorem ccmZetaCircleCriticalPoint_eq_completedXiSpectralLabel
    (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCircleCriticalPoint L m =
      1 / 2 + ccmZetaCircleCompletedXiSpectralLabel L m * Complex.I := by
  simpa [ccmZetaCircleCompletedXiSpectralLabel] using
    ccmZetaCircleCriticalPoint_as_ordinate L m

/-- Completion introduces no extra zero on a zeta-cycle critical character. -/
theorem XiC_ccmZetaCircleSpectralLabel_eq_zero_iff
    (L : CCMZetaCircleLength) (m : ℤ) :
    XiC (ccmZetaCircleCompletedXiSpectralLabel L m) = 0 ↔
      riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 := by
  rw [ccmZetaCircleCriticalPoint_eq_completedXiSpectralLabel]
  apply xi_eq_zero_iff
  · simp [ccmZetaCircleCompletedXiSpectralLabel]
  · intro h
    have hre := congrArg Complex.re h
    norm_num [ccmZetaCircleCompletedXiSpectralLabel] at hre

/-- Exact receiver comparison: a Scaling-Site zeta-cycle character survives
exactly when the corresponding completed-Xi theta spectral fibre is inhabited. -/
theorem ccmZetaCycleCharacterSurvives_iff_nonempty_completedXiThetaSpectralFiber
    (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCycleCharacterSurvives L m ↔
      Nonempty (CompletedXiThetaSpectralFiber
        (ccmZetaCircleCompletedXiSpectralLabel L m)) := by
  rw [ccmZetaCycleCharacterSurvives_iff,
    ← XiC_ccmZetaCircleSpectralLabel_eq_zero_iff,
    nonempty_completedXiThetaSpectralFiber_iff]

/-- A rational prime as a positive cover degree. -/
def ccmZetaCirclePrimeCoverDegree (p : Nat.Primes) : ℕ+ :=
  ⟨p, p.2.pos⟩

/-- Prime-cover rigidity: `(L,m) -> (pL,pm)` fixes the centered completed-Xi
label exactly.  The receiver action is not `alpha -> p*alpha`. -/
theorem ccmZetaCircleCompletedXiSpectralLabel_primeCover
    (p : Nat.Primes) (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCircleCompletedXiSpectralLabel
        (ccmZetaCircleCoverLength L (ccmZetaCirclePrimeCoverDegree p))
        ((ccmZetaCirclePrimeCoverDegree p : ℤ) * m) =
      ccmZetaCircleCompletedXiSpectralLabel L m := by
  have hcritical := ccmZetaCircleCriticalPoint_cover L
    (ccmZetaCirclePrimeCoverDegree p) m
  rw [ccmZetaCircleCriticalPoint_eq_completedXiSpectralLabel,
    ccmZetaCircleCriticalPoint_eq_completedXiSpectralLabel] at hcritical
  exact mul_right_cancel₀ Complex.I_ne_zero (add_left_cancel hcritical)

/-- Character survival is invariant under the prime cover, without assuming
that either character survives. -/
theorem ccmZetaCycleCharacterSurvives_primeCover_iff
    (p : Nat.Primes) (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCycleCharacterSurvives
        (ccmZetaCircleCoverLength L (ccmZetaCirclePrimeCoverDegree p))
        ((ccmZetaCirclePrimeCoverDegree p : ℤ) * m) ↔
      ccmZetaCycleCharacterSurvives L m := by
  rw [ccmZetaCycleCharacterSurvives_iff,
    ccmZetaCycleCharacterSurvives_iff,
    ccmZetaCircleCriticalPoint_cover]

/-- Actual cross-fibre equivalence induced by prime-cover label rigidity.
It exists for every character; when the Xi fibre is empty it is the unique
equivalence between the corresponding empty dependent fibres. -/
def ccmZetaCircleCompletedXiPrimeCoverFiberEquiv
    (p : Nat.Primes) (L : CCMZetaCircleLength) (m : ℤ) :
    CompletedXiThetaSpectralFiber
        (ccmZetaCircleCompletedXiSpectralLabel L m) ≃
      CompletedXiThetaSpectralFiber
        (ccmZetaCircleCompletedXiSpectralLabel
          (ccmZetaCircleCoverLength L (ccmZetaCirclePrimeCoverDegree p))
          ((ccmZetaCirclePrimeCoverDegree p : ℤ) * m)) :=
  Equiv.cast (congrArg CompletedXiThetaSpectralFiber
    (ccmZetaCircleCompletedXiSpectralLabel_primeCover p L m).symm)

/-- Correct dyadic Big-Witt/Scaling-Site naturality.  Big-Witt Frobenius
squares the arithmetic reporter base; the cover equivalence keeps the Xi
spectral label fixed. -/
theorem deningerBigWittFrobeniusTwo_ccmZetaCircleCompletedXiPrimeCover_naturality
    (q : ℕ) (L : CCMZetaCircleLength) (m : ℤ)
    (x : CompletedXiThetaSpectralFiber
      (ccmZetaCircleCompletedXiSpectralLabel L m)) :
    deningerBigWittFrobeniusTwoRingHom
        (completedXiThetaFiberBigWittReporter q
          (ccmZetaCircleCompletedXiSpectralLabel L m) x) =
      completedXiThetaFiberBigWittReporter (q ^ 2)
        (ccmZetaCircleCompletedXiSpectralLabel
          (ccmZetaCircleCoverLength L
            (ccmZetaCirclePrimeCoverDegree ⟨2, Nat.prime_two⟩))
          ((ccmZetaCirclePrimeCoverDegree ⟨2, Nat.prime_two⟩ : ℤ) * m))
        (ccmZetaCircleCompletedXiPrimeCoverFiberEquiv
          ⟨2, Nat.prime_two⟩ L m x) := by
  simpa [completedXiThetaFiberBigWittReporter,
    ccmZetaCircleCompletedXiSpectralLabel_primeCover] using
      deningerBigWittFrobeniusTwo_completedXiThetaFiberReporter q
        (ccmZetaCircleCompletedXiSpectralLabel L m) x

/-- The dyadic prime used by both arithmetic-Jacobian monodromy and
Big-Witt Frobenius two. -/
def ccmArithmeticJacobianPrimeTwo : Nat.Primes :=
  ⟨2, Nat.prime_two⟩

/-- Source-first cross-fibre natural transformation.  Left component is the
literal 2026 arithmetic-Jacobian deck relation.  Right component is Big-Witt
Frobenius transported across the Scaling-Site prime cover to the same
completed-Xi spectral fibre. -/
theorem ccmArithmeticJacobianBigWittCompletedXi_actualCrossFiberNaturality
    (u : DeningerPacketUnits ccmArithmeticJacobianPrimeTwo) (t : ℝ)
    (q : ℕ) (L : CCMZetaCircleLength) (m : ℤ)
    (x : CompletedXiThetaSpectralFiber
      (ccmZetaCircleCompletedXiSpectralLabel L m)) :
    ccmArithmeticJacobianPrimeFibreMk ccmArithmeticJacobianPrimeTwo
        (Additive.ofMul
          (deningerPacketFrobeniusUnit ccmArithmeticJacobianPrimeTwo * u),
          t + Real.log (2 : ℝ)) =
      ccmArithmeticJacobianPrimeFibreMk ccmArithmeticJacobianPrimeTwo
        (Additive.ofMul u, t) ∧
    deningerBigWittFrobeniusTwoRingHom
        (completedXiThetaFiberBigWittReporter q
          (ccmZetaCircleCompletedXiSpectralLabel L m) x) =
      completedXiThetaFiberBigWittReporter (q ^ 2)
        (ccmZetaCircleCompletedXiSpectralLabel
          (ccmZetaCircleCoverLength L
            (ccmZetaCirclePrimeCoverDegree ccmArithmeticJacobianPrimeTwo))
          ((ccmZetaCirclePrimeCoverDegree
            ccmArithmeticJacobianPrimeTwo : ℤ) * m))
        (ccmZetaCircleCompletedXiPrimeCoverFiberEquiv
          ccmArithmeticJacobianPrimeTwo L m x) := by
  exact ⟨ccmArithmeticJacobianPrimeFibre_frobenius_relation
      ccmArithmeticJacobianPrimeTwo u t,
    deningerBigWittFrobeniusTwo_ccmZetaCircleCompletedXiPrimeCover_naturality
      q L m x⟩

end

end RHTower
