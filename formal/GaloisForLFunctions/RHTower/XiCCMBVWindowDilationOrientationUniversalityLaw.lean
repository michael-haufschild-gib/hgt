import GaloisForLFunctions.RHTower.BVPrimeWindowDilationOrientation
import GaloisForLFunctions.RHTower.XiCCMMultiObservableDivisorUniversalityLaw

/-!
# Xi CCM bounded-variation window dilation orientation universality

A single noncensoring compact bounded-variation prime window generates two complete Xi-divisor
tomographies after forward and inverse integer dilation.  Their normalized residues still recover
the same Xi multiplicity, while their raw residues carry opposite Mellin characters.  The resulting
norm orientation is strictly positive at every right Xi divisor copy, and its source origin is the
exact square-index decimation law before continuation.
-/

open Complex Filter Function Set Topology WithTop

namespace RHTower

noncomputable section

open CompactBVPrimeWindow

private theorem natCast_pos_of_one_lt {r : ℕ} (hr : 1 < r) : (0 : ℝ) < r := by
  exact_mod_cast (lt_trans Nat.zero_lt_one hr)

/-- The full source-to-divisor certificate for a forward/inverse BV-window dilation pair. -/
structure XiCCMBVWindowDilationOrientationUniversalCertificate
    (W : CompactBVPrimeWindow) (L : ℝ) (N r : ℕ) (hr : 1 < r)
    (q : XiRightZeroCopy) : Prop where
  dilationTomography :
    XiCCMMultiObservableDivisorUniversalCertificate
      (W.argumentDilation r (natCast_pos_of_one_lt hr)) L N q
  expansionTomography :
    XiCCMMultiObservableDivisorUniversalCertificate
      (W.argumentExpansion r (natCast_pos_of_one_lt hr)) L N q
  dilationResidueCharacter :
    (W.argumentDilation r (natCast_pos_of_one_lt hr)).continuedSourceResidueValue
        (q.1.1 : ℂ) =
      (r : ℂ) ^ ((q.1.1 : ℂ) - 1 / 2) *
        W.continuedSourceResidueValue (q.1.1 : ℂ)
  expansionResidueCharacter :
    (W.argumentExpansion r (natCast_pos_of_one_lt hr)).continuedSourceResidueValue
        (q.1.1 : ℂ) =
      (r : ℂ) ^ (1 / 2 - (q.1.1 : ℂ)) *
        W.continuedSourceResidueValue (q.1.1 : ℂ)
  residueOrientation_pos :
    0 < W.continuedSourceResidueOrientation r (natCast_pos_of_one_lt hr) (q.1.1 : ℂ)
  weightedPrimeWindow_squareIndexDecimation :
    ∀ n : ℕ,
      (W.argumentDilation r (natCast_pos_of_one_lt hr)).weightedPrimeWindow n =
        (W.argumentExpansion r (natCast_pos_of_one_lt hr)).weightedPrimeWindow (r ^ (2 : ℕ) * n)
  polarCoefficient_squareIndexDecimation :
    ∀ n : ℕ,
      (W.argumentDilation r (natCast_pos_of_one_lt hr)).polarCoefficient n =
        (W.argumentExpansion r (natCast_pos_of_one_lt hr)).polarCoefficient (r ^ (2 : ℕ) * n)
  actualResidueLimits :
    Tendsto
        (fun s : ℂ => (s - ((q.1.1 : ℂ) + 1 / 2)) *
          (W.argumentDilation r (natCast_pos_of_one_lt hr)).continuedSource s)
        (nhdsWithin ((q.1.1 : ℂ) + 1 / 2) ({(q.1.1 : ℂ) + 1 / 2}ᶜ))
        (𝓝 ((W.argumentDilation r (natCast_pos_of_one_lt hr)).continuedSourceResidueValue
          (q.1.1 : ℂ))) ∧
      Tendsto
        (fun s : ℂ => (s - ((q.1.1 : ℂ) + 1 / 2)) *
          (W.argumentExpansion r (natCast_pos_of_one_lt hr)).continuedSource s)
        (nhdsWithin ((q.1.1 : ℂ) + 1 / 2) ({(q.1.1 : ℂ) + 1 / 2}ᶜ))
        (𝓝 ((W.argumentExpansion r (natCast_pos_of_one_lt hr)).continuedSourceResidueValue
          (q.1.1 : ℂ)))

/-- **Dilation/tomography/orientation law.**  One noncensoring BV prime window and every integer
dilation `r > 1` produce two nine-chart simple-pole tomography packets with the same normalized Xi
multiplicity.  Their raw actual residues have opposite Mellin characters and strictly positive
forward-minus-inverse norm orientation at every right Xi divisor copy.  Before continuation, the
same pair is related by literal square-index decimation of both prime and prime--polar sources. -/
theorem xiRightZero_ccmBVWindowDilationOrientationUniversalCertificate
    (W : CompactBVPrimeWindow) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2)
    (r : ℕ) (hr : 1 < r) (q : XiRightZeroCopy)
    (hM : W.mellinTransform (inverseTiltedXiPole q.1.1) ≠ 0) :
    XiCCMBVWindowDilationOrientationUniversalCertificate W L N r hr q := by
  have hrNat : 0 < r := lt_trans Nat.zero_lt_one hr
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hrNat
  have hrComplex : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrNat.ne'
  have hMDilation :
      (W.argumentDilation r hrReal).mellinTransform (inverseTiltedXiPole q.1.1) ≠ 0 := by
    rw [mellinTransform_argumentDilation]
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hrComplex)) hM
  have hMExpansion :
      (W.argumentExpansion r hrReal).mellinTransform (inverseTiltedXiPole q.1.1) ≠ 0 := by
    rw [mellinTransform_argumentExpansion]
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hrComplex)) hM
  have hbaseResidue : W.continuedSourceResidueValue (q.1.1 : ℂ) ≠ 0 := by
    rw [continuedSourceResidueValue,
      analyticOrderAt_regularizedRiemannZeta_eq_xi_of_support]
    change 2 * W.mellinTransform ((q.1.1 : ℂ) + 1 / 2) *
      (xiRightMultiplicity q : ℂ) ≠ 0
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (by simpa [inverseTiltedXiPole] using hM))
      (by exact_mod_cast (Nat.ne_of_gt (xiRightMultiplicity_pos q)))
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  have hrho : 0 < ((q.1.1 : XiDivisorSupport) : ℂ).re :=
    (xi_divisor_support_re_mem_open_unit q.1.1).1
  have hzero : regularizedRiemannZeta (q.1.1 : ℂ) = 0 := by
    have h := regularizedRiemannZeta_eq_zero_at_inverseTiltedXiPole q.1.1
    convert h using 1
    rw [inverseTiltedXiPole]
    ring
  exact {
    dilationTomography :=
      xiRightZero_ccmMultiObservableDivisorUniversalCertificate
        (W.argumentDilation r hrReal) hL hN q hMDilation
    expansionTomography :=
      xiRightZero_ccmMultiObservableDivisorUniversalCertificate
        (W.argumentExpansion r hrReal) hL hN q hMExpansion
    dilationResidueCharacter :=
      continuedSourceResidueValue_argumentDilation W r hrReal (q.1.1 : ℂ)
    expansionResidueCharacter :=
      continuedSourceResidueValue_argumentExpansion W r hrReal (q.1.1 : ℂ)
    residueOrientation_pos :=
      (continuedSourceResidueOrientation_pos_iff W (by exact_mod_cast hr) hbaseResidue).2 hright
    weightedPrimeWindow_squareIndexDecimation := fun n =>
      weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul W r hrNat n
    polarCoefficient_squareIndexDecimation := fun n =>
      polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul W r hrNat n
    actualResidueLimits :=
      tendsto_argumentDilation_expansion_continuedSource_residues
        W r hrReal hrho hzero }

end

end RHTower
