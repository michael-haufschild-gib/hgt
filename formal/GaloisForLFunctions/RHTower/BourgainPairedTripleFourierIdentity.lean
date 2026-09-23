/-
# Paired triple Fourier identity

The paired triple cloud used by the Gaussian large sieve is exactly the
product of the cubes of its two generating extension sums.  For Bourgain's
exact osculating frequencies, those two extension sums are the corresponding
exact local square-root sums, up to constant unit phases.
-/
import GaloisForLFunctions.RHTower.BourgainExactOsculatingGaussianDecoupling

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Additive characters turn vector addition into multiplication. -/
theorem bourgainAdditiveCharacter_add
    (x u v : BourgainPhaseSpace) :
    bourgainAdditiveCharacter x (u + v) =
      bourgainAdditiveCharacter x u *
        bourgainAdditiveCharacter x v := by
  unfold bourgainAdditiveCharacter bourgainDot
  rw [show
    (∑ j : Fin 4, x j * (u + v) j) =
      (∑ j : Fin 4, x j * u j) +
        ∑ j : Fin 4, x j * v j by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The triple-cloud Fourier sum is the cube of its generating sum. -/
theorem bourgainWeightedFourierSum_tripleCloud
    {H : ℕ} (L : BourgainPhaseSpace)
    (p : Fin H → BourgainPhaseSpace) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainWeightedFourierSum L (bourgainTripleCloud p)
        (bourgainTripleWeight c) x =
      bourgainWeightedFourierSum L p c x ^ (3 : ℕ) := by
  unfold bourgainWeightedFourierSum
  rw [Fintype.sum_pow]
  apply Fintype.sum_congr
  intro h
  simp only [Fin.prod_univ_three, bourgainTripleWeight,
    bourgainTripleCloud, Fin.sum_univ_three]
  rw [bourgainAdditiveCharacter_add,
    bourgainAdditiveCharacter_add]
  ring

/-- The paired-cloud Fourier sum factors into two cubic extension sums. -/
theorem bourgainWeightedFourierSum_pairedTripleCloud
    {H : ℕ} (L : BourgainPhaseSpace)
    (p q : Fin H → BourgainPhaseSpace) (c₁ c₂ : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainWeightedFourierSum L
        (bourgainPairedTripleCloud p q)
        (bourgainPairedTripleWeight c₁ c₂) x =
      bourgainWeightedFourierSum L p c₁ x ^ (3 : ℕ) *
        bourgainWeightedFourierSum L q c₂ x ^ (3 : ℕ) := by
  calc
    bourgainWeightedFourierSum L
        (bourgainPairedTripleCloud p q)
        (bourgainPairedTripleWeight c₁ c₂) x =
      bourgainWeightedFourierSum L (bourgainTripleCloud p)
          (bourgainTripleWeight c₁) x *
        bourgainWeightedFourierSum L (bourgainTripleCloud q)
          (bourgainTripleWeight c₂) x := by
      unfold bourgainWeightedFourierSum
        bourgainPairedTripleCloud bourgainPairedTripleWeight
      rw [Fintype.sum_prod_type]
      simp only [bourgainAdditiveCharacter_add]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [bourgainWeightedFourierSum_tripleCloud,
        bourgainWeightedFourierSum_tripleCloud]

/-- Bourgain's vector additive character is the scalar unit character of
the corresponding dot product. -/
theorem bourgainAdditiveCharacter_eq_unitCharacter
    (x u : BourgainPhaseSpace) :
    bourgainAdditiveCharacter x u =
      bourgainUnitCharacter (bourgainDot x u) := by
  rfl

/-- The exact left local square-root sum is its osculating-frequency
extension sum times a constant unit phase. -/
theorem bourgainSquareRootExactLocalSum_eq_leftFrequencySum
    {H : ℕ} {scale a b D : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (L : BourgainPhaseSpace) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainSquareRootExactLocalSum H D a c
        ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ha hab).symm (bourgainCoordinateScale L x)) =
      bourgainUnitCharacter
          (bourgainSquareRootCurvePhase
            ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
              hscale ha hab).symm (bourgainCoordinateScale L x))
            (a ^ (2 : ℕ))) *
        bourgainWeightedFourierSum L
          (bourgainExactLeftOsculatingFrequency hscale ha hab D) c x := by
  unfold bourgainSquareRootExactLocalSum
    bourgainWeightedFourierSum
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  rw [bourgainAdditiveCharacter_eq_unitCharacter,
    bourgainDot_exactLeftOsculatingFrequency]
  calc
    c n * bourgainUnitCharacter
        (bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm (bourgainCoordinateScale L x))
          (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D)) =
      c n * bourgainUnitCharacter
        (bourgainSquareRootCurvePhase
            ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
              hscale ha hab).symm (bourgainCoordinateScale L x))
            (a ^ (2 : ℕ)) +
          (bourgainSquareRootCurvePhase
              ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
                hscale ha hab).symm (bourgainCoordinateScale L x))
              (a ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
            bourgainSquareRootCurvePhase
              ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
                hscale ha hab).symm (bourgainCoordinateScale L x))
              (a ^ (2 : ℕ)))) := by
        congr 3
        ring
    _ = _ := by
      rw [bourgainUnitCharacter_add]
      ring

/-- The exact right local square-root sum is its osculating-frequency
extension sum times a constant unit phase. -/
theorem bourgainSquareRootExactLocalSum_eq_rightFrequencySum
    {H : ℕ} {scale a b D : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (L : BourgainPhaseSpace) (c : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    bourgainSquareRootExactLocalSum H D b c
        ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
          hscale ha hab).symm (bourgainCoordinateScale L x)) =
      bourgainUnitCharacter
          (bourgainSquareRootCurvePhase
            ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
              hscale ha hab).symm (bourgainCoordinateScale L x))
            (b ^ (2 : ℕ))) *
        bourgainWeightedFourierSum L
          (bourgainExactRightOsculatingFrequency hscale ha hab D) c x := by
  unfold bourgainSquareRootExactLocalSum
    bourgainWeightedFourierSum
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro n
  rw [bourgainAdditiveCharacter_eq_unitCharacter,
    bourgainDot_exactRightOsculatingFrequency]
  calc
    c n * bourgainUnitCharacter
        (bourgainSquareRootCurvePhase
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm (bourgainCoordinateScale L x))
          (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D)) =
      c n * bourgainUnitCharacter
        (bourgainSquareRootCurvePhase
            ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
              hscale ha hab).symm (bourgainCoordinateScale L x))
            (b ^ (2 : ℕ)) +
          (bourgainSquareRootCurvePhase
              ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
                hscale ha hab).symm (bourgainCoordinateScale L x))
              (b ^ (2 : ℕ) + (bourgainIndex n : ℝ) / D) -
            bourgainSquareRootCurvePhase
              ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
                hscale ha hab).symm (bourgainCoordinateScale L x))
              (b ^ (2 : ℕ)))) := by
        congr 3
        ring
    _ = _ := by
      rw [bourgainUnitCharacter_add]
      ring

/-- Pointwise bridge from paired-cloud Fourier mass to the exact bilinear
sixth moment in physical coordinates. -/
theorem norm_sq_bourgainWeightedFourierSum_pairedTripleCloud_eq_exact
    {H : ℕ} {scale a b D : ℝ}
    (hscale : scale ≠ 0) (ha : 0 < a) (hab : a < b)
    (L : BourgainPhaseSpace) (c₁ c₂ : Fin H → ℂ)
    (x : BourgainPhaseSpace) :
    ‖bourgainWeightedFourierSum L
        (bourgainPairedTripleCloud
          (bourgainExactLeftOsculatingFrequency hscale ha hab D)
          (bourgainExactRightOsculatingFrequency hscale ha hab D))
        (bourgainPairedTripleWeight c₁ c₂) x‖ ^ (2 : ℕ) =
      ‖bourgainSquareRootExactLocalSum H D a c₁
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm (bourgainCoordinateScale L x))‖ ^
            (6 : ℕ) *
        ‖bourgainSquareRootExactLocalSum H D b c₂
          ((bourgainScaledOsculatingPhaseContinuousLinearEquiv
            hscale ha hab).symm (bourgainCoordinateScale L x))‖ ^
            (6 : ℕ) := by
  rw [bourgainWeightedFourierSum_pairedTripleCloud]
  rw [norm_mul, norm_pow, norm_pow]
  rw [bourgainSquareRootExactLocalSum_eq_leftFrequencySum,
    bourgainSquareRootExactLocalSum_eq_rightFrequencySum]
  simp only [norm_mul, norm_bourgainUnitCharacter, one_mul]
  ring

end

end RHTower
