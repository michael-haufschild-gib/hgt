import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Kerr--Newman charged-scalar Gamma-response boundary

The exact charged-scalar Kerr--Newman response coefficient of Ma--Wu--Pang--Lu contains,
after removing factors independent of the complexified frequency coordinate `z`,

`Gamma(z + (1 + Delta) / 2) / Gamma(z + (1 - Delta) / 2)`,

where `Delta = 1 + 2*L` is the effective multipole gap.  Their equation (4) gives
`Delta = sqrt((2*ell+1)^2 - 4*(q_e Q)^2)`, and equation (21) gives the Gamma ratio.

This file applies the existing same-orientation Gamma-shift classification.  The response is
differentially algebraic exactly on the integral `Delta` lattice and hypertranscendental off it.
At the neutral odd gaps `Delta = 2*ell+1`, it is exactly a finite Pochhammer polynomial, matching
the polynomial collapse in their equation (33).  Its logarithmic response clock is the exact
difference of two digamma clocks and has the same DA/HT boundary.

Thus the selector is the observable's effective-multipole translation gap, not temporal evolution.

Physics provenance: L. Ma, Z.-H. Wu, Y. Pang, and H. Lu,
*Charging the Love numbers: Charged scalar response coefficients of Kerr-Newman black holes*,
arXiv:2408.10352v2 (2024), equations (4), (21), and (33).
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial ComplexOrder

noncomputable section

open scoped UnivMeroFieldInstances

/-- Effective multipole gap in the charged-scalar Kerr--Newman response.  The dimensionless
coupling `charge` represents `q_e Q`. -/
def kerrNewmanChargedScalarEffectiveMultipoleGap
    (ell : ℕ) (charge : ℂ) : ℂ :=
  Complex.sqrt ((2 * (ell : ℂ) + 1) ^ 2 - 4 * charge ^ 2)

/-- At zero scalar charge, the principal effective-multipole gap is the positive odd integer
selected by the neutral Kerr--Newman sector. -/
theorem kerrNewmanChargedScalarEffectiveMultipoleGap_neutral
    (ell : ℕ) :
    kerrNewmanChargedScalarEffectiveMultipoleGap ell 0 = 2 * (ell : ℂ) + 1 := by
  unfold kerrNewmanChargedScalarEffectiveMultipoleGap
  let x : ℝ := 2 * (ell : ℝ) + 1
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hcast : 2 * (ell : ℂ) + 1 = (x : ℂ) := by
    dsimp [x]
    push_cast
    ring
  rw [show ((2 * (ell : ℂ) + 1) ^ 2 - 4 * (0 : ℂ) ^ 2) =
    (2 * (ell : ℂ) + 1) ^ 2 by ring, hcast]
  have hnonneg : (0 : ℂ) ≤ (x : ℂ) ^ 2 := by
    refine RCLike.nonneg_iff_exists_ofReal.mpr ⟨x ^ 2, sq_nonneg x, ?_⟩
    simp
  rw [Complex.sqrt_of_nonneg hnonneg]
  have hre : ((x : ℂ) ^ 2).re = x ^ 2 := by
    simp [pow_two]
  rw [hre]
  simpa using congrArg (fun y : ℝ => (y : ℂ)) (Real.sqrt_sq hx)

/-- The real critical charge amplitude `sqrt (ell (ell + 1))` selects the unit effective gap. -/
theorem kerrNewmanChargedScalarEffectiveMultipoleGap_criticalCharge
    (ell : ℕ) :
    kerrNewmanChargedScalarEffectiveMultipoleGap ell
      (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) = 1 := by
  unfold kerrNewmanChargedScalarEffectiveMultipoleGap
  let x : ℝ := (ell : ℝ) * ((ell : ℝ) + 1)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hchargeSq : (Real.sqrt x : ℂ) ^ 2 = (x : ℂ) := by
    rw [← Complex.ofReal_pow]
    exact_mod_cast Real.sq_sqrt hx
  rw [show ((2 * (ell : ℂ) + 1) ^ 2 - 4 * (Real.sqrt x : ℂ) ^ 2) = 1 by
    rw [hchargeSq]
    dsimp [x]
    push_cast
    ring]
  simp

/-- Frequency-dependent Gamma core of the charged-scalar response, parameterized by its effective
multipole gap.  Frequency-independent Gamma factors from equation (21) are omitted. -/
def kerrNewmanChargedScalarGammaResponseMero
    (gap : ℂ) : meroField Set.univ :=
  reducedVenezianoAmplitudeMero ((1 + gap) / 2) (-gap)

/-- The physical specialization obtained by inserting the charged effective multipole gap. -/
def kerrNewmanChargedScalarPhysicalGammaResponseMero
    (ell : ℕ) (charge : ℂ) : meroField Set.univ :=
  kerrNewmanChargedScalarGammaResponseMero
    (kerrNewmanChargedScalarEffectiveMultipoleGap ell charge)

/-- **Kerr--Newman Gamma value relation.**  The normalized frequency response is exactly the
quotient with shifts `(1+Delta)/2` and `(1-Delta)/2`. -/
theorem kerrNewmanChargedScalarGammaResponseMero_eq_gammaRatio
    (gap : ℂ) :
    kerrNewmanChargedScalarGammaResponseMero gap =
      gammaShiftMero ((1 + gap) / 2) /
        gammaShiftMero ((1 - gap) / 2) := by
  rw [kerrNewmanChargedScalarGammaResponseMero,
    reducedVenezianoAmplitudeMero]
  congr 2
  ring

/-- **Exact effective-multipole boundary.**  The response is DA precisely when the physical
translation gap is integral. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap
    (gap : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (kerrNewmanChargedScalarGammaResponseMero gap) ↔
      ∃ k : ℤ, gap = (k : ℂ) := by
  rw [kerrNewmanChargedScalarGammaResponseMero,
    differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    simpa using congrArg Neg.neg hk
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    simpa using congrArg Neg.neg hk

/-- Off the integral effective-multipole lattice, the charged response is HT. -/
theorem hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap
    (gap : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (kerrNewmanChargedScalarGammaResponseMero gap) ↔
      ∀ k : ℤ, gap ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap]
  push Not
  rfl

/-- The paper's physical charged response is DA exactly when its square-root effective gap lands
on the integer lattice. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarPhysicalGammaResponseMero_iff
    (ell : ℕ) (charge : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (kerrNewmanChargedScalarPhysicalGammaResponseMero ell charge) ↔
      ∃ k : ℤ,
        kerrNewmanChargedScalarEffectiveMultipoleGap ell charge = (k : ℂ) := by
  exact
    differentialAlgebraicOver_kerrNewmanChargedScalarGammaResponseMero_iff_integerGap
      (kerrNewmanChargedScalarEffectiveMultipoleGap ell charge)

/-- The complementary physical charged sector is HT. -/
theorem hypertranscendentalOver_kerrNewmanChargedScalarPhysicalGammaResponseMero_iff
    (ell : ℕ) (charge : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (kerrNewmanChargedScalarPhysicalGammaResponseMero ell charge) ↔
      ∀ k : ℤ,
        kerrNewmanChargedScalarEffectiveMultipoleGap ell charge ≠ (k : ℂ) := by
  exact
    hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap
      (kerrNewmanChargedScalarEffectiveMultipoleGap ell charge)

/-- **Positive exceptional-sector normal form.**  At the neutral odd gap `2*ell+1`, the complete
frequency-dependent Gamma core is the finite Pochhammer polynomial with roots from `-ell` through
`ell`. -/
theorem kerrNewmanNeutralScalarGammaResponseMero_eq_pochhammer
    (ell : ℕ) :
    kerrNewmanChargedScalarGammaResponseMero (2 * (ell : ℂ) + 1) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaOrbitNatFactor (-(ell : ℂ)) (2 * ell + 1)) := by
  have h := reducedVenezianoAmplitudeMero_negSuccShift
    ((ell : ℂ) + 1) (2 * ell)
  rw [kerrNewmanChargedScalarGammaResponseMero]
  convert h using 1 <;> push_cast <;> ring_nf

/-- Neutral integer multipoles therefore have a finite differential-algebraic response core. -/
theorem differentialAlgebraicOver_kerrNewmanNeutralScalarGammaResponseMero
    (ell : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrNewmanChargedScalarGammaResponseMero (2 * (ell : ℂ) + 1)) := by
  rw [kerrNewmanNeutralScalarGammaResponseMero_eq_pochhammer]
  exact HTGeometry.differentialAlgebraicOver_algebraMap _

/-- At the critical real charge amplitude, the physical response is the unit-gap finite
Gamma-orbit factor. -/
theorem kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_linearOrbit
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalGammaResponseMero ell
      (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (gammaOrbitNatFactor 0 1) := by
  unfold kerrNewmanChargedScalarPhysicalGammaResponseMero
  rw [kerrNewmanChargedScalarEffectiveMultipoleGap_criticalCharge]
  simpa using kerrNewmanNeutralScalarGammaResponseMero_eq_pochhammer 0

/-- The critical-charge physical Kerr--Newman response lies in the differential-algebraic sector
because its Gamma core is a finite unit-gap orbit factor. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge
    (ell : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrNewmanChargedScalarPhysicalGammaResponseMero ell
        (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ)) := by
  rw [kerrNewmanChargedScalarPhysicalGammaResponseMero_criticalCharge_eq_linearOrbit]
  exact HTGeometry.differentialAlgebraicOver_algebraMap _

/-- Logarithmic response clock of the normalized charged-scalar Gamma coefficient. -/
def kerrNewmanChargedScalarLogResponseClockMero
    (gap : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock
    (kerrNewmanChargedScalarGammaResponseMero gap)

/-- Physical logarithmic response clock after specializing the charged effective multipole gap. -/
def kerrNewmanChargedScalarPhysicalLogResponseClockMero
    (ell : ℕ) (charge : ℂ) : meroField Set.univ :=
  kerrNewmanChargedScalarLogResponseClockMero
    (kerrNewmanChargedScalarEffectiveMultipoleGap ell charge)

/-- **Logarithmic clock value relation.**  The response clock is the difference of the two
digamma observations selected by the effective multipole gap. -/
theorem kerrNewmanChargedScalarLogResponseClockMero_eq_digammaDifference
    (gap : ℂ) :
    kerrNewmanChargedScalarLogResponseClockMero gap =
      digammaShiftMero ((1 + gap) / 2) -
        digammaShiftMero ((1 - gap) / 2) := by
  unfold kerrNewmanChargedScalarLogResponseClockMero
    HTGeometry.wignerSmithLogClock
  rw [kerrNewmanChargedScalarGammaResponseMero_eq_gammaRatio,
    Differential.logDeriv_div]
  · rfl
  · exact gammaShiftMero_ne_zero ((1 + gap) / 2)
  · exact gammaShiftMero_ne_zero ((1 - gap) / 2)

/-- The logarithmic clock has exactly the same integral-gap DA/HT boundary as the response. -/
theorem hypertranscendentalOver_kerrNewmanChargedScalarLogResponseClockMero_iff_nonintegerGap
    (gap : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (kerrNewmanChargedScalarLogResponseClockMero gap) ↔
      ∀ k : ℤ, gap ≠ (k : ℂ) := by
  rw [kerrNewmanChargedScalarLogResponseClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff,
    hypertranscendentalOver_kerrNewmanChargedScalarGammaResponseMero_iff_nonintegerGap]

/-- The unit-gap logarithmic response clock is differentially algebraic. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarLogResponseClockMero_unitGap :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrNewmanChargedScalarLogResponseClockMero 1) := by
  unfold kerrNewmanChargedScalarLogResponseClockMero
    HTGeometry.wignerSmithLogClock Differential.logDeriv
  apply differentialAlgebraicOver_deriv_div_self
  simpa using differentialAlgebraicOver_kerrNewmanNeutralScalarGammaResponseMero 0

/-- Critical charge selects the universal unit-gap logarithmic response clock. -/
theorem kerrNewmanChargedScalarPhysicalLogResponseClockMero_criticalCharge_eq_unitGap
    (ell : ℕ) :
    kerrNewmanChargedScalarPhysicalLogResponseClockMero ell
      (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ) =
      kerrNewmanChargedScalarLogResponseClockMero 1 := by
  unfold kerrNewmanChargedScalarPhysicalLogResponseClockMero
  rw [kerrNewmanChargedScalarEffectiveMultipoleGap_criticalCharge]

/-- The physical Wigner--Smith/logarithmic clock at critical charge remains in the DA sector. -/
theorem differentialAlgebraicOver_kerrNewmanChargedScalarPhysicalLogResponseClockMero_criticalCharge
    (ell : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (kerrNewmanChargedScalarPhysicalLogResponseClockMero ell
        (Real.sqrt ((ell : ℝ) * ((ell : ℝ) + 1)) : ℂ)) := by
  rw [kerrNewmanChargedScalarPhysicalLogResponseClockMero_criticalCharge_eq_unitGap]
  exact differentialAlgebraicOver_kerrNewmanChargedScalarLogResponseClockMero_unitGap

end

end GaloisForLFunctions
