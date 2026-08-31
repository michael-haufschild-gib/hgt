import GaloisForLFunctions.RHTower.SelbergGeneralSineRecurrence

/-!
# Canonical premise-free Selberg cusp root law

The general-rank cusp root law needs positive degree, a height above every selected Gamma pole
line, and a base point off the asymmetric sine exceptional lattice.  For a nonempty Gamma
presentation none of these is extra mathematical data: positive degree follows from positivity of
the Gamma slopes, and the purely imaginary point one unit above `gammaTailHeight` has every affine
Gamma argument, hence every sine argument, genuinely nonreal.
-/

open Complex Filter Set
open scoped BigOperators Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A complex sine with nonzero imaginary part cannot vanish. -/
theorem complexSin_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.sin z ≠ 0 := by
  intro hzero
  have hpositive : 0 < Real.sinh |z.im| := by
    rw [Real.sinh_pos_iff]
    exact abs_pos.mpr hz
  have hbound := sinh_abs_im_le_norm_sin z
  rw [hzero, norm_zero] at hbound
  linarith

/-- Canonical height one unit above the presentation-dependent Gamma tail. -/
def SelbergGammaData.canonicalCuspHeight (G : SelbergGammaData) : ℝ :=
  G.gammaTailHeight + 1

theorem SelbergGammaData.canonicalCuspHeight_pos (G : SelbergGammaData) :
    0 < G.canonicalCuspHeight := by
  unfold SelbergGammaData.canonicalCuspHeight
  linarith [G.gammaTailHeight_nonneg]

theorem SelbergGammaData.gammaTailHeight_lt_abs_canonicalCuspHeight
    (G : SelbergGammaData) :
    G.gammaTailHeight < |G.canonicalCuspHeight| := by
  rw [abs_of_pos G.canonicalCuspHeight_pos]
  unfold SelbergGammaData.canonicalCuspHeight
  linarith

/-- Canonical purely imaginary base point above every Gamma-factor pole line. -/
def SelbergGammaData.canonicalCuspBasePoint (G : SelbergGammaData) : ℂ :=
  selbergVerticalPoint 0 G.canonicalCuspHeight

theorem SelbergGammaData.canonicalCuspBasePoint_im (G : SelbergGammaData) :
    G.canonicalCuspBasePoint.im = G.canonicalCuspHeight := by
  simp [SelbergGammaData.canonicalCuspBasePoint, selbergVerticalPoint]

theorem SelbergGammaData.gammaTailHeight_lt_abs_canonicalCuspBasePoint_im
    (G : SelbergGammaData) :
    G.gammaTailHeight < |G.canonicalCuspBasePoint.im| := by
  rw [G.canonicalCuspBasePoint_im]
  exact G.gammaTailHeight_lt_abs_canonicalCuspHeight

/-- Every sine factor is nonzero at the canonical high imaginary point. -/
theorem SelbergGammaData.sin_affine_canonicalCuspBasePoint_ne_zero
    (G : SelbergGammaData) (j : Fin G.rank) :
    Complex.sin (Real.pi * ((G.lambda j : ℂ) * G.canonicalCuspBasePoint + G.mu j)) ≠ 0 := by
  apply complexSin_ne_zero_of_im_ne_zero
  have htail : G.verticalTailCondition G.canonicalCuspHeight :=
    G.verticalTailCondition_of_gammaTailHeight_lt_abs
      G.gammaTailHeight_lt_abs_canonicalCuspHeight
  have harg :
      ((G.lambda j : ℂ) * G.canonicalCuspBasePoint + G.mu j).im ≠ 0 := by
    exact G.verticalArgument_im_ne_zero_of_tail (sigma := 0) htail j
  simpa [Complex.mul_im] using mul_ne_zero Real.pi_ne_zero harg

/-- Canonical high imaginary point lies off the complete asymmetric sine exceptional lattice. -/
theorem SelbergGammaData.asymmetricS_canonicalCuspBasePoint_ne_zero
    (G : SelbergGammaData) :
    G.asymmetricS G.canonicalCuspBasePoint ≠ 0 := by
  unfold SelbergGammaData.asymmetricS
  apply mul_ne_zero
  · norm_num
  · exact Finset.prod_ne_zero_iff.mpr fun j _ ↦
      G.sin_affine_canonicalCuspBasePoint_ne_zero j

/-- Selberg-class data with a nonempty Gamma presentation.  Positive degree is derived. -/
abbrev PositiveRankSelbergClass :=
  {F : SelbergClass // 0 < F.gammaData.rank}

/-- Premise-free canonical cusp-spectrum radius law for every positive-rank Selberg class. -/
theorem PositiveRankSelbergClass.canonicalCuspRootLaw
    (F : PositiveRankSelbergClass) :
    limsup (fun k : ℕ =>
        (‖F.1 (F.1.gammaData.canonicalCuspBasePoint -
            (k : ℂ) / (F.1.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^
          (1 / (k : ℝ))) atTop
      = F.1.gammaData.conductor ^ (1 / F.1.gammaData.degree) /
        (2 * Real.pi * F.1.gammaData.degree) := by
  exact F.1.limsup_norm_shift_rpow_inv_of_height_of_asymmetricS_ne_zero
    (F.1.gammaData.degree_pos_of_rank_pos F.2)
    F.1.gammaData.gammaTailHeight_lt_abs_canonicalCuspBasePoint_im
    F.1.gammaData.asymmetricS_canonicalCuspBasePoint_ne_zero

end

end RHTower
