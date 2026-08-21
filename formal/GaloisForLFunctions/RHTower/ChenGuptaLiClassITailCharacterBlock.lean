/-
# Chen--Gupta--Li Class-I tail character blocks

Identifies each literal finite CGL shifted-tail dyadic annulus with the
existing character/ordinate Dirichlet-polynomial matrix at ordinate
`-Im(ρ)`. Real decay and exponential smoothing are retained in the exact
finite coefficient vector.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailDyadicIncrements
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- The imaginary complex-power factor at a positive dyadic index is the CGL
character-row phase at the negated ordinate. -/
theorem cglCharacterDyadic_cpow_neg_im_eq_phase
    (N : ℕ) (s : CGLRightHalfPlanePoint) (j : Fin N) :
    (cglCharacterDyadicIndex N j : ℂ) ^ (((-s.1.im : ℝ) : ℂ) * I) =
      cglCharacterDyadicPhase N (-s.1.im) j := by
  have hpos : 0 < (cglCharacterDyadicIndex N j : ℝ) := by
    unfold cglCharacterDyadicIndex
    positivity
  have hne : (cglCharacterDyadicIndex N j : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hlog : Complex.log (cglCharacterDyadicIndex N j : ℂ) =
      ((Real.log (cglCharacterDyadicIndex N j : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hpos.le]
  unfold cglCharacterDyadicPhase
  rw [Complex.cpow_def_of_ne_zero hne, hlog]
  push_cast
  congr 1
  ring

/-- Splits the shifted CGL power into real decay and the exact CGL row phase. -/
theorem cglCharacterDyadic_cpow_neg_eq_re_mul_phase
    (N : ℕ) (s : CGLRightHalfPlanePoint) (j : Fin N) :
    (cglCharacterDyadicIndex N j : ℂ) ^ (-s.1) =
      (cglCharacterDyadicIndex N j : ℂ) ^ (-((s.1.re : ℝ) : ℂ)) *
        cglCharacterDyadicPhase N (-s.1.im) j := by
  have hpos : 0 < (cglCharacterDyadicIndex N j : ℝ) := by
    unfold cglCharacterDyadicIndex
    positivity
  have hne : (cglCharacterDyadicIndex N j : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hsplit : -s.1 = -((s.1.re : ℝ) : ℂ) + ((-s.1.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hsplit, Complex.cpow_add _ _ hne, cglCharacterDyadic_cpow_neg_im_eq_phase]

/-- Exact finite CGL class-I block coefficients: Möbius convolution coefficient,
real shift, and literal exponential smoothing. -/
def cglShiftedTailDyadicCoefficients
    (X N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    (zeroDetectionMobiusCoefficient X (cglCharacterDyadicIndex N j) : ℂ) *
      (cglCharacterDyadicIndex N j : ℂ) ^ (-((s.1.re : ℝ) : ℂ)) *
        Complex.exp (-((cglCharacterDyadicIndex N j : ℝ) * x.1 : ℝ)))

/-- CGL's character-row carrier at the negated imaginary coordinate of the
shifted point. -/
def cglShiftedTailDyadicRow
    (χ : DirichletCharacter ℂ Q) (s : CGLRightHalfPlanePoint) :
    CGLCharacterDyadicRowData Q :=
  { time := -s.1.im
    character := χ }

/-- A weighted shifted-tail term is exactly the corresponding CGL
character/ordinate matrix term. -/
theorem cglShiftedTail_weightedTerm_eq_characterTerm
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (j : Fin N) :
    cglShiftedDetectorTailCoefficient X q χ s (cglCharacterDyadicIndex N j) *
      Complex.exp (-((cglCharacterDyadicIndex N j : ℝ) * x.1 : ℝ)) =
      (cglShiftedTailDyadicCoefficients X N s x) j *
        χ (cglCharacterDyadicIndex N j) * cglCharacterDyadicPhase N (-s.1.im) j := by
  have hindex_ne_one : cglCharacterDyadicIndex N j ≠ 1 := by
    unfold cglCharacterDyadicIndex
    omega
  have htail : cglDetectorTailCoefficient X q χ (cglCharacterDyadicIndex N j) =
      (zeroDetectionMobiusCoefficient X (cglCharacterDyadicIndex N j) : ℂ) *
        χ (cglCharacterDyadicIndex N j) := by
    unfold cglDetectorTailCoefficient
    rw [cglTruncatedMobiusTwist_convolution_character_eq_mobiusCoefficient_all]
    simp [cglUnitCoefficient, hindex_ne_one]
  rw [cglShiftedDetectorTailCoefficient, htail, cglCharacterDyadic_cpow_neg_eq_re_mul_phase]
  simp only [cglShiftedTailDyadicCoefficients]
  ring

/-- The CGL character-row polynomial is exactly the literal finite weighted
shifted-tail block. -/
theorem cglCharacterDyadicPolynomial_eq_shiftedTailBlock
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    cglCharacterDyadicPolynomial N (q + 1) (cglShiftedTailDyadicRow χ s)
      (cglShiftedTailDyadicCoefficients X N s x) =
      ∑ j : Fin N, cglShiftedDetectorTailCoefficient X q χ s
        (cglCharacterDyadicIndex N j) *
          Complex.exp (-((cglCharacterDyadicIndex N j : ℝ) * x.1 : ℝ)) := by
  unfold cglCharacterDyadicPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  exact (cglShiftedTail_weightedTerm_eq_characterTerm X N q χ s x j).symm

/-- A canonical CGL dyadic tail increment is exactly its finite
character/ordinate Dirichlet polynomial. -/
theorem cglShiftedDetectorTailDyadicIncrement_eq_characterPolynomial
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (L : ℕ) :
    cglShiftedDetectorTailDyadicIncrement X q χ s x L =
      cglCharacterDyadicPolynomial (2 ^ L) (q + 1) (cglShiftedTailDyadicRow χ s)
        (cglShiftedTailDyadicCoefficients X (2 ^ L) s x) := by
  rw [cglShiftedDetectorTailDyadicIncrement_eq_block,
    cglCharacterDyadicPolynomial_eq_shiftedTailBlock]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj, cglCharacterDyadicIndex]

end RHTower
