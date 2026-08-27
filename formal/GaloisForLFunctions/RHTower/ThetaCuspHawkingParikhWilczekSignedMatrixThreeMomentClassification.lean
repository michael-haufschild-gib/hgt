import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekPositiveMatrixCrossGradeClassification

/-!
# Parikh--Wilczek signed matrix three-moment classification

The residual of every PW Borel grade lies in the affine span of one common spectral coordinate and
the fixed shift `4k(k+1)`.  Consequently every finite signed matrix cross-grade interaction depends
on only three matrix moments, and its exact zero locus is the reflection wall together with roots of
one real quadratic.

This rank-two collapse also exposes a universal three-grade dark vector `(2,-3,1)`.  Its outer
product is nonzero, symmetric, and positive semidefinite as a quadratic form, yet its signed entries
annihilate the recoil signal identically.  Thus positive semidefiniteness alone cannot rescue the
finite signed-matrix route; entrywise positivity in the preceding classification is essential.

`[NEW] [CLASSIFICATION] [EXACT DARK SECTOR] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Common scalar spectral coordinate carried by every Borel-grade residual. -/
def schwarzschildParikhWilczekBorelSpectralCoordinate (s : ℂ) : ℝ :=
  s.re * (1 - s.re) + s.im ^ 2 + 1

/-- Grade-dependent shift complementary to the common spectral coordinate. -/
def schwarzschildParikhWilczekBorelGradeShift (k : ℕ) : ℝ :=
  4 * (k : ℝ) * ((k : ℝ) + 1)

/-- Exact affine-rank-two decomposition of every grade residual. -/
theorem schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift
    (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekBorelGradeResidual s k =
      schwarzschildParikhWilczekBorelSpectralCoordinate s +
        schwarzschildParikhWilczekBorelGradeShift k := by
  rw [schwarzschildParikhWilczekBorelGradeResidual,
    schwarzschildParikhWilczekBorelSpectralCoordinate,
    schwarzschildParikhWilczekBorelGradeShift]
  ring

/-- Zeroth signed matrix moment. -/
def schwarzschildParikhWilczekSignedMatrixMomentZero
    {N : ℕ} (M : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j

/-- First signed matrix moment against the sum of grade shifts. -/
def schwarzschildParikhWilczekSignedMatrixMomentOne
    {N : ℕ} (M : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j *
    (schwarzschildParikhWilczekBorelGradeShift (i : ℕ) +
      schwarzschildParikhWilczekBorelGradeShift (j : ℕ))

/-- Second signed matrix moment against the product of grade shifts. -/
def schwarzschildParikhWilczekSignedMatrixMomentTwo
    {N : ℕ} (M : Fin N → Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, M i j *
    schwarzschildParikhWilczekBorelGradeShift (i : ℕ) *
      schwarzschildParikhWilczekBorelGradeShift (j : ℕ)

/-- Quadratic residual polynomial determined by the three signed matrix moments. -/
def schwarzschildParikhWilczekSignedMatrixResidualPolynomial
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) : ℝ :=
  schwarzschildParikhWilczekSignedMatrixMomentZero M *
      schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2 +
    schwarzschildParikhWilczekSignedMatrixMomentOne M *
      schwarzschildParikhWilczekBorelSpectralCoordinate s +
    schwarzschildParikhWilczekSignedMatrixMomentTwo M

/-- Every finite signed matrix residual energy is its three-moment quadratic. -/
theorem schwarzschildParikhWilczekMatrixResidualEnergy_three_moment
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) :
    schwarzschildParikhWilczekMatrixResidualEnergy M s =
      schwarzschildParikhWilczekSignedMatrixResidualPolynomial M s := by
  rw [schwarzschildParikhWilczekMatrixResidualEnergy,
    schwarzschildParikhWilczekSignedMatrixResidualPolynomial,
    schwarzschildParikhWilczekSignedMatrixMomentZero,
    schwarzschildParikhWilczekSignedMatrixMomentOne,
    schwarzschildParikhWilczekSignedMatrixMomentTwo]
  simp_rw [schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift]
  apply Eq.symm
  calc
    _ = ∑ i, ∑ j,
        (M i j * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2 +
          M i j *
            (schwarzschildParikhWilczekBorelGradeShift (i : ℕ) +
              schwarzschildParikhWilczekBorelGradeShift (j : ℕ)) *
                schwarzschildParikhWilczekBorelSpectralCoordinate s +
          M i j * schwarzschildParikhWilczekBorelGradeShift (i : ℕ) *
            schwarzschildParikhWilczekBorelGradeShift (j : ℕ)) := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Full signed cross-grade energy is wall squared times the three-moment quadratic. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_three_moment
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy M s =
      schwarzschildParikhWilczekBorelWallFactor s ^ 2 *
        schwarzschildParikhWilczekSignedMatrixResidualPolynomial M s := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_factorization,
    schwarzschildParikhWilczekMatrixResidualEnergy_three_moment]

/-- On Xi support, exact zero locus is wall union residual-quadratic roots. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff_wall_or_residual
    {N : ℕ} (M : Fin N → Fin N → ℝ) (rho : XiDivisorSupport) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy M (rho : ℂ) = 0 ↔
      (rho : ℂ).re = 1 / 2 ∨
        schwarzschildParikhWilczekSignedMatrixResidualPolynomial M (rho : ℂ) = 0 := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_three_moment]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hwallSq | hres
    · left
      have hwall := (sq_eq_zero_iff).mp hwallSq
      rw [schwarzschildParikhWilczekBorelWallFactor] at hwall
      rcases mul_eq_zero.mp hwall with him | hcenter
      · exact False.elim (xi_divisor_support_im_ne_zero rho (by linarith))
      · linarith
    · exact Or.inr hres
  · rintro (hre | hres)
    · rw [schwarzschildParikhWilczekBorelWallFactor, hre]
      norm_num
    · rw [hres, mul_zero]

/-- Residual polynomial is identically zero exactly when all three moments vanish. -/
theorem schwarzschildParikhWilczekSignedMatrixResidualPolynomial_eq_zero_forall_iff
    {N : ℕ} (M : Fin N → Fin N → ℝ) :
    (∀ s : ℂ,
      schwarzschildParikhWilczekSignedMatrixResidualPolynomial M s = 0) ↔
      schwarzschildParikhWilczekSignedMatrixMomentZero M = 0 ∧
        schwarzschildParikhWilczekSignedMatrixMomentOne M = 0 ∧
          schwarzschildParikhWilczekSignedMatrixMomentTwo M = 0 := by
  constructor
  · intro h
    have h1 := h 0
    have h2 := h I
    have h5 := h (2 * I)
    norm_num [schwarzschildParikhWilczekSignedMatrixResidualPolynomial,
      schwarzschildParikhWilczekBorelSpectralCoordinate] at h1 h2 h5
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩ s
    simp [schwarzschildParikhWilczekSignedMatrixResidualPolynomial, h0, h1, h2]

/-- Full cross-grade energy is identically zero exactly on the three-moment kernel. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_forall_iff_moments
    {N : ℕ} (M : Fin N → Fin N → ℝ) :
    (∀ s : ℂ, schwarzschildParikhWilczekMatrixCrossGradeEnergy M s = 0) ↔
      schwarzschildParikhWilczekSignedMatrixMomentZero M = 0 ∧
        schwarzschildParikhWilczekSignedMatrixMomentOne M = 0 ∧
          schwarzschildParikhWilczekSignedMatrixMomentTwo M = 0 := by
  constructor
  · intro h
    have h2 := h I
    have h5 := h (2 * I)
    have h10 := h (3 * I)
    rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_three_moment] at h2 h5 h10
    norm_num [schwarzschildParikhWilczekBorelWallFactor,
      schwarzschildParikhWilczekSignedMatrixResidualPolynomial,
      schwarzschildParikhWilczekBorelSpectralCoordinate] at h2 h5 h10
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩ s
    rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_three_moment]
    simp [schwarzschildParikhWilczekSignedMatrixResidualPolynomial, h0, h1, h2]

/-- Universal three-grade signed dark relation. -/
theorem schwarzschildParikhWilczekBorelRecoilHolonomy_im_three_grade_dark
    (s : ℂ) :
    2 * (schwarzschildParikhWilczekBorelRecoilHolonomy s 0).im -
      3 * (schwarzschildParikhWilczekBorelRecoilHolonomy s 1).im +
        (schwarzschildParikhWilczekBorelRecoilHolonomy s 2).im = 0 := by
  simp_rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization,
    schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift]
  norm_num [schwarzschildParikhWilczekBorelGradeShift]
  ring

/-- Minimal three-grade dark weight `(2,-3,1)`. -/
def schwarzschildParikhWilczekThreeGradeDarkWeight : Fin 3 → ℝ :=
  ![2, -3, 1]

/-- Symmetric rank-one outer product of the minimal dark weight. -/
def schwarzschildParikhWilczekThreeGradeDarkMatrix : Fin 3 → Fin 3 → ℝ :=
  fun i j => schwarzschildParikhWilczekThreeGradeDarkWeight i *
    schwarzschildParikhWilczekThreeGradeDarkWeight j

/-- The explicit dark matrix is symmetric. -/
theorem schwarzschildParikhWilczekThreeGradeDarkMatrix_symmetric
    (i j : Fin 3) :
    schwarzschildParikhWilczekThreeGradeDarkMatrix i j =
      schwarzschildParikhWilczekThreeGradeDarkMatrix j i := by
  simp [schwarzschildParikhWilczekThreeGradeDarkMatrix, mul_comm]

/-- The explicit dark matrix is nonzero. -/
theorem schwarzschildParikhWilczekThreeGradeDarkMatrix_ne_zero :
    schwarzschildParikhWilczekThreeGradeDarkMatrix ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [schwarzschildParikhWilczekThreeGradeDarkMatrix,
    schwarzschildParikhWilczekThreeGradeDarkWeight] at h00

/-- Entrywise positivity fails: one explicit dark-matrix entry is `-6`. -/
theorem schwarzschildParikhWilczekThreeGradeDarkMatrix_has_negative_entry :
    schwarzschildParikhWilczekThreeGradeDarkMatrix 0 1 = -6 := by
  norm_num [schwarzschildParikhWilczekThreeGradeDarkMatrix,
    schwarzschildParikhWilczekThreeGradeDarkWeight]

/-- Any finite real rank-one quadratic form is a square. -/
theorem finite_rankOneQuadraticForm_eq_sq
    {N : ℕ} (w v : Fin N → ℝ) :
    (∑ i, ∑ j, v i * (w i * w j) * v j) = (∑ i, v i * w i) ^ 2 := by
  calc
    (∑ i, ∑ j, v i * (w i * w j) * v j) =
        ∑ i, ∑ j, (v i * w i) * (v j * w j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ i, v i * w i) * (∑ j, v j * w j) :=
      (Finset.sum_mul_sum Finset.univ Finset.univ
        (fun i => v i * w i) (fun j => v j * w j)).symm
    _ = _ := by ring

/-- Despite signed entries, the explicit dark matrix has nonnegative quadratic form. -/
theorem schwarzschildParikhWilczekThreeGradeDarkMatrix_quadraticForm_nonneg
    (v : Fin 3 → ℝ) :
    0 ≤ ∑ i, ∑ j,
      v i * schwarzschildParikhWilczekThreeGradeDarkMatrix i j * v j := by
  rw [show (∑ i, ∑ j,
      v i * schwarzschildParikhWilczekThreeGradeDarkMatrix i j * v j) =
      (∑ i, v i * schwarzschildParikhWilczekThreeGradeDarkWeight i) ^ 2 by
        simpa only [schwarzschildParikhWilczekThreeGradeDarkMatrix] using
          finite_rankOneQuadraticForm_eq_sq
            schwarzschildParikhWilczekThreeGradeDarkWeight v]
  positivity

/-- The dark weight annihilates the full Borel recoil reporter for every spectral parameter. -/
theorem schwarzschildParikhWilczekThreeGradeDarkReporter_zero (s : ℂ) :
    ∑ k, schwarzschildParikhWilczekThreeGradeDarkWeight k *
      (schwarzschildParikhWilczekBorelRecoilHolonomy s (k : ℕ)).im = 0 := by
  have hexpand : (∑ k : Fin 3, schwarzschildParikhWilczekThreeGradeDarkWeight k *
      (schwarzschildParikhWilczekBorelRecoilHolonomy s (k : ℕ)).im) =
      2 * (schwarzschildParikhWilczekBorelRecoilHolonomy s 0).im -
        3 * (schwarzschildParikhWilczekBorelRecoilHolonomy s 1).im +
          (schwarzschildParikhWilczekBorelRecoilHolonomy s 2).im := by
    simp [Fin.sum_univ_succ, schwarzschildParikhWilczekThreeGradeDarkWeight]
    ring
  rw [hexpand]
  exact schwarzschildParikhWilczekBorelRecoilHolonomy_im_three_grade_dark s

/-- The nonzero symmetric positive-semidefinite signed dark matrix has identically zero energy. -/
theorem schwarzschildParikhWilczekThreeGradeDarkMatrix_energy_zero (s : ℂ) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy
      schwarzschildParikhWilczekThreeGradeDarkMatrix s = 0 := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy]
  simp_rw [schwarzschildParikhWilczekThreeGradeDarkMatrix]
  calc
    (∑ i, ∑ j,
        schwarzschildParikhWilczekThreeGradeDarkWeight i *
            schwarzschildParikhWilczekThreeGradeDarkWeight j *
          (schwarzschildParikhWilczekBorelRecoilHolonomy s (i : ℕ)).im *
            (schwarzschildParikhWilczekBorelRecoilHolonomy s (j : ℕ)).im) =
      (∑ i, schwarzschildParikhWilczekThreeGradeDarkWeight i *
        (schwarzschildParikhWilczekBorelRecoilHolonomy s (i : ℕ)).im) ^ 2 := by
          rw [← finite_rankOneQuadraticForm_eq_sq]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = 0 := by rw [schwarzschildParikhWilczekThreeGradeDarkReporter_zero]; norm_num

end

end RHTower
