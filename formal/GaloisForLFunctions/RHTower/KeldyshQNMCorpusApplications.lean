import GaloisForLFunctions.HTGeometry.KeldyshQNMAlgebra
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalBlackHoleQNMIncidence
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicLeftConnectionCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingHBProjectivelyNormalizedQNMResponseNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment

/-!
# Keldysh QNM applications in the black-hole corpus

Mechanical applications of the finite-rank identities extracted from
Besson--Jaramillo, arXiv:2412.02793v2, to exact structures already formalized
in `RHTower`.

Results include quadratic QNM frequency sums, shadow behavior, damping closure,
Hankel-rank bounds for sampled nonlinear signals, an exact BM biorthogonal
resolution, and unconditional unit-rescaling laws for the existing normalized
HB QNM response. No analytic completeness, Weyl-law, or convergence conjecture
is introduced.
-/

open Complex Real Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Equal-overtone cross-branch frequency generated at quadratic order. -/
def thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency
    (n : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n z +
    thetaCuspHawkingTopologicalBlackHoleQNMMinus n z

theorem thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_eq
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency n z =
      -2 * Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  ring

theorem thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_shadow
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency n
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency n z := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_shadow,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus_shadow]
  exact add_comm _ _

theorem thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_re
    (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency n z).re = 0 := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_eq]
  simp

theorem thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_im
    (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency n z).im =
      -2 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMixedSecondOrderFrequency_eq]
  simp

/-- Cross-branch second-order frequency for independently chosen overtones. -/
def thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency
    (n m : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n z +
    thetaCuspHawkingTopologicalBlackHoleQNMMinus m z

/-- Every cross-branch combination loses angular/Xi data, even across distinct overtones. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency_eq
    (n m : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency n m z =
      -Complex.I *
        (thetaCuspHawkingTopologicalBlackHoleConformalDecay n +
          thetaCuspHawkingTopologicalBlackHoleConformalDecay m) := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  ring

theorem thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency_shadow
    (n m : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency n m
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency n m z := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency_eq,
    thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency_eq]

/-- Same-sign positive-branch quadratic combination frequency. -/
def thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency
    (n m : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n z +
    thetaCuspHawkingTopologicalBlackHoleQNMPlus m z

/-- Same-sign negative-branch quadratic combination frequency. -/
def thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency
    (n m : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMMinus n z +
    thetaCuspHawkingTopologicalBlackHoleQNMMinus m z

theorem thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency_shadow
    (n m : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency n m
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency n m z := by
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_shadow]

/-- Quadratic `++` combinations stay strictly damped on every Xi copy. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMPlusPlus_xi_im_lt_zero
    (n m : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency
      n m (xiSpectralPoint q)).im < 0 := by
  have hstrip := abs_xiSpectralPoint_im_lt_half q
  rw [abs_lt] at hstrip
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency,
    add_im, thetaCuspHawkingTopologicalBlackHoleQNMPlus_im,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_im]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  norm_num at hstrip ⊢
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Quadratic `--` combinations stay strictly damped on every Xi copy. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMMinusMinus_xi_im_lt_zero
    (n m : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency
      n m (xiSpectralPoint q)).im < 0 := by
  have hstrip := abs_xiSpectralPoint_im_lt_half q
  rw [abs_lt] at hstrip
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency,
    add_im, thetaCuspHawkingTopologicalBlackHoleQNMMinus_im,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus_im]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  norm_num at hstrip ⊢
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Mixed quadratic combinations stay strictly damped on every Xi copy. -/
theorem thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertone_xi_im_lt_zero
    (n m : ℕ) (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency
      n m (xiSpectralPoint q)).im < 0 := by
  have hstrip := abs_xiSpectralPoint_im_lt_half q
  rw [abs_lt] at hstrip
  rw [thetaCuspHawkingTopologicalBlackHoleQNMCrossOvertoneFrequency,
    add_im, thetaCuspHawkingTopologicalBlackHoleQNMPlus_im,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus_im]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  norm_num at hstrip ⊢
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem thetaCuspHawkingTopologicalBlackHoleSecondOrderSameBranchDifference
    (n m : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency n m z -
        thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency n m z =
      4 * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMPlusPlusSecondOrderFrequency
    thetaCuspHawkingTopologicalBlackHoleQNMMinusMinusSecondOrderFrequency
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  ring

/-- Sampled packet of positive-branch topological-black-hole QNMs. -/
def thetaCuspHawkingTopologicalBlackHoleQNMPlusSequence {d : ℕ}
    (amplitude : Fin d → ℂ) (z : ℂ) : ℕ → ℂ :=
  GaloisForLFunctions.HTGeometry.finiteQNMSequence amplitude
    (fun i => thetaCuspHawkingTopologicalBlackHoleQNMPlus i.val z)

/-- Sampled packet of negative-branch topological-black-hole QNMs. -/
def thetaCuspHawkingTopologicalBlackHoleQNMMinusSequence {d : ℕ}
    (amplitude : Fin d → ℂ) (z : ℂ) : ℕ → ℂ :=
  GaloisForLFunctions.HTGeometry.finiteQNMSequence amplitude
    (fun i => thetaCuspHawkingTopologicalBlackHoleQNMMinus i.val z)

theorem thetaCuspHawkingTopologicalBlackHoleQNMPlus_quadratic_hankel_det_eq_zero
    {d : ℕ} (amplitude : Fin d → ℂ) (z : ℂ) :
    (HTGeometry.algebraicHankelMatrix
      (fun n => thetaCuspHawkingTopologicalBlackHoleQNMPlusSequence amplitude z n ^ 2)
      (d * d + 1)).det = 0 := by
  exact GaloisForLFunctions.HTGeometry.finiteQNMSequence_quadratic_hankel_det_eq_zero
    amplitude (fun i => thetaCuspHawkingTopologicalBlackHoleQNMPlus i.val z)

theorem thetaCuspHawkingTopologicalBlackHoleQNMMinus_quadratic_hankel_det_eq_zero
    {d : ℕ} (amplitude : Fin d → ℂ) (z : ℂ) :
    (HTGeometry.algebraicHankelMatrix
      (fun n => thetaCuspHawkingTopologicalBlackHoleQNMMinusSequence amplitude z n ^ 2)
      (d * d + 1)).det = 0 := by
  exact GaloisForLFunctions.HTGeometry.finiteQNMSequence_quadratic_hankel_det_eq_zero
    amplitude (fun i => thetaCuspHawkingTopologicalBlackHoleQNMMinus i.val z)

/-- Regular horizon mode as its two outer AdS coefficients. -/
def d4BMXiPlusPlusRegularOuterMode (n : ℕ) (q : XiZeroCopy) : Fin 2 → ℂ :=
  ![d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q),
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q)]

/-- Complementary horizon mode as its two outer AdS coefficients. -/
def d4BMXiPlusPlusComplementaryOuterMode (n : ℕ) (q : XiZeroCopy) : Fin 2 → ℂ :=
  ![d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q),
    d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q)]

/-- Regular Keldysh left comode on the exact BM two-channel outer-data space. -/
def d4BMXiPlusPlusRegularKeldyshComode (n : ℕ) (q : XiZeroCopy) :
    (Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun x := d4BMXiPlusPlusRegularLeftConnectionCovector n q (x 0) (x 1)
  map_add' x y := by
    unfold d4BMXiPlusPlusRegularLeftConnectionCovector
    dsimp only
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    unfold d4BMXiPlusPlusRegularLeftConnectionCovector
    dsimp only
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Complementary Keldysh left comode on the exact BM outer-data space. -/
def d4BMXiPlusPlusComplementaryKeldyshComode (n : ℕ) (q : XiZeroCopy) :
    (Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun x := d4BMXiPlusPlusComplementaryLeftConnectionCovector n q (x 0) (x 1)
  map_add' x y := by
    unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
    dsimp only
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
    dsimp only
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The regular BM left covector is reconstructed from its two coordinate values. -/
theorem d4BMXiPlusPlusRegularLeftConnectionCovector_basis_expansion
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q source response =
      d4BMXiPlusPlusRegularLeftConnectionCovector n q 1 0 * source +
        d4BMXiPlusPlusRegularLeftConnectionCovector n q 0 1 * response := by
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
  dsimp only
  ring

/-- The complementary BM left covector is reconstructed from its coordinate values. -/
theorem d4BMXiPlusPlusComplementaryLeftConnectionCovector_basis_expansion
    (n : ℕ) (q : XiZeroCopy) (source response : ℂ) :
    d4BMXiPlusPlusComplementaryLeftConnectionCovector n q source response =
      d4BMXiPlusPlusComplementaryLeftConnectionCovector n q 1 0 * source +
        d4BMXiPlusPlusComplementaryLeftConnectionCovector n q 0 1 * response := by
  unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
  dsimp only
  ring

/-- BM connection columns assembled as a two-mode Keldysh basis matrix. -/
def d4BMXiPlusPlusConnectionMatrix
    (n : ℕ) (q : XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 then
      if j = 0 then
        d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q)
      else
        d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q)
    else
      if j = 0 then
        d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q)
      else
        d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
          (d4BMXiMixedHorizonAngularMomentum q)

/-- Rows of BM left covector coordinates, assembled as inverse modal matrix. -/
def d4BMXiPlusPlusLeftComodeMatrix
    (n : ℕ) (q : XiZeroCopy) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i = 0 then
      if j = 0 then d4BMXiPlusPlusRegularLeftConnectionCovector n q 1 0
      else d4BMXiPlusPlusRegularLeftConnectionCovector n q 0 1
    else
      if j = 0 then d4BMXiPlusPlusComplementaryLeftConnectionCovector n q 1 0
      else d4BMXiPlusPlusComplementaryLeftConnectionCovector n q 0 1

/-- Exact inverse law for the BM left/right modal matrices. -/
theorem d4BMXiPlusPlusLeftComodeMatrix_mul_connectionMatrix
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusLeftComodeMatrix n q * d4BMXiPlusPlusConnectionMatrix n q = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [d4BMXiPlusPlusLeftComodeMatrix, d4BMXiPlusPlusConnectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
    rw [← d4BMXiPlusPlusRegularLeftConnectionCovector_basis_expansion]
    exact d4BMXiPlusPlusRegularLeftConnectionCovector_regular_eq_one n q
  · simp [d4BMXiPlusPlusLeftComodeMatrix, d4BMXiPlusPlusConnectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
    rw [← d4BMXiPlusPlusRegularLeftConnectionCovector_basis_expansion]
    exact d4BMXiPlusPlusRegularLeftConnectionCovector_complementary_eq_zero n q
  · simp [d4BMXiPlusPlusLeftComodeMatrix, d4BMXiPlusPlusConnectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
    rw [← d4BMXiPlusPlusComplementaryLeftConnectionCovector_basis_expansion]
    exact d4BMXiPlusPlusComplementaryLeftConnectionCovector_regular_eq_zero n q
  · simp [d4BMXiPlusPlusLeftComodeMatrix, d4BMXiPlusPlusConnectionMatrix,
      Matrix.mul_apply, Fin.sum_univ_two]
    rw [← d4BMXiPlusPlusComplementaryLeftConnectionCovector_basis_expansion]
    exact d4BMXiPlusPlusComplementaryLeftConnectionCovector_complementary_eq_one n q

/-- Exact BM connection matrix as an invertible Keldysh modal basis. -/
def d4BMXiPlusPlusKeldyshBasis (n : ℕ) (q : XiZeroCopy) :
    GaloisForLFunctions.HTGeometry.KeldyshGL 2 :=
  Units.mk (d4BMXiPlusPlusConnectionMatrix n q)
    (d4BMXiPlusPlusLeftComodeMatrix n q)
    (mul_eq_one_comm.mpr (d4BMXiPlusPlusLeftComodeMatrix_mul_connectionMatrix n q))
    (d4BMXiPlusPlusLeftComodeMatrix_mul_connectionMatrix n q)

/-- BM Keldysh generator diagonalizes on the exact regular/complementary connection basis. -/
theorem d4BMXiPlusPlusKeldyshGenerator_mul_connectionMatrix
    (n : ℕ) (q : XiZeroCopy) (omega : Fin 2 → ℂ) :
    GaloisForLFunctions.HTGeometry.keldyshGenerator
        (d4BMXiPlusPlusKeldyshBasis n q) omega *
        d4BMXiPlusPlusConnectionMatrix n q =
      d4BMXiPlusPlusConnectionMatrix n q * Matrix.diagonal omega := by
  exact GaloisForLFunctions.HTGeometry.keldyshGenerator_mul_basis
    (d4BMXiPlusPlusKeldyshBasis n q) omega

/-- Totalized Keldysh resolvent of the exact two-channel BM connection system. -/
def d4BMXiPlusPlusKeldyshResolvent
    (n : ℕ) (q : XiZeroCopy) (omega : Fin 2 → ℂ) (z : ℂ)
    (outer : Fin 2 → ℂ) : Fin 2 → ℂ :=
  GaloisForLFunctions.HTGeometry.keldyshResolvent
    (d4BMXiPlusPlusKeldyshBasis n q) omega z outer

/-- Exact BM resolvent expansion into its two rank-one pole residues. -/
theorem d4BMXiPlusPlusKeldyshResolvent_apply
    (n : ℕ) (q : XiZeroCopy) (omega : Fin 2 → ℂ) (z : ℂ)
    (outer : Fin 2 → ℂ) (r : Fin 2) :
    d4BMXiPlusPlusKeldyshResolvent n q omega z outer r =
      ∑ i, (z - omega i)⁻¹ *
        GaloisForLFunctions.HTGeometry.keldyshModeProjector
          (d4BMXiPlusPlusKeldyshBasis n q) i outer r := by
  exact GaloisForLFunctions.HTGeometry.keldyshResolvent_apply
    (d4BMXiPlusPlusKeldyshBasis n q) omega z outer r

/-- The two BM Keldysh residues sum to the identity on outer data. -/
theorem sum_d4BMXiPlusPlusKeldyshModeProjector
    (n : ℕ) (q : XiZeroCopy) (outer : Fin 2 → ℂ) :
    ∑ i, GaloisForLFunctions.HTGeometry.keldyshModeProjector
      (d4BMXiPlusPlusKeldyshBasis n q) i outer = outer := by
  exact GaloisForLFunctions.HTGeometry.sum_keldyshModeProjector
    (d4BMXiPlusPlusKeldyshBasis n q) outer

@[simp] theorem d4BMXiPlusPlusRegularKeldyshComode_regular
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusRegularKeldyshComode n q
        (d4BMXiPlusPlusRegularOuterMode n q) = 1 := by
  exact d4BMXiPlusPlusRegularLeftConnectionCovector_regular_eq_one n q

@[simp] theorem d4BMXiPlusPlusRegularKeldyshComode_complementary
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusRegularKeldyshComode n q
        (d4BMXiPlusPlusComplementaryOuterMode n q) = 0 := by
  exact d4BMXiPlusPlusRegularLeftConnectionCovector_complementary_eq_zero n q

@[simp] theorem d4BMXiPlusPlusComplementaryKeldyshComode_regular
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryKeldyshComode n q
        (d4BMXiPlusPlusRegularOuterMode n q) = 0 := by
  exact d4BMXiPlusPlusComplementaryLeftConnectionCovector_regular_eq_zero n q

@[simp] theorem d4BMXiPlusPlusComplementaryKeldyshComode_complementary
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryKeldyshComode n q
        (d4BMXiPlusPlusComplementaryOuterMode n q) = 1 := by
  exact d4BMXiPlusPlusComplementaryLeftConnectionCovector_complementary_eq_one n q

/-- Sum of the two exact Keldysh rank-one projectors. -/
def d4BMXiPlusPlusKeldyshReconstruction
    (n : ℕ) (q : XiZeroCopy) (outer : Fin 2 → ℂ) : Fin 2 → ℂ :=
  d4BMXiPlusPlusRegularKeldyshComode n q outer •
      d4BMXiPlusPlusRegularOuterMode n q +
    d4BMXiPlusPlusComplementaryKeldyshComode n q outer •
      d4BMXiPlusPlusComplementaryOuterMode n q

/-- Exact rank-one Keldysh resolution of every two-channel BM outer datum. -/
theorem d4BMXiPlusPlusKeldyshReconstruction_eq
    (n : ℕ) (q : XiZeroCopy) (outer : Fin 2 → ℂ) :
    d4BMXiPlusPlusKeldyshReconstruction n q outer = outer := by
  funext i
  fin_cases i
  · exact d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_source n q (outer 0) (outer 1)
  · exact d4BMXiPlusPlusLeftConnectionCovectors_reconstruct_response n q (outer 0) (outer 1)

/-- The regular Keldysh rank-one projector is idempotent. -/
theorem d4BMXiPlusPlusRegularKeldyshProjector_idempotent
    (n : ℕ) (q : XiZeroCopy) (outer : Fin 2 → ℂ) :
    let P := fun x => d4BMXiPlusPlusRegularKeldyshComode n q x •
      d4BMXiPlusPlusRegularOuterMode n q
    P (P outer) = P outer := by
  dsimp only
  rw [map_smul, d4BMXiPlusPlusRegularKeldyshComode_regular]
  simp

/-- Regular and complementary Keldysh projectors annihilate one another. -/
theorem d4BMXiPlusPlusKeldyshProjectors_cross_zero
    (n : ℕ) (q : XiZeroCopy) (outer : Fin 2 → ℂ) :
    d4BMXiPlusPlusRegularKeldyshComode n q
        (d4BMXiPlusPlusComplementaryKeldyshComode n q outer •
          d4BMXiPlusPlusComplementaryOuterMode n q) •
      d4BMXiPlusPlusRegularOuterMode n q = 0 := by
  rw [map_smul, d4BMXiPlusPlusRegularKeldyshComode_complementary]
  simp

/-- Unit rescaling law for the corpus's bilinear QNM coefficient, with no
nondegeneracy premise. Lean's totalized division makes the degenerate case exact too. -/
theorem d4HBAdjointQNMNormalizedExcitationCoefficient_mode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X) (z : ℂˣ) :
    d4HBAdjointQNMNormalizedExcitationCoefficient B source ((z : ℂ) • mode) =
      (z⁻¹ : ℂ) * d4HBAdjointQNMNormalizedExcitationCoefficient B source mode := by
  simp only [d4HBAdjointQNMNormalizedExcitationCoefficient,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp [z.ne_zero]

/-- Bilinearly normalized returned field is unconditionally projective for unit scalings. -/
theorem d4HBAdjointQNMNormalizedReturnedField_mode_unit_smul
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (B : X →ₗ[ℂ] X →ₗ[ℂ] ℂ) (source mode : X) (z : ℂˣ) :
    d4HBAdjointQNMNormalizedReturnedField B source ((z : ℂ) • mode) =
      d4HBAdjointQNMNormalizedReturnedField B source mode := by
  rw [d4HBAdjointQNMNormalizedReturnedField,
    d4HBAdjointQNMNormalizedExcitationCoefficient_mode_unit_smul,
    d4HBAdjointQNMNormalizedReturnedField]
  simp only [smul_smul]
  congr 1
  change ((z⁻¹ : ℂ) *
      d4HBAdjointQNMNormalizedExcitationCoefficient B source mode) * (z : ℂ) = _
  field_simp [z.ne_zero]

/-- BM cross-branch second-order frequency predicted by quadratic Keldysh theory. -/
def d4BMCausalCrossBranchSecondOrderFrequency
    (n m : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalQNMPlus n chi + d4BMCausalQNMMinus m chi

/-- Cross-branch BM mixing cancels angular momentum and retains only total decay. -/
theorem d4BMCausalCrossBranchSecondOrderFrequency_eq
    (n m : ℕ) (chi : ℂ) :
    d4BMCausalCrossBranchSecondOrderFrequency n m chi =
      -Complex.I * (d4BMCausalDecay n + d4BMCausalDecay m) := by
  unfold d4BMCausalCrossBranchSecondOrderFrequency
    d4BMCausalQNMPlus d4BMCausalQNMMinus
  ring

/-- Existing `++` second-harmonic frequency is literally a Keldysh frequency sum. -/
theorem d4BMCausalPlusPlusFrequency_eq_keldysh_sum
    (n : ℕ) (chi : ℂ) :
    d4BMCausalPlusPlusFrequency n chi =
      d4BMCausalQNMPlus n chi + d4BMCausalQNMPlus n chi := by
  unfold d4BMCausalPlusPlusFrequency
  ring

/-- Existing `--` second-harmonic frequency is literally a Keldysh frequency sum. -/
theorem d4BMCausalMinusMinusFrequency_eq_keldysh_sum
    (n : ℕ) (chi : ℂ) :
    d4BMCausalMinusMinusFrequency n chi =
      d4BMCausalQNMMinus n chi + d4BMCausalQNMMinus n chi := by
  unfold d4BMCausalMinusMinusFrequency
  ring

/-- Sampled BM cross-branch node is the product of the two linear QNM nodes. -/
theorem d4BMCausalCrossBranchSampleNode_factorization
    (n m : ℕ) (chi : ℂ) :
    GaloisForLFunctions.HTGeometry.qnmSampleNode
        (d4BMCausalCrossBranchSecondOrderFrequency n m chi) =
      GaloisForLFunctions.HTGeometry.qnmSampleNode (d4BMCausalQNMPlus n chi) *
        GaloisForLFunctions.HTGeometry.qnmSampleNode (d4BMCausalQNMMinus m chi) := by
  exact GaloisForLFunctions.HTGeometry.qnmSampleNode_add _ _

end
end RHTower
