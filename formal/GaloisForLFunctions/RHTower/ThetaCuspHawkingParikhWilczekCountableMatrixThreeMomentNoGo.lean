import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekQuadraticHalfLineReceiverCone
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability

/-!
# Parikh--Wilczek countable matrix three-moment no-go

Every moment-admissible countable signed PW cross-grade matrix still sees only the affine span of
one common spectral coordinate and the grade shift `4k(k+1)`.  Its residual energy is therefore
exactly one quadratic determined by three unconditional product-index `tsum`s.  The finite
half-line receiver cone consequently remains complete after absolutely summable countable
completion.

The obstruction is sharp.  An explicit infinite-support vector has zero total weight and zero
shift-weighted moment.  Its outer-product kernel is symmetric, nonzero on every sufficiently high
diagonal, and positive semidefinite on every finite section, but all three matrix moments and the
full recoil energy vanish identically.  Thus countable/cofinal linear completion alone retains no
new PW spectral invariant; any surviving route must be conditionally renormalized, nonlinear,
nonpolynomial, or coupled to an independent physical channel.

`[NEW] [CLASSIFICATION] [INFINITE DARK SECTOR] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Zeroth moment of a countable signed grade matrix, summed unconditionally on `ℕ × ℕ`. -/
def schwarzschildParikhWilczekCountableMatrixMomentZero (M : ℕ → ℕ → ℝ) : ℝ :=
  ∑' ij : ℕ × ℕ, M ij.1 ij.2

/-- First countable matrix moment against the sum of the two PW grade shifts. -/
def schwarzschildParikhWilczekCountableMatrixMomentOne (M : ℕ → ℕ → ℝ) : ℝ :=
  ∑' ij : ℕ × ℕ, M ij.1 ij.2 *
    (schwarzschildParikhWilczekBorelGradeShift ij.1 +
      schwarzschildParikhWilczekBorelGradeShift ij.2)

/-- Second countable matrix moment against the product of the two PW grade shifts. -/
def schwarzschildParikhWilczekCountableMatrixMomentTwo (M : ℕ → ℕ → ℝ) : ℝ :=
  ∑' ij : ℕ × ℕ, M ij.1 ij.2 *
    schwarzschildParikhWilczekBorelGradeShift ij.1 *
      schwarzschildParikhWilczekBorelGradeShift ij.2

/-- Exact unconditional convergence domain needed by the three-moment decomposition. -/
def schwarzschildParikhWilczekCountableMatrixMomentAdmissible (M : ℕ → ℕ → ℝ) : Prop :=
  Summable (fun ij : ℕ × ℕ => M ij.1 ij.2) ∧
  Summable (fun ij : ℕ × ℕ => M ij.1 ij.2 *
    (schwarzschildParikhWilczekBorelGradeShift ij.1 +
      schwarzschildParikhWilczekBorelGradeShift ij.2)) ∧
  Summable (fun ij : ℕ × ℕ => M ij.1 ij.2 *
    schwarzschildParikhWilczekBorelGradeShift ij.1 *
      schwarzschildParikhWilczekBorelGradeShift ij.2)

/-- Countable signed interaction energy of the affine PW grade residuals. -/
def schwarzschildParikhWilczekCountableMatrixResidualEnergy (M : ℕ → ℕ → ℝ) (s : ℂ) : ℝ :=
  ∑' ij : ℕ × ℕ, M ij.1 ij.2 *
    schwarzschildParikhWilczekBorelGradeResidual s ij.1 *
      schwarzschildParikhWilczekBorelGradeResidual s ij.2

/-- Quadratic spectral polynomial carried by the three countable matrix moments. -/
def schwarzschildParikhWilczekCountableMatrixResidualPolynomial (M : ℕ → ℕ → ℝ) (s : ℂ) : ℝ :=
  schwarzschildParikhWilczekCountableMatrixMomentZero M * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2 +
  schwarzschildParikhWilczekCountableMatrixMomentOne M * schwarzschildParikhWilczekBorelSpectralCoordinate s +
  schwarzschildParikhWilczekCountableMatrixMomentTwo M

/-- Moment admissibility makes the residual energy summable at every spectral parameter. -/
theorem summable_schwarzschildParikhWilczekCountableMatrixResidualEnergy
    {M : ℕ → ℕ → ℝ}
    (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) (s : ℂ) :
    Summable (fun ij : ℕ × ℕ => M ij.1 ij.2 *
      schwarzschildParikhWilczekBorelGradeResidual s ij.1 *
        schwarzschildParikhWilczekBorelGradeResidual s ij.2) := by
  rcases hM with ⟨h0, h1, h2⟩
  have h0x : Summable (fun ij : ℕ × ℕ =>
      M ij.1 ij.2 * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2) :=
    h0.mul_right _
  have h1x : Summable (fun ij : ℕ × ℕ =>
      M ij.1 ij.2 *
        (schwarzschildParikhWilczekBorelGradeShift ij.1 +
          schwarzschildParikhWilczekBorelGradeShift ij.2) *
            schwarzschildParikhWilczekBorelSpectralCoordinate s) :=
    h1.mul_right _
  refine ((h0x.add h1x).add h2).congr ?_
  intro ij
  simp_rw [schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift]
  ring

/-- Every admissible countable residual energy is exactly its three-moment quadratic. -/
theorem schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment
    {M : ℕ → ℕ → ℝ}
    (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) (s : ℂ) :
    schwarzschildParikhWilczekCountableMatrixResidualEnergy M s = schwarzschildParikhWilczekCountableMatrixResidualPolynomial M s := by
  rcases hM with ⟨h0, h1, h2⟩
  have h0x : Summable (fun ij : ℕ × ℕ =>
      M ij.1 ij.2 * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2) :=
    h0.mul_right _
  have h1x : Summable (fun ij : ℕ × ℕ =>
      M ij.1 ij.2 *
        (schwarzschildParikhWilczekBorelGradeShift ij.1 +
          schwarzschildParikhWilczekBorelGradeShift ij.2) *
            schwarzschildParikhWilczekBorelSpectralCoordinate s) :=
    h1.mul_right _
  rw [schwarzschildParikhWilczekCountableMatrixResidualEnergy, schwarzschildParikhWilczekCountableMatrixResidualPolynomial]
  simp_rw [schwarzschildParikhWilczekBorelGradeResidual_eq_coordinate_add_shift]
  calc
    (∑' ij : ℕ × ℕ, M ij.1 ij.2 *
        (schwarzschildParikhWilczekBorelSpectralCoordinate s +
          schwarzschildParikhWilczekBorelGradeShift ij.1) *
        (schwarzschildParikhWilczekBorelSpectralCoordinate s +
          schwarzschildParikhWilczekBorelGradeShift ij.2)) =
      ∑' ij : ℕ × ℕ,
        ((M ij.1 ij.2 * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2 +
          M ij.1 ij.2 *
            (schwarzschildParikhWilczekBorelGradeShift ij.1 +
              schwarzschildParikhWilczekBorelGradeShift ij.2) *
                schwarzschildParikhWilczekBorelSpectralCoordinate s) +
          M ij.1 ij.2 * schwarzschildParikhWilczekBorelGradeShift ij.1 *
            schwarzschildParikhWilczekBorelGradeShift ij.2) := by
              apply tsum_congr
              intro ij
              ring
    _ = (∑' ij : ℕ × ℕ,
          M ij.1 ij.2 * schwarzschildParikhWilczekBorelSpectralCoordinate s ^ 2) +
        (∑' ij : ℕ × ℕ,
          M ij.1 ij.2 *
            (schwarzschildParikhWilczekBorelGradeShift ij.1 +
              schwarzschildParikhWilczekBorelGradeShift ij.2) *
                schwarzschildParikhWilczekBorelSpectralCoordinate s) +
        ∑' ij : ℕ × ℕ, M ij.1 ij.2 *
          schwarzschildParikhWilczekBorelGradeShift ij.1 *
            schwarzschildParikhWilczekBorelGradeShift ij.2 := by
              rw [(h0x.add h1x).tsum_add h2, h0x.tsum_add h1x]
    _ = _ := by
      rw [tsum_mul_right, tsum_mul_right]
      rfl

/-- Countable signed interaction energy of the full PW recoil-holonomy reporters. -/
def schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy (M : ℕ → ℕ → ℝ) (s : ℂ) : ℝ :=
  ∑' ij : ℕ × ℕ, M ij.1 ij.2 *
    (schwarzschildParikhWilczekBorelRecoilHolonomy s ij.1).im *
      (schwarzschildParikhWilczekBorelRecoilHolonomy s ij.2).im

/-- Full countable cross-grade energy factors as wall squared times residual energy. -/
theorem schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_factorization
    (M : ℕ → ℕ → ℝ) (s : ℂ) :
    schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy M s =
      schwarzschildParikhWilczekBorelWallFactor s ^ 2 * schwarzschildParikhWilczekCountableMatrixResidualEnergy M s := by
  rw [schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy, schwarzschildParikhWilczekCountableMatrixResidualEnergy]
  simp_rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization]
  calc
    (∑' ij : ℕ × ℕ, M ij.1 ij.2 *
        (schwarzschildParikhWilczekBorelWallFactor s *
          schwarzschildParikhWilczekBorelGradeResidual s ij.1) *
        (schwarzschildParikhWilczekBorelWallFactor s *
          schwarzschildParikhWilczekBorelGradeResidual s ij.2)) =
      ∑' ij : ℕ × ℕ, schwarzschildParikhWilczekBorelWallFactor s ^ 2 *
        (M ij.1 ij.2 * schwarzschildParikhWilczekBorelGradeResidual s ij.1 *
          schwarzschildParikhWilczekBorelGradeResidual s ij.2) := by
            apply tsum_congr
            intro ij
            ring
    _ = _ := tsum_mul_left

/-- Full countable energy is wall squared times the same three-moment quadratic. -/
theorem schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_three_moment
    {M : ℕ → ℕ → ℝ} (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) (s : ℂ) :
    schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy M s =
      schwarzschildParikhWilczekBorelWallFactor s ^ 2 * schwarzschildParikhWilczekCountableMatrixResidualPolynomial M s := by
  rw [schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_factorization, schwarzschildParikhWilczekCountableMatrixResidualEnergy_three_moment hM]

/-- Countable residual polynomial is identically zero exactly on the three-moment kernel. -/
theorem schwarzschildParikhWilczekCountableMatrixResidualPolynomial_eq_zero_forall_iff
    (M : ℕ → ℕ → ℝ) :
    (∀ s : ℂ, schwarzschildParikhWilczekCountableMatrixResidualPolynomial M s = 0) ↔
      schwarzschildParikhWilczekCountableMatrixMomentZero M = 0 ∧ schwarzschildParikhWilczekCountableMatrixMomentOne M = 0 ∧ schwarzschildParikhWilczekCountableMatrixMomentTwo M = 0 := by
  constructor
  · intro h
    have h1 := h 0
    have h2 := h I
    have h5 := h (2 * I)
    norm_num [schwarzschildParikhWilczekCountableMatrixResidualPolynomial, schwarzschildParikhWilczekBorelSpectralCoordinate] at h1 h2 h5
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩ s
    simp [schwarzschildParikhWilczekCountableMatrixResidualPolynomial, h0, h1, h2]

/-- Countable signed receiver cone, expressed by the complete quadratic half-line classifier. -/
def schwarzschildParikhWilczekCountableSignedMatrixReceiverCone (M : ℕ → ℕ → ℝ) : Prop :=
  quadraticPositiveOnOneCondition (schwarzschildParikhWilczekCountableMatrixMomentZero M) (schwarzschildParikhWilczekCountableMatrixMomentOne M) (schwarzschildParikhWilczekCountableMatrixMomentTwo M)

/-- Receiver-cone membership is exactly strict positivity of the moment quadratic on `x > 1`. -/
theorem schwarzschildParikhWilczekCountableSignedMatrixReceiverCone_iff
    (M : ℕ → ℕ → ℝ) :
    schwarzschildParikhWilczekCountableSignedMatrixReceiverCone M ↔ ∀ x : ℝ, 1 < x →
      0 < schwarzschildParikhWilczekCountableMatrixMomentZero M * x ^ 2 + schwarzschildParikhWilczekCountableMatrixMomentOne M * x + schwarzschildParikhWilczekCountableMatrixMomentTwo M := by
  exact (quadratic_pos_on_one_iff _ _ _).symm

/-- A countable receiver-cone kernel has positive residual at every Xi divisor. -/
theorem schwarzschildParikhWilczekCountableMatrixResidualPolynomial_pos_of_receiverCone
    {M : ℕ → ℕ → ℝ} (hcone : schwarzschildParikhWilczekCountableSignedMatrixReceiverCone M) (rho : XiDivisorSupport) :
    0 < schwarzschildParikhWilczekCountableMatrixResidualPolynomial M (rho : ℂ) := by
  rw [schwarzschildParikhWilczekCountableMatrixResidualPolynomial]
  exact (schwarzschildParikhWilczekCountableSignedMatrixReceiverCone_iff M).mp hcone
    (schwarzschildParikhWilczekBorelSpectralCoordinate (rho : ℂ))
    (schwarzschildParikhWilczekBorelSpectralCoordinate_gt_one rho)

/-- In the countable receiver cone, energy vanishing is exactly critical-wall placement. -/
theorem schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone
    {M : ℕ → ℕ → ℝ} (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) (hcone : schwarzschildParikhWilczekCountableSignedMatrixReceiverCone M)
    (rho : XiDivisorSupport) :
    schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy M (rho : ℂ) = 0 ↔ (rho : ℂ).re = 1 / 2 := by
  rw [schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_three_moment hM]
  have hpoly := schwarzschildParikhWilczekCountableMatrixResidualPolynomial_pos_of_receiverCone hcone rho
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hwallSq | hzero
    · have hwall := (sq_eq_zero_iff).mp hwallSq
      rw [schwarzschildParikhWilczekBorelWallFactor] at hwall
      rcases mul_eq_zero.mp hwall with him | hcenter
      · exact False.elim (xi_divisor_support_im_ne_zero rho (by linarith))
      · linarith
    · exact False.elim (hpoly.ne' hzero)
  · intro hre
    rw [schwarzschildParikhWilczekBorelWallFactor, hre]
    norm_num

/-- Universal vanishing of any admissible countable receiver is exactly RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_zero
    {M : ℕ → ℕ → ℝ} (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) (hcone : schwarzschildParikhWilczekCountableSignedMatrixReceiverCone M) :
    RiemannHypothesis ↔ ∀ rho : XiDivisorSupport,
      schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy M (rho : ℂ) = 0 := by
  constructor
  · intro hRH rho
    exact (schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone hM hcone rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_iff_of_receiverCone hM hcone rho).mp (h rho)

/-- Full countable energy is identically dark exactly when all three moments vanish. -/
theorem schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_forall_iff_moments
    {M : ℕ → ℕ → ℝ} (hM : schwarzschildParikhWilczekCountableMatrixMomentAdmissible M) :
    (∀ s : ℂ, schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy M s = 0) ↔
      schwarzschildParikhWilczekCountableMatrixMomentZero M = 0 ∧ schwarzschildParikhWilczekCountableMatrixMomentOne M = 0 ∧ schwarzschildParikhWilczekCountableMatrixMomentTwo M = 0 := by
  constructor
  · intro h
    have h2 := h I
    have h5 := h (2 * I)
    have h10 := h (3 * I)
    rw [schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_three_moment hM] at h2 h5 h10
    norm_num [schwarzschildParikhWilczekBorelWallFactor,
      schwarzschildParikhWilczekCountableMatrixResidualPolynomial, schwarzschildParikhWilczekBorelSpectralCoordinate] at h2 h5 h10
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨h0, h1, h2⟩ s
    rw [schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_three_moment hM]
    simp [schwarzschildParikhWilczekCountableMatrixResidualPolynomial, h0, h1, h2]

/-- Zero extension of the finite three-grade dark vector `(2,-3,1)`. -/
def schwarzschildParikhWilczekCountableThreeGradeDarkWeight : ℕ → ℝ
  | 0 => 2
  | 1 => -3
  | 2 => 1
  | _ => 0

/-- Countable outer-product kernel of the zero-extended three-grade dark vector. -/
def schwarzschildParikhWilczekCountableThreeGradeDarkMatrix (i j : ℕ) : ℝ :=
  schwarzschildParikhWilczekCountableThreeGradeDarkWeight i *
    schwarzschildParikhWilczekCountableThreeGradeDarkWeight j

/-- The zero-extended finite dark vector vanishes from grade three onward. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkWeight_eq_zero_of_three_le
    {n : ℕ} (hn : 3 ≤ n) :
    schwarzschildParikhWilczekCountableThreeGradeDarkWeight n = 0 := by
  rcases n with _ | _ | _ | n <;> simp [schwarzschildParikhWilczekCountableThreeGradeDarkWeight] at hn ⊢

/-- The zero-extended dark kernel is supported on the leading `3 × 3` block. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem
    {ij : ℕ × ℕ} (hij : ij ∉ Finset.range 3 ×ˢ Finset.range 3) :
    schwarzschildParikhWilczekCountableThreeGradeDarkMatrix ij.1 ij.2 = 0 := by
  simp only [Finset.mem_product, Finset.mem_range, not_and_or] at hij
  rcases hij with hi | hj
  · rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight_eq_zero_of_three_le (Nat.le_of_not_gt hi), zero_mul]
  · rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight_eq_zero_of_three_le (Nat.le_of_not_gt hj), mul_zero]

/-- The zero-extended three-grade dark kernel is countably moment-admissible. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_admissible :
    schwarzschildParikhWilczekCountableMatrixMomentAdmissible
      schwarzschildParikhWilczekCountableThreeGradeDarkMatrix := by
  refine ⟨?_, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := Finset.range 3 ×ˢ Finset.range 3)
    intro ij hij
    exact schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij
  · apply summable_of_ne_finset_zero (s := Finset.range 3 ×ˢ Finset.range 3)
    intro ij hij
    rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij, zero_mul]
  · apply summable_of_ne_finset_zero (s := Finset.range 3 ×ˢ Finset.range 3)
    intro ij hij
    rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij, zero_mul, zero_mul]

/-- All three countable moments of the zero-extended finite dark kernel vanish. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_moments :
    schwarzschildParikhWilczekCountableMatrixMomentZero schwarzschildParikhWilczekCountableThreeGradeDarkMatrix = 0 ∧
      schwarzschildParikhWilczekCountableMatrixMomentOne schwarzschildParikhWilczekCountableThreeGradeDarkMatrix = 0 ∧
        schwarzschildParikhWilczekCountableMatrixMomentTwo schwarzschildParikhWilczekCountableThreeGradeDarkMatrix = 0 := by
  constructor
  · rw [schwarzschildParikhWilczekCountableMatrixMomentZero, tsum_eq_sum (s := Finset.range 3 ×ˢ Finset.range 3)
      (fun ij hij => schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij)]
    norm_num [Finset.sum_product, schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight,
      Finset.sum_range_succ]
  constructor
  · rw [schwarzschildParikhWilczekCountableMatrixMomentOne, tsum_eq_sum (s := Finset.range 3 ×ˢ Finset.range 3)
      (fun ij hij => by rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij, zero_mul])]
    norm_num [Finset.sum_product, schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight,
      schwarzschildParikhWilczekBorelGradeShift, Finset.sum_range_succ]
  · rw [schwarzschildParikhWilczekCountableMatrixMomentTwo, tsum_eq_sum (s := Finset.range 3 ×ˢ Finset.range 3)
      (fun ij hij => by rw [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_eq_zero_of_not_mem hij, zero_mul, zero_mul])]
    norm_num [Finset.sum_product, schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight,
      schwarzschildParikhWilczekBorelGradeShift, Finset.sum_range_succ]

/-- The zero-extended finite dark kernel remains nonzero. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_ne_zero :
    schwarzschildParikhWilczekCountableThreeGradeDarkMatrix ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  norm_num [schwarzschildParikhWilczekCountableThreeGradeDarkMatrix, schwarzschildParikhWilczekCountableThreeGradeDarkWeight] at h00

/-- The zero-extended finite dark kernel annihilates full countable energy identically. -/
theorem schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_energy_zero (s : ℂ) :
    schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy schwarzschildParikhWilczekCountableThreeGradeDarkMatrix s = 0 :=
  (schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_forall_iff_moments schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_admissible).mpr
    schwarzschildParikhWilczekCountableThreeGradeDarkMatrix_moments s

/-- Infinite-support dark vector: geometric tail with two low-grade moment corrections. -/
def schwarzschildParikhWilczekInfiniteGradeDarkWeight (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n + (if n = 0 then 2 else 0) + (if n = 1 then -4 else 0)

/-- The infinite dark vector is summable and has total weight zero. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkWeight_hasSum :
    HasSum schwarzschildParikhWilczekInfiniteGradeDarkWeight 0 := by
  have hgeo : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have hzero := hasSum_ite_eq (0 : ℕ) (2 : ℝ)
  have hone := hasSum_ite_eq (1 : ℕ) (-4 : ℝ)
  convert (hgeo.add hzero).add hone using 1
  · ext n
    simp [schwarzschildParikhWilczekInfiniteGradeDarkWeight]
  · norm_num

/-- The infinite dark vector's grade-shift-weighted moment is also zero. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkWeight_shift_hasSum :
    HasSum (fun n : ℕ => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
      schwarzschildParikhWilczekBorelGradeShift n) 0 := by
  have hsq := hasSum_sq_mul_geometric_of_abs_lt_one (q := (1 / 2 : ℝ)) (by norm_num)
  have hlin := hasSum_coe_mul_geometric_of_norm_lt_one
    (𝕜 := ℝ) (r := (1 / 2 : ℝ)) (by norm_num)
  have hgeo : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n *
      schwarzschildParikhWilczekBorelGradeShift n) 32 := by
    have hraw := (hsq.mul_left 4).add (hlin.mul_left 4)
    have hraw' : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n *
        schwarzschildParikhWilczekBorelGradeShift n)
        (4 * ((1 / 2 : ℝ) * (1 + 1 / 2) / (1 - 1 / 2) ^ 3) +
          4 * ((1 / 2 : ℝ) / (1 - 1 / 2) ^ 2)) := by
      apply hraw.congr_fun
      intro n
      rw [schwarzschildParikhWilczekBorelGradeShift]
      ring
    norm_num at hraw'
    exact hraw'
  have hzero := hasSum_ite_eq (0 : ℕ)
    ((2 : ℝ) * schwarzschildParikhWilczekBorelGradeShift 0)
  have hone := hasSum_ite_eq (1 : ℕ)
    ((-4 : ℝ) * schwarzschildParikhWilczekBorelGradeShift 1)
  convert (hgeo.add hzero).add hone using 1
  · ext n
    by_cases hn0 : n = 0
    · subst n
      norm_num [schwarzschildParikhWilczekInfiniteGradeDarkWeight, schwarzschildParikhWilczekBorelGradeShift]
    by_cases hn1 : n = 1
    · subst n
      norm_num [schwarzschildParikhWilczekInfiniteGradeDarkWeight, schwarzschildParikhWilczekBorelGradeShift]
    simp [schwarzschildParikhWilczekInfiniteGradeDarkWeight, hn0, hn1]
  · norm_num [schwarzschildParikhWilczekBorelGradeShift]

/-- Every grade at least two lies in the support of the infinite dark vector. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkWeight_ne_zero_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    schwarzschildParikhWilczekInfiniteGradeDarkWeight n ≠ 0 := by
  rw [schwarzschildParikhWilczekInfiniteGradeDarkWeight, if_neg (by omega), if_neg (by omega)]
  positivity

/-- Infinite-support rank-one outer-product dark kernel. -/
def schwarzschildParikhWilczekInfiniteGradeDarkMatrix (i j : ℕ) : ℝ :=
  schwarzschildParikhWilczekInfiniteGradeDarkWeight i * schwarzschildParikhWilczekInfiniteGradeDarkWeight j

/-- The infinite-support dark kernel satisfies all three countable summability conditions. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_admissible :
    schwarzschildParikhWilczekCountableMatrixMomentAdmissible
      schwarzschildParikhWilczekInfiniteGradeDarkMatrix := by
  have hw := schwarzschildParikhWilczekInfiniteGradeDarkWeight_hasSum.summable
  have hu := schwarzschildParikhWilczekInfiniteGradeDarkWeight_shift_hasSum.summable
  have hwnorm : Summable (fun n : ℕ => ‖schwarzschildParikhWilczekInfiniteGradeDarkWeight n‖) := hw.norm
  have hunorm : Summable (fun n : ℕ =>
      ‖schwarzschildParikhWilczekInfiniteGradeDarkWeight n * schwarzschildParikhWilczekBorelGradeShift n‖) := hu.norm
  have hww : Summable (fun ij : ℕ × ℕ =>
      schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 * schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2) :=
    summable_mul_of_summable_norm
      (f := schwarzschildParikhWilczekInfiniteGradeDarkWeight) (g := schwarzschildParikhWilczekInfiniteGradeDarkWeight) hwnorm hwnorm
  refine ⟨hww, ?_, ?_⟩
  · have hleft : Summable (fun ij : ℕ × ℕ =>
        (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
          schwarzschildParikhWilczekBorelGradeShift ij.1) *
            schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2) :=
      summable_mul_of_summable_norm
        (f := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n)
        (g := schwarzschildParikhWilczekInfiniteGradeDarkWeight) hunorm hwnorm
    have hright : Summable (fun ij : ℕ × ℕ =>
        schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
          (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2 *
            schwarzschildParikhWilczekBorelGradeShift ij.2)) :=
      summable_mul_of_summable_norm
        (f := schwarzschildParikhWilczekInfiniteGradeDarkWeight)
        (g := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n) hwnorm hunorm
    refine (hleft.add hright).congr ?_
    intro ij
    rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix]
    ring
  · have hprod : Summable (fun ij : ℕ × ℕ =>
        (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
          schwarzschildParikhWilczekBorelGradeShift ij.1) *
        (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2 *
          schwarzschildParikhWilczekBorelGradeShift ij.2)) :=
      summable_mul_of_summable_norm
        (f := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n)
        (g := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n) hunorm hunorm
    refine hprod.congr ?_
    intro ij
    rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix]
    ring

/-- All three countable moments of the infinite-support kernel vanish. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_moments :
    schwarzschildParikhWilczekCountableMatrixMomentZero schwarzschildParikhWilczekInfiniteGradeDarkMatrix = 0 ∧
      schwarzschildParikhWilczekCountableMatrixMomentOne schwarzschildParikhWilczekInfiniteGradeDarkMatrix = 0 ∧
        schwarzschildParikhWilczekCountableMatrixMomentTwo schwarzschildParikhWilczekInfiniteGradeDarkMatrix = 0 := by
  have hw := schwarzschildParikhWilczekInfiniteGradeDarkWeight_hasSum.summable
  have hu := schwarzschildParikhWilczekInfiniteGradeDarkWeight_shift_hasSum.summable
  have hwnorm : Summable (fun n : ℕ => ‖schwarzschildParikhWilczekInfiniteGradeDarkWeight n‖) := hw.norm
  have hunorm : Summable (fun n : ℕ =>
      ‖schwarzschildParikhWilczekInfiniteGradeDarkWeight n * schwarzschildParikhWilczekBorelGradeShift n‖) := hu.norm
  have hw0 := schwarzschildParikhWilczekInfiniteGradeDarkWeight_hasSum.tsum_eq
  have hu0 := schwarzschildParikhWilczekInfiniteGradeDarkWeight_shift_hasSum.tsum_eq
  constructor
  · change (∑' ij : ℕ × ℕ,
      schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 * schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2) = 0
    rw [← tsum_mul_tsum_of_summable_norm
      (f := schwarzschildParikhWilczekInfiniteGradeDarkWeight) (g := schwarzschildParikhWilczekInfiniteGradeDarkWeight) hwnorm hwnorm, hw0]
    norm_num
  constructor
  · have hleft : Summable (fun ij : ℕ × ℕ =>
        (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
          schwarzschildParikhWilczekBorelGradeShift ij.1) *
            schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2) :=
      summable_mul_of_summable_norm
        (f := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n)
        (g := schwarzschildParikhWilczekInfiniteGradeDarkWeight) hunorm hwnorm
    have hright : Summable (fun ij : ℕ × ℕ =>
        schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
          (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2 *
            schwarzschildParikhWilczekBorelGradeShift ij.2)) :=
      summable_mul_of_summable_norm
        (f := schwarzschildParikhWilczekInfiniteGradeDarkWeight)
        (g := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
          schwarzschildParikhWilczekBorelGradeShift n) hwnorm hunorm
    rw [schwarzschildParikhWilczekCountableMatrixMomentOne]
    calc
      (∑' ij : ℕ × ℕ, schwarzschildParikhWilczekInfiniteGradeDarkMatrix ij.1 ij.2 *
          (schwarzschildParikhWilczekBorelGradeShift ij.1 +
            schwarzschildParikhWilczekBorelGradeShift ij.2)) =
        (∑' ij : ℕ × ℕ,
          (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
            schwarzschildParikhWilczekBorelGradeShift ij.1) *
              schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2) +
        ∑' ij : ℕ × ℕ,
          schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
            (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2 *
              schwarzschildParikhWilczekBorelGradeShift ij.2) := by
                rw [← hleft.tsum_add hright]
                apply tsum_congr
                intro ij
                rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix]
                ring
      _ = (∑' i : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight i *
            schwarzschildParikhWilczekBorelGradeShift i) *
            (∑' j : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight j) +
          (∑' i : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight i) *
            ∑' j : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight j *
              schwarzschildParikhWilczekBorelGradeShift j := by
                rw [tsum_mul_tsum_of_summable_norm
                    (f := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
                      schwarzschildParikhWilczekBorelGradeShift n)
                    (g := schwarzschildParikhWilczekInfiniteGradeDarkWeight) hunorm hwnorm,
                  tsum_mul_tsum_of_summable_norm
                    (f := schwarzschildParikhWilczekInfiniteGradeDarkWeight)
                    (g := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
                      schwarzschildParikhWilczekBorelGradeShift n) hwnorm hunorm]
      _ = 0 := by rw [hw0, hu0]; norm_num
  · rw [schwarzschildParikhWilczekCountableMatrixMomentTwo]
    calc
      (∑' ij : ℕ × ℕ, schwarzschildParikhWilczekInfiniteGradeDarkMatrix ij.1 ij.2 *
          schwarzschildParikhWilczekBorelGradeShift ij.1 *
            schwarzschildParikhWilczekBorelGradeShift ij.2) =
        (∑' ij : ℕ × ℕ,
          (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.1 *
            schwarzschildParikhWilczekBorelGradeShift ij.1) *
          (schwarzschildParikhWilczekInfiniteGradeDarkWeight ij.2 *
            schwarzschildParikhWilczekBorelGradeShift ij.2)) := by
              apply tsum_congr
              intro ij
              rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix]
              ring
      _ = (∑' i : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight i *
              schwarzschildParikhWilczekBorelGradeShift i) *
            ∑' j : ℕ, schwarzschildParikhWilczekInfiniteGradeDarkWeight j *
              schwarzschildParikhWilczekBorelGradeShift j := by
                rw [tsum_mul_tsum_of_summable_norm
                  (f := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
                    schwarzschildParikhWilczekBorelGradeShift n)
                  (g := fun n => schwarzschildParikhWilczekInfiniteGradeDarkWeight n *
                    schwarzschildParikhWilczekBorelGradeShift n) hunorm hunorm]
      _ = 0 := by rw [hu0]; norm_num

/-- Every diagonal entry from grade two onward is nonzero. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_infinite_diagonal_support
    {n : ℕ} (hn : 2 ≤ n) :
    schwarzschildParikhWilczekInfiniteGradeDarkMatrix n n ≠ 0 := by
  rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix]
  exact mul_ne_zero (schwarzschildParikhWilczekInfiniteGradeDarkWeight_ne_zero_of_two_le hn)
    (schwarzschildParikhWilczekInfiniteGradeDarkWeight_ne_zero_of_two_le hn)

/-- The infinite dark kernel is symmetric. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_symmetric (i j : ℕ) :
    schwarzschildParikhWilczekInfiniteGradeDarkMatrix i j = schwarzschildParikhWilczekInfiniteGradeDarkMatrix j i := by
  rw [schwarzschildParikhWilczekInfiniteGradeDarkMatrix, schwarzschildParikhWilczekInfiniteGradeDarkMatrix, mul_comm]

/-- Every finite principal section of the infinite dark kernel is positive semidefinite. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_finiteQuadraticForm_nonneg
    {N : ℕ} (v : Fin N → ℝ) :
    0 ≤ ∑ i : Fin N, ∑ j : Fin N,
      v i * schwarzschildParikhWilczekInfiniteGradeDarkMatrix (i : ℕ) (j : ℕ) * v j := by
  rw [show (∑ i : Fin N, ∑ j : Fin N,
      v i * schwarzschildParikhWilczekInfiniteGradeDarkMatrix (i : ℕ) (j : ℕ) * v j) =
      (∑ i, v i * schwarzschildParikhWilczekInfiniteGradeDarkWeight (i : ℕ)) ^ 2 by
        simpa only [schwarzschildParikhWilczekInfiniteGradeDarkMatrix] using
          finite_rankOneQuadraticForm_eq_sq
            (fun i : Fin N => schwarzschildParikhWilczekInfiniteGradeDarkWeight (i : ℕ)) v]
  positivity

/-- The nonzero infinite-support positive-semidefinite kernel is identically PW-dark. -/
theorem schwarzschildParikhWilczekInfiniteGradeDarkMatrix_energy_zero (s : ℂ) :
    schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy schwarzschildParikhWilczekInfiniteGradeDarkMatrix s = 0 :=
  (schwarzschildParikhWilczekCountableMatrixCrossGradeEnergy_eq_zero_forall_iff_moments
    schwarzschildParikhWilczekInfiniteGradeDarkMatrix_admissible).mpr schwarzschildParikhWilczekInfiniteGradeDarkMatrix_moments s

end

end RHTower
