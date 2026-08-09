import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature
import GaloisForLFunctions.HTGeometry.HankelBoundaryFlux

/-!
# Projective extension class of a flat finite Hankel face

The first omitted coupling depends linearly on the chosen kernel vector and therefore changes sign
under reversal of that vector.  A singular Hankel face itself only determines the kernel line.
The canonical scalar is obtained by making the null polynomial monic.  This file proves that the
usual terminal product is the square of the terminal coefficient times that monic remainder.
Consequently its sign is intrinsic to the projective null line.
-/

open Matrix Polynomial

namespace HTGeometry

noncomputable section

/-- Canonically oriented first extension coordinate of a finite Hankel boundary. -/
def finiteHankelBoundaryMonicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  momentFunctional s
    (X ^ (n + 1) * finiteHankelNullMonicPolynomial c)

/-- The leading coefficient of the finite-coordinate null polynomial is its terminal coordinate. -/
theorem finiteHankelNullPolynomial_leadingCoeff_eq_terminal
    {n : ℕ} (c : Fin (n + 1) → ℝ) (hlast : c (Fin.last n) ≠ 0) :
    (finiteHankelNullPolynomial c).leadingCoeff = c (Fin.last n) := by
  rw [Polynomial.leadingCoeff, finiteHankelNullPolynomial_natDegree c hlast,
    finiteHankelNullPolynomial,
    Polynomial.ofFn_coeff_eq_val_of_lt c (Nat.lt_succ_self n)]
  apply congrArg c
  exact Fin.ext rfl

/-- Monic normalization divides the raw first remainder by the terminal coefficient. -/
theorem finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryMonicRemainder s c =
      (c (Fin.last n))⁻¹ *
        momentFunctional s (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
  rw [finiteHankelBoundaryMonicRemainder, finiteHankelNullMonicPolynomial]
  have hpoly :
      X ^ (n + 1) *
          (finiteHankelNullPolynomial c *
            C (finiteHankelNullPolynomial c).leadingCoeff⁻¹) =
        (finiteHankelNullPolynomial c).leadingCoeff⁻¹ •
          (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, momentFunctional_smul,
    finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast]

/-- **Projective terminal law.** The scaling-dependent terminal product is a positive square times
the canonical monic extension class. -/
theorem terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) *
        GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c =
      c (Fin.last n) ^ 2 * finiteHankelBoundaryMonicRemainder s c := by
  rw [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
    ← momentFunctional_X_pow_mul_finiteHankelNullPolynomial]
  rw [finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw s c hlast]
  field_simp [hlast]

/-- The canonical monic remainder is also the quadrature error of the monic first-unseen
polynomial. -/
theorem finiteHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    finiteHankelBoundaryQuadratureError s c
        (X ^ (n + 1) * finiteHankelNullMonicPolynomial c) =
      finiteHankelBoundaryMonicRemainder s c := by
  have hsum : ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x *
        (X ^ (n + 1) * finiteHankelNullMonicPolynomial c).eval x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [eval_mul, finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx,
      mul_zero, mul_zero]
  rw [finiteHankelBoundaryQuadratureError, hsum, sub_zero,
    finiteHankelBoundaryMonicRemainder]

/-- **First-unseen moment law.**  On a positive flat Hankel face, the projective extension
coordinate is exactly the error made by extending its canonical positive quadrature from degree
`2n` to the first unseen monomial of degree `2n+1`. -/
theorem finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryMonicRemainder s c =
      s (2 * n + 1) -
        ∑ x ∈ finiteHankelBoundaryNodes c,
          finiteHankelBoundaryWeight s c x * x ^ (2 * n + 1) := by
  let P : Polynomial ℝ := finiteHankelNullMonicPolynomial c
  let top : Polynomial ℝ := X ^ (2 * n + 1)
  let boundary : Polynomial ℝ := X ^ (n + 1) * P
  let q : Polynomial ℝ := top - boundary
  have hPne : P ≠ 0 := (finiteHankelNullMonicPolynomial_monic c hlast).ne_zero
  have hPdeg : P.degree = (n : WithBot ℕ) := by
    rw [degree_eq_natDegree hPne,
      finiteHankelNullMonicPolynomial_natDegree c hlast]
  have htopne : top ≠ 0 := pow_ne_zero _ X_ne_zero
  have htopdeg : top.degree = ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    dsimp only [top]
    rw [degree_X_pow]
  have hboundarydeg : boundary.degree = ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    dsimp only [boundary]
    rw [degree_mul, degree_X_pow, hPdeg]
    norm_cast
    omega
  have hlead : top.leadingCoeff = boundary.leadingCoeff := by
    dsimp only [top, boundary]
    rw [leadingCoeff_X_pow, leadingCoeff_mul, leadingCoeff_X_pow,
      (finiteHankelNullMonicPolynomial_monic c hlast).leadingCoeff,
      mul_one]
  have hqdeg : q.degree < ((2 * n + 1 : ℕ) : WithBot ℕ) := by
    dsimp only [q]
    have h := degree_sub_lt
      (by rw [htopdeg, hboundarydeg]) htopne hlead
    rwa [htopdeg] at h
  have hqle : q.degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    by_cases hqzero : q = 0
    · simp [hqzero]
    · have hqnat : q.natDegree < 2 * n + 1 :=
        (natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
      exact natDegree_le_iff_degree_le.mp (Nat.lt_succ_iff.mp (by
        simpa only [Nat.succ_eq_add_one] using hqnat))
  have hqexact := momentFunctional_eq_finiteHankelBoundarySum
    c hhead hc hlast q hqle
  have hlinear : momentFunctional s q =
      momentFunctional s top - momentFunctional s boundary := by
    dsimp only [q]
    rw [sub_eq_add_neg, momentFunctional_add]
    rw [show -boundary = (-1 : ℝ) • boundary by rw [neg_one_smul],
      momentFunctional_smul]
    ring
  have hsumlinear :
      (∑ x ∈ finiteHankelBoundaryNodes c,
          finiteHankelBoundaryWeight s c x * q.eval x) =
        (∑ x ∈ finiteHankelBoundaryNodes c,
          finiteHankelBoundaryWeight s c x * top.eval x) -
        (∑ x ∈ finiteHankelBoundaryNodes c,
          finiteHankelBoundaryWeight s c x * boundary.eval x) := by
    dsimp only [q]
    simp only [eval_sub, mul_sub, Finset.sum_sub_distrib]
  have hboundarysum :
      (∑ x ∈ finiteHankelBoundaryNodes c,
          finiteHankelBoundaryWeight s c x * boundary.eval x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp only [boundary]
    rw [eval_mul, finiteHankelNullMonicPolynomial_eval_eq_zero_of_mem c hx,
      mul_zero, mul_zero]
  have htopmoment : momentFunctional s top = s (2 * n + 1) := by
    dsimp only [top]
    rw [momentFunctional_X_pow]
  have htopeval : ∀ x : ℝ, top.eval x = x ^ (2 * n + 1) := by
    intro x
    simp [top]
  have hboundarymoment : momentFunctional s boundary =
      finiteHankelBoundaryMonicRemainder s c := by
    rfl
  rw [hlinear, hsumlinear, hboundarysum, sub_zero, htopmoment,
    hboundarymoment] at hqexact
  simp_rw [htopeval] at hqexact
  linarith only [hqexact]

/-! ### Canonical finite-atomic Möbius tangent -/

/-- Moment of one quadrature atom under the canonical mass-shift transport: node
`x ↦ x/(1+hx)` and weight `ω ↦ ω/(1+hx)`.  The combined closed form avoids any domain
restriction at exceptional `h`; its germ at zero is the transport used below. -/
def atomicMobiusMomentTrajectory (weight node : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  (weight * node ^ k) / (1 + h * node) ^ (k + 1)

/-- The closed trajectory is exactly simultaneous Möbius transport of atomic weight and node. -/
theorem atomicMobiusMomentTrajectory_eq_weightNodeFlow
    (weight node : ℝ) (k : ℕ) (h : ℝ) :
    atomicMobiusMomentTrajectory weight node k h =
      (weight / (1 + h * node)) * (node / (1 + h * node)) ^ k := by
  simp only [atomicMobiusMomentTrajectory, div_eq_mul_inv]
  rw [pow_succ]
  simp only [_root_.mul_inv_rev]
  ring

/-- **One-atom Möbius tangent law.**  Simultaneous weight/node transport differentiates the
`k`th moment by `-(k+1)` times the next moment. -/
theorem atomicMobiusMomentTrajectory_hasDerivAt
    (weight node : ℝ) (k : ℕ) :
    HasDerivAt (atomicMobiusMomentTrajectory weight node k)
      (-((k + 1 : ℕ) : ℝ) * weight * node ^ (k + 1)) 0 := by
  have hden : HasDerivAt (fun h : ℝ => 1 + h * node) node 0 := by
    simpa [add_comm] using
      ((hasDerivAt_id (0 : ℝ)).mul_const node).const_add 1
  have hden0 : (1 : ℝ) + 0 * node ≠ 0 := by norm_num
  have hpow := hden.pow (k + 1)
  have hraw :=
    (hasDerivAt_const (x := (0 : ℝ)) (weight * node ^ k)).div hpow
      (pow_ne_zero _ hden0)
  have hcoef :
      (0 * ((fun h : ℝ => 1 + h * node) ^ (k + 1)) 0 -
          (weight * node ^ k) *
            (((k + 1 : ℕ) : ℝ) * (1 + 0 * node) ^ (k + 1 - 1) * node)) /
        ((fun h : ℝ => 1 + h * node) ^ (k + 1)) 0 ^ 2 =
      -((k + 1 : ℕ) : ℝ) * weight * node ^ (k + 1) := by
    simp only [Pi.pow_apply, zero_mul, add_zero, one_pow, zero_sub, neg_mul]
    rw [pow_succ]
    ring
  have hnormalized := hraw.congr_deriv hcoef
  convert! hnormalized using 1

/-- Canonical finite-atomic continuation of a flat quadrature moment under mass-shift transport. -/
def finiteHankelBoundaryAtomicMobiusMomentTrajectory
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  ∑ x ∈ finiteHankelBoundaryNodes c,
    atomicMobiusMomentTrajectory (finiteHankelBoundaryWeight s c x) x k h

/-- Velocity of the canonical finite-atomic continuation at the current face. -/
def finiteHankelBoundaryAtomicMobiusMomentTangent
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  -((k + 1 : ℕ) : ℝ) *
    ∑ x ∈ finiteHankelBoundaryNodes c,
      finiteHankelBoundaryWeight s c x * x ^ (k + 1)

/-- The canonical finite-atomic continuation has the displayed Möbius tangent at zero. -/
theorem finiteHankelBoundaryAtomicMobiusMomentTrajectory_hasDerivAt
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) :
    HasDerivAt (finiteHankelBoundaryAtomicMobiusMomentTrajectory s c k)
      (finiteHankelBoundaryAtomicMobiusMomentTangent s c k) 0 := by
  have hterm : ∀ x ∈ finiteHankelBoundaryNodes c,
      HasDerivAt
        (atomicMobiusMomentTrajectory (finiteHankelBoundaryWeight s c x) x k)
        (-((k + 1 : ℕ) : ℝ) * finiteHankelBoundaryWeight s c x * x ^ (k + 1)) 0 := by
    intro x _
    exact atomicMobiusMomentTrajectory_hasDerivAt
      (finiteHankelBoundaryWeight s c x) x k
  have hsum := HasDerivAt.sum hterm
  have hfun :
      (∑ x ∈ finiteHankelBoundaryNodes c,
          atomicMobiusMomentTrajectory (finiteHankelBoundaryWeight s c x) x k) =
        finiteHankelBoundaryAtomicMobiusMomentTrajectory s c k := by
    funext h
    simp only [finiteHankelBoundaryAtomicMobiusMomentTrajectory, Finset.sum_apply]
  rw [hfun] at hsum
  change HasDerivAt (finiteHankelBoundaryAtomicMobiusMomentTrajectory s c k)
    (∑ x ∈ finiteHankelBoundaryNodes c,
      -((k + 1 : ℕ) : ℝ) * finiteHankelBoundaryWeight s c x * x ^ (k + 1)) 0 at hsum
  convert! hsum using 1
  simp only [finiteHankelBoundaryAtomicMobiusMomentTangent]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- **Visible tangency.**  Canonical atomic transport and source mass-shift transport have the
same velocity in every degree whose next moment is visible on the current face. -/
theorem finiteHankelBoundaryAtomicMobiusMomentTangent_visible
    (s : ℕ → ℝ) {n k : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hk : k < 2 * n) :
    finiteHankelBoundaryAtomicMobiusMomentTangent s c k =
      -((k + 1 : ℕ) : ℝ) * s (k + 1) := by
  have hdegree : (X ^ (k + 1) : Polynomial ℝ).degree ≤
      ((2 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact WithBot.coe_le_coe.mpr (Nat.succ_le_iff.mpr hk)
  have hexact := momentFunctional_eq_finiteHankelBoundarySum
    c hhead hc hlast (X ^ (k + 1)) hdegree
  rw [momentFunctional_X_pow] at hexact
  simp only [eval_pow, eval_X] at hexact
  rw [finiteHankelBoundaryAtomicMobiusMomentTangent, ← hexact]

/-- **First-unseen normal defect.**  At the first degree beyond current-face control, source
velocity minus canonical atomic velocity is exactly `-(2n+1)` times the projective extension
coordinate.  Thus the RH-facing sign is a transverse transport orientation. -/
theorem finiteHankelBoundaryAtomicMobiusMomentTangent_firstUnseenDefect
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (-((2 * n + 1 : ℕ) : ℝ) * s (2 * n + 1)) -
        finiteHankelBoundaryAtomicMobiusMomentTangent s c (2 * n) =
      -((2 * n + 1 : ℕ) : ℝ) * finiteHankelBoundaryMonicRemainder s c := by
  rw [finiteHankelBoundaryAtomicMobiusMomentTangent,
    finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError s c hhead hc hlast]
  push_cast
  ring

/-- Positive extension orientation is equivalent to the completed source moving strictly below
the canonical finite-atomic continuation in the first unseen moment coordinate. -/
theorem finiteHankelBoundaryMonicRemainder_pos_iff_sourceTangent_lt_atomic
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < finiteHankelBoundaryMonicRemainder s c ↔
      -((2 * n + 1 : ℕ) : ℝ) * s (2 * n + 1) <
        finiteHankelBoundaryAtomicMobiusMomentTangent s c (2 * n) := by
  have hdefect :=
    finiteHankelBoundaryAtomicMobiusMomentTangent_firstUnseenDefect
      s c hhead hc hlast
  have hfactor : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  constructor <;> intro h <;> nlinarith

/-! ### Transport-only orientation no-go -/

/-- Four-atom third-difference source.  Its moments of degrees one and two vanish, while its
degree-three moment is the freely prescribed parameter `r`. -/
def atomicMobiusTransportNoGoMoment (r : ℝ) (k : ℕ) : ℝ :=
  (1 - r / 6) * (0 : ℝ) ^ k +
    (r / 2) * (1 : ℝ) ^ k -
    (r / 2) * (2 : ℝ) ^ k +
    (r / 6) * (3 : ℝ) ^ k

@[simp] theorem atomicMobiusTransportNoGoMoment_zero (r : ℝ) :
    atomicMobiusTransportNoGoMoment r 0 = 1 := by
  simp [atomicMobiusTransportNoGoMoment]

@[simp] theorem atomicMobiusTransportNoGoMoment_one (r : ℝ) :
    atomicMobiusTransportNoGoMoment r 1 = 0 := by
  norm_num [atomicMobiusTransportNoGoMoment]
  ring

@[simp] theorem atomicMobiusTransportNoGoMoment_two (r : ℝ) :
    atomicMobiusTransportNoGoMoment r 2 = 0 := by
  norm_num [atomicMobiusTransportNoGoMoment]
  ring

@[simp] theorem atomicMobiusTransportNoGoMoment_three (r : ℝ) :
    atomicMobiusTransportNoGoMoment r 3 = r := by
  norm_num [atomicMobiusTransportNoGoMoment]
  ring

/-- Exact finite signed-atomic Möbius orbit generating the no-go moments at time zero. -/
def atomicMobiusTransportNoGoTrajectory (r : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  atomicMobiusMomentTrajectory (1 - r / 6) 0 k h +
    atomicMobiusMomentTrajectory (r / 2) 1 k h -
    atomicMobiusMomentTrajectory (r / 2) 2 k h +
    atomicMobiusMomentTrajectory (r / 6) 3 k h

theorem atomicMobiusTransportNoGoTrajectory_zero (r : ℝ) (k : ℕ) :
    atomicMobiusTransportNoGoTrajectory r k 0 =
      atomicMobiusTransportNoGoMoment r k := by
  simp only [atomicMobiusTransportNoGoTrajectory,
    atomicMobiusMomentTrajectory, zero_mul, add_zero, one_pow, div_one]
  rw [atomicMobiusTransportNoGoMoment]
  ring

/-- **Transport-recursion no-go.**  For every prescribed first-unseen remainder, the complete
finite signed-atomic orbit obeys the exact mass-shift differential hierarchy
`mₖ' = -(k+1)mₖ₊₁`.  Therefore this hierarchy alone cannot select extension orientation. -/
theorem atomicMobiusTransportNoGoTrajectory_hasDerivAt (r : ℝ) (k : ℕ) :
    HasDerivAt (atomicMobiusTransportNoGoTrajectory r k)
      (-((k + 1 : ℕ) : ℝ) * atomicMobiusTransportNoGoMoment r (k + 1)) 0 := by
  have h0 := atomicMobiusMomentTrajectory_hasDerivAt (1 - r / 6) 0 k
  have h1 := atomicMobiusMomentTrajectory_hasDerivAt (r / 2) 1 k
  have h2 := atomicMobiusMomentTrajectory_hasDerivAt (r / 2) 2 k
  have h3 := atomicMobiusMomentTrajectory_hasDerivAt (r / 6) 3 k
  have hsum := ((h0.add h1).sub h2).add h3
  convert! hsum using 1
  rw [atomicMobiusTransportNoGoMoment]
  push_cast
  ring

/-- Projective null vector of the common size-two flat face in the transport no-go family. -/
def atomicMobiusTransportNoGoKernel : Fin 2 → ℝ := ![0, 1]

theorem atomicMobiusTransportNoGoKernel_last :
    atomicMobiusTransportNoGoKernel (Fin.last 1) ≠ 0 := by
  change (1 : ℝ) ≠ 0
  norm_num

/-- Every member of the no-go family has the same positive-definite Hankel head. -/
theorem atomicMobiusTransportNoGoMoment_head_posDef (r : ℝ) :
    (momentHankelMatrix (atomicMobiusTransportNoGoMoment r) 1).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i
    fin_cases j
    simp [momentHankelMatrix]
  · intro x hx
    have hx0 : x 0 ≠ 0 := by
      intro hx0
      apply hx
      funext i
      fin_cases i
      exact hx0
    simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_one]
    simp [momentHankelMatrix]
    exact hx0

/-- Every member has the same singular current face and projective null line. -/
theorem atomicMobiusTransportNoGoMoment_kernel (r : ℝ) :
    momentHankelMatrix (atomicMobiusTransportNoGoMoment r) 2 *ᵥ
      atomicMobiusTransportNoGoKernel = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, momentHankelMatrix,
      atomicMobiusTransportNoGoKernel]

/-- **Exact orientation countermodel.**  The positive head, singular face, null line, and full
Möbius transport hierarchy stay fixed while the projective first extension remainder is the
arbitrary real parameter `r`.  Source-specific constitutive information beyond mass-shift
transport is therefore logically necessary. -/
theorem atomicMobiusTransportNoGo_monicRemainder (r : ℝ) :
    finiteHankelBoundaryMonicRemainder
        (atomicMobiusTransportNoGoMoment r) atomicMobiusTransportNoGoKernel = r := by
  have hraw :
      finiteHankelNullPolynomial atomicMobiusTransportNoGoKernel = X := by
    rw [finiteHankelNullPolynomial, Polynomial.ofFn_eq_sum_monomial,
      Fin.sum_univ_two]
    simp [atomicMobiusTransportNoGoKernel, monomial_one_right_eq_X_pow]
  have hmonic :
      finiteHankelNullMonicPolynomial atomicMobiusTransportNoGoKernel = X := by
    rw [finiteHankelNullMonicPolynomial, hraw]
    simp
  rw [finiteHankelBoundaryMonicRemainder, hmonic]
  rw [show X ^ (1 + 1) * X = (X : Polynomial ℝ) ^ 3 by ring,
    momentFunctional_X_pow]
  exact atomicMobiusTransportNoGoMoment_three r

/-! ### The extension class is a shifted-square energy -/

/-- On a Hankel null vector, the shifted square of its raw null polynomial is exactly the
terminal coefficient times the first unseen moment pairing.  All other coefficients disappear by
the current kernel equations. -/
theorem momentFunctional_X_mul_finiteHankelNullPolynomial_sq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
        (X * finiteHankelNullPolynomial c * finiteHankelNullPolynomial c) =
      c (Fin.last n) *
        momentFunctional s (X ^ (n + 1) * finiteHankelNullPolynomial c) := by
  let P := finiteHankelNullPolynomial c
  let a := c (Fin.last n)
  let q := X * P - C a * X ^ (n + 1)
  have hPne : P ≠ 0 := finiteHankelNullPolynomial_ne_zero c hlast
  have hPdeg : P.degree = (n : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hPne,
      finiteHankelNullPolynomial_natDegree c hlast]
  have hXPne : X * P ≠ 0 := mul_ne_zero X_ne_zero hPne
  have hXPdeg : (X * P).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X, hPdeg]
    rw [add_comm]
    norm_cast
  have hmonomialNe : C a * X ^ (n + 1) ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hlast) (pow_ne_zero _ X_ne_zero)
  have hmonomialDeg : (C a * X ^ (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) := by
    exact Polynomial.degree_C_mul_X_pow _ hlast
  have hlead : (X * P).leadingCoeff = (C a * X ^ (n + 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X,
      one_mul, Polynomial.leadingCoeff_C_mul_X_pow]
    exact finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast
  have hqdeg : q.degree < ((n + 1 : ℕ) : WithBot ℕ) := by
    dsimp [q]
    have h := Polynomial.degree_sub_lt
      (by rw [hXPdeg, hmonomialDeg]) hXPne hlead
    rwa [hXPdeg] at h
  have hqnat : q.natDegree < n + 1 := by
    by_cases hqzero : q = 0
    · simp [hqzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hqzero).mpr hqdeg
  have horth : momentInner s P q = 0 := by
    exact momentInner_finiteHankelNullPolynomial_eq_zero_of_kernel hc hqnat
  have hsplit : X * P = q + C a * X ^ (n + 1) := by
    dsimp [q]
    ring
  change momentFunctional s (X * P * P) =
    a * momentFunctional s (X ^ (n + 1) * P)
  calc
    momentFunctional s (X * P * P) = momentInner s P (X * P) := by
      rw [momentInner_def]
      congr 1
      ring
    _ = momentInner s P (q + C a * X ^ (n + 1)) := by rw [← hsplit]
    _ = momentInner s P q + momentInner s P (C a * X ^ (n + 1)) := by
      rw [momentInner_add_right]
    _ = momentInner s P (C a * X ^ (n + 1)) := by rw [horth, zero_add]
    _ = a * momentFunctional s (X ^ (n + 1) * P) := by
      rw [momentInner_def, show P * (C a * X ^ (n + 1)) =
          a • (X ^ (n + 1) * P) by
        simp only [Polynomial.smul_eq_C_mul]
        ring,
        momentFunctional_smul]

/-- **Stieltjes boundary-energy law.** The projective extension coordinate is exactly the moment
of `X` times the square of the monic null polynomial.  The mass-shifted spectral-face problem is
therefore one shifted-Hankel square on the current Hankel kernel. -/
theorem finiteHankelBoundaryMonicRemainder_eq_shiftedSquare
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryMonicRemainder s c =
      momentFunctional s
        (X * finiteHankelNullMonicPolynomial c * finiteHankelNullMonicPolynomial c) := by
  have hraw := momentFunctional_X_mul_finiteHankelNullPolynomial_sq s c hc hlast
  rw [finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw s c hlast]
  rw [finiteHankelNullMonicPolynomial,
    finiteHankelNullPolynomial_leadingCoeff_eq_terminal c hlast]
  rw [show X *
      (finiteHankelNullPolynomial c * C (c (Fin.last n))⁻¹) *
      (finiteHankelNullPolynomial c * C (c (Fin.last n))⁻¹) =
        (c (Fin.last n))⁻¹ ^ 2 •
          (X * finiteHankelNullPolynomial c * finiteHankelNullPolynomial c) by
    simp only [Polynomial.smul_eq_C_mul]
    rw [map_pow]
    ring,
    momentFunctional_smul, hraw]
  field_simp [hlast]

/-! ### The shifted square is an oriented Christoffel-port imbalance -/

/-- **Universal Christoffel-port polarization.**  For every moment functional, the difference
between the forward and backward affine-multiplier square energies is exactly four times the
adjacent Hankel energy.  No positivity or moment-representability assumption is used. -/
theorem momentFunctional_christoffelPortDifference
    (s : ℕ → ℝ) (p : Polynomial ℝ) (a : ℝ) :
    momentFunctional s (((X + C a) * p) ^ 2) -
        momentFunctional s (((X - C a) * p) ^ 2) =
      4 * a * momentFunctional s (X * p * p) := by
  have hC4 : C (4 : ℝ) = (4 : Polynomial ℝ) := by
    exact map_natCast (Polynomial.C : ℝ →+* Polynomial ℝ) 4
  have hpoly :
      ((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2 =
        (4 * a) • (X * p * p) := by
    simp only [Polynomial.smul_eq_C_mul]
    rw [map_mul, hC4]
    ring
  have hlinear :
      momentFunctional s (((X + C a) * p) ^ 2) -
          momentFunctional s (((X - C a) * p) ^ 2) =
        momentFunctional s
          (((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2) := by
    symm
    calc
      momentFunctional s
          (((X + C a) * p) ^ 2 - ((X - C a) * p) ^ 2) =
          momentFunctional s
            (((X + C a) * p) ^ 2 + -((X - C a) * p) ^ 2) := by
              rw [sub_eq_add_neg]
      _ = momentFunctional s (((X + C a) * p) ^ 2) +
          momentFunctional s (-((X - C a) * p) ^ 2) := by
            rw [momentFunctional_add]
      _ = momentFunctional s (((X + C a) * p) ^ 2) -
          momentFunctional s (((X - C a) * p) ^ 2) := by
            rw [show -((X - C a) * p) ^ 2 =
                (-1 : ℝ) • (((X - C a) * p) ^ 2) by rw [neg_one_smul],
              momentFunctional_smul]
            ring
  rw [hlinear, hpoly, momentFunctional_smul]

/-- The symmetric two-port sum contains an even second-extension capacity and the current square
energy, but no orientation term.  Together with `momentFunctional_christoffelPortDifference`, this
is the exact capacity/orientation decomposition of the affine-multiplier pair. -/
theorem momentFunctional_christoffelPortSum
    (s : ℕ → ℝ) (p : Polynomial ℝ) (a : ℝ) :
    momentFunctional s (((X + C a) * p) ^ 2) +
        momentFunctional s (((X - C a) * p) ^ 2) =
      2 * momentFunctional s (X ^ 2 * p * p) +
        2 * a ^ 2 * momentFunctional s (p * p) := by
  have hC2 : C (2 : ℝ) = (2 : Polynomial ℝ) := by
    exact map_natCast (Polynomial.C : ℝ →+* Polynomial ℝ) 2
  have hpoly :
      ((X + C a) * p) ^ 2 + ((X - C a) * p) ^ 2 =
        (2 : ℝ) • (X ^ 2 * p * p) + (2 * a ^ 2) • (p * p) := by
    simp only [Polynomial.smul_eq_C_mul]
    rw [map_mul, map_pow, hC2]
    ring
  calc
    momentFunctional s (((X + C a) * p) ^ 2) +
        momentFunctional s (((X - C a) * p) ^ 2) =
      momentFunctional s
        ((((X + C a) * p) ^ 2) + (((X - C a) * p) ^ 2)) := by
          rw [momentFunctional_add]
    _ = momentFunctional s
        ((2 : ℝ) • (X ^ 2 * p * p) + (2 * a ^ 2) • (p * p)) := by
          rw [hpoly]
    _ = 2 * momentFunctional s (X ^ 2 * p * p) +
        2 * a ^ 2 * momentFunctional s (p * p) := by
          simp only [momentFunctional_add, momentFunctional_smul]

/-- A monic null polynomial has zero square energy on its current singular Hankel face. -/
theorem momentFunctional_finiteHankelNullMonicPolynomial_sq_eq_zero
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
      (finiteHankelNullMonicPolynomial c * finiteHankelNullMonicPolynomial c) = 0 := by
  have hdeg : (finiteHankelNullMonicPolynomial c).natDegree < n + 1 := by
    rw [finiteHankelNullMonicPolynomial_natDegree c hlast]
    omega
  have horth :=
    momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel hc hdeg
  rw [momentInner_def] at horth
  exact horth

/-- On a flat Hankel face, the canonical extension coordinate is exactly the normalized
forward-minus-backward Christoffel-port imbalance of its monic null polynomial. -/
theorem finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (a : ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
          (((X + C a) * finiteHankelNullMonicPolynomial c) ^ 2) -
        momentFunctional s
          (((X - C a) * finiteHankelNullMonicPolynomial c) ^ 2) =
      4 * a * finiteHankelBoundaryMonicRemainder s c := by
  rw [momentFunctional_christoffelPortDifference,
    ← finiteHankelBoundaryMonicRemainder_eq_shiftedSquare s c hc hlast]

/-- **Capacity/orientation separation on a flat face.**  The two affine-multiplier ports share one
even capacity `L(X²p²)` and differ only by the signed first extension coordinate.  Current null
incidence kills the third possible coordinate `L(p²)` exactly. -/
theorem finiteHankelBoundary_christoffelPortCapacityOrientation
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (a : ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentFunctional s
        (((X + C a) * finiteHankelNullMonicPolynomial c) ^ 2) =
          momentFunctional s
              (X ^ 2 * finiteHankelNullMonicPolynomial c *
                finiteHankelNullMonicPolynomial c) +
            2 * a * finiteHankelBoundaryMonicRemainder s c ∧
      momentFunctional s
        (((X - C a) * finiteHankelNullMonicPolynomial c) ^ 2) =
          momentFunctional s
              (X ^ 2 * finiteHankelNullMonicPolynomial c *
                finiteHankelNullMonicPolynomial c) -
            2 * a * finiteHankelBoundaryMonicRemainder s c := by
  let p := finiteHankelNullMonicPolynomial c
  let Eplus := momentFunctional s (((X + C a) * p) ^ 2)
  let Eminus := momentFunctional s (((X - C a) * p) ^ 2)
  let T := momentFunctional s (X ^ 2 * p * p)
  let R := finiteHankelBoundaryMonicRemainder s c
  have hzero : momentFunctional s (p * p) = 0 := by
    exact momentFunctional_finiteHankelNullMonicPolynomial_sq_eq_zero
      s c hc hlast
  have hsum := momentFunctional_christoffelPortSum s p a
  have hdiff :=
    finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
      s c a hc hlast
  change Eplus + Eminus =
    2 * T + 2 * a ^ 2 * momentFunctional s (p * p) at hsum
  change Eplus - Eminus = 4 * a * R at hdiff
  rw [hzero, mul_zero, add_zero] at hsum
  change Eplus = T + 2 * a * R ∧ Eminus = T - 2 * a * R
  constructor <;> linarith only [hsum, hdiff]

/-- **Port-orientation criterion.**  Positivity of the first extension coordinate is equivalent
to strict dominance of the forward unit Christoffel port over the backward unit port. -/
theorem finiteHankelBoundaryMonicRemainder_pos_iff_christoffelPortOrder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < finiteHankelBoundaryMonicRemainder s c ↔
      momentFunctional s
          (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
        momentFunctional s
          (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
  have hdiff :=
    finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
      s c 1 hc hlast
  norm_num at hdiff
  constructor
  · intro h
    have h' :
        momentFunctional s
            (((X - 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
          momentFunctional s
            (((X + 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
      linarith
    simpa using h'
  · intro h
    have h' :
        momentFunctional s
            (((X - 1) * finiteHankelNullMonicPolynomial c) ^ 2) <
          momentFunctional s
            (((X + 1) * finiteHankelNullMonicPolynomial c) ^ 2) := by
      simpa using h
    linarith

/-! ### The extension coordinate is invisible to the current face -/

/-- Perturb one coordinate of a moment sequence additively. -/
def momentCoordinatePerturbation
    (s : ℕ → ℝ) (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  s k + if k = N then δ else 0

/-- A one-coordinate moment perturbation is evaluated by the corresponding polynomial
coefficient. -/
theorem momentFunctional_momentCoordinatePerturbation
    (s : ℕ → ℝ) (N : ℕ) (δ : ℝ) (p : Polynomial ℝ) :
    momentFunctional (momentCoordinatePerturbation s N δ) p =
      momentFunctional s p + δ * p.coeff N := by
  rw [momentFunctional_eq_support_sum, momentFunctional_eq_support_sum]
  simp only [momentCoordinatePerturbation, mul_add, Finset.sum_add_distrib]
  have hpert :
      (∑ k ∈ p.support, p.coeff k * if k = N then δ else 0) =
        δ * p.coeff N := by
    by_cases hN : N ∈ p.support
    · rw [Finset.sum_eq_single N]
      · simp [mul_comm]
      · intro k hk hkN
        simp [hkN]
      · exact fun h => (h hN).elim
    · have hcoeff : p.coeff N = 0 := by
        by_contra hcoeff
        exact hN (Polynomial.mem_support_iff.mpr hcoeff)
      rw [hcoeff]
      simp [hN]
  rw [hpert]

/-- Changing only moment `2n+1` leaves the entire size-`n+1` Hankel face unchanged. -/
theorem momentHankelMatrix_momentCoordinatePerturbation_firstUnseen
    (s : ℕ → ℝ) (n : ℕ) (δ : ℝ) :
    momentHankelMatrix (momentCoordinatePerturbation s (2 * n + 1) δ) (n + 1) =
      momentHankelMatrix s (n + 1) := by
  ext i j
  have hij : (i : ℕ) + (j : ℕ) ≠ 2 * n + 1 := by
    have hi : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.isLt
    have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    omega
  simp [momentHankelMatrix, momentCoordinatePerturbation, hij]

/-- Distinct first-unseen perturbations give distinct complete moment sequences. -/
theorem momentCoordinatePerturbation_injective
    (s : ℕ → ℝ) (N : ℕ) :
    Function.Injective (momentCoordinatePerturbation s N) := by
  intro δ ε h
  have hN := congrFun h N
  simpa [momentCoordinatePerturbation] using hN

/-- **Infinite-branching face law.**  Every finite Hankel face has infinitely many complete moment
extensions already along its first unseen coordinate.  Thus a tower of finite Hankel observations
fails local finiteness at every extension step. -/
theorem sameMomentHankelFace_infinite
    (s : ℕ → ℝ) (n : ℕ) :
    Set.Infinite {t : ℕ → ℝ |
      momentHankelMatrix t (n + 1) = momentHankelMatrix s (n + 1)} := by
  let f : ℝ → (ℕ → ℝ) := fun δ =>
    momentCoordinatePerturbation s (2 * n + 1) δ
  have hf : Function.Injective f :=
    momentCoordinatePerturbation_injective s (2 * n + 1)
  apply (Set.infinite_range_of_injective hf).mono
  rintro t ⟨δ, rfl⟩
  exact momentHankelMatrix_momentCoordinatePerturbation_firstUnseen s n δ

/-- The monic first extension class translates by exactly the unseen coordinate perturbation. -/
theorem finiteHankelBoundaryMonicRemainder_momentCoordinatePerturbation
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (δ : ℝ) :
    finiteHankelBoundaryMonicRemainder
        (momentCoordinatePerturbation s (2 * n + 1) δ) c =
      finiteHankelBoundaryMonicRemainder s c + δ := by
  let P : Polynomial ℝ :=
    X ^ (n + 1) * finiteHankelNullMonicPolynomial c
  have hmonic : P.Monic :=
    (Polynomial.monic_X_pow (n + 1)).mul
      (finiteHankelNullMonicPolynomial_monic c hlast)
  have hdegree : P.natDegree = 2 * n + 1 := by
    rw [show P = X ^ (n + 1) * finiteHankelNullMonicPolynomial c by rfl,
      (Polynomial.monic_X_pow (R := ℝ) (n + 1)).natDegree_mul
        (finiteHankelNullMonicPolynomial_monic c hlast),
      Polynomial.natDegree_X_pow,
      finiteHankelNullMonicPolynomial_natDegree c hlast]
    omega
  have hcoeff : P.coeff (2 * n + 1) = 1 := by
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  rw [finiteHankelBoundaryMonicRemainder,
    finiteHankelBoundaryMonicRemainder,
    momentFunctional_momentCoordinatePerturbation]
  change momentFunctional s P + δ * P.coeff (2 * n + 1) =
    momentFunctional s P + δ
  rw [hcoeff]
  ring

/-- **Face-indeterminacy theorem.** Keeping every current Hankel entry, null polynomial, root,
node, and quadrature weight fixed, the first extension class can be assigned any prescribed real
value by changing only moment `2n+1`. -/
theorem exists_momentSequence_same_face_monicRemainder_eq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) (r : ℝ) :
    ∃ t : ℕ → ℝ,
      momentHankelMatrix t (n + 1) = momentHankelMatrix s (n + 1) ∧
        finiteHankelBoundaryMonicRemainder t c = r := by
  let δ := r - finiteHankelBoundaryMonicRemainder s c
  refine ⟨momentCoordinatePerturbation s (2 * n + 1) δ,
    momentHankelMatrix_momentCoordinatePerturbation_firstUnseen s n δ, ?_⟩
  rw [finiteHankelBoundaryMonicRemainder_momentCoordinatePerturbation s c hlast]
  dsimp [δ]
  ring

/-- **Port-orientation face no-go.**  Keeping the complete current Hankel face fixed, the
forward-minus-backward unit Christoffel-port imbalance can be assigned any prescribed real value.
Thus no theorem depending only on current-face incidence can select its orientation. -/
theorem exists_momentSequence_same_face_christoffelPortDifference_eq
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (d : ℝ) :
    ∃ t : ℕ → ℝ,
      momentHankelMatrix t (n + 1) = momentHankelMatrix s (n + 1) ∧
        momentFunctional t
              (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) -
            momentFunctional t
              (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) = d := by
  obtain ⟨t, hface, hremainder⟩ :=
    exists_momentSequence_same_face_monicRemainder_eq s c hlast (d / 4)
  have hct : momentHankelMatrix t (n + 1) *ᵥ c = 0 := by
    rw [hface]
    exact hc
  refine ⟨t, hface, ?_⟩
  have hdiff :=
    finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
      t c 1 hct hlast
  norm_num at hdiff
  rw [hremainder] at hdiff
  calc
    momentFunctional t
          (((X + C 1) * finiteHankelNullMonicPolynomial c) ^ 2) -
        momentFunctional t
          (((X - C 1) * finiteHankelNullMonicPolynomial c) ^ 2) =
        4 * (d / 4) := by simpa using hdiff
    _ = d := by ring

/-- The monic extension class depends only on the projective null line, not on a nonzero choice of
kernel-vector scale. -/
theorem finiteHankelBoundaryMonicRemainder_smul
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
      finiteHankelBoundaryMonicRemainder s c := by
  let ac : Fin (n + 1) → ℝ := fun i => a * c i
  have hlastac : ac (Fin.last n) ≠ 0 := mul_ne_zero ha hlast
  have hcoupling :
      GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) ac =
        a * GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling s (n + 1) c := by
    rw [GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
      GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [ac]
    ring
  have hnew :=
    terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s ac hlastac
  have hold :=
    terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
      s c hlast
  rw [hcoupling] at hnew
  dsimp [ac] at hnew
  have heq :
      (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
        (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s c := by
    calc
      (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s (fun i => a * c i) =
          (a * c (Fin.last n)) *
            (a * GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
              s (n + 1) c) := hnew.symm
      _ = a ^ 2 *
          (c (Fin.last n) *
            GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling
              s (n + 1) c) := by ring
      _ = a ^ 2 *
          (c (Fin.last n) ^ 2 * finiteHankelBoundaryMonicRemainder s c) := by
            rw [hold]
      _ = (a * c (Fin.last n)) ^ 2 *
          finiteHankelBoundaryMonicRemainder s c := by ring
  exact mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero ha hlast)) heq

end

end HTGeometry
