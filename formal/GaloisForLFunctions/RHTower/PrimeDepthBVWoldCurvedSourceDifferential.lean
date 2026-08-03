import GaloisForLFunctions.RHTower.PrimeEssentialEdgeOccupationDet2BVRelativeClass
import GaloisForLFunctions.RHTower.EulerPrimitiveJointDepthOffDiagonalCountertransport
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

/-!
# Prime/depth BV--Wold curved source differential

The relative `det₂` class has two independent source records at a
prime/depth cell `i=(p,e)`:

* the depth-transported singular BV trace
  `m_i = (1-p⁻¹)p⁻ᵉ`;
* the Wold--Gamma depth clock `lambda_i = log(p^(e+1))`.

Their alternating edge coupling

`theta(i,j) = m_i lambda_j - m_j lambda_i`

is diagonal-zero and sign-indefinite.  Unlike the previously constructed
reflected incidence `exp(a(lambda_j-lambda_i))`, it is not an endpoint
gauge.  On the explicit labelled triangle

`(2,0), (2,1), (2,2)`

its additive curvature is exactly `-log(2)/8`.  Moreover, the first two
adjacent edges have the same log-clock difference but unequal connection
coefficients, so the connection is not even a function of clock difference.

Exponentiating `a*theta` gives a discrete line connection.  This file
constructs its degree-zero and degree-one exterior covariant derivatives
and proves that their composite is the labelled curvature coefficient.
Specializing `a=2 Re(rho)-1` pointwise over the Xi divisor preserves the
divisor, prime, and depth labels.  Global flatness is equivalent to RH; it
is not asserted.  All results below are unconditional.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Two source records and their alternating edge connection -/

/-- Prime/depth source cell. -/
abbrev PrimeDepthBVWoldCell := Nat.Primes × ℕ

/-- Wold depth transport of the singular BV first trace.  Depth zero is the
literal residue-one trace; higher depths are its canonical Wold cells. -/
def primeDepthBVFirstTraceDepthWeight
    (i : PrimeDepthBVWoldCell) : ℝ :=
  unitExponentialWoldCellMass (Real.log i.1.1) i.2

theorem primeDepthBVFirstTraceDepthWeight_eq
    (p : Nat.Primes) (e : ℕ) :
    primeDepthBVFirstTraceDepthWeight (p, e) =
      (1 - ((p.1 : ℝ)⁻¹)) * ((p.1 : ℝ)⁻¹) ^ e := by
  rw [primeDepthBVFirstTraceDepthWeight,
    unitExponentialWoldCellMass_log (by exact_mod_cast p.2.pos)]

theorem primeDepthBVFirstTraceDepthWeight_zero
    (p : Nat.Primes) :
    primeDepthBVFirstTraceDepthWeight (p, 0) =
      unitExponentialWoldBoundaryMass (Real.log p.1) := by
  simp [primeDepthBVFirstTraceDepthWeight,
    unitExponentialWoldCellMass]

/-- The depth-zero record is literally the residue-one reading of the
relative Wold--BV spectral-zeta class constructed from the essential source
edge. -/
theorem primeDepthBVFirstTraceDepthWeight_zero_eq_relativeSpectralZetaResidue
    (p : Nat.Primes) :
    Filter.Tendsto
      (fun s : ℂ => (s - 1) * primeWoldBVRelativeSpectralZeta p s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds ((primeDepthBVFirstTraceDepthWeight (p, 0) : ℝ) : ℂ)) := by
  rw [primeDepthBVFirstTraceDepthWeight_zero]
  exact primeWoldBVRelativeSpectralZeta_residue_one_eq_woldBoundaryMass p

/-- Alternating coupling of singular BV mass and regular Wold--Gamma depth
clock.  Both endpoint labels remain visible. -/
def primeDepthBVWoldConnection
    (i j : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVFirstTraceDepthWeight i *
      xiGammaEulerPrimitivePrimeDepthLogClock j -
    primeDepthBVFirstTraceDepthWeight j *
      xiGammaEulerPrimitivePrimeDepthLogClock i

@[simp]
theorem primeDepthBVWoldConnection_self
    (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldConnection i i = 0 := by
  simp [primeDepthBVWoldConnection]

theorem primeDepthBVWoldConnection_swap
    (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldConnection j i =
      -primeDepthBVWoldConnection i j := by
  simp only [primeDepthBVWoldConnection]
  ring

/-- First vertex of the exact nonseparability witness. -/
def primeDepthBVWoldWitnessZero : PrimeDepthBVWoldCell :=
  (⟨2, Nat.prime_two⟩, 0)

/-- Second vertex of the exact nonseparability witness. -/
def primeDepthBVWoldWitnessOne : PrimeDepthBVWoldCell :=
  (⟨2, Nat.prime_two⟩, 1)

/-- Third vertex of the exact nonseparability witness. -/
def primeDepthBVWoldWitnessTwo : PrimeDepthBVWoldCell :=
  (⟨2, Nat.prime_two⟩, 2)

/-- The connection has both signs before every scalar trace. -/
theorem primeDepthBVWoldConnection_witness_pos :
    0 < primeDepthBVWoldConnection
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne := by
  rw [primeDepthBVWoldConnection]
  simp only [primeDepthBVFirstTraceDepthWeight,
    primeDepthBVWoldWitnessZero,
    primeDepthBVWoldWitnessOne,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  simp_rw [unitExponentialWoldCellMass_log
    (by norm_num : (0 : ℝ) < 2)]
  norm_num
  have hlog : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

theorem primeDepthBVWoldConnection_witness_neg :
    primeDepthBVWoldConnection
      primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessZero < 0 := by
  rw [primeDepthBVWoldConnection_swap]
  exact neg_neg_of_pos primeDepthBVWoldConnection_witness_pos

/-- Additive two-simplex curvature of the BV--Wold edge connection. -/
def primeDepthBVWoldAdditiveCurvature
    (i j k : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldConnection i j +
    primeDepthBVWoldConnection j k +
      primeDepthBVWoldConnection k i

/-- Exact same-prime, three-depth curvature witness. -/
theorem primeDepthBVWoldAdditiveCurvature_witness :
    primeDepthBVWoldAdditiveCurvature
        primeDepthBVWoldWitnessZero
        primeDepthBVWoldWitnessOne
        primeDepthBVWoldWitnessTwo =
      -Real.log 2 / 8 := by
  rw [primeDepthBVWoldAdditiveCurvature,
    primeDepthBVWoldConnection, primeDepthBVWoldConnection,
    primeDepthBVWoldConnection]
  simp only [primeDepthBVFirstTraceDepthWeight,
    primeDepthBVWoldWitnessZero,
    primeDepthBVWoldWitnessOne, primeDepthBVWoldWitnessTwo,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  simp_rw [unitExponentialWoldCellMass_log
    (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

theorem primeDepthBVWoldAdditiveCurvature_witness_ne_zero :
    primeDepthBVWoldAdditiveCurvature
        primeDepthBVWoldWitnessZero
        primeDepthBVWoldWitnessOne
        primeDepthBVWoldWitnessTwo ≠ 0 := by
  rw [primeDepthBVWoldAdditiveCurvature_witness]
  exact div_ne_zero
    (neg_ne_zero.mpr <| ne_of_gt <|
      Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (by norm_num)

/-- **Nonseparability.**  No vertex potential can produce the BV--Wold
edge field.  The explicit triangle curvature is the obstruction. -/
theorem not_exists_primeDepthBVWoldConnection_vertexPotential :
    ¬ ∃ phi : PrimeDepthBVWoldCell → ℝ,
      ∀ i j, primeDepthBVWoldConnection i j = phi j - phi i := by
  rintro ⟨phi, hphi⟩
  have hzero :
      primeDepthBVWoldAdditiveCurvature
          primeDepthBVWoldWitnessZero
          primeDepthBVWoldWitnessOne
          primeDepthBVWoldWitnessTwo = 0 := by
    rw [primeDepthBVWoldAdditiveCurvature,
      hphi primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne,
      hphi primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo,
      hphi primeDepthBVWoldWitnessTwo primeDepthBVWoldWitnessZero]
    ring
  exact primeDepthBVWoldAdditiveCurvature_witness_ne_zero hzero

/-- The two adjacent witness edges have the same Wold log-clock
difference. -/
theorem primeDepthBVWoldWitness_adjacentClockDifferences_eq :
    xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessOne -
        xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessZero =
      xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessTwo -
        xiGammaEulerPrimitivePrimeDepthLogClock primeDepthBVWoldWitnessOne := by
  simp only [primeDepthBVWoldWitnessZero, primeDepthBVWoldWitnessOne,
    primeDepthBVWoldWitnessTwo,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  ring

/-- Despite equal clock differences, the connection coefficients differ
by the nonzero exact amount `log 2 / 4`. -/
theorem primeDepthBVWoldConnection_adjacentDifference :
    primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne -
        primeDepthBVWoldConnection
          primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo =
      Real.log 2 / 4 := by
  rw [primeDepthBVWoldConnection, primeDepthBVWoldConnection]
  simp only [primeDepthBVFirstTraceDepthWeight,
    primeDepthBVWoldWitnessZero, primeDepthBVWoldWitnessOne,
    primeDepthBVWoldWitnessTwo,
    xiGammaEulerPrimitivePrimeDepthLogClock_apply]
  norm_num
  simp_rw [unitExponentialWoldCellMass_log
    (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring

/-- Strong nonseparability required by the Route-R frontier: the edge
connection is not a function only of log-clock difference. -/
theorem not_exists_primeDepthBVWoldConnection_clockDifferenceFunction :
    ¬ ∃ F : ℝ → ℝ, ∀ i j,
      primeDepthBVWoldConnection i j =
        F (xiGammaEulerPrimitivePrimeDepthLogClock j -
          xiGammaEulerPrimitivePrimeDepthLogClock i) := by
  rintro ⟨F, hF⟩
  have hsame :
      primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne =
        primeDepthBVWoldConnection
          primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo := by
    rw [hF, hF, primeDepthBVWoldWitness_adjacentClockDifferences_eq]
  have hzero :
      primeDepthBVWoldConnection
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne -
          primeDepthBVWoldConnection
            primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo = 0 :=
    sub_eq_zero.mpr hsame
  rw [primeDepthBVWoldConnection_adjacentDifference] at hzero
  exact (div_ne_zero
    (ne_of_gt <| Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (by norm_num)) hzero

/-! ## Multiplicative transport and curved exterior differential -/

/-- Exponentiated nonseparable transport at centered real parameter `a`. -/
def primeDepthBVWoldTransport
    (a : ℝ) (i j : PrimeDepthBVWoldCell) : ℝ :=
  Real.exp (a * primeDepthBVWoldConnection i j)

theorem primeDepthBVWoldTransport_pos
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    0 < primeDepthBVWoldTransport a i j :=
  Real.exp_pos _

@[simp]
theorem primeDepthBVWoldTransport_self
    (a : ℝ) (i : PrimeDepthBVWoldCell) :
    primeDepthBVWoldTransport a i i = 1 := by
  simp [primeDepthBVWoldTransport]

theorem primeDepthBVWoldTransport_swap
    (a : ℝ) (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldTransport a j i =
      (primeDepthBVWoldTransport a i j)⁻¹ := by
  rw [primeDepthBVWoldTransport, primeDepthBVWoldTransport,
    primeDepthBVWoldConnection_swap]
  rw [show a * -primeDepthBVWoldConnection i j =
      -(a * primeDepthBVWoldConnection i j) by ring,
    Real.exp_neg]

/-- Exact failure of multiplicative flatness on the witness triangle. -/
theorem primeDepthBVWoldTransport_witness_flat_iff (a : ℝ) :
    primeDepthBVWoldTransport a
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne *
        primeDepthBVWoldTransport a
          primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo =
      primeDepthBVWoldTransport a
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo ↔
    a = 0 := by
  rw [primeDepthBVWoldTransport, primeDepthBVWoldTransport,
    primeDepthBVWoldTransport, ← Real.exp_add,
    Real.exp_injective.eq_iff]
  have htri :
      primeDepthBVWoldConnection
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne +
          primeDepthBVWoldConnection
            primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo -
        primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo =
      -Real.log 2 / 8 := by
    have hswap := primeDepthBVWoldConnection_swap
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo
    calc
      primeDepthBVWoldConnection
            primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne +
          primeDepthBVWoldConnection
            primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo -
        primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo =
          primeDepthBVWoldAdditiveCurvature
            primeDepthBVWoldWitnessZero
            primeDepthBVWoldWitnessOne
            primeDepthBVWoldWitnessTwo := by
              rw [primeDepthBVWoldAdditiveCurvature, hswap]
              ring
      _ = -Real.log 2 / 8 :=
        primeDepthBVWoldAdditiveCurvature_witness
  rw [show
    a * primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne +
        a * primeDepthBVWoldConnection
          primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo =
      a * primeDepthBVWoldConnection
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo ↔
        a * (primeDepthBVWoldConnection
              primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne +
            primeDepthBVWoldConnection
              primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo -
            primeDepthBVWoldConnection
              primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo) = 0 by
      constructor <;> intro h <;> nlinarith]
  rw [htri, mul_eq_zero]
  simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

/-- Degree-zero, degree-one, and degree-two complex cochains on the complete
prime/depth incidence complex. -/
abbrev PrimeDepthBVWoldZeroCochain := PrimeDepthBVWoldCell → ℂ
abbrev PrimeDepthBVWoldOneCochain :=
  PrimeDepthBVWoldCell → PrimeDepthBVWoldCell → ℂ
abbrev PrimeDepthBVWoldTwoCochain :=
  PrimeDepthBVWoldCell → PrimeDepthBVWoldCell →
    PrimeDepthBVWoldCell → ℂ

/-- Degree-zero exterior covariant derivative for the BV--Wold transport. -/
def primeDepthBVWoldCovariantD0 (a : ℝ) :
    PrimeDepthBVWoldZeroCochain →ₗ[ℂ]
      PrimeDepthBVWoldOneCochain where
  toFun f i j := (primeDepthBVWoldTransport a i j : ℂ) * f j - f i
  map_add' f g := by
    funext i j
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- Degree-one exterior covariant derivative for the same transport. -/
def primeDepthBVWoldCovariantD1 (a : ℝ) :
    PrimeDepthBVWoldOneCochain →ₗ[ℂ]
      PrimeDepthBVWoldTwoCochain where
  toFun omega i j k :=
    (primeDepthBVWoldTransport a i j : ℂ) * omega j k -
      omega i k + omega i j
  map_add' omega eta := by
    funext i j k
    simp only [Pi.add_apply]
    ring
  map_smul' c omega := by
    funext i j k
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- **Curved-square law.**  The square of the pre-scalar differential is
the unsummed, fully labelled transport curvature. -/
theorem primeDepthBVWoldCovariantD1_comp_D0_apply
    (a : ℝ) (f : PrimeDepthBVWoldZeroCochain)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldCovariantD1 a
        (primeDepthBVWoldCovariantD0 a f) i j k =
      (((primeDepthBVWoldTransport a i j *
            primeDepthBVWoldTransport a j k -
          primeDepthBVWoldTransport a i k : ℝ) : ℂ) * f k) := by
  change
    (primeDepthBVWoldTransport a i j : ℂ) *
          ((primeDepthBVWoldTransport a j k : ℂ) * f k - f j) -
        ((primeDepthBVWoldTransport a i k : ℂ) * f k - f i) +
      ((primeDepthBVWoldTransport a i j : ℂ) * f j - f i) = _
  push_cast
  ring

theorem primeDepthBVWoldCovariant_square_zero_of_parameter_zero
    (f : PrimeDepthBVWoldZeroCochain)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldCovariantD1 0
        (primeDepthBVWoldCovariantD0 0 f) i j k = 0 := by
  rw [primeDepthBVWoldCovariantD1_comp_D0_apply]
  simp [primeDepthBVWoldTransport]

/-! ## Divisor-resolved specialization -/

/-- Centered horizontal divisor rate.  This is applied uniformly to every
divisor copy; it is not a coefficient selected after inspecting a zero. -/
def primeDepthBVWoldXiCenteredRate (rho : XiDivisorSupport) : ℝ :=
  2 * (rho : ℂ).re - 1

theorem primeDepthBVWoldXiCenteredRate_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiCenteredRate rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiCenteredRate]
  constructor <;> intro h <;> linarith

theorem primeDepthBVWoldXiCenteredRate_reflection
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiCenteredRate (xiZeroLineConjEquiv rho) =
      -primeDepthBVWoldXiCenteredRate rho := by
  rw [primeDepthBVWoldXiCenteredRate,
    primeDepthBVWoldXiCenteredRate, xiZeroLineConjEquiv_apply]
  simp
  ring

/-- Divisor-labelled additive connection. -/
def primeDepthBVWoldXiConnection
    (rho : XiDivisorSupport) (i j : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldXiCenteredRate rho *
    primeDepthBVWoldConnection i j

theorem primeDepthBVWoldXiConnection_reflection
    (rho : XiDivisorSupport) (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiConnection (xiZeroLineConjEquiv rho) i j =
      -primeDepthBVWoldXiConnection rho i j := by
  rw [primeDepthBVWoldXiConnection, primeDepthBVWoldXiConnection,
    primeDepthBVWoldXiCenteredRate_reflection]
  ring

/-- Divisor-labelled multiplicative transport. -/
def primeDepthBVWoldXiTransport
    (rho : XiDivisorSupport) (i j : PrimeDepthBVWoldCell) : ℝ :=
  primeDepthBVWoldTransport
    (primeDepthBVWoldXiCenteredRate rho) i j

theorem primeDepthBVWoldXiTransport_reflection
    (rho : XiDivisorSupport) (i j : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiTransport (xiZeroLineConjEquiv rho) i j =
      (primeDepthBVWoldXiTransport rho i j)⁻¹ := by
  rw [primeDepthBVWoldXiTransport, primeDepthBVWoldXiTransport,
    primeDepthBVWoldXiCenteredRate_reflection,
    primeDepthBVWoldTransport, primeDepthBVWoldTransport]
  rw [show -primeDepthBVWoldXiCenteredRate rho *
        primeDepthBVWoldConnection i j =
      -(primeDepthBVWoldXiCenteredRate rho *
        primeDepthBVWoldConnection i j) by ring,
    Real.exp_neg]

theorem primeDepthBVWoldXiTransport_witness_flat_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiTransport rho
          primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne *
        primeDepthBVWoldXiTransport rho
          primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo =
      primeDepthBVWoldXiTransport rho
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo ↔
    (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiTransport,
    primeDepthBVWoldXiTransport, primeDepthBVWoldXiTransport,
    primeDepthBVWoldTransport_witness_flat_iff,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Divisor-resolved zero-, one-, and two-cochains. -/
abbrev PrimeDepthBVWoldXiZeroCochain :=
  XiDivisorSupport → PrimeDepthBVWoldZeroCochain
abbrev PrimeDepthBVWoldXiOneCochain :=
  XiDivisorSupport → PrimeDepthBVWoldOneCochain
abbrev PrimeDepthBVWoldXiTwoCochain :=
  XiDivisorSupport → PrimeDepthBVWoldTwoCochain

/-- Pointwise divisor-profile degree-zero differential.  No divisor fibre
is summed or identified with another. -/
def primeDepthBVWoldXiCovariantD0 :
    PrimeDepthBVWoldXiZeroCochain →ₗ[ℂ]
      PrimeDepthBVWoldXiOneCochain where
  toFun f rho :=
    primeDepthBVWoldCovariantD0
      (primeDepthBVWoldXiCenteredRate rho) (f rho)
  map_add' f g := by
    funext rho i j
    simp only [Pi.add_apply, map_add]
  map_smul' c f := by
    funext rho i j
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

/-- Pointwise divisor-profile degree-one differential. -/
def primeDepthBVWoldXiCovariantD1 :
    PrimeDepthBVWoldXiOneCochain →ₗ[ℂ]
      PrimeDepthBVWoldXiTwoCochain where
  toFun omega rho :=
    primeDepthBVWoldCovariantD1
      (primeDepthBVWoldXiCenteredRate rho) (omega rho)
  map_add' omega eta := by
    funext rho i j k
    simp only [Pi.add_apply, map_add]
  map_smul' c omega := by
    funext rho i j k
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul]

theorem primeDepthBVWoldXiCovariantD1_comp_D0_apply
    (f : PrimeDepthBVWoldXiZeroCochain)
    (rho : XiDivisorSupport)
    (i j k : PrimeDepthBVWoldCell) :
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0 f) rho i j k =
      (((primeDepthBVWoldXiTransport rho i j *
            primeDepthBVWoldXiTransport rho j k -
          primeDepthBVWoldXiTransport rho i k : ℝ) : ℂ) *
        f rho k) := by
  exact primeDepthBVWoldCovariantD1_comp_D0_apply
    (primeDepthBVWoldXiCenteredRate rho) (f rho) i j k

/-- Constant source section used only to read the retained curvature; it
does not erase any prime/depth/divisor label from the output. -/
def primeDepthBVWoldXiConstantOne : PrimeDepthBVWoldXiZeroCochain :=
  fun _ _ => 1

/-- On the exact labelled witness simplex, nilpotence of the divisor-profile
differential is precisely the critical-line equation. -/
theorem primeDepthBVWoldXiCovariant_square_witness_eq_zero_iff
    (rho : XiDivisorSupport) :
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0 primeDepthBVWoldXiConstantOne)
          rho primeDepthBVWoldWitnessZero
            primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [primeDepthBVWoldXiCovariantD1_comp_D0_apply]
  simp only [primeDepthBVWoldXiConstantOne, mul_one,
    Complex.ofReal_sub, Complex.ofReal_mul, sub_eq_zero]
  norm_cast
  exact primeDepthBVWoldXiTransport_witness_flat_iff rho

/-- Global flatness predicate for the complete divisor-resolved curved
differential. -/
def PrimeDepthBVWoldXiDifferentialFlat : Prop :=
  ∀ (rho : XiDivisorSupport)
    (f : PrimeDepthBVWoldXiZeroCochain)
    (i j k : PrimeDepthBVWoldCell),
    primeDepthBVWoldXiCovariantD1
        (primeDepthBVWoldXiCovariantD0 f) rho i j k = 0

/-- Global flatness of the constructed source differential is exactly RH.
This is an unconditional equivalence, not a proof of either side. -/
theorem primeDepthBVWoldXiDifferentialFlat_iff_riemannHypothesis :
    PrimeDepthBVWoldXiDifferentialFlat ↔ RiemannHypothesis := by
  constructor
  · intro hflat
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    have hmem := mem_xi_divisor_support_of_eq_zero hzero
    let rho : XiDivisorSupport := ⟨z, hmem⟩
    have hcurv := hflat rho primeDepthBVWoldXiConstantOne
      primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
      primeDepthBVWoldWitnessTwo
    have hre : (rho : ℂ).re = 1 / 2 :=
      (primeDepthBVWoldXiCovariant_square_witness_eq_zero_iff rho).mp hcurv
    exact (ne_of_gt (mem_rightHalf.mp hz)) hre
  · intro hRH rho f i j k
    have hre := xi_divisor_support_re_eq_half_of_rh hRH rho
    have hrate : primeDepthBVWoldXiCenteredRate rho = 0 :=
      (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mpr hre
    rw [primeDepthBVWoldXiCovariantD1_comp_D0_apply]
    simp [primeDepthBVWoldXiTransport, hrate,
      primeDepthBVWoldTransport]

end

end RHTower
