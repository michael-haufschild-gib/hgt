import GaloisForLFunctions.RHTower.BVCoPoissonHellingerBetaResonanceTransmutation
import GaloisForLFunctions.RHTower.CCMFirstClockPrimitivePromotedPureHodgeModularTransgression

/-!
# Hellinger--Gamma gauged pure-Hodge coface

The ungauged pure-Hodge modular orbit has reciprocal exponential capacity
and therefore diverges at every nonzero modular displacement.  The even
Gamma residue inside the reflected Hellinger--Beta column supplies the
source-native adjacent-grade gauge

`g n = Res(Gamma, -2 n) = 1 / (2 n)!`.

Multiplying the common-depth pure-Hodge orbit by `g n` suppresses both
reflected exponential directions.  The resulting capacity tends to zero
for every real displacement, not merely at the critical value.  Adjacent
differences form an actual-admitted off-diagonal coface and telescope
exactly.  Every finite secondary Poincare trace still detects nonzero
modular displacement, so the construction preserves the unsquared charge
before its graph limit.

This is the local graph-Cauchy coface required by the source-admission
frontier.  It does not yet identify its graph limit with the completed Xi
Green primitive; that coefficient-faithful global tensoring remains open.
-/

open Complex Set Finset Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

namespace PrimitivePromotedHellingerGammaPureHodgeCoface

open PrimitivePromotedCellHodgeRigidity
open PrimitivePromotedPureHodgeCountertransport
open PrimitivePromotedPureHodgeModularTransgression

/-- Even Gamma residue gauge occurring inside the reflected Hellinger--Beta
half-lattice residue. -/
def hellingerEvenGammaResidueGauge (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ)⁻¹

theorem hellingerEvenGammaResidueGauge_eq_gammaNegNatResidue (n : ℕ) :
    (hellingerEvenGammaResidueGauge n : ℂ) = gammaNegNatResidue (2 * n) := by
  rw [gammaNegNatResidue_eq]
  simp [hellingerEvenGammaResidueGauge, div_eq_mul_inv]

theorem hellingerEvenGammaResidueGauge_ne_zero (n : ℕ) :
    hellingerEvenGammaResidueGauge n ≠ 0 := by
  unfold hellingerEvenGammaResidueGauge
  exact inv_ne_zero (by positivity)

/-- One Gamma-gauged modular coefficient.  This is the scalar acting on
either completed Xi channel before forming the balanced pair. -/
def hellingerGammaGaugedModularCoefficient
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  hellingerEvenGammaResidueGauge n *
    Real.exp
      (a * (xiGammaEulerPrimitiveModularRate (p, n) +
        xiGammaEulerPrimitiveModularRate (q, n)))

theorem hellingerGammaGaugedModularCoefficient_nonneg
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    0 ≤ hellingerGammaGaugedModularCoefficient a p q n := by
  unfold hellingerGammaGaugedModularCoefficient
    hellingerEvenGammaResidueGauge
  positivity

theorem hellingerGammaGaugedModularCoefficient_le_majorant
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    hellingerGammaGaugedModularCoefficient a p q n ≤
      Real.exp |a * (Real.log (p : ℝ) + Real.log (q : ℝ))| *
        Real.exp |a * (Real.log (p : ℝ) + Real.log (q : ℝ))| ^ n /
          (n.factorial : ℝ) := by
  let d : ℝ := -a * (Real.log (p : ℝ) + Real.log (q : ℝ))
  let c : ℝ := |a * (Real.log (p : ℝ) + Real.log (q : ℝ))|
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hdc : d ≤ c := by
    dsimp only [d, c]
    calc
      -a * (Real.log (p : ℝ) + Real.log (q : ℝ)) =
          -(a * (Real.log (p : ℝ) + Real.log (q : ℝ))) := by ring
      _ ≤ |a * (Real.log (p : ℝ) + Real.log (q : ℝ))| := neg_le_abs _
  have hexp :
      Real.exp (d * ((n : ℝ) + 1)) ≤
        Real.exp (c * ((n : ℝ) + 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hn)
  have hrate :
      a * (xiGammaEulerPrimitiveModularRate (p, n) +
        xiGammaEulerPrimitiveModularRate (q, n)) =
      d * ((n : ℝ) + 1) := by
    rw [xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
      xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
    unfold xiGammaEulerBoundaryHalfHeight
    dsimp only [d]
    ring
  have hfacNat : n.factorial ≤ (2 * n).factorial :=
    Nat.factorial_le (by omega)
  have hfac : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) := by
    exact_mod_cast hfacNat
  have hnfac : (0 : ℝ) < n.factorial := by positivity
  have hnum : 0 ≤ Real.exp (c * ((n : ℝ) + 1)) := Real.exp_nonneg _
  calc
    hellingerGammaGaugedModularCoefficient a p q n =
        Real.exp (d * ((n : ℝ) + 1)) /
          ((2 * n).factorial : ℝ) := by
      rw [hellingerGammaGaugedModularCoefficient, hrate]
      simp only [hellingerEvenGammaResidueGauge, div_eq_mul_inv]
      ring
    _ ≤ Real.exp (c * ((n : ℝ) + 1)) /
          ((2 * n).factorial : ℝ) := by
      exact div_le_div_of_nonneg_right hexp (by positivity)
    _ ≤ Real.exp (c * ((n : ℝ) + 1)) / (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hnum hnfac hfac
    _ = Real.exp c * Real.exp c ^ n / (n.factorial : ℝ) := by
      rw [show c * ((n : ℝ) + 1) = c + n * c by ring,
        Real.exp_add, Real.exp_nat_mul]

/-- Every Gamma-gauged modular coefficient tends to zero at cofinal
Hellinger grade. -/
theorem hellingerGammaGaugedModularCoefficient_tendsto_zero
    (a : ℝ) (p q : Nat.Primes) :
    Tendsto
      (fun n : ℕ => hellingerGammaGaugedModularCoefficient a p q n)
      atTop (𝓝 0) := by
  let c : ℝ := |a * (Real.log (p : ℝ) + Real.log (q : ℝ))|
  have hmajor :
      Tendsto
        (fun n : ℕ => Real.exp c * Real.exp c ^ n / (n.factorial : ℝ))
        atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (Real.exp c)).const_mul
        (Real.exp c)
  apply squeeze_zero
  · exact hellingerGammaGaugedModularCoefficient_nonneg a p q
  · exact hellingerGammaGaugedModularCoefficient_le_majorant a p q
  · exact hmajor

/-- Squared two-sided PHMT capacity after applying the even Gamma residue
gauge. -/
def hellingerGammaGaugedPureHodgeCapacity
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  hellingerEvenGammaResidueGauge n ^ 2 *
    pureHodgeBalancedGraphCapacity a p q n

theorem hellingerGammaGaugedPureHodgeCapacity_nonneg
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    0 ≤ hellingerGammaGaugedPureHodgeCapacity a p q n := by
  unfold hellingerGammaGaugedPureHodgeCapacity
    pureHodgeBalancedGraphCapacity
  positivity

/-- Both reciprocal modular exponentials are bounded by the exponential of
the absolute source rate. -/
theorem pureHodgeBalancedGraphCapacity_le_absExp
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    pureHodgeBalancedGraphCapacity a p q n ≤
      2 * Real.exp
        (|2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))| *
          ((n : ℝ) + 1)) := by
  let c : ℝ := 2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hpos :
      c * ((n : ℝ) + 1) ≤ |c| * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hn
  have hneg :
      -c * ((n : ℝ) + 1) ≤ |c| * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (neg_le_abs c) hn
  rw [pureHodgeBalancedGraphCapacity_eq_sewing_add_reflection,
    deningerCalderonWittGammaReflectionSewingCost_eq_exp,
    deningerCalderonWittGammaReflectionSewingCost_eq_exp]
  rw [show 2 * -a * (Real.log (p : ℝ) + Real.log (q : ℝ)) = -c by
    dsimp only [c]
    ring]
  change Real.exp (c * ((n : ℝ) + 1)) +
      Real.exp (-c * ((n : ℝ) + 1)) ≤
    2 * Real.exp (|c| * ((n : ℝ) + 1))
  calc
    _ ≤ Real.exp (|c| * ((n : ℝ) + 1)) +
        Real.exp (|c| * ((n : ℝ) + 1)) :=
      add_le_add (Real.exp_le_exp.mpr hpos) (Real.exp_le_exp.mpr hneg)
    _ = _ := by ring

/-- Factorial domination reduces gauged graph capacity to one term of an
exponential series. -/
theorem hellingerGammaGaugedPureHodgeCapacity_le_majorant
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    hellingerGammaGaugedPureHodgeCapacity a p q n ≤
      2 * Real.exp
          |2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))| *
        Real.exp
            |2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))| ^ n /
          (n.factorial : ℝ) := by
  let c : ℝ := |2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))|
  have hcap := pureHodgeBalancedGraphCapacity_le_absExp a p q n
  have hfacNat : n.factorial ≤ ((2 * n).factorial) ^ 2 := by
    calc
      n.factorial ≤ (2 * n).factorial := Nat.factorial_le (by omega)
      _ ≤ ((2 * n).factorial) ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)
  have hfac : (n.factorial : ℝ) ≤ ((2 * n).factorial : ℝ) ^ 2 := by
    exact_mod_cast hfacNat
  have hnfac : (0 : ℝ) < n.factorial := by positivity
  have hnum : 0 ≤ 2 * Real.exp (c * ((n : ℝ) + 1)) := by positivity
  calc
    hellingerGammaGaugedPureHodgeCapacity a p q n ≤
        hellingerEvenGammaResidueGauge n ^ 2 *
          (2 * Real.exp (c * ((n : ℝ) + 1))) := by
      exact mul_le_mul_of_nonneg_left hcap (sq_nonneg _)
    _ = (2 * Real.exp (c * ((n : ℝ) + 1))) /
          ((2 * n).factorial : ℝ) ^ 2 := by
      simp only [hellingerEvenGammaResidueGauge, inv_pow, div_eq_mul_inv]
      ring
    _ ≤ (2 * Real.exp (c * ((n : ℝ) + 1))) /
          (n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hnum hnfac hfac
    _ = 2 * Real.exp c * Real.exp c ^ n / (n.factorial : ℝ) := by
      rw [show c * ((n : ℝ) + 1) = c + n * c by ring,
        Real.exp_add, Real.exp_nat_mul]
      ring

/-- The factorial Hellinger--Gamma gauge makes the two-sided PHMT graph
capacity converge to zero for every real modular displacement. -/
theorem hellingerGammaGaugedPureHodgeCapacity_tendsto_zero
    (a : ℝ) (p q : Nat.Primes) :
    Tendsto
      (fun n : ℕ => hellingerGammaGaugedPureHodgeCapacity a p q n)
      atTop (𝓝 0) := by
  let c : ℝ := |2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))|
  have hmajor :
      Tendsto
        (fun n : ℕ =>
          2 * Real.exp c * Real.exp c ^ n / (n.factorial : ℝ))
        atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop (Real.exp c)).const_mul
        (2 * Real.exp c)
  apply squeeze_zero
  · exact hellingerGammaGaugedPureHodgeCapacity_nonneg a p q
  · intro n
    exact hellingerGammaGaugedPureHodgeCapacity_le_majorant a p q n
  · exact hmajor

/-- Squared Euclidean coefficient norm of the gauged odd transgression.
The factor `2` from its two opposite coordinates has already been
simplified into the displayed quotient. -/
def hellingerGammaGaugedOddCoefficientCapacity
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) : ℝ :=
  hellingerEvenGammaResidueGauge n ^ 2 *
    ((Real.exp
        (a * (xiGammaEulerPrimitiveModularRate (p, n) +
          xiGammaEulerPrimitiveModularRate (q, n))) -
      Real.exp
        (-a * (xiGammaEulerPrimitiveModularRate (p, n) +
          xiGammaEulerPrimitiveModularRate (q, n)))) ^ 2 / 2)

theorem hellingerGammaGaugedOddCoefficientCapacity_nonneg
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    0 ≤ hellingerGammaGaugedOddCoefficientCapacity a p q n := by
  unfold hellingerGammaGaugedOddCoefficientCapacity
  positivity

/-- Odd-transgression coefficient capacity is controlled by the full
two-sided balanced graph capacity. -/
theorem hellingerGammaGaugedOddCoefficientCapacity_le
    (a : ℝ) (p q : Nat.Primes) (n : ℕ) :
    hellingerGammaGaugedOddCoefficientCapacity a p q n ≤
      hellingerGammaGaugedPureHodgeCapacity a p q n := by
  let x := Real.exp
    (-a * (xiGammaEulerPrimitiveModularRate (p, n) +
      xiGammaEulerPrimitiveModularRate (q, n)))
  let y := Real.exp
    (a * (xiGammaEulerPrimitiveModularRate (p, n) +
      xiGammaEulerPrimitiveModularRate (q, n)))
  have hxy : (y - x) ^ 2 / 2 ≤ x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg (x + y)]
  unfold hellingerGammaGaugedOddCoefficientCapacity
    hellingerGammaGaugedPureHodgeCapacity
    pureHodgeBalancedGraphCapacity
  exact mul_le_mul_of_nonneg_left hxy (sq_nonneg _)

/-- The actual odd-transgression coefficients are graph-null at cofinal
Hellinger grade, for every fixed displacement. -/
theorem hellingerGammaGaugedOddCoefficientCapacity_tendsto_zero
    (a : ℝ) (p q : Nat.Primes) :
    Tendsto
      (fun n : ℕ => hellingerGammaGaugedOddCoefficientCapacity a p q n)
      atTop (𝓝 0) := by
  apply squeeze_zero
  · exact hellingerGammaGaugedOddCoefficientCapacity_nonneg a p q
  · exact hellingerGammaGaugedOddCoefficientCapacity_le a p q
  · exact hellingerGammaGaugedPureHodgeCapacity_tendsto_zero a p q

/-- Explicit uniform capacity, stronger than mere boundedness from
convergence. -/
theorem hellingerGammaGaugedPureHodgeCapacity_uniform
    (a : ℝ) (p q : Nat.Primes) :
    ∃ C : ℝ, ∀ n : ℕ,
      hellingerGammaGaugedPureHodgeCapacity a p q n ≤ C := by
  let c : ℝ := |2 * a * (Real.log (p : ℝ) + Real.log (q : ℝ))|
  refine ⟨2 * Real.exp c * Real.exp (Real.exp c), ?_⟩
  intro n
  calc
    hellingerGammaGaugedPureHodgeCapacity a p q n ≤
        2 * Real.exp c * Real.exp c ^ n / (n.factorial : ℝ) :=
      hellingerGammaGaugedPureHodgeCapacity_le_majorant a p q n
    _ ≤ 2 * Real.exp c * Real.exp (Real.exp c) := by
      have hseries :
          Real.exp c ^ n / (n.factorial : ℝ) ≤ Real.exp (Real.exp c) :=
        Real.pow_div_factorial_le_exp (Real.exp c) (Real.exp_nonneg c) n
      rw [show 2 * Real.exp c * Real.exp c ^ n / (n.factorial : ℝ) =
        (2 * Real.exp c) *
          (Real.exp c ^ n / (n.factorial : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left hseries
        (mul_nonneg (by norm_num) (Real.exp_nonneg c))

/-- Gauged pure-Hodge primitive on the common-depth labelled cell pair. -/
def hellingerGammaGaugedPureHodgePrimitive
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  (hellingerEvenGammaResidueGauge n : ℂ) •
    pureHodgeCellOddTransgression a
      (shiftedPureOrderedDistinctCellPair hpq n n)

/-- Coefficient-plane presentation of the gauged primitive. -/
def hellingerGammaGaugedPureHodgeCoefficients
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    PureHodgeCellPlane :=
  (hellingerEvenGammaResidueGauge n : ℂ) •
    pureHodgeCellOddTransgressionCoefficients a
      (shiftedPureOrderedDistinctCellPair hpq n n)

theorem hellingerGammaGaugedPureHodgeCoefficients_antiFixed
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    pureHodgeCellExchange
        (hellingerGammaGaugedPureHodgeCoefficients hpq a n) =
      -hellingerGammaGaugedPureHodgeCoefficients hpq a n := by
  rw [hellingerGammaGaugedPureHodgeCoefficients, map_smul,
    pureHodgeCellOddTransgressionCoefficients_antiFixed]
  module

/-- Adjacent-grade off-diagonal coface. -/
def hellingerGammaPureHodgeAdjacentCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    xiGammaEulerCalderonWittCellMilnorIncidence :=
  hellingerGammaGaugedPureHodgePrimitive hpq a (n + 1) -
    hellingerGammaGaugedPureHodgePrimitive hpq a n

theorem hellingerGammaGaugedPureHodgePrimitive_mem_actual
    {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℝ) (n : ℕ) :
    hellingerGammaGaugedPureHodgePrimitive hpq a n ∈
      actualCellGammaAdmittedHodgeSector b := by
  exact Submodule.smul_mem _ _
    (pureHodgeCellOddTransgression_mem_actual a b
      (shiftedPureOrderedDistinctCellPair hpq n n))

theorem hellingerGammaPureHodgeAdjacentCoface_defect_eq_zero
    {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℝ) (n : ℕ) :
    cellReflectionOddBoundaryDefect b
        (hellingerGammaPureHodgeAdjacentCoface hpq a n) = 0 := by
  have hsucc := hellingerGammaGaugedPureHodgePrimitive_mem_actual
    (p := p) (q := q) hpq a b (n + 1)
  have hn := hellingerGammaGaugedPureHodgePrimitive_mem_actual
    (p := p) (q := q) hpq a b n
  calc
    cellReflectionOddBoundaryDefect b
        (hellingerGammaPureHodgeAdjacentCoface hpq a n) =
      cellReflectionOddBoundaryDefect b
          (hellingerGammaGaugedPureHodgePrimitive hpq a (n + 1)) -
        cellReflectionOddBoundaryDefect b
          (hellingerGammaGaugedPureHodgePrimitive hpq a n) := by
      exact map_sub (cellReflectionOddBoundaryDefect b) _ _
    _ = 0 := by
      rw [(LinearMap.mem_ker.mp hsucc), (LinearMap.mem_ker.mp hn), sub_self]

/-- Every coface edge remains in the actual admitted sector for every
auxiliary boundary displacement. -/
theorem hellingerGammaPureHodgeAdjacentCoface_mem_actual
    {p q : Nat.Primes} (hpq : p ≠ q) (a b : ℝ) (n : ℕ) :
    hellingerGammaPureHodgeAdjacentCoface hpq a n ∈
      actualCellGammaAdmittedHodgeSector b := by
  exact LinearMap.mem_ker.mpr
    (hellingerGammaPureHodgeAdjacentCoface_defect_eq_zero
      (p := p) (q := q) hpq a b n)

/-- Finite adjacent-grade boundaries telescope exactly. -/
theorem sum_hellingerGammaPureHodgeAdjacentCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        hellingerGammaPureHodgeAdjacentCoface hpq a n =
      hellingerGammaGaugedPureHodgePrimitive hpq a N -
        hellingerGammaGaugedPureHodgePrimitive hpq a 0 := by
  simpa only [hellingerGammaPureHodgeAdjacentCoface, Nat.add_comm] using
    (Finset.sum_range_sub
      (fun n => hellingerGammaGaugedPureHodgePrimitive hpq a n) N)

/-- Unsquared Poincare trace of one gauged primitive. -/
def hellingerGammaGaugedPureHodgeSecondaryTrace
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) : ℂ :=
  pureHodgeCellPoincareTrace
      (shiftedPureOrderedDistinctCellPair hpq n n)
    (hellingerGammaGaugedPureHodgePrimitive hpq a n)

theorem hellingerGammaGaugedPureHodgeSecondaryTrace_eq
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n =
      (hellingerEvenGammaResidueGauge n : ℂ) *
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, n) (q, n) : ℂ) := by
  rw [hellingerGammaGaugedPureHodgeSecondaryTrace,
    hellingerGammaGaugedPureHodgePrimitive, map_smul,
    pureHodgeCellPoincareTrace_oddTransgression_eq_reflectionOddExterior]
  rfl

/-- Factorial graph damping does not erase the finite unsquared detector:
every grade still vanishes exactly at zero displacement. -/
theorem hellingerGammaGaugedPureHodgeSecondaryTrace_eq_zero_iff
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) :
    hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n = 0 ↔
      a = 0 := by
  rw [hellingerGammaGaugedPureHodgeSecondaryTrace_eq]
  constructor
  · intro hzero
    have hgamma :
        (xiGammaEulerPrimitiveReflectionOddExterior
          a (p, n) (q, n) : ℂ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left
        (Complex.ofReal_ne_zero.mpr
          (hellingerEvenGammaResidueGauge_ne_zero n))
    have hreal :
        xiGammaEulerPrimitiveReflectionOddExterior
          a (p, n) (q, n) = 0 := by
      exact_mod_cast hgamma
    exact
      (xiGammaEulerPrimitiveReflectionOddExterior_eq_zero_iff
        a (p, n) (q, n)
          (xiGammaEulerBoundaryHalfHeight_ne_of_primes_ne_sameDepth hpq n)).mp
        hreal
  · rintro rfl
    simp [xiGammaEulerPrimitiveReflectionOddExterior_zero]

/-- Scalar adjacent-grade coface obtained after the vector construction. -/
def hellingerGammaPureHodgeSecondaryTraceCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (n : ℕ) : ℂ :=
  hellingerGammaGaugedPureHodgeSecondaryTrace hpq a (n + 1) -
    hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n

theorem sum_hellingerGammaPureHodgeSecondaryTraceCoface
    {p q : Nat.Primes} (hpq : p ≠ q) (a : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        hellingerGammaPureHodgeSecondaryTraceCoface hpq a n =
      hellingerGammaGaugedPureHodgeSecondaryTrace hpq a N -
        hellingerGammaGaugedPureHodgeSecondaryTrace hpq a 0 := by
  simpa only [hellingerGammaPureHodgeSecondaryTraceCoface, Nat.add_comm] using
    (Finset.sum_range_sub
      (fun n => hellingerGammaGaugedPureHodgeSecondaryTrace hpq a n) N)

end PrimitivePromotedHellingerGammaPureHodgeCoface

end

end RHTower
