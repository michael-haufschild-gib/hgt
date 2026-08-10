import GaloisForLFunctions.RHTower.HedenmalmGammaSewnProjectiveKadisonFracture
import GaloisForLFunctions.RHTower.BilateralModerationXiDivisorBridge

/-!
# The Route N Xi/Kadison endpoint is an RH receiver

The preceding projective/Kadison dictionary recovers absolute radial grade from one local defect.
At an actual Xi divisor copy, take that grade to be the horizontal displacement from the critical
line.  The resulting defect vanishes exactly when that divisor point lies on the line, and its
vanishing at every Xi divisor copy is exactly the Riemann hypothesis.

This is a no-go for treating same-fibre duality--adjunction equality, zero complementary record, or
projective multiplicative-domain purity as an unexplained Route N producer: each is already the RH
receiver.  Functional-equation reflection may exchange a free off-line pair without making either
local defect vanish.

The positive survivor is the exact local fracture dictionary from the preceding module.  Any live
successor must construct an independent source incidence or annihilator that kills this already
identified fracture before divisor specialization.
-/

namespace RHTower

noncomputable section

/-- Horizontal Route N grade of an actual Xi divisor copy. -/
def routeNGammaSewnXiRadialGrade (q : XiZeroCopy) : ℝ :=
  (deningerDivisorThetaEigen q).re - 1 / 2

/-- Projective/Kadison record of an actual Xi divisor copy at one ordinary prime. -/
def routeNGammaSewnXiProjectiveKadisonDefect
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  routeNGammaSewnProjectiveKadisonDefect
    (routeNGammaSewnXiRadialGrade q) p

/-- The Xi projective/Kadison record vanishes exactly when the divisor copy is critical. -/
theorem routeNGammaSewnXiProjectiveKadisonDefect_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    routeNGammaSewnXiProjectiveKadisonDefect p q = 0 ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  rw [routeNGammaSewnXiProjectiveKadisonDefect,
    routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff,
    routeNGammaSewnXiRadialGrade]
  constructor <;> intro h <;> linarith

/-- **Receiver/no-go.**  At any fixed ordinary prime, zero projective/Kadison record on every Xi
principal conormal is equivalent to RH. -/
theorem forall_xiZero_routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff_rh
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      routeNGammaSewnXiProjectiveKadisonDefect p q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    exact (routeNGammaSewnXiProjectiveKadisonDefect_eq_zero_iff p q).1
      (hzero q)
  · intro hRH q
    apply (routeNGammaSewnXiProjectiveKadisonDefect_eq_zero_iff p q).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Pointwise Route N projective/Kadison record before restricting to the Xi divisor. -/
def routeNGammaSewnPointProjectiveKadisonDefect
    (ρ : ℂ) (p : Nat.Primes) : ℝ :=
  routeNGammaSewnProjectiveKadisonDefect (ρ.re - 1 / 2) p

/-- Every strict-right point has strictly positive projective/Kadison record. -/
theorem routeNGammaSewnPointProjectiveKadisonDefect_pos_of_half_lt_re
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (p : Nat.Primes) :
    0 < routeNGammaSewnPointProjectiveKadisonDefect ρ p := by
  have hgrade : ρ.re - 1 / 2 ≠ 0 := by linarith
  have hmem := routeNGammaSewnProjectiveKadisonDefect_mem_Ico
    (ρ.re - 1 / 2) p
  have hne := (routeNGammaSewnProjectiveKadisonDefect_eq_zero_iff
    (ρ.re - 1 / 2) p).not.mpr hgrade
  rw [routeNGammaSewnPointProjectiveKadisonDefect]
  exact lt_of_le_of_ne hmem.1 (Ne.symm hne)

/-- **Strict-right squarefree-germ no-go.**  Algebraic Xi attachment to the squarefree reporter
does not imply zero record: every hypothetical strict-right squarefree Xi zero has positive local
projective/Kadison defect. -/
theorem routeNGammaSewnSquarefreeXiGerm_projectiveKadisonDefect_pos
    {ρ : ℂ} (hρhalf : 1 / 2 < ρ.re) (_hρone : ρ.re < 1)
    (_hzero : GaloisForLFunctions.squarefreePartition ρ = 0)
    (p : Nat.Primes) :
    0 < routeNGammaSewnPointProjectiveKadisonDefect ρ p :=
  routeNGammaSewnPointProjectiveKadisonDefect_pos_of_half_lt_re hρhalf p

end

end RHTower
