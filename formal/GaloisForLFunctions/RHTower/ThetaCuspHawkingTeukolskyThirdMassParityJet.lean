import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyFiniteMassParityRigidity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo

/-!
# Fixed-radius third mass jet of the four-dimensional Teukolsky parity split

For the exact Birmingham--Mokhtari scalar/vector potential gap, subtracting the linear and
quadratic mass terms leaves a cubic factor with continuous coefficient.  Its value at zero mass is

`36 (2 - 2 Q - 3 u) / (Q + 2)^(3 : ℕ)`.

Thus the third Taylor jet is strictly negative on the physical theta exterior, although the exact
finite-positive-mass parity gap is strictly positive.  Finite-mass positivity therefore does not
imply coefficientwise cubic positivity.  If a total cubic projection is required to be
nonnegative, the sum of its remaining causal and orthogonal-helicity channels must exceed the
explicit positive compensation threshold below.

On the Xi-reflected BM mediator, the specialization `u = 1` is the partial mass derivative at the
massless event-horizon radius held fixed.  It is not the finite-mass event horizon, which moves by
`u = 1 + x`.  This fixed-radius third-jet variation factors through the same horizontal
displacement as the first mass response.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Continuous cubic coefficient after subtracting the first two mass Taylor terms from the exact
scalar/vector parity gap. -/
def d4ParitySplitThirdJetCompletion (Q u x : ℝ) : ℝ :=
  (36 * (Q + 2) * (2 - 2 * Q - 3 * u) - 162 * (Q + u - 1) * x) /
    ((Q + 2) ^ (2 : ℕ) * (Q + 2 + 3 * x) ^ (2 : ℕ))

/-- Exact cubic factorization of the BM parity gap after its linear and quadratic mass jets are
removed. -/
theorem d4ParitySplit_sub_linear_sub_quadratic_eq_thirdJet
    (Q x u : ℝ) (hQ2 : Q + 2 ≠ 0) (hden : Q + 2 + 3 * x ≠ 0) :
    d4ScalarBracket Q x u - d4VectorBracket Q x -
          (12 / (Q + 2)) * x -
        (18 * (Q + u - 1) / (Q + 2) ^ (2 : ℕ)) * x ^ (2 : ℕ) =
      x ^ (3 : ℕ) * d4ParitySplitThirdJetCompletion Q u x := by
  rw [d4ParitySplit_sub_linear_eq_secondJet Q x u hQ2 hden]
  unfold d4ParitySplitSecondJetCompletion d4ParitySplitThirdJetCompletion
  let A : ℝ := Q + 2
  let d : ℝ := Q + 2 + 3 * x
  have hA : A ≠ 0 := by simpa [A] using hQ2
  have hd : d ≠ 0 := by simpa [d] using hden
  change
    x ^ (2 : ℕ) * ((18 * A * (Q + u - 1) + 36 * (Q - 1) * x) /
        (A * d ^ (2 : ℕ))) -
      (18 * (Q + u - 1) / A ^ (2 : ℕ)) * x ^ (2 : ℕ) =
    x ^ (3 : ℕ) * ((36 * A * (2 - 2 * Q - 3 * u) -
        162 * (Q + u - 1) * x) / (A ^ (2 : ℕ) * d ^ (2 : ℕ)))
  field_simp [hA, hd]
  ring

/-- Cubic Taylor coefficient of the exact parity gap at zero mass. -/
theorem d4ParitySplitThirdJetCompletion_zero
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4ParitySplitThirdJetCompletion Q u 0 =
      36 * (2 - 2 * Q - 3 * u) / (Q + 2) ^ (3 : ℕ) := by
  unfold d4ParitySplitThirdJetCompletion
  field_simp [hQ2]
  ring

/-- The cubic coefficient has no singularity at the massless background. -/
theorem continuousAt_d4ParitySplitThirdJetCompletion_zero
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    ContinuousAt (d4ParitySplitThirdJetCompletion Q u) 0 := by
  unfold d4ParitySplitThirdJetCompletion
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  exact mul_ne_zero (pow_ne_zero 2 hQ2)
    (pow_ne_zero 2 (by simpa using hQ2))

/-- Third mass Taylor jet: six times the cubic coefficient of the exact BM parity gap. -/
def d4ThirdMassParityJet (Q u : ℝ) : ℝ :=
  216 * (2 - 2 * Q - 3 * u) / (Q + 2) ^ (3 : ℕ)

theorem d4ThirdMassParityJet_eq_six_mul_completion
    (Q u : ℝ) (hQ2 : Q + 2 ≠ 0) :
    d4ThirdMassParityJet Q u =
      6 * d4ParitySplitThirdJetCompletion Q u 0 := by
  rw [d4ParitySplitThirdJetCompletion_zero Q u hQ2]
  unfold d4ThirdMassParityJet
  ring

/-- The exact diagonal third mass jet is negative throughout the physical theta exterior. -/
theorem d4ThirdMassParityJet_neg_physical
    (xi u : ℝ) (hu : 1 ≤ u) :
    d4ThirdMassParityJet (d4ThetaPhysicalAngularQ xi) u < 0 := by
  unfold d4ThirdMassParityJet d4ThetaPhysicalAngularQ
  have hnum : 2 - 2 * ((1 / 4 : ℝ) + xi ^ (2 : ℕ)) - 3 * u < 0 := by
    nlinarith [sq_nonneg xi]
  have hden : 0 < (((1 / 4 : ℝ) + xi ^ (2 : ℕ)) + 2) ^ (3 : ℕ) := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hnum) hden

/-- Positive exact finite-mass response and negative third Taylor jet coexist on every physical
theta exterior ray. -/
theorem d4FiniteMassParityGap_pos_and_thirdJet_neg_physical
    (xi u x : ℝ) (hu : 1 ≤ u) (hx : 0 < x) :
    0 < d4ScalarBracket (d4ThetaPhysicalAngularQ xi) x u -
          d4VectorBracket (d4ThetaPhysicalAngularQ xi) x ∧
      d4ThirdMassParityJet (d4ThetaPhysicalAngularQ xi) u < 0 := by
  exact ⟨d4ParitySplit_pos_of_physical
      (d4ThetaPhysicalAngularQ_nonneg xi) hx (by linarith),
    d4ThirdMassParityJet_neg_physical xi u hu⟩

/-- Positive amount which other cubic channels must supply to compensate the negative radial
third mass jet. -/
def d4ThirdMassParityCompensationThreshold (Q u : ℝ) : ℝ :=
  -d4ThirdMassParityJet Q u

/-- Total cubic balance after grouping every causal, direct, continuum, and orthogonal-helicity
contribution other than the exact BM diagonal mass jet into one residual coefficient. -/
def d4ThirdMassParityCubicBalance (Q u residual : ℝ) : ℝ :=
  d4ThirdMassParityJet Q u + residual

theorem d4ThirdMassParityCubicBalance_nonneg_iff
    (Q u residual : ℝ) :
    0 ≤ d4ThirdMassParityCubicBalance Q u residual ↔
      d4ThirdMassParityCompensationThreshold Q u ≤ residual := by
  unfold d4ThirdMassParityCubicBalance d4ThirdMassParityCompensationThreshold
  constructor <;> intro h <;> linarith

theorem d4ThirdMassParityCompensationThreshold_pos_physical
    (xi u : ℝ) (hu : 1 ≤ u) :
    0 < d4ThirdMassParityCompensationThreshold
      (d4ThetaPhysicalAngularQ xi) u := by
  unfold d4ThirdMassParityCompensationThreshold
  linarith [d4ThirdMassParityJet_neg_physical xi u hu]

/-- A nonnegative total cubic balance forces a strictly positive complementary channel on the
physical theta exterior. -/
theorem d4ThirdMassParityCubicBalance_nonneg_forces_residual_pos
    (xi u residual : ℝ) (hu : 1 ≤ u)
    (hbalance : 0 ≤ d4ThirdMassParityCubicBalance
      (d4ThetaPhysicalAngularQ xi) u residual) :
    0 < residual := by
  have hthreshold := d4ThirdMassParityCompensationThreshold_pos_physical xi u hu
  have hresidual :=
    (d4ThirdMassParityCubicBalance_nonneg_iff
      (d4ThetaPhysicalAngularQ xi) u residual).1 hbalance
  linarith

/-- Vanishing complementary flux leaves the cubic BM balance strictly negative. -/
theorem d4ThirdMassParityCubicBalance_zeroResidual_neg_physical
    (xi u : ℝ) (hu : 1 ≤ u) :
    d4ThirdMassParityCubicBalance (d4ThetaPhysicalAngularQ xi) u 0 < 0 := by
  simpa [d4ThirdMassParityCubicBalance] using
    d4ThirdMassParityJet_neg_physical xi u hu

/-- Third mass jet of the BM reflected real-pair mediator at fixed `u=1`. -/
def d4BMXiReflectedFixedUnitRadiusThirdMassParityJet (q : XiZeroCopy) : ℝ :=
  d4ThirdMassParityJet (d4BMXiReflectedRealPairMediatorAngularQ q) 1

/-- Reflection-odd variation of the exact fixed-unit-radius third mass jet. -/
def d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiReflectedFixedUnitRadiusThirdMassParityJet q -
    d4BMXiReflectedFixedUnitRadiusThirdMassParityJet (xiZeroCopyReflectEquiv q)

/-- Positive polynomial multiplying horizontal Xi displacement in fixed-radius third-jet
variation. -/
def d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial (q : XiZeroCopy) : ℝ :=
  let a := (q.1 : ℂ).re
  24 - 36 * (a * (1 - a)) - 38 * (a * (1 - a)) ^ (2 : ℕ) -
    8 * (a * (1 - a)) ^ (3 : ℕ)

/-- Exact reflection variation of the BM fixed-unit-radius third mass jet. -/
theorem d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq
    (q : XiZeroCopy) :
    d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect q =
      216 * (1 - 2 * (q.1 : ℂ).re) *
          d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
        ((q.1 : ℂ).re ^ (3 : ℕ) * (3 - (q.1 : ℂ).re) ^ (3 : ℕ) *
          (1 - (q.1 : ℂ).re) ^ (3 : ℕ) * (2 + (q.1 : ℂ).re) ^ (3 : ℕ)) := by
  let a : ℝ := (q.1 : ℂ).re
  have hQ : d4BMXiReflectedRealPairMediatorAngularQ q =
      (2 - a) * (a - 1) := by
    rfl
  have hQr : d4BMXiReflectedRealPairMediatorAngularQ
      (xiZeroCopyReflectEquiv q) = -a * (a + 1) := by
    unfold d4BMXiReflectedRealPairMediatorAngularQ
    rw [xiZeroCopyReflectEquiv_rho]
    simp only [Complex.sub_re, Complex.one_re]
    dsimp [a]
    ring
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hstrip.1)
  have h1a : 1 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h3a : 3 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h2a : 2 + a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  unfold d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect
    d4BMXiReflectedFixedUnitRadiusThirdMassParityJet
  rw [hQ, hQr]
  unfold d4ThirdMassParityJet d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial
  change
    216 * (2 - 2 * ((2 - a) * (a - 1)) - 3 * 1) /
          (((2 - a) * (a - 1)) + 2) ^ (3 : ℕ) -
        216 * (2 - 2 * (-a * (a + 1)) - 3 * 1) /
          ((-a * (a + 1)) + 2) ^ (3 : ℕ) =
      216 * (1 - 2 * a) *
          (24 - 36 * (a * (1 - a)) - 38 * (a * (1 - a)) ^ (2 : ℕ) -
            8 * (a * (1 - a)) ^ (3 : ℕ)) /
        (a ^ (3 : ℕ) * (3 - a) ^ (3 : ℕ) * (1 - a) ^ (3 : ℕ) * (2 + a) ^ (3 : ℕ))
  rw [show 2 - 2 * ((2 - a) * (a - 1)) - 3 * 1 =
        2 * a ^ (2 : ℕ) - 6 * a + 3 by ring,
    show (2 - a) * (a - 1) + 2 = a * (3 - a) by ring,
    show 2 - 2 * (-a * (a + 1)) - 3 * 1 =
        2 * a ^ (2 : ℕ) + 2 * a - 1 by ring,
    show -a * (a + 1) + 2 = (1 - a) * (2 + a) by ring]
  field_simp [ha, h1a, h3a, h2a]
  ring

theorem d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial_pos
    (q : XiZeroCopy) :
    0 < d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q := by
  let a : ℝ := (q.1 : ℂ).re
  let t : ℝ := a * (1 - a)
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha0 : 0 < a := by simpa [a] using hstrip.1
  have ha1 : a < 1 := by simpa [a] using hstrip.2
  have ht : 0 ≤ t := mul_nonneg (le_of_lt ha0) (by linarith)
  have htle : t ≤ 1 / 4 := by
    dsimp [t]
    nlinarith [sq_nonneg (a - 1 / 2)]
  have hgap : 0 ≤ t * (1 / 4 - t) :=
    mul_nonneg ht (sub_nonneg.mpr htle)
  have hgap2 : 0 ≤ t ^ (2 : ℕ) * (1 / 4 - t) :=
    mul_nonneg (sq_nonneg t) (sub_nonneg.mpr htle)
  unfold d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial
  change 0 < 24 - 36 * t - 38 * t ^ (2 : ℕ) - 8 * t ^ (3 : ℕ)
  nlinarith

/-- Reflected BM fixed-unit-radius third mass jets agree exactly at critical-line incidence. -/
theorem d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq]
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hstrip.1)
  have h1a : 1 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h3a : 3 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h2a : 2 + a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have hp := d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial_pos q
  have hden : a ^ (3 : ℕ) * (3 - a) ^ (3 : ℕ) * (1 - a) ^ (3 : ℕ) * (2 + a) ^ (3 : ℕ) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (pow_ne_zero 3 ha) (pow_ne_zero 3 h3a))
        (pow_ne_zero 3 h1a))
      (pow_ne_zero 3 h2a)
  change
    216 * (1 - 2 * a) *
          d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
        (a ^ (3 : ℕ) * (3 - a) ^ (3 : ℕ) * (1 - a) ^ (3 : ℕ) * (2 + a) ^ (3 : ℕ)) = 0 ↔
      a = 1 / 2
  constructor
  · intro h
    have hnum : 216 * (1 - 2 * a) *
        d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q = 0 := by
      rcases div_eq_zero_iff.mp h with hnum | hdenzero
      · exact hnum
      · exact False.elim (hden hdenzero)
    rcases mul_eq_zero.mp hnum with hprod | hpzero
    · rcases mul_eq_zero.mp hprod with h216 | htilt
      · norm_num at h216
      · linarith
    · exact False.elim ((ne_of_gt hp) hpzero)
  · intro h
    rw [h]
    norm_num

/-- Positive susceptibility relating fixed-unit-radius third mass jet to first BM parity
response. -/
def d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility (q : XiZeroCopy) : ℝ :=
  let a := (q.1 : ℂ).re
  9 * d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
    (a * (1 - a) * (3 - a) * (2 + a)) ^ (2 : ℕ)

theorem d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility_pos
    (q : XiZeroCopy) :
    0 < d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility q := by
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hstrip.1)
  have h1a : 1 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h3a : 3 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h2a : 2 + a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have hD : a * (1 - a) * (3 - a) * (2 + a) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha h1a) h3a) h2a
  unfold d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility
  change 0 < 9 * d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
    (a * (1 - a) * (3 - a) * (2 + a)) ^ (2 : ℕ)
  exact div_pos
    (mul_pos (by norm_num)
      (d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial_pos q))
    (sq_pos_of_ne_zero hD)

/-- Fixed-unit-radius third mass variant is a positive multiple of first BM variant. -/
theorem d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq_susceptibility_mul_first
    (q : XiZeroCopy) :
    d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect q =
      d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility q *
        d4BMXiReflectionOddBackreactionDefect q := by
  rw [d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq,
    d4BMXiReflectionOddBackreactionDefect_eq]
  let a : ℝ := (q.1 : ℂ).re
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : a ≠ 0 := ne_of_gt (by simpa [a] using hstrip.1)
  have h1a : 1 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h3a : 3 - a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  have h2a : 2 + a ≠ 0 := ne_of_gt (by dsimp [a]; linarith)
  unfold d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility
  change
    216 * (1 - 2 * a) *
          d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
        (a ^ (3 : ℕ) * (3 - a) ^ (3 : ℕ) * (1 - a) ^ (3 : ℕ) * (2 + a) ^ (3 : ℕ)) =
      (9 * d4BMXiFixedUnitRadiusThirdMassParityReflectionPolynomial q /
          (a * (1 - a) * (3 - a) * (2 + a)) ^ (2 : ℕ)) *
        (24 * (1 - 2 * a) /
          (a * (1 - a) * (3 - a) * (2 + a)))
  field_simp [ha, h1a, h3a, h2a]
  ring

/-- Off critical line, first and fixed-unit-radius third mass variants have same orientation. -/
theorem d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_mul_first_pos_of_tilt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect q *
      d4BMXiReflectionOddBackreactionDefect q := by
  rw [d4BMXiReflectedFixedUnitRadiusThirdMassParityJetDefect_eq_susceptibility_mul_first]
  have hs := d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility_pos q
  have hf : d4BMXiReflectionOddBackreactionDefect q ≠ 0 := by
    intro hzero
    exact hoff ((d4BMXiReflectionOddBackreactionDefect_eq_zero_iff q).1 hzero)
  calc
    d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility q *
          d4BMXiReflectionOddBackreactionDefect q *
        d4BMXiReflectionOddBackreactionDefect q =
      d4BMXiFixedUnitRadiusThirdToFirstMassSusceptibility q *
        d4BMXiReflectionOddBackreactionDefect q ^ (2 : ℕ) := by ring
    _ > 0 := mul_pos hs (sq_pos_of_ne_zero hf)

end

end RHTower
