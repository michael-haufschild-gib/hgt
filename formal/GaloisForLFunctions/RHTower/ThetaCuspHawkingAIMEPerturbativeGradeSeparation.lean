import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMECrossBranchTeukolskyResidue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullEinsteinGaugeFixedRadiationGram
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyMassMemoryDoublePole

/-!
# Perturbative-grade separation of AIME from the second-order Teukolsky source

Spiers--Pound--Moxon's reduced second-order vacuum Teukolsky equation has a source quadratic in
the first-order metric.  For one real Einstein seed with positive-helicity cusp weight `s` and
negative-helicity weight `conj(s)`, its complete grade support is therefore

`{2s, s + conj(s), 2conj(s)}`.

Absorption-induced mode excitation is different.  Horizon mass change is quadratic in the seed,
and its action on the surviving seed is cubic.  Its monomial `A * |A|^(2 : ℕ) = A^(2 : ℕ) * conj(A)` has cusp
weight

`2s + conj(s)`.

At every Xi divisor, `im(s) != 0`.  Hence this cubic AIME grade is disjoint from every quadratic
grade.  It is also distinct from the other three cubic real-helicity grades `3s`,
`s + 2conj(s)`, and `3conj(s)`.  Thus only the third-order `++-` Einstein--Teukolsky coefficient
can share the AIME pole numerator's grade.

Perturbative order gives an independent obstruction.  The exact AIME numerator scales cubically
under real rescaling of the seed.  If one quadratic coefficient cancelled it for every seed
scale, evaluation at scales one and two would force both coefficients to vanish.  The explicit
AIME coefficient is nonzero at every Xi divisor for a nonzero seed, so such cancellation is
impossible.

Consequently the previously posited reduced *second-order* same-pole counterterm cannot exist.
The remaining dynamical problem is narrower and one order higher: compute the gauge-fixed
third-order `++-` Einstein--Teukolsky projection and determine whether it equals the unique
opposite AIME numerator.  No sign or vanishing claim about that coefficient is made here.

`[LITERATURE-CORRECTED] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Real

namespace RHTower

noncomputable section

private lemma d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero (q : XiZeroCopy) :
    (d4ThetaTeukolskyLinearCuspWeight (xiSpectralPoint q)).im ≠ 0 := by
  rw [d4ThetaTeukolskyLinearCuspWeight_eq_half_rho,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  intro h
  norm_num [Complex.div_im] at h
  exact xi_divisor_support_im_ne_zero q.1 h

/-! ## Separation from every second-order Einstein grade -/

/-- Cubic AIME weight differs from the Hermitian mixed quadratic weight at every Xi divisor. -/
theorem d4ThetaTeukolskyAIMECubicCuspWeight_ne_quadraticMixed (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinHermitianMixedCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq]
  intro h
  have him := congrArg Complex.im h
  simp [d4ThetaEinsteinHermitianMixedCuspWeight] at him
  exact d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero q (by linarith)

/-- Cubic AIME weight differs from the anti-chiral quadratic weight at every Xi divisor. -/
theorem d4ThetaTeukolskyAIMECubicCuspWeight_ne_quadraticAnti (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinAntiChiralQuadraticCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq]
  intro h
  have him := congrArg Complex.im h
  simp [d4ThetaEinsteinAntiChiralQuadraticCuspWeight] at him
  exact d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero q (by linarith)

/-- Arbitrary one-seed quadratic Einstein source resolved over all three helicity grades. -/
def d4ThetaEinsteinArbitraryQuadraticGradeSource
    (chiral mixed anti : ℂ) (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  (if weight = d4ThetaTeukolskyQuadraticChiralCuspWeight (xiSpectralPoint q)
    then chiral else 0) +
  (if weight = d4ThetaEinsteinHermitianMixedCuspWeight (xiSpectralPoint q)
    then mixed else 0) +
  if weight = d4ThetaEinsteinAntiChiralQuadraticCuspWeight (xiSpectralPoint q)
    then anti else 0

/-- Complete quadratic Einstein source has zero coefficient in the cubic AIME grade. -/
theorem d4ThetaEinsteinArbitraryQuadraticGradeSource_at_aimeCubic_eq_zero
    (chiral mixed anti : ℂ) (q : XiZeroCopy) :
    d4ThetaEinsteinArbitraryQuadraticGradeSource chiral mixed anti q
        (d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q)) = 0 := by
  simp [d4ThetaEinsteinArbitraryQuadraticGradeSource,
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_ne_quadraticChiral q,
    d4ThetaTeukolskyAIMECubicCuspWeight_ne_quadraticMixed q,
    d4ThetaTeukolskyAIMECubicCuspWeight_ne_quadraticAnti q]

/-! ## Unique same-grade cubic helicity channel -/

/-- Cusp weight of the pure positive-helicity cubic monomial `A^(3 : ℕ)`. -/
def d4ThetaEinsteinPureChiralCubicCuspWeight (z : ℂ) : ℂ :=
  3 * d4ThetaTeukolskyLinearCuspWeight z

/-- Cusp weight of the conjugate mixed cubic monomial `A * conj(A)^(2 : ℕ)`. -/
def d4ThetaEinsteinConjugateMixedCubicCuspWeight (z : ℂ) : ℂ :=
  d4ThetaTeukolskyLinearCuspWeight z +
    2 * star (d4ThetaTeukolskyLinearCuspWeight z)

/-- Cusp weight of the pure negative-helicity cubic monomial `conj(A)^(3 : ℕ)`. -/
def d4ThetaEinsteinPureAntiChiralCubicCuspWeight (z : ℂ) : ℂ :=
  3 * star (d4ThetaTeukolskyLinearCuspWeight z)

/-- AIME's `++-` weight differs from the pure chiral cubic weight at every Xi divisor. -/
theorem d4ThetaTeukolskyAIMECubicCuspWeight_ne_pureChiralCubic (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinPureChiralCubicCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq]
  intro h
  have him := congrArg Complex.im h
  simp [d4ThetaEinsteinPureChiralCubicCuspWeight] at him
  exact d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero q (by linarith)

/-- AIME's `++-` weight differs from the `+--` cubic weight at every Xi divisor. -/
theorem d4ThetaTeukolskyAIMECubicCuspWeight_ne_conjugateMixedCubic (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinConjugateMixedCubicCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq]
  intro h
  have him := congrArg Complex.im h
  simp [d4ThetaEinsteinConjugateMixedCubicCuspWeight] at him
  exact d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero q (by linarith)

/-- AIME's `++-` weight differs from the pure anti-chiral cubic weight at every Xi divisor. -/
theorem d4ThetaTeukolskyAIMECubicCuspWeight_ne_pureAntiCubic (q : XiZeroCopy) :
    d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q) ≠
      d4ThetaEinsteinPureAntiChiralCubicCuspWeight (xiSpectralPoint q) := by
  rw [d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight_eq]
  intro h
  have him := congrArg Complex.im h
  simp [d4ThetaEinsteinPureAntiChiralCubicCuspWeight] at him
  exact d4ThetaTeukolskyLinearCuspWeight_xi_im_ne_zero q (by linarith)

/-- Arbitrary one-seed cubic Einstein source resolved over its four helicity grades. -/
def d4ThetaEinsteinCubicGradeSource
    (pureChiral aimeCompatible conjugateMixed pureAnti : ℂ)
    (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  (if weight = d4ThetaEinsteinPureChiralCubicCuspWeight (xiSpectralPoint q)
    then pureChiral else 0) +
  (if weight = d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight
      (xiSpectralPoint q) then aimeCompatible else 0) +
  (if weight = d4ThetaEinsteinConjugateMixedCubicCuspWeight (xiSpectralPoint q)
    then conjugateMixed else 0) +
  if weight = d4ThetaEinsteinPureAntiChiralCubicCuspWeight (xiSpectralPoint q)
    then pureAnti else 0

/-- Projection onto AIME grade extracts only third-order `++-` coefficient. -/
theorem d4ThetaEinsteinCubicGradeSource_at_aime_eq
    (pureChiral aimeCompatible conjugateMixed pureAnti : ℂ) (q : XiZeroCopy) :
    d4ThetaEinsteinCubicGradeSource pureChiral aimeCompatible conjugateMixed pureAnti q
        (d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q)) =
      aimeCompatible := by
  simp [d4ThetaEinsteinCubicGradeSource,
    d4ThetaTeukolskyAIMECubicCuspWeight_ne_pureChiralCubic q,
    d4ThetaTeukolskyAIMECubicCuspWeight_ne_conjugateMixedCubic q,
    d4ThetaTeukolskyAIMECubicCuspWeight_ne_pureAntiCubic q]

/-- Einstein source through third order, with perturbative orders kept as separate summands. -/
def d4ThetaEinsteinThroughCubicGradeSource
    (quadraticChiral quadraticMixed quadraticAnti
      cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti : ℂ)
    (q : XiZeroCopy) (weight : ℂ) : ℂ :=
  d4ThetaEinsteinArbitraryQuadraticGradeSource
      quadraticChiral quadraticMixed quadraticAnti q weight +
    d4ThetaEinsteinCubicGradeSource
      cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti q weight

/-- Through third order, AIME-grade projection is exactly the cubic `++-` coefficient. -/
theorem d4ThetaEinsteinThroughCubicGradeSource_at_aime_eq
    (quadraticChiral quadraticMixed quadraticAnti
      cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti : ℂ)
    (q : XiZeroCopy) :
    d4ThetaEinsteinThroughCubicGradeSource quadraticChiral quadraticMixed quadraticAnti
        cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti q
        (d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight (xiSpectralPoint q)) =
      cubicAIME := by
  rw [d4ThetaEinsteinThroughCubicGradeSource,
    d4ThetaEinsteinArbitraryQuadraticGradeSource_at_aimeCubic_eq_zero,
    d4ThetaEinsteinCubicGradeSource_at_aime_eq]
  simp

/-- Exact correction of same-pole classification: only third-order `++-` coefficient can cancel
the AIME numerator; all quadratic and other cubic coefficients disappear under grade projection. -/
theorem d4ThetaEinsteinThroughCubicAIMENumerator_eq_zero_iff
    (amplitude quadraticChiral quadraticMixed quadraticAnti
      cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti : ℂ)
    (q : XiZeroCopy) :
    d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
        d4ThetaEinsteinThroughCubicGradeSource quadraticChiral quadraticMixed quadraticAnti
          cubicPureChiral cubicAIME cubicConjugateMixed cubicPureAnti q
          (d4ThetaTeukolskyCubicHorizonMemoryReturnCuspWeight
            (xiSpectralPoint q)) = 0 ↔
      cubicAIME =
        -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4ThetaEinsteinThroughCubicGradeSource_at_aime_eq]
  constructor <;> intro h <;> linear_combination h

/-! ## Perturbative homogeneity obstruction -/

/-- A quadratic and a cubic coefficient cancelling at every real scale both vanish. -/
theorem d4ThetaQuadraticCubicScaleSeparation
    (quadratic cubic : ℂ)
    (hcancel : ∀ scale : ℝ,
      ((scale ^ (2 : ℕ) : ℝ) : ℂ) * quadratic +
        ((scale ^ (3 : ℕ) : ℝ) : ℂ) * cubic = 0) :
    quadratic = 0 ∧ cubic = 0 := by
  have h1 := hcancel 1
  have h2 := hcancel 2
  norm_num at h1 h2
  constructor
  · linear_combination 2 * h1 - (1 / 4) * h2
  · linear_combination (1 / 4) * h2 - h1

/-- Exact AIME numerator is homogeneous of degree three under real seed rescaling. -/
theorem d4FundamentalQNMCrossBranchAIMENumerator_realScale
    (scale : ℝ) (amplitude z : ℂ) :
    d4FundamentalQNMCrossBranchAIMENumerator ((scale : ℂ) * amplitude) z =
      ((scale ^ (3 : ℕ) : ℝ) : ℂ) *
        d4FundamentalQNMCrossBranchAIMENumerator amplitude z := by
  rw [d4FundamentalQNMCrossBranchAIMENumerator,
    d4FundamentalQNMCrossBranchAIMENumerator,
    Complex.normSq_mul, Complex.normSq_ofReal]
  push_cast
  ring

/-- No homogeneous second-order coefficient cancels nonzero AIME for every seed scale. -/
theorem d4ThetaNoQuadraticSourceCancelsAIMEAtEveryScale
    (amplitude quadratic : ℂ) (q : XiZeroCopy) (ha : amplitude ≠ 0) :
    ¬ (∀ scale : ℝ,
      ((scale ^ (2 : ℕ) : ℝ) : ℂ) * quadratic +
        d4FundamentalQNMCrossBranchAIMENumerator
          ((scale : ℂ) * amplitude) (xiSpectralPoint q) = 0) := by
  intro h
  have hcubic : ∀ scale : ℝ,
      ((scale ^ (2 : ℕ) : ℝ) : ℂ) * quadratic +
        ((scale ^ (3 : ℕ) : ℝ) : ℂ) *
          d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
    intro scale
    rw [← d4FundamentalQNMCrossBranchAIMENumerator_realScale]
    exact h scale
  have hsep := d4ThetaQuadraticCubicScaleSeparation quadratic
    (d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q)) hcubic
  exact (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).2 ha hsep.2

end

end RHTower
