import GaloisForLFunctions.RHTower.MobiusSquarefreeReciprocalTransfer

/-!
# The squarefree higher-trace correction is a positive shift contraction

The factor `ζ(2s)/ζ(2σ)` is not only holomorphic and harmless.  It is the Laplace multiplier of
the probability average of logarithmic translations with weights proportional to
`(n+1)^(-2σ)`.  Hence composing it with the signed Möbius shift preserves contractivity before
Gamma completion.
-/

open Complex MeasureTheory Filter
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Positive zeta-two Gibbs mass, indexed from zero to avoid a special zero term. -/
def zetaTwoShiftMass (sigma : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (-(2 * sigma))

theorem zetaTwoShiftMass_pos (sigma : ℝ) (n : ℕ) :
    0 < zetaTwoShiftMass sigma n := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem summable_zetaTwoShiftMass {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (zetaTwoShiftMass sigma) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * sigma))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa [zetaTwoShiftMass, Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 hbase

/-- The zeta-two partition function in positive real coordinates. -/
def zetaTwoShiftTotal (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, zetaTwoShiftMass sigma n

theorem zetaTwoShiftTotal_pos {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < zetaTwoShiftTotal sigma := by
  exact (summable_zetaTwoShiftMass hsigma).tsum_pos
    (fun n => (zetaTwoShiftMass_pos sigma n).le) 0 (zetaTwoShiftMass_pos sigma 0)

/-- The real partition function is the actual value `ζ(2σ)`. -/
theorem ofReal_zetaTwoShiftTotal_eq_riemannZeta
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (zetaTwoShiftTotal sigma : ℂ) = riemannZeta (2 * (sigma : ℂ)) := by
  have hmap := Complex.ofRealCLM.map_tsum (summable_zetaTwoShiftMass hsigma)
  simp only [Complex.ofRealCLM_apply] at hmap
  have harg : 1 < (2 * (sigma : ℂ)).re := by
    simp
    linarith
  calc
    (zetaTwoShiftTotal sigma : ℂ) =
        ∑' n : ℕ, (zetaTwoShiftMass sigma n : ℂ) := by
      rw [zetaTwoShiftTotal]
      exact hmap
    _ = ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℂ) ^ (2 * (sigma : ℂ))) := by
      apply tsum_congr
      intro n
      rw [zetaTwoShiftMass, Complex.ofReal_cpow (by positivity)]
      rw [show ((-(2 * sigma) : ℝ) : ℂ) = -(2 * (sigma : ℂ)) by
        push_cast
        ring]
      rw [Complex.cpow_neg, one_div]
      norm_cast
    _ = riemannZeta (2 * (sigma : ℂ)) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow harg]
      apply tsum_congr
      intro n
      norm_cast

/-- Zeta-two Gibbs probability. -/
def zetaTwoShiftProbability (sigma : ℝ) (n : ℕ) : ℝ :=
  zetaTwoShiftMass sigma n / zetaTwoShiftTotal sigma

theorem zetaTwoShiftProbability_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ) :
    0 ≤ zetaTwoShiftProbability sigma n :=
  div_nonneg (zetaTwoShiftMass_pos sigma n).le (zetaTwoShiftTotal_pos hsigma).le

theorem summable_zetaTwoShiftProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (zetaTwoShiftProbability sigma) :=
  (summable_zetaTwoShiftMass hsigma).div_const _

theorem tsum_zetaTwoShiftProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ∑' n : ℕ, zetaTwoShiftProbability sigma n = 1 := by
  rw [show (∑' n : ℕ, zetaTwoShiftProbability sigma n) =
      (∑' n : ℕ, zetaTwoShiftMass sigma n) / zetaTwoShiftTotal sigma by
    exact tsum_div_const]
  rw [show (∑' n : ℕ, zetaTwoShiftMass sigma n) = zetaTwoShiftTotal sigma by rfl]
  exact div_self (ne_of_gt (zetaTwoShiftTotal_pos hsigma))

/-- One positive logarithmic-translation channel. -/
def zetaTwoShiftTerm (sigma : ℝ) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  zetaTwoShiftProbability sigma n •
    MellinL2.additiveTranslationUnitary (-2 * Real.log (n + 1)) f

theorem norm_zetaTwoShiftTerm
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖zetaTwoShiftTerm sigma n f‖ = zetaTwoShiftProbability sigma n * ‖f‖ := by
  rw [zetaTwoShiftTerm, norm_smul, LinearIsometryEquiv.norm_map,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (zetaTwoShiftProbability_nonneg hsigma n)]

theorem summable_zetaTwoShiftTerm
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Summable (fun n => zetaTwoShiftTerm sigma n f) := by
  apply Summable.of_norm
  simpa only [norm_zetaTwoShiftTerm hsigma] using
    (summable_zetaTwoShiftProbability hsigma).mul_right ‖f‖

/-- Positive zeta-two average of logarithmic translations. -/
def zetaTwoShiftAverage (sigma : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑' n : ℕ, zetaTwoShiftTerm sigma n f

/-- The higher-trace correction is a contraction on logarithmic `L²`. -/
theorem norm_zetaTwoShiftAverage_le
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖zetaTwoShiftAverage sigma f‖ ≤ ‖f‖ := by
  have hnorm : Summable (fun n => ‖zetaTwoShiftTerm sigma n f‖) := by
    simpa only [norm_zetaTwoShiftTerm hsigma] using
      (summable_zetaTwoShiftProbability hsigma).mul_right ‖f‖
  calc
    ‖zetaTwoShiftAverage sigma f‖ ≤ ∑' n : ℕ, ‖zetaTwoShiftTerm sigma n f‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, zetaTwoShiftProbability sigma n * ‖f‖ := by
      apply tsum_congr
      exact fun n => norm_zetaTwoShiftTerm hsigma n f
    _ = (∑' n : ℕ, zetaTwoShiftProbability sigma n) * ‖f‖ := tsum_mul_right
    _ = ‖f‖ := by rw [tsum_zetaTwoShiftProbability hsigma, one_mul]

/-- The positive boundary term whose sum is the safe squarefree correction. -/
def zetaTwoBoundaryTerm (sigma x : ℝ) (n : ℕ) : ℝ :=
  zetaTwoShiftProbability sigma n *
    ((n + 1 : ℕ) : ℝ) ^ (-(2 * Real.pi * x))

theorem zetaTwoBoundaryTerm_eq
    (sigma x : ℝ) (n : ℕ) :
    zetaTwoBoundaryTerm sigma x n =
      zetaTwoShiftMass (sigma + Real.pi * x) n / zetaTwoShiftTotal sigma := by
  rw [zetaTwoBoundaryTerm, zetaTwoShiftProbability, zetaTwoShiftMass,
    zetaTwoShiftMass]
  rw [div_mul_eq_mul_div, ← Real.rpow_add (by positivity)]
  congr 2
  ring

theorem tsum_zetaTwoBoundaryTerm (sigma x : ℝ) :
    ∑' n : ℕ, zetaTwoBoundaryTerm sigma x n =
      zetaTwoShiftTotal (sigma + Real.pi * x) / zetaTwoShiftTotal sigma := by
  rw [show (∑' n : ℕ, zetaTwoBoundaryTerm sigma x n) =
      ∑' n : ℕ, zetaTwoShiftMass (sigma + Real.pi * x) n /
        zetaTwoShiftTotal sigma by
    apply tsum_congr
    exact zetaTwoBoundaryTerm_eq sigma x]
  rw [tsum_div_const]
  rfl

/-- The positive translation average has the exact safe-correction Laplace multiplier. -/
theorem ofReal_tsum_zetaTwoBoundaryTerm_eq_safeCorrection
    {sigma x : ℝ} (hsigma : 1 < sigma) (hx : 0 ≤ x) :
    ((∑' n : ℕ, zetaTwoBoundaryTerm sigma x n : ℝ) : ℂ) =
      mobiusSquarefreeSafeCorrection sigma x := by
  have hshift : 1 < sigma + Real.pi * x := by
    nlinarith [Real.pi_pos]
  rw [tsum_zetaTwoBoundaryTerm, Complex.ofReal_div,
    ofReal_zetaTwoShiftTotal_eq_riemannZeta hshift,
    ofReal_zetaTwoShiftTotal_eq_riemannZeta hsigma,
    mobiusSquarefreeSafeCorrection]

/-- The pre-Gamma reciprocal squarefree operator is the composition of the positive safe
correction with the actual signed Möbius contraction. -/
def mobiusSquarefreeShiftContraction (sigma : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  zetaTwoShiftAverage sigma (infiniteMobiusShiftAverage sigma f)

theorem norm_mobiusSquarefreeShiftContraction_le
    {sigma : ℝ} (hsigma : 1 < sigma)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mobiusSquarefreeShiftContraction sigma f‖ ≤ ‖f‖ :=
  (norm_zetaTwoShiftAverage_le hsigma _).trans
    (norm_infiniteMobiusShiftAverage_le hsigma f)

end RHTower

