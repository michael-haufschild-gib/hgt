import GaloisForLFunctions.RHTower.FZZCigarParityDiagonalFlowDetectorHorizon

/-!
# Uniform fixed-reporter escape under stabilized FZZ diagonal flow

The stabilized source flow acts affinely on all Hermitian reporter coefficients.  Because the
literal Fermi source ratio `Q/R` is strictly greater than one, a single source-defined positive
time ejects every initially separating fixed reporter from the sharp reciprocal-radius cone.
-/

open Complex

namespace RHTower

noncomputable section

/-- First coefficient of an arbitrary Hermitian reporter pulled back along stabilized flow. -/
def fzzCigarParityDilatedStabilizedFlowHermitianA
    (beta t a b d : ℝ) : ℝ :=
  Real.exp (fzzKreinPAt beta * t) ^ (2 : ℕ) * a -
    2 * Real.exp (fzzKreinPAt beta * t) *
      fzzCigarParityDilatedSecondDiagonalFlowShear beta t * b +
    fzzCigarParityDilatedSecondDiagonalFlowShear beta t ^ (2 : ℕ) * d

/-- Real off-diagonal coefficient after pullback. -/
def fzzCigarParityDilatedStabilizedFlowHermitianB
    (beta t b d : ℝ) : ℝ :=
  Real.exp (fzzKreinPAt beta * t) * b -
    fzzCigarParityDilatedSecondDiagonalFlowShear beta t * d

/-- Chiral coefficient after pullback. -/
def fzzCigarParityDilatedStabilizedFlowHermitianC
    (beta t c : ℝ) : ℝ :=
  Real.exp (fzzKreinPAt beta * t) * c

private theorem fzzCigarParityHermitianQuadraticObservable_realTriangular_pullback
    (e k a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (((e : ℝ) : ℂ) * u.1, u.2 - (k : ℂ) * u.1) =
      fzzCigarParityHermitianQuadraticObservable
        (e ^ (2 : ℕ) * a - 2 * e * k * b + k ^ (2 : ℕ) * d)
        (e * b - k * d) (e * c) d u := by
  rcases u with ⟨u₁, u₂⟩
  simp [fzzCigarParityHermitianQuadraticObservable,
    Complex.conj_ofReal, star_sub, star_mul]
  ring

/-- Exact coefficient-space action of the stabilized flow on every Hermitian reporter. -/
theorem fzzCigarParityDilatedSecondDiagonalStabilizedFlow_hermitian_pullback
    (beta t a b c d : ℝ) (u : ℂ × ℂ) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityDilatedSecondDiagonalStabilizedFlow beta t u) =
      fzzCigarParityHermitianQuadraticObservable
        (fzzCigarParityDilatedStabilizedFlowHermitianA beta t a b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianB beta t b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianC beta t c) d u := by
  simpa [fzzCigarParityDilatedSecondDiagonalStabilizedFlow,
    fzzCigarParityDilatedStabilizedFlowHermitianA,
    fzzCigarParityDilatedStabilizedFlowHermitianB,
    fzzCigarParityDilatedStabilizedFlowHermitianC] using
    fzzCigarParityHermitianQuadraticObservable_realTriangular_pullback
      (Real.exp (fzzKreinPAt beta * t))
      (fzzCigarParityDilatedSecondDiagonalFlowShear beta t) a b c d u

/-- Reciprocal-radius detector membership is completely independent of the first-coordinate
coefficient. -/
theorem fzzCigarParityHermitianUniversalRadialReflectionSeparating_congr_first
    (a a' b c d : ℝ) :
    FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d ↔
      FZZCigarParityHermitianUniversalRadialReflectionSeparating a' b c d := by
  rw [fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff,
    fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff]

/-- Literal source shear slope. -/
def fzzCigarParityDilatedStabilizedFlowSlope (beta : ℝ) : ℝ :=
  fzzKreinQAt beta / fzzKreinRAt beta

theorem fzzKreinQAt_gt_fzzKreinRAt
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzKreinRAt beta < fzzKreinQAt beta := by
  change fzzCigarParityDelay (4 * beta) < fzzCigarParityDelay (2 * beta)
  rw [fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta),
    fzzCigarParityDelay_eq_fermi (mul_pos (by norm_num) hbeta)]
  have hexp : Real.exp (2 * beta) + 1 < Real.exp (4 * beta) + 1 := by
    have := Real.exp_lt_exp.mpr (by nlinarith : 2 * beta < 4 * beta)
    linarith
  simpa [one_div] using one_div_lt_one_div_of_lt (by positivity) hexp

theorem fzzCigarParityDilatedStabilizedFlowSlope_gt_one
    {beta : ℝ} (hbeta : 0 < beta) :
    1 < fzzCigarParityDilatedStabilizedFlowSlope beta := by
  rw [fzzCigarParityDilatedStabilizedFlowSlope,
    one_lt_div₀ (fzzKreinRAt_pos hbeta)]
  exact fzzKreinQAt_gt_fzzKreinRAt hbeta

/-- Source multiplier beyond the intersection time of initial and transported detector disks. -/
def fzzCigarParityDilatedFixedReporterEscapeMultiplier
    (beta : ℝ) : ℝ :=
  2 * fzzCigarParityDilatedStabilizedFlowSlope beta /
    (fzzCigarParityDilatedStabilizedFlowSlope beta - 1)

/-- Uniform source time at which no initially separating fixed reporter remains separating. -/
def fzzCigarParityDilatedFixedReporterEscapeTime
    (beta : ℝ) : ℝ :=
  Real.log (fzzCigarParityDilatedFixedReporterEscapeMultiplier beta) /
    fzzKreinPAt beta

theorem fzzCigarParityDilatedFixedReporterEscapeMultiplier_gt_one
    {beta : ℝ} (hbeta : 0 < beta) :
    1 < fzzCigarParityDilatedFixedReporterEscapeMultiplier beta := by
  have hα := fzzCigarParityDilatedStabilizedFlowSlope_gt_one hbeta
  rw [fzzCigarParityDilatedFixedReporterEscapeMultiplier]
  rw [lt_div_iff₀ (sub_pos.mpr hα)]
  nlinarith

theorem fzzCigarParityDilatedFixedReporterEscapeTime_pos
    {beta : ℝ} (hbeta : 0 < beta) :
    0 < fzzCigarParityDilatedFixedReporterEscapeTime beta := by
  rw [fzzCigarParityDilatedFixedReporterEscapeTime]
  exact div_pos
    (Real.log_pos
      (fzzCigarParityDilatedFixedReporterEscapeMultiplier_gt_one hbeta))
    (fzzKreinPAt_pos hbeta)

theorem fzzCigarParityDilatedFixedReporterEscapeTime_exp
    {beta : ℝ} (hbeta : 0 < beta) :
    Real.exp
        (fzzKreinPAt beta *
          fzzCigarParityDilatedFixedReporterEscapeTime beta) =
      fzzCigarParityDilatedFixedReporterEscapeMultiplier beta := by
  have hP := fzzKreinPAt_pos hbeta
  have hE :=
    fzzCigarParityDilatedFixedReporterEscapeMultiplier_gt_one hbeta
  rw [fzzCigarParityDilatedFixedReporterEscapeTime]
  have hcancel :
      fzzKreinPAt beta *
          (Real.log (fzzCigarParityDilatedFixedReporterEscapeMultiplier beta) /
            fzzKreinPAt beta) =
        Real.log (fzzCigarParityDilatedFixedReporterEscapeMultiplier beta) := by
    field_simp [hP.ne']
  rw [hcancel, Real.exp_log (lt_trans zero_lt_one hE)]

theorem fzzCigarParityDilatedFixedReporterEscapeMultiplier_source_strict
    {beta : ℝ} (hbeta : 0 < beta) :
    fzzCigarParityDilatedFixedReporterEscapeMultiplier beta + 1 <
      fzzCigarParityDilatedStabilizedFlowSlope beta *
        (fzzCigarParityDilatedFixedReporterEscapeMultiplier beta - 1) := by
  let α := fzzCigarParityDilatedStabilizedFlowSlope beta
  have hα : 1 < α := fzzCigarParityDilatedStabilizedFlowSlope_gt_one hbeta
  have hne : α - 1 ≠ 0 := (sub_pos.mpr hα).ne'
  have hid :
      α * ((2 * α / (α - 1)) - 1) -
          ((2 * α / (α - 1)) + 1) =
        α - 1 := by
    field_simp [hne]
    ring
  change 2 * α / (α - 1) + 1 <
    α * (2 * α / (α - 1) - 1)
  nlinarith

theorem fzzCigarParityDilatedFixedReporter_uniform_escape
    {beta a b c d : ℝ} (hbeta : 0 < beta)
    (hzero :
      FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d) :
    ¬ FZZCigarParityHermitianUniversalRadialReflectionSeparating
        (fzzCigarParityDilatedStabilizedFlowHermitianA beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) a b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianB beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianC beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) c) d := by
  intro hlate
  have hcone0 :=
    (fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff
      a b c d).mp hzero
  have hconeLate :=
    (fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff
      (fzzCigarParityDilatedStabilizedFlowHermitianA beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) a b d)
      (fzzCigarParityDilatedStabilizedFlowHermitianB beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) b d)
      (fzzCigarParityDilatedStabilizedFlowHermitianC beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) c) d).mp hlate
  have hb0sq : b ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    nlinarith [sq_nonneg c]
  have hb0 : |b| ≤ |d| := sq_le_sq.mp hb0sq
  let E := fzzCigarParityDilatedFixedReporterEscapeMultiplier beta
  let α := fzzCigarParityDilatedStabilizedFlowSlope beta
  have hα : 1 < α := fzzCigarParityDilatedStabilizedFlowSlope_gt_one hbeta
  have hE : 1 < E :=
    fzzCigarParityDilatedFixedReporterEscapeMultiplier_gt_one hbeta
  have hexp :
      Real.exp
          (fzzKreinPAt beta *
            fzzCigarParityDilatedFixedReporterEscapeTime beta) = E :=
    fzzCigarParityDilatedFixedReporterEscapeTime_exp hbeta
  have hbEsq : (E * b - α * (E - 1) * d) ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
    have hbc := hconeLate.2
    have hCnonneg :
        0 ≤
          fzzCigarParityDilatedStabilizedFlowHermitianC beta
            (fzzCigarParityDilatedFixedReporterEscapeTime beta) c ^ (2 : ℕ) :=
      sq_nonneg _
    have hBsq :
        fzzCigarParityDilatedStabilizedFlowHermitianB beta
            (fzzCigarParityDilatedFixedReporterEscapeTime beta) b d ^ (2 : ℕ) ≤
          d ^ (2 : ℕ) := by
      nlinarith
    rw [fzzCigarParityDilatedStabilizedFlowHermitianB,
      fzzCigarParityDilatedSecondDiagonalFlowShear,
      ← fzzCigarParityDilatedStabilizedFlowSlope] at hBsq
    rw [hexp] at hBsq
    exact hBsq
  have hbE : |E * b - α * (E - 1) * d| ≤ |d| :=
    sq_le_sq.mp hbEsq
  have hbound : |d| * (α * (E - 1)) ≤ |d| * (E + 1) := by
    calc
      |d| * (α * (E - 1)) = |α * (E - 1) * d| := by
        simp only [abs_mul,
          abs_of_pos (lt_trans zero_lt_one hα),
          abs_of_pos (sub_pos.mpr hE)]
        ring
      _ = |E * b - (E * b - α * (E - 1) * d)| := by
        congr 1
        ring
      _ ≤ |E * b| + |E * b - α * (E - 1) * d| := abs_sub _ _
      _ ≤ E * |d| + |d| := by
        apply add_le_add
        · rw [abs_mul, abs_of_pos (lt_trans zero_lt_one hE)]
          exact mul_le_mul_of_nonneg_left hb0 (le_trans zero_le_one hE.le)
        · exact hbE
      _ = |d| * (E + 1) := by ring
  have hdabs : 0 < |d| := abs_pos.mpr hcone0.1
  have hnecessary : α * (E - 1) ≤ E + 1 := by
    by_contra hnot
    have hpos :
        0 < |d| * (α * (E - 1) - (E + 1)) :=
      mul_pos hdabs (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith
  have hstrict : E + 1 < α * (E - 1) :=
    fzzCigarParityDilatedFixedReporterEscapeMultiplier_source_strict hbeta
  linarith

/-- No arbitrary first-coordinate counterterm repairs uniform cone escape. -/
theorem fzzCigarParityDilatedFixedReporter_uniform_escape_firstCounterterm
    {beta a b c d : ℝ} (hbeta : 0 < beta)
    (hzero :
      FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d)
    (counterterm : ℝ) :
    ¬ FZZCigarParityHermitianUniversalRadialReflectionSeparating
        (fzzCigarParityDilatedStabilizedFlowHermitianA beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) a b d + counterterm)
        (fzzCigarParityDilatedStabilizedFlowHermitianB beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianC beta
          (fzzCigarParityDilatedFixedReporterEscapeTime beta) c) d := by
  intro hrepair
  apply fzzCigarParityDilatedFixedReporter_uniform_escape hbeta hzero
  exact
    (fzzCigarParityHermitianUniversalRadialReflectionSeparating_congr_first
      (fzzCigarParityDilatedStabilizedFlowHermitianA beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) a b d + counterterm)
      (fzzCigarParityDilatedStabilizedFlowHermitianA beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) a b d)
      (fzzCigarParityDilatedStabilizedFlowHermitianB beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) b d)
      (fzzCigarParityDilatedStabilizedFlowHermitianC beta
        (fzzCigarParityDilatedFixedReporterEscapeTime beta) c) d).mp hrepair

/-- No fixed Hermitian reciprocal-radius detector survives every nonnegative source-flow time. -/
theorem not_fzzCigarParityDilatedFixedHermitianReporter_allTimeSeparating
    {beta a b c d : ℝ} (hbeta : 0 < beta) :
    ¬ (∀ t : ℝ, 0 ≤ t →
      FZZCigarParityHermitianUniversalRadialReflectionSeparating
        (fzzCigarParityDilatedStabilizedFlowHermitianA beta t a b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianB beta t b d)
        (fzzCigarParityDilatedStabilizedFlowHermitianC beta t c) d) := by
  intro hall
  have hzero := hall 0 le_rfl
  have hzero' :
      FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d := by
    simpa [fzzCigarParityDilatedStabilizedFlowHermitianA,
      fzzCigarParityDilatedStabilizedFlowHermitianB,
      fzzCigarParityDilatedStabilizedFlowHermitianC,
      fzzCigarParityDilatedSecondDiagonalFlowShear] using hzero
  exact fzzCigarParityDilatedFixedReporter_uniform_escape hbeta hzero'
    (hall (fzzCigarParityDilatedFixedReporterEscapeTime beta)
      (fzzCigarParityDilatedFixedReporterEscapeTime_pos hbeta).le)

end

end RHTower

