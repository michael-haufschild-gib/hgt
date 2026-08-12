import GaloisForLFunctions.RHTower.Sieve.MaynardArbitraryAmplitudeCount

/-!
# Exact reserve geometry at Maynard's near-one endpoint

The corrected fixed-Perron-abscissa Huxley count has exponent reserve

`(mu - 2b) * (1 - alpha) - b * rho`, where `b = 1367/2160`.

This file isolates the sharp endpoint law.  It proves that every positive energy loss forces a
strict amplitude gap, identifies the exact gap required to absorb an additional exponent `gamma`,
and shows that the matched schedule already used by Route T is sharp at the worst height slope
`mu = 4/3`.
-/

noncomputable section
namespace RHTower.Sieve

/-- Huxley's raised-length coefficient in the corrected amplitude count. -/
def maynardHuxleyLengthSlope : ℝ := 1367 / 2160

/-- Power reserve between Maynard alternative (i) and the corrected Huxley fibre count. -/
def maynardHuxleyAmplitudeReserve (mu alpha rho : ℝ) : ℝ :=
  (mu - 2 * maynardHuxleyLengthSlope) * (1 - alpha) -
    maynardHuxleyLengthSlope * rho

/-- Exact amplitude gap required to pay energy exponent `rho` and remaining exponent `gamma`. -/
def maynardRequiredAmplitudeGap (mu rho gamma : ℝ) : ℝ :=
  (gamma + maynardHuxleyLengthSlope * rho) /
    (mu - 2 * maynardHuxleyLengthSlope)

theorem maynardHuxleyLengthSlope_pos : 0 < maynardHuxleyLengthSlope := by
  norm_num [maynardHuxleyLengthSlope]

theorem maynard_worst_height_slope_gap :
    (4 / 3 : ℝ) - 2 * maynardHuxleyLengthSlope = 73 / 1080 := by
  norm_num [maynardHuxleyLengthSlope]

/-- At maximal amplitude the corrected reserve is strictly negative for every positive energy
loss.  Thus no fixed positive `rho` reaches `alpha = 1`. -/
theorem maynardHuxleyAmplitudeReserve_at_one (mu rho : ℝ) :
    maynardHuxleyAmplitudeReserve mu 1 rho =
      -maynardHuxleyLengthSlope * rho := by
  simp [maynardHuxleyAmplitudeReserve]

theorem maynardHuxleyAmplitudeReserve_at_one_neg
    (mu : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    maynardHuxleyAmplitudeReserve mu 1 rho < 0 := by
  rw [maynardHuxleyAmplitudeReserve_at_one]
  have hprod := mul_pos maynardHuxleyLengthSlope_pos hrho
  nlinarith

/-- Exact threshold law: paying an extra exponent `gamma` is equivalent to separating the
amplitude from one by `maynardRequiredAmplitudeGap`. -/
theorem gamma_le_maynardHuxleyAmplitudeReserve_iff
    {mu alpha rho gamma : ℝ}
    (hmu : 2 * maynardHuxleyLengthSlope < mu) :
    gamma ≤ maynardHuxleyAmplitudeReserve mu alpha rho ↔
      alpha ≤ 1 - maynardRequiredAmplitudeGap mu rho gamma := by
  have hden : 0 < mu - 2 * maynardHuxleyLengthSlope := by linarith
  constructor
  · intro h
    have hmul :
        gamma + maynardHuxleyLengthSlope * rho ≤
          (mu - 2 * maynardHuxleyLengthSlope) * (1 - alpha) := by
      dsimp [maynardHuxleyAmplitudeReserve] at h
      linarith
    have hdiv :
        (gamma + maynardHuxleyLengthSlope * rho) /
            (mu - 2 * maynardHuxleyLengthSlope) ≤
          1 - alpha := by
      exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hmul)
    dsimp [maynardRequiredAmplitudeGap]
    linarith
  · intro h
    have hdiv :
        (gamma + maynardHuxleyLengthSlope * rho) /
            (mu - 2 * maynardHuxleyLengthSlope) ≤
          1 - alpha := by
      dsimp [maynardRequiredAmplitudeGap] at h
      linarith
    have hmul :
        gamma + maynardHuxleyLengthSlope * rho ≤
          (mu - 2 * maynardHuxleyLengthSlope) * (1 - alpha) := by
      exact (div_le_iff₀ hden).1 hdiv |>.trans_eq (mul_comm _ _)
    dsimp [maynardHuxleyAmplitudeReserve]
    linarith

/-- Positive reserve with positive energy loss forces a strict amplitude gap. -/
theorem alpha_lt_one_of_maynardHuxleyAmplitudeReserve_pos
    {mu alpha rho : ℝ}
    (hmu : 2 * maynardHuxleyLengthSlope < mu)
    (hrho : 0 < rho)
    (hreserve : 0 < maynardHuxleyAmplitudeReserve mu alpha rho) :
    alpha < 1 := by
  have hthreshold :=
    (gamma_le_maynardHuxleyAmplitudeReserve_iff
      (mu := mu) (alpha := alpha) (rho := rho) (gamma := 0) hmu).1 hreserve.le
  have hgap : 0 < maynardRequiredAmplitudeGap mu rho 0 := by
    dsimp [maynardRequiredAmplitudeGap]
    have hnum : 0 < maynardHuxleyLengthSlope * rho :=
      mul_pos maynardHuxleyLengthSlope_pos hrho
    have hden : 0 < mu - 2 * maynardHuxleyLengthSlope := by linarith
    exact div_pos (by simpa using hnum) hden
  linarith

/-- The worst Route-T height slope has the exact required-gap denominator `73/1080`. -/
theorem maynardRequiredAmplitudeGap_at_worst_height (rho gamma : ℝ) :
    maynardRequiredAmplitudeGap (4 / 3) rho gamma =
      (gamma + maynardHuxleyLengthSlope * rho) / (73 / 1080 : ℝ) := by
  rw [maynardRequiredAmplitudeGap, maynard_worst_height_slope_gap]

/-- The matched energy schedule is sharp: at `mu=4/3` and boundary amplitude `alpha=1-d`,
the reserve is exactly `73d/2160`, not merely bounded below by it. -/
theorem maynard_pointwise_matched_reserve_sharp (d : ℝ) :
    maynardHuxleyAmplitudeReserve (4 / 3) (1 - d)
        (maynardPointwiseMatchedRho d) =
      (73 / 2160 : ℝ) * d := by
  dsimp [maynardHuxleyAmplitudeReserve, maynardHuxleyLengthSlope,
    maynardPointwiseMatchedRho]
  ring

/-- Conversely, at the worst height slope the matched schedule cannot pay any positive additional
exponent at the boundary amplitude.  Endpoint work must create more amplitude gap or remove the
remaining cost before Huxley counting. -/
theorem maynard_pointwise_matched_boundary_cannot_pay
    {d gamma : ℝ} (hgamma : 0 < gamma) :
    ¬ gamma ≤ maynardHuxleyAmplitudeReserve (4 / 3) (1 - d)
      (maynardPointwiseMatchedRho d) - (73 / 2160 : ℝ) * d := by
  rw [maynard_pointwise_matched_reserve_sharp]
  norm_num
  exact hgamma

end RHTower.Sieve
