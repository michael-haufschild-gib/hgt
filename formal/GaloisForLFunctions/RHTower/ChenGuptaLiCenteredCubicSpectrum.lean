import GaloisForLFunctions.RHTower.ChenGuptaLiOperatorNormReduction

noncomputable section

namespace RHTower

/-- Arithmetic mean of a nonnegative finite spectrum indexed by `Fin (R + 1)`. -/
def CGLSpectrumMean (R : ℕ) (spectrum : Fin (R + 1) → NNReal) : ℝ :=
  (∑ i, (spectrum i : ℝ)) / (R + 1 : ℝ)

/-- Cubic spectral excess above the cube of the arithmetic mean. -/
def CGLCenteredCubicDeviation (R : ℕ) (spectrum : Fin (R + 1) → NNReal) : ℝ :=
  ∑ i, (spectrum i : ℝ) ^ 3 - (R + 1 : ℝ) * CGLSpectrumMean R spectrum ^ 3

theorem sum_cglSpectrum_eq_card_mul_mean (R : ℕ) (spectrum : Fin (R + 1) → NNReal) :
    ∑ i, (spectrum i : ℝ) = (R + 1 : ℝ) * CGLSpectrumMean R spectrum := by
  unfold CGLSpectrumMean
  field_simp

theorem cglCenteredCubicDeviation_eq_sum_sq_mul (R : ℕ) (spectrum : Fin (R + 1) → NNReal) :
    CGLCenteredCubicDeviation R spectrum =
      ∑ i, ((spectrum i : ℝ) - CGLSpectrumMean R spectrum) ^ 2 *
        ((spectrum i : ℝ) + 2 * CGLSpectrumMean R spectrum) := by
  let μ := CGLSpectrumMean R spectrum
  have hsum : ∑ i, (spectrum i : ℝ) = (R + 1 : ℝ) * μ := by
    exact sum_cglSpectrum_eq_card_mul_mean R spectrum
  unfold CGLCenteredCubicDeviation
  change (∑ i, (spectrum i : ℝ) ^ 3) - (R + 1 : ℝ) * μ ^ 3 =
    ∑ i, ((spectrum i : ℝ) - μ) ^ 2 * ((spectrum i : ℝ) + 2 * μ)
  simp_rw [show ∀ i : Fin (R + 1),
      ((spectrum i : ℝ) - μ) ^ 2 * ((spectrum i : ℝ) + 2 * μ) =
        (spectrum i : ℝ) ^ 3 - 3 * (spectrum i : ℝ) * μ ^ 2 + 2 * μ ^ 3 by
      intro i
      ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlinear : ∑ i : Fin (R + 1), 3 * (spectrum i : ℝ) * μ ^ 2 =
      3 * μ ^ 2 * ∑ i, (spectrum i : ℝ) := by
    calc
      ∑ i : Fin (R + 1), 3 * (spectrum i : ℝ) * μ ^ 2 =
          ∑ i, (3 * μ ^ 2) * (spectrum i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 3 * μ ^ 2 * ∑ i, (spectrum i : ℝ) := by rw [Finset.mul_sum]
  have hconst : ∑ _i : Fin (R + 1), 2 * μ ^ 3 =
      (R + 1 : ℝ) * (2 * μ ^ 3) := by simp
  rw [hlinear, hconst, hsum]
  ring

theorem cglCenteredCubicDeviation_nonneg (R : ℕ) (spectrum : Fin (R + 1) → NNReal) :
    0 ≤ CGLCenteredCubicDeviation R spectrum := by
  rw [cglCenteredCubicDeviation_eq_sum_sq_mul]
  apply Finset.sum_nonneg
  intro i hi
  have hmean : 0 ≤ CGLSpectrumMean R spectrum := by
    unfold CGLSpectrumMean
    positivity
  exact mul_nonneg (sq_nonneg _) (by positivity)

theorem centeredCube_le_cglCenteredCubicDeviation (R : ℕ)
    (spectrum : Fin (R + 1) → NNReal) (j : Fin (R + 1)) :
    ((spectrum j : ℝ) - CGLSpectrumMean R spectrum) ^ 3 ≤
      CGLCenteredCubicDeviation R spectrum := by
  have hmean : 0 ≤ CGLSpectrumMean R spectrum := by
    unfold CGLSpectrumMean
    positivity
  have hterm_nonneg : ∀ i : Fin (R + 1),
      0 ≤ ((spectrum i : ℝ) - CGLSpectrumMean R spectrum) ^ 2 *
        ((spectrum i : ℝ) + 2 * CGLSpectrumMean R spectrum) := by
    intro i
    exact mul_nonneg (sq_nonneg _) (by positivity)
  rw [cglCenteredCubicDeviation_eq_sum_sq_mul]
  calc
    ((spectrum j : ℝ) - CGLSpectrumMean R spectrum) ^ 3 ≤
        ((spectrum j : ℝ) - CGLSpectrumMean R spectrum) ^ 2 *
          ((spectrum j : ℝ) + 2 * CGLSpectrumMean R spectrum) := by
      nlinarith [sq_nonneg ((spectrum j : ℝ) - CGLSpectrumMean R spectrum)]
    _ ≤ ∑ i, ((spectrum i : ℝ) - CGLSpectrumMean R spectrum) ^ 2 *
        ((spectrum i : ℝ) + 2 * CGLSpectrumMean R spectrum) := by
      exact Finset.single_le_sum (fun i hi => hterm_nonneg i) (Finset.mem_univ j)

theorem cglSpectrum_coordinate_le_mean_add_cuberoot (R : ℕ)
    (spectrum : Fin (R + 1) → NNReal) (j : Fin (R + 1)) :
    (spectrum j : ℝ) ≤ CGLSpectrumMean R spectrum +
      CGLCenteredCubicDeviation R spectrum ^ (1 / 3 : ℝ) := by
  let d : ℝ := (spectrum j : ℝ) - CGLSpectrumMean R spectrum
  let D : ℝ := CGLCenteredCubicDeviation R spectrum
  have hD : 0 ≤ D := cglCenteredCubicDeviation_nonneg R spectrum
  have hcube : d ^ 3 ≤ D := by
    exact centeredCube_le_cglCenteredCubicDeviation R spectrum j
  by_cases hd : d ≤ 0
  · have hroot : 0 ≤ D ^ (1 / 3 : ℝ) := Real.rpow_nonneg hD _
    dsimp [d] at hd
    linarith
  · have hdpos : 0 < d := lt_of_not_ge hd
    have hcubeR : d ^ (3 : ℝ) ≤ D := by
      simpa [Real.rpow_natCast] using hcube
    have hroot := Real.rpow_le_rpow (by positivity : 0 ≤ d ^ (3 : ℝ)) hcubeR
      (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hdle : d ≤ D ^ (1 / 3 : ℝ) := by
      rw [← Real.rpow_mul hdpos.le] at hroot
      norm_num at hroot
      simpa using hroot
    dsimp [d] at hdle
    linarith

theorem sqrt_cglSpectrum_coordinate_le_sqrtMean_add_sixthRoot (R : ℕ)
    (spectrum : Fin (R + 1) → NNReal) (j : Fin (R + 1)) :
    √(spectrum j : ℝ) ≤ √(CGLSpectrumMean R spectrum) +
      CGLCenteredCubicDeviation R spectrum ^ (1 / 6 : ℝ) := by
  let μ : ℝ := CGLSpectrumMean R spectrum
  let D : ℝ := CGLCenteredCubicDeviation R spectrum
  have hμ : 0 ≤ μ := by
    unfold μ CGLSpectrumMean
    positivity
  have hD : 0 ≤ D := cglCenteredCubicDeviation_nonneg R spectrum
  have hcoord : (spectrum j : ℝ) ≤ μ + D ^ (1 / 3 : ℝ) := by
    exact cglSpectrum_coordinate_le_mean_add_cuberoot R spectrum j
  have hroot : √(spectrum j : ℝ) ≤ √(μ + D ^ (1 / 3 : ℝ)) :=
    Real.sqrt_le_sqrt hcoord
  have hD13 : 0 ≤ D ^ (1 / 3 : ℝ) := Real.rpow_nonneg hD _
  have hsplit : √(μ + D ^ (1 / 3 : ℝ)) ≤ √μ + √(D ^ (1 / 3 : ℝ)) := by
    have hsquare : (√(μ + D ^ (1 / 3 : ℝ)) : ℝ) ^ 2 = μ + D ^ (1 / 3 : ℝ) :=
      Real.sq_sqrt (add_nonneg hμ hD13)
    have hμsquare : (√μ : ℝ) ^ 2 = μ := Real.sq_sqrt hμ
    have hD13square : (√(D ^ (1 / 3 : ℝ)) : ℝ) ^ 2 = D ^ (1 / 3 : ℝ) :=
      Real.sq_sqrt hD13
    by_contra hsplit
    have hlt : √μ + √(D ^ (1 / 3 : ℝ)) < √(μ + D ^ (1 / 3 : ℝ)) := lt_of_not_ge hsplit
    have hdiff : 0 < √(μ + D ^ (1 / 3 : ℝ)) -
        (√μ + √(D ^ (1 / 3 : ℝ))) := sub_pos.mpr hlt
    have hsumpos : 0 < √(μ + D ^ (1 / 3 : ℝ)) +
        (√μ + √(D ^ (1 / 3 : ℝ))) := by
      nlinarith [Real.sqrt_nonneg μ, Real.sqrt_nonneg (D ^ (1 / 3 : ℝ))]
    have hmul : 0 < (√(μ + D ^ (1 / 3 : ℝ)) -
        (√μ + √(D ^ (1 / 3 : ℝ)))) *
        (√(μ + D ^ (1 / 3 : ℝ)) + (√μ + √(D ^ (1 / 3 : ℝ)))) :=
      mul_pos hdiff hsumpos
    have hsquares : (√μ + √(D ^ (1 / 3 : ℝ))) ^ 2 <
        (√(μ + D ^ (1 / 3 : ℝ))) ^ 2 := by
      nlinarith
    nlinarith [mul_nonneg (Real.sqrt_nonneg μ) (Real.sqrt_nonneg (D ^ (1 / 3 : ℝ)))]
  have hsixth : √(D ^ (1 / 3 : ℝ)) = D ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hD]
    congr 1
    ring
  calc
    √(spectrum j : ℝ) ≤ √(μ + D ^ (1 / 3 : ℝ)) := hroot
    _ ≤ √μ + √(D ^ (1 / 3 : ℝ)) := hsplit
    _ = √μ + D ^ (1 / 6 : ℝ) := by rw [hsixth]

theorem sqrt_cglSpectrum_coordinate_le_twoConstantBound (R : ℕ)
    (spectrum : Fin (R + 1) → NNReal) (j : Fin (R + 1)) :
    √(spectrum j : ℝ) ≤
      2 * CGLCenteredCubicDeviation R spectrum ^ (1 / 6 : ℝ) +
        2 * √(CGLSpectrumMean R spectrum) := by
  have h := sqrt_cglSpectrum_coordinate_le_sqrtMean_add_sixthRoot R spectrum j
  have hD : 0 ≤ CGLCenteredCubicDeviation R spectrum :=
    cglCenteredCubicDeviation_nonneg R spectrum
  have hroot : 0 ≤ CGLCenteredCubicDeviation R spectrum ^ (1 / 6 : ℝ) :=
    Real.rpow_nonneg hD _
  have hmean : 0 ≤ CGLSpectrumMean R spectrum := by
    unfold CGLSpectrumMean
    positivity
  nlinarith [Real.sqrt_nonneg (CGLSpectrumMean R spectrum)]

end RHTower
