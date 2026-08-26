import GaloisForLFunctions.RHTower.Sieve.BarbanVehovHigherSelbergForms

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Continuous-window base main at logarithmic window length `log N`. -/
def barbanVehovLongBasePolynomialMain (N : ℕ) : ℝ :=
  Real.log N * barbanVehovSelbergDiagonal N

/-- Continuous-window mixed main when `log L / log N = p`. -/
def barbanVehovLongCrossPolynomialMain (p : ℝ) (N : ℕ) : ℝ :=
  -(Real.log N * barbanVehovSelbergMixedDiagonal N +
    (p - 1 / 2) * Real.log N ^ 2 * barbanVehovSelbergDiagonal N)

/-- Continuous-window differentiated main when `log L / log N = p`. -/
def barbanVehovLongDerivativePolynomialMain (p : ℝ) (N : ℕ) : ℝ :=
  Real.log N * barbanVehovSelbergQuadraticLogDiagonal N +
    (2 * p - 1) * Real.log N ^ 2 * barbanVehovSelbergMixedDiagonal N +
    (p ^ 2 - p + 1 / 3) * Real.log N ^ 3 * barbanVehovSelbergDiagonal N

/-- Continuous-window detector energy at `lambda = r / log N`. -/
def barbanVehovLongEnergyPolynomialMain (p r : ℝ) (N : ℕ) : ℝ :=
  (barbanVehovLongBasePolynomialMain N +
      2 * (r / Real.log N) * barbanVehovLongCrossPolynomialMain p N +
      (r / Real.log N) ^ 2 * barbanVehovLongDerivativePolynomialMain p N) /
    Real.log N ^ 2

theorem tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one :
    Tendsto (fun N : ℕ =>
      barbanVehovLongBasePolynomialMain N / Real.log N ^ 2)
      atTop (𝓝 1) := by
  refine tendsto_barbanVehovSelbergDiagonal_div_log_one.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [barbanVehovLongBasePolynomialMain]
  field_simp [hlog]

theorem tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube
    (p : ℝ) :
    Tendsto (fun N : ℕ =>
      barbanVehovLongCrossPolynomialMain p N / Real.log N ^ 3)
      atTop (𝓝 (-(p + 1 / 2))) := by
  have hmixed := tendsto_barbanVehovSelbergMixedDiagonal_div_log_sq_one
  have hbase := tendsto_barbanVehovSelbergDiagonal_div_log_one
  have hlim := (hmixed.add (hbase.const_mul (p - 1 / 2))).neg
  have hfun : Tendsto (fun N : ℕ =>
      barbanVehovLongCrossPolynomialMain p N / Real.log N ^ 3)
      atTop (𝓝 (-(1 + (p - 1 / 2) * 1))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log N ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    change -(barbanVehovSelbergMixedDiagonal N / Real.log N ^ 2 +
        (p - 1 / 2) * (barbanVehovSelbergDiagonal N / Real.log N)) = _
    rw [barbanVehovLongCrossPolynomialMain]
    field_simp [hlog]
  convert hfun using 1
  ring

theorem tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four
    (p : ℝ) :
    Tendsto (fun N : ℕ =>
      barbanVehovLongDerivativePolynomialMain p N / Real.log N ^ 4)
      atTop (𝓝 (p ^ 2 + p + 2 / 3)) := by
  have hquad := tendsto_barbanVehovSelbergQuadraticLogDiagonal_div_log_cube_four_thirds
  have hmixed := tendsto_barbanVehovSelbergMixedDiagonal_div_log_sq_one
  have hbase := tendsto_barbanVehovSelbergDiagonal_div_log_one
  have hlim := (hquad.add (hmixed.const_mul (2 * p - 1))).add
    (hbase.const_mul (p ^ 2 - p + 1 / 3))
  have hfun : Tendsto (fun N : ℕ =>
      barbanVehovLongDerivativePolynomialMain p N / Real.log N ^ 4)
      atTop (𝓝 (4 / 3 + (2 * p - 1) * 1 +
        (p ^ 2 - p + 1 / 3) * 1)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log N ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    change barbanVehovSelbergQuadraticLogDiagonal N / Real.log N ^ 3 +
        (2 * p - 1) * (barbanVehovSelbergMixedDiagonal N / Real.log N ^ 2) +
        (p ^ 2 - p + 1 / 3) * (barbanVehovSelbergDiagonal N / Real.log N) = _
    rw [barbanVehovLongDerivativePolynomialMain]
    field_simp [hlog]
  convert hfun using 1
  norm_num
  ring

theorem tendsto_barbanVehovLongEnergyPolynomialMain
    (p r : ℝ) :
    Tendsto (fun N : ℕ => barbanVehovLongEnergyPolynomialMain p r N)
      atTop (𝓝 (1 - (2 * p + 1) * r + (p ^ 2 + p + 2 / 3) * r ^ 2)) := by
  have hbase := tendsto_barbanVehovLongBasePolynomialMain_div_log_sq_one
  have hcross := tendsto_barbanVehovLongCrossPolynomialMain_div_log_cube p
  have hderiv := tendsto_barbanVehovLongDerivativePolynomialMain_div_log_four p
  have hlim := (hbase.add (hcross.const_mul (2 * r))).add
    (hderiv.const_mul (r ^ 2))
  have hfun : Tendsto (fun N : ℕ =>
      barbanVehovLongEnergyPolynomialMain p r N) atTop
      (𝓝 (1 + 2 * r * (-(p + 1 / 2)) +
        r ^ 2 * (p ^ 2 + p + 2 / 3))) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log N ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hN)).ne'
    change barbanVehovLongBasePolynomialMain N / Real.log N ^ 2 +
        2 * r * (barbanVehovLongCrossPolynomialMain p N / Real.log N ^ 3) +
        r ^ 2 * (barbanVehovLongDerivativePolynomialMain p N / Real.log N ^ 4) = _
    rw [barbanVehovLongEnergyPolynomialMain]
    field_simp [hlog]
  convert hfun using 1
  ring

end

end RHTower.Sieve
