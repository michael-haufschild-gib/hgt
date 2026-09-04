import Mathlib

/-!
# Flux-sector arithmetic and curvature closure

Odd fluxes split into the two residue classes `4k+1` and `4k+3`; on each class the quotient
`m(n^2-1)/8` has a polynomial formula.  Quadratic family binding then gives an exact three-versus-six
sector crossover law.  The FLRW Kretschmann bracket has its unique minimum at equation-of-state
parameter `-1/3`, and the closure-density substitution gives the exact curvature `12/ell^4`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Chiral family multiplicity determined by the two flux integers. -/
def familyCount (m n : ℕ) : ℕ := m * (n ^ 2 - 1) / 8

/-- Polynomial family count on the odd residue class `1 mod 4`. -/
theorem familyCount_four_mul_add_one (m k : ℕ) :
    familyCount m (4 * k + 1) = m * (k * (2 * k + 1)) := by
  unfold familyCount
  have h : (4 * k + 1) ^ 2 - 1 = 8 * (k * (2 * k + 1)) := by
    ring_nf
    omega
  rw [h]
  calc
    m * (8 * (k * (2 * k + 1))) / 8 = (m * (k * (2 * k + 1))) * 8 / 8 := by
      congr 1
      ring
    _ = m * (k * (2 * k + 1)) := Nat.mul_div_cancel _ (by norm_num)

/-- Polynomial family count on the odd residue class `3 mod 4`. -/
theorem familyCount_four_mul_add_three (m k : ℕ) :
    familyCount m (4 * k + 3) = m * ((k + 1) * (2 * k + 1)) := by
  unfold familyCount
  have h : (4 * k + 3) ^ 2 - 1 = 8 * ((k + 1) * (2 * k + 1)) := by
    ring_nf
    omega
  rw [h]
  calc
    m * (8 * ((k + 1) * (2 * k + 1))) / 8 =
        (m * ((k + 1) * (2 * k + 1))) * 8 / 8 := by
      congr 1
      ring
    _ = m * ((k + 1) * (2 * k + 1)) := Nat.mul_div_cancel _ (by norm_num)

/-- Flux `n=3` makes the first flux integer equal the family count. -/
theorem familyCount_three (m : ℕ) : familyCount m 3 = m := by
  simp [familyCount]

/-- Flux `n=5` triples the first flux integer. -/
theorem familyCount_five (m : ℕ) : familyCount m 5 = 3 * m := by
  unfold familyCount
  norm_num
  calc
    m * 24 / 8 = (3 * m) * 8 / 8 := by
      congr 1
      ring
    _ = 3 * m := Nat.mul_div_cancel _ (by norm_num)

/-- Baseline sector energy with quadratic family-dependent binding. -/
def familyWeightedEnergy (baseline family coupling : ℝ) : ℝ :=
  baseline - coupling * family ^ 2

/-- Exact coupling where three- and six-family sectors exchange order. -/
def threeSixCrossoverCoupling (threeBaseline sixBaseline : ℝ) : ℝ :=
  (sixBaseline - threeBaseline) / 27

/-- The two sector energies agree at the exact quadratic crossover. -/
theorem threeSixCrossover_equal_energy (threeBaseline sixBaseline : ℝ) :
    familyWeightedEnergy threeBaseline 3
        (threeSixCrossoverCoupling threeBaseline sixBaseline) =
      familyWeightedEnergy sixBaseline 6
        (threeSixCrossoverCoupling threeBaseline sixBaseline) := by
  unfold familyWeightedEnergy threeSixCrossoverCoupling
  ring

/-- Any positive margin below crossover favors the three-family sector. -/
theorem threeFamily_wins_below_crossover (threeBaseline sixBaseline margin : ℝ) :
    familyWeightedEnergy threeBaseline 3
        (threeSixCrossoverCoupling threeBaseline sixBaseline - Real.exp margin) <
      familyWeightedEnergy sixBaseline 6
        (threeSixCrossoverCoupling threeBaseline sixBaseline - Real.exp margin) := by
  unfold familyWeightedEnergy threeSixCrossoverCoupling
  nlinarith [Real.exp_pos margin]

/-- Any positive margin above crossover favors the six-family sector. -/
theorem sixFamily_wins_above_crossover (threeBaseline sixBaseline margin : ℝ) :
    familyWeightedEnergy sixBaseline 6
        (threeSixCrossoverCoupling threeBaseline sixBaseline + Real.exp margin) <
      familyWeightedEnergy threeBaseline 3
        (threeSixCrossoverCoupling threeBaseline sixBaseline + Real.exp margin) := by
  unfold familyWeightedEnergy threeSixCrossoverCoupling
  nlinarith [Real.exp_pos margin]

/-- Equation-of-state factor in the homogeneous FLRW Kretschmann scalar. -/
def flrwKretschmannBracket (w : ℝ) : ℝ := 4 + (1 + 3 * w) ^ 2

/-- The FLRW Kretschmann bracket is minimized at `w=-1/3`. -/
theorem flrwKretschmannBracket_minimum (w : ℝ) :
    flrwKretschmannBracket (-1 / 3) ≤ flrwKretschmannBracket w := by
  unfold flrwKretschmannBracket
  nlinarith [sq_nonneg (1 + 3 * w)]

/-- The minimizing equation of state is unique. -/
theorem flrwKretschmannBracket_eq_minimum_iff (w : ℝ) :
    flrwKretschmannBracket w = flrwKretschmannBracket (-1 / 3) ↔ w = -1 / 3 := by
  unfold flrwKretschmannBracket
  constructor <;> intro h
  · nlinarith [sq_nonneg (1 + 3 * w)]
  · rw [h]

/-- Kretschmann scalar with positive gravitational and density scales encoded logarithmically. -/
def flrwKretschmann (logG logRho w : ℝ) : ℝ :=
  (64 * Real.pi ^ 2 * Real.exp (2 * logG) * Real.exp (2 * logRho) / 3) *
    flrwKretschmannBracket w

/-- Multiplying by physical scales preserves the equation-of-state minimum. -/
theorem flrwKretschmann_minimum (logG logRho w : ℝ) :
    flrwKretschmann logG logRho (-1 / 3) ≤ flrwKretschmann logG logRho w := by
  unfold flrwKretschmann
  exact mul_le_mul_of_nonneg_left (flrwKretschmannBracket_minimum w) (by positivity)

/-- Density at which a homogeneous Hubble radius equals the cell scale. -/
def closureDensity (G c ell : ℝ) : ℝ := 3 * c ^ 2 / (8 * Real.pi * G * ell ^ 2)

/-- Minimum FLRW Kretschmann scalar at a fixed density. -/
def minimumKretschmannAtDensity (G c rho : ℝ) : ℝ :=
  256 * Real.pi ^ 2 * G ^ 2 * rho ^ 2 / (3 * c ^ 4)

/-- Closure-density substitution gives the exact curvature `12/ell^4`. -/
theorem closureKretschmann_eq (logG logC logEll : ℝ) :
    minimumKretschmannAtDensity (Real.exp logG) (Real.exp logC)
        (closureDensity (Real.exp logG) (Real.exp logC) (Real.exp logEll)) =
      12 / Real.exp logEll ^ 4 := by
  unfold minimumKretschmannAtDensity closureDensity
  field_simp [Real.exp_ne_zero, Real.pi_ne_zero]
  ring

end GaloisForLFunctions.HTGeometry
