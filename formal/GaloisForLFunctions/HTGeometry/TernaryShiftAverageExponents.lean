/-
Exponent arithmetic of a candidate shift-average bound for the ternary divisor correlation.

The chain of exponents below is the arithmetic skeleton of a route that expands the shift-average
`Σ_{h≤H} Δ₃(x,h)` by Voronoi summation twice, cancels the resonant half by antisymmetry, factors the
non-resonant half into the square of a one-variable divisor exponential sum, and estimates that sum
by splitting it at the wavelength of its phase.  Only the arithmetic is certified here; each analytic
input is named as a hypothesis of the corresponding theorem.

With `H = x^{1/3}`, the chain is

    Σ_B e(θ_B) δ₃(B)  ≪  N_B^{1/2} (Σ_B |δ₃(B)|²)^{1/2}  =  x^{1/3} · (x · L^{1/3})^{1/2}  =  x^{8/9},
    F                 ≪  x^{-1/3} · x^{8/9}                                             =  x^{5/9},
    E                 ≪  |F|²                                                            =  x^{10/9},
    Σ_{h≤H} Δ₃(x,h)   ≪  H^{1/2} x^{b}  with  1/6 + b = 10/9,  so  b = 17/18 < 1.

and the transfer converts `(a,b) = (1/2, 17/18)` into `m(3) ≤ 7/6`, below the envelope value `5/4`.
The same chain run at `k = 2` returns `m(2) = 1`, which is the correct known value.
-/
import GaloisForLFunctions.HTGeometry.ShiftAverageTransfer
import GaloisForLFunctions.HTGeometry.MomentChordPivot

namespace HTGeometry

/-- Shift length used in the sixth-moment application: `H = x^{1/3}`, in exponent form. -/
def shiftExponent : ℚ := 1/3

/-- Block length at which the dual phase `3x^{1/3}m^{1/3}` advances by one unit: `L = x^{1/3}`. -/
def blockExponent : ℚ := 1/3

/-- Number of blocks in `[x, 2x]`: `N_B = x/L`. -/
def blockCountExponent : ℚ := 1 - blockExponent

/-- Exponent of `Σ_B |δ₃(B)|² ≍ x · L^{1/3}`, from the short-interval mean square `x L^{4/3}` for
`Δ₃` divided by the block length. -/
def meanSquareExponent : ℚ := 1 + blockExponent / 3

/-- Cauchy–Schwarz output for the fluctuation sum `Σ_B e(θ_B) δ₃(B)`. -/
def fluctuationExponent : ℚ := blockCountExponent / 2 + meanSquareExponent / 2

theorem fluctuationExponent_eq : fluctuationExponent = 8/9 := by
  unfold fluctuationExponent blockCountExponent meanSquareExponent blockExponent
  norm_num

/-- Exponent of the one-variable divisor exponential sum `F` after removing the weight `m^{-1/3}`. -/
def dualSumExponent : ℚ := fluctuationExponent - 1/3

theorem dualSumExponent_eq : dualSumExponent = 5/9 := by
  unfold dualSumExponent; rw [fluctuationExponent_eq]; norm_num

/-- Exponent of `E = Σ_n d₃(n)[Δ₃(n+H) - Δ₃(n)]`, which the factorisation makes `|F|²`. -/
def shiftAverageExponent : ℚ := 2 * dualSumExponent

theorem shiftAverageExponent_eq : shiftAverageExponent = 10/9 := by
  unfold shiftAverageExponent; rw [dualSumExponent_eq]; norm_num

/-- The resulting `x`-exponent `b` in the input shape `Σ_{h≤H} Δ₃ ≪ H^{1/2} x^b`. -/
def candidateB : ℚ := shiftAverageExponent - shiftExponent / 2

theorem candidateB_eq : candidateB = 17/18 := by
  unfold candidateB shiftExponent; rw [shiftAverageExponent_eq]; norm_num

theorem candidateB_lt_one : candidateB < 1 := by
  rw [candidateB_eq]; norm_num

/-- **The transfer output of the candidate input.**  `(a,b) = (1/2, 17/18)` gives `m(3) ≤ 7/6`. -/
theorem candidate_transfer : transferBound 3 (1/2) (17/18) = 7/6 := by
  unfold transferBound
  rw [show (3 : ℝ) * ((1/2 : ℝ) + 17/18 - 1) / 2 - 1/2 = 1/6 by norm_num]
  rw [max_eq_right (by norm_num : (0:ℝ) ≤ 1/6)]
  norm_num

/-- …which is strictly below the known envelope value `momentChord 6 = 5/4`. -/
theorem candidate_beats_envelope : transferBound 3 (1/2) (17/18) < momentChord (2 * 3) := by
  rw [candidate_transfer]
  unfold momentChord
  norm_num

/-- **The same chain at `k = 2` returns the correct known value.**  There the block length is
`L = x^{1/2}`, the dual phase advances by one unit per step, and the chain yields
`Σ_{h≤H} Δ₂ ≪ H^{1/2} x^{5/6}`, whose transfer output is exactly `m(2) = 1`. -/
theorem binary_consistency : transferBound 2 (1/2) (5/6) = 1 := by
  unfold transferBound
  rw [show (2 : ℝ) * ((1/2 : ℝ) + 5/6 - 1) / 2 - 1/2 = -1/6 by norm_num]
  rw [max_eq_left (by norm_num : (-1/6 : ℝ) ≤ 0)]
  norm_num

/-- The chain run with a general short-interval mean square exponent `β`, i.e. with the input
`∫_X^{2X}(Δ₃(x+h) - Δ₃(x))² dx ≪ X^{1+ε} h^{β}` at `h ≍ X^{1/3}`.  The output is the `x`-exponent
`b` in `Σ_{h≤H} Δ₃ ≪ H^{1/2} x^{b}`.

`β = 2` is the trivial input; `β = 4/3` is the strongest known bound, which however holds only when
`σ(3) = 1/2`, i.e. only when `∫_0^T|ζ(1/2+it)|^(6 : ℕ) dt ≪ T^{1+ε}` — the sixth moment conjecture itself.
-/
def shortIntervalOutput (β : ℚ) : ℚ := 5/6 + (β - 1) / 3

/-- Trivial input returns `b = 7/6`, above the envelope's `b = 1`: nothing. -/
theorem shortIntervalOutput_trivial : shortIntervalOutput 2 = 7/6 := by
  unfold shortIntervalOutput; norm_num

/-- The conditional input `β = 4/3` returns the candidate `b = 17/18`. -/
theorem shortIntervalOutput_conditional : shortIntervalOutput (4/3) = 17/18 := by
  unfold shortIntervalOutput; norm_num

/-- **The threshold.**  The chain breaks the moment envelope exactly when `β < 3/2` — strictly
between the trivial exponent `2` and the Lindelöf-conditional exponent `4/3`. -/
theorem shortIntervalOutput_lt_one_iff {β : ℚ} : shortIntervalOutput β < 1 ↔ β < 3/2 := by
  unfold shortIntervalOutput
  constructor <;> intro h <;> linarith

/-- At the threshold the output is exactly the envelope value `b = 1`. -/
theorem shortIntervalOutput_threshold : shortIntervalOutput (3/2) = 1 := by
  unfold shortIntervalOutput; norm_num

/-- Ivić's estimate for the short-interval mean square is
`∫_X^{2X}(Δ_k(x+h)-Δ_k(x))²dx ≪ X^ε (h² X^{2σ-1} T₀^{m} + X³ T₀^{-2})`, where `σ` is any abscissa and
`m` the exponent in `∫_0^T|ζ(σ+it)|^{2k}dt ≪ T^{m+ε}`; he uses `m = 1`, which forces `σ = σ(k)`.
Optimising `T₀` and evaluating at `h = X^{1/3}` gives the exponent `(3m + 4σ - 2/3)/(m+2)`, and the
Voronoi chain breaks the moment envelope exactly when that is `< 3/2`, i.e. when

    m  <  chainRequirement σ  :=  22/9 - 8σ/3. -/
def chainRequirement (σ : ℚ) : ℚ := 22/9 - 8 * σ / 3

@[simp] theorem chainRequirement_half : chainRequirement (1/2) = 10/9 := by
  unfold chainRequirement; norm_num

@[simp] theorem chainRequirement_seven_twelfths : chainRequirement (7/12) = 8/9 := by
  unfold chainRequirement; norm_num

/-- Above `σ = 13/24` the requirement drops below `1`, which no moment exponent can meet. -/
theorem chainRequirement_lt_one_iff {σ : ℚ} : chainRequirement σ < 1 ↔ 13/24 < σ := by
  unfold chainRequirement
  constructor <;> intro h <;> linarith

/-- **The chain is circular at the critical line.**  At `σ = 1/2` the chain demands
`m(3) < 10/9` as input, while it delivers only `m(3) < 5/4` as output: the hypothesis is strictly
stronger than the conclusion. -/
theorem chain_input_stronger_than_output : chainRequirement (1/2) < 5/4 := by
  rw [chainRequirement_half]; norm_num

/-- The best known upper curve for the sixth-moment exponent on `[1/2, 7/12]`: the chord from
`(1/2, 5/4)` to `(7/12, 1)`, which convexity of the moment exponent makes an admissible bound. -/
def knownSixthMomentCurve (σ : ℚ) : ℚ := 5/4 - 3 * (σ - 1/2)

@[simp] theorem knownSixthMomentCurve_half : knownSixthMomentCurve (1/2) = 5/4 := by
  unfold knownSixthMomentCurve; norm_num

@[simp] theorem knownSixthMomentCurve_seven_twelfths : knownSixthMomentCurve (7/12) = 1 := by
  unfold knownSixthMomentCurve; norm_num

/-- **The chain fails at every abscissa.**  The known curve meets the requirement only for
`σ > 11/12`, far outside the admissible range `[1/2, 7/12]`.  So no choice of abscissa makes the
Voronoi chain improve the moment envelope from known inputs. -/
theorem knownCurve_meets_requirement_iff {σ : ℚ} :
    knownSixthMomentCurve σ < chainRequirement σ ↔ 11/12 < σ := by
  unfold knownSixthMomentCurve chainRequirement
  constructor <;> intro h <;> linarith

theorem chain_fails_on_admissible_range {σ : ℚ} (h2 : σ ≤ 7/12) :
    ¬ (knownSixthMomentCurve σ < chainRequirement σ) := by
  rw [knownCurve_meets_requirement_iff, not_lt]
  linarith

end HTGeometry
