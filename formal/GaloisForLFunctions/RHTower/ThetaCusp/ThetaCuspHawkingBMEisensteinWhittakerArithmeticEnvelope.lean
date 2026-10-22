import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBesselOrderExteriorEnvelope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinCuspExponentialJetTail
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower

/-!
# Arithmetic envelope for the completed Eisenstein Whittaker coefficient

At centered spectral parameter `u = s - 1/2`, the positive-index nonconstant coefficient of the
completed weight-zero Eisenstein series is

`a_u(n) = n^u * sum_{d|n} d^(-2u)`.

The corpus supplied exact norm formulas for positive-real complex powers and arbitrary-real
polynomial--exponential summability, but this actual coefficient had not been constructed or
admitted into the cusp-tail machinery.  Divisor positivity and `d <= n` give the unconditional
uniform estimate

`||a_u(n)|| <= n^(3 * |Re u| + 1)`.

Consequently every fixed differentiated arithmetic packet has the weighted summability needed by
the infinite cusp-tail theorem.  Together with the arbitrary-order Bessel exterior envelope this
is the arithmetic half of the actual weights `0,±4` Whittaker admission required to annihilate
the two balanced-spin Stokes defects.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [EISENSTEIN WHITTAKER ARITHMETIC]`
-/

open Complex Real Finset
open scoped BigOperators NNReal

namespace RHTower

noncomputable section

/-- Positive Fourier indices, excluding the Eisenstein constant term by construction. -/
abbrev D4BMPositiveIndex := {n : ℕ // 0 < n}

/-- Arithmetic coefficient of the nonconstant term of the completed weight-zero Eisenstein
series at centered parameter `u = s - 1/2`. -/
def d4BMCompletedEisensteinWhittakerCoefficient
    (u : ℂ) (n : D4BMPositiveIndex) : ℂ :=
  (n.1 : ℂ) ^ u * ∑ d ∈ n.1.divisors, (d : ℂ) ^ (-2 * u)

private theorem d4BM_norm_divisor_cpow_le
    (u : ℂ) (n : D4BMPositiveIndex) {d : ℕ} (hd : d ∈ n.1.divisors) :
    ‖(d : ℂ) ^ (-2 * u)‖ ≤ (n.1 : ℝ) ^ (2 * |u.re|) := by
  have hdvd : d ∣ n.1 := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd n.2
  have hdn : d ≤ n.1 := Nat.le_of_dvd n.2 hdvd
  rw [Complex.norm_natCast_cpow_of_pos hdpos]
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hnzero : (0 : ℝ) ≤ n.1 := by positivity
  calc
    (d : ℝ) ^ (-2 * u).re ≤ (d : ℝ) ^ (2 * |u.re|) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hdone
      · norm_num [mul_re]
        linarith [neg_le_abs u.re]
    _ ≤ (n.1 : ℝ) ^ (2 * |u.re|) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast hdn
      · positivity

/-- The actual completed Eisenstein arithmetic coefficient has a fixed polynomial envelope at
every spectral parameter. -/
theorem d4BM_norm_completedEisensteinWhittakerCoefficient_le
    (u : ℂ) (n : D4BMPositiveIndex) :
    ‖d4BMCompletedEisensteinWhittakerCoefficient u n‖ ≤
      (n.1 : ℝ) ^ (3 * |u.re| + 1) := by
  have hnOne : (1 : ℝ) ≤ n.1 := by exact_mod_cast n.2
  have hnPos : (0 : ℝ) < n.1 := by exact_mod_cast n.2
  rw [d4BMCompletedEisensteinWhittakerCoefficient, norm_mul,
    Complex.norm_natCast_cpow_of_pos n.2]
  calc
    (n.1 : ℝ) ^ u.re * ‖∑ d ∈ n.1.divisors, (d : ℂ) ^ (-2 * u)‖
        ≤ (n.1 : ℝ) ^ |u.re| *
            ∑ d ∈ n.1.divisors, (n.1 : ℝ) ^ (2 * |u.re|) := by
          apply mul_le_mul
          · exact Real.rpow_le_rpow_of_exponent_le hnOne (le_abs_self u.re)
          · exact norm_sum_le_of_le _ (fun d hd => d4BM_norm_divisor_cpow_le u n hd)
          · exact norm_nonneg _
          · positivity
    _ = (n.1 : ℝ) ^ |u.re| *
          ((n.1.divisors.card : ℝ) * (n.1 : ℝ) ^ (2 * |u.re|)) := by
          simp
    _ ≤ (n.1 : ℝ) ^ |u.re| *
          ((n.1 : ℝ) * (n.1 : ℝ) ^ (2 * |u.re|)) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n.1
    _ = (n.1 : ℝ) ^ (3 * |u.re| + 1) := by
          have hn_rpow_one : (n.1 : ℝ) = (n.1 : ℝ) ^ (1 : ℝ) := by simp
          conv_lhs =>
            rhs
            lhs
            rw [hn_rpow_one]
          rw [← Real.rpow_add hnPos, ← Real.rpow_add hnPos]
          congr 1
          ring

/-- The actual completed Eisenstein arithmetic coefficients satisfy the abstract exponential-jet
packet's summability certificate at every fixed derivative order. -/
theorem d4BM_completedEisensteinWhittakerCoefficient_weightedSummable
    (u : ℂ) (degree : ℕ) :
    Summable (fun N : ℕ =>
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
        (degree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ degree *
        Real.exp (-(((N : ℝ) + 1) / 2))) := by
  let r : ℝ := 3 * |u.re| + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hbase : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ)))) :=
    (summable_natSucc_rpow_exp_neg_and_tsum_le hr (by norm_num : (0 : ℝ) < 1 / 2)).1
  have hmajor : Summable (fun N : ℕ =>
      ((degree.factorial : ℝ) * (2 : ℝ) ^ degree) *
        (((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ))))) :=
    hbase.mul_left ((degree.factorial : ℝ) * (2 : ℝ) ^ degree)
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hmajor
  have hcoeff := d4BM_norm_completedEisensteinWhittakerCoefficient_le
    u ⟨N + 1, by omega⟩
  have hdenom : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hratio : 2 / ((N : ℝ) + 1) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hdenom]
    nlinarith
  have hpow : (2 / ((N : ℝ) + 1)) ^ degree ≤ (2 : ℝ) ^ degree := by
    gcongr
  have hexp : Real.exp (-(((N : ℝ) + 1) / 2)) ≤
      Real.exp (-((N : ℝ) * (1 / 2 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    ring_nf
    norm_num
  calc
    ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          (degree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ degree *
          Real.exp (-(((N : ℝ) + 1) / 2))
        ≤ (((N : ℝ) + 1) ^ r) * (degree.factorial : ℝ) *
          (2 : ℝ) ^ degree * Real.exp (-((N : ℝ) * (1 / 2 : ℝ))) := by
            gcongr
            simpa [r] using hcoeff
    _ = ((degree.factorial : ℝ) * (2 : ℝ) ^ degree) *
          (((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ)))) := by
            ring

/-- Actual arithmetic coefficients admitted as an infinite cusp exponential-jet packet. -/
def d4BMCompletedEisensteinArithmeticJetPacket
    (u : ℂ) (degree : ℕ) : D4BMCuspExponentialJetTailPacket where
  degree := degree
  coefficient := fun N =>
    d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩
  weightedNormSummable :=
    d4BM_completedEisensteinWhittakerCoefficient_weightedSummable u degree

end

end RHTower
