import GaloisForLFunctions.RHTower.PrimeArchBernsteinExponentialPhase

/-!
# Bernstein coefficient purity and its Loschmidt realization

The endpoint Bernstein order-unit criterion can be rewritten without absolute values or negative
parts. The squared `l2` norm of the coefficient vector has the same exponential rate as its `l1`
norm because the vector has only `n + 1` coordinates. This positive quadratic observable is also
the exact long-time mean-square of a finite Loschmidt amplitude with distinct algebraic unit
phases.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Squared `l2` norm of one Bernstein coefficient vector. -/
def bernsteinCoefficientPurity (m : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (bernsteinCoefficient m n i) ^ 2

theorem bernsteinCoefficientPurity_nonneg (m : ℕ → ℝ) (n : ℕ) :
    0 ≤ bernsteinCoefficientPurity m n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The coefficient purity is bounded above by the square of total variation. -/
theorem bernsteinCoefficientPurity_le_l1_sq (m : ℕ → ℝ) (n : ℕ) :
    bernsteinCoefficientPurity m n ≤ (bernsteinCoefficientL1 m n) ^ 2 := by
  rw [bernsteinCoefficientPurity, bernsteinCoefficientL1]
  calc
    (∑ i ∈ Finset.range (n + 1), (bernsteinCoefficient m n i) ^ 2) =
        ∑ i ∈ Finset.range (n + 1), |bernsteinCoefficient m n i| ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sq_abs _).symm
    _ ≤ (∑ i ∈ Finset.range (n + 1), |bernsteinCoefficient m n i|) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => abs_nonneg _

/-- Cauchy--Schwarz bounds the total-variation square by dimension times purity. -/
theorem bernsteinCoefficientL1_sq_le_card_mul_purity (m : ℕ → ℝ) (n : ℕ) :
    (bernsteinCoefficientL1 m n) ^ 2 ≤
      (n + 1 : ℝ) * bernsteinCoefficientPurity m n := by
  rw [bernsteinCoefficientPurity, bernsteinCoefficientL1]
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (n + 1))
    (f := fun i => |bernsteinCoefficient m n i|)
  simpa [sq_abs] using h

/-- Zero exponential rate for a nonnegative quadratic-energy sequence. -/
def SubexponentialSquareEnergyAtNatInfinity (E : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 1 < r → Tendsto (fun n : ℕ => E n / r ^ n) atTop (nhds 0)

/-- Finite-dimensional `l1` and squared-`l2` norms have exactly the same exponential phase when
the dimension grows only linearly. -/
theorem subexponentialSquareEnergy_iff_l1 (m : ℕ → ℝ) :
    SubexponentialSquareEnergyAtNatInfinity (bernsteinCoefficientPurity m) ↔
      SubexponentialAtNatInfinity (bernsteinCoefficientL1 m) := by
  constructor
  · intro hE r hr
    have hpoly : Tendsto (fun n : ℕ => (n + 1 : ℝ) / r ^ n) atTop (nhds 0) := by
      have hn := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
      have hone : Tendsto (fun n : ℕ => 1 / r ^ n) atTop (nhds 0) := by
        have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
          (inv_nonneg.mpr (zero_le_one.trans hr.le))
          (inv_lt_one_of_one_lt₀ hr)
        simpa [div_eq_mul_inv, inv_pow] using hp
      simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_div, zero_add] using hn.add hone
    have henergy := hE r hr
    have havg : Tendsto
        (fun n : ℕ => ((n + 1 : ℝ) / r ^ n +
          bernsteinCoefficientPurity m n / r ^ n) / 2)
        atTop (nhds 0) := by
      convert (hpoly.add henergy).div_const 2 using 1
      · norm_num
    apply squeeze_zero
      (fun n => div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (pow_nonneg (zero_le_one.trans hr.le) _))
      (fun n => ?_) havg
    have hL1nonneg : 0 ≤ bernsteinCoefficientL1 m n :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hPnonneg := bernsteinCoefficientPurity_nonneg m n
    have hsq := bernsteinCoefficientL1_sq_le_card_mul_purity m n
    have hAM : bernsteinCoefficientL1 m n ≤
        ((n + 1 : ℝ) + bernsteinCoefficientPurity m n) / 2 := by
      nlinarith [sq_nonneg ((n + 1 : ℝ) - bernsteinCoefficientPurity m n)]
    have hrpow : 0 ≤ r ^ n := pow_nonneg (zero_le_one.trans hr.le) n
    calc
      bernsteinCoefficientL1 m n / r ^ n ≤
          (((n + 1 : ℝ) + bernsteinCoefficientPurity m n) / 2) / r ^ n :=
        div_le_div_of_nonneg_right hAM hrpow
      _ = ((n + 1 : ℝ) / r ^ n +
          bernsteinCoefficientPurity m n / r ^ n) / 2 := by ring
  · intro hL1 r hr
    let q : ℝ := Real.sqrt r
    have hq : 1 < q := by
      have hsq : q ^ 2 = r := Real.sq_sqrt (zero_le_one.trans hr.le)
      nlinarith [Real.sqrt_nonneg r]
    have hbase := hL1 q hq
    have hsqT : Tendsto
        (fun n : ℕ => (bernsteinCoefficientL1 m n / q ^ n) ^ 2)
        atTop (nhds 0) := by
      simpa using hbase.pow 2
    apply squeeze_zero
      (fun n => div_nonneg (bernsteinCoefficientPurity_nonneg m n)
        (pow_nonneg (zero_le_one.trans hr.le) _))
      (fun n => ?_) hsqT
    have hle := bernsteinCoefficientPurity_le_l1_sq m n
    calc
      bernsteinCoefficientPurity m n / r ^ n ≤
          (bernsteinCoefficientL1 m n) ^ 2 / r ^ n :=
        div_le_div_of_nonneg_right hle (pow_nonneg (zero_le_one.trans hr.le) _)
      _ = (bernsteinCoefficientL1 m n / q ^ n) ^ 2 := by
        have hden : r ^ n = (q ^ n) ^ 2 := by
          calc
            r ^ n = (q ^ 2) ^ n := by rw [show q ^ 2 = r by
              exact Real.sq_sqrt (zero_le_one.trans hr.le)]
            _ = q ^ (2 * n) := (pow_mul q 2 n).symm
            _ = q ^ (n * 2) := by congr 1; omega
            _ = (q ^ n) ^ 2 := pow_mul q n 2
        rw [div_pow, hden]

/-- Algebraic unit phases used to dephase a finite coefficient vector. -/
def natCayleyPhase (n : ℕ) : ℂ :=
  (1 + Complex.I * (n : ℂ)) / (1 - Complex.I * (n : ℂ))

private lemma natCayleyPhase_den_ne (n : ℕ) :
    (1 - Complex.I * (n : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem natCayleyPhase_norm (n : ℕ) : ‖natCayleyPhase n‖ = 1 := by
  rw [natCayleyPhase, norm_div]
  have hnorm : ‖(1 : ℂ) + Complex.I * (n : ℂ)‖ =
      ‖(1 : ℂ) - Complex.I * (n : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [hnorm]
  exact div_self (norm_ne_zero_iff.mpr (natCayleyPhase_den_ne n))

theorem natCayleyPhase_injective : Function.Injective natCayleyPhase := by
  intro n m h
  rw [natCayleyPhase, natCayleyPhase] at h
  have hcross :
      ((1 : ℂ) + Complex.I * (n : ℂ)) * (1 - Complex.I * (m : ℂ)) =
        ((1 : ℂ) + Complex.I * (m : ℂ)) * (1 - Complex.I * (n : ℂ)) :=
    (div_eq_div_iff (natCayleyPhase_den_ne n) (natCayleyPhase_den_ne m)).mp h
  have him := congrArg Complex.im hcross
  norm_num at him
  have hnm : (n : ℝ) = (m : ℝ) := by linarith
  exact_mod_cast hnm

/-- Finite Loschmidt amplitude of one Bernstein coefficient vector. -/
def bernsteinCoefficientLoschmidtAmplitude (m : ℕ → ℝ) (M n : ℕ) : ℂ :=
  finiteExponentialPencil (Finset.range (M + 1))
    (fun i => (bernsteinCoefficient m M i : ℂ)) natCayleyPhase n

/-- Exact dephasing law: the long-time mean-square Loschmidt amplitude is the coefficient
purity. -/
theorem tendsto_bernsteinCoefficientLoschmidtAmplitude_cesaro_norm_sq
    (m : ℕ → ℝ) (M : ℕ) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖bernsteinCoefficientLoschmidtAmplitude m M n‖ ^ 2)
      atTop (nhds (bernsteinCoefficientPurity m M)) := by
  have h := tendsto_finiteExponentialPencil_cesaro_norm_sq
    (Finset.range (M + 1))
    (fun i => (bernsteinCoefficient m M i : ℂ)) natCayleyPhase
    (fun i _ => natCayleyPhase_norm i)
    natCayleyPhase_injective.injOn
  simpa only [bernsteinCoefficientLoschmidtAmplitude, bernsteinCoefficientPurity,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- Endpoint coefficient purity of the completed prime--Gamma source. -/
def primeArchEndpointBernsteinPurity (n : ℕ) : ℝ :=
  bernsteinCoefficientPurity
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n

/-- Endpoint Loschmidt amplitude of the completed prime--Gamma Bernstein source. -/
def primeArchEndpointBernsteinLoschmidtAmplitude (M n : ℕ) : ℂ :=
  bernsteinCoefficientLoschmidtAmplitude
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) M n

theorem tendsto_primeArchEndpointBernsteinLoschmidtAmplitude_cesaro_norm_sq (M : ℕ) :
    Tendsto
      (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖primeArchEndpointBernsteinLoschmidtAmplitude M n‖ ^ 2)
      atTop (nhds (primeArchEndpointBernsteinPurity M)) := by
  simpa only [primeArchEndpointBernsteinLoschmidtAmplitude,
    primeArchEndpointBernsteinPurity] using
    tendsto_bernsteinCoefficientLoschmidtAmplitude_cesaro_norm_sq
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) M

/-- **Loschmidt-purity RH law.** RH is equivalent to zero exponential rate of one positive
coefficient-purity sequence, which is itself the exact long-time mean square of a finite
Loschmidt amplitude at every degree. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential :
    RiemannHypothesis ↔
      SubexponentialSquareEnergyAtNatInfinity primeArchEndpointBernsteinPurity := by
  change RiemannHypothesis ↔
    SubexponentialSquareEnergyAtNatInfinity
      (bernsteinCoefficientPurity
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment))
  exact riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential.trans
    (subexponentialSquareEnergy_iff_l1
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment)).symm

end

end RHTower
