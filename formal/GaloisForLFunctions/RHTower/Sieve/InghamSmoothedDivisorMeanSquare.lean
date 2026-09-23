import GaloisForLFunctions.RHTower.Sieve.CriticalDivisorAffineMeanSquare
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangleSubpower
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Uniform mean square for Ingham's exponentially smoothed divisor carrier

Ramachandra's symmetric approximate functional equation for `ζ(1/2+it)²` naturally produces the
exponentially smoothed coefficients

`d(n)n⁻¹ᐟ² exp(-n/(2X))`.

This file proves bounds uniform in an arbitrary finite truncation.  The weighted coefficient mass
has exponent `201/200`; splitting the plain mass at the smoothing scale leaves only a logarithmic
head and an `X^(1/200)` tail.  The affine mean-square theorem then gives a carrier bound of order

`X^(201/200) + T ((1+log X)^(4 : ℕ) + X^(1/200))`.

At `X = T`, this has height exponent `201/200 = 1.005`, strictly inside Route T's certified
fourth-moment budget `101/100 = 1.01`.  Unlike a finite conductor-length estimate, uniformity in the
truncation controls the full exponential series after passage to a limit.
-/

open Complex MeasureTheory Set Finset

namespace RHTower.Sieve

noncomputable section

/-- Squared exponential weight of the Ramachandra divisor coefficient. -/
noncomputable def inghamSmoothedDivisorWeight (X n : ℕ) : ℝ :=
  Real.exp (-((n : ℝ) / (X : ℝ)))

/-- `n`-weighted mass of a finite smoothed critical divisor carrier. -/
noncomputable def inghamSmoothedDivisorWeightedMass (X M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n

/-- Plain mass of a finite smoothed critical divisor carrier. -/
noncomputable def inghamSmoothedDivisorPlainMass (X M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 M,
    ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) * inghamSmoothedDivisorWeight X n

theorem inghamSmoothedDivisorWeight_nonneg (X n : ℕ) :
    0 ≤ inghamSmoothedDivisorWeight X n := by
  unfold inghamSmoothedDivisorWeight
  positivity

/-- Uniform `X^(201/200)` bound for the weighted mass, independently of truncation. -/
theorem exists_inghamSmoothedDivisorWeightedMass_le :
    ∃ K : ℝ, 0 < K ∧ ∀ X M : ℕ, 1 ≤ X →
      inghamSmoothedDivisorWeightedMass X M ≤ K * (X : ℝ) ^ (201 / 200 : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ :=
    _root_.RHTower.card_divisors_le_const_mul_rpow (ε := (1 / 400 : ℝ)) (by norm_num)
  let A : ℝ := Real.exp 1 * 2 ^ (1 / 200 : ℝ) * Real.Gamma (201 / 200 : ℝ)
  refine ⟨C ^ 2 * (1 + A), by
    have hGamma : 0 < Real.Gamma (201 / 200 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num)
    dsimp [A]
    positivity, ?_⟩
  intro X M hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  let x : ℝ := 1 / (X : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxOne : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hXR).2 (by exact_mod_cast hX)
  let f : ℕ → ℝ := fun n =>
    ((n : ℝ) + 1) ^ (1 / 200 : ℝ) * Real.exp (-((n : ℝ) * x))
  have hmoment := _root_.RHTower.summable_natSucc_rpow_exp_neg_and_tsum_le
    (r := (1 / 200 : ℝ)) (x := x) (by norm_num) hx
  have hterm : ∀ n ∈ Finset.Icc 1 M,
      (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n ≤ C ^ 2 * f n := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hd := hdiv n hn1
    have hdsq : (n.divisors.card : ℝ) ^ 2 ≤
        C ^ 2 * (n : ℝ) ^ (1 / 200 : ℝ) := by
      calc
        (n.divisors.card : ℝ) ^ 2 ≤ (C * (n : ℝ) ^ (1 / 400 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hd 2
        _ = C ^ 2 * (n : ℝ) ^ (1 / 200 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 400 : ℝ)) 2,
            ← Real.rpow_mul hnR.le]
          congr 2
          norm_num
    have hpow : (n : ℝ) ^ (1 / 200 : ℝ) ≤
        ((n : ℝ) + 1) ^ (1 / 200 : ℝ) := by
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hweight : inghamSmoothedDivisorWeight X n =
        Real.exp (-((n : ℝ) * x)) := by
      unfold inghamSmoothedDivisorWeight
      dsimp [x]
      congr 1
      field_simp
    rw [hweight]
    calc
      (n.divisors.card : ℝ) ^ 2 * Real.exp (-((n : ℝ) * x)) ≤
          (C ^ 2 * (n : ℝ) ^ (1 / 200 : ℝ)) * Real.exp (-((n : ℝ) * x)) :=
        mul_le_mul_of_nonneg_right hdsq (Real.exp_pos _).le
      _ ≤ (C ^ 2 * ((n : ℝ) + 1) ^ (1 / 200 : ℝ)) *
          Real.exp (-((n : ℝ) * x)) := by
        gcongr
      _ = C ^ 2 * f n := by dsimp [f]; ring
  have hfinite : ∑ n ∈ Finset.Icc 1 M,
      (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n ≤
        C ^ 2 * ∑' n : ℕ, f n := by
    calc
      ∑ n ∈ Finset.Icc 1 M,
          (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n ≤
          ∑ n ∈ Finset.Icc 1 M, C ^ 2 * f n := Finset.sum_le_sum hterm
      _ ≤ ∑' n : ℕ, C ^ 2 * f n :=
        (hmoment.1.mul_left (C ^ 2)).sum_le_tsum _ (fun n _ => by
          dsimp [f]
          positivity)
      _ = C ^ 2 * ∑' n : ℕ, f n := by
        rw [hmoment.1.tsum_mul_left]
  have hInv : 1 / x = (X : ℝ) := by
    dsimp [x]
    field_simp
  have hmoment' : (∑' n : ℕ, f n) ≤
      1 + Real.exp x * 2 ^ (1 / 200 : ℝ) *
        (X : ℝ) ^ (201 / 200 : ℝ) * Real.Gamma (201 / 200 : ℝ) := by
    have hrat : (1 / 200 : ℝ) + 1 = 201 / 200 := by norm_num
    simpa only [f, hInv, hrat] using hmoment.2
  have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hxOne
  have hpowOne : 1 ≤ (X : ℝ) ^ (201 / 200 : ℝ) := by
    exact Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  have hGamma : 0 ≤ Real.Gamma (201 / 200 : ℝ) :=
    (Real.Gamma_pos_of_pos (by norm_num)).le
  have hcoarse : (∑' n : ℕ, f n) ≤
      (1 + A) * (X : ℝ) ^ (201 / 200 : ℝ) := by
    calc
      (∑' n : ℕ, f n) ≤
          1 + Real.exp x * 2 ^ (1 / 200 : ℝ) *
            (X : ℝ) ^ (201 / 200 : ℝ) * Real.Gamma (201 / 200 : ℝ) := hmoment'
      _ ≤ 1 + A * (X : ℝ) ^ (201 / 200 : ℝ) := by
        dsimp [A]
        have hfac : 0 ≤ 2 ^ (1 / 200 : ℝ) *
            (X : ℝ) ^ (201 / 200 : ℝ) * Real.Gamma (201 / 200 : ℝ) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hexp hfac]
      _ ≤ (1 + A) * (X : ℝ) ^ (201 / 200 : ℝ) := by
        have hA : 0 ≤ A := by dsimp [A]; positivity
        nlinarith
  unfold inghamSmoothedDivisorWeightedMass
  calc
    ∑ n ∈ Finset.Icc 1 M,
        (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n ≤
        C ^ 2 * ∑' n : ℕ, f n := hfinite
    _ ≤ C ^ 2 * ((1 + A) * (X : ℝ) ^ (201 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoarse (sq_nonneg C)
    _ = C ^ 2 * (1 + A) * (X : ℝ) ^ (201 / 200 : ℝ) := by ring

/-- Uniform plain mass bound.  Below the smoothing scale it is the exact logarithmic divisor
mass; above that scale one factor `1/n` converts the weighted `X^(201/200)` estimate into the
subpower tail `X^(1/200)`. -/
theorem exists_inghamSmoothedDivisorPlainMass_le :
    ∃ K : ℝ, 0 < K ∧ ∀ X M : ℕ, 1 ≤ X →
      inghamSmoothedDivisorPlainMass X M ≤
        (1 + Real.log X) ^ 4 + K * (X : ℝ) ^ (1 / 200 : ℝ) := by
  obtain ⟨K, hK, hweighted⟩ := exists_inghamSmoothedDivisorWeightedMass_le
  refine ⟨K, hK, ?_⟩
  intro X M hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  let s : Finset ℕ := Finset.Icc 1 M
  let q : ℕ → ℝ := fun n =>
    ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) * inghamSmoothedDivisorWeight X n
  let w : ℕ → ℝ := fun n =>
    (n.divisors.card : ℝ) ^ 2 * inghamSmoothedDivisorWeight X n
  have hhead : ∑ n ∈ s.filter (fun n => n ≤ X), q n ≤
      (1 + Real.log X) ^ 4 := by
    calc
      ∑ n ∈ s.filter (fun n => n ≤ X), q n ≤
          ∑ n ∈ s.filter (fun n => n ≤ X),
            (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnmem := (Finset.mem_filter.mp hn).1
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
        have hexp : inghamSmoothedDivisorWeight X n ≤ 1 := by
          unfold inghamSmoothedDivisorWeight
          rw [Real.exp_le_one_iff]
          exact neg_nonpos.mpr (div_nonneg (by positivity) hXR.le)
        dsimp [q]
        exact mul_le_of_le_one_right (by positivity) hexp
      _ ≤ ∑ n ∈ Finset.Icc 1 X,
          (n.divisors.card : ℝ) ^ 2 / (n : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hnmem, hnX⟩ := Finset.mem_filter.mp hn
          rw [Finset.mem_Icc]
          exact ⟨(Finset.mem_Icc.mp hnmem).1, hnX⟩
        · intro n _ _
          positivity
      _ ≤ (1 + Real.log X) ^ 4 :=
        sum_card_divisors_sq_div_le_polylog X hX
  have htail : ∑ n ∈ s.filter (fun n => ¬ n ≤ X), q n ≤
      K * (X : ℝ) ^ (1 / 200 : ℝ) := by
    have htailPoint : ∀ n ∈ s.filter (fun n => ¬ n ≤ X),
        q n ≤ (1 / (X : ℝ)) * w n := by
      intro n hn
      obtain ⟨hnmem, hnX⟩ := Finset.mem_filter.mp hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnmem).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
      have hXnR : (X : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hnX))
      have hinv : 1 / (n : ℝ) ≤ 1 / (X : ℝ) := one_div_le_one_div_of_le hXR hXnR
      dsimp [q, w]
      calc
        ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) *
            inghamSmoothedDivisorWeight X n =
            (1 / (n : ℝ)) * ((n.divisors.card : ℝ) ^ 2 *
              inghamSmoothedDivisorWeight X n) := by ring
        _ ≤ (1 / (X : ℝ)) * ((n.divisors.card : ℝ) ^ 2 *
              inghamSmoothedDivisorWeight X n) :=
          mul_le_mul_of_nonneg_right hinv
            (mul_nonneg (sq_nonneg _) (inghamSmoothedDivisorWeight_nonneg X n))
    have hsubset : s.filter (fun n => ¬ n ≤ X) ⊆ Finset.Icc 1 M := by
      exact fun _ hn => (Finset.mem_filter.mp hn).1
    have htailWeighted : ∑ n ∈ s.filter (fun n => ¬ n ≤ X), w n ≤
        inghamSmoothedDivisorWeightedMass X M := by
      unfold inghamSmoothedDivisorWeightedMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun n _ _ => by
        dsimp [w]
        exact mul_nonneg (sq_nonneg _) (inghamSmoothedDivisorWeight_nonneg X n))
    have hpow : (1 / (X : ℝ)) * (X : ℝ) ^ (201 / 200 : ℝ) =
        (X : ℝ) ^ (1 / 200 : ℝ) := by
      rw [one_div, ← Real.rpow_neg_one]
      rw [← Real.rpow_add hXR]
      congr 1
      norm_num
    calc
      ∑ n ∈ s.filter (fun n => ¬ n ≤ X), q n ≤
          ∑ n ∈ s.filter (fun n => ¬ n ≤ X), (1 / (X : ℝ)) * w n :=
        Finset.sum_le_sum htailPoint
      _ = (1 / (X : ℝ)) * ∑ n ∈ s.filter (fun n => ¬ n ≤ X), w n := by
        rw [Finset.mul_sum]
      _ ≤ (1 / (X : ℝ)) * inghamSmoothedDivisorWeightedMass X M :=
        mul_le_mul_of_nonneg_left htailWeighted (by positivity)
      _ ≤ (1 / (X : ℝ)) * (K * (X : ℝ) ^ (201 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hweighted X M hX) (by positivity)
      _ = K * ((1 / (X : ℝ)) * (X : ℝ) ^ (201 / 200 : ℝ)) := by ring
      _ = K * (X : ℝ) ^ (1 / 200 : ℝ) := by rw [hpow]
  unfold inghamSmoothedDivisorPlainMass
  change ∑ n ∈ s, q n ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ X) q]
  exact add_le_add hhead htail

/-- Critical-line coefficient `d(n)n⁻¹ᐟ² exp(-n/(2X))`, with arbitrary finite truncation. -/
noncomputable def inghamSmoothedCriticalDivisorSeq (X M n : ℕ) : ℂ :=
  if n ∈ Finset.Icc 1 M then
    (n.divisors.card : ℂ) *
      (((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      ((Real.exp (-((n : ℝ) / (2 * (X : ℝ)))) : ℝ) : ℂ)
  else 0

theorem inghamSmoothedCriticalDivisorSeq_support {X M n : ℕ}
    (h : inghamSmoothedCriticalDivisorSeq X M n ≠ 0) :
    n ∈ Finset.Icc 1 M := by
  by_contra hn
  simp [inghamSmoothedCriticalDivisorSeq, hn] at h

/-- Squaring the half-exponential coefficient produces the exact weight `exp(-n/X)`. -/
theorem inghamSmoothedCriticalDivisorSeq_norm_sq
    (X M n : ℕ) (hX : 1 ≤ X) (hn : n ∈ Finset.Icc 1 M) :
    ‖inghamSmoothedCriticalDivisorSeq X M n‖ ^ 2 =
      ((n.divisors.card : ℝ) ^ 2 / (n : ℝ)) * inghamSmoothedDivisorWeight X n := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  rw [inghamSmoothedCriticalDivisorSeq, if_pos hn, norm_mul, norm_mul,
    Complex.norm_natCast]
  have hamp : ‖(((n : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 =
      1 / (n : ℝ) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg _ _)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hnR.le]
    rw [show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -1 by norm_num]
    rw [Real.rpow_neg_one]
    exact inv_eq_one_div _
    all_goals positivity
  have hexp : ‖((Real.exp (-((n : ℝ) / (2 * (X : ℝ)))) : ℝ) : ℂ)‖ ^ 2 =
      inghamSmoothedDivisorWeight X n := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    rw [pow_two, ← Real.exp_add]
    unfold inghamSmoothedDivisorWeight
    congr 1
    field_simp
    ring
  rw [mul_pow, mul_pow, hamp, hexp]
  ring

theorem inghamSmoothedCriticalDivisorSeq_weighted_mass_eq
    (X M : ℕ) (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Icc 1 M,
      (n : ℝ) * ‖inghamSmoothedCriticalDivisorSeq X M n‖ ^ 2 =
        inghamSmoothedDivisorWeightedMass X M := by
  unfold inghamSmoothedDivisorWeightedMass
  apply Finset.sum_congr rfl
  intro n hn
  rw [inghamSmoothedCriticalDivisorSeq_norm_sq X M n hX hn]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
  field_simp

theorem inghamSmoothedCriticalDivisorSeq_plain_mass_eq
    (X M : ℕ) (hX : 1 ≤ X) :
    ∑ n ∈ Finset.Icc 1 M, ‖inghamSmoothedCriticalDivisorSeq X M n‖ ^ 2 =
      inghamSmoothedDivisorPlainMass X M := by
  unfold inghamSmoothedDivisorPlainMass
  exact Finset.sum_congr rfl fun n hn =>
    inghamSmoothedCriticalDivisorSeq_norm_sq X M n hX hn

/-- Finite truncation of the smoothed critical divisor series. -/
noncomputable def inghamSmoothedCriticalDivisorPolynomial (X M : ℕ) (t : ℝ) : ℂ :=
  LSeries (inghamSmoothedCriticalDivisorSeq X M)
    (((0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)

/-- **Uniform affine mean square for the Ramachandra carrier.**  Both constants are independent of
the truncation `M`; this is the form needed to pass to the full exponential series. -/
theorem exists_integral_Icc_normSq_inghamSmoothedCriticalDivisorPolynomial_le :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧
      ∀ X M : ℕ, 1 ≤ X → ∀ T : ℝ, 1 ≤ T →
        (∫ t in Set.Icc (-T) T,
          ‖inghamSmoothedCriticalDivisorPolynomial X M t‖ ^ 2) ≤
            5 * Real.pi * Real.exp 1 *
                (K₁ * (X : ℝ) ^ (201 / 200 : ℝ)) +
              (5 * Real.pi / 2) *
                ((1 + Real.log X) ^ 4 + K₂ * (X : ℝ) ^ (1 / 200 : ℝ)) * T := by
  obtain ⟨K₁, hK₁, hweighted⟩ := exists_inghamSmoothedDivisorWeightedMass_le
  obtain ⟨K₂, hK₂, hplain⟩ := exists_inghamSmoothedDivisorPlainMass_le
  refine ⟨K₁, K₂, hK₁, hK₂, ?_⟩
  intro X M hX T hT
  have hbase := integral_Icc_normSq_LSeries_le_general_affine
    (a := inghamSmoothedCriticalDivisorSeq X M) (s := Finset.Icc 1 M)
    (by simp) (fun _n hn => inghamSmoothedCriticalDivisorSeq_support hn) 0 hT
  have hconst : generalMeanSquareConst (inghamSmoothedCriticalDivisorSeq X M)
      (Finset.Icc 1 M) 0 ≤
        5 * Real.pi * Real.exp 1 *
          (K₁ * (X : ℝ) ^ (201 / 200 : ℝ)) := by
    rw [generalMeanSquareConst]
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    rw [inghamSmoothedCriticalDivisorSeq_weighted_mass_eq X M hX]
    exact mul_le_mul_of_nonneg_left (hweighted X M hX) (by positivity)
  have hrate : generalMeanSquareRate (inghamSmoothedCriticalDivisorSeq X M)
      (Finset.Icc 1 M) 0 ≤
        (5 * Real.pi / 2) *
          ((1 + Real.log X) ^ 4 + K₂ * (X : ℝ) ^ (1 / 200 : ℝ)) := by
    rw [generalMeanSquareRate]
    simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
    rw [inghamSmoothedCriticalDivisorSeq_plain_mass_eq X M hX]
    exact mul_le_mul_of_nonneg_left (hplain X M hX) (by positivity)
  unfold inghamSmoothedCriticalDivisorPolynomial
  exact hbase.trans (add_le_add hconst
    (mul_le_mul_of_nonneg_right hrate (by linarith)))

/-- Explicit absorption of the fourth logarithmic power into `X^(1/100)`. -/
theorem one_add_log_nat_pow_four_le_rpow_one_hundredth
    (X : ℕ) (hX : 1 ≤ X) :
    (1 + Real.log X) ^ 4 ≤
      (401 : ℝ) ^ 4 * (X : ℝ) ^ (1 / 100 : ℝ) := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXpowOne : 1 ≤ (X : ℝ) ^ (1 / 400 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  have hlog : Real.log (X : ℝ) ≤
      400 * (X : ℝ) ^ (1 / 400 : ℝ) := by
    have hraw := Real.log_le_rpow_div hXR.le (by norm_num : (0 : ℝ) < 1 / 400)
    calc
      Real.log (X : ℝ) ≤ (X : ℝ) ^ (1 / 400 : ℝ) / (1 / 400 : ℝ) := hraw
      _ = 400 * (X : ℝ) ^ (1 / 400 : ℝ) := by ring
  have hbase : 1 + Real.log (X : ℝ) ≤
      401 * (X : ℝ) ^ (1 / 400 : ℝ) := by nlinarith
  have hlogNonneg : 0 ≤ 1 + Real.log (X : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hX : (1 : ℝ) ≤ X)
    linarith
  have hpow := pow_le_pow_left₀ hlogNonneg hbase 4
  have hpowFour : ((X : ℝ) ^ (1 / 400 : ℝ)) ^ 4 =
      (X : ℝ) ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hXR.le]
    congr 1
    norm_num
  calc
    (1 + Real.log X) ^ 4 ≤
        (401 * (X : ℝ) ^ (1 / 400 : ℝ)) ^ 4 := hpow
    _ = (401 : ℝ) ^ 4 * (X : ℝ) ^ (1 / 100 : ℝ) := by
      rw [mul_pow, hpowFour]

/-- **Route-T admissible power form.**  At smoothing scale and height both `X`, every finite
Ramachandra carrier has second moment `O(X^(101/100))`, with one constant uniform in truncation.
The intrinsic carrier exponent is only `201/200`; the extra margin absorbs the logarithmic head. -/
theorem exists_integral_inghamSmoothedCriticalDivisorPolynomial_le_routeTBudget :
    ∃ C : ℝ, 0 < C ∧ ∀ X M : ℕ, 1 ≤ X →
      (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamSmoothedCriticalDivisorPolynomial X M t‖ ^ 2) ≤
          C * (X : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hmean⟩ :=
    exists_integral_Icc_normSq_inghamSmoothedCriticalDivisorPolynomial_le
  let C : ℝ :=
    5 * Real.pi * Real.exp 1 * K₁ +
      (5 * Real.pi / 2) * ((401 : ℝ) ^ 4 + K₂)
  refine ⟨C, by
    dsimp [C]
    positivity, ?_⟩
  intro X M hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hraw := hmean X M hX (X : ℝ) hXone
  have h201 : (X : ℝ) ^ (201 / 200 : ℝ) ≤
      (X : ℝ) ^ (101 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
  have h1 : (X : ℝ) ^ (1 / 200 : ℝ) ≤
      (X : ℝ) ^ (1 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hXone (by norm_num)
  have hlog := one_add_log_nat_pow_four_le_rpow_one_hundredth X hX
  have hbracket :
      (1 + Real.log X) ^ 4 + K₂ * (X : ℝ) ^ (1 / 200 : ℝ) ≤
        ((401 : ℝ) ^ 4 + K₂) * (X : ℝ) ^ (1 / 100 : ℝ) := by
    calc
      (1 + Real.log X) ^ 4 + K₂ * (X : ℝ) ^ (1 / 200 : ℝ) ≤
          (401 : ℝ) ^ 4 * (X : ℝ) ^ (1 / 100 : ℝ) +
            K₂ * (X : ℝ) ^ (1 / 100 : ℝ) :=
        add_le_add hlog (mul_le_mul_of_nonneg_left h1 hK₂.le)
      _ = ((401 : ℝ) ^ 4 + K₂) * (X : ℝ) ^ (1 / 100 : ℝ) := by ring
  have hmulPow : (X : ℝ) ^ (1 / 100 : ℝ) * (X : ℝ) =
      (X : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      (X : ℝ) ^ (1 / 100 : ℝ) * (X : ℝ) =
          (X : ℝ) ^ (1 / 100 : ℝ) * (X : ℝ) ^ (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one (X : ℝ)).symm
      _ = (X : ℝ) ^ ((1 / 100 : ℝ) + 1) :=
        (Real.rpow_add hXR _ _).symm
      _ = (X : ℝ) ^ (101 / 100 : ℝ) := by norm_num
  calc
    (∫ t in Set.Icc (-(X : ℝ)) (X : ℝ),
        ‖inghamSmoothedCriticalDivisorPolynomial X M t‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (K₁ * (X : ℝ) ^ (201 / 200 : ℝ)) +
          (5 * Real.pi / 2) *
            ((1 + Real.log X) ^ 4 + K₂ * (X : ℝ) ^ (1 / 200 : ℝ)) * (X : ℝ) := hraw
    _ ≤ 5 * Real.pi * Real.exp 1 *
            (K₁ * (X : ℝ) ^ (101 / 100 : ℝ)) +
          (5 * Real.pi / 2) *
            (((401 : ℝ) ^ 4 + K₂) * (X : ℝ) ^ (1 / 100 : ℝ)) * (X : ℝ) := by
      gcongr
    _ = C * (X : ℝ) ^ (101 / 100 : ℝ) := by
      dsimp [C]
      calc
        5 * Real.pi * Real.exp 1 * (K₁ * (X : ℝ) ^ (101 / 100 : ℝ)) +
              (5 * Real.pi / 2) *
                (((401 : ℝ) ^ 4 + K₂) * (X : ℝ) ^ (1 / 100 : ℝ)) * (X : ℝ) =
            5 * Real.pi * Real.exp 1 * K₁ * (X : ℝ) ^ (101 / 100 : ℝ) +
              (5 * Real.pi / 2) * ((401 : ℝ) ^ 4 + K₂) *
                ((X : ℝ) ^ (1 / 100 : ℝ) * (X : ℝ)) := by ring
        _ = 5 * Real.pi * Real.exp 1 * K₁ * (X : ℝ) ^ (101 / 100 : ℝ) +
              (5 * Real.pi / 2) * ((401 : ℝ) ^ 4 + K₂) *
                (X : ℝ) ^ (101 / 100 : ℝ) := by rw [hmulPow]
        _ = (5 * Real.pi * Real.exp 1 * K₁ +
              5 * Real.pi / 2 * ((401 : ℝ) ^ 4 + K₂)) *
                (X : ℝ) ^ (101 / 100 : ℝ) := by ring

end

end RHTower.Sieve
