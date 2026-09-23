import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Even moments of the band trial weights

The weights `(1 - x²)^k` on `[-1, 1]` are the coefficients of the Kaiser–Bessel trial function of the
band concentration problem, and its finite-Fourier transform is assembled from the moments

```text
M(j, k) = ∫_(-1)^(1 : ℕ) x^(2j) (1 - x²)^k dx.
```

These moments have the closed form

```text
M(j, k) · j! · (2j + 2k + 2)! = (2j)! · k! · 4^(k+1) · (j + k + 1)!,
```

proved here with no Beta or Gamma function: the identity `(1-x²)^(k+1) = (1-x²)^k - x²(1-x²)^k` gives
the recursion `M(j, k+1) = M(j, k) - M(j+1, k)`, the base case is an elementary power integral, and the
induction step is the polynomial identity

```text
(2j+2k+4)(2j+2k+3) - 2(2j+1)(j+k+2) = 4(k+1)(j+k+2).
```

The multiplicative form of the statement keeps every step inside the factorials, so no division has to
be cleared.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral

/-- The even moment of the `k`-th trial weight on the band. -/
def trialMoment (j k : ℕ) : ℝ := ∫ x in (-1 : ℝ)..1, x ^ (2 * j) * (1 - x ^ 2) ^ k

theorem continuous_trialIntegrand (j k : ℕ) :
    Continuous fun x : ℝ => x ^ (2 * j) * (1 - x ^ 2) ^ k := by
  fun_prop

theorem intervalIntegrable_trialIntegrand (j k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ (2 * j) * (1 - x ^ 2) ^ k) volume (-1) 1 :=
  (continuous_trialIntegrand j k).intervalIntegrable _ _

/-- The moments of the trivial weight. -/
theorem trialMoment_zero (j : ℕ) : trialMoment j 0 = 2 / (2 * (j : ℝ) + 1) := by
  have h : trialMoment j 0 = ∫ x in (-1 : ℝ)..1, x ^ (2 * j) := by
    rw [trialMoment]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [pow_zero, mul_one]
  rw [h, integral_pow]
  have hodd : ((-1 : ℝ)) ^ (2 * j + 1) = -1 := by
    rw [pow_succ, pow_mul]
    simp
  rw [hodd, one_pow]
  push_cast
  ring

/-- **The recursion in the weight exponent.**  It comes from `(1-x²)^(k+1) = (1-x²)^k - x²(1-x²)^k`. -/
theorem trialMoment_succ (j k : ℕ) :
    trialMoment j (k + 1) = trialMoment j k - trialMoment (j + 1) k := by
  have hpt : ∀ x : ℝ, x ^ (2 * j) * (1 - x ^ 2) ^ (k + 1)
      = x ^ (2 * j) * (1 - x ^ 2) ^ k - x ^ (2 * (j + 1)) * (1 - x ^ 2) ^ k := by
    intro x
    have hj : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [hj, pow_succ, pow_add]
    ring
  rw [trialMoment, trialMoment, trialMoment]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_trialIntegrand j k)
    (intervalIntegrable_trialIntegrand (j + 1) k)]
  exact intervalIntegral.integral_congr fun x _ => hpt x

/-- **The closed form of the trial moments**, in multiplicative shape. -/
theorem trialMoment_mul_factorial (k : ℕ) : ∀ j : ℕ,
    trialMoment j k * ((Nat.factorial j : ℝ) * (Nat.factorial (2 * j + 2 * k + 2) : ℝ))
      = (Nat.factorial (2 * j) : ℝ) * (Nat.factorial k : ℝ) * 4 ^ (k + 1)
        * (Nat.factorial (j + k + 1) : ℝ) := by
  induction k with
  | zero =>
    intro j
    rw [trialMoment_zero]
    have h1 : 2 * j + 2 * 0 + 2 = 2 * j + 2 := by ring
    have h2 : j + 0 + 1 = j + 1 := by ring
    rw [h1, h2]
    have hfac : Nat.factorial (2 * j + 2) = (2 * j + 2) * ((2 * j + 1) * Nat.factorial (2 * j)) := by
      rw [Nat.factorial_succ (2 * j + 1)]
      have : 2 * j + 1 + 1 = 2 * j + 2 := by ring
      rw [this, Nat.factorial_succ (2 * j)]
    have hfacj : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    rw [hfac, hfacj]
    have hpos : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ k ih =>
    intro j
    have hrec := trialMoment_succ j k
    have hj := ih j
    have hj1 := ih (j + 1)
    -- expand the two factorials that grow
    have hfac1 : Nat.factorial (2 * j + 2 * (k + 1) + 2)
        = (2 * j + 2 * k + 4) * ((2 * j + 2 * k + 3) * Nat.factorial (2 * j + 2 * k + 2)) := by
      have e1 : 2 * j + 2 * (k + 1) + 2 = (2 * j + 2 * k + 3) + 1 := by ring
      have e2 : 2 * j + 2 * k + 3 = (2 * j + 2 * k + 2) + 1 := by ring
      rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
    have hfac2 : Nat.factorial (2 * (j + 1) + 2 * k + 2)
        = Nat.factorial (2 * j + 2 * k + 4) := by
      congr 1
      ring
    have hfac3 : Nat.factorial (2 * j + 2 * k + 4)
        = (2 * j + 2 * k + 4) * ((2 * j + 2 * k + 3) * Nat.factorial (2 * j + 2 * k + 2)) := hfac1
    have hfacj : Nat.factorial (j + 1) = (j + 1) * Nat.factorial j := Nat.factorial_succ j
    have hfac2j : Nat.factorial (2 * (j + 1)) = (2 * j + 2) * ((2 * j + 1) * Nat.factorial (2 * j)) := by
      have e1 : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ, Nat.factorial_succ]
    have hfack : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
    have hfacjk : Nat.factorial (j + (k + 1) + 1) = (j + k + 2) * Nat.factorial (j + k + 1) := by
      have e1 : j + (k + 1) + 1 = (j + k + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ]
    have hfacjk1 : Nat.factorial ((j + 1) + k + 1) = Nat.factorial (j + k + 2) := by
      congr 1
      ring
    have hfacjk2 : Nat.factorial (j + k + 2) = (j + k + 2) * Nat.factorial (j + k + 1) := by
      have e1 : j + k + 2 = (j + k + 1) + 1 := by ring
      rw [e1, Nat.factorial_succ]
    -- the positive factorial values
    have hjpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by
      exact_mod_cast Nat.factorial_pos j
    have hfpos : (0 : ℝ) < (Nat.factorial (2 * j + 2 * k + 2) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    rw [hrec]
    rw [hfac1, hfacjk, hfack]
    rw [hfac2, hfac3, hfacj, hfac2j, hfacjk1, hfacjk2] at hj1
    push_cast at hj hj1 ⊢
    have hjne : (Nat.factorial j : ℝ) ≠ 0 := ne_of_gt hjpos
    have hfne : (Nat.factorial (2 * j + 2 * k + 2) : ℝ) ≠ 0 := ne_of_gt hfpos
    field_simp at hj hj1 ⊢
    linear_combination ((2 * (j : ℝ) + 2 * (k : ℝ) + 4) * (2 * (j : ℝ) + 2 * (k : ℝ) + 3)) * hj - hj1

/-! ## The cosine transform of a trial weight -/

/-- The restricted band measure has total mass `2`. -/
theorem bandMeasure_univ :
    ((volume.restrict (Set.Ioc (-1 : ℝ) 1)) Set.univ).toReal = 2 := by
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem bandMeasure_real_univ :
    (volume.restrict (Set.Ioc (-1 : ℝ) 1)).real Set.univ = 2 := by
  show ((volume.restrict (Set.Ioc (-1 : ℝ) 1)) Set.univ).toReal = 2
  exact bandMeasure_univ

instance bandMeasure_isFinite : IsFiniteMeasure (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

/-- **The cosine transform of a trial weight is the moment series.**  Term-by-term integration of the
cosine series against the weight; the interchange is dominated by the exponential series. -/
theorem integral_trialWeight_cos (k : ℕ) (ω : ℝ) :
    (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ k * Real.cos (ω * x))
      = ∑' j : ℕ, (-1) ^ j * ω ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) * trialMoment j k := by
  have hle : (-1 : ℝ) ≤ 1 := by norm_num
  set F : ℕ → ℝ → ℝ := fun j x =>
    (1 - x ^ 2) ^ k * ((-1) ^ j * (ω * x) ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) with hF
  have hcont : ∀ j, Continuous (F j) := by
    intro j
    rw [hF]
    fun_prop
  have hint : ∀ j, Integrable (F j) (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := by
    intro j
    exact (hcont j).integrableOn_Ioc
  -- the pointwise bound on the band
  have hptbound : ∀ (j : ℕ), ∀ x ∈ Set.Ioc (-1 : ℝ) 1,
      ‖F j x‖ ≤ |ω| ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) := by
    intro j x hx
    have hx1 : |x| ≤ 1 := by
      rw [abs_le]
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hw : |1 - x ^ 2| ≤ 1 := by
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg x, sq_abs x, abs_le.mp hx1]
      · nlinarith [sq_nonneg x]
    have hfacpos : (0 : ℝ) < (Nat.factorial (2 * j) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have hnorm : ‖F j x‖
        = |1 - x ^ 2| ^ k * |ω| ^ (2 * j) * |x| ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) := by
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos hfacpos, mul_pow]
      ring
    rw [hnorm]
    have h1 : |1 - x ^ 2| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) hw
    have h2 : |x| ^ (2 * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx1
    have hnum : |1 - x ^ 2| ^ k * |ω| ^ (2 * j) * |x| ^ (2 * j) ≤ |ω| ^ (2 * j) := by
      calc |1 - x ^ 2| ^ k * |ω| ^ (2 * j) * |x| ^ (2 * j)
          ≤ 1 * |ω| ^ (2 * j) * 1 := by
            gcongr
        _ = |ω| ^ (2 * j) := by ring
    gcongr
  have hnormbound : ∀ j : ℕ,
      (∫ x, ‖F j x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
        ≤ 2 * (|ω| ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) := by
    intro j
    have hmono : (∫ x, ‖F j x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
        ≤ ∫ _x : ℝ, |ω| ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)
            ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => norm_nonneg _)
        (integrable_const _)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact hptbound j x hx)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const, smul_eq_mul, bandMeasure_real_univ]
  have hsummable : Summable fun j : ℕ =>
      (∫ x, ‖F j x‖ ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1))) := by
    have hbase : Summable fun j : ℕ => |ω| ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) := by
      have hinj : Function.Injective fun j : ℕ => 2 * j := fun a b hab => by
        have h2 : 2 * a = 2 * b := hab
        omega
      exact (Real.summable_pow_div_factorial |ω|).comp_injective hinj
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _)
      hnormbound (hbase.mul_left 2)
  have hkey := MeasureTheory.integral_tsum_of_summable_integral_norm hint hsummable
  -- the sum of the series is the weight times the cosine
  have hsumpt : ∀ x : ℝ, (∑' j : ℕ, F j x) = (1 - x ^ 2) ^ k * Real.cos (ω * x) := by
    intro x
    rw [hF]
    rw [tsum_mul_left, Real.cos_eq_tsum]
  -- each term integrates to the moment
  have hterm : ∀ j : ℕ, (∫ x, F j x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)))
      = (-1) ^ j * ω ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) * trialMoment j k := by
    intro j
    have hrew : ∀ x : ℝ, F j x
        = ((-1) ^ j * ω ^ (2 * j) / (Nat.factorial (2 * j) : ℝ)) *
          (x ^ (2 * j) * (1 - x ^ 2) ^ k) := by
      intro x
      simp only [hF, mul_pow]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrew),
      MeasureTheory.integral_const_mul, trialMoment,
      intervalIntegral.integral_of_le hle]
  rw [intervalIntegral.integral_of_le hle]
  rw [← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsumpt), ← hkey]
  exact tsum_congr hterm

/-! ## The Kaiser–Bessel coefficients -/

/-- The trial moments in divided form. -/
theorem trialMoment_eq (j k : ℕ) :
    trialMoment j k = (Nat.factorial (2 * j) : ℝ) * (Nat.factorial k : ℝ) * 4 ^ (k + 1)
        * (Nat.factorial (j + k + 1) : ℝ)
      / ((Nat.factorial j : ℝ) * (Nat.factorial (2 * j + 2 * k + 2) : ℝ)) := by
  have hjpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hfpos : (0 : ℝ) < (Nat.factorial (2 * j + 2 * k + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h := trialMoment_mul_factorial k j
  field_simp at h ⊢
  linarith [h]

/-- **The Kaiser–Bessel coefficient identity.**  The `(j, k)` term of the trial's cosine series is a
binomial coefficient over an odd factorial: exactly the `(j, k)` term of the binomial expansion of
`2 (c² - omega²)^(j+k)/(2(j+k)+1)!`. -/
theorem trialCoeff_eq (c ω : ℝ) (j k : ℕ) :
    (c ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2 *
        ((-1) ^ j * ω ^ (2 * j) / (Nat.factorial (2 * j) : ℝ) * trialMoment j k)
      = 2 * (Nat.choose (j + k) j : ℝ) * (c ^ 2) ^ k * (-(ω ^ 2)) ^ j
          / (Nat.factorial (2 * (j + k) + 1) : ℝ) := by
  have hjpos : (0 : ℝ) < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hkpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2jpos : (0 : ℝ) < (Nat.factorial (2 * j) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hoddpos : (0 : ℝ) < (Nat.factorial (2 * (j + k) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  -- the two factorial expansions
  have hchoose : (Nat.factorial (j + k) : ℝ)
      = (Nat.choose (j + k) j : ℝ) * (Nat.factorial j : ℝ) * (Nat.factorial k : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j k)
    have hsub : j + k - j = k := by omega
    rw [hsub] at h
    exact_mod_cast h.symm
  have hjk1 : (Nat.factorial (j + k + 1) : ℝ)
      = ((j : ℝ) + k + 1) * (Nat.factorial (j + k) : ℝ) := by
    have h : Nat.factorial (j + k + 1) = (j + k + 1) * Nat.factorial (j + k) :=
      Nat.factorial_succ (j + k)
    rw [h]
    push_cast
    ring
  have hbig : (Nat.factorial (2 * j + 2 * k + 2) : ℝ)
      = (2 * ((j : ℝ) + k + 1)) * (Nat.factorial (2 * (j + k) + 1) : ℝ) := by
    have e1 : 2 * j + 2 * k + 2 = (2 * (j + k) + 1) + 1 := by ring
    have h : Nat.factorial (2 * j + 2 * k + 2)
        = (2 * (j + k) + 1 + 1) * Nat.factorial (2 * (j + k) + 1) := by
      rw [e1, Nat.factorial_succ]
    rw [h]
    push_cast
    ring
  have hpow : ((-1 : ℝ)) ^ j * ω ^ (2 * j) = (-(ω ^ 2)) ^ j := by
    rw [pow_mul, show -(ω ^ 2) = (-1) * ω ^ 2 by ring, mul_pow]
  rw [trialMoment_eq, hjk1, hchoose, hbig, ← hpow, div_pow]
  have hjk1pos : (0 : ℝ) < (j : ℝ) + k + 1 := by positivity
  have h4 : ((4 : ℝ)) ^ k ≠ 0 := by positivity
  field_simp
  ring

/-- **The antidiagonal collapse.**  Summing the coefficient identity over `j + k = m` is the binomial
theorem for `(c² - omega²)^m`. -/
theorem antidiagonal_trialCoeff_sum (c ω : ℝ) (m : ℕ) :
    ∑ p ∈ Finset.antidiagonal m,
        2 * (Nat.choose m p.1 : ℝ) * (c ^ 2) ^ p.2 * (-(ω ^ 2)) ^ p.1
          / (Nat.factorial (2 * m + 1) : ℝ)
      = 2 * (c ^ 2 - ω ^ 2) ^ m / (Nat.factorial (2 * m + 1) : ℝ) := by
  have hbinom : (c ^ 2 - ω ^ 2) ^ m
      = ∑ i ∈ Finset.range (m + 1),
        (-(ω ^ 2)) ^ i * (c ^ 2) ^ (m - i) * (Nat.choose m i : ℝ) := by
    have h : (c : ℝ) ^ 2 - ω ^ 2 = (-(ω ^ 2)) + c ^ 2 := by ring
    rw [h, add_pow]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, hbinom, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end GaloisForLFunctions.RHTower

end
