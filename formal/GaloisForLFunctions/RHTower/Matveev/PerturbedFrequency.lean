import GaloisForLFunctions.RHTower.Matveev.SmallForm

/-!
# The perturbed frequency identity and integral frequency values

The exact normalization of a vanishing relation rewrites the pivot logarithm in terms of the
others.  For a *small* form the same rewriting is available with no denominators at all: multiplying
a frequency by the pivot coefficient produces integer direction coefficients together with the
single explicit error `m_pivot · Λ`.  This is the perturbation the effective construction has to
carry, and it is exact — no estimate is involved.

At a nonnegative integer sample the exponential of a frequency is an `S`-unit: a product of prime
powers, hence a positive rational integer.  Together these two facts are what make the rational
prime case of Baker's method arithmetically elementary at the terminal step, where a nonzero
rational integer is at least one in absolute value.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

variable {d : ℕ}

/-! ## The perturbed normalization with integer coefficients -/

/-- The integer direction coefficients of the perturbed normalization. -/
def perturbedDirection (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) (i : Fin d) : ℤ :=
  b pivot * m i - m pivot * b i

theorem perturbedDirection_pivot (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) :
    perturbedDirection b pivot m pivot = 0 := by
  rw [perturbedDirection]
  ring

/-- **The perturbed frequency identity.**  Multiplying a frequency by the pivot coefficient
rewrites it in the non-pivot directions with integer coefficients, plus the explicit error
`m_pivot · Λ`.  With a vanishing form this is the classical exact normalization. -/
theorem pivot_mul_primeLogForm (p : Fin d → ℕ) (b : Fin d → ℤ) (pivot : Fin d) (m : Fin d → ℤ) :
    (b pivot : ℝ) * primeLogForm p m
      = (∑ i ∈ Finset.univ.erase pivot,
          (perturbedDirection b pivot m i : ℝ) * Real.log (p i))
        + (m pivot : ℝ) * primeLogForm p b := by
  have hsplit : ∀ f : Fin d → ℝ,
      ∑ i, f i = (∑ i ∈ Finset.univ.erase pivot, f i) + f pivot := fun f =>
    (Finset.sum_erase_add _ _ (Finset.mem_univ pivot)).symm
  rw [primeLogForm, primeLogForm, hsplit (fun i => (m i : ℝ) * Real.log (p i)),
    hsplit (fun i => (b i : ℝ) * Real.log (p i))]
  have hterm : ∀ i ∈ Finset.univ.erase pivot,
      (perturbedDirection b pivot m i : ℝ) * Real.log (p i)
        = (b pivot : ℝ) * ((m i : ℝ) * Real.log (p i))
          - (m pivot : ℝ) * ((b i : ℝ) * Real.log (p i)) := by
    intro i _
    rw [perturbedDirection]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-! ## Integral values of the frequency exponential -/

/-- The `S`-unit value of a nonnegative frequency at a nonnegative integer sample. -/
def freqUnit (p : Fin d → ℕ) (m : Fin d → ℕ) (s : ℕ) : ℕ := ∏ i, p i ^ (s * m i)

theorem freqUnit_pos (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime) (m : Fin d → ℕ) (s : ℕ) :
    0 < freqUnit p m s :=
  Finset.prod_pos fun i _ => pow_pos (hprime i).pos _

/-- **The exponential of an integral frequency is an `S`-unit.** -/
theorem exp_nsmul_primeLogForm (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime)
    (m : Fin d → ℕ) (s : ℕ) :
    Real.exp ((s : ℝ) * primeLogForm p (fun i => (m i : ℤ))) = (freqUnit p m s : ℝ) := by
  have hpos : ∀ i : Fin d, (0 : ℝ) < (p i : ℝ) := fun i => by
    exact_mod_cast (hprime i).pos
  have hlog : (s : ℝ) * primeLogForm p (fun i => (m i : ℤ))
      = Real.log ((freqUnit p m s : ℕ) : ℝ) := by
    rw [freqUnit]
    push_cast
    rw [Real.log_prod]
    · rw [primeLogForm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.log_pow]
      push_cast
      ring
    · intro i _
      have : (0 : ℝ) < (p i : ℝ) ^ (s * m i) := pow_pos (hpos i) _
      exact this.ne'
  rw [hlog, Real.exp_log]
  exact_mod_cast freqUnit_pos p hprime m s

/-! ## Size of a frequency -/

/-- The uniform bound for a frequency of an exponent box of width `L`. -/
theorem abs_primeLogForm_le_of_box (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime)
    {L : ℕ} {m : Fin d → ℕ} (hm : ∀ i, m i ≤ L) :
    |primeLogForm p (fun i => (m i : ℤ))| ≤ (L : ℝ) * ∑ i, Real.log (p i) := by
  have hlogpos : ∀ i : Fin d, 0 ≤ Real.log (p i) := fun i =>
    Real.log_nonneg (by exact_mod_cast (hprime i).one_lt.le)
  have hnn : 0 ≤ primeLogForm p (fun i => (m i : ℤ)) := by
    rw [primeLogForm]
    refine Finset.sum_nonneg fun i _ => ?_
    have : (0 : ℝ) ≤ ((m i : ℤ) : ℝ) := by positivity
    exact mul_nonneg this (hlogpos i)
  rw [abs_of_nonneg hnn, primeLogForm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (hlogpos i)
  exact_mod_cast hm i

end GaloisForLFunctions.RHTower.Matveev
