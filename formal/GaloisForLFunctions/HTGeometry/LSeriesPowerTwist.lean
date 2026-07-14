import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Power twists and finite-prefix peeling for Dirichlet series

This module packages two reusable operations on `LSeries` coefficients:

* multiplication by `n ^ a`, which translates the series argument by `a`;
* deletion of a finite coefficient prefix, after which mathlib's first-coefficient asymptotic
  extracts the next coefficient exactly.

The second operation is the formal dominated-convergence engine behind all-index Dirichlet
coefficient tomography.  Keeping it generic avoids repeating analytic tail estimates in each
arithmetic application.
-/

namespace GaloisForLFunctions

open Complex Filter Topology LSeries

noncomputable section

/-- Twist Dirichlet coefficients by the complex power `n ^ a`. -/
def lseriesPowerTwistCoeff (f : ℕ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  f n * (n : ℂ) ^ a

/-- The `LSeries` term of a power-twisted coefficient sequence is the untwisted term at the
translated argument. -/
theorem lseriesPowerTwist_term (f : ℕ → ℂ) (a s : ℂ) (n : ℕ) :
    LSeries.term (lseriesPowerTwistCoeff f a) s n = LSeries.term f (s - a) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [lseriesPowerTwistCoeff]
    rw [Complex.cpow_sub _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

/-- Multiplication of coefficients by `n ^ a` translates the `LSeries` argument by `a`. -/
theorem LSeries_powerTwist (f : ℕ → ℂ) (a s : ℂ) :
    LSeries (lseriesPowerTwistCoeff f a) s = LSeries f (s - a) :=
  tsum_congr (lseriesPowerTwist_term f a s)

/-- Absolute convergence transfers across the same coefficient power twist. -/
theorem LSeriesSummable_powerTwist (f : ℕ → ℂ) (a s : ℂ) :
    LSeriesSummable (lseriesPowerTwistCoeff f a) s ↔ LSeriesSummable f (s - a) :=
  summable_congr (lseriesPowerTwist_term f a s)

/-- Delete all coefficients through index `n`. -/
def lseriesPeeledCoeff (f : ℕ → ℂ) (n m : ℕ) : ℂ :=
  if m ≤ n then 0 else f m

@[simp]
theorem lseriesPeeledCoeff_eq_zero (f : ℕ → ℂ) (n : ℕ) {m : ℕ} (hm : m ≤ n) :
    lseriesPeeledCoeff f n m = 0 := by
  simp [lseriesPeeledCoeff, hm]

@[simp]
theorem lseriesPeeledCoeff_succ (f : ℕ → ℂ) (n : ℕ) :
    lseriesPeeledCoeff f n (n + 1) = f (n + 1) := by
  simp [lseriesPeeledCoeff]

/-- Deleting finitely many coefficients preserves convergence at every point where the original
series converges. -/
theorem LSeriesSummable.peeled {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (n : ℕ) :
    LSeriesSummable (lseriesPeeledCoeff f n) s := by
  change Summable (LSeries.term (lseriesPeeledCoeff f n) s)
  have hi := hf.indicator {m : ℕ | n < m}
  refine hi.congr (fun m => ?_)
  by_cases hm : m ≤ n
  · simp [LSeries.term, lseriesPeeledCoeff, hm, not_lt_of_ge hm]
  · have hnm : n < m := Nat.lt_of_not_ge hm
    by_cases hm0 : m = 0
    · omega
    · simp [LSeries.term_of_ne_zero hm0, lseriesPeeledCoeff, hm, hnm]

/-- The peeled series is the original series minus its finite coefficient prefix. -/
theorem LSeries_peeled_eq_sub_sum {f : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (n : ℕ) :
    LSeries (lseriesPeeledCoeff f n) s =
      LSeries f s - ∑ m ∈ Finset.range (n + 1), LSeries.term f s m := by
  have hsplit := hf.sum_add_tsum_subtype_compl (Finset.range (n + 1))
  have heq : LSeries (lseriesPeeledCoeff f n) s =
      ∑' m : {m : ℕ // m ∉ Finset.range (n + 1)}, LSeries.term f s m := by
    rw [LSeries]
    calc
      (∑' m, LSeries.term (lseriesPeeledCoeff f n) s m) =
          ∑' m, {m : ℕ | m ∉ Finset.range (n + 1)}.indicator (LSeries.term f s) m := by
        apply tsum_congr
        intro m
        by_cases hm : m ≤ n
        · simp [Set.indicator, lseriesPeeledCoeff, hm, LSeries.term]
        · by_cases hm0 : m = 0
          · omega
          · simp [Set.indicator, lseriesPeeledCoeff, hm, LSeries.term_of_ne_zero hm0]
      _ = ∑' m : {m : ℕ // m ∉ Finset.range (n + 1)}, LSeries.term f s m :=
        (tsum_subtype {m : ℕ | m ∉ Finset.range (n + 1)} (LSeries.term f s)).symm
  rw [heq, LSeries]
  exact (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hsplit)

/-- Finite-prefix deletion preserves a finite absolute-convergence abscissa. -/
theorem lseriesPeeledCoeff_abscissa_lt_top {f : ℕ → ℂ}
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (n : ℕ) :
    LSeries.abscissaOfAbsConv (lseriesPeeledCoeff f n) < ⊤ := by
  obtain ⟨y, hfy, hyt⟩ := exists_between hf
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hfy).ne'⟩
  have hs : LSeriesSummable f (y : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hfy)
  exact (LSeriesSummable.peeled hs n).abscissaOfAbsConv_le.trans_lt (by simp)

/-- Arbitrary coefficient extraction after deleting a finite prefix.  This is the reusable
all-index coefficient-peeling law: `(n+1)^x` times the peeled series tends to coefficient `n+1` as
`x` tends to positive infinity. -/
theorem tendsto_cpow_mul_LSeries_peeled {f : ℕ → ℂ} (n : ℕ)
    (hf : LSeries.abscissaOfAbsConv f < ⊤) :
    Tendsto
      (fun x : ℝ => ((n + 1 : ℕ) : ℂ) ^ (x : ℂ) *
        LSeries (lseriesPeeledCoeff f n) (x : ℂ))
      atTop (nhds (f (n + 1))) := by
  simpa using LSeries.tendsto_cpow_mul_atTop
    (f := lseriesPeeledCoeff f n) (n := n)
    (fun m hm => lseriesPeeledCoeff_eq_zero f n hm)
    (lseriesPeeledCoeff_abscissa_lt_top hf n)

end

end GaloisForLFunctions
