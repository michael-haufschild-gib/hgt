import GaloisForLFunctions.RHTower.DirichletHalfPlane

/-!
# The Dirichlet series of `log ζ` diverges on `Re s < 1`

`log ζ(s) = Σ_{n ≥ 2} (Λ(n)/log n) n^{-s}` on `Re s > 1`.  The coefficients are nonnegative, so
the abscissa of convergence equals the abscissa of absolute convergence, which is `1`.  Hence the
series converges at no point of `Re s < 1` (`not_dirichletConvergesAt_logZetaShiftedCoeff`): convergence at
`s` would propagate to the real point `σ = (Re s + 1)/2` (`tendsto_dirichlet_partialSum_of_re_lt`),
where the partial sums are nonnegative and bounded, so `Σ_p p^{-σ} ≥ Σ_p 1/p` would converge.

In particular no conditionally convergent Dirichlet-series representation of `log ζ` exists in the
strip, with or without RH: a convergent representation of `log ζ` on `½ < Re s < 1` must subtract
the pole, e.g. `Σ_{n ≤ x} Λ(n) n^{-s}/log n − ∫_2^x u^{-s}/log u du`.

The mechanism is general (`summable_of_dirichletConvergesAt_of_nonneg`): for nonnegative
coefficients, convergence at `s` gives absolute convergence at every real `σ > Re s`, so the abscissae
of convergence and of absolute convergence coincide.  The prime zeta series `Σ_p p^{-s}` therefore
also diverges at every `s` with `Re s < 1` (`not_dirichletConvergesAt_primeIndicator`).
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- The coefficients `Λ(n+1)/log(n+1)` of `log ζ`, indexed from `0`. -/
def logZetaShiftedCoeff (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt (n + 1) / Real.log ((n : ℝ) + 1) : ℝ) : ℂ)

theorem logZetaShiftedCoeff_nonneg (n : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt (n + 1) / Real.log ((n : ℝ) + 1) :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_nonneg (by linarith [n.cast_nonneg (α := ℝ)]))

/-- **No convergence left of `1`.**  The Dirichlet series `Σ Λ(n) n^{-s}/log n` of `log ζ` diverges
at every `s` with `Re s < 1`. -/
theorem not_dirichletConvergesAt_logZetaShiftedCoeff {s : ℂ} (hs : s.re < 1) :
    ¬ ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        logZetaShiftedCoeff n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L) := by
  intro hconv
  set σ : ℝ := (s.re + 1) / 2 with hσ
  have hσs : s.re < (σ : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have hσ1 : σ < 1 := by linarith
  obtain ⟨L, hL⟩ := tendsto_dirichlet_partialSum_of_re_lt hconv hσs
  set b : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt (n + 1) / Real.log ((n : ℝ) + 1) *
    ((n : ℝ) + 1) ^ (-σ) with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n =>
    mul_nonneg (logZetaShiftedCoeff_nonneg n) (Real.rpow_nonneg (by positivity) _)
  have hterm : ∀ n, logZetaShiftedCoeff n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) = ((b n : ℝ) : ℂ) := by
    intro n
    rw [hb, logZetaShiftedCoeff, Complex.ofReal_mul, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_neg]
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hL.cauchySeq.isBounded_range
  have hbs : Summable b := by
    refine summable_of_sum_range_le (c := C) hb0 fun N => ?_
    have h := hC _ (Set.mem_range_self N)
    simp only [hterm] at h
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] at h
    exact le_trans (le_abs_self _) h
  -- restrict to the primes
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    have hp := p.2.two_le
    have hq := q.2.two_le
    exact Subtype.ext (by simp only at hpq; omega)
  refine Nat.Primes.not_summable_one_div ((hbs.comp_injective hinj).of_nonneg_of_le
    (fun p => by positivity) fun p => ?_)
  have hp := p.2
  have hp2 := hp.two_le
  have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega)]; ring
  simp only [Function.comp_apply, hb, hcast, Nat.sub_add_cancel (by omega : 1 ≤ (p : ℕ))]
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp,
    div_self (Real.log_pos (by exact_mod_cast hp.one_lt)).ne', one_mul]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  calc 1 / (p : ℝ) = (p : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ (p : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)

/-- **Nonnegative coefficients: convergence is absolute to the right.**  If the Dirichlet series
with coefficients `a n ≥ 0` (at `n + 1`) converges at `s`, then `Σ a n (n+1)^{-σ}` is summable for
every real `σ > Re s`. -/
theorem summable_of_dirichletConvergesAt_of_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {s : ℂ}
    (hconv : ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        (a n : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L))
    {σ : ℝ} (hσ : s.re < σ) :
    Summable fun n => a n * ((n : ℝ) + 1) ^ (-σ) := by
  have hσs : s.re < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ
  obtain ⟨L, hL⟩ := tendsto_dirichlet_partialSum_of_re_lt hconv hσs
  have hterm : ∀ n, (a n : ℂ) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(σ : ℂ)) =
      ((a n * ((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity), Complex.ofReal_neg]
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hL.cauchySeq.isBounded_range
  refine summable_of_sum_range_le (c := C) (fun n => mul_nonneg (ha n)
    (Real.rpow_nonneg (by positivity) _)) fun N => ?_
  have h := hC _ (Set.mem_range_self N)
  simp only [hterm] at h
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] at h
  exact le_trans (le_abs_self _) h

/-- **The prime zeta series diverges on `Re s < 1`.**  `Σ_p p^{-s}` converges at no `s` with
`Re s < 1`, with or without RH. -/
theorem not_dirichletConvergesAt_primeIndicator {s : ℂ} (hs : s.re < 1) :
    ¬ ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N,
        ((if (n + 1).Prime then (1 : ℝ) else 0 : ℝ) : ℂ) *
          (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) atTop (𝓝 L) := by
  intro hconv
  set σ : ℝ := (s.re + 1) / 2 with hσ
  have hbs := summable_of_dirichletConvergesAt_of_nonneg
    (a := fun n => if (n + 1).Prime then (1 : ℝ) else 0)
    (fun n => by split_ifs <;> norm_num) hconv (σ := σ) (by rw [hσ]; linarith)
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ) - 1) := by
    intro p q hpq
    have hp := p.2.two_le
    have hq := q.2.two_le
    exact Subtype.ext (by simp only at hpq; omega)
  refine Nat.Primes.not_summable_one_div ((hbs.comp_injective hinj).of_nonneg_of_le
    (fun p => by positivity) fun p => ?_)
  have hp := p.2
  have hp2 := hp.two_le
  have hcast : (((p : ℕ) - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    rw [Nat.cast_sub (by omega)]; ring
  simp only [Function.comp_apply, hcast, Nat.sub_add_cancel (by omega : 1 ≤ (p : ℕ)), if_pos hp,
    one_mul]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  calc 1 / (p : ℝ) = (p : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ (p : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le hp1 (by rw [hσ]; linarith)

end GaloisForLFunctions.RHTower
