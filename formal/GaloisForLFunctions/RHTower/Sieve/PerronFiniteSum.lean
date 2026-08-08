import GaloisForLFunctions.RHTower.Sieve.PerronLemma

/-!
# The truncated Perron formula for a finitely supported coefficient sequence

For a coefficient sequence supported on a finite set of positive integers, the partial sum below `x`
equals the truncated vertical integral of its Dirichlet polynomial against the kernel `x^s/s`, up to
the sum of the individual Perron errors:

`‖∑_{n < x} c_n − (1/2π)∫_{−T}^{T} D(σ+it)·x^{σ+it}/(σ+it) dt‖ ≤ ∑_n ‖c_n‖(x/n)^σ/(πT|log(x/n)|)`.

No interchange theorem is needed: the sum is finite, so the integral of the sum is the sum of the
integrals, and each term is Perron's lemma at `y = x/n`.  The error is a *global* sum over the
support, weighted by the reciprocal logarithmic distance of `n` from `x`; unlike a smoothing window
it involves no short-interval arithmetic, and unlike a smoothing kernel it costs no power of the
reciprocal window width.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set Filter Topology

/-- `(x/y)^w = x^w·y^{−w}` for positive reals, by multiplicativity of the complex power on the
nonnegative reals. -/
theorem ofReal_div_cpow_eq_mul_cpow_neg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℂ) :
    ((x / y : ℝ) : ℂ) ^ w = (x : ℂ) ^ w * (y : ℂ) ^ (-w) := by
  have hxy : (0 : ℝ) ≤ x / y := (div_pos hx hy).le
  have hmul := Complex.mul_cpow_ofReal_nonneg hxy hy.le w
  have hx' : ((x / y * y : ℝ) : ℂ) = ((x : ℝ) : ℂ) := by
    rw [div_mul_cancel₀ _ hy.ne']
  rw [← Complex.ofReal_mul, hx'] at hmul
  have hyne : ((y : ℝ) : ℂ) ^ w ≠ 0 := by
    refine Complex.cpow_ne_zero_iff.2 ?_
    exact Or.inl (by exact_mod_cast hy.ne')
  rw [Complex.cpow_neg, eq_comm, mul_inv_eq_iff_eq_mul₀ hyne, hmul]

/-- The Perron kernel of a single term is continuous on the line `Re s = σ > 0`. -/
theorem continuous_perronTerm {y : ℝ} (hy : 0 < y) {σ : ℝ} (hσ : 0 < σ) (a : ℂ) :
    Continuous (fun t : ℝ =>
      a * (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))) := by
  have hden : ∀ t : ℝ, ((σ : ℂ) + (t : ℝ) * I) ≠ 0 := by
    intro t h
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    exact absurd hre.symm (ne_of_gt hσ)
  refine continuous_const.mul (Continuous.div ?_ (by fun_prop) hden)
  refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
  exact_mod_cast hy.ne'

/-- The single-term Perron integral is the normalised kernel integral of `y = x/n`. -/
theorem integral_perronTerm_eq {y σ T : ℝ} (a : ℂ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (-T)..T, a * (((y : ℝ) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
      = a * perronVertical σ T y := by
  rw [intervalIntegral.integral_const_mul, perronVertical]
  ring

/-- **The truncated Perron formula.**  For `c` supported on a finite set of positive integers, none
of them equal to `x`, the partial sum below `x` is the truncated vertical integral of the Dirichlet
polynomial against `x^s/s`, with error the sum of the individual Perron errors. -/
theorem norm_sum_lt_sub_perron_integral_le {c : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    {x : ℝ} (hx : 0 < x) (hne : ∀ n ∈ s, (n : ℝ) ≠ x) {σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    ‖(∑ n ∈ Finset.filter (fun n : ℕ => ((n : ℝ) < x)) s, c n)
        - ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t in (-T)..T,
            (∑ n ∈ s, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
              * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      ≤ ∑ n ∈ s, ‖c n‖ * ((x / n) ^ σ / (Real.pi * T * |Real.log (x / n)|)) := by
  classical
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnpos : ∀ n ∈ s, (0 : ℝ) < (n : ℝ) := by
    intro n hn
    have : n ≠ 0 := fun h => hs0 (h ▸ hn)
    exact_mod_cast Nat.pos_of_ne_zero this
  -- the integrand is a finite sum of Perron terms
  have hpt : ∀ t : ℝ,
      (∑ n ∈ s, c n * ((n : ℂ) ^ (-((σ : ℂ) + (t : ℝ) * I))))
          * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))
        = ∑ n ∈ s, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
            / ((σ : ℂ) + (t : ℝ) * I)) := by
    intro t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ofReal_div_cpow_eq_mul_cpow_neg hx (hnpos n hn)]
    push_cast
    ring
  rw [intervalIntegral.integral_congr (g := fun t =>
      ∑ n ∈ s, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I)))
    (fun t _ => hpt t)]
  rw [intervalIntegral.integral_finsetSum (fun n hn =>
    (continuous_perronTerm (div_pos hx (hnpos n hn)) hσ (c n)).intervalIntegrable _ _)]
  rw [Finset.mul_sum]
  have hterm : ∀ n ∈ s,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t in (-T)..T, c n * ((((x / n : ℝ)) : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I)
            / ((σ : ℂ) + (t : ℝ) * I))
        = c n * perronVertical σ T (x / n) := fun n _ => integral_perronTerm_eq (c n)
  rw [Finset.sum_congr rfl hterm, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : (0 : ℝ) < (n : ℝ) := hnpos n hn
  have hxn : (0 : ℝ) < x / n := div_pos hx hn0
  by_cases hlt : (n : ℝ) < x
  · have hy1 : 1 < x / n := (one_lt_div hn0).2 hlt
    have hlogpos : (0 : ℝ) < Real.log (x / n) := Real.log_pos hy1
    rw [if_pos hlt]
    have hstep : ‖c n - c n * perronVertical σ T (x / n)‖
        = ‖c n‖ * ‖perronVertical σ T (x / n) - 1‖ := by
      rw [show c n - c n * perronVertical σ T (x / n)
          = -(c n * (perronVertical σ T (x / n) - 1)) by ring, norm_neg, norm_mul]
    rw [hstep, abs_of_pos hlogpos]
    exact mul_le_mul_of_nonneg_left (norm_perronVertical_sub_one_le hy1 hσ hT) (norm_nonneg _)
  · have hgt : x < (n : ℝ) := lt_of_le_of_ne (not_lt.1 hlt) (fun h => hne n hn h.symm)
    have hy1 : x / n < 1 := (div_lt_one hn0).2 hgt
    rw [if_neg hlt, zero_sub, norm_neg, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_perronVertical_le hxn hy1 hσ hT) (norm_nonneg _)

end RHTower.Sieve
end
