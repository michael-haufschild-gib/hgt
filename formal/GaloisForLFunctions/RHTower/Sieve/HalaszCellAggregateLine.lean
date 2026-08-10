import GaloisForLFunctions.RHTower.Sieve.HalaszCellAggregate
import GaloisForLFunctions.RHTower.Sieve.PerronTripleRegrouped

/-!
# The cell aggregate on the Perron line

The cell decomposition, transported from Gallagher's frequency variable to the Perron variable.  A
shift of the Perron frequency twists the coefficients of a Dirichlet series by `n^{-iv}`, which is
unimodular, so the mean square is the same on every unit cell of the line:

```text
∫_{v−1/2}^{v+1/2} ‖L(a, σ+iy)‖² dy ≤ 2π · (prime cell mass) ,
```

and therefore, for any continuous nonnegative envelope `E`,

```text
∫_b^{b+m} E(y)·‖L(a, σ+iy)‖² dy ≤ (∑_{k<m} E(v_k)) · 2π · (prime cell mass) .
```

With `E(y) = ‖L(f, σ+iy)‖²·x^{2σ}/‖σ+iy‖²` this is the second Cauchy–Schwarz factor of the
regrouped triple bound, and the aggregate `∑_k E(v_k)` is the quantity that replaces the long
factor's global supremum.
-/

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset GaloisForLFunctions.HTGeometry

/-- **Shifting the Perron frequency twists the coefficients by `n^{-iv}`.** -/
theorem LSeries_line_shift (a : ℕ → ℂ) (σ v y : ℝ) :
    LSeries a ((σ : ℂ) + ((v + y : ℝ) : ℂ) * I)
      = LSeries (fun n => a n * ((n : ℂ) ^ (-((v : ℂ) * I)))) ((σ : ℂ) + (y : ℝ) * I) := by
  rw [LSeries, LSeries]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : ((n : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hsplit : ((σ : ℂ) + ((v + y : ℝ) : ℂ) * I)
        = ((σ : ℂ) + (y : ℝ) * I) + (v : ℂ) * I := by
      push_cast
      ring
    rw [hsplit, Complex.cpow_add _ _ hn0, Complex.cpow_neg, div_eq_mul_inv, div_eq_mul_inv,
      mul_inv]
    ring

/-- The twist is unimodular. -/
theorem norm_twist_cpow {n : ℕ} (hn : n ≠ 0) (a : ℂ) (v : ℝ) :
    ‖a * ((n : ℂ) ^ (-((v : ℂ) * I)))‖ = ‖a‖ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  rw [norm_mul, show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp

/-- **The mean square on one unit cell of the Perron line.** -/
theorem integral_Icc_normSq_LSeries_cell_le_prime {a : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s) (σ v : ℝ) :
    (∫ y in Set.Icc (v - 1 / 2) (v + 1 / 2), ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 2 * Real.pi * primeCellMass (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun n => a n * ((n : ℂ) ^ (-((v : ℂ) * I))) with hbdef
  have hbsupp : ∀ n : ℕ, b n ≠ 0 → n ∈ s := by
    intro n hne
    refine hsupp n ?_
    intro h
    rw [hbdef] at hne
    simp only [h, zero_mul, ne_eq, not_true_eq_false] at hne
  -- move the cell to the origin
  have hle : v - 1 / 2 ≤ v + 1 / 2 := by linarith
  have hle' : (-(1 / 2) : ℝ) ≤ 1 / 2 := by norm_num
  have hconv : (∫ y in Set.Icc (v - 1 / 2) (v + 1 / 2), ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      = ∫ y in (v - 1 / 2)..(v + 1 / 2), ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hshift : (∫ y in (-(1 / 2) : ℝ)..(1 / 2), ‖LSeries a ((σ : ℂ) + ((v + y : ℝ) : ℂ) * I)‖ ^ 2)
      = ∫ y in (v - 1 / 2)..(v + 1 / 2), ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_add_left
      (a := (-(1 / 2) : ℝ)) (b := (1 / 2 : ℝ))
      (fun y : ℝ => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) v
    rw [show v + (-(1 / 2) : ℝ) = v - 1 / 2 by ring] at h
    exact h
  have hcongr : (∫ y in (-(1 / 2) : ℝ)..(1 / 2),
        ‖LSeries a ((σ : ℂ) + ((v + y : ℝ) : ℂ) * I)‖ ^ 2)
      = ∫ y in (-(1 / 2) : ℝ)..(1 / 2), ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [LSeries_line_shift a σ v y]
  have hback : (∫ y in (-(1 / 2) : ℝ)..(1 / 2), ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      = ∫ y in Set.Icc (-(1 / 2) : ℝ) (1 / 2), ‖LSeries b ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hle', MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- the centred cell, through Gallagher's variable
  have hW : 2 * Real.pi * 1 * ((1 / 2 : ℝ) / (2 * Real.pi)) ≤ 1 := by
    field_simp
    norm_num
  have heq := integral_Icc_normSq_LSeries_eq (a := b) hs0 hbsupp σ (T := (1 / 2 : ℝ)) (by norm_num)
  have hpoly := integral_Icc_normSq_logPoly_le_prime_sharp
    (fun n => b n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s hs hW
  -- the twist does not change the coefficient sizes
  have hmass : primeCellMass (fun n => b n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s
      = primeCellMass (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s := by
    rw [primeCellMass, primeCellMass]
    refine congrArg _ (Finset.sum_congr rfl fun q hq => ?_)
    have hq0 : q ≠ 0 := fun h => hs0 (h ▸ hq)
    rw [hbdef]
    simp only
    congr 2
    rw [show a q * ((q : ℂ) ^ (-((v : ℂ) * I))) * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)
        = (a q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)) * ((q : ℂ) ^ (-((v : ℂ) * I))) by ring,
      norm_twist_cpow hq0]
  rw [hconv, ← hshift, hcongr, hback, heq, ← hmass, primeCellMass]
  have hbound : (∫ w in Set.Icc (-((1 / 2 : ℝ) / (2 * Real.pi))) ((1 / 2 : ℝ) / (2 * Real.pi)),
        ‖logPoly (fun n => b n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s w‖ ^ 2)
      ≤ 5 / 4 * ∑ q ∈ s, (700 * ((q : ℝ) / Real.log q) + 1)
          * ‖b q * ((((q : ℝ) ^ (-σ) : ℝ)) : ℂ)‖ ^ 2 := hpoly
  have hπ2 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  exact mul_le_mul_of_nonneg_left hbound hπ2

/-- **The envelope enters as an aggregate over unit cells of the Perron line.** -/
theorem exists_cell_aggregate_normSq_LSeries_le {a : ℕ → ℂ} {s : Finset ℕ}
    (hs : ∀ m ∈ s, m.Prime) (hs0 : 0 ∉ s) (hsupp : ∀ n : ℕ, a n ≠ 0 → n ∈ s)
    {E : ℝ → ℝ} (hE : Continuous E) (hE0 : ∀ t, 0 ≤ E t) (σ b : ℝ) (m : ℕ) :
    ∃ v : ℕ → ℝ,
      (∀ k, k < m → v k ∈ Set.Icc (b + (k : ℝ) * 1) (b + ((k : ℝ) + 1) * 1))
      ∧ (∫ y in b..(b + (m : ℝ) * 1), E y * ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
          ≤ (∑ k ∈ Finset.range m, E (v k))
            * (2 * Real.pi * primeCellMass (fun n => a n * ((((n : ℝ) ^ (-σ) : ℝ)) : ℂ)) s) := by
  have hH : Continuous fun y : ℝ => ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 :=
    ((continuous_LSeries_line_of_support hs0 hsupp σ).norm).pow 2
  have hH0 : ∀ y : ℝ, 0 ≤ ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2 := fun y => by positivity
  obtain ⟨v, hvmem, hvle⟩ := exists_cell_max_mul_integral_le hE hH hH0 b 1 one_pos m
  refine ⟨v, hvmem, le_trans hvle ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (hE0 (v k))
  have hlecell : (b + (k : ℝ) + 1 / 2) - 1 / 2 ≤ (b + (k : ℝ) + 1 / 2) + 1 / 2 := by linarith
  rw [show b + (k : ℝ) * 1 = (b + (k : ℝ) + 1 / 2) - 1 / 2 by ring,
    show b + ((k : ℝ) + 1) * 1 = (b + (k : ℝ) + 1 / 2) + 1 / 2 by ring,
    intervalIntegral.integral_of_le hlecell, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact integral_Icc_normSq_LSeries_cell_le_prime hs hs0 hsupp σ (b + (k : ℝ) + 1 / 2)

end RHTower.Sieve

end
