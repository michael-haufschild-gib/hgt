import GaloisForLFunctions.HTGeometry.RisingFactorialTelescope

/-!
# The first expansion step for a polygamma jet

The polygamma series `∑_n (s+n)^{-(m+2)}` and the factorial series
`∑_n 1/((s+n)⋯(s+n+m+1))` have the same leading behaviour: termwise their difference is one order
smaller, because `x(x+1)⋯(x+m+1)` differs from `x^{m+2}` by a polynomial of one lower degree.  The
factorial series sums in closed form, so a polygamma jet equals an explicit reciprocal rising
factorial up to an error one order better than the jet itself:

`ψ^{(m+1)}(s) = (−1)^m (m+1)!/((m+1)·s(s+1)⋯(s+m)) + O(t^{-(m+2)})`

on a vertical line.  This is the quantitative form of the leading asymptotic, and the first step of
the expansion to arbitrary depth.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ t : ℝ}

/-- Shifting right by a natural number does not decrease the modulus, in the right half plane. -/
theorem norm_le_norm_add_nat {x : ℂ} (hx : 0 < x.re) (j : ℕ) : ‖x‖ ≤ ‖x + (j : ℂ)‖ := by
  have hre : (x + (j : ℂ)).re = x.re + (j : ℝ) := by simp
  have him : (x + (j : ℂ)).im = x.im := by simp
  have hsq : ‖x‖ ^ 2 ≤ ‖x + (j : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hre, him]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖x + (j : ℂ)‖ := norm_nonneg _
  nlinarith

/-- The modulus of a rising factorial dominates the corresponding power of the modulus. -/
theorem norm_pow_le_norm_risingProd {x : ℂ} (hx : 0 < x.re) (m : ℕ) :
    ‖x‖ ^ m ≤ ‖risingProd x m‖ := by
  rw [risingProd, norm_prod]
  have hprod : ∏ _j ∈ Finset.range m, ‖x‖ = ‖x‖ ^ m := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← hprod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => norm_le_norm_add_nat hx j)

/-- The rising factorial differs from the pure power by one degree: the leading terms cancel. -/
theorem exists_norm_risingProd_sub_pow_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 1 ≤ ‖x‖ →
      ‖risingProd x (m + 1) - x ^ (m + 1)‖ ≤ C * ‖x‖ ^ m := by
  induction m with
  | zero =>
    refine ⟨0, le_refl 0, fun x _ => ?_⟩
    have h1 : risingProd x 1 = x := by
      rw [risingProd_succ, risingProd_zero]
      simp
    rw [h1]
    simp
  | succ m ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨C * (2 + m) + (m + 1), by positivity, fun x hx => ?_⟩
    have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
    have hsplit : risingProd x (m + 2) - x ^ (m + 2)
        = (risingProd x (m + 1) - x ^ (m + 1)) * (x + ((m : ℂ) + 1))
          + x ^ (m + 1) * ((m : ℂ) + 1) := by
      have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
      have hstep : risingProd x (m + 1 + 1) = risingProd x (m + 1) * (x + ((m + 1 : ℕ) : ℂ)) :=
        risingProd_succ x (m + 1)
      rw [show m + 2 = m + 1 + 1 from rfl, hstep, hcast]
      ring
    have hxm : ‖x + ((m : ℂ) + 1)‖ ≤ (2 + m) * ‖x‖ := by
      have h1 : ‖x + ((m : ℂ) + 1)‖ ≤ ‖x‖ + ((m : ℝ) + 1) := by
        refine le_trans (norm_add_le _ _) ?_
        have h2 : ‖((m : ℂ) + 1)‖ ≤ (m : ℝ) + 1 := by
          refine le_trans (norm_add_le _ _) ?_
          simp
        linarith
      have h3 : (m : ℝ) + 1 ≤ ((m : ℝ) + 1) * ‖x‖ :=
        le_mul_of_one_le_right (by positivity) hx
      nlinarith
    have hnorm1 : ‖((m : ℂ) + 1)‖ ≤ (m : ℝ) + 1 := by
      refine le_trans (norm_add_le _ _) ?_
      simp
    calc ‖risingProd x (m + 2) - x ^ (m + 2)‖
        ≤ ‖(risingProd x (m + 1) - x ^ (m + 1)) * (x + ((m : ℂ) + 1))‖
          + ‖x ^ (m + 1) * ((m : ℂ) + 1)‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ (C * ‖x‖ ^ m) * ((2 + m) * ‖x‖) + ‖x‖ ^ (m + 1) * ((m : ℝ) + 1) := by
          rw [norm_mul, norm_mul, norm_pow]
          refine add_le_add (mul_le_mul (hbound x hx) hxm (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left hnorm1 (by positivity))
      _ = (C * (2 + m) + (m + 1)) * ‖x‖ ^ (m + 1) := by rw [pow_succ]; ring

/-- **The termwise comparison.**  The reciprocal power and the reciprocal rising factorial of the
same length differ by one order. -/
theorem exists_norm_inv_pow_sub_inv_risingProd_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 < x.re → 1 ≤ ‖x‖ →
      ‖(x ^ (m + 2))⁻¹ - (risingProd x (m + 2))⁻¹‖ ≤ C * (‖x‖⁻¹ ^ (m + 3)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_risingProd_sub_pow_le (m + 1)
  refine ⟨C, hC, fun x hx hx1 => ?_⟩
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le zero_lt_one hx1
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hxpos
    simp at hxpos
  have hR : risingProd x (m + 2) ≠ 0 := risingProd_ne_zero hx (m + 2)
  have hpow : (x ^ (m + 2)) ≠ 0 := pow_ne_zero _ hxne
  have hdiff : (x ^ (m + 2))⁻¹ - (risingProd x (m + 2))⁻¹
      = (risingProd x (m + 2) - x ^ (m + 2)) / (x ^ (m + 2) * risingProd x (m + 2)) := by
    field_simp
  rw [hdiff, norm_div, norm_mul, norm_pow]
  have hnum : ‖risingProd x (m + 2) - x ^ (m + 2)‖ ≤ C * ‖x‖ ^ (m + 1) := hbound x hx1
  have hden : ‖x‖ ^ (m + 2) * ‖x‖ ^ (m + 2) ≤ ‖x‖ ^ (m + 2) * ‖risingProd x (m + 2)‖ :=
    mul_le_mul_of_nonneg_left (norm_pow_le_norm_risingProd hx (m + 2)) (by positivity)
  have hdenpos : (0 : ℝ) < ‖x‖ ^ (m + 2) * ‖risingProd x (m + 2)‖ := by
    have : (0 : ℝ) < ‖risingProd x (m + 2)‖ :=
      lt_of_lt_of_le (by positivity) (norm_pow_le_norm_risingProd hx (m + 2))
    positivity
  rw [div_le_iff₀ hdenpos]
  have hgoal : C * ‖x‖⁻¹ ^ (m + 3) * (‖x‖ ^ (m + 2) * ‖x‖ ^ (m + 2))
      = C * ‖x‖ ^ (m + 1) := by
    rw [inv_pow]
    field_simp
    ring
  calc ‖risingProd x (m + 2) - x ^ (m + 2)‖ ≤ C * ‖x‖ ^ (m + 1) := hnum
    _ = C * ‖x‖⁻¹ ^ (m + 3) * (‖x‖ ^ (m + 2) * ‖x‖ ^ (m + 2)) := hgoal.symm
    _ ≤ C * ‖x‖⁻¹ ^ (m + 3) * (‖x‖ ^ (m + 2) * ‖risingProd x (m + 2)‖) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- **The summed comparison on a vertical line.**  The polygamma series and the factorial series
differ by one order. -/
theorem exists_norm_polygammaSeries_sub_factorial_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖(∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
          - ((m : ℂ) + 1)⁻¹ * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹‖
        ≤ C / t ^ (m + 2) := by
  obtain ⟨C, hC, hcomp⟩ := exists_norm_inv_pow_sub_inv_risingProd_le m
  refine ⟨4 * C, by positivity, fun σ t hσ ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have hs : (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have hpoly := hasSum_polygamma_series hσ t m
  have hfact := hasSum_inv_risingProd hs m
  have hshift : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := by
    intro n
    have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + (n : ℝ) := by simp
    rw [hre]
    positivity
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
    intro n
    have := norm_vertical_add_nat_ge_im (σ := σ) t n
    linarith
  have hterm : ∀ n : ℕ,
      ‖(((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹
        - (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2))⁻¹‖
      ≤ C * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 3) :=
    fun n => hcomp _ (hshift n) (hone n)
  have hfactshift : ∀ n : ℕ, risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2)
      = risingProd (((σ : ℂ) + (t : ℂ) * Complex.I) + (n : ℂ)) (m + 2) := fun n => rfl
  have hsub : (∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
      - ((m : ℂ) + 1)⁻¹ * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹
      = ∑' n : ℕ, ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹
          - (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2))⁻¹) := by
    rw [← hfact.tsum_eq, ← Summable.tsum_sub hpoly.summable hfact.summable]
  rw [hsub]
  have hsummablenorm : Summable (fun n : ℕ =>
      C * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 3)) :=
    (summable_norm_shift_inv_pow hσ t (k := m + 3) (by omega)).mul_left C
  have hnormbound := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
      (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹
        - (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) (m + 2))⁻¹)
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsummablenorm)
  refine le_trans hnormbound ?_
  have hle := Summable.tsum_le_tsum hterm
    (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsummablenorm) hsummablenorm
  refine le_trans hle ?_
  rw [tsum_mul_left]
  have horbit := tsum_norm_shift_inv_pow_le hσ ht m
  have hmul : C * (∑' n : ℕ, ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖⁻¹ ^ (m + 3))
      ≤ C * (4 / t ^ (m + 2)) := mul_le_mul_of_nonneg_left horbit hC
  refine le_trans hmul (le_of_eq ?_)
  field_simp

/-- **The quantitative leading asymptotic of a polygamma jet.**  Each jet equals an explicit
reciprocal rising factorial up to an error one order smaller than the jet itself. -/
theorem exists_norm_iteratedDeriv_digamma_sub_rising_le (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 < σ → 2 ≤ t →
      ‖iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ) * ((m : ℂ) + 1)⁻¹
            * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹‖
        ≤ C / t ^ (m + 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_polygammaSeries_sub_factorial_le m
  refine ⟨(((m + 1).factorial : ℕ) : ℝ) * C, by positivity, fun σ t hσ ht => ?_⟩
  have hpoly := hasSum_polygamma_series hσ t m
  have hfac : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hsign : ((-1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hval : iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
      = (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹ := by
    have h := hpoly.tsum_eq
    have hsq : ((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    rw [h, show ((-1 : ℂ)) ^ m * (((m + 1).factorial : ℕ) : ℂ)
        * (((-1 : ℂ)) ^ m / (((m + 1).factorial : ℕ) : ℂ)
          * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
        = (((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m)
          * ((((m + 1).factorial : ℕ) : ℂ) / (((m + 1).factorial : ℕ) : ℂ))
          * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) from by
        field_simp]
    rw [hsq, div_self hfac]
    ring
  rw [hval]
  have hfactor : (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
        * (∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
      - (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ) * ((m : ℂ) + 1)⁻¹
        * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹
      = (-1 : ℂ) ^ m * (((m + 1).factorial : ℕ) : ℂ)
        * ((∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
          - ((m : ℂ) + 1)⁻¹ * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹) := by
    ring
  rw [hfactor, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast]
  have := hbound σ t hσ ht
  have hfacnn : (0 : ℝ) ≤ (((m + 1).factorial : ℕ) : ℝ) := by positivity
  calc (((m + 1).factorial : ℕ) : ℝ)
        * ‖(∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
          - ((m : ℂ) + 1)⁻¹ * (risingProd ((σ : ℂ) + (t : ℂ) * Complex.I) (m + 1))⁻¹‖
      ≤ (((m + 1).factorial : ℕ) : ℝ) * (C / t ^ (m + 2)) :=
        mul_le_mul_of_nonneg_left this hfacnn
    _ = (((m + 1).factorial : ℕ) : ℝ) * C / t ^ (m + 2) := by ring

end GaloisForLFunctions
