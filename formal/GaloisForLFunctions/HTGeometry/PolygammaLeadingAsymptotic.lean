import GaloisForLFunctions.HTGeometry.ReciprocalPowerTelescope

/-!
# The leading asymptotic of every polygamma jet

On a vertical line the reciprocals `a = (s+n)⁻¹` and `b = (s+n+1)⁻¹` satisfy `a − b = a·b`, so the
telescoping series `Σ (a^{m+1} − b^{m+1}) = s^{−(m+1)}` differs from `(m+1)Σ a^{m+2}` by terms of
order `‖s+n‖^{−(m+3)}`.  Multiplied by `s^{m+1}` those terms are dominated by a fixed summable
sequence and each tends to zero, so dominated convergence gives

`s^{m+1} Σ_n (s+n)^{−(m+2)} → 1/(m+1)`,

and with the polygamma series the exact leading law of every jet:

`s^{m+1} · ψ⁽ᵐ⁺¹⁾(s) → (−1)^m m!`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- Along a vertical line the modulus increases under a unit shift of the index. -/
theorem norm_vertical_add_nat_le_succ (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖
      ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
  have hsq : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
      ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ ^ 2 := by
    have h1 : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 = (σ + n) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    have h2 : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ ^ 2 = (σ + n + 1) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      ring
    rw [h1, h2]
    have hnn : (0 : ℝ) ≤ σ + n := by positivity
    nlinarith
  have hnn : (0 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := norm_nonneg _
  nlinarith [norm_nonneg ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))]

/-- The reciprocal relation `a − b = a·b` for consecutive shifts on a vertical line. -/
theorem inv_sub_inv_eq_mul (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹
        - ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1)⁻¹
      = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹
        * ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1)⁻¹ := by
  have h1 : (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) ≠ 0 := vertical_add_nat_ne_zero hσ t n
  have h2 : (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1 ≠ 0 := by
    have h := vertical_add_nat_ne_zero hσ t (n + 1)
    intro hzero
    apply h
    push_cast
    rw [← hzero]
    ring
  field_simp
  ring

/-- **The telescoping series of reciprocal powers.** -/
theorem hasSum_telescope_pow (hσ : 0 < σ) (t : ℝ) (m : ℕ) :
    HasSum (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 1))⁻¹
        - (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1) ^ (m + 1))⁻¹)
      ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1))⁻¹) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  have hbound : ∀ n : ℕ, ‖((s + (n : ℂ)) ^ (m + 1))⁻¹ - ((s + (n : ℂ) + 1) ^ (m + 1))⁻¹‖
      ≤ ((m : ℝ) + 1) * (1 / (σ + n) ^ (m + 2)) := by
    intro n
    have hab := inv_sub_inv_eq_mul hσ t n
    have hposn : (0 : ℝ) < ‖s + (n : ℂ)‖ :=
      lt_of_lt_of_le (hpos n) (norm_vertical_add_nat_ge_re t n)
    have hba : ‖(s + (n : ℂ) + 1)⁻¹‖ ≤ ‖(s + (n : ℂ))⁻¹‖ := by
      rw [norm_inv, norm_inv, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hposn (norm_vertical_add_nat_le_succ hσ t n)
    have h := norm_pow_sub_pow_le_of_sub_eq_mul hab hba (m + 1)
    rw [← inv_pow, ← inv_pow]
    refine h.trans ?_
    have hge : σ + n ≤ ‖s + (n : ℂ)‖ := norm_vertical_add_nat_ge_re t n
    have hnorm : ‖(s + (n : ℂ))⁻¹‖ ^ (m + 2) ≤ 1 / (σ + n) ^ (m + 2) := by
      rw [norm_inv, inv_pow, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (hpos n).le hge _)
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsummable : Summable (fun n : ℕ => ((s + (n : ℂ)) ^ (m + 1))⁻¹
      - ((s + (n : ℂ) + 1) ^ (m + 1))⁻¹) :=
    Summable.of_norm_bounded
      (((summable_one_div_shift_pow hσ (m + 2) (by omega))).mul_left ((m : ℝ) + 1)) hbound
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, (((s + (i : ℂ)) ^ (m + 1))⁻¹
      - (((s + (i : ℂ) + 1)) ^ (m + 1))⁻¹)
      = ((s ^ (m + 1))⁻¹) - (((s + (N : ℂ)) ^ (m + 1))⁻¹) := by
    intro N
    have h := Finset.sum_range_sub' (fun i : ℕ => ((s + (i : ℂ)) ^ (m + 1))⁻¹) N
    have hcongr : ∀ i ∈ Finset.range N, ((s + (i : ℂ)) ^ (m + 1))⁻¹
        - ((s + ((i + 1 : ℕ) : ℂ)) ^ (m + 1))⁻¹
        = ((s + (i : ℂ)) ^ (m + 1))⁻¹ - (((s + (i : ℂ) + 1)) ^ (m + 1))⁻¹ := by
      intro i _
      have hcast : s + ((i + 1 : ℕ) : ℂ) = s + (i : ℂ) + 1 := by push_cast; ring
      rw [hcast]
    rw [← Finset.sum_congr rfl hcongr, h]
    simp
  have htail : Tendsto (fun N : ℕ => (((s + (N : ℂ)) ^ (m + 1))⁻¹)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      (g := fun N : ℕ => 1 / (σ + (N : ℝ)) ^ (m + 1)) ?_
    · rw [norm_inv, norm_pow, ← one_div]
      exact one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_left₀ (hpos N).le (norm_vertical_add_nat_ge_re t N) _)
    · have hdiv : Tendsto (fun N : ℕ => (σ + (N : ℝ)) ^ (m + 1)) atTop atTop := by
        refine Filter.Tendsto.comp (tendsto_pow_atTop (by omega)) ?_
        exact tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
      exact Tendsto.congr (fun N => by simp [Pi.inv_apply, one_div]) hdiv.inv_tendsto_atTop
  have := (tendsto_const_nhds (x := ((s ^ (m + 1))⁻¹)) (f := atTop (α := ℕ))).sub htail
  rw [sub_zero] at this
  exact this.congr (fun N => (hpartial N).symm)

/-- **The asymptotic of the polygamma sum.**  On a vertical line the `(m+2)`-nd reciprocal power sum
is `1/((m+1)s^{m+1})` to leading order. -/
theorem tendsto_pow_mul_polygamma_sum (hσ : 0 < σ) (m : ℕ) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)
      atTop (nhds (1 / ((m : ℂ) + 1))) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  set D : ℝ → ℕ → ℂ := fun t n => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
    * (((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹) ^ (m + 1)
        - (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1)⁻¹) ^ (m + 1))
      - ((m : ℂ) + 1) * (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹) ^ (m + 2)) with hD
  have hnormle : ∀ t : ℝ, 0 ≤ t → ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := by
    intro t ht
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = σ + t := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.le, norm_mul, Complex.norm_I,
            mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  -- the defect bound, with the two lower bounds on the modulus
  have hdefect : ∀ t : ℝ, 0 < t → ∀ n : ℕ,
      ‖D t n‖ ≤ (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
        / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3) := by
    intro t ht n
    have hab := inv_sub_inv_eq_mul hσ t n
    have hposn : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
      lt_of_lt_of_le (hpos n) (norm_vertical_add_nat_ge_re t n)
    have hba : ‖((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1)⁻¹‖
        ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹‖ := by
      rw [norm_inv, norm_inv, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hposn (norm_vertical_add_nat_le_succ hσ t n)
    have hd := norm_telescope_defect_le hab hba m
    have hnorma : ‖((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹‖ ^ (m + 3)
        = 1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3) := by
      rw [norm_inv, inv_pow, inv_eq_one_div]
    rw [hnorma] at hd
    rw [hD]
    simp only
    rw [norm_mul]
    have hs := hnormle t ht.le
    have hnn : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) * (1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I
        + (n : ℂ)‖ ^ (m + 3)) := by positivity
    calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)‖
          * ‖((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹) ^ (m + 1)
            - (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1)⁻¹) ^ (m + 1))
            - ((m : ℂ) + 1) * (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))⁻¹) ^ (m + 2)‖
        ≤ (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)
            * (1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3))) := by
          rw [norm_pow]
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hs _) hd (norm_nonneg _) ?_
          positivity
      _ = (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
            / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3) := by
          field_simp
  -- uniform summable bound
  have hunif : ∀ t : ℝ, max σ 1 ≤ t → ∀ n : ℕ,
      ‖D t n‖ ≤ (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (1 / (σ + n) ^ 2) := by
    intro t ht n
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right σ 1) ht
    have htσ : σ ≤ t := le_trans (le_max_left σ 1) ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hd := hdefect t ht0 n
    have hden : t ^ (m + 1) * (σ + n) ^ 2
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3) := by
      have hsplit : ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3)
          = ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 1)
            * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 := by
        rw [← pow_add]
      rw [hsplit]
      exact mul_le_mul (pow_le_pow_left₀ ht0.le (norm_vertical_add_nat_ge_im t n) _)
        (pow_le_pow_left₀ (hpos n).le (norm_vertical_add_nat_ge_re t n) _) (by positivity)
        (by positivity)
    have hdenpos : (0 : ℝ) < t ^ (m + 1) * (σ + n) ^ 2 := by
      have := hpos n
      positivity
    have hstep : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
        / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3)
        ≤ (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) / (t ^ (m + 1) * (σ + n) ^ 2) := by
      refine div_le_div_of_nonneg_left (by positivity) hdenpos hden
    have hnum : (σ + t) ^ (m + 1) ≤ (2 * t) ^ (m + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      linarith
    have hfinal : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) / (t ^ (m + 1) * (σ + n) ^ 2)
        ≤ (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (1 / (σ + n) ^ 2) := by
      rw [div_le_iff₀ hdenpos]
      have hmul : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
          ≤ (2 * t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      have hexp : (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (1 / (σ + n) ^ 2)
          * (t ^ (m + 1) * (σ + n) ^ 2)
          = (2 * t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
        have hn : (0 : ℝ) < σ + n := hpos n
        field_simp
        ring
      rw [hexp]
      exact hmul
    exact le_trans hd (le_trans hstep hfinal)
  -- each term vanishes
  have hpoint : ∀ n : ℕ, Tendsto (fun t : ℝ => D t n) atTop (nhds 0) := by
    intro n
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun t : ℝ => (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
        * (t ^ 2)⁻¹) atTop (nhds 0) := by
      have hpow : Tendsto (fun t : ℝ => t ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
      have := hpow.inv_tendsto_atTop.const_mul
        ((2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)))
      simpa using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (max σ 1)] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right σ 1) ht
    have htσ : σ ≤ t := le_trans (le_max_left σ 1) ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hd := hdefect t ht0 n
    have hden : t ^ (m + 3) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3) :=
      pow_le_pow_left₀ ht0.le (norm_vertical_add_nat_ge_im t n) _
    have hdenpos : (0 : ℝ) < t ^ (m + 3) := by positivity
    have hstep : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
        / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ (m + 3)
        ≤ (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) / t ^ (m + 3) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden
    have hnum : (σ + t) ^ (m + 1) ≤ (2 * t) ^ (m + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ _
      linarith
    have hfinal : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) / t ^ (m + 3)
        ≤ (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (t ^ 2)⁻¹ := by
      rw [div_le_iff₀ hdenpos]
      have hmul : (σ + t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
          ≤ (2 * t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      have hexp : (2 : ℝ) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (t ^ 2)⁻¹ * t ^ (m + 3)
          = (2 * t) ^ (m + 1) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
        field_simp
        ring
      rw [hexp]
      exact hmul
    exact le_trans hd (le_trans hstep hfinal)
  -- dominated convergence
  have hboundsummable : Summable (fun n : ℕ => (2 : ℝ) ^ (m + 1)
      * (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (1 / (σ + n) ^ 2)) :=
    (summable_one_div_shift_pow hσ 2 le_rfl).mul_left _
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := D)
    (g := fun _ : ℕ => (0 : ℂ)) hboundsummable hpoint
    (by
      filter_upwards [eventually_ge_atTop (max σ 1)] with t ht
      exact hunif t ht)
  rw [tsum_zero] at hdom
  -- identify the sum
  have hsum_eq : ∀ t : ℝ, 0 < t → ∑' n : ℕ, D t n
      = 1 - ((m : ℂ) + 1) * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹) := by
    intro t ht
    have hs0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      have := vertical_add_nat_ne_zero hσ t 0
      simpa using this
    have h1 := (hasSum_telescope_pow hσ t m).mul_left
      (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1))
    have h2 := ((summable_polygamma_terms hσ t m).hasSum).mul_left
      (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1) * ((m : ℂ) + 1))
    have hsub := h1.sub h2
    have hfun : (fun n : ℕ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 1))⁻¹
          - (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1) ^ (m + 1))⁻¹)
        - ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1) * ((m : ℂ) + 1)
          * ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹)) = D t := by
      funext n
      rw [hD]
      simp only [inv_pow]
      ring
    rw [hfun] at hsub
    rw [hsub.tsum_eq]
    have hone : ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1))⁻¹) = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hs0)
    rw [hone]
    ring
  have hfinal : Tendsto (fun t : ℝ => 1 - ((m : ℂ) + 1)
      * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹))
      atTop (nhds 0) := by
    refine hdom.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hsum_eq t ht
  have hmne : ((m : ℂ) + 1) ≠ 0 := by
    intro h
    have : ((m : ℝ) + 1 : ℂ) = 0 := by push_cast at h ⊢; exact h
    have hre : ((m : ℝ) + 1 : ℝ) = 0 := by exact_mod_cast this
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hstep : Tendsto (fun t : ℝ => ((m : ℂ) + 1)
      * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹))
      atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℝ))).sub hfinal
    rw [sub_zero] at this
    exact this.congr (fun t => by ring)
  have h2 := hstep.const_mul (((m : ℂ) + 1)⁻¹)
  rw [mul_one] at h2
  have hfun : ∀ t : ℝ, ((m : ℂ) + 1)⁻¹ * (((m : ℂ) + 1)
      * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹))
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹ := by
    intro t
    rw [← mul_assoc, inv_mul_cancel₀ hmne, one_mul]
  have h3 := h2.congr hfun
  rwa [one_div]

/-- **The leading asymptotic of every polygamma jet.**  On every vertical line to the right of the
imaginary axis, `s^{m+1}·ψ⁽ᵐ⁺¹⁾(s) → (−1)^m m!`: each jet is exactly `(−1)^m m!/s^{m+1}` to leading
order. -/
theorem tendsto_pow_mul_iteratedDeriv_digamma_vertical (hσ : 0 < σ) (m : ℕ) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds ((-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ))) := by
  have hsum := tendsto_pow_mul_polygamma_sum hσ m
  have hfactne : (((m + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hsignne : ((-1 : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  set c : ℂ := (-1 : ℂ) ^ m / (((m + 1).factorial : ℕ) : ℂ) with hc
  have hcne : c ≠ 0 := by
    rw [hc]
    exact div_ne_zero hsignne hfactne
  have hrw : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
      * ∑' n : ℕ, (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ (m + 2))⁻¹
      = c * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    intro t
    rw [(hasSum_polygamma_series hσ t m).tsum_eq, hc]
    ring
  have hmul := (hsum.congr hrw).const_mul c⁻¹
  have hfun : ∀ t : ℝ, c⁻¹ * (c * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
      * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)))
      = ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
        * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  have hmul := hmul.congr hfun
  have hlimval : c⁻¹ * (1 / ((m : ℂ) + 1)) = (-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ) := by
    have hfs : (((m + 1).factorial : ℕ) : ℂ) = ((m : ℂ) + 1) * ((m.factorial : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hmne : ((m : ℂ) + 1) ≠ 0 := by
      intro h
      have hre : ((m : ℝ) + 1 : ℝ) = 0 := by
        have : ((m : ℝ) + 1 : ℂ) = 0 := by push_cast at h ⊢; exact h
        exact_mod_cast this
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hsq : ((-1 : ℂ)) ^ m * ((-1 : ℂ)) ^ m = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hcinv : c⁻¹ = (((m : ℂ) + 1) * ((m.factorial : ℕ) : ℂ)) * (-1 : ℂ) ^ m := by
      rw [hc, hfs, inv_div, div_eq_mul_inv, inv_eq_of_mul_eq_one_right hsq]
    rw [hcinv]
    field_simp
  rw [hlimval] at hmul
  exact hmul

end GaloisForLFunctions
