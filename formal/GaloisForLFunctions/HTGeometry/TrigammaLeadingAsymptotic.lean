import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# The leading asymptotic of the trigamma function on a vertical line

The trigamma series `ψ′(s) = Σ (s+n)^{-2}` differs from the telescoping series
`Σ [(s+n)^{-1} − (s+n+1)^{-1}] = s^{-1}` term by term by `((s+n)^2 (s+n+1))^{-1}`.  On a vertical
line the modulus of `s+n` is bounded below both by the height and by the real part, so those terms
are dominated by a fixed summable sequence once multiplied by `s`, and each of them tends to zero.

Dominated convergence for series then gives the exact first-order law

`s · ψ′(s) → 1`,

the leading datum of the first digamma jet — the `O`-estimates in the corpus give only the order.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The telescoping majorant on a shifted arithmetic progression. -/
theorem hasSum_one_div_shift_mul_succ {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun n : ℕ => 1 / ((σ + n) * (σ + n + 1))) (1 / σ) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  have hterm : ∀ n : ℕ, 1 / ((σ + n) * (σ + n + 1)) = 1 / (σ + n) - 1 / (σ + (n + 1 : ℕ)) := by
    intro n
    have h1 : (0 : ℝ) < σ + n := hpos n
    have h2 : (0 : ℝ) < σ + (n + 1 : ℕ) := by
      push_cast
      linarith
    push_cast
    field_simp
    ring
  have hpartial : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((σ + i) * (σ + i + 1))
      = 1 / σ - 1 / (σ + N) := by
    intro N
    have := Finset.sum_range_sub' (fun i : ℕ => 1 / (σ + (i : ℝ))) N
    rw [Finset.sum_congr rfl (fun i _ => hterm i), this]
    push_cast
    simp
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((σ + n) * (σ + n + 1)) := by
    intro n
    have h1 : (0 : ℝ) < σ + n := hpos n
    positivity
  have hsummable : Summable (fun n : ℕ => 1 / ((σ + n) * (σ + n + 1))) := by
    refine summable_of_sum_range_le hnonneg (c := 1 / σ) (fun N => ?_)
    rw [hpartial N]
    have : (0 : ℝ) ≤ 1 / (σ + N) := by
      have := hpos N
      positivity
    linarith
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hlim : Tendsto (fun N : ℕ => 1 / (σ + (N : ℝ))) atTop (nhds 0) := by
    have hdiv : Tendsto (fun N : ℕ => σ + (N : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
    exact Tendsto.congr (fun N => by simp [Pi.inv_apply, one_div]) hdiv.inv_tendsto_atTop
  have := (tendsto_const_nhds (x := 1 / σ) (f := atTop (α := ℕ))).sub hlim
  rw [sub_zero] at this
  exact this.congr (fun N => (hpartial N).symm)

variable {σ : ℝ}

/-- The real part bounds the modulus on a vertical line. -/
theorem norm_vertical_add_nat_ge_re (t : ℝ) (n : ℕ) :
    σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
  calc σ + (n : ℝ) = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := hre.symm
    _ ≤ |((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re| := le_abs_self _
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := Complex.abs_re_le_norm _

/-- The height bounds the modulus on a vertical line. -/
theorem norm_vertical_add_nat_ge_im (t : ℝ) (n : ℕ) :
    t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im = t := by simp
  calc t = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im := him.symm
    _ ≤ |((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).im| := le_abs_self _
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := Complex.abs_im_le_norm _

/-- Off the poles on a vertical line the shifted argument is nonzero. -/
theorem vertical_add_nat_ne_zero (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) ≠ 0 := by
  intro h
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
  rw [h] at hre
  simp at hre
  have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- **The trigamma tail.**  On a vertical line the trigamma series minus the telescoping series for
`s⁻¹` sums to `Σ ((s+n)²(s+n+1))⁻¹`. -/
theorem hasSum_trigamma_tail (hσ : 0 < σ) (t : ℝ) :
    HasSum (fun n : ℕ => (((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ 2
        * ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1))⁻¹)
      (deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hre : 0 < s.re := by
    rw [hs]
    simpa using hσ
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  have hmaj : Summable (fun n : ℕ => (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1)))) :=
    ((hasSum_one_div_shift_mul_succ hσ).summable).mul_left _
  have hne : ∀ n : ℕ, s + (n : ℂ) ≠ 0 := fun n => vertical_add_nat_ne_zero hσ t n
  have hne' : ∀ n : ℕ, s + (n : ℂ) + 1 ≠ 0 := by
    intro n h
    have := vertical_add_nat_ne_zero hσ t (n + 1)
    apply this
    push_cast
    rw [← h]
    ring
  -- the trigamma series
  have hbound1 : ∀ n : ℕ, ‖((s + (n : ℂ)) ^ 2)⁻¹‖ ≤ (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by
    intro n
    have h1 : (0 : ℝ) < σ + n := hpos n
    have hge : σ + n ≤ ‖s + (n : ℂ)‖ := norm_vertical_add_nat_ge_re t n
    have hnorm : ‖((s + (n : ℂ)) ^ 2)⁻¹‖ = 1 / ‖s + (n : ℂ)‖ ^ 2 := by
      rw [norm_inv, norm_pow, one_div]
    rw [hnorm]
    have hle : 1 / ‖s + (n : ℂ)‖ ^ 2 ≤ 1 / (σ + n) ^ 2 := by
      have hsq : (σ + n) ^ 2 ≤ ‖s + (n : ℂ)‖ ^ 2 := by nlinarith
      exact one_div_le_one_div_of_le (by positivity) hsq
    have hstep : 1 / ((σ + n) ^ 2) = (1 / ((σ + n) * (σ + n + 1))) * ((σ + n + 1) / (σ + n)) := by
      field_simp
    have hfrac : (σ + n + 1) / (σ + n) ≤ 1 + 1 / σ := by
      rw [div_le_iff₀ h1]
      have hle : σ ≤ σ + (n : ℝ) := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hinv : 1 ≤ 1 / σ * (σ + (n : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 1 / σ)
        rw [one_div, inv_mul_cancel₀ hσ.ne'] at hmul
        rwa [one_div]
      nlinarith
    calc 1 / ‖s + (n : ℂ)‖ ^ 2 ≤ 1 / (σ + n) ^ 2 := hle
      _ = (1 / ((σ + n) * (σ + n + 1))) * ((σ + n + 1) / (σ + n)) := hstep
      _ ≤ (1 / ((σ + n) * (σ + n + 1))) * (1 + 1 / σ) := by
          have hnn : (0 : ℝ) ≤ 1 / ((σ + n) * (σ + n + 1)) := by positivity
          exact mul_le_mul_of_nonneg_left hfrac hnn
      _ = (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by ring
  have hsum1 : Summable (fun n : ℕ => ((s + (n : ℂ)) ^ 2)⁻¹) :=
    Summable.of_norm_bounded hmaj hbound1
  have h1 : HasSum (fun n : ℕ => ((s + (n : ℂ)) ^ 2)⁻¹) (deriv Complex.digamma s) :=
    (hsum1.hasSum_iff_tendsto_nat).mpr (RHTower.deriv_digamma_partialSum_tendsto hre)
  -- the telescoping series
  have hbound2 : ∀ n : ℕ, ‖((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹‖
      ≤ (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by
    intro n
    have h1' : (0 : ℝ) < σ + n := hpos n
    have hge : σ + n ≤ ‖s + (n : ℂ)‖ := norm_vertical_add_nat_ge_re t n
    have hge' : σ + n + 1 ≤ ‖s + (n : ℂ) + 1‖ := by
      have := norm_vertical_add_nat_ge_re (σ := σ) t (n + 1)
      have hcast : s + ((n + 1 : ℕ) : ℂ) = s + (n : ℂ) + 1 := by push_cast; ring
      rw [hcast] at this
      push_cast at this
      linarith
    have hnorm : ‖((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹‖
        = 1 / (‖s + (n : ℂ)‖ * ‖s + (n : ℂ) + 1‖) := by
      rw [norm_inv, norm_mul, one_div]
    rw [hnorm]
    have hprod : (σ + n) * (σ + n + 1) ≤ ‖s + (n : ℂ)‖ * ‖s + (n : ℂ) + 1‖ := by
      have hnn : (0 : ℝ) ≤ σ + n + 1 := by linarith
      exact mul_le_mul hge hge' (by linarith) (le_trans (by linarith) hge)
    have hle : 1 / (‖s + (n : ℂ)‖ * ‖s + (n : ℂ) + 1‖) ≤ 1 / ((σ + n) * (σ + n + 1)) :=
      one_div_le_one_div_of_le (by positivity) hprod
    have hnn : (0 : ℝ) ≤ 1 / ((σ + n) * (σ + n + 1)) := by positivity
    have hone : (1 : ℝ) ≤ 1 + 1 / σ := by
      have : (0 : ℝ) < 1 / σ := by positivity
      linarith
    calc 1 / (‖s + (n : ℂ)‖ * ‖s + (n : ℂ) + 1‖) ≤ 1 / ((σ + n) * (σ + n + 1)) := hle
      _ ≤ (1 + 1 / σ) * (1 / ((σ + n) * (σ + n + 1))) := by nlinarith
  have hsum2 : Summable (fun n : ℕ => ((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹) :=
    Summable.of_norm_bounded hmaj hbound2
  have hterm2 : ∀ n : ℕ, ((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹
      = (s + (n : ℂ))⁻¹ - (s + ((n + 1 : ℕ) : ℂ))⁻¹ := by
    intro n
    have h1' := hne n
    have h2' := hne' n
    have hcast : s + ((n + 1 : ℕ) : ℂ) = s + (n : ℂ) + 1 := by push_cast; ring
    rw [hcast]
    field_simp
    ring
  have hpartial2 : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((s + (i : ℂ)) * (s + (i : ℂ) + 1))⁻¹
      = s⁻¹ - (s + (N : ℂ))⁻¹ := by
    intro N
    have := Finset.sum_range_sub' (fun i : ℕ => (s + (i : ℂ))⁻¹) N
    rw [Finset.sum_congr rfl (fun i _ => hterm2 i), this]
    simp
  have htail0 : Tendsto (fun N : ℕ => (s + (N : ℂ))⁻¹) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      (g := fun N : ℕ => 1 / (σ + (N : ℝ))) ?_
    · rw [norm_inv]
      have hge : σ + N ≤ ‖s + (N : ℂ)‖ := norm_vertical_add_nat_ge_re t N
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (hpos N) hge
    · have hdiv : Tendsto (fun N : ℕ => σ + (N : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
      exact Tendsto.congr (fun N => by simp [Pi.inv_apply, one_div]) hdiv.inv_tendsto_atTop
  have h2 : HasSum (fun n : ℕ => ((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹) s⁻¹ := by
    rw [hsum2.hasSum_iff_tendsto_nat]
    have := (tendsto_const_nhds (x := s⁻¹) (f := atTop (α := ℕ))).sub htail0
    rw [sub_zero] at this
    exact this.congr (fun N => (hpartial2 N).symm)
  -- the difference is the tail series
  have hdiff := h1.sub h2
  have hfun : (fun n : ℕ => ((s + (n : ℂ)) ^ 2)⁻¹ - ((s + (n : ℂ)) * (s + (n : ℂ) + 1))⁻¹)
      = fun n : ℕ => ((s + (n : ℂ)) ^ 2 * (s + (n : ℂ) + 1))⁻¹ := by
    funext n
    have h1' := hne n
    have h2' := hne' n
    field_simp
    ring
  rwa [hfun] at hdiff

/-- **The leading asymptotic of the trigamma function.**  On every vertical line to the right of the
imaginary axis, `s · ψ′(s) → 1`: the first digamma jet is exactly `1/s` to leading order. -/
theorem tendsto_mul_deriv_digamma_vertical (hσ : 0 < σ) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)
        * deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds 1) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < σ + n := fun n => by positivity
  set F : ℝ → ℕ → ℂ := fun t n =>
    ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ((((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) ^ 2
        * ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1))⁻¹) with hF
  -- a uniform bound on the terms
  have hnormle : ∀ t : ℝ, 0 ≤ t → ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := by
    intro t ht
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = σ + t := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ.le, norm_mul, Complex.norm_I,
            mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hterm_bound : ∀ t : ℝ, max σ 1 ≤ t → ∀ n : ℕ,
      ‖F t n‖ ≤ 2 * (1 / ((σ + n) * (σ + n + 1))) := by
    intro t ht n
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right σ 1) ht
    have htσ : σ ≤ t := le_trans (le_max_left σ 1) ht
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    have hgeRe : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
      norm_vertical_add_nat_ge_re t n
    have hgeIm : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
      norm_vertical_add_nat_ge_im t n
    have hge' : σ + n + 1 ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have h := norm_vertical_add_nat_ge_re (σ := σ) t (n + 1)
      have hcast : (σ : ℂ) + (t : ℂ) * Complex.I + ((n + 1 : ℕ) : ℂ)
          = (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1 := by push_cast; ring
      rw [hcast] at h
      push_cast at h
      linarith
    have hsq : t * (σ + n) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 := by
      have h1 := hgeIm
      have h2 := hgeRe
      have hnn : (0 : ℝ) ≤ σ + n := (hpos n).le
      nlinarith
    have hnormF : ‖F t n‖ = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
        / (‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖) := by
      rw [hF]
      simp only [norm_mul, norm_inv, norm_pow]
      rw [div_eq_mul_inv]
    rw [hnormF]
    have hden : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
        * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have h1 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
        lt_of_lt_of_le (hpos n) hgeRe
      have h2 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
        have : (0 : ℝ) < σ + n + 1 := by linarith [hpos n]
        linarith
      positivity
    rw [div_le_iff₀ hden]
    have hnum : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := hnormle t ht0
    have hprod : t * (σ + n) * (σ + n + 1)
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have hnn : (0 : ℝ) ≤ σ + n + 1 := by linarith [hpos n]
      have hsq0 : (0 : ℝ) ≤ t * (σ + n) := by positivity
      exact mul_le_mul hsq hge' hnn (le_trans hsq0 hsq)
    have hkey : σ + t ≤ 2 * (1 / ((σ + n) * (σ + n + 1))) * (t * (σ + n) * (σ + n + 1)) := by
      have hfac : 2 * (1 / ((σ + n) * (σ + n + 1))) * (t * (σ + n) * (σ + n + 1)) = 2 * t := by
        have h1 : (0 : ℝ) < σ + n := hpos n
        have h2 : (0 : ℝ) < σ + n + 1 := by linarith
        field_simp
      rw [hfac]
      linarith
    have hmono : 2 * (1 / ((σ + n) * (σ + n + 1))) * (t * (σ + n) * (σ + n + 1))
        ≤ 2 * (1 / ((σ + n) * (σ + n + 1)))
          * (‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
            * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖) := by
      have hnn : (0 : ℝ) ≤ 2 * (1 / ((σ + n) * (σ + n + 1))) := by
        have := hpos n
        positivity
      have hassoc : t * (σ + n) * (σ + n + 1) = t * (σ + n) * (σ + n + 1) := rfl
      exact mul_le_mul_of_nonneg_left hprod hnn
    linarith
  -- each term vanishes
  have hpointwise : ∀ n : ℕ, Tendsto (fun t : ℝ => F t n) atTop (nhds 0) := by
    intro n
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun t : ℝ => 2 * (1 / (σ + n)) * t⁻¹) atTop (nhds 0) := by
      have := tendsto_inv_atTop_zero.const_mul (2 * (1 / (σ + n)))
      simpa using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop (max σ 1)] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right σ 1) ht
    have htσ : σ ≤ t := le_trans (le_max_left σ 1) ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hgeRe : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
      norm_vertical_add_nat_ge_re t n
    have hgeIm : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
      norm_vertical_add_nat_ge_im t n
    have hge'Im : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have h := norm_vertical_add_nat_ge_im (σ := σ) t (n + 1)
      have hcast : (σ : ℂ) + (t : ℂ) * Complex.I + ((n + 1 : ℕ) : ℂ)
          = (σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1 := by push_cast; ring
      rw [hcast] at h
      exact h
    have hsq : t * (σ + n) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ σ + n := (hpos n).le
      nlinarith
    have hnormF : ‖F t n‖ = ‖(σ : ℂ) + (t : ℂ) * Complex.I‖
        / (‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖) := by
      rw [hF]
      simp only [norm_mul, norm_inv, norm_pow]
      rw [div_eq_mul_inv]
    rw [hnormF]
    have hden : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
        * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have h1 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
        lt_of_lt_of_le (hpos n) hgeRe
      have h2 : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ :=
        lt_of_lt_of_le ht0 hge'Im
      positivity
    rw [div_le_iff₀ hden]
    have hnum : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := hnormle t ht0.le
    have hprod : (t * (σ + n)) * t
        ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ ^ 2
          * ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ) + 1‖ := by
      have hsq0 : (0 : ℝ) ≤ t * (σ + n) := by positivity
      exact mul_le_mul hsq hge'Im ht0.le (le_trans hsq0 hsq)
    have hfac : 2 * (1 / (σ + n)) * t⁻¹ * ((t * (σ + n)) * t) = 2 * t := by
      have h1 : (0 : ℝ) < σ + n := hpos n
      field_simp
    have hnn : (0 : ℝ) ≤ 2 * (1 / (σ + n)) * t⁻¹ := by
      have := hpos n
      positivity
    have hmono := mul_le_mul_of_nonneg_left hprod hnn
    have hle : σ + t ≤ 2 * (1 / (σ + n)) * t⁻¹ * ((t * (σ + n)) * t) := by
      rw [hfac]
      linarith
    linarith
  -- dominated convergence
  have hboundsummable : Summable (fun n : ℕ => 2 * (1 / ((σ + n) * (σ + n + 1)))) :=
    ((hasSum_one_div_shift_mul_succ hσ).summable).mul_left _
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := F) (g := fun _ : ℕ => (0 : ℂ))
    hboundsummable hpointwise
    (by
      filter_upwards [eventually_ge_atTop (max σ 1)] with t ht
      exact hterm_bound t ht)
  rw [tsum_zero] at hdom
  -- identify the sum
  have hsum_eq : ∀ t : ℝ, ∑' n : ℕ, F t n
      = ((σ : ℂ) + (t : ℂ) * Complex.I)
        * deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 := by
    intro t
    have hs := (hasSum_trigamma_tail hσ t).mul_left ((σ : ℂ) + (t : ℂ) * Complex.I)
    have hne0 : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      have := vertical_add_nat_ne_zero hσ t 0
      simpa using this
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹)
        = ((σ : ℂ) + (t : ℂ) * Complex.I)
          * deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 := by
      field_simp
    rw [hval] at hs
    exact hs.tsum_eq
  have hfinal : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I)
      * deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - 1) atTop (nhds 0) :=
    hdom.congr hsum_eq
  have := hfinal.add (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℝ)))
  rw [zero_add] at this
  exact this.congr (fun t => by ring)

end GaloisForLFunctions
