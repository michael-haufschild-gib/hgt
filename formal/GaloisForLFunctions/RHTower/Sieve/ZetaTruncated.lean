import GaloisForLFunctions.RHTower.ZetaPartialSumStrip
import GaloisForLFunctions.RHTower.Sieve.ZetaStripGrowth
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# The truncated formula for zeta

Combining the corpus's finite Abel identity with the fractional-part continuation gives, for
`re w > 0`, `w ≠ 1` and any `N ≥ 1`,

`ζ(w) = ∑_{k ≤ N} k^{-w} + N^{1-w}/(w−1) − w ∫_N^∞ fract(t) t^{-w-1} dt`.

The tail integral is at most `N^{-σ}/σ`, so at `N ≍ |t|` the whole expression is `O(log|t|)` — the
logarithmic growth the zero-free region needs, which the single-term formula could not give.
-/

namespace RHTower.Sieve

open MeasureTheory Set

/-- The fractional-part integrand is integrable beyond any point of `[1, ∞)`. -/
theorem integrableOn_Ioi_fract_cpow {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi (N : ℝ)) := by
  have hsub : Ioi (N : ℝ) ⊆ Ioi (1 : ℝ) := by
    refine Ioi_subset_Ioi ?_
    exact_mod_cast hN
  exact (RHTower.integrableOn_Ioi_one_fract_cpow hs).mono_set hsub

/-- **The truncated formula.** -/
theorem riemannZeta_eq_sum_add_tail {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta w
      = (∑ k ∈ Finset.Icc 1 N, ((k : ℝ) : ℂ) ^ (-w)) + ((N : ℝ) : ℂ) ^ (1 - w) / (w - 1)
        - w * ∫ t in Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsplit : (∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)))
      = (∫ t in Ioc (1 : ℝ) (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)))
        + ∫ t in Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hNR]
    refine setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi ?_ ?_
    · exact (RHTower.integrableOn_Ioi_one_fract_cpow hw0).mono_set Set.Ioc_subset_Ioi_self
    · exact integrableOn_Ioi_fract_cpow hw0 hN
  have habel := RHTower.sum_cpow_sub_pow_eq hw0 hwne1 hN
  have hcont := RHTower.integral_Ioi_one_fract_cpow_of_re_pos hw0 hwne1
  have hneg : ∀ t : ℝ, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-w - 1)
      = ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    intro t
    rw [RHTower.neg_sub_one_eq]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hneg t)] at habel
  have hw1ne : w - 1 ≠ 0 := sub_ne_zero.2 hwne1
  have hwne0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    exact lt_irrefl 0 hw0
  rw [hsplit] at hcont
  have h1w : (1 : ℂ) - w ≠ 0 := by
    intro h
    apply hwne1
    linear_combination -h
  linear_combination (norm := (field_simp; ring)) w * hcont - habel

/-- The tail integral beyond `N` is at most `N^{-σ}/σ`. -/
theorem norm_integral_Ioi_fract_cpow_le {w : ℂ} (hw : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∫ t in Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))‖
      ≤ (N : ℝ) ^ (-w.re) / w.re := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hintegrable : IntegrableOn (fun t : ℝ => t ^ (-w.re - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  have hpt : ∀ t ∈ Ioi (N : ℝ),
      ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))‖ ≤ t ^ (-w.re - 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans hN0 ht
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
      exact le_of_lt (Int.fract_lt_one t)
    have hpow : ‖(t : ℂ) ^ (-(w + 1))‖ = t ^ (-w.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      congr 1
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
      ring
    rw [norm_mul, hpow]
    have hnn : (0 : ℝ) ≤ t ^ (-w.re - 1) := Real.rpow_nonneg ht0.le _
    nlinarith [hfract, hnn, norm_nonneg (((Int.fract t : ℝ) : ℂ))]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hae : ∀ᵐ t ∂(Measure.restrict volume (Ioi (N : ℝ))),
      ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))‖ ≤ t ^ (-w.re - 1) :=
    Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi) hpt
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
    hintegrable hae) ?_
  rw [integral_Ioi_rpow_of_lt (by linarith : -w.re - 1 < -1) hN0]
  have hexp : -w.re - 1 + 1 = -w.re := by ring
  rw [hexp]
  rw [neg_div_neg_eq]

/-- **The truncated bound.**  Every term is elementary in `N` and `w`. -/
theorem norm_riemannZeta_le_truncated {w : ℂ} (hw0 : 0 < w.re) (hwne1 : w ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) :
    ‖riemannZeta w‖
      ≤ (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-w.re))
        + (N : ℝ) ^ (1 - w.re) / ‖w - 1‖
        + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [riemannZeta_eq_sum_add_tail hw0 hwne1 hN]
  refine le_trans (norm_sub_le _ _) ?_
  refine add_le_add ?_ ?_
  · refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ ?_
    · refine le_trans (norm_sum_le _ _) ?_
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < (k : ℝ) := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        linarith
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hk0, Complex.neg_re]
    · rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      have hre : ((1 : ℂ) - w).re = 1 - w.re := by simp
      rw [hre]
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_Ioi_fract_cpow_le hw0 hN) (norm_nonneg w)

/-- The truncated sum is at most the harmonic sum when `σ ≥ 1`. -/
theorem sum_rpow_neg_le_harmonic {σ : ℝ} (hσ : 1 ≤ σ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ)) ≤ 1 + Real.log N := by
  refine le_trans (Finset.sum_le_sum fun k hk => ?_) (sum_Icc_one_div_le_one_add_log N)
  rw [Finset.mem_Icc] at hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
  have hmono : (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
  have hval : (k : ℝ) ^ (-1 : ℝ) = 1 / (k : ℝ) := by
    rw [show (-1 : ℝ) = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
      Real.rpow_natCast]
    simp
  rw [hval] at hmono
  exact hmono

/-- **The logarithmic bound in the strip.**  For `σ ≥ 1` and any truncation point at least `‖w‖`,
the size of `ζ` is logarithmic. -/
theorem norm_riemannZeta_le_log {w : ℂ} (hσ : 1 ≤ w.re) (hwne1 : w ≠ 1) {N : ℕ}
    (hN : 1 ≤ N) (hNw : ‖w‖ ≤ (N : ℝ)) :
    ‖riemannZeta w‖ ≤ 2 + Real.log N + 1 / ‖w - 1‖ := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hw0 : 0 < w.re := by linarith
  refine le_trans (norm_riemannZeta_le_truncated hw0 hwne1 hN) ?_
  have h1 : (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-w.re)) ≤ 1 + Real.log N :=
    sum_rpow_neg_le_harmonic hσ N
  have h2 : (N : ℝ) ^ (1 - w.re) ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_le hNR (by linarith : 1 - w.re ≤ 0)
    simpa using this
  have hw1 : (0 : ℝ) < ‖w - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hwne1
  have h3 : (N : ℝ) ^ (1 - w.re) / ‖w - 1‖ ≤ 1 / ‖w - 1‖ := by
    exact div_le_div_of_nonneg_right h2 hw1.le
  have hNpow : (N : ℝ) ^ (-w.re) ≤ 1 / (N : ℝ) := by
    have hstep : (N : ℝ) ^ (-w.re) ≤ (N : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    have hval : (N : ℝ) ^ (-1 : ℝ) = 1 / (N : ℝ) := by
      rw [show (-1 : ℝ) = -((1 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by linarith),
        Real.rpow_natCast]
      simp
    rw [hval] at hstep
    exact hstep
  have h4 : ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) ≤ 1 := by
    have hstep1 : (N : ℝ) ^ (-w.re) / w.re ≤ (1 / (N : ℝ)) / 1 := by
      have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-w.re) := Real.rpow_nonneg (by linarith) _
      gcongr
    have hstep2 : ‖w‖ * ((1 / (N : ℝ)) / 1) ≤ 1 := by
      rw [div_one]
      rw [mul_one_div, div_le_one hN0]
      exact hNw
    calc ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re)
        ≤ ‖w‖ * ((1 / (N : ℝ)) / 1) := mul_le_mul_of_nonneg_left hstep1 (norm_nonneg w)
      _ ≤ 1 := hstep2
  linarith

/-- The truncated sum below the abscissa, by integral comparison. -/
theorem sum_rpow_neg_le_of_lt_one {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ))
      ≤ 1 + ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) + (N : ℝ) ^ (-σ) := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hsplit : ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ)
      = ((1 : ℝ) ^ (-σ) + ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ)) + (N : ℝ) ^ (-σ) := by
    rw [show Finset.Icc 1 N = Finset.Ico 1 N ∪ {N} by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton]
      omega]
    rw [Finset.sum_union (by
      simp only [Finset.disjoint_singleton_right, Finset.mem_Ico]
      omega)]
    rw [Finset.sum_singleton]
    congr 1
    rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ 2) (by omega : 2 ≤ N)]
    congr 1
    rw [show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton]
    norm_num
  have hreindex : ∑ i ∈ Finset.Ico 1 (N - 1), ((i : ℝ) + 1) ^ (-σ)
      = ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ) := by
    have h := Finset.sum_Ico_add' (fun k : ℕ => ((k : ℝ)) ^ (-σ)) 1 (N - 1) 1
    push_cast at h
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using h
  have hsubset : ∑ i ∈ Finset.Ico 1 (N - 1), ((i : ℝ) + 1) ^ (-σ)
      ≤ ∑ i ∈ Finset.Ico 1 N, ((i : ℝ) + 1) ^ (-σ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun i _ _ => Real.rpow_nonneg (by positivity) _)
    exact Finset.Ico_subset_Ico (le_refl 1) (by omega)
  have hcomp := (antitoneOn_rpow_neg (le_of_lt hσ0) 1 N (le_refl 1)).sum_le_integral_Ico
    (by omega : 1 ≤ N)
  norm_num at hcomp
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-σ)) = ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith))]
    have hexp : -σ + 1 = 1 - σ := by ring
    rw [hexp, Real.one_rpow]
  rw [hsplit, Real.one_rpow]
  have hchain : ∑ k ∈ Finset.Ico 2 N, (k : ℝ) ^ (-σ) ≤ ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [← hreindex, ← hint]
    exact le_trans hsubset hcomp
  linarith

/-- **The truncated bound below the abscissa.**  Every term is elementary in `N` and `w`; at
`σ = 1 − 1/log N` the first group is `O(log N)`, so this is the logarithmic bound extended to the
left of `re = 1`. -/
theorem norm_riemannZeta_le_truncated_of_lt_one {w : ℂ} (hσ0 : 0 < w.re) (hσ1 : w.re < 1)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖riemannZeta w‖
      ≤ (1 + ((N : ℝ) ^ (1 - w.re) - 1) / (1 - w.re) + (N : ℝ) ^ (-w.re))
        + (N : ℝ) ^ (1 - w.re) / ‖w - 1‖
        + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by
  have hwne1 : w ≠ 1 := fun h => by
    rw [h, Complex.one_re] at hσ1
    exact absurd hσ1 (lt_irrefl 1)
  have hN1 : 1 ≤ N := by omega
  refine le_trans (norm_riemannZeta_le_truncated hσ0 hwne1 hN1) ?_
  have hsum := sum_rpow_neg_le_of_lt_one hσ0 hσ1 hN
  linarith

/-- `(e^u − 1)/u ≤ e` for `0 < u ≤ 1`. -/
theorem exp_sub_one_div_le {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    (Real.exp u - 1) / u ≤ Real.exp 1 := by
  have hstep : Real.exp u - 1 ≤ u * Real.exp u := by
    have h := Real.add_one_le_exp (-u)
    have hpos : (0 : ℝ) < Real.exp u := Real.exp_pos u
    have hmul := mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at hmul
    simp only [add_neg_cancel, Real.exp_zero] at hmul
    nlinarith [hmul, hpos]
  have hexp : Real.exp u ≤ Real.exp 1 := Real.exp_le_exp.2 hu1
  rw [div_le_iff₀ hu0]
  nlinarith [hstep, hexp, hu0]

/-- **The uniform truncated sum bound.**  For `σ` within `1/log N` of `1` on either side the sum is
`O(log N)`, with the same explicit constant. -/
theorem sum_rpow_neg_le_uniform {σ : ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hlow : 1 - 1 / Real.log N ≤ σ) (hσ0 : 0 < σ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-σ)) ≤ 2 + Real.exp 1 * Real.log N := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogNn : (0 : ℝ) ≤ Real.log N := hlogpos.le
  rcases lt_or_ge σ 1 with hσ1 | hσ1
  · have h := sum_rpow_neg_le_of_lt_one hσ0 hσ1 hN
    have hx0 : 0 < 1 - σ := by linarith
    have hxle : (1 - σ) * Real.log N ≤ 1 := by
      have : 1 - σ ≤ 1 / Real.log N := by linarith
      calc (1 - σ) * Real.log N ≤ (1 / Real.log N) * Real.log N :=
            mul_le_mul_of_nonneg_right this hlogNn
        _ = 1 := by field_simp
    have hpow : (N : ℝ) ^ (1 - σ) = Real.exp ((1 - σ) * Real.log N) := by
      rw [Real.rpow_def_of_pos (by linarith)]
      ring_nf
    have hkey : ((N : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ Real.exp 1 * Real.log N := by
      rw [hpow]
      have hu := exp_sub_one_div_le (by positivity : 0 < (1 - σ) * Real.log N) hxle
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (1 - σ) * Real.log N)] at hu
      rw [div_le_iff₀ hx0]
      nlinarith [hu, hlogNn, hx0]
    have hlast : (N : ℝ) ^ (-σ) ≤ 1 := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (N:ℝ))
        (by linarith : -σ ≤ 0)
      simpa using this
    linarith
  · have h := sum_rpow_neg_le_harmonic hσ1 N
    have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith [h, he, hlogNn]

/-- **The logarithmic bound, uniform across the abscissa.**  Valid on a strip reaching `1/log N` to
the left of `re = 1`, which is where a Cauchy disc around a near-`1` point lives. -/
theorem norm_riemannZeta_le_log_uniform {w : ℂ} (hσ : 1 / 2 ≤ w.re) (hwne1 : w ≠ 1)
    {N : ℕ} (hN : 2 ≤ N) (hlow : 1 - 1 / Real.log N ≤ w.re) (hNw : ‖w‖ ≤ (N : ℝ)) :
    ‖riemannZeta w‖
      ≤ 2 + Real.exp 1 * Real.log N + Real.exp 1 / ‖w - 1‖ + 2 * Real.exp 1 := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogpos : 0 < Real.log N := Real.log_pos (by linarith)
  have hσ0 : 0 < w.re := by linarith
  have hxle : (1 - w.re) * Real.log N ≤ 1 := by
    have hd : 1 - w.re ≤ 1 / Real.log N := by linarith
    rcases le_or_gt (1 - w.re) 0 with h | h
    · nlinarith [hlogpos]
    · calc (1 - w.re) * Real.log N ≤ (1 / Real.log N) * Real.log N :=
            mul_le_mul_of_nonneg_right hd hlogpos.le
        _ = 1 := by field_simp
  have hNpow1 : (N : ℝ) ^ (1 - w.re) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hN0]
    refine Real.exp_le_exp.2 ?_
    calc Real.log N * (1 - w.re) = (1 - w.re) * Real.log N := by ring
      _ ≤ 1 := hxle
  have hNpow2 : (N : ℝ) ^ (-w.re) ≤ Real.exp 1 / (N : ℝ) := by
    have hrw : (N : ℝ) ^ (1 - w.re) / (N : ℝ) = (N : ℝ) ^ (-w.re) := by
      rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]
      field_simp
    rw [← hrw]
    exact div_le_div_of_nonneg_right hNpow1 hN0.le
  refine le_trans (norm_riemannZeta_le_truncated hσ0 hwne1 (by omega : 1 ≤ N)) ?_
  have hsum := sum_rpow_neg_le_uniform hN hlow hσ0
  have hw1 : (0 : ℝ) < ‖w - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hwne1
  have hmid : (N : ℝ) ^ (1 - w.re) / ‖w - 1‖ ≤ Real.exp 1 / ‖w - 1‖ :=
    div_le_div_of_nonneg_right hNpow1 hw1.le
  have hlast : ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) ≤ 2 * Real.exp 1 := by
    have h1 : (N : ℝ) ^ (-w.re) / w.re ≤ (Real.exp 1 / (N : ℝ)) / (1 / 2) := by
      have hnn : (0 : ℝ) ≤ (N : ℝ) ^ (-w.re) := Real.rpow_nonneg hN0.le _
      gcongr
    calc ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re)
        ≤ ‖w‖ * ((Real.exp 1 / (N : ℝ)) / (1 / 2)) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg w)
      _ ≤ (N : ℝ) * ((Real.exp 1 / (N : ℝ)) / (1 / 2)) := by
          refine mul_le_mul_of_nonneg_right hNw ?_
          positivity
      _ = 2 * Real.exp 1 := by field_simp
  linarith

end RHTower.Sieve
