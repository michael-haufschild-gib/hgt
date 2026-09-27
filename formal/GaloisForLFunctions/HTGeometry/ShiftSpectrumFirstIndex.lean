import GaloisForLFunctions.HTGeometry.LSeriesRightLimit
import GaloisForLFunctions.HTGeometry.ShiftLatticeRadiusLaw

/-!
# The first non-vanishing coefficient: right limit and cusp gap

For a Dirichlet series whose coefficients vanish below an index `m`, the normalized series
`m^w L(f,w)` tends to `f(m)` along every family with `Re w → ∞`
(`tendsto_cpow_mul_LSeries_of_re_atTop`): past `m` every term carries the factor
`(m/n)^{Re w} ≤ (m/(m+1))^{Re w - σ₀}`.

On the spectral side, the first non-vanishing coefficient is the nearest point of the shift
spectrum to the cusp: `dist(0, Spec) = d (m/q)^{1/d}` (`infDist_zero_shiftSpectrum_of_first`).
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **A Dirichlet series with vanishing initial coefficients, normalized by its first index,
tends to its first coefficient along every family escaping to the right.** -/
theorem tendsto_cpow_mul_LSeries_of_re_atTop {f : ℕ → ℂ} {σ₀ : ℝ}
    (hσ : Summable (fun n : ℕ => ‖LSeries.term f (σ₀ : ℂ) n‖)) {m : ℕ} (hm : 0 < m)
    (hf : ∀ n : ℕ, 0 < n → n < m → f n = 0)
    {α : Type*} {l : Filter α} {w : α → ℂ} (hw : Tendsto (fun a => (w a).re) l atTop) :
    Tendsto (fun a => (m : ℂ) ^ (w a) * LSeries f (w a)) l (𝓝 (f m)) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set ρ : ℝ := (m : ℝ) / (m + 1) with hρ
  have hρpos : 0 < ρ := by positivity
  have hρlt : ρ < 1 := by rw [hρ, div_lt_one (by positivity)]; linarith
  set S : ℝ := ∑' n : ℕ, ‖LSeries.term f (σ₀ : ℂ) n‖ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have key : ∀ᶠ a in l, ‖(m : ℂ) ^ (w a) * LSeries f (w a) - f m‖ ≤
      (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * S := by
    filter_upwards [hw.eventually_ge_atTop σ₀] with a ha
    have hnorm : Summable (fun n : ℕ => ‖LSeries.term f (w a) n‖) :=
      hσ.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le_of_re_le ha n)
    have hsummable : Summable (LSeries.term f (w a)) := hnorm.of_norm
    have hmul : Summable (fun n => (m : ℂ) ^ (w a) * LSeries.term f (w a) n) :=
      hsummable.mul_left _
    have hsplit := hmul.tsum_eq_add_tsum_ite m
    have hone : (m : ℂ) ^ (w a) * LSeries.term f (w a) m = f m := by
      have hne : (m : ℂ) ^ (w a) ≠ 0 :=
        Complex.cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hm.ne'))
      rw [LSeries.term_of_ne_zero hm.ne', mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hne, mul_one]
    have hLS : (m : ℂ) ^ (w a) * LSeries f (w a) - f m
        = ∑' n : ℕ, (if n = m then 0 else (m : ℂ) ^ (w a) * LSeries.term f (w a) n) := by
      have : (m : ℂ) ^ (w a) * LSeries f (w a) =
          ∑' n : ℕ, (m : ℂ) ^ (w a) * LSeries.term f (w a) n := by
        rw [LSeries, tsum_mul_left]
      rw [this, hsplit, hone]
      ring
    have hbound : ∀ n : ℕ, ‖(if n = m then 0 else (m : ℂ) ^ (w a) * LSeries.term f (w a) n)‖
        ≤ (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * ‖LSeries.term f (σ₀ : ℂ) n‖ := by
      intro n
      by_cases hnm : n = m
      · simp only [hnm, if_true, norm_zero]
        positivity
      rw [if_neg hnm]
      rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
      · rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        · rw [LSeries.term_of_ne_zero hn0.ne', hf n hn0 hlt, zero_div, mul_zero, norm_zero]
          positivity
      · have hn0 : n ≠ 0 := by omega
        have hnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
        have hnpos : (0 : ℝ) < n := by linarith
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos hm, LSeries.norm_term_eq,
          LSeries.norm_term_eq, if_neg hn0, if_neg hn0, Complex.ofReal_re]
        have hratio : (m : ℝ) / n ≤ ρ := by
          rw [hρ]
          exact div_le_div_of_nonneg_left hmR.le (by positivity) hnR
        have hexp : 0 ≤ (w a).re - σ₀ := by linarith
        have hpow : ((m : ℝ) / n) ^ ((w a).re - σ₀) ≤ ρ ^ ((w a).re - σ₀) :=
          Real.rpow_le_rpow (by positivity) hratio hexp
        have hsplitpow : (m : ℝ) ^ (w a).re / (n : ℝ) ^ (w a).re =
            (m : ℝ) ^ σ₀ / (n : ℝ) ^ σ₀ * ((m : ℝ) / n) ^ ((w a).re - σ₀) := by
          rw [Real.div_rpow hmR.le hnpos.le, Real.rpow_sub hmR, Real.rpow_sub hnpos]
          field_simp
        calc (m : ℝ) ^ (w a).re * (‖f n‖ / (n : ℝ) ^ (w a).re)
            = ‖f n‖ / (n : ℝ) ^ σ₀ * ((m : ℝ) ^ σ₀ * ((m : ℝ) / n) ^ ((w a).re - σ₀)) := by
              rw [mul_div_assoc', mul_comm _ ‖f n‖, mul_div_assoc, hsplitpow]
              ring
          _ ≤ ‖f n‖ / (n : ℝ) ^ σ₀ * ((m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀)) := by
              gcongr
          _ = (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * (‖f n‖ / (n : ℝ) ^ σ₀) := by ring
    have hsum2 : Summable (fun n : ℕ =>
        (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * ‖LSeries.term f (σ₀ : ℂ) n‖) := hσ.mul_left _
    have hsumu : Summable (fun n : ℕ =>
        ‖(if n = m then 0 else (m : ℂ) ^ (w a) * LSeries.term f (w a) n)‖) :=
      hsum2.of_nonneg_of_le (fun n => norm_nonneg _) hbound
    rw [hLS]
    calc ‖∑' n : ℕ, (if n = m then 0 else (m : ℂ) ^ (w a) * LSeries.term f (w a) n)‖
        ≤ ∑' n : ℕ, ‖(if n = m then 0 else (m : ℂ) ^ (w a) * LSeries.term f (w a) n)‖ :=
          norm_tsum_le_tsum_norm hsumu
      _ ≤ ∑' n : ℕ, (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * ‖LSeries.term f (σ₀ : ℂ) n‖ :=
          hsumu.tsum_le_tsum hbound hsum2
      _ = (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * S := by rw [tsum_mul_left]
  have hten : Tendsto (fun a => ρ ^ ((w a).re - σ₀)) l (𝓝 0) := by
    have hsub : Tendsto (fun a => (w a).re - σ₀) l atTop :=
      tendsto_atTop_add_const_right _ _ hw
    exact (tendsto_rpow_atTop_of_base_lt_one ρ (by linarith) hρlt).comp hsub
  have hzero : Tendsto (fun a => (m : ℝ) ^ σ₀ * ρ ^ ((w a).re - σ₀) * S) l (𝓝 0) := by
    have := (hten.const_mul ((m : ℝ) ^ σ₀)).mul_const S
    rwa [mul_zero, zero_mul] at this
  have hsub : Tendsto (fun a => (m : ℂ) ^ (w a) * LSeries f (w a) - f m) l (𝓝 0) :=
    squeeze_zero_norm' key hzero
  have := hsub.add (tendsto_const_nhds (x := f m) (f := l))
  rw [zero_add] at this
  refine this.congr fun a => ?_
  ring

/-- **Uniform bound at the first index.**  To the right of an abscissa of absolute convergence,
`‖m^w L(f,w)‖` is bounded, uniformly in `w`. -/
theorem exists_bound_norm_cpow_mul_LSeries {f : ℕ → ℂ} {σ₀ : ℝ}
    (hσ : Summable (fun n : ℕ => ‖LSeries.term f (σ₀ : ℂ) n‖)) {m : ℕ} (hm : 0 < m)
    (hf : ∀ n : ℕ, 0 < n → n < m → f n = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, σ₀ ≤ w.re → ‖LSeries f w‖ ≤ C * (m : ℝ) ^ (-w.re) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set S : ℝ := ∑' n : ℕ, ‖LSeries.term f (σ₀ : ℂ) n‖ with hS
  have hSnn : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  refine ⟨(m : ℝ) ^ σ₀ * S, by positivity, fun w hw => ?_⟩
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f w n‖) :=
    hσ.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le_of_re_le hw n)
  have hbound : ∀ n : ℕ, (m : ℝ) ^ w.re * ‖LSeries.term f w n‖ ≤
      (m : ℝ) ^ σ₀ * ‖LSeries.term f (σ₀ : ℂ) n‖ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    by_cases hnm : n < m
    · rw [LSeries.term_of_ne_zero hn0.ne', hf n hn0 hnm, zero_div, norm_zero, mul_zero]
      positivity
    · push Not at hnm
      have hnR : (m : ℝ) ≤ n := by exact_mod_cast hnm
      have hnpos : (0 : ℝ) < n := by linarith
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn0.ne', if_neg hn0.ne',
        Complex.ofReal_re]
      have hexp : 0 ≤ w.re - σ₀ := by linarith
      have hratio : ((m : ℝ) / n) ^ (w.re - σ₀) ≤ 1 :=
        Real.rpow_le_one (by positivity) (div_le_one_of_le₀ hnR hnpos.le) hexp
      have hsplitpow : (m : ℝ) ^ w.re / (n : ℝ) ^ w.re =
          (m : ℝ) ^ σ₀ / (n : ℝ) ^ σ₀ * ((m : ℝ) / n) ^ (w.re - σ₀) := by
        rw [Real.div_rpow hmR.le hnpos.le, Real.rpow_sub hmR, Real.rpow_sub hnpos]
        field_simp
      calc (m : ℝ) ^ w.re * (‖f n‖ / (n : ℝ) ^ w.re)
          = ‖f n‖ * ((m : ℝ) ^ σ₀ / (n : ℝ) ^ σ₀ * ((m : ℝ) / n) ^ (w.re - σ₀)) := by
            rw [← hsplitpow]; ring
        _ ≤ ‖f n‖ * ((m : ℝ) ^ σ₀ / (n : ℝ) ^ σ₀ * 1) := by gcongr
        _ = (m : ℝ) ^ σ₀ * (‖f n‖ / (n : ℝ) ^ σ₀) := by ring
  have hsum2 : Summable (fun n : ℕ => (m : ℝ) ^ σ₀ * ‖LSeries.term f (σ₀ : ℂ) n‖) :=
    hσ.mul_left _
  have hmw : 0 < (m : ℝ) ^ w.re := Real.rpow_pos_of_pos hmR _
  have htot : (m : ℝ) ^ w.re * ‖LSeries f w‖ ≤ (m : ℝ) ^ σ₀ * S := by
    calc (m : ℝ) ^ w.re * ‖LSeries f w‖
        ≤ (m : ℝ) ^ w.re * ∑' n : ℕ, ‖LSeries.term f w n‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hmw.le
      _ = ∑' n : ℕ, (m : ℝ) ^ w.re * ‖LSeries.term f w n‖ := (tsum_mul_left).symm
      _ ≤ ∑' n : ℕ, (m : ℝ) ^ σ₀ * ‖LSeries.term f (σ₀ : ℂ) n‖ :=
          (hnorm.mul_left _).tsum_le_tsum hbound hsum2
      _ = (m : ℝ) ^ σ₀ * S := tsum_mul_left
  rw [Real.rpow_neg hmR.le, ← div_eq_mul_inv, le_div_iff₀ hmw, mul_comm]
  exact htot

/-- The first non-vanishing coefficient places `d (m/q)^{1/d}` in the shift spectrum. -/
theorem first_mem_shiftSpectrum {a : ℕ → ℂ} {m : ℕ} (hm : 0 < m) (ha : a m ≠ 0) (d q : ℝ) :
    d * ((m : ℝ) / q) ^ (1 / d) ∈ shiftSpectrum a d q :=
  ⟨m, hm, ha, rfl⟩

/-- **The cusp gap at the first non-vanishing coefficient.**  The distance from the cusp to the
shift spectrum is `d (m/q)^{1/d}`, with `m` the first index carrying a nonzero coefficient. -/
theorem infDist_zero_shiftSpectrum_of_first {a : ℕ → ℂ} {m : ℕ} (hm : 0 < m) (ha : a m ≠ 0)
    (hlt : ∀ n : ℕ, 0 < n → n < m → a n = 0) {d q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    Metric.infDist 0 (shiftSpectrum a d q) = d * ((m : ℝ) / q) ^ (1 / d) := by
  have hmem := first_mem_shiftSpectrum hm ha d q
  have hne : (shiftSpectrum a d q).Nonempty := ⟨_, hmem⟩
  refine le_antisymm ?_ ?_
  · have hle := Metric.infDist_le_dist_of_mem (x := (0 : ℝ)) hmem
    rwa [Real.dist_eq, zero_sub, abs_neg,
      abs_of_pos (shiftSpectrum_pos hd hq hmem)] at hle
  · refine (Metric.le_infDist hne).mpr fun y hy => ?_
    obtain ⟨n, hn, han, rfl⟩ := hy
    have hmn : m ≤ n := by
      by_contra h
      exact han (hlt n hn (by omega))
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hstep : ((m : ℝ) / q) ^ (1 / d) ≤ ((n : ℝ) / q) ^ (1 / d) :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
    have hpos : (0 : ℝ) < d * ((n : ℝ) / q) ^ (1 / d) :=
      shiftSpectrum_pos hd hq ⟨n, hn, han, rfl⟩
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left hstep hd.le

end GaloisForLFunctions.HTGeometry
