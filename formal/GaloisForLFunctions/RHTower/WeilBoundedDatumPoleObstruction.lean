import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence
import Mathlib.NumberTheory.LSeries.Basic

/-!
# A pole at `s = 1` forces an unbounded archimedean datum

Let `w : ℕ → ℝ` be absolutely summable and `u : ℕ → ℝ` arbitrary frequencies.  The series
`f(t) = Σ w_n e^{i t u_n}` returns arbitrarily close to its value `f(0) = Σ w_n` at arbitrarily
large times (`exists_large_apSeries_near`).  Hence an eventual upper bound `Re f(t) ≤ C` for large
`t` already bounds the total sum: `Σ w_n ≤ C` (`tsum_le_of_eventually_re_le`).

Applied to a Dirichlet series `L(s) = Σ_{n ≥ 1} a_n n^{-s}` with real coefficients on a vertical
line `Re s = σ` of absolute convergence (`w_n = a_n n^{-σ}`, `u_n = -log n`): if
`Re L(σ + it) ≤ C + Re (1/(σ + it - 1))` for all large `t`, then `L(σ) ≤ C`
(`dirichlet_value_le_of_bounded_datum`).  The pole term `Re 1/(s-1)` tends to `0` at large height, so
a datum that stays bounded at large height cannot carry a pole: if the bound holds on every line
`σ > 1`, then `L(σ)` is bounded above on `(1, ∞)` and in particular does not tend to `+∞` as
`σ → 1⁺` (`not_tendsto_atTop_of_bounded_datum`).

**Proof.** Truncate the series at `N` with tail mass `< ε/3`; the simultaneous recurrence of the
finitely many characters `e^{i t u_n}`, `n < N` (`exists_large_atomicSymbol_revival`) moves the
truncated sum within `ε/3` of its value at `t = 0`, at a time beyond any threshold.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.BoundedDatumPoleObstruction

open GaloisForLFunctions

/-- The almost periodic series `t ↦ Σ w_n e^{i t u_n}`. -/
def apSeries (w u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' n, (w n : ℂ) * cexp (I * ((t : ℂ) * (u n : ℂ)))

theorem norm_apTerm (w u : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ‖(w n : ℂ) * cexp (I * ((t : ℂ) * (u n : ℂ)))‖ = |w n| := by
  have h : I * ((t : ℂ) * (u n : ℂ)) = ((t * u n : ℝ) : ℂ) * I := by push_cast; ring
  rw [norm_mul, h, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem summable_apTerm {w : ℕ → ℝ} (hw : Summable fun n => |w n|) (u : ℕ → ℝ) (t : ℝ) :
    Summable fun n => (w n : ℂ) * cexp (I * ((t : ℂ) * (u n : ℂ))) :=
  Summable.of_norm_bounded hw fun n => (norm_apTerm w u t n).le

theorem summable_ofReal {w : ℕ → ℝ} (hw : Summable fun n => |w n|) :
    Summable fun n => (w n : ℂ) :=
  Summable.of_norm_bounded hw fun n => by rw [Complex.norm_real, Real.norm_eq_abs]

/-- **Recurrence of an absolutely summable almost periodic series.** At times beyond any threshold
the series returns within any tolerance of its value at the origin. -/
theorem exists_large_apSeries_near {w : ℕ → ℝ} (hw : Summable fun n => |w n|) (u : ℕ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ ξ : ℝ, R ≤ ξ ∧ ‖apSeries w u ξ - ∑' n, (w n : ℂ)‖ ≤ ε := by
  -- the tail of `Σ |w|`
  have htail := tendsto_sum_nat_add (fun n => |w n|)
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htail) (ε / 3) (by positivity)
  have hNt : ∑' k, |w (k + N)| < ε / 3 := by
    have := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hNt0 : 0 ≤ ∑' k, |w (k + N)| := tsum_nonneg fun k => abs_nonneg _
  have hws : Summable fun k => |w (k + N)| := (summable_nat_add_iff N).2 hw
  set S : ℝ := ∑ j : Fin N, ‖(w j : ℂ)‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  obtain ⟨ξ, hξR, hξ⟩ := exists_large_atomicSymbol_revival (fun j : Fin N => u j)
    (fun j : Fin N => (w j : ℂ)) (ε := ε / (3 * (S + 1))) (by positivity) R
  refine ⟨ξ, hξR, ?_⟩
  have hsf := summable_apTerm hw u ξ
  have hsw := summable_ofReal hw
  rw [apSeries, ← hsf.sum_add_tsum_nat_add N, ← hsw.sum_add_tsum_nat_add N,
    Finset.sum_range (fun i => (w i : ℂ) * cexp (I * ((ξ : ℂ) * (u i : ℂ)))),
    Finset.sum_range (fun i => (w i : ℂ))]
  have hsplit :
      (∑ j : Fin N, (w j : ℂ) * cexp (I * ((ξ : ℂ) * (u j : ℂ))) +
          ∑' k, (w (k + N) : ℂ) * cexp (I * ((ξ : ℂ) * (u (k + N) : ℂ)))) -
        (∑ j : Fin N, (w j : ℂ) + ∑' k, (w (k + N) : ℂ)) =
      ((∑ j : Fin N, (w j : ℂ) * cexp (I * ((ξ : ℂ) * (u j : ℂ)))) - ∑ j : Fin N, (w j : ℂ)) +
        (∑' k, (w (k + N) : ℂ) * cexp (I * ((ξ : ℂ) * (u (k + N) : ℂ))) -
          ∑' k, (w (k + N) : ℂ)) := by ring
  rw [hsplit]
  have h1 : ‖(∑ j : Fin N, (w j : ℂ) * cexp (I * ((ξ : ℂ) * (u j : ℂ)))) -
      ∑ j : Fin N, (w j : ℂ)‖ ≤ ε / 3 := by
    refine hξ.trans ?_
    rw [← hS]
    have : S * (ε / (3 * (S + 1))) = (ε / 3) * (S / (S + 1)) := by field_simp
    rw [this]
    have hq : S / (S + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith [hq, hε]
  have h2 : ‖∑' k, (w (k + N) : ℂ) * cexp (I * ((ξ : ℂ) * (u (k + N) : ℂ)))‖ ≤ ε / 3 := by
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa only [norm_apTerm] using hws
    · simp only [norm_apTerm]; exact hNt.le
  have h3 : ‖∑' k, (w (k + N) : ℂ)‖ ≤ ε / 3 := by
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hws
    · simp only [Complex.norm_real, Real.norm_eq_abs]; exact hNt.le
  calc _ ≤ ‖(∑ j : Fin N, (w j : ℂ) * cexp (I * ((ξ : ℂ) * (u j : ℂ)))) -
          ∑ j : Fin N, (w j : ℂ)‖ +
        ‖∑' k, (w (k + N) : ℂ) * cexp (I * ((ξ : ℂ) * (u (k + N) : ℂ))) -
          ∑' k, (w (k + N) : ℂ)‖ := norm_add_le _ _
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add h2 h3)
    _ = ε := by ring

/-- **An eventual upper bound on the real part bounds the total sum.** If for every `ε > 0` the
real part of `Σ w_n e^{i t u_n}` is eventually at most `C + ε`, then `Σ w_n ≤ C`. -/
theorem tsum_le_of_eventually_re_le {w : ℕ → ℝ} (hw : Summable fun n => |w n|) (u : ℕ → ℝ)
    {C : ℝ} (h : ∀ ε > 0, ∃ T : ℝ, ∀ t, T ≤ t → (apSeries w u t).re ≤ C + ε) :
    ∑' n, w n ≤ C := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨T, hT⟩ := h (ε / 2) (by positivity)
  obtain ⟨ξ, hξT, hξ⟩ := exists_large_apSeries_near hw u (ε := ε / 2) (by positivity) T
  have hre : (∑' n, (w n : ℂ)).re = ∑' n, w n := by
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hclose : (∑' n, (w n : ℂ)).re ≤ (apSeries w u ξ).re + ε / 2 := by
    have := Complex.re_le_norm (∑' n, (w n : ℂ) - apSeries w u ξ)
    rw [Complex.sub_re, norm_sub_rev] at this
    linarith
  have := hT ξ hξT
  linarith

/-! ## Dirichlet series on a vertical line -/

/-- The real part of `1/(σ + it - 1)` is at most `(σ - 1)/t²` for `σ > 1`, `t ≠ 0`. -/
theorem re_inv_le {σ t : ℝ} (hσ : 1 < σ) (ht : t ≠ 0) :
    (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re ≤ (σ - 1) / t ^ 2 := by
  have hz : ((σ : ℂ) + (t : ℂ) * I - 1) = ((σ - 1 : ℝ) : ℂ) + (t : ℂ) * I := by push_cast; ring
  rw [hz, one_div, Complex.inv_re, Complex.normSq_add_mul_I]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, mul_one]
  have hσ1 : 0 < σ - 1 := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) ht2]
  nlinarith [sq_nonneg (σ - 1)]

/-- **Bounded datum at large height bounds the Dirichlet value.** Let `w_n = a_n n^{-σ}` be the
absolutely summable weights of a real Dirichlet series on the line `Re s = σ > 1`, written as
`L(σ + it) = Σ w_n e^{-it log n}`. If `Re L(σ + it) ≤ C + Re (1/(σ + it - 1))` for all `t ≥ T₀`,
then `L(σ) = Σ w_n ≤ C`. -/
theorem dirichlet_value_le_of_bounded_datum {w : ℕ → ℝ} (hw : Summable fun n => |w n|)
    {σ C T₀ : ℝ} (hσ : 1 < σ)
    (h : ∀ t, T₀ ≤ t →
      (apSeries w (fun n => -Real.log n) t).re ≤ C + (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re) :
    ∑' n, w n ≤ C := by
  refine tsum_le_of_eventually_re_le hw (fun n => -Real.log n) fun ε hε => ?_
  refine ⟨max (max T₀ 1) (Real.sqrt ((σ - 1) / ε)), fun t ht => ?_⟩
  have hT₀ : T₀ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht1 : 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have hts : Real.sqrt ((σ - 1) / ε) ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : t ≠ 0 := by linarith
  have hpole := re_inv_le hσ ht0
  have hsq : (σ - 1) / ε ≤ t ^ 2 := by
    have h0 : 0 ≤ (σ - 1) / ε := div_nonneg (by linarith) hε.le
    calc (σ - 1) / ε = Real.sqrt ((σ - 1) / ε) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ t ^ 2 := by
          have := Real.sqrt_nonneg ((σ - 1) / ε)
          nlinarith
  have hsmall : (σ - 1) / t ^ 2 ≤ ε := by
    have ht2 : 0 < t ^ 2 := by positivity
    rw [div_le_iff₀ ht2]
    rw [div_le_iff₀ hε] at hsq
    linarith
  linarith [h t hT₀]

/-- **A bounded datum cannot carry the pole.** If on every line `Re s = σ > 1` the real Dirichlet
series `L(σ + it) = Σ w_σ(n) e^{-it log n}` (absolutely summable weights `w_σ`) obeys
`Re L(σ + it) ≤ C + Re (1/(σ + it - 1))` at all large heights, then `σ ↦ L(σ)` is bounded above by
`C` on `(1, ∞)`; in particular it does not tend to `+∞` as `σ → 1⁺`. -/
theorem not_tendsto_atTop_of_bounded_datum {w : ℝ → ℕ → ℝ}
    (hw : ∀ σ : ℝ, 1 < σ → Summable fun n => |w σ n|) {C : ℝ}
    (h : ∀ σ : ℝ, 1 < σ → ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      (apSeries (w σ) (fun n => -Real.log n) t).re ≤ C + (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re) :
    ¬ Tendsto (fun σ => ∑' n, w σ n) (𝓝[>] 1) atTop := by
  intro htend
  have hev : ∀ᶠ σ in 𝓝[>] (1 : ℝ), C + 1 ≤ ∑' n, w σ n := htend.eventually_ge_atTop (C + 1)
  have hmem : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ := self_mem_nhdsWithin
  obtain ⟨σ, hσC, hσ1⟩ := (hev.and hmem).exists
  obtain ⟨T₀, hT₀⟩ := h σ hσ1
  have := dirichlet_value_le_of_bounded_datum (hw σ hσ1) hσ1 hT₀
  linarith

/-! ## The `LSeries` form -/

/-- On the line `Re s = σ > 0`, the terms of a real `LSeries` are the terms of the almost periodic
series with weights `a_n n^{-σ}` and frequencies `-log n`. -/
theorem lseries_term_eq (a : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) ((σ : ℂ) + (t : ℂ) * I) n =
      ((a n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * cexp (I * ((t : ℂ) * ((-Real.log n : ℝ) : ℂ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term, Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_def_of_ne_zero hn0]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnr.le]
    rw [hlog, Real.rpow_def_of_pos hnr]
    push_cast
    rw [div_eq_mul_inv, ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
    congr 2
    ring

theorem lseries_eq_apSeries (a : ℕ → ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    LSeries (fun n => (a n : ℂ)) ((σ : ℂ) + (t : ℂ) * I) =
      apSeries (fun n => a n * (n : ℝ) ^ (-σ)) (fun n => -Real.log n) t := by
  rw [LSeries, apSeries]
  exact tsum_congr fun n => lseries_term_eq a hσ t n

/-- **`LSeries` form.** A real Dirichlet series absolutely convergent on `Re s = σ > 1` whose real
part satisfies `Re L(σ + it) ≤ C + Re (1/(σ + it - 1))` at all large heights has `L(σ) ≤ C`. -/
theorem lseries_re_le_of_bounded_datum (a : ℕ → ℝ) {σ C T₀ : ℝ} (hσ : 1 < σ)
    (hs : Summable fun n => |a n * (n : ℝ) ^ (-σ)|)
    (h : ∀ t, T₀ ≤ t → (LSeries (fun n => (a n : ℂ)) ((σ : ℂ) + (t : ℂ) * I)).re ≤
      C + (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re) :
    (LSeries (fun n => (a n : ℂ)) (σ : ℂ)).re ≤ C := by
  have hσ0 : 0 < σ := by linarith
  have h0 : LSeries (fun n => (a n : ℂ)) (σ : ℂ) =
      LSeries (fun n => (a n : ℂ)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) := by simp
  rw [h0, lseries_eq_apSeries a hσ0 0]
  have hap0 : apSeries (fun n => a n * (n : ℝ) ^ (-σ)) (fun n => -Real.log n) 0 =
      ∑' n, ((a n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [apSeries]; exact tsum_congr fun n => by simp
  rw [hap0, ← Complex.ofReal_tsum, Complex.ofReal_re]
  refine dirichlet_value_le_of_bounded_datum hs hσ (T₀ := T₀) fun t ht => ?_
  rw [← lseries_eq_apSeries a hσ0 t]
  exact h t ht

/-- **No integer pole carrier for a bounded datum.** Let `a : ℕ → ℝ` have a Dirichlet series
absolutely convergent on every line `Re s = σ > 1`. If on every such line
`Re L(σ + it) ≤ C + Re (1/(σ + it - 1))` holds at all large heights, then `L(σ)` does not tend to
`+∞` as `σ → 1⁺`: the series cannot carry a pole of positive residue at `s = 1`. -/
theorem not_tendsto_lseries_atTop_of_bounded_datum (a : ℕ → ℝ) {C : ℝ}
    (hs : ∀ σ : ℝ, 1 < σ → Summable fun n => |a n * (n : ℝ) ^ (-σ)|)
    (h : ∀ σ : ℝ, 1 < σ → ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t →
      (LSeries (fun n => (a n : ℂ)) ((σ : ℂ) + (t : ℂ) * I)).re ≤
        C + (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re) :
    ¬ Tendsto (fun σ : ℝ => (LSeries (fun n => (a n : ℂ)) (σ : ℂ)).re) (𝓝[>] 1) atTop := by
  intro htend
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), C + 1 ≤ (LSeries (fun n => (a n : ℂ)) (σ : ℂ)).re :=
    htend.eventually_ge_atTop (C + 1)
  have hmem : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 1 < σ := self_mem_nhdsWithin
  obtain ⟨σ, hσC, hσ1⟩ := (hev.and hmem).exists
  obtain ⟨T₀, hT₀⟩ := h σ hσ1
  have := lseries_re_le_of_bounded_datum a hσ1 (hs σ hσ1) hT₀
  linarith

end RHTower.BoundedDatumPoleObstruction
