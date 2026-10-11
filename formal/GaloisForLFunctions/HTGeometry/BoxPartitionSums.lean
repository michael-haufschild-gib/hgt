import Mathlib

/-!
# Box partitions of point sums

Let `S` be a finite index set with points `y_n ∈ ℝ` and weights `ψ_n ≥ 0`. Spread each weight
uniformly over the box `[y_n − h, y_n + h]`; then `2h Σ ψ_n = ∫ Σ_n 1_{|y_n − t| ≤ h} ψ_n dt`.

**Theorem** (`box_partition_sum_le`). Suppose that:
* outside a set `Bad`, every weight whose box contains `t` is `≤ ε₁`;
* at every `t ∈ Bad`, the weights of the boxes containing `t` sum to at most `F(t)`.

Then `2h Σ ψ_n ≤ 2h ε₁ |S| + ∫ 1_Bad F`. Neither `Bad` nor `F` needs to be measurable: the bad part
enters through the lower integral `∫⁻ 1_Bad F`.

`volume_Icc_inter_lt_norm_le` is Chebyshev's inequality for a continuous `f` on `[A, B]`:
`|{t ∈ [A, B] : ‖f t‖ > Θ}| ≤ Θ⁻² ∫_A^B ‖f‖²`.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **The box partition bound.** -/
theorem box_partition_sum_le {S : Finset ℕ} {y ψ : ℕ → ℝ} {h ε₁ I : ℝ} (hh : 0 < h)
    (hψ : ∀ n, 0 ≤ ψ n) (hε : 0 ≤ ε₁) (hI0 : 0 ≤ I) (Bad : Set ℝ) (F : ℝ → ℝ)
    (hgood : ∀ t ∉ Bad, ∀ n ∈ S, |y n - t| ≤ h → ψ n ≤ ε₁)
    (hbad : ∀ t ∈ Bad, ∑ n ∈ S.filter (fun n => |y n - t| ≤ h), ψ n ≤ F t)
    (hI : ∫⁻ t, Bad.indicator (fun t => ENNReal.ofReal (F t)) t ≤ ENNReal.ofReal I) :
    2 * h * ∑ n ∈ S, ψ n ≤ 2 * h * ε₁ * S.card + I := by
  classical
  set box : ℕ → Set ℝ := fun n => Icc (y n - h) (y n + h) with hbox
  have hmem : ∀ n t, t ∈ box n ↔ |y n - t| ≤ h := by
    intro n t
    simp only [hbox, mem_Icc, abs_le]
    constructor <;> intro h' <;> constructor <;> linarith [h'.1, h'.2]
  have hmeas : ∀ n, MeasurableSet (box n) := fun n => measurableSet_Icc
  have hvol : ∀ n, volume (box n) = ENNReal.ofReal (2 * h) := by
    intro n; simp only [hbox, Real.volume_Icc]; ring_nf
  -- the weights as integrals
  have hlhs : ENNReal.ofReal (2 * h * ∑ n ∈ S, ψ n) =
      ∫⁻ t, ∑ n ∈ S, (box n).indicator (fun _ => ENNReal.ofReal (ψ n)) t := by
    rw [lintegral_finsetSum _ fun n _ => (measurable_const.indicator (hmeas n))]
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun n _ => by
      have := hψ n; positivity]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [lintegral_indicator_const (hmeas n), hvol, ← ENNReal.ofReal_mul (hψ n), mul_comm]
  -- the pointwise bound
  have hpt : (fun t => ∑ n ∈ S, (box n).indicator (fun _ => ENNReal.ofReal (ψ n)) t) ≤
      fun t => ∑ n ∈ S, (box n).indicator (fun _ => ENNReal.ofReal ε₁) t +
        Bad.indicator (fun t => ENNReal.ofReal (F t)) t := by
    intro t
    dsimp only
    by_cases ht : t ∈ Bad
    · refine le_add_left ?_
      rw [Set.indicator_of_mem ht]
      have e : ∑ n ∈ S, (box n).indicator (fun _ => ENNReal.ofReal (ψ n)) t =
          ENNReal.ofReal (∑ n ∈ S.filter (fun n => |y n - t| ≤ h), ψ n) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => hψ n, Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hn : |y n - t| ≤ h
        · rw [if_pos hn, Set.indicator_of_mem ((hmem n t).mpr hn)]
        · rw [if_neg hn, Set.indicator_of_notMem (fun h' => hn ((hmem n t).mp h'))]
      rw [e]
      exact ENNReal.ofReal_le_ofReal (hbad t ht)
    · refine le_add_right (Finset.sum_le_sum fun n hn => ?_)
      by_cases hb : t ∈ box n
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
        exact ENNReal.ofReal_le_ofReal (hgood t ht n hn ((hmem n t).mp hb))
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
  have hint := lintegral_mono (μ := volume) hpt
  rw [← hlhs, lintegral_add_left (Finset.measurable_sum _ fun n _ =>
    measurable_const.indicator (hmeas n)),
    lintegral_finsetSum _ fun n _ => (measurable_const.indicator (hmeas n))] at hint
  have hgoodpart : ∑ n ∈ S, ∫⁻ t, (box n).indicator (fun _ => ENNReal.ofReal ε₁) t =
      ENNReal.ofReal (2 * h * ε₁ * S.card) := by
    simp_rw [lintegral_indicator_const (hmeas _), hvol]
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [hgoodpart] at hint
  have h2 := hint.trans (add_le_add_right hI _)
  rw [← ENNReal.ofReal_add (by positivity) hI0] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2


/-- **Chebyshev on an interval.** -/
theorem volume_Icc_inter_lt_norm_le {f : ℝ → ℂ} (hf : Continuous f) {A B Θ : ℝ} (hAB : A ≤ B)
    (hΘ : 0 < Θ) :
    volume (Icc A B ∩ {t | Θ < ‖f t‖}) ≤
      ENNReal.ofReal ((∫ t in A..B, ‖f t‖ ^ 2) / Θ ^ 2) := by
  set μ := volume.restrict (Icc A B) with hμ
  set g : ℝ → ENNReal := fun t => ENNReal.ofReal (‖f t‖ ^ 2) with hg
  have hgm : Measurable g := ((hf.norm.pow 2).measurable).ennreal_ofReal
  have hmark := mul_meas_ge_le_lintegral₀ (μ := μ) hgm.aemeasurable (ENNReal.ofReal (Θ ^ 2))
  have hsub : {t | Θ < ‖f t‖} ⊆ {t | ENNReal.ofReal (Θ ^ 2) ≤ g t} := by
    intro t ht
    simp only [Set.mem_setOf_eq, hg] at ht ⊢
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hΘ.le ht.le 2)
  have hvol : volume (Icc A B ∩ {t | Θ < ‖f t‖}) ≤ μ {t | ENNReal.ofReal (Θ ^ 2) ≤ g t} := by
    rw [hμ, Measure.restrict_apply' measurableSet_Icc, Set.inter_comm]
    exact measure_mono (Set.inter_subset_inter_left _ hsub)
  have hint : ∫⁻ t, g t ∂μ = ENNReal.ofReal (∫ t in A..B, ‖f t‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hAB, ← integral_Icc_eq_integral_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal (μ := μ)
      ((hf.norm.pow 2).integrableOn_Icc)
      (Filter.Eventually.of_forall fun t => sq_nonneg ‖f t‖)).symm
  rw [hint] at hmark
  refine hvol.trans ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.le_div_iff_mul_le
    (Or.inl (by simp [hΘ.ne'])) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hmark

end GaloisForLFunctions.HTGeometry
