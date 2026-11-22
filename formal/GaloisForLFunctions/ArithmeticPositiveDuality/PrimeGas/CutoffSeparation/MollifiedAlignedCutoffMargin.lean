import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.BilateralReflectionRigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.HighOrdinateMarginAdvances
import GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZerosOfTheMollifierCondense

/-!
# Constructive mollified aligned cutoff margins and the Hurwitz–Jentzsch boundary

In `BilateralReflectionRigidity`, finite-support Dirichlet convolution weights
`dirichletSurgWeight M c` (`c 1 = 1`) were introduced to classify surgery obstructions and prove
two-prime germ rigidity. Here we turn `tendsto_weightedAlignedReconstructed_dirichletSurgWeight`
into a constructive high-ordinate mollified cutoff mechanism and establish its exact Hurwitz–Jentzsch
zero-condensation boundary:

1. **Pole-free, `|ζ|`-free mollified aligned reconstruction (`mollifiedAlignedReconstructed`)**:
   coupling `dirichletSurgPoly M c w` to `alignedReconstructedCutoff K w` gives an explicit
   `|ζ|`-free error bound `mollifiedAlignedError M c K w` across all `Re w > 0` (including `w = 1`),
   asymptotic agreement with `weightedAlignedReconstructed (dirichletSurgWeight M c) K w`,
   **zero-exception** pointwise transfer from a single mollified shell margin to `ζ(w) ≠ 0` and an
   actual unmollified `renormalizedCutoff` margin, and an exact equivalence with `RiemannHypothesis`
   above Bohman height `169/2`.
2. **Truncated Möbius mollifier (`moebiusReal`) and power-saving high-ordinate margin
   (`moebius_mollifier_powerSaving_highOrdinate_margin`)**:
   the prime-gas weight `dirichletSurgWeight M moebiusReal` annihilates every `2 ≤ n ≤ M` while
   keeping `n = 1` at unit weight. Using the `L²` three-lines estimate on `mobMollifiedError`, for
   every `1/2 < σ ≤ 1`, `U ≥ e^100`, `M = ⌊U^{1/4}⌋₊`, and `[T₁, T₂] ⊂ (U/4, U/2)`, outside an
   exceptional ordinate set of measure `O((log U)^5 U^{1 - (σ - 1/2)/5})`, the mollified reading
   `‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K (σ + i t)‖` stays bounded
   below by `t / 4` (`≥ U / 16`) for large `K` — defeating Voronin small-value collapse of `ζ` — and
   certifies both mollified and actual `renormalizedCutoff` margins.
3. **Sharp Hurwitz–Jentzsch boundary on the zero abscissa `1/2 + zetaZeroWidth`**:
   right of `1/2 + zetaZeroWidth` away from `1`, every compact set eventually has a **zero-exception**
   Möbius-mollified margin (`hurwitz_uniform_mollified_margin_right_of_abscissa`); on
   `Re s = 1/2 + zetaZeroWidth`, every disc contains zeros of `dirichletSurgPoly M moebiusReal` for
   arbitrarily large `M` where `mollifiedAlignedReconstructed` vanishes identically and
   `weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K z → 0`
   (`jentzsch_moebius_mollified_extinction_near_abscissa`).
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Complex Filter MeasureTheory Set Metric
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth)
open scoped Topology ComplexConjugate

/-! ### Part 1: Constructive mollified aligned shell readings and zero-exception margin transfer -/

/-- Finite Dirichlet-mollified two-prime aligned shell reading `Q_{M,c}(w) · R_K(w)`. -/
def mollifiedAlignedReconstructed (M : ℕ) (c : ℕ → ℝ) (K : ℕ) (w : ℂ) : ℂ :=
  dirichletSurgPoly M c w * alignedReconstructedCutoff K w

/-- Explicit `|ζ(w)|`-free, pole-free truncation bound for `mollifiedAlignedReconstructed`,
continuous across `Re w > 0` including `w = 1`. -/
def mollifiedAlignedError (M : ℕ) (c : ℕ → ℝ) (K : ℕ) (w : ℂ) : ℝ :=
  ‖dirichletSurgPoly M c w‖ * alignedReconstructionError K w

/-- Pole-free, `|ζ|`-free error bound for `mollifiedAlignedReconstructed` across all `Re w > 0`
(including `w = 1`) and all `K ≥ 1`. -/
theorem norm_mollifiedAlignedReconstructed_sub_le (M : ℕ) (c : ℕ → ℝ)
    {K : ℕ} (hK : 1 ≤ K) {w : ℂ} (hw : 0 < w.re) :
    ‖mollifiedAlignedReconstructed M c K w -
        dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ ≤
      mollifiedAlignedError M c K w := by
  unfold mollifiedAlignedReconstructed mollifiedAlignedError
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_alignedReconstructedCutoff_sub_le hK hw) (norm_nonneg _)

theorem tendsto_mollifiedAlignedError_zero (M : ℕ) (c : ℕ → ℝ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ => mollifiedAlignedError M c K w) atTop (𝓝 0) := by
  unfold mollifiedAlignedError
  simpa only [mul_zero] using
    (tendsto_alignedReconstructionError_zero hw).const_mul ‖dirichletSurgPoly M c w‖

theorem tendsto_mollifiedAlignedReconstructed (M : ℕ) (c : ℕ → ℝ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ => mollifiedAlignedReconstructed M c K w) atTop
      (𝓝 (dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w)) := by
  have hsub : Tendsto (fun K : ℕ => mollifiedAlignedReconstructed M c K w -
      dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_mollifiedAlignedError_zero M c hw)
    filter_upwards [eventually_ge_atTop 1] with K hK
    exact norm_mollifiedAlignedReconstructed_sub_le M c hK hw
  have hadd := hsub.add (tendsto_const_nhds (x := dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w))
  rw [zero_add] at hadd
  exact hadd.congr fun _ => sub_add_cancel _ _

/-- Direct shell-reading coupling: the `dirichletSurgWeight M c`-weighted prime-gas shell reading
`weightedAlignedReconstructed (dirichletSurgWeight M c) K w` and `mollifiedAlignedReconstructed M c K w`
have vanishing asymptotic difference across all `Re w > 0`. -/
theorem tendsto_weightedAlignedReconstructed_sub_mollifiedAligned_zero
    (M : ℕ) (c : ℕ → ℝ) {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun K : ℕ =>
      weightedAlignedReconstructed (dirichletSurgWeight M c) K w -
        mollifiedAlignedReconstructed M c K w) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (tendsto_weightedAlignedReconstructed_dirichletSurgWeight M c hw).sub
      (tendsto_mollifiedAlignedReconstructed M c hw)

/-- **Zero-exception pointwise margin transfer:** a single mollified shell cutoff `K₀ ≥ 1` beating
`mollifiedAlignedError M c K₀ w` forces `ζ(w) ≠ 0`, `Q_{M,c}(w) ≠ 0`, an eventual positive floor on
`weightedAlignedReconstructed (dirichletSurgWeight M c) K w`, and an actual unmollified
`renormalizedCutoff` margin for every prime clock `(t, j)`. -/
theorem mollified_margin_forces_actual_cutoff_margin (M : ℕ) (c : ℕ → ℝ)
    {K₀ : ℕ} (hK₀ : 1 ≤ K₀) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (hmarg : mollifiedAlignedError M c K₀ w < ‖mollifiedAlignedReconstructed M c K₀ w‖) :
    riemannZeta w ≠ 0 ∧
      dirichletSurgPoly M c w ≠ 0 ∧
      (∀ᶠ K : ℕ in atTop,
        ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ / 2 ≤
          ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖) ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  have herr := norm_mollifiedAlignedReconstructed_sub_le M c hK₀ hw
  have hlim_pos : 0 < ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ := by
    have htri := norm_sub_norm_le (mollifiedAlignedReconstructed M c K₀ w)
      (dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w)
    -- `htri` and `herr` bound the same difference norm.
    linarith [htri, herr, hmarg]
  have hprod_ne : dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w ≠ 0 :=
    norm_pos_iff.mp hlim_pos
  have hQ_ne : dirichletSurgPoly M c w ≠ 0 := left_ne_zero_of_mul hprod_ne
  have hZ_ne : _root_.RHTower.zetaPoleUnit w ≠ 0 := right_ne_zero_of_mul hprod_ne
  have hzeta_ne : riemannZeta w ≠ 0 := by
    rw [_root_.RHTower.zetaPoleUnit_of_ne hw1] at hZ_ne
    exact right_ne_zero_of_mul hZ_ne
  have hnorm_lim := (tendsto_weightedAlignedReconstructed_dirichletSurgWeight M c hw).norm
  have hfloor : ∀ᶠ K : ℕ in atTop,
      ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ / 2 ≤
        ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖ := by
    filter_upwards [hnorm_lim.eventually
      (Ioi_mem_nhds (by linarith : ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ / 2 <
        ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖))] with _ hK
    exact le_of_lt hK
  exact ⟨hzeta_ne, hQ_ne, hfloor, fun t j =>
    (exists_zetaFree_margin_iff_zeta_ne_zero t j hw hw1).mpr hzeta_ne⟩

/-- **Constructive dampened-oscillation cutoff margin:** whenever `‖ζ(w) Q_{M,c}(w) - 1‖ ≤ θ < 1`
at `w` (`Re w > 0`, `w ≠ 1`), the mollified limit has magnitude `≥ (1 - θ) ‖w - 1‖` (linear in
`|Im w|` at high ordinate), `weightedAlignedReconstructed (dirichletSurgWeight M c) K w` stays
bounded below by `(1 - θ) / 2 * ‖w - 1‖` for all large `K`, and both mollified and unmollified
strict cutoff margins hold at `w`. -/
theorem dampened_mollifier_forces_weightedAligned_floor_and_margin
    (M : ℕ) (c : ℕ → ℝ) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) {θ : ℝ} (hθ : θ < 1)
    (hdamp : ‖riemannZeta w * dirichletSurgPoly M c w - 1‖ ≤ θ) :
    (1 - θ) * ‖w - 1‖ ≤ ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ ∧
      (∀ᶠ K : ℕ in atTop,
        (1 - θ) / 2 * ‖w - 1‖ ≤
          ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖) ∧
      (∃ K₀ : ℕ, 1 ≤ K₀ ∧
        mollifiedAlignedError M c K₀ w < ‖mollifiedAlignedReconstructed M c K₀ w‖) ∧
      ∀ (t : ExceptionalTime) (j : ℕ),
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ zetaFreeTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  have hw_sub_pos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  have h1_sub : 1 - θ ≤ ‖riemannZeta w * dirichletSurgPoly M c w‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (riemannZeta w * dirichletSurgPoly M c w)
    rw [norm_one, norm_sub_rev] at htri
    linarith [htri, hdamp]
  have hid : dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w =
      (w - 1) * (riemannZeta w * dirichletSurgPoly M c w) := by
    rw [_root_.RHTower.zetaPoleUnit_of_ne hw1]; ring
  have hlim_ge : (1 - θ) * ‖w - 1‖ ≤ ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ := by
    rw [hid, norm_mul, mul_comm ‖w - 1‖]
    exact mul_le_mul_of_nonneg_right h1_sub hw_sub_pos.le
  have hpos_floor : 0 < (1 - θ) / 2 * ‖w - 1‖ := mul_pos (by linarith) hw_sub_pos
  have hlt_lim : (1 - θ) / 2 * ‖w - 1‖ <
      ‖dirichletSurgPoly M c w * _root_.RHTower.zetaPoleUnit w‖ := by
    have : (1 - θ) / 2 * ‖w - 1‖ < (1 - θ) * ‖w - 1‖ :=
      mul_lt_mul_of_pos_right (by linarith) hw_sub_pos
    exact this.trans_le hlim_ge
  have hw_lim := (tendsto_weightedAlignedReconstructed_dirichletSurgWeight M c hw).norm
  have hfloor : ∀ᶠ K : ℕ in atTop,
      (1 - θ) / 2 * ‖w - 1‖ ≤ ‖weightedAlignedReconstructed (dirichletSurgWeight M c) K w‖ := by
    filter_upwards [hw_lim.eventually (Ioi_mem_nhds hlt_lim)] with _ hK
    exact le_of_lt hK
  have hm_lim := (tendsto_mollifiedAlignedReconstructed M c hw).norm
  have herr_lim := tendsto_mollifiedAlignedError_zero M c hw
  obtain ⟨K₀, ⟨hK1, herr_small⟩, hm_large⟩ :=
    (((eventually_ge_atTop 1).and (herr_lim.eventually (Iio_mem_nhds hpos_floor))).and
      (hm_lim.eventually (Ioi_mem_nhds hlt_lim))).exists
  have hmarg : mollifiedAlignedError M c K₀ w < ‖mollifiedAlignedReconstructed M c K₀ w‖ :=
    herr_small.trans hm_large
  exact ⟨hlim_ge, hfloor, ⟨K₀, hK1, hmarg⟩,
    (mollified_margin_forces_actual_cutoff_margin M c hK1 hw hw1 hmarg).2.2.2⟩

/-- Exact zero-exception equivalence between `RiemannHypothesis` and the existence of a normalized
finite Dirichlet mollifier (`c 1 = 1`) with a strict mollified aligned cutoff margin above Bohman
height `169/2 = 84.5`. -/
theorem rh_iff_mollified_aligned_margin_above_eightyFour_and_half :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 20999 / 24000 → 169 / 2 < |w.im| →
        ∃ M : ℕ, ∃ c : ℕ → ℝ, c 1 = 1 ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
          mollifiedAlignedError M c K₀ w < ‖mollifiedAlignedReconstructed M c K₀ w‖ := by
  rw [rh_iff_zetaFree_margin_above_eightyFour_and_half halfTurnClock 0]
  constructor
  · intro hRH w hlo hhi him
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    have hzeta_ne : riemannZeta w ≠ 0 :=
      (exists_zetaFree_margin_iff_zeta_ne_zero halfTurnClock 0 hw0 hw1).mp (hRH w hlo hhi him)
    have hQ1 : dirichletSurgPoly 1 (fun _ => 1) w = 1 := by
      simp [dirichletSurgPoly]
    have hZ_pos : 0 < ‖dirichletSurgPoly 1 (fun _ => 1) w * _root_.RHTower.zetaPoleUnit w‖ := by
      rw [hQ1, one_mul, _root_.RHTower.zetaPoleUnit_of_ne hw1]
      exact norm_pos_iff.mpr (mul_ne_zero (sub_ne_zero.mpr hw1) hzeta_ne)
    have hm_lim := (tendsto_mollifiedAlignedReconstructed 1 (fun _ => 1) hw0).norm
    have herr_lim := tendsto_mollifiedAlignedError_zero 1 (fun _ => 1) hw0
    obtain ⟨K₀, ⟨hK1, herr_small⟩, hm_large⟩ :=
      (((eventually_ge_atTop 1).and
        (herr_lim.eventually (Iio_mem_nhds (half_pos hZ_pos)))).and
        (hm_lim.eventually (Ioi_mem_nhds (half_lt_self hZ_pos)))).exists
    exact ⟨1, fun _ => 1, rfl, K₀, hK1, herr_small.trans hm_large⟩
  · intro hmol w hlo hhi him
    have hw0 : 0 < w.re := by linarith
    have hw_lt1 : w.re < 1 := by linarith
    have hw1 : w ≠ 1 := fun he => hw_lt1.ne (by rw [he, Complex.one_re])
    obtain ⟨M, c, -, K₀, hK1, hmarg⟩ := hmol w hlo hhi him
    exact (mollified_margin_forces_actual_cutoff_margin M c hK1 hw0 hw1 hmarg).2.2.2 halfTurnClock 0

/-! ### Part 2: Truncated Möbius prime-gas mollifier and power-saving high-ordinate margin -/

/-- Real Möbius arithmetic coefficients `d ↦ (μ(d) : ℝ)` for `dirichletSurgWeight`. -/
def moebiusReal (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ)

theorem moebiusReal_one : moebiusReal 1 = 1 := by simp [moebiusReal]

/-- **Exact prime-gas head annihilation:** for `1 ≤ n ≤ M`, `dirichletSurgWeight M moebiusReal n`
equals `1` at `n = 1` and `0` on every prime and composite `2 ≤ n ≤ M`. -/
theorem dirichletSurgWeight_moebiusReal_of_le {M n : ℕ} (hn1 : 1 ≤ n) (hnM : n ≤ M) :
    dirichletSurgWeight M moebiusReal n = if n = 1 then 1 else 0 := by
  unfold dirichletSurgWeight moebiusReal
  have hsum : (∑ d ∈ Finset.Icc 1 M, if d ∣ n then (ArithmeticFunction.moebius d : ℝ) else 0) =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2, by omega⟩, fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn1,
      (Nat.le_of_dvd hn1 h.1).trans hnM⟩, h.1⟩⟩
  rw [hsum]
  have hmob := _root_.RHTower.sum_divisors_mobCoeff n
  apply Complex.ofReal_injective
  have h1 : ((∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) : ℝ) : ℂ) =
      ∑ d ∈ n.divisors, _root_.RHTower.mobCoeff d := by
    unfold _root_.RHTower.mobCoeff; push_cast; rfl
  rw [h1, hmob]
  split_ifs <;> simp

theorem dirichletSurgPoly_moebiusReal_eq_edPoly (M : ℕ) (w : ℂ) :
    dirichletSurgPoly M moebiusReal w =
      _root_.RHTower.edPoly _root_.RHTower.mobCoeff (Finset.Icc 1 M) w := by
  unfold dirichletSurgPoly moebiusReal _root_.RHTower.edPoly _root_.RHTower.mobCoeff
  refine Finset.sum_congr rfl fun d _ => ?_
  push_cast; rfl

theorem dirichletSurgPoly_moebiusReal_eq_moebiusPoly (M : ℕ) (w : ℂ) :
    dirichletSurgPoly M moebiusReal w = MultiscaleMollifiedZetaField.moebiusPoly M w :=
  dirichletSurgPoly_moebiusReal_eq_edPoly M w

private theorem continuous_clamped_mobMollifiedError_normSq (M : ℕ) {σ T₁ T₂ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hT₁ : 1 ≤ T₁) (hT : T₁ ≤ T₂) :
    Continuous fun t : ℝ =>
      ‖_root_.RHTower.mobMollifiedError M
        ((σ : ℂ) + ((max T₁ (min t T₂) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  let z (t : ℝ) : ℂ := (σ : ℂ) + ((max T₁ (min t T₂) : ℝ) : ℂ) * Complex.I
  have hz_cont : Continuous z := by unfold z; fun_prop
  have hz_re : ∀ t : ℝ, 0 < (z t).re := fun t => by simp [z]; linarith
  have hz_im : ∀ t : ℝ, 1 ≤ (z t).im := fun t => by
    have him : (z t).im = max T₁ (min t T₂) := by simp [z]
    rw [him]
    exact hT₁.trans (le_max_left _ _)
  have hz_ne0 : ∀ t : ℝ, z t ≠ 0 := fun t h => by have := hz_re t; simp [h] at this
  have hz_ne1 : ∀ t : ℝ, z t ≠ 1 := fun t h => by have := hz_im t; simp [h] at this; linarith
  have heq : (fun t : ℝ => _root_.RHTower.mobMollifiedError M (z t)) =
      fun t : ℝ => z t / (z t - 1) * _root_.RHTower.mobField M (z t) := by
    funext t
    have hf := _root_.RHTower.mobField_eq (X := M) (hz_ne0 t) (hz_ne1 t)
    have hsub : z t - 1 ≠ 0 := sub_ne_zero.mpr (hz_ne1 t)
    rw [hf]
    field_simp [hsub, hz_ne0 t]
  have hcont_field : Continuous fun t : ℝ => _root_.RHTower.mobField M (z t) :=
    (_root_.RHTower.differentiableOn_mobField M).continuousOn.comp_continuous hz_cont hz_re
  have hcont_rat : Continuous fun t : ℝ => z t / (z t - 1) :=
    hz_cont.div (hz_cont.sub continuous_const) fun t => sub_ne_zero.mpr (hz_ne1 t)
  have hcont_err : Continuous fun t : ℝ => _root_.RHTower.mobMollifiedError M (z t) := by
    rw [heq]; exact hcont_rat.mul hcont_field
  exact (continuous_pow 2).comp hcont_err.norm

/-- **Power-saving high-ordinate mollified cutoff margin:** for every `1/2 < σ ≤ 1`, scale
`U ≥ exp 100`, Möbius cutoff `M = ⌊U^{1/4}⌋₊`, and interval `[T₁, T₂] ⊂ (U/4, U/2)` (`T₁ ≤ T₂`),
the `L²` oscillation of `ζ(σ + i t) Q_{M,μ}(σ + i t) - 1` is `O((log U)^5 U^{1 - (σ - 1/2)/5})`,
and outside an exceptional set of measure `≤ 4 B_mob (log U + 2)^5 U^{1 - (σ - 1/2)/5}`, every
ordinate `t ∈ [T₁, T₂]` has linear-in-`t` shell reading floor `≥ t / 4` and strict mollified and
unmollified cutoff margins. -/
theorem moebius_mollifier_powerSaving_highOrdinate_margin :
    ∃ B_mob : ℝ, 0 < B_mob ∧
      ∀ {σ U T₁ T₂ : ℝ}, 1 / 2 < σ → σ ≤ 1 → Real.exp 100 ≤ U →
        U / 4 < T₁ → T₁ ≤ T₂ → T₂ < U / 2 →
        let M : ℕ := ⌊U ^ (1 / 4 : ℝ)⌋₊
        let badSet : Set ℝ := {t ∈ Icc T₁ T₂ |
          (1 / 2 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
            dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖}
        (∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
            dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 ≤
          B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (σ - 1 / 2) / 5)) ∧
        MeasurableSet badSet ∧
        (volume badSet).toReal ≤
          4 * B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (σ - 1 / 2) / 5) ∧
        ∀ t ∈ Icc T₁ T₂ \ badSet,
          (∀ᶠ K : ℕ in atTop,
            t / 4 ≤ ‖weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K
              ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ∧
          (∃ K₀ : ℕ, 1 ≤ K₀ ∧
            mollifiedAlignedError M moebiusReal K₀ ((σ : ℂ) + (t : ℂ) * Complex.I) <
              ‖mollifiedAlignedReconstructed M moebiusReal K₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖) ∧
          ∀ (tc : ExceptionalTime) (j : ℕ),
            ∃ X₀ : ℕ, 1 ≤ X₀ ∧
              zetaFreeTruncationBound tc j X₀ ((σ : ℂ) + (t : ℂ) * Complex.I) <
                ‖renormalizedCutoff tc j X₀ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨C, D, hC, hD, h3⟩ := _root_.RHTower.exists_integral_normSq_mobMollifiedError_le_threeLines
  set B_mob : ℝ := 4 * max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256
  have hB_pos : 0 < B_mob := by
    have : (256 : ℝ) ≤ max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256 := le_max_right _ _
    dsimp only [B_mob]; linarith
  refine ⟨B_mob, hB_pos, fun {σ U T₁ T₂} hσ hσ1 hU hT₁ hT hT₂ => ?_⟩
  dsimp only
  have hU_pos : 0 < U := (Real.exp_pos 100).trans_le hU
  set L : ℝ := Real.log U
  have hL100 : 100 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 100) hU
  have hEL : Real.exp L = U := Real.exp_log hU_pos
  set M : ℕ := ⌊U ^ (1 / 4 : ℝ)⌋₊
  have hU14 : U ^ (1 / 4 : ℝ) = Real.exp (L / 4) := by
    rw [← hEL, ← Real.exp_mul]; congr 1; ring
  have hM_le : (M : ℝ) ≤ Real.exp (L / 4) := by
    rw [← hU14]; exact Nat.floor_le (by positivity)
  have hM_gt : Real.exp (L / 4) - 1 < M := by
    rw [← hU14]; have := Nat.lt_floor_add_one (U ^ (1 / 4 : ℝ)); linarith
  set N : ℕ := ⌊Real.exp L * (L + 2)⌋₊
  have hN_le : (N : ℝ) ≤ Real.exp L * (L + 2) := Nat.floor_le (by positivity)
  have hN_gt : Real.exp L * (L + 2) - 1 < N := by
    have := Nat.lt_floor_add_one (Real.exp L * (L + 2)); linarith
  set δ : ℝ := 2 * (σ - 1 / 2)
  have hδ0 : 0 < δ := by dsimp only [δ]; linarith
  have hδ1 : δ ≤ 1 := by dsimp only [δ]; linarith
  have hσ_eq : 1 / 2 + δ / 2 = σ := by dsimp only [δ]; ring
  have hpow_err := _root_.RHTower.powerSaving_error_le hC hD hL100 hδ0 hδ1 h3
    hM_le hM_gt hN_le hN_gt (by rwa [hEL]) hT (by rwa [hEL])
  have hrhs_eq : 4 * (max (16 * Real.sqrt (160 * D + 1) + 32 + 96 * C ^ 2) 256 * (L + 2) ^ 5) *
        Real.exp (L * (1 - δ / 10)) =
      B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (σ - 1 / 2) / 5) := by
    have hexp_u : Real.exp (L * (1 - δ / 10)) = U ^ (1 - (σ - 1 / 2) / 5) := by
      rw [Real.rpow_def_of_pos hU_pos]
      congr 1; dsimp only [L, δ]; ring
    rw [hexp_u]
    dsimp only [B_mob, L]
    ring
  rw [hσ_eq, hrhs_eq] at hpow_err
  have herr_pt : ∀ t : ℝ,
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
        dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1 =
      _root_.RHTower.mobMollifiedError M ((σ : ℂ) + (t : ℂ) * Complex.I) := fun t => by
    rw [dirichletSurgPoly_moebiusReal_eq_edPoly, _root_.RHTower.mobMollifiedError]
  simp_rw [← herr_pt] at hpow_err
  -- Measurability and Markov measure bound on `badSet`.
  have hT₁_ge1 : 1 ≤ T₁ := by
    have : 101 ≤ U := (by linarith [Real.add_one_le_exp 100] : (101 : ℝ) ≤ Real.exp 100).trans hU
    linarith
  let gClamp (t : ℝ) : ℝ :=
    ‖_root_.RHTower.mobMollifiedError M ((σ : ℂ) + ((max T₁ (min t T₂) : ℝ) : ℂ) * Complex.I)‖ ^ 2
  have hg_cont : Continuous gClamp :=
    continuous_clamped_mobMollifiedError_normSq M hσ.le hT₁_ge1 hT
  have hg_eq_on : ∀ t ∈ Icc T₁ T₂, gClamp t =
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
        dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 := fun t ht => by
    dsimp only [gClamp]
    rw [min_eq_left ht.2, max_eq_right ht.1, herr_pt]
  set badSet : Set ℝ := {t ∈ Icc T₁ T₂ |
    (1 / 2 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
      dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖}
  have hbad_eq : badSet = Icc T₁ T₂ ∩ gClamp ⁻¹' Ioi (1 / 4 : ℝ) := by
    ext t
    simp only [badSet, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Ioi]
    refine ⟨fun ⟨ht, hgt⟩ => ⟨ht, ?_⟩, fun ⟨ht, hgt⟩ => ⟨ht, ?_⟩⟩
    · rw [hg_eq_on t ht]
      have := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num : 2 ≠ 0)
      norm_num at this; exact this
    · rw [hg_eq_on t ht] at hgt
      by_contra hle
      have hle' : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
          dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ 1 / 2 := not_lt.mp hle
      have := pow_le_pow_left₀ (norm_nonneg _) hle' 2
      norm_num at this; linarith
  have hbad_meas : MeasurableSet badSet := by
    rw [hbad_eq]
    exact measurableSet_Icc.inter (measurableSet_Ioi.preimage hg_cont.measurable)
  have hbad_sub : badSet ⊆ Icc T₁ T₂ := fun _ ht => ht.1
  have hbad_lt_top : volume badSet < ⊤ :=
    (measure_mono hbad_sub).trans_lt measure_Icc_lt_top
  have hg_int_Icc : IntegrableOn gClamp (Icc T₁ T₂) := hg_cont.integrableOn_Icc
  have hmarkov : (volume badSet).toReal ≤
      4 * ∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
        dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 := by
    have hconst : ∫ _t in badSet, (1 / 4 : ℝ) = (volume badSet).toReal * (1 / 4) := by
      rw [setIntegral_const, Measure.real, smul_eq_mul]
    have hle1 : ∫ _t in badSet, (1 / 4 : ℝ) ≤ ∫ t in badSet, gClamp t := by
      refine setIntegral_mono_on (integrableOn_const hbad_lt_top.ne) (hg_int_Icc.mono_set hbad_sub)
        hbad_meas fun t ht => ?_
      rw [hbad_eq] at ht; exact le_of_lt ht.2
    have hle2 : ∫ t in badSet, gClamp t ≤ ∫ t in Icc T₁ T₂, gClamp t :=
      setIntegral_mono_set hg_int_Icc (ae_of_all _ fun _ => by dsimp only [gClamp]; positivity)
        (Eventually.of_forall hbad_sub)
    have hIcc_eq : ∫ t in Icc T₁ T₂, gClamp t =
        ∫ t in T₁..T₂, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
          dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT] at ht
      exact hg_eq_on t ht
    linarith [hconst, hle1, hle2, hIcc_eq]
  have hmeas_bound : (volume badSet).toReal ≤
      4 * B_mob * (Real.log U + 2) ^ 5 * U ^ (1 - (σ - 1 / 2) / 5) :=
    hmarkov.trans (by linarith [hpow_err])
  refine ⟨hpow_err, hbad_meas, hmeas_bound, fun t ⟨ht_mem, ht_good⟩ => ?_⟩
  have hdamp : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) *
      dirichletSurgPoly M moebiusReal ((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ 1 / 2 :=
    not_lt.mp fun hgt => ht_good ⟨ht_mem, hgt⟩
  set w : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hw_re : 0 < w.re := by simp [w]; linarith
  have hw_im : w.im = t := by simp [w]
  have ht_pos : 1 ≤ t := hT₁_ge1.trans ht_mem.1
  have hw_ne1 : w ≠ 1 := fun he => by have := congrArg Complex.im he; rw [hw_im] at this; simp at this; linarith
  have ht_le_norm : t ≤ ‖w - 1‖ := by
    have him_sub : (w - 1).im = t := by simp [w]
    calc t = |(w - 1).im| := by rw [him_sub, abs_of_pos (by linarith)]
      _ ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
  obtain ⟨-, hfloor, hmol_marg, hact_marg⟩ :=
    dampened_mollifier_forces_weightedAligned_floor_and_margin M moebiusReal hw_re hw_ne1
      (θ := 1 / 2) (by norm_num) hdamp
  refine ⟨?_, hmol_marg, hact_marg⟩
  filter_upwards [hfloor] with K hK
  exact (by linarith [ht_le_norm] : t / 4 ≤ (1 - (1 / 2 : ℝ)) / 2 * ‖w - 1‖).trans hK

/-! ### Part 3: The Hurwitz–Jentzsch zero-condensation boundary on `Re s = 1/2 + zetaZeroWidth` -/

/-- **Hurwitz zero-exception compact-set margin:** on every compact set `S` strictly right of the
zero abscissa `1/2 + zetaZeroWidth` and avoiding `1`, for all sufficiently large `M`, **every**
point `w ∈ S` (with zero exceptions) admits a strict Möbius-mollified aligned shell margin. -/
theorem hurwitz_uniform_mollified_margin_right_of_abscissa {S : Set ℂ}
    (hS : IsCompact S) (hre : ∀ z ∈ S, 1 / 2 + zetaZeroWidth < z.re) (h1 : (1 : ℂ) ∉ S) :
    ∀ᶠ M : ℕ in atTop, ∀ z ∈ S,
      dirichletSurgPoly M moebiusReal z * _root_.RHTower.zetaPoleUnit z ≠ 0 ∧
        ∃ K₀ : ℕ, 1 ≤ K₀ ∧
          mollifiedAlignedError M moebiusReal K₀ z <
            ‖mollifiedAlignedReconstructed M moebiusReal K₀ z‖ := by
  have hev := MultiscaleMollifiedZetaField.eventually_moebiusPoly_ne_zero hS hre h1
  filter_upwards [hev] with M hM z hz
  have hw_absc : 1 / 2 + zetaZeroWidth < z.re := hre z hz
  have hw0 : 0 < z.re := by
    have := GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
    linarith
  have hzne1 : z ≠ 1 := fun he => h1 (he ▸ hz)
  have hzeta_ne : riemannZeta z ≠ 0 := by
    obtain ⟨σ, hσ, hσz⟩ := exists_between hw_absc
    have hmul := MultiscaleMollifiedZetaField.dirichletSum_mul_zeta_of_convergesAt
      (s₀ := (σ : ℂ))
      (MultiscaleMollifiedZetaField.moebius_convergesAt_of_abscissa_lt (by rwa [Complex.ofReal_re]))
      (s := z) (by rwa [Complex.ofReal_re]) hzne1
    exact fun h0 => zero_ne_one (by rw [h0, mul_zero] at hmul; exact hmul)
  have hQ_ne : dirichletSurgPoly M moebiusReal z ≠ 0 := by
    rw [dirichletSurgPoly_moebiusReal_eq_moebiusPoly]
    exact hM z hz
  have hprod_ne : dirichletSurgPoly M moebiusReal z * _root_.RHTower.zetaPoleUnit z ≠ 0 := by
    rw [_root_.RHTower.zetaPoleUnit_of_ne hzne1]
    exact mul_ne_zero hQ_ne (mul_ne_zero (sub_ne_zero.mpr hzne1) hzeta_ne)
  have hpos : 0 < ‖dirichletSurgPoly M moebiusReal z * _root_.RHTower.zetaPoleUnit z‖ :=
    norm_pos_iff.mpr hprod_ne
  have hm_lim := (tendsto_mollifiedAlignedReconstructed M moebiusReal hw0).norm
  have herr_lim := tendsto_mollifiedAlignedError_zero M moebiusReal hw0
  obtain ⟨K₀, ⟨hK1, herr_small⟩, hm_large⟩ :=
    (((eventually_ge_atTop 1).and
      (herr_lim.eventually (Iio_mem_nhds (half_pos hpos)))).and
      (hm_lim.eventually (Ioi_mem_nhds (half_lt_self hpos)))).exists
  exact ⟨hprod_ne, K₀, hK1, herr_small.trans hm_large⟩

/-- **Jentzsch condensation obstruction on the abscissa:** every open disc around any point `s₀` on
`Re s = 1/2 + zetaZeroWidth` contains, for arbitrarily large `M`, a point `z` (`Re z > 0`) where
`dirichletSurgPoly M moebiusReal z = 0`, extinguishing `mollifiedAlignedReconstructed` at all `K`
and driving `weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K z → 0`. -/
theorem jentzsch_moebius_mollified_extinction_near_abscissa {s₀ : ℂ}
    (hs₀ : s₀.re = 1 / 2 + zetaZeroWidth) {R : ℝ} (hR : 0 < R) (M₀ : ℕ) :
    ∃ M : ℕ, M₀ ≤ M ∧ ∃ z ∈ ball s₀ R, 0 < z.re ∧
      dirichletSurgPoly M moebiusReal z = 0 ∧
      (∀ K : ℕ, mollifiedAlignedReconstructed M moebiusReal K z = 0) ∧
      Tendsto (fun K : ℕ =>
        weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K z) atTop (𝓝 0) := by
  set r : ℝ := min R (1 / 4)
  have hr_pos : 0 < r := lt_min hR (by norm_num)
  obtain ⟨M, hM, z, hz_r, hzero⟩ :=
    MultiscaleMollifiedZetaField.exists_zero_moebiusPoly_near hs₀ hr_pos M₀
  have hz_R : z ∈ ball s₀ R := ball_subset_ball (min_le_left _ _) hz_r
  have hz_re : 0 < z.re := by
    have hnorm : ‖z - s₀‖ < 1 / 4 := (mem_ball_iff_norm.mp hz_r).trans_le (min_le_right _ _)
    have hre_diff := (abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hnorm.le)).1
    rw [Complex.sub_re, hs₀] at hre_diff
    have := GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_nonneg
    linarith
  have hQ0 : dirichletSurgPoly M moebiusReal z = 0 := by
    rwa [dirichletSurgPoly_moebiusReal_eq_moebiusPoly]
  have hm0 : ∀ K : ℕ, mollifiedAlignedReconstructed M moebiusReal K z = 0 := fun K => by
    simp [mollifiedAlignedReconstructed, hQ0]
  have hlim0 : Tendsto (fun K : ℕ =>
      weightedAlignedReconstructed (dirichletSurgWeight M moebiusReal) K z) atTop (𝓝 0) := by
    have h := tendsto_weightedAlignedReconstructed_dirichletSurgWeight M moebiusReal hz_re
    rwa [hQ0, zero_mul] at h
  exact ⟨M, hM, z, hz_R, hz_re, hQ0, hm0, hlim0⟩

#print axioms mollified_margin_forces_actual_cutoff_margin
#print axioms dampened_mollifier_forces_weightedAligned_floor_and_margin
#print axioms rh_iff_mollified_aligned_margin_above_eightyFour_and_half
#print axioms dirichletSurgWeight_moebiusReal_of_le
#print axioms moebius_mollifier_powerSaving_highOrdinate_margin
#print axioms hurwitz_uniform_mollified_margin_right_of_abscissa
#print axioms jentzsch_moebius_mollified_extinction_near_abscissa

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
