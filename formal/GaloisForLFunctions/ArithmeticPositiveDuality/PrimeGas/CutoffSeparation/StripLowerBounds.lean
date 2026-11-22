import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation.DigitImbalanceLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RemainderEndpoint
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaStripLowerBound

/-!
# Cutoff lower-bound criteria, single-cutoff margin certificates, and unconditional zero-free floors

Convergence of `renormalizedCutoff t j X w` to `2 ζ(w) / (C^w - 1)` identifies the limit without
supplying a lower bound. Combining convergence with the explicit all-cutoff truncation bound
`cutoffTruncationBound` establishes:

1. Eventual lower bounds (`∃ ε > 0, ∀ᶠ X, ε ≤ ‖renormalizedCutoff‖`), cofinal lower bounds, and
   single-cutoff margin certificates (`∃ X₀ ≥ 1, cutoffTruncationBound < ‖renormalizedCutoff‖`)
   across `1/2 < Re w < 1` are each equivalent to `RiemannHypothesis`, and equivalent to failure of
   cutoff separation forcing the weak-trace / non-trace endpoint on `dampedRemainder`.
2. Unconditionally, `‖renormalizedCutoff t j X w‖` stays eventually bounded away from zero across
   the proven right zero-free half-plane `Re w > 20999 / 24000` (`w ≠ 1`), its symmetric left strip
   `0 < Re w < 3001 / 24000`, and the entire real critical segment `w ∈ (0, 1)`.
3. In the near-one collar `|σ - 1| ≤ A / log^9 |τ|` (`|τ| ≥ 9`, `σ > 0`), every cutoff `X ≥ 1`
   whose explicit truncation error clears the fourth-power threshold satisfies the quantitative
   lower bound `((C^σ + 1)⁻¹ ^ 4) * A^3 / (12096 * log^28 |τ|) ≤ ‖renormalizedCutoff‖^4`.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation

open AntipodalSpectrum Filter
open scoped Topology

/-- Explicit all-cutoff upper bound on `‖renormalizedCutoff t j X w - 2 q ζ(w) / (1 - q)‖`. -/
def cutoffTruncationBound (t : ExceptionalTime) (j X : ℕ) (w : ℂ) : ℝ :=
  (Real.logb (tailRadix t j).val X + 1 + digitImbalanceErrorConst t j w) * (X : ℝ) ^ (-w.re)

theorem tendsto_cutoffTruncationBound_zero (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun X : ℕ => cutoffTruncationBound t j X w) atTop (𝓝 0) := by
  let C := tailRadix t j
  have hCr1 : (1 : ℝ) < C.val := by exact_mod_cast radix_gt_one t j
  have hlogC : 0 < Real.log C.val := Real.log_pos hCr1
  -- Write `(log_C X + const) * X^(-w.re)` using `X = exp (log X)` and `u * exp (-s u) → 0`.
  have h1 : Tendsto (fun X : ℕ => Real.logb C.val X * (X : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    have hexp := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hw)).const_mul
      (1 / (w.re * Real.log C.val))
    rw [mul_zero] at hexp
    refine hexp.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with X hX0
    have hXpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX0
    dsimp only [Function.comp_apply]
    rw [pow_one, Real.logb, Real.rpow_def_of_pos hXpos]
    have : -(w.re * Real.log X) = Real.log X * (-w.re) := by ring
    rw [this]
    field_simp [hw.ne', hlogC.ne']
  have h2 : Tendsto (fun X : ℕ =>
      (1 + digitImbalanceErrorConst t j w) * (X : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
    have hrp := (tendsto_rpow_neg_atTop hw).comp tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_def] using hrp.const_mul (1 + digitImbalanceErrorConst t j w)
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine hsum.congr fun X => ?_
  unfold cutoffTruncationBound
  ring

/-- Pointwise eventual lower-bound characterization of nonvanishing of `ζ(w)`. -/
theorem eventually_norm_renormalizedCutoff_ge_iff (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w‖) ↔
      riemannZeta w ≠ 0 := by
  set C := tailRadix t j
  set q := heat w C
  have hq_lt : ‖q‖ < 1 := heat_contraction C (radix_gt_one t j) w hw
  have h1q : (1 : ℂ) - q ≠ 0 := sub_ne_zero.mpr fun he => hq_lt.ne (by rw [← he, norm_one])
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hlim := (renormalized_cutoff_limit t j ⟨w, hw, hw1⟩).norm
  dsimp only at hlim
  constructor
  · rintro ⟨ε, hε, hev⟩ hz
    have hvan := ((cutoff_vanishes_iff t j ⟨w, hw, hw1⟩).mpr hz).norm
    rw [norm_zero] at hvan
    obtain ⟨X, hge, hlt⟩ := (hev.and (hvan.eventually (Iio_mem_nhds hε))).exists
    exact hlt.not_ge hge
  · intro hz
    set L := 2 * q * riemannZeta w / (1 - q)
    have hL_ne : L ≠ 0 :=
      div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hq0) hz) h1q
    have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL_ne
    refine ⟨‖L‖ / 2, half_pos hL_pos, ?_⟩
    filter_upwards [hlim.eventually (Ioi_mem_nhds (half_lt_self hL_pos))] with X hX
    exact le_of_lt hX

/-- Pointwise cofinal lower-bound characterization of nonvanishing of `ζ(w)`. -/
theorem frequently_norm_renormalizedCutoff_ge_iff (t : ExceptionalTime) (j : ℕ)
    {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) :
    (∃ ε : ℝ, 0 < ε ∧ ∃ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w‖) ↔
      riemannZeta w ≠ 0 := by
  constructor
  · rintro ⟨ε, hε, hfreq⟩ hz
    have hvan := ((cutoff_vanishes_iff t j ⟨w, hw, hw1⟩).mpr hz).norm
    rw [norm_zero] at hvan
    exact hfreq (hvan.eventually (Iio_mem_nhds hε) |>.mono fun _ hlt => hlt.not_ge)
  · intro hz
    obtain ⟨ε, hε, hev⟩ := (eventually_norm_renormalizedCutoff_ge_iff t j hw hw1).mpr hz
    exact ⟨ε, hε, hev.frequently⟩

/-- Single-cutoff margin certificate: if at one finite cutoff `X₀ ≥ 1` the modulus of
`renormalizedCutoff` exceeds `cutoffTruncationBound` by margin `δ > 0`, then `ζ(w) ≠ 0` and every
cutoff `X ≥ 1` with `cutoffTruncationBound ≤ δ / 2` stays bounded below by `δ / 2`. -/
theorem single_cutoff_margin_forces_lower_bound (t : ExceptionalTime) (j : ℕ)
    {X₀ : ℕ} (hX₀ : 1 ≤ X₀) {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1)
    (hmargin : cutoffTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖) :
    let δ := ‖renormalizedCutoff t j X₀ w‖ - cutoffTruncationBound t j X₀ w
    riemannZeta w ≠ 0 ∧
      (∀ X : ℕ, 1 ≤ X → cutoffTruncationBound t j X w ≤ δ / 2 →
        δ / 2 ≤ ‖renormalizedCutoff t j X w‖) ∧
      (∀ᶠ X : ℕ in atTop, δ / 2 ≤ ‖renormalizedCutoff t j X w‖) := by
  dsimp only
  set C := tailRadix t j
  set q := heat w C
  set L := 2 * q * riemannZeta w / (1 - q)
  set δ := ‖renormalizedCutoff t j X₀ w‖ - cutoffTruncationBound t j X₀ w
  have hδ : 0 < δ := sub_pos.mpr hmargin
  have hb₀ : ‖renormalizedCutoff t j X₀ w - L‖ ≤ cutoffTruncationBound t j X₀ w :=
    norm_renormalizedCutoff_sub_limit_le t j hX₀ hw hw1
  have hL_ge : δ ≤ ‖L‖ := by
    have htri : ‖renormalizedCutoff t j X₀ w‖ ≤ ‖renormalizedCutoff t j X₀ w - L‖ + ‖L‖ := by
      simpa only [sub_add_cancel] using norm_add_le (renormalizedCutoff t j X₀ w - L) L
    linarith
  have hzeta_ne : riemannZeta w ≠ 0 := by
    intro hz
    have hL0 : L = 0 := by dsimp [L]; rw [hz, mul_zero, zero_div]
    rw [hL0, norm_zero] at hL_ge
    linarith
  have hall : ∀ X : ℕ, 1 ≤ X → cutoffTruncationBound t j X w ≤ δ / 2 →
      δ / 2 ≤ ‖renormalizedCutoff t j X w‖ := by
    intro X hX1 hsmall
    have hbX : ‖renormalizedCutoff t j X w - L‖ ≤ cutoffTruncationBound t j X w :=
      norm_renormalizedCutoff_sub_limit_le t j hX1 hw hw1
    have htri : ‖L‖ ≤ ‖renormalizedCutoff t j X w‖ + ‖L - renormalizedCutoff t j X w‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (renormalizedCutoff t j X w) (L - renormalizedCutoff t j X w)
    rw [norm_sub_rev] at htri
    linarith
  refine ⟨hzeta_ne, hall, ?_⟩
  have h0 := tendsto_cutoffTruncationBound_zero t j hw
  filter_upwards [eventually_ge_atTop 1,
    h0.eventually (Iio_mem_nhds (half_pos hδ))] with X hX1 hlt
  exact hall X hX1 hlt.le

/-- Exact equivalence of the Riemann Hypothesis with `renormalizedCutoff` staying bounded away
from zero as `X → ∞` at every point of `1/2 < Re w < 1`. -/
theorem rh_iff_renormalizedCutoff_bounded_away_from_zero (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 →
        ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w‖ := by
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  refine forall_congr' fun w => forall_congr' fun hlo => forall_congr' fun hhi => ?_
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  exact (eventually_norm_renormalizedCutoff_ge_iff t j hw0 hw1).symm

/-- Exact equivalence of RH with existence of one finite cutoff beating `cutoffTruncationBound`
at each point of `1/2 < Re w < 1`. -/
theorem rh_iff_single_cutoff_margin (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 →
        ∃ X₀ : ℕ, 1 ≤ X₀ ∧ cutoffTruncationBound t j X₀ w < ‖renormalizedCutoff t j X₀ w‖ := by
  rw [rh_iff_renormalizedCutoff_bounded_away_from_zero t j]
  refine forall_congr' fun w => forall_congr' fun hlo => forall_congr' fun hhi => ?_
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := fun he => hhi.ne (by rw [he, Complex.one_re])
  constructor
  · rintro ⟨ε, hε, hev⟩
    have h0 := tendsto_cutoffTruncationBound_zero t j hw0
    obtain ⟨X₀, ⟨hX1, hge⟩, hlt⟩ :=
      ((eventually_ge_atTop 1).and hev |>.and (h0.eventually (Iio_mem_nhds hε))).exists
    exact ⟨X₀, hX1, lt_of_lt_of_le hlt hge⟩
  · rintro ⟨X₀, hX1, hmargin⟩
    obtain ⟨_, _, hev⟩ := single_cutoff_margin_forces_lower_bound t j hX1 hw0 hw1 hmargin
    exact ⟨_, half_pos (sub_pos.mpr hmargin), hev⟩

/-- Direct bridge to the weak-trace / non-trace remainder endpoint: RH holds iff failure of
eventual cutoff separation in `0 < Re w < 1` forces `dampedRemainder` onto its critical endpoint. -/
theorem rh_iff_cutoff_failure_forces_weak_nontrace (t : ExceptionalTime) (j : ℕ) :
    RiemannHypothesis ↔
      ∀ w : {z : ℂ // 0 < z.re ∧ z.re < 1},
        (¬∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w.val‖) →
          _root_.RHTower.MemWeakSchattenClass 1 (dampedRemainder t j ⟨w.val, w.2.1.le⟩) ∧
            ¬(dampedRemainder t j ⟨w.val, w.2.1.le⟩).IsTraceClass := by
  constructor
  · intro hrh w hnot
    have hw1 : w.val ≠ 1 := fun he => w.2.2.ne (by rw [he, Complex.one_re])
    have hz : riemannZeta w.val = 0 :=
      Classical.not_not.mp (mt (eventually_norm_renormalizedCutoff_ge_iff t j w.2.1 hw1).mpr hnot)
    apply (split_iff_weak_nontrace t j ⟨w.val, w.2.1⟩).mp
    apply (PrimeGas.split_isometric_iff w.val).mpr
    apply hrh w.val hz
    · rintro ⟨n, hn⟩
      have hp := w.2.1
      rw [hn] at hp
      norm_num [Complex.mul_re] at hp
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · exact hw1
  · intro hend
    rw [rh_iff_renormalizedCutoff_bounded_away_from_zero t j]
    intro w hlo hhi
    by_contra hnot
    have hw0 : 0 < w.re := by linarith
    have hiso := (split_iff_weak_nontrace t j ⟨w, hw0⟩).mpr (hend ⟨w, hw0, hhi⟩ hnot)
    have hhalf := (PrimeGas.split_isometric_iff w).mp hiso
    linarith

/-- Unconditional cutoff separation on the proven right zero-free half-plane `Re w > 20999 / 24000`
away from the pole `w = 1` (covering `20999 / 24000 < Re w < 1` inside the right critical strip). -/
theorem eventually_norm_renormalizedCutoff_ge_of_sub_seven_eighths
    (t : ExceptionalTime) (j : ℕ) {w : ℂ}
    (hw : (20999 / 24000 : ℝ) < w.re) (hw1 : w ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w‖ :=
  (eventually_norm_renormalizedCutoff_ge_iff t j (by linarith) hw1).mpr
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hw)

/-- Unconditional cutoff separation on the reflected left zero-free strip `0 < Re w < 3001 / 24000`. -/
theorem eventually_norm_renormalizedCutoff_ge_of_re_lt_sub_one_eighth
    (t : ExceptionalTime) (j : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw : w.re < (3001 / 24000 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X w‖ :=
  (eventually_norm_renormalizedCutoff_ge_iff t j hw0
    (fun he => by rw [he, Complex.one_re] at hw; norm_num at hw)).mpr
    (MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_re_lt_sub_one_eighth hw0 hw)

/-- Unconditional cutoff separation across the entire real open critical interval `(0, 1)`,
in particular for every real `1/2 < σ < 1`. -/
theorem eventually_norm_renormalizedCutoff_ge_of_real_mem_Ioo
    (t : ExceptionalTime) (j : ℕ) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ X : ℕ in atTop, ε ≤ ‖renormalizedCutoff t j X (σ : ℂ)‖ :=
  (eventually_norm_renormalizedCutoff_ge_iff t j (by simpa using h0)
    (fun he => h1.ne (by simpa using congrArg Complex.re he))).mpr
    (_root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo h0 h1)

/-- Root-free quantitative cutoff lower bound in the near-one zero-free collar
`|σ - 1| ≤ A / log^9 |τ|`, `|τ| ≥ 9`: every finite cutoff `X ≥ 1` whose explicit truncation error
clears the fourth-power threshold satisfies an explicit inverse-logarithmic lower bound. -/
theorem pow_four_norm_renormalizedCutoff_ge_collar (t : ExceptionalTime) (j : ℕ)
    {σ τ : ℝ} (hσ0 : 0 < σ) (hτ : 9 ≤ |τ|)
    (hσl : 1 - _root_.RHTower.zetaLowerA / Real.log |τ| ^ (9 : ℕ) ≤ σ)
    (hσu : σ ≤ 1 + _root_.RHTower.zetaLowerA / Real.log |τ| ^ (9 : ℕ))
    {X : ℕ} (hX : 1 ≤ X)
    (hcut : cutoffTruncationBound t j X ((σ : ℂ) + (τ : ℂ) * Complex.I) ^ (4 : ℕ) ≤
      (((tailRadix t j).val : ℝ) ^ σ + 1)⁻¹ ^ (4 : ℕ) *
        _root_.RHTower.zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |τ| ^ (28 : ℕ))) :
    (((tailRadix t j).val : ℝ) ^ σ + 1)⁻¹ ^ (4 : ℕ) *
      _root_.RHTower.zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |τ| ^ (28 : ℕ)) ≤
      ‖renormalizedCutoff t j X ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ^ (4 : ℕ) := by
  set w : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I
  set C := tailRadix t j
  let Cr : ℝ := C.val
  set q := heat w C
  have hCr0 : (0 : ℝ) < Cr := Nat.cast_pos.mpr C.pos
  have hw_re : w.re = σ := by simp [w]
  have hw_im : w.im = τ := by simp [w]
  have hw0 : 0 < w.re := by rwa [hw_re]
  have hw1 : w ≠ 1 := by
    intro he
    have := congrArg Complex.im he
    rw [hw_im, Complex.one_im] at this
    rw [this, abs_zero] at hτ
    linarith
  set L := 2 * q * riemannZeta w / (1 - q)
  set F := (Cr ^ σ + 1)⁻¹ ^ (4 : ℕ) *
    _root_.RHTower.zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |τ| ^ (28 : ℕ))
  -- Lower bound `‖L‖` from `pow_four_norm_riemannZeta_ge_strip`.
  have hq_norm : ‖q‖ = Cr ^ (-σ) := by
    rw [norm_heat, hw_re, energy, Real.rpow_def_of_pos hCr0]
    congr 1; dsimp only [Cr]; ring
  have h1q_le : ‖(1 : ℂ) - q‖ ≤ 1 + Cr ^ (-σ) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, hq_norm]
  have h1q_pos : 0 < ‖(1 : ℂ) - q‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr fun he =>
      (heat_contraction C (radix_gt_one t j) w hw0).ne (by dsimp only [q] at he; rw [← he, norm_one])
  have hfactor : 2 * Cr ^ (-σ) / (1 + Cr ^ (-σ)) = 2 * (Cr ^ σ + 1)⁻¹ := by
    have hp1 : 0 < Cr ^ σ := Real.rpow_pos_of_pos hCr0 σ
    have hp2 : Cr ^ (-σ) = (Cr ^ σ)⁻¹ := Real.rpow_neg hCr0.le σ
    rw [hp2]
    field_simp [hp1.ne', (by linarith : Cr ^ σ + 1 ≠ 0), (by positivity : 1 + (Cr ^ σ)⁻¹ ≠ 0)]
  have hL_ge_zeta : 2 * (Cr ^ σ + 1)⁻¹ * ‖riemannZeta w‖ ≤ ‖L‖ := by
    dsimp only [L]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, hq_norm, ← hfactor]
    calc 2 * Cr ^ (-σ) / (1 + Cr ^ (-σ)) * ‖riemannZeta w‖
        = (2 * Cr ^ (-σ) * ‖riemannZeta w‖) / (1 + Cr ^ (-σ)) := by ring
      _ ≤ (2 * Cr ^ (-σ) * ‖riemannZeta w‖) / ‖(1 : ℂ) - q‖ :=
        div_le_div_of_nonneg_left (by positivity) h1q_pos h1q_le
  have hzeta4 := _root_.RHTower.pow_four_norm_riemannZeta_ge_strip hτ hσl hσu
  have hL4 : 16 * F ≤ ‖L‖ ^ (4 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by positivity) hL_ge_zeta 4
    rw [mul_pow, mul_pow] at hpow
    refine le_trans ?_ hpow
    have h16 : (2 : ℝ) ^ (4 : ℕ) = 16 := by norm_num
    rw [h16]
    calc 16 * F
        = 16 * (Cr ^ σ + 1)⁻¹ ^ (4 : ℕ) *
            (_root_.RHTower.zetaLowerA ^ (3 : ℕ) / (12096 * Real.log |τ| ^ (28 : ℕ))) := by
            dsimp [F]; ring
      _ ≤ 16 * (Cr ^ σ + 1)⁻¹ ^ (4 : ℕ) * ‖riemannZeta w‖ ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_left hzeta4 (by positivity)
  -- Compare `cutoffTruncationBound` with `‖L‖ / 2` via fourth powers.
  have hbX : ‖renormalizedCutoff t j X w - L‖ ≤ cutoffTruncationBound t j X w :=
    norm_renormalizedCutoff_sub_limit_le t j hX hw0 hw1
  have hcut_nn : 0 ≤ cutoffTruncationBound t j X w :=
    (norm_nonneg _).trans hbX
  have hcut_le_half : cutoffTruncationBound t j X w ≤ ‖L‖ / 2 := by
    have h4 : cutoffTruncationBound t j X w ^ (4 : ℕ) ≤ (‖L‖ / 2) ^ (4 : ℕ) := by
      calc cutoffTruncationBound t j X w ^ (4 : ℕ) ≤ F := hcut
        _ = (16 * F) / 16 := by ring
        _ ≤ ‖L‖ ^ (4 : ℕ) / 16 := div_le_div_of_nonneg_right hL4 (by norm_num)
        _ = (‖L‖ / 2) ^ (4 : ℕ) := by ring
    by_contra! hgt
    have hstrict := pow_lt_pow_left₀ hgt (div_nonneg (norm_nonneg L) zero_le_two) (by norm_num : 4 ≠ 0)
    linarith
  have hU_ge : ‖L‖ / 2 ≤ ‖renormalizedCutoff t j X w‖ := by
    have htri : ‖L‖ ≤ ‖renormalizedCutoff t j X w‖ + ‖L - renormalizedCutoff t j X w‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (renormalizedCutoff t j X w) (L - renormalizedCutoff t j X w)
    rw [norm_sub_rev] at htri
    linarith
  calc F = (16 * F) / 16 := by ring
    _ ≤ ‖L‖ ^ (4 : ℕ) / 16 := div_le_div_of_nonneg_right hL4 (by norm_num)
    _ = (‖L‖ / 2) ^ (4 : ℕ) := by ring
    _ ≤ ‖renormalizedCutoff t j X w‖ ^ (4 : ℕ) :=
      pow_le_pow_left₀ (div_nonneg (norm_nonneg L) zero_le_two) hU_ge 4

#print axioms eventually_norm_renormalizedCutoff_ge_iff
#print axioms frequently_norm_renormalizedCutoff_ge_iff
#print axioms single_cutoff_margin_forces_lower_bound
#print axioms rh_iff_renormalizedCutoff_bounded_away_from_zero
#print axioms rh_iff_single_cutoff_margin
#print axioms rh_iff_cutoff_failure_forces_weak_nontrace
#print axioms eventually_norm_renormalizedCutoff_ge_of_sub_seven_eighths
#print axioms eventually_norm_renormalizedCutoff_ge_of_re_lt_sub_one_eighth
#print axioms eventually_norm_renormalizedCutoff_ge_of_real_mem_Ioo
#print axioms pow_four_norm_renormalizedCutoff_ge_collar

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CutoffSeparation
