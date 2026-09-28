import GaloisForLFunctions.RHTower.Sieve.ShiuOmegaTiltShortInterval
import GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerCapacity
import GaloisForLFunctions.RHTower.MobiusWoldBreadthTwoSidedDeviationRate
import GaloisForLFunctions.RHTower.MobiusWoldBreadthGibbsCost

/-!
# Low-breadth transport by reciprocal markers

For `0 < c₀ < 1` the integers of an interval `(A, A+y]`, `y ≥ √A`, with at most `c₀ log log A`
distinct prime factors number `≪ y (log A)^{-I(c₀)}`, `I(c) = 1 − c + c log c` (Chernoff with
Shiu's bound for `c₀^{ω(n)}`).  At the near-maximal subpower window `H = √X exp(log X/log log X)`
this is `o(H/log log X)`, while the reciprocal-marker targets of each Möbius sign number
`≫ H/log log X`.  So every low-breadth squarefree vertex of an `H`-cell can be matched to a
distinct target of the opposite sign in the same cell, outside the low-breadth set, and across a
dyadic shell the first-order Gibbs cost of all these moves is `O(H)`.
-/

namespace RHTower.Sieve

open Finset Filter Topology ArithmeticFunction

noncomputable section

/-- **Chernoff's bound for the lower tail of `ω`.**  For `0 < c₀ ≤ 1`, the integers of a finite
set with `ω(n) ≤ k` number at most `c₀^{-k} ∑ c₀^{ω(n)}`. -/
theorem card_omega_le_le_tilt {c₀ k : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ ≤ 1) (S : Finset ℕ) :
    ((S.filter (fun n => (n.primeFactors.card : ℝ) ≤ k)).card : ℝ)
      ≤ c₀ ^ (-k) * ∑ n ∈ S, omegaTilt c₀ n := by
  classical
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum]
  calc ∑ n ∈ S.filter (fun n => (n.primeFactors.card : ℝ) ≤ k), (1 : ℝ)
      ≤ ∑ n ∈ S.filter (fun n => (n.primeFactors.card : ℝ) ≤ k), c₀ ^ (-k) * omegaTilt c₀ n := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hk := (Finset.mem_filter.1 hn).2
        rw [omegaTilt, ← Real.rpow_natCast, ← Real.rpow_add hc0]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc0 hc1 (by linarith)
    _ ≤ ∑ n ∈ S, c₀ ^ (-k) * omegaTilt c₀ n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => mul_nonneg (Real.rpow_nonneg hc0.le _) (omegaTilt_nonneg hc0.le n))

/-- `c₀^{-c₀ log log A} = (log A)^{-c₀ log c₀}`. -/
theorem rpow_neg_mul_logLog {c₀ : ℝ} (hc0 : 0 < c₀) {L : ℝ} (hL : 0 < L) :
    c₀ ^ (-(c₀ * Real.log L)) = L ^ (-(c₀ * Real.log c₀)) := by
  rw [Real.rpow_def_of_pos hc0, Real.rpow_def_of_pos hL]
  congr 1
  ring

open Classical in
/-- **The low-breadth count (the Chernoff lower tail).**  For fixed `0 < c₀ < 1`, uniformly in
`y ≥ √A`, the integers of `(A, A+y]` with `ω(n) ≤ c₀ log log A` number at most
`C y (log A)^{-I(c₀)}`, `I(c) = 1 − c + c log c`. -/
theorem card_lowBreadth_le {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ < 1) :
    ∀ᶠ A : ℕ in atTop, ∀ y : ℕ, A ≤ y * y →
      ((((Finset.Ioc A (A + y)).filter (fun n => moebius n ≠ 0
          ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log A))).card : ℕ) : ℝ)
        ≤ (shiuMainConst + 3) * (y : ℝ)
          * (Real.log A) ^ (-RHTower.woldBreadthDeviationRate c₀) := by
  have hlogA : Tendsto (fun A : ℕ => Real.log (A : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [shiu_omegaTilt_short_interval hc0.le hc1.le,
    hlogA.eventually_gt_atTop 0] with A hA hL0 y hy
  have hsub : ((Finset.Ioc A (A + y)).filter (fun n => moebius n ≠ 0
        ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log A)))
      ⊆ (Finset.Ioc A (A + y)).filter
          (fun n => (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log A)) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.2⟩
  refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
  refine (card_omega_le_le_tilt hc0 hc1.le _).trans ?_
  have hshiu := hA y hy
  have hC : 0 ≤ shiuMainConst + 3 := by
    rw [shiuMainConst]; positivity
  calc c₀ ^ (-(c₀ * Real.log (Real.log A))) * ∑ n ∈ Finset.Ioc A (A + y), omegaTilt c₀ n
      ≤ c₀ ^ (-(c₀ * Real.log (Real.log A)))
          * ((shiuMainConst + 3) * (y : ℝ) * (Real.log A) ^ (c₀ - 1)) :=
        mul_le_mul_of_nonneg_left hshiu (Real.rpow_nonneg hc0.le _)
    _ = (shiuMainConst + 3) * (y : ℝ)
          * ((Real.log A) ^ (-(c₀ * Real.log c₀)) * (Real.log A) ^ (c₀ - 1)) := by
        rw [rpow_neg_mul_logLog hc0 hL0]; ring
    _ = (shiuMainConst + 3) * (y : ℝ)
          * (Real.log A) ^ (-RHTower.woldBreadthDeviationRate c₀) := by
        rw [← Real.rpow_add hL0, RHTower.woldBreadthDeviationRate]
        congr 2
        ring

/-- The logarithmic facts behind the subpower cells, eventually in `s = log X`. -/
theorem eventually_subpower_cell_logs :
    ∀ᶠ s : ℝ in atTop, (Real.log (s + Real.log 2)) ^ (2 : ℕ) ≤ s / Real.log s - 3 / 2 * Real.log 2
      ∧ s / Real.log s + 3 / 2 * Real.log 2 ≤ (s - Real.log 2) / 10
      ∧ s / (2 * Real.log s) ≤ s / Real.log s - 3 / 2 * Real.log 2
      ∧ 2 + Real.log 2 ≤ s := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlo : (fun s : ℝ => Real.log s ^ (3 : ℝ)) =o[atTop] fun s : ℝ => s ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 3 (by norm_num)
  filter_upwards [hlo.bound (show (0 : ℝ) < 1 / 8 by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (20 : ℝ), eventually_ge_atTop (100 : ℝ)]
    with s hs hls hs100
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < Real.log s := by linarith
  rw [Real.rpow_one, Real.norm_of_nonneg hs0.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _)] at hs
  have hl3 : Real.log s ^ (3 : ℝ) = (Real.log s) ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hl3] at hs
  have hsl : 20 ≤ s / Real.log s := by
    rw [le_div_iff₀ hl0]
    nlinarith [hs, hls, sq_nonneg (Real.log s)]
  have hlog2s : Real.log (s + Real.log 2) ≤ 2 * Real.log s := by
    have h1 : s + Real.log 2 ≤ s * s := by nlinarith
    have := Real.log_le_log (by linarith) h1
    rw [Real.log_mul hs0.ne' hs0.ne'] at this
    linarith
  have hlog2s0 : 0 ≤ Real.log (s + Real.log 2) := Real.log_nonneg (by linarith)
  refine ⟨?_, ?_, ?_, by linarith⟩
  · have h1 : (Real.log (s + Real.log 2)) ^ (2 : ℕ) ≤ 4 * (Real.log s) ^ (2 : ℕ) := by
      nlinarith [hlog2s, hlog2s0]
    have h2 : 4 * (Real.log s) ^ (2 : ℕ) + 3 / 2 * Real.log 2 ≤ s / Real.log s := by
      rw [le_div_iff₀ hl0]
      nlinarith [hs, hls, hlog2le]
    linarith
  · have h1 : s / Real.log s ≤ s / 20 := div_le_div_of_nonneg_left hs0.le (by norm_num) hls
    linarith
  · have h1 : s / (2 * Real.log s) = (s / Real.log s) / 2 := by ring
    rw [h1]
    linarith

open Classical in
/-- **Targets in every cell of a dyadic shell.**  With `W = √X exp(log X/log log X)`, every
interval `(Y, Y+H₀]` with `X − 1 ≤ Y ≤ 2X` and `W/2 ≤ H₀ ≤ 2W` contains at least
`c·W/log log X` integers of each Möbius sign. -/
theorem cell_target_count :
    ∃ c : ℝ, 0 < c ∧ ∀ σ : ℤ, (σ = 1 ∨ σ = -1) → ∀ᶠ X : ℝ in atTop, ∀ Y H₀ : ℕ,
      X - 1 ≤ (Y : ℝ) → (Y : ℝ) ≤ 2 * X →
      growingReciprocalMarkerWindow X / 2 ≤ (H₀ : ℝ) →
      (H₀ : ℝ) ≤ 2 * growingReciprocalMarkerWindow X →
      c * (growingReciprocalMarkerWindow X / Real.log (Real.log X))
        ≤ ((((Finset.Ioc Y (Y + H₀)).filter (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := growingMarker_count_uniform
  refine ⟨c / 8, by positivity, fun σ hσ => ?_⟩
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.1 (hcount σ hσ)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  filter_upwards [Real.tendsto_log_atTop.eventually eventually_subpower_cell_logs,
    eventually_ge_atTop (Z₀ + 1), eventually_ge_atTop (4 : ℝ)] with X hXlog hXZ hX4
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hXlog
  intro Y H₀ hY1 hY2 hH1 hH2
  have hX0 : 0 < X := by linarith
  have hWexp : growingReciprocalMarkerWindow X
      = Real.exp (Real.log X / 2 + Real.log X / Real.log (Real.log X)) := by
    rw [growingReciprocalMarkerWindow, growingReciprocalMarkerH, Real.exp_add,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
    ring_nf
  set a : ℝ := Real.log X with ha
  have ha0 : 0 < a := by linarith
  have hla : 0 < Real.log a := by
    have : (2 : ℝ) ≤ a := by linarith
    exact Real.log_pos (by linarith)
  set ℓ : ℝ := a / Real.log a with hℓ
  set W : ℝ := growingReciprocalMarkerWindow X with hW
  have hW0 : 0 < W := by rw [hWexp]; exact Real.exp_pos _
  have hYR : (1 : ℝ) ≤ (Y : ℝ) := by linarith
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hH00 : (0 : ℝ) < (H₀ : ℝ) := by linarith
  have hlogY_le : Real.log Y ≤ a + Real.log 2 := by
    have := Real.log_le_log hY0 hY2
    rw [Real.log_mul (by norm_num) hX0.ne'] at this; linarith
  have hlogY_ge : a - Real.log 2 ≤ Real.log Y := by
    have h1 : X / 2 ≤ (Y : ℝ) := by linarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hX0.ne' (by norm_num)] at this; linarith
  have hlogH_le : Real.log H₀ ≤ a / 2 + ℓ + Real.log 2 := by
    have := Real.log_le_log hH00 hH2
    rw [Real.log_mul (by norm_num) hW0.ne', hWexp, Real.log_exp] at this; linarith
  have hlogH_ge : a / 2 + ℓ - Real.log 2 ≤ Real.log H₀ := by
    have := Real.log_le_log (by positivity) hH1
    rw [Real.log_div hW0.ne' (by norm_num), hWexp, Real.log_exp] at this; linarith
  -- the length at scale `Y`
  set h' : ℝ := (H₀ : ℝ) / Real.sqrt Y with hh'
  have hsY : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.2 hY0
  have hh'0 : 0 < h' := div_pos hH00 hsY
  have hlogh' : Real.log h' = Real.log H₀ - Real.log Y / 2 := by
    rw [hh', Real.log_div hH00.ne' hsY.ne', Real.log_sqrt hY0.le]
  have hlogh'_ge : ℓ - 3 / 2 * Real.log 2 ≤ Real.log h' := by rw [hlogh']; linarith
  have hlogh'_le : Real.log h' ≤ ℓ + 3 / 2 * Real.log 2 := by rw [hlogh']; linarith
  have hloglogY : (Real.log (Real.log Y)) ^ (2 : ℕ) ≤ Real.log h' := by
    have hlY1 : 1 ≤ Real.log Y := by linarith
    have h1 : Real.log (Real.log Y) ≤ Real.log (a + Real.log 2) :=
      Real.log_le_log (by linarith) hlogY_le
    have h0 : 0 ≤ Real.log (Real.log Y) := Real.log_nonneg hlY1
    have := pow_le_pow_left₀ h0 h1 2
    linarith
  have hhigh : Real.log h' ≤ Real.log Y / 10 := by linarith
  have hsqrt : Real.sqrt (Y : ℝ) * h' = (H₀ : ℝ) := by
    rw [hh']; field_simp
  have hkey := hZ₀ (Y : ℝ) (by linarith) h' hh'0 hloglogY hhigh
  rw [hsqrt, Nat.floor_natCast] at hkey
  have hfl : ⌊(Y : ℝ) + (H₀ : ℝ)⌋₊ = Y + H₀ := by
    rw [show (Y : ℝ) + (H₀ : ℝ) = ((Y + H₀ : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hfl] at hkey
  have hsub : ((Finset.Ioc Y (Y + H₀)).filter
        (fun n => moebius n = σ ∧ ReciprocalMarkerForm (Y : ℝ) σ n))
      ⊆ (Finset.Ioc Y (Y + H₀)).filter (fun n => moebius n = σ) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  refine le_trans ?_ (hkey.trans (by exact_mod_cast Finset.card_le_card hsub))
  -- the lower bound for `c H₀ log h'/log Y`
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlh'0 : 0 < Real.log h' := by
    have : 0 < a / (2 * Real.log a) := by positivity
    linarith
  have hratio : ℓ / (2 * (2 * a)) ≤ Real.log h' / Real.log Y := by
    rw [div_le_div_iff₀ (by positivity) hlogY0]
    have h1 : ℓ / 2 ≤ Real.log h' := by
      have : ℓ / 2 = a / (2 * Real.log a) := by rw [hℓ]; ring
      linarith
    have h2 : Real.log Y ≤ 2 * a := by linarith
    nlinarith [mul_le_mul h1 h2 hlogY0.le hlh'0.le]
  have hℓa : ℓ / (2 * (2 * a)) = 1 / (4 * Real.log a) := by
    rw [hℓ]; field_simp; ring
  rw [hℓa] at hratio
  calc c / 8 * (W / Real.log a) = c * (W / 2) * (1 / (4 * Real.log a)) := by ring
    _ ≤ c * (H₀ : ℝ) * (Real.log h' / Real.log Y) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hH1 hc.le) hratio (by positivity)
          (by positivity)
    _ = c * ((H₀ : ℝ) * Real.log h' / Real.log Y) := by ring

open Classical in
/-- The low-breadth squarefree vertices of a cell, at breadth threshold `c₀ log log X`. -/
def lowBreadthCell (c₀ X : ℝ) (Y H₀ : ℕ) : Finset ℕ :=
  (Finset.Ioc Y (Y + H₀)).filter
    (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X))

/-- The low-breadth count is `o(W/log log X)` in every cell of the shell. -/
theorem eventually_card_lowBreadthCell_le {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ < 1) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ Y H₀ : ℕ,
      X - 1 ≤ (Y : ℝ) → (Y : ℝ) ≤ 2 * X →
      growingReciprocalMarkerWindow X / 2 ≤ (H₀ : ℝ) →
      (H₀ : ℝ) ≤ 2 * growingReciprocalMarkerWindow X →
      (((lowBreadthCell c₀ X Y H₀).card : ℕ) : ℝ)
        ≤ c / 2 * (growingReciprocalMarkerWindow X / Real.log (Real.log X)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (shiu_omegaTilt_short_interval hc0.le hc1.le)
  have hI : 0 < RHTower.woldBreadthDeviationRate c₀ :=
    RHTower.woldBreadthDeviationRate_pos_of_lt_one hc0 hc1
  set CS : ℝ := shiuMainConst + 3 with hCS
  have hCS0 : 0 < CS := by rw [hCS, shiuMainConst]; positivity
  -- `(log X)^{-I} log log X → 0`
  have hdecay : Tendsto (fun X : ℝ => Real.log (Real.log X)
      * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => Real.log s * s ^ (-RHTower.woldBreadthDeviationRate c₀))
        atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hI).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      rw [Real.rpow_neg hs.le, div_eq_mul_inv]
    exact h1.comp Real.tendsto_log_atTop
  have hsmall := hdecay.eventually (gt_mem_nhds (show (0 : ℝ) < c / (8 * CS) by positivity))
  have hexpℓ : ∀ᶠ X : ℝ in atTop, 4 ≤ growingReciprocalMarkerH X := by
    have : Tendsto growingReciprocalMarkerH atTop atTop := by
      have hℓ : Tendsto (fun X : ℝ => Real.log X / Real.log (Real.log X)) atTop atTop := by
        have hq : Tendsto (fun s : ℝ => s / Real.log s) atTop atTop := by
          have h0 : Tendsto (fun s : ℝ => Real.log s / s) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
            refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              (by simpa only [Real.rpow_one] using
                (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero) ?_
            filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
            exact div_pos (Real.log_pos hz) (by linarith)
          refine (tendsto_inv_nhdsGT_zero.comp h0).congr fun z => ?_
          simp only [Function.comp_apply]; rw [inv_div]
        exact hq.comp Real.tendsto_log_atTop
      exact Real.tendsto_exp_atTop.comp hℓ
    exact this.eventually_ge_atTop 4
  have hLL : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop ((N₀ : ℝ) + 1), hsmall, hexpℓ,
    hLL.eventually_gt_atTop 0, Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log 2),
    eventually_ge_atTop (4 : ℝ)] with X hXN hXs hXh hLL0 hlogX hX4
  intro Y H₀ hY1 hY2 hH1 hH2
  have hX0 : 0 < X := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hYN : N₀ ≤ Y := by
    have : (N₀ : ℝ) ≤ (Y : ℝ) := by linarith
    exact_mod_cast this
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  set W := growingReciprocalMarkerWindow X with hW
  have hW0 : 0 < W := by
    rw [hW, growingReciprocalMarkerWindow, growingReciprocalMarkerH]
    have := Real.sqrt_pos.2 hX0
    positivity
  have hWge : 2 * Real.sqrt X ≤ W / 2 := by
    rw [hW, growingReciprocalMarkerWindow]
    have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
    nlinarith [hXh, hs]
  have hYH : Y ≤ H₀ * H₀ := by
    have hsX : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    have h2 : 2 * Real.sqrt X ≤ (H₀ : ℝ) := le_trans hWge hH1
    have : (Y : ℝ) ≤ (H₀ : ℝ) * (H₀ : ℝ) := by
      have hs : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
      nlinarith [mul_le_mul h2 h2 (by positivity) (by linarith)]
    exact_mod_cast this
  have hshiu := hN₀ Y hYN H₀ hYH
  -- Chernoff
  have hsub : lowBreadthCell c₀ X Y H₀ ⊆ (Finset.Ioc Y (Y + H₀)).filter
      (fun n => (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X)) := by
    intro n hn
    rw [lowBreadthCell, Finset.mem_filter] at hn
    exact Finset.mem_filter.2 ⟨hn.1, hn.2.2⟩
  have hch := card_omega_le_le_tilt hc0 hc1.le (Finset.Ioc Y (Y + H₀))
    (k := c₀ * Real.log (Real.log X))
  have hlogX0 : 0 < Real.log X := by linarith
  rw [rpow_neg_mul_logLog hc0 hlogX0] at hch
  -- `(log Y)^{c₀-1} ≤ 2 (log X)^{c₀-1}`
  have hlogY : Real.log X / 2 ≤ Real.log Y := by
    have h1 : X / 2 ≤ (Y : ℝ) := by linarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hX0.ne' (by norm_num)] at this
    linarith
  have hpowY : (Real.log Y) ^ (c₀ - 1) ≤ 2 * (Real.log X) ^ (c₀ - 1) := by
    have h1 : (Real.log Y) ^ (c₀ - 1) ≤ (Real.log X / 2) ^ (c₀ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlogY (by linarith)
    have h2 : (Real.log X / 2) ^ (c₀ - 1) = (2 : ℝ) ^ (1 - c₀) * (Real.log X) ^ (c₀ - 1) := by
      rw [Real.div_rpow hlogX0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num),
        neg_sub, mul_comm]
    have h3 : (2 : ℝ) ^ (1 - c₀) ≤ 2 := by
      calc (2 : ℝ) ^ (1 - c₀) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    rw [h2] at h1
    have hp : 0 ≤ (Real.log X) ^ (c₀ - 1) := Real.rpow_nonneg hlogX0.le _
    nlinarith [h1, h3, hp]
  have hcombine : (Real.log X) ^ (-(c₀ * Real.log c₀)) * (Real.log X) ^ (c₀ - 1)
      = (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀) := by
    rw [← Real.rpow_add hlogX0, RHTower.woldBreadthDeviationRate]; congr 1; ring
  have hcard := (Nat.cast_le (α := ℝ)).2 (Finset.card_le_card hsub)
  have hA : (Real.log X) ^ (-(c₀ * Real.log c₀)) ≥ 0 := Real.rpow_nonneg hlogX0.le _
  calc (((lowBreadthCell c₀ X Y H₀).card : ℕ) : ℝ)
      ≤ (Real.log X) ^ (-(c₀ * Real.log c₀)) * ∑ n ∈ Finset.Ioc Y (Y + H₀), omegaTilt c₀ n :=
        hcard.trans hch
    _ ≤ (Real.log X) ^ (-(c₀ * Real.log c₀)) * (CS * (H₀ : ℝ) * (Real.log Y) ^ (c₀ - 1)) :=
        mul_le_mul_of_nonneg_left hshiu hA
    _ ≤ (Real.log X) ^ (-(c₀ * Real.log c₀))
          * (CS * (2 * W) * (2 * (Real.log X) ^ (c₀ - 1))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hH2 hCS0.le)
          hpowY (Real.rpow_nonneg (by linarith) _) (by nlinarith [hW0, hCS0])) hA
    _ = 4 * CS * W * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀) := by
        rw [← hcombine]; ring
    _ ≤ c / 2 * (W / Real.log (Real.log X)) := by
        rw [mul_div_assoc', le_div_iff₀ hLL0]
        have h1 : Real.log (Real.log X) * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀)
            ≤ c / (8 * CS) := hXs.le
        have e : 4 * CS * W * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀)
              * Real.log (Real.log X)
            = 4 * CS * W
              * (Real.log (Real.log X) * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀)) := by
          ring
        rw [e]
        calc 4 * CS * W
              * (Real.log (Real.log X) * (Real.log X) ^ (-RHTower.woldBreadthDeviationRate c₀))
            ≤ 4 * CS * W * (c / (8 * CS)) := mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = c / 2 * W := by field_simp; ring

open Classical in
/-- **Low-breadth matching in every cell.**  For fixed `0 < c₀ < 1` and all large `X`, every cell
`(Y, Y+H₀]` of the dyadic shell (`X − 1 ≤ Y ≤ 2X`, `W/2 ≤ H₀ ≤ 2W`) carries an injection sending each
low-breadth squarefree `n` to an integer of the same cell, outside the low-breadth set, of the
opposite Möbius sign. -/
theorem lowBreadth_cell_matching {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ < 1) :
    ∀ᶠ X : ℝ in atTop, ∀ Y H₀ : ℕ,
      X - 1 ≤ (Y : ℝ) → (Y : ℝ) ≤ 2 * X →
      growingReciprocalMarkerWindow X / 2 ≤ (H₀ : ℝ) →
      (H₀ : ℝ) ≤ 2 * growingReciprocalMarkerWindow X →
      ∃ f : ℕ → ℕ, Set.InjOn f (lowBreadthCell c₀ X Y H₀) ∧
        ∀ n ∈ lowBreadthCell c₀ X Y H₀, f n ∈ Finset.Ioc Y (Y + H₀)
          ∧ f n ∉ lowBreadthCell c₀ X Y H₀ ∧ moebius (f n) = -moebius n := by
  obtain ⟨c, hc, htarget⟩ := cell_target_count
  filter_upwards [htarget 1 (Or.inl rfl), htarget (-1) (Or.inr rfl),
    eventually_card_lowBreadthCell_le hc0 hc1 hc] with X hpos hneg hlow
  intro Y H₀ hY1 hY2 hH1 hH2
  set L := lowBreadthCell c₀ X Y H₀ with hL
  set cell := Finset.Ioc Y (Y + H₀) with hcell
  set B : ℝ := c * (growingReciprocalMarkerWindow X / Real.log (Real.log X)) with hB
  have hLc : ((L.card : ℕ) : ℝ) ≤ B / 2 := by
    have := hlow Y H₀ hY1 hY2 hH1 hH2
    rw [hB]; linarith
  have hP := hpos Y H₀ hY1 hY2 hH1 hH2
  have hN := hneg Y H₀ hY1 hY2 hH1 hH2
  -- targets of each sign outside the low-breadth set
  have htarget_card : ∀ σ : ℤ, B ≤ (((cell.filter (fun n => moebius n = σ)).card : ℕ) : ℝ) →
      (L.card : ℝ) ≤ ((((cell.filter (fun n => moebius n = σ)) \ L).card : ℕ) : ℝ) := by
    intro σ hσ
    have h1 := Finset.card_le_card_sdiff_add_card (s := cell.filter (fun n => moebius n = σ))
      (t := L)
    have h1R : (((cell.filter (fun n => moebius n = σ)).card : ℕ) : ℝ)
        ≤ ((((cell.filter (fun n => moebius n = σ)) \ L).card : ℕ) : ℝ) + (L.card : ℝ) := by
      exact_mod_cast h1
    linarith
  set Lp := L.filter (fun n => moebius n = 1) with hLp
  set Lm := L.filter (fun n => moebius n ≠ 1) with hLm
  have hLp_le : Lp.card ≤ ((cell.filter (fun n => moebius n = -1)) \ L).card := by
    have h1 : (Lp.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := htarget_card (-1) hN
    exact_mod_cast h1.trans h2
  have hLm_le : Lm.card ≤ ((cell.filter (fun n => moebius n = 1)) \ L).card := by
    have h1 : (Lm.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := htarget_card 1 hP
    exact_mod_cast h1.trans h2
  obtain ⟨gp, hgp_inj, hgp_mem⟩ := exists_injOn_of_card_le hLp_le
  obtain ⟨gm, hgm_inj, hgm_mem⟩ := exists_injOn_of_card_le hLm_le
  -- the sign of a low-breadth vertex
  have hsign : ∀ n ∈ L, moebius n = 1 ∨ moebius n = -1 := by
    intro n hn
    have hne : moebius n ≠ 0 := (Finset.mem_filter.1 hn).2.1
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  refine ⟨fun n => if moebius n = 1 then gp n else gm n, ?_, ?_⟩
  · intro a ha b hb hab
    simp only at hab
    have ha' := Finset.mem_coe.1 ha
    have hb' := Finset.mem_coe.1 hb
    by_cases hpa : moebius a = 1 <;> by_cases hpb : moebius b = 1
    · rw [if_pos hpa, if_pos hpb] at hab
      exact hgp_inj (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨ha', hpa⟩))
        (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hb', hpb⟩)) hab
    · rw [if_pos hpa, if_neg hpb] at hab
      have h1 := (Finset.mem_filter.1 (Finset.mem_sdiff.1
        (hgp_mem a (Finset.mem_filter.2 ⟨ha', hpa⟩))).1).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_sdiff.1
        (hgm_mem b (Finset.mem_filter.2 ⟨hb', hpb⟩))).1).2
      rw [hab] at h1
      rw [h1] at h2
      norm_num at h2
    · rw [if_neg hpa, if_pos hpb] at hab
      have h1 := (Finset.mem_filter.1 (Finset.mem_sdiff.1
        (hgm_mem a (Finset.mem_filter.2 ⟨ha', hpa⟩))).1).2
      have h2 := (Finset.mem_filter.1 (Finset.mem_sdiff.1
        (hgp_mem b (Finset.mem_filter.2 ⟨hb', hpb⟩))).1).2
      rw [hab] at h1
      rw [h1] at h2
      norm_num at h2
    · rw [if_neg hpa, if_neg hpb] at hab
      exact hgm_inj (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨ha', hpa⟩))
        (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hb', hpb⟩)) hab
  · intro n hn
    by_cases hp : moebius n = 1
    · simp only [if_pos hp]
      have hmem := hgp_mem n (Finset.mem_filter.2 ⟨hn, hp⟩)
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hmem
      obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
      exact ⟨h3, h2, by rw [h4, hp]⟩
    · simp only [if_neg hp]
      have hmem := hgm_mem n (Finset.mem_filter.2 ⟨hn, hp⟩)
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hmem
      obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
      have hm : moebius n = -1 := (hsign n hn).resolve_left hp
      exact ⟨h3, h2, by rw [h4, hm]; norm_num⟩

open Classical in
/-- The low-breadth squarefree vertices of the full cells of a shell. -/
def lowBreadthShell (c₀ X : ℝ) (H₀ J : ℕ) : Finset ℕ :=
  (Finset.Ioc ⌊X⌋₊ (⌊X⌋₊ + J * H₀)).filter
    (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X))

/-- The cell of an integer of the tiled range. -/
theorem exists_cell {B H₀ J n : ℕ} (hH : 0 < H₀) (hn : n ∈ Finset.Ioc B (B + J * H₀)) :
    ∃ j, j < J ∧ n ∈ Finset.Ioc (B + j * H₀) (B + j * H₀ + H₀) := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
  refine ⟨(n - B - 1) / H₀, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hH]
    omega
  · have hd := Nat.div_add_mod (n - B - 1) H₀
    have hm := Nat.mod_lt (n - B - 1) hH
    refine Finset.mem_Ioc.2 ⟨?_, ?_⟩
    · have : (n - B - 1) / H₀ * H₀ ≤ n - B - 1 := Nat.div_mul_le_self _ _
      omega
    · have e : (n - B - 1) / H₀ * H₀ = H₀ * ((n - B - 1) / H₀) := Nat.mul_comm _ _
      omega

/-- Distinct cells are disjoint. -/
theorem cell_eq_of_mem {B H₀ j j' n : ℕ} (hj : n ∈ Finset.Ioc (B + j * H₀) (B + j * H₀ + H₀))
    (hj' : n ∈ Finset.Ioc (B + j' * H₀) (B + j' * H₀ + H₀)) : j = j' := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hj
  obtain ⟨h1', h2'⟩ := Finset.mem_Ioc.1 hj'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (j + 1) * H₀ ≤ j' * H₀ := Nat.mul_le_mul_right H₀ h
    have e : (j + 1) * H₀ = j * H₀ + H₀ := by ring
    omega
  · have : (j' + 1) * H₀ ≤ j * H₀ := Nat.mul_le_mul_right H₀ h
    have e : (j' + 1) * H₀ = j' * H₀ + H₀ := by ring
    omega

open Classical in
/-- **Low-breadth transport across a dyadic shell.**  Fix `0 < c₀ < 1` and `C`.  For all large
`X`, with `W = √X exp(log X/log log X)`, the shell `(X, 2X]` is cut into `J` full cells of length
`H₀ ∈ [W/2, W]` and a terminal piece shorter than `H₀`; there is an injection `f` moving every
low-breadth squarefree integer of the full cells (`ω(n) ≤ c₀ log log X`) to an integer of its own
cell, outside the low-breadth set, of the opposite Möbius sign; and for every `0 ≤ x ≤ C/X` the
first-order Gibbs cost of all the moves together with the mass of the terminal piece is at most
`(2C + 1) W = X^{1/2+o(1)}`. -/
theorem lowBreadth_transport_shell {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ < 1) (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∃ (H₀ J : ℕ) (f : ℕ → ℕ),
      growingReciprocalMarkerWindow X / 2 ≤ (H₀ : ℝ) ∧ (H₀ : ℝ) ≤ growingReciprocalMarkerWindow X
      ∧ ⌊X⌋₊ + J * H₀ ≤ ⌊2 * X⌋₊ ∧ ⌊2 * X⌋₊ < ⌊X⌋₊ + (J + 1) * H₀
      ∧ Set.InjOn f (lowBreadthShell c₀ X H₀ J)
      ∧ (∀ n ∈ lowBreadthShell c₀ X H₀ J, f n ∈ Finset.Ioc ⌊X⌋₊ (⌊X⌋₊ + J * H₀)
          ∧ f n ∉ lowBreadthShell c₀ X H₀ J ∧ moebius (f n) = -moebius n
          ∧ |((f n : ℕ) : ℝ) - (n : ℝ)| ≤ (H₀ : ℝ))
      ∧ ∀ x : ℝ, 0 ≤ x → x ≤ C / X →
          ∑ n ∈ lowBreadthShell c₀ X H₀ J,
              |Real.exp (-(x * (n : ℝ))) - Real.exp (-(x * ((f n : ℕ) : ℝ)))|
            + ∑ n ∈ Finset.Ioc (⌊X⌋₊ + J * H₀) ⌊2 * X⌋₊, Real.exp (-(x * (n : ℝ)))
          ≤ (2 * C + 1) * growingReciprocalMarkerWindow X := by
  have hWtop : Tendsto growingReciprocalMarkerWindow atTop atTop := by
    have h1 : Tendsto (fun X : ℝ => Real.sqrt X) atTop atTop := Real.tendsto_sqrt_atTop
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
    rw [growingReciprocalMarkerWindow]
    have hlX : 1 < Real.log X := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hH : 1 ≤ growingReciprocalMarkerH X := by
      rw [growingReciprocalMarkerH]
      exact Real.one_le_exp (div_nonneg (by linarith) (Real.log_pos hlX).le)
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hH
  filter_upwards [lowBreadth_cell_matching hc0 hc1, hWtop.eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with X hmatch hW2 hX1
  set W := growingReciprocalMarkerWindow X with hW
  set B : ℕ := ⌊X⌋₊ with hB
  set H₀ : ℕ := ⌊W⌋₊ with hH₀
  have hH₀le : (H₀ : ℝ) ≤ W := Nat.floor_le (by linarith)
  have hH₀ge : W / 2 ≤ (H₀ : ℝ) := by
    have := Nat.lt_floor_add_one W; rw [← hH₀] at this; linarith
  have hH₀pos : 0 < H₀ := by
    have : (0 : ℝ) < (H₀ : ℝ) := by linarith
    exact_mod_cast this
  have hX0 : 0 < X := by linarith
  have hBle : (B : ℝ) ≤ X := Nat.floor_le hX0.le
  have hBgt : X - 1 < (B : ℝ) := by have := Nat.lt_floor_add_one X; rw [← hB] at this; linarith
  have hB2 : B ≤ ⌊2 * X⌋₊ := Nat.floor_le_floor (by linarith)
  set J : ℕ := (⌊2 * X⌋₊ - B) / H₀ with hJ
  have hJle : B + J * H₀ ≤ ⌊2 * X⌋₊ := by
    have h := Nat.div_mul_le_self (⌊2 * X⌋₊ - B) H₀
    rw [← hJ] at h
    calc B + J * H₀ ≤ B + (⌊2 * X⌋₊ - B) := Nat.add_le_add_left h B
      _ = ⌊2 * X⌋₊ := Nat.add_sub_cancel' hB2
  have hJlt : ⌊2 * X⌋₊ < B + (J + 1) * H₀ := by
    have := Nat.lt_div_mul_add (a := ⌊2 * X⌋₊ - B) hH₀pos
    rw [← hJ] at this
    have e : (J + 1) * H₀ = J * H₀ + H₀ := by ring
    omega
  -- the cells and their matchings
  have hcell : ∀ j : ℕ, ∃ g : ℕ → ℕ, j < J →
      Set.InjOn g (lowBreadthCell c₀ X (B + j * H₀) H₀) ∧
        ∀ n ∈ lowBreadthCell c₀ X (B + j * H₀) H₀, g n ∈ Finset.Ioc (B + j * H₀) (B + j * H₀ + H₀)
          ∧ g n ∉ lowBreadthCell c₀ X (B + j * H₀) H₀ ∧ moebius (g n) = -moebius n := by
    intro j
    by_cases hj : j < J
    · have hY1 : X - 1 ≤ ((B + j * H₀ : ℕ) : ℝ) := by push_cast; nlinarith [hBgt]
      have hY2 : ((B + j * H₀ : ℕ) : ℝ) ≤ 2 * X := by
        have h1 : B + j * H₀ ≤ ⌊2 * X⌋₊ := le_trans (by
          have := Nat.mul_le_mul_right H₀ hj.le; omega) hJle
        have h2 : ((⌊2 * X⌋₊ : ℕ) : ℝ) ≤ 2 * X := Nat.floor_le (by linarith)
        exact le_trans (by exact_mod_cast h1) h2
      obtain ⟨g, hg⟩ := hmatch (B + j * H₀) H₀ hY1 hY2 hH₀ge (by linarith)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨id, fun h => absurd h hj⟩
  choose g hg using hcell
  -- the global map
  set jf : ℕ → ℕ := fun n => (n - B - 1) / H₀ with hjf
  have hjf_mem : ∀ n ∈ Finset.Ioc B (B + J * H₀),
      jf n < J ∧ n ∈ Finset.Ioc (B + jf n * H₀) (B + jf n * H₀ + H₀) := by
    intro n hn
    obtain ⟨j, hjJ, hj⟩ := exists_cell hH₀pos hn
    have hjeq : jf n = j := by
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hn
      obtain ⟨h3, h4⟩ := Finset.mem_Ioc.1 hj
      rw [hjf]
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have e : j * H₀ = j * H₀ := rfl; omega
      · have e : (j + 1) * H₀ = j * H₀ + H₀ := by ring
        omega
    rw [hjeq]; exact ⟨hjJ, hj⟩
  have hshell_cell : ∀ n ∈ lowBreadthShell c₀ X H₀ J,
      n ∈ lowBreadthCell c₀ X (B + jf n * H₀) H₀ := by
    intro n hn
    rw [lowBreadthShell, Finset.mem_filter] at hn
    obtain ⟨hn1, hn2⟩ := hn
    rw [lowBreadthCell, Finset.mem_filter]
    exact ⟨(hjf_mem n hn1).2, hn2⟩
  refine ⟨H₀, J, fun n => g (jf n) n, hH₀ge, hH₀le, hJle, hJlt, ?_, ?_, ?_⟩
  · -- injectivity
    intro a ha b hb hab
    have ha' := Finset.mem_coe.1 ha
    have hb' := Finset.mem_coe.1 hb
    have haJ := (hjf_mem a (Finset.mem_filter.1 ha').1).1
    have hbJ := (hjf_mem b (Finset.mem_filter.1 hb').1).1
    obtain ⟨-, hga⟩ := hg (jf a) haJ
    obtain ⟨-, hgb⟩ := hg (jf b) hbJ
    have hma := (hga a (hshell_cell a ha')).1
    have hmb := (hgb b (hshell_cell b hb')).1
    simp only at hab
    rw [hab] at hma
    have hjj : jf a = jf b := cell_eq_of_mem hma hmb
    have hbc := hshell_cell b hb'
    rw [← hjj] at hbc hab
    exact (hg (jf a) haJ).1 (Finset.mem_coe.2 (hshell_cell a ha')) (Finset.mem_coe.2 hbc) hab
  · intro n hn
    have hJn := (hjf_mem n (Finset.mem_filter.1 hn).1).1
    have hnc := (hjf_mem n (Finset.mem_filter.1 hn).1).2
    obtain ⟨hmem, hnot, hsign⟩ := (hg (jf n) hJn).2 n (hshell_cell n hn)
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hmem
    obtain ⟨h3, h4⟩ := Finset.mem_Ioc.1 hnc
    have hup : B + jf n * H₀ + H₀ ≤ B + J * H₀ := by
      calc B + jf n * H₀ + H₀ = B + (jf n + 1) * H₀ := by ring
        _ ≤ B + J * H₀ := Nat.add_le_add_left (Nat.mul_le_mul_right H₀ (Nat.succ_le_of_lt hJn)) B
    refine ⟨Finset.mem_Ioc.2 ⟨lt_of_le_of_lt (Nat.le_add_right B (jf n * H₀)) h1,
      le_trans h2 hup⟩, ?_, hsign, ?_⟩
    · intro hin
      apply hnot
      rw [lowBreadthShell, Finset.mem_filter] at hin
      rw [lowBreadthCell, Finset.mem_filter]
      exact ⟨hmem, hin.2⟩
    · rw [abs_le]
      constructor
      · have : (B + jf n * H₀ : ℝ) < ((g (jf n) n : ℕ) : ℝ) := by exact_mod_cast h1
        have : (n : ℝ) ≤ (B + jf n * H₀ + H₀ : ℝ) := by exact_mod_cast h4
        linarith
      · have : ((g (jf n) n : ℕ) : ℝ) ≤ (B + jf n * H₀ + H₀ : ℝ) := by exact_mod_cast h2
        have : (B + jf n * H₀ : ℝ) < (n : ℝ) := by exact_mod_cast h3
        linarith
  · -- the Gibbs cost
    intro x hx0 hxC
    have hedge : ∀ n ∈ lowBreadthShell c₀ X H₀ J,
        |Real.exp (-(x * (n : ℝ))) - Real.exp (-(x * ((g (jf n) n : ℕ) : ℝ)))| ≤ x * W := by
      intro n hn
      have hJn := (hjf_mem n (Finset.mem_filter.1 hn).1).1
      have hnc := (hjf_mem n (Finset.mem_filter.1 hn).1).2
      obtain ⟨hmem, -, -⟩ := (hg (jf n) hJn).2 n (hshell_cell n hn)
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hmem
      obtain ⟨h3, h4⟩ := Finset.mem_Ioc.1 hnc
      refine RHTower.abs_gibbsEdge_le hx0 (Nat.cast_nonneg _) (Nat.cast_nonneg _) ?_
      rw [abs_le]
      constructor
      · have : (B + jf n * H₀ : ℝ) < (n : ℝ) := by exact_mod_cast h3
        have : ((g (jf n) n : ℕ) : ℝ) ≤ (B + jf n * H₀ + H₀ : ℝ) := by exact_mod_cast h2
        linarith
      · have : (n : ℝ) ≤ (B + jf n * H₀ + H₀ : ℝ) := by exact_mod_cast h4
        have : (B + jf n * H₀ : ℝ) < ((g (jf n) n : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
    have hS1 : ∑ n ∈ lowBreadthShell c₀ X H₀ J,
          |Real.exp (-(x * (n : ℝ))) - Real.exp (-(x * ((g (jf n) n : ℕ) : ℝ)))|
        ≤ 2 * C * W := by
      refine (Finset.sum_le_sum hedge).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((lowBreadthShell c₀ X H₀ J).card : ℝ) ≤ 2 * X := by
        have h1 : (lowBreadthShell c₀ X H₀ J).card ≤ J * H₀ := by
          have h := Finset.card_le_card (show lowBreadthShell c₀ X H₀ J
              ⊆ Finset.Ioc B (B + J * H₀) from Finset.filter_subset _ _)
          rw [Nat.card_Ioc, Nat.add_sub_cancel_left] at h
          exact h
        have h2 : (J * H₀ : ℝ) ≤ 2 * X := by
          have h3 : ((⌊2 * X⌋₊ : ℕ) : ℝ) ≤ 2 * X := Nat.floor_le (by linarith)
          have h4 : ((B + J * H₀ : ℕ) : ℝ) ≤ ((⌊2 * X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hJle
          push_cast at h4
          have h5 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg _
          linarith
        exact le_trans (by exact_mod_cast h1) h2
      have hxX : x * X ≤ C := by rw [le_div_iff₀ hX0] at hxC; linarith
      have hW0 : 0 ≤ W := by linarith
      calc ((lowBreadthShell c₀ X H₀ J).card : ℝ) * (x * W) ≤ 2 * X * (x * W) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = 2 * (x * X) * W := by ring
        _ ≤ 2 * C * W := by nlinarith [hxX, hW0]
    have hS2 : ∑ n ∈ Finset.Ioc (B + J * H₀) ⌊2 * X⌋₊, Real.exp (-(x * (n : ℝ))) ≤ W := by
      have hterm : ∀ n ∈ Finset.Ioc (B + J * H₀) ⌊2 * X⌋₊, Real.exp (-(x * (n : ℝ))) ≤ 1 := by
        intro n _
        rw [Real.exp_le_one_iff]
        have : 0 ≤ x * (n : ℝ) := mul_nonneg hx0 (Nat.cast_nonneg _)
        linarith
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]
      have : ⌊2 * X⌋₊ - (B + J * H₀) ≤ H₀ := by
        have e : (J + 1) * H₀ = J * H₀ + H₀ := by ring
        omega
      exact le_trans (by exact_mod_cast this) hH₀le
    linarith

open Classical in
/-- **Low-breadth transport in a cell.**  For fixed `0 < c₀ < 1`, every sufficiently large cell
`(X, X+H]`, `H = √X exp(log X/log log X)`, admits disjoint opposite-Möbius-sign edges of
displacement at most `H` covering every squarefree `n` of the cell with `ω(n) ≤ c₀ log log X`, the
other endpoint of every edge lying outside that low-breadth set. -/
theorem lowBreadth_matching_cell {c₀ : ℝ} (hc0 : 0 < c₀) (hc1 : c₀ < 1) :
    ∀ᶠ X : ℝ in atTop, ∃ f : ℕ → ℕ,
      Set.InjOn f ((Finset.Ioc ⌊X⌋₊ ⌊X + growingReciprocalMarkerWindow X⌋₊).filter
        (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X)))
      ∧ ∀ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊X + growingReciprocalMarkerWindow X⌋₊).filter
          (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X)),
        f n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + growingReciprocalMarkerWindow X⌋₊
        ∧ f n ∉ (Finset.Ioc ⌊X⌋₊ ⌊X + growingReciprocalMarkerWindow X⌋₊).filter
            (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X))
        ∧ moebius (f n) = -moebius n
        ∧ |((f n : ℕ) : ℝ) - (n : ℝ)| ≤ growingReciprocalMarkerWindow X := by
  have hWtop : Tendsto growingReciprocalMarkerWindow atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ Real.tendsto_sqrt_atTop
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with X hX
    rw [growingReciprocalMarkerWindow]
    have hlX : 1 < Real.log X := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Real.exp_one_lt_d9; linarith
    have hH : 1 ≤ growingReciprocalMarkerH X := by
      rw [growingReciprocalMarkerH]
      exact Real.one_le_exp (div_nonneg (by linarith) (Real.log_pos hlX).le)
    exact le_mul_of_one_le_right (Real.sqrt_nonneg _) hH
  filter_upwards [lowBreadth_cell_matching hc0 hc1, hWtop.eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with X hmatch hW2 hX1
  set W := growingReciprocalMarkerWindow X with hW
  have hX0 : 0 < X := by linarith
  set B : ℕ := ⌊X⌋₊ with hB
  set H₀ : ℕ := ⌊X + W⌋₊ - B with hH₀
  have hBle : (B : ℝ) ≤ X := Nat.floor_le hX0.le
  have hBgt : X - 1 < (B : ℝ) := by have := Nat.lt_floor_add_one X; rw [← hB] at this; linarith
  have htop_le : ((⌊X + W⌋₊ : ℕ) : ℝ) ≤ X + W := Nat.floor_le (by linarith)
  have htop_gt : X + W - 1 < ((⌊X + W⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (X + W); linarith
  have hBtop : B ≤ ⌊X + W⌋₊ := Nat.floor_le_floor (by linarith)
  have hH₀R : (H₀ : ℝ) = ((⌊X + W⌋₊ : ℕ) : ℝ) - (B : ℝ) := by
    rw [hH₀, Nat.cast_sub hBtop]
  have hcell : Finset.Ioc B ⌊X + W⌋₊ = Finset.Ioc B (B + H₀) := by
    rw [hH₀, Nat.add_sub_cancel' hBtop]
  obtain ⟨f, hinj, hf⟩ := hmatch B H₀ (by linarith) (by linarith) (by rw [hH₀R]; linarith)
    (by rw [hH₀R]; linarith)
  have hL : (Finset.Ioc B ⌊X + W⌋₊).filter
        (fun n => moebius n ≠ 0 ∧ (n.primeFactors.card : ℝ) ≤ c₀ * Real.log (Real.log X))
      = lowBreadthCell c₀ X B H₀ := by rw [hcell, lowBreadthCell]
  rw [hL, hcell]
  refine ⟨f, hinj, fun n hn => ?_⟩
  obtain ⟨hmem, hnot, hsign⟩ := hf n hn
  refine ⟨hmem, hnot, hsign, ?_⟩
  have hn' := (Finset.mem_filter.1 hn).1
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hmem
  obtain ⟨h3, h4⟩ := Finset.mem_Ioc.1 hn'
  have e1 : (B : ℝ) + 1 ≤ ((f n : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h1
  have e2 : ((f n : ℕ) : ℝ) ≤ ((B + H₀ : ℕ) : ℝ) := by exact_mod_cast h2
  have e3 : (B : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h3
  have e4 : (n : ℝ) ≤ ((B + H₀ : ℕ) : ℝ) := by exact_mod_cast h4
  have e5 : ((B + H₀ : ℕ) : ℝ) = ((⌊X + W⌋₊ : ℕ) : ℝ) := by
    rw [hH₀, Nat.add_sub_cancel' hBtop]
  rw [abs_le]
  constructor <;> linarith

end

end RHTower.Sieve
