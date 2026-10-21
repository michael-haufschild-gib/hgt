import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowFloorPolarAsymptotics
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowLiouvilleMirror
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The window spectrum with a de la Vallée Poussin remainder

The prime-side ceiling on windows of length `L` is `c(L) = e^{L/2}(1 + o(1))` and the floor is
`−e^{L/2}(1 + o(1))` (`tendsto_windowCeiling_div_exp`, `tendsto_windowFloor_div_exp`); on the lag
side the corpus's strongest unconditional envelope is `P_v ≥ −|φ(0)| − C e^{v/2 − √v/10}`
(`zeta_lag_envelope`). This module gives the window spectrum the same strength. Unconditionally
there are `C ≥ 0`, `κ > 0` with, for all large `L`,

* `|x| ≤ e^{L/2} + C e^{L/2 − κ√L}` for every window deviation `x` at length `L`
  (`exists_eventually_abs_windowDeviations_le_exp_half_add_remainder`);
* some window deviation is `≥ e^{L/2} − C e^{L/2 − κ√L}`
  (`exists_eventually_exists_windowDeviation_ge_exp_half_sub_remainder`);
* hence `|c(L) − e^{L/2}| ≤ C e^{L/2 − κ√L}` and `|floor(L) + e^{L/2}| ≤ C e^{L/2 − κ√L}`
  (`exists_eventually_abs_windowCeiling_sub_exp_half_le`,
  `exists_eventually_abs_windowFloor_add_exp_half_le`), and `c(L)/e^{L/2} − 1 ≤ C e^{−κ√L}`.

**Mechanism, upper side.** The prime number theorem with error term,
`|ψ(x) − x| ≤ K x e^{−c√(log x)}` (`RHTower.exists_psi_error_eventually`), enters the polar Schur
bound of `PrimeWindowCeilingWidthLaw` through the majorant `ψ(e^y) ≤ e^y + K e^y e^{−c√y} + B`
(`exists_psi_exp_le_dlvp`). At the point `τ` of a window of length `L` the error at distance `τ`
costs `K e^{L/2} e^{−(L−τ)/2} e^{−c√τ}` against the polar weight `φ = e^{−τ/2} + e^{−(L−τ)/2}`.
Near the ends (`τ < L/4`) the factor `e^{−(L−τ)/2} ≤ e^{−L/4} e^{−τ/2}` pays; in the bulk
(`τ ≥ L/4`) the error `e^{−c√τ} ≤ e^{−c√L/2}` pays (`exp_neg_half_mul_exp_neg_sqrt_le`). The
Schur constant is `e^{L/2}(1 + 2K(e^{−c√L/2} + e^{−L/4})) + B + (1 + L)²`
(`abs_nodeArchEnergy_sub_weilEnergy_le_dlvp`): the polar weight loses at the midpoint only
against power errors `x^γ` (the loss `1/4 + β/2` of the width law), not against the
de la Vallée Poussin error.

**Mechanism, lower side.** The polar test with cutoff `δ = e^{−L/2}` has prime side
`≥ 2δ (e^T − 1 − D(T))`, `T = L − 2δ`, with the integrated deficit `D`
(`primeSide_polarTest_ge`, `riesz_eq_deficit`), and the two-sided majorant gives
`|D(T)| ≤ T (K e^{c²/2} e^{T} e^{−c√T} + B)` (`abs_ccmLogChebyshevDeficitPrimitive_le_dlvp`), since
`e^{t − c√t} ≤ e^{c²/2} e^{T − c√T}` on `[0, T]` (`exp_sub_mul_sqrt_le_of_le`). The floor follows
from the Liouville mirror `|c(L) + floor(L)| ≤ 2T(N) = O(L)`.

The gap to RH is unchanged: RH is `c(L) ≤ e^{L/2} + O(L)` (`riemannHypothesis_of_windowCeiling_le`),
and `e^{L/2 − κ√L}` is `O(e^{θL})` for no `θ < 1/2`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open RHTower RHTower.WeilOneSided
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The Schur gain of the de la Vallée Poussin error -/

/-- The gain of the de la Vallée Poussin error against the polar weight on a window of length
`L`: `e^{−κ√L/2} + e^{−L/4}`. -/
def dlvpSchurGain (κ L : ℝ) : ℝ := Real.exp (-(κ * Real.sqrt L / 2)) + Real.exp (-(L / 4))

theorem dlvpSchurGain_nonneg (κ L : ℝ) : 0 ≤ dlvpSchurGain κ L := by
  unfold dlvpSchurGain; positivity

/-- **The error at distance `s` pays the polar weight.** For `0 ≤ s ≤ L`,
`e^{−(L−s)/2} e^{−κ√s} ≤ (e^{−κ√L/2} + e^{−L/4}) (e^{−s/2} + e^{−(L−s)/2})`: in the bulk
`s ≥ L/4` the error factor is at most `e^{−κ√L/2}`; near the ends `s < L/4` the weight itself
satisfies `e^{−(L−s)/2} ≤ e^{−L/4} e^{−s/2}`. -/
theorem exp_neg_half_mul_exp_neg_sqrt_le {κ L s : ℝ} (hκ : 0 ≤ κ) (hL : 0 ≤ L) (hs : 0 ≤ s) :
    Real.exp (-(L - s) / 2) * Real.exp (-κ * Real.sqrt s) ≤
      dlvpSchurGain κ L * (Real.exp (-s / 2) + Real.exp (-(L - s) / 2)) := by
  unfold dlvpSchurGain
  have h1 : 0 < Real.exp (-s / 2) := Real.exp_pos _
  have h2 : 0 < Real.exp (-(L - s) / 2) := Real.exp_pos _
  have h3 : 0 < Real.exp (-(κ * Real.sqrt L / 2)) := Real.exp_pos _
  have h4 : 0 < Real.exp (-(L / 4)) := Real.exp_pos _
  by_cases hbulk : L / 4 ≤ s
  · -- bulk: `√s ≥ √L / 2`
    have hsq : Real.sqrt L / 2 ≤ Real.sqrt s := by
      rw [Real.le_sqrt (by positivity) hs, div_pow, Real.sq_sqrt hL]
      linarith
    have herr : Real.exp (-κ * Real.sqrt s) ≤ Real.exp (-(κ * Real.sqrt L / 2)) :=
      Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hsq hκ])
    calc Real.exp (-(L - s) / 2) * Real.exp (-κ * Real.sqrt s)
        ≤ Real.exp (-(L - s) / 2) * Real.exp (-(κ * Real.sqrt L / 2)) :=
          mul_le_mul_of_nonneg_left herr h2.le
      _ ≤ _ := by nlinarith [mul_pos h3 h1, mul_pos h4 h1, mul_pos h4 h2]
  · -- ends: `e^{−(L−s)/2} = e^{−s/2} e^{−(L−2s)/2} ≤ e^{−s/2} e^{−L/4}`
    have hend : s < L / 4 := not_le.mp hbulk
    have hsplit : Real.exp (-(L - s) / 2) = Real.exp (-s / 2) * Real.exp (-(L - 2 * s) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmid : Real.exp (-(L - 2 * s) / 2) ≤ Real.exp (-(L / 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    have herr : Real.exp (-κ * Real.sqrt s) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg hκ (Real.sqrt_nonneg s))
    calc Real.exp (-(L - s) / 2) * Real.exp (-κ * Real.sqrt s)
        ≤ Real.exp (-(L - s) / 2) * 1 := mul_le_mul_of_nonneg_left herr h2.le
      _ = Real.exp (-s / 2) * Real.exp (-(L - 2 * s) / 2) := by rw [mul_one, hsplit]
      _ ≤ Real.exp (-s / 2) * Real.exp (-(L / 4)) := mul_le_mul_of_nonneg_left hmid h1.le
      _ ≤ _ := by nlinarith [mul_pos h3 h1, mul_pos h3 h2, mul_pos h4 h2]

/-! ### 2. The prime number theorem with error term as a majorant -/

/-- **The de la Vallée Poussin majorant in the logarithmic variable.** There are `K ≥ 0`, `c > 0`,
`B ≥ 0` with `ψ(e^y) ≤ e^y + K e^y e^{−c√y} + B` for every `y ≥ 0`; `B` absorbs the finitely
many small `y` through Chebyshev's bound `ψ(x) ≤ (log 4 + 4) x`. -/
theorem exists_psi_exp_le_dlvp : ∃ K c B : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ B ∧ ∀ y : ℝ, 0 ≤ y →
    Chebyshev.psi (Real.exp y) ≤
      Real.exp y + K * (Real.exp y * Real.exp (-c * Real.sqrt y)) + B := by
  obtain ⟨K, c, hc, hK, hev⟩ := RHTower.exists_psi_error_eventually
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hev
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmax : 0 < max X₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K, c, (Real.log 4 + 4) * max X₀ 1, hK, hc, mul_nonneg (by linarith) hmax.le,
    fun y hy => ?_⟩
  have hx0 : 0 < Real.exp y := Real.exp_pos y
  have hterm : 0 ≤ K * (Real.exp y * Real.exp (-c * Real.sqrt y)) := by positivity
  have hB : 0 ≤ (Real.log 4 + 4) * max X₀ 1 := mul_nonneg (by linarith) hmax.le
  by_cases hge : X₀ ≤ Real.exp y
  · have hb := hX₀ (Real.exp y) hge
    rw [Real.log_exp] at hb
    linarith [le_abs_self (Chebyshev.psi (Real.exp y) - Real.exp y)]
  · have hlt : Real.exp y < X₀ := not_le.mp hge
    have h1 : Chebyshev.psi (Real.exp y) ≤ (Real.log 4 + 4) * Real.exp y :=
      Chebyshev.psi_le_const_mul_self hx0.le
    have h2 : (Real.log 4 + 4) * Real.exp y ≤ (Real.log 4 + 4) * max X₀ 1 :=
      mul_le_mul_of_nonneg_left (hlt.le.trans (le_max_left _ _)) (by linarith)
    linarith

/-! ### 3. The Schur bound with the de la Vallée Poussin majorant -/

/-- **The polar Schur bound with a de la Vallée Poussin majorant.** If
`ψ(e^y) ≤ e^y + K e^y e^{−κ√y} + B` for `y ≥ 0`, then on windows of length `L`
`|A − W| ≤ (e^{L/2}(1 + 2K·gain(κ, L)) + B + (1 + L)²) ‖c‖²`, where
`gain(κ, L) = e^{−κ√L/2} + e^{−L/4}`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_dlvp {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L))
    {K κ B : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ)
    (hψ : ∀ y : ℝ, 0 ≤ y → Chebyshev.psi (Real.exp y) ≤
      Real.exp y + K * (Real.exp y * Real.exp (-κ * Real.sqrt y)) + B) :
    |nodeArchEnergy c - weilEnergy c| ≤
      (Real.exp (L / 2) * (1 + 2 * K * dlvpSchurGain κ L) + B + (1 + L) ^ 2) * massOf c := by
  set C := Real.exp (L / 2) * (1 + 2 * K * dlvpSchurGain κ L) + B + (1 + L) ^ 2 with hCdef
  have hN : L ≤ Real.log ⌈Real.exp L⌉₊ :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log ⌈Real.exp L⌉₊ := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  have hψe : ∀ y : ℝ, 0 ≤ y → y ≤ L → Chebyshev.psi (Real.exp y) ≤
      Real.exp y + K * (Real.exp y * Real.exp (-κ * Real.sqrt y)) + B := fun y hy _ => hψ y hy
  -- the Schur quotient of the neighbour sum against the polar weight
  have hS : ∀ a t, t ∈ Ioo a (a + L) → ∑ n ∈ Finset.Ico 2 ⌈Real.exp L⌉₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        ((Ioo a (a + L)).indicator (polarWeight a L) (t - Real.log n) +
          (Ioo a (a + L)).indicator (polarWeight a L) (t + Real.log n)) ≤ C * polarWeight a L t := by
    intro a t ht
    refine (polar_schur_le_of_psi_le ht _ hψe).trans ?_
    set τ := t - a with hτdef
    have hτ0 : 0 ≤ τ := by rw [hτdef]; linarith [ht.1]
    have hτL : τ ≤ L := by rw [hτdef]; linarith [ht.2]
    have hφ : polarWeight a L t = Real.exp (-τ / 2) + Real.exp (-(L - τ) / 2) := by
      rw [polarWeight, clampWindow_of_mem (Ioo_subset_Icc_self ht)]
      congr 2; ring
    -- `e^{−τ/2} e^{τ} = e^{L/2} e^{−(L−τ)/2}`: the main term is the polar weight at the far end
    have hc1 : Real.exp (-τ / 2) * Real.exp τ = Real.exp (L / 2) * Real.exp (-(L - τ) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hc2 : Real.exp (-(L - τ) / 2) * Real.exp (L - τ) =
        Real.exp (L / 2) * Real.exp (-τ / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hp1 := exp_neg_half_mul_exp_neg_sqrt_le hκ hL hτ0
    have hp2 := exp_neg_half_mul_exp_neg_sqrt_le hκ hL (s := L - τ) (by linarith)
    rw [show L - (L - τ) = τ by ring] at hp2
    rw [hφ]
    have e1 : Real.exp (-τ / 2) *
        (Real.exp τ + K * (Real.exp τ * Real.exp (-κ * Real.sqrt τ)) + B) =
        Real.exp (L / 2) * Real.exp (-(L - τ) / 2) +
          K * Real.exp (L / 2) * (Real.exp (-(L - τ) / 2) * Real.exp (-κ * Real.sqrt τ)) +
          B * Real.exp (-τ / 2) := by
      linear_combination (1 + K * Real.exp (-κ * Real.sqrt τ)) * hc1
    have e2 : Real.exp (-(L - τ) / 2) *
        (Real.exp (L - τ) + K * (Real.exp (L - τ) * Real.exp (-κ * Real.sqrt (L - τ))) + B) =
        Real.exp (L / 2) * Real.exp (-τ / 2) +
          K * Real.exp (L / 2) * (Real.exp (-τ / 2) * Real.exp (-κ * Real.sqrt (L - τ))) +
          B * Real.exp (-(L - τ) / 2) := by
      linear_combination (1 + K * Real.exp (-κ * Real.sqrt (L - τ))) * hc2
    rw [e1, e2]
    have hKE : 0 ≤ K * Real.exp (L / 2) := by positivity
    have k1 := mul_le_mul_of_nonneg_left hp1 hKE
    have k2 := mul_le_mul_of_nonneg_left hp2 hKE
    rw [hCdef]
    nlinarith [k1, k2]
  rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_eq,
    linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  have hX : ∀ f ∈ c.support,
      |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (c f • logVector f)| ≤ c f * (C * ∫ u, ‖f.1 u‖ ^ 2) := by
    intro f hf
    obtain ⟨a, ha⟩ := hsupp f hf
    rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (hc f)]
    exact mul_le_mul_of_nonneg_left (abs_primeSide_le_of_window_schur ha hN
      (continuous_polarWeight a L).measurable (Real.exp_pos (-L / 2))
      (polarWeight_pos_lower hL) (polarWeight_le hL) fun t ht => hS a t ht) (hc f)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [WeilOneSided.massOf, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun f hf => ?_
  have := hX f hf
  linarith

/-! ### 4. The window spectrum with a de la Vallée Poussin remainder -/

/-- `B + (1 + L)² ≤ e^{L/2 − κ√L}` for all large `L`. -/
theorem eventually_add_sq_le_exp_half_sub_sqrt {B κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L in atTop, B + (1 + L) ^ 2 ≤ Real.exp (L / 2 - κ * Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (64 * κ ^ 2), eventually_ge_atTop (8 * Real.log (|B| + 66)),
    eventually_ge_atTop (0 : ℝ)] with L h1 h2 h0
  -- `κ√L ≤ L/8` once `√L ≥ 8κ`
  have hs : κ * Real.sqrt L ≤ L / 8 := by
    have h8 : 8 * κ ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) h0]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg L), Real.sq_sqrt h0]
  have hexp : Real.exp (3 * L / 8) ≤ Real.exp (L / 2 - κ * Real.sqrt L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp (3 * L / 8) = Real.exp (L / 8) * Real.exp (L / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hB : |B| + 66 ≤ Real.exp (L / 8) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]; linarith
  have hq := one_add_sq_le_exp_quarter h0
  have h1e : 1 ≤ Real.exp (L / 4) := Real.one_le_exp (by linarith)
  calc B + (1 + L) ^ 2 ≤ |B| + 66 * Real.exp (L / 4) := by linarith [le_abs_self B]
    _ ≤ (|B| + 66) * Real.exp (L / 4) := by
        linarith [mul_le_mul_of_nonneg_left h1e (abs_nonneg B)]
    _ ≤ Real.exp (L / 8) * Real.exp (L / 4) := mul_le_mul_of_nonneg_right hB (by positivity)
    _ = Real.exp (3 * L / 8) := hsplit.symm
    _ ≤ _ := hexp

/-- **The window spectrum with a de la Vallée Poussin remainder.** Unconditionally there are
`C ≥ 0` and `κ > 0` such that for all large `L` every window deviation `x` at length `L` satisfies
`|x| ≤ e^{L/2} + C e^{L/2 − κ√L}`. -/
theorem exists_eventually_abs_windowDeviations_le_exp_half_add_remainder :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L,
      |x| ≤ Real.exp (L / 2) + C * Real.exp (L / 2 - κ * Real.sqrt L) := by
  obtain ⟨K, c, B, hK, hc, -, hψ⟩ := exists_psi_exp_le_dlvp
  refine ⟨4 * K + 1, c / 2, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_add_sq_le_exp_half_sub_sqrt (B := B) (κ := c / 2) (by positivity),
    eventually_ge_atTop (4 * c ^ 2), eventually_ge_atTop (0 : ℝ)] with L hpoly h4 h0 x hx
  obtain ⟨cf, hcf, hs, hm, rfl⟩ := hx
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_dlvp hcf h0 hs hK hc.le hψ
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  -- the two pieces of the Schur gain against `e^{L/2 − (c/2)√L}`
  have hE : Real.exp (L / 2) * Real.exp (-(c * Real.sqrt L / 2)) =
      Real.exp (L / 2 - c / 2 * Real.sqrt L) := by
    rw [← Real.exp_add]; congr 1; ring
  have hq : Real.exp (L / 2) * Real.exp (-(L / 4)) ≤
      Real.exp (L / 2 - c / 2 * Real.sqrt L) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h2c : 2 * c ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) h0]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2c (Real.sqrt_nonneg L), Real.sq_sqrt h0]
  have hgain : Real.exp (L / 2) * (2 * K * dlvpSchurGain c L) ≤
      4 * K * Real.exp (L / 2 - c / 2 * Real.sqrt L) := by
    have h1 : Real.exp (L / 2) * (2 * K * dlvpSchurGain c L) =
        2 * K * (Real.exp (L / 2) * Real.exp (-(c * Real.sqrt L / 2))) +
          2 * K * (Real.exp (L / 2) * Real.exp (-(L / 4))) := by
      unfold dlvpSchurGain; ring
    rw [h1, hE]
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 2 * K)
    linarith
  have hC : Real.exp (L / 2) * (1 + 2 * K * dlvpSchurGain c L) + B + (1 + L) ^ 2 ≤
      Real.exp (L / 2) + (4 * K + 1) * Real.exp (L / 2 - c / 2 * Real.sqrt L) := by
    linarith [hgain, hpoly]
  calc |nodeArchEnergy cf - weilEnergy cf| ≤ _ := h
    _ ≤ (Real.exp (L / 2) + (4 * K + 1) * Real.exp (L / 2 - c / 2 * Real.sqrt L)) * massOf cf :=
      mul_le_mul_of_nonneg_right hC hm.le

/-- **The ceiling.** `c(L) ≤ e^{L/2} + C e^{L/2 − κ√L}` for all large `L`. -/
theorem exists_eventually_windowCeiling_le_exp_half_add_remainder :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      windowCeiling L ≤ Real.exp (L / 2) + C * Real.exp (L / 2 - κ * Real.sqrt L) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowDeviations_le_exp_half_add_remainder
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl] with L hL hne
  obtain ⟨x, hx, -⟩ := hne
  exact csSup_le ⟨x, hx⟩ fun y hy => (le_abs_self y).trans (hL y hy)

/-- **The floor.** `floor(L) ≥ −e^{L/2} − C e^{L/2 − κ√L}` for all large `L`. -/
theorem exists_eventually_windowFloor_ge_neg_exp_half_sub_remainder :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      -(Real.exp (L / 2) + C * Real.exp (L / 2 - κ * Real.sqrt L)) ≤ windowFloor L := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowDeviations_le_exp_half_add_remainder
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl] with L hL hne
  obtain ⟨x, hx, -⟩ := hne
  exact le_csInf ⟨x, hx⟩ fun y hy => (neg_le_neg (hL y hy)).trans (neg_abs_le y)

/-- **The rate of `c(L)/e^{L/2} → 1`.** `c(L)/e^{L/2} − 1 ≤ C e^{−κ√L}` for all large `L`. -/
theorem exists_eventually_windowCeiling_div_exp_sub_one_le :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      windowCeiling L / Real.exp (L / 2) - 1 ≤ C * Real.exp (-(κ * Real.sqrt L)) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_windowCeiling_le_exp_half_add_remainder
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev] with L hL
  have hE : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hsplit : Real.exp (L / 2 - κ * Real.sqrt L) =
      Real.exp (L / 2) * Real.exp (-(κ * Real.sqrt L)) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [sub_le_iff_le_add, div_le_iff₀ hE]
  rw [hsplit] at hL
  linarith

/-! ### 5. The lower side: the polar test attains the pole to de la Vallée Poussin precision -/

/-- **The two-sided de la Vallée Poussin majorant.** There are `K ≥ 0`, `c > 0`, `B ≥ 0` with
`|ψ(e^y) − e^y| ≤ K e^y e^{−c√y} + B` for every `y ≥ 0`. -/
theorem exists_abs_psi_exp_sub_le_dlvp : ∃ K c B : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ B ∧ ∀ y : ℝ, 0 ≤ y →
    |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
      K * (Real.exp y * Real.exp (-c * Real.sqrt y)) + B := by
  obtain ⟨K, c, hc, hK, hev⟩ := RHTower.exists_psi_error_eventually
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hev
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmax : 0 < max X₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K, c, (Real.log 4 + 5) * max X₀ 1, hK, hc, mul_nonneg (by linarith) hmax.le,
    fun y hy => ?_⟩
  have hx0 : 0 < Real.exp y := Real.exp_pos y
  have hterm : 0 ≤ K * (Real.exp y * Real.exp (-c * Real.sqrt y)) := by positivity
  have hB : 0 ≤ (Real.log 4 + 5) * max X₀ 1 := mul_nonneg (by linarith) hmax.le
  by_cases hge : X₀ ≤ Real.exp y
  · have hb := hX₀ (Real.exp y) hge
    rw [Real.log_exp] at hb
    linarith
  · have hlt : Real.exp y < X₀ := not_le.mp hge
    have h1 : Chebyshev.psi (Real.exp y) ≤ (Real.log 4 + 4) * Real.exp y :=
      Chebyshev.psi_le_const_mul_self hx0.le
    have h0 := Chebyshev.psi_nonneg (Real.exp y)
    have h2 : (Real.log 4 + 5) * Real.exp y ≤ (Real.log 4 + 5) * max X₀ 1 :=
      mul_le_mul_of_nonneg_left (hlt.le.trans (le_max_left _ _)) (by linarith)
    have h3 : Real.exp y ≤ (Real.log 4 + 5) * Real.exp y := by nlinarith
    rw [abs_le]; constructor <;> linarith

/-- `e^{t − c√t} ≤ e^{c²/2} e^{T − c√T}` for `0 ≤ t ≤ T`: `c(√T − √t) ≤ (c² + (√T − √t)²)/2` and
`(√T − √t)² ≤ T − t`. -/
theorem exp_sub_mul_sqrt_le_of_le {c t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    Real.exp t * Real.exp (-c * Real.sqrt t) ≤
      Real.exp (c ^ 2 / 2) * (Real.exp T * Real.exp (-c * Real.sqrt T)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hT : 0 ≤ T := ht.trans htT
  have hst : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have h1 := Real.sq_sqrt ht
  have h2 := Real.sq_sqrt hT
  have hs0 := Real.sqrt_nonneg t
  nlinarith [sq_nonneg (c - (Real.sqrt T - Real.sqrt t)), mul_nonneg hs0 (sub_nonneg.mpr hst)]

/-- **The integrated Chebyshev deficit to de la Vallée Poussin precision.** With the two-sided
majorant `|ψ(e^y) − e^y| ≤ K e^y e^{−c√y} + B`, `|D(T)| ≤ T (K e^{c²/2} e^{T} e^{−c√T} + B)` for
`T ≥ 0`, where `D(T) = ∫₀^T (e^t − ψ(e^t)) dt`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_le_dlvp {K c B : ℝ} (hK : 0 ≤ K)
    (hψ : ∀ y : ℝ, 0 ≤ y → |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
      K * (Real.exp y * Real.exp (-c * Real.sqrt y)) + B) {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T| ≤
      T * (K * Real.exp (c ^ 2 / 2) * (Real.exp T * Real.exp (-c * Real.sqrt T)) + B) := by
  unfold ccmLogChebyshevDeficitPrimitive
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp t - Chebyshev.psi (Real.exp t)) volume 0 T :=
    (Real.continuous_exp.intervalIntegrable 0 T).sub
      ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)
  set M := K * Real.exp (c ^ 2 / 2) * (Real.exp T * Real.exp (-c * Real.sqrt T)) + B with hM
  calc |∫ t in (0 : ℝ)..T, Real.exp t - Chebyshev.psi (Real.exp t)|
      ≤ ∫ t in (0 : ℝ)..T, |Real.exp t - Chebyshev.psi (Real.exp t)| :=
        intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ _t in (0 : ℝ)..T, M := by
        refine intervalIntegral.integral_mono_on hT hi.abs intervalIntegrable_const
          fun t ht => ?_
        rw [abs_sub_comm]
        refine (hψ t ht.1).trans ?_
        have := mul_le_mul_of_nonneg_left (exp_sub_mul_sqrt_le_of_le (c := c) ht.1 ht.2) hK
        rw [hM]
        linarith
    _ = T * M := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- `L ≤ e^{κ√L}` for all large `L`, from `e^u ≥ u⁴/24`. -/
theorem eventually_le_exp_mul_sqrt {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L in atTop, L ≤ Real.exp (κ * Real.sqrt L) := by
  filter_upwards [eventually_ge_atTop (24 / κ ^ 4), eventually_ge_atTop (0 : ℝ)] with L h1 hL0
  have hu : 0 ≤ κ * Real.sqrt L := by positivity
  have h4 := Real.pow_div_factorial_le_exp _ hu 4
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hsq : (κ * Real.sqrt L) ^ 4 = κ ^ 4 * L ^ 2 := by
    rw [mul_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, Real.sq_sqrt hL0]
  rw [hfac, hsq] at h4
  have hκ4 : 0 < κ ^ 4 := by positivity
  have h24 : 24 ≤ κ ^ 4 * L := by
    have := mul_le_mul_of_nonneg_left h1 hκ4.le
    rwa [mul_div_cancel₀ _ hκ4.ne'] at this
  nlinarith [h4, mul_nonneg hL0 (sub_nonneg.mpr h24)]

/-- **The deficit against the polar cutoff.** For `L ≥ 4` with `L ≤ e^{(c/2)√L}`, the integrated
deficit at `T = L − 2δ`, `δ = e^{−L/2}`, satisfies
`2δ |D(T)| ≤ 2 K e^{c²/2} e^{c} e^{L/2 − (c/2)√L} + 2B`: `√T ≥ √L − 1`, `δ e^T ≤ e^{L/2}`, `Lδ ≤ 1`
and `L e^{−c√L} ≤ e^{−(c/2)√L}`. -/
theorem two_mul_exp_neg_half_mul_abs_deficit_le {K c B : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hψ : ∀ y : ℝ, 0 ≤ y → |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
      K * (Real.exp y * Real.exp (-c * Real.sqrt y)) + B)
    {L : ℝ} (hL4 : 4 ≤ L) (hLexp : L ≤ Real.exp (c / 2 * Real.sqrt L)) :
    2 * Real.exp (-(L / 2)) *
        |ccmLogChebyshevDeficitPrimitive (L - 2 * Real.exp (-(L / 2)))| ≤
      2 * (K * Real.exp (c ^ 2 / 2) * Real.exp c) * Real.exp (L / 2 - c / 2 * Real.sqrt L) +
        2 * B := by
  have hL0 : 0 ≤ L := by linarith
  set E := Real.exp (L / 2) with hEdef
  have hEL : 0 < E := Real.exp_pos _
  set R := Real.exp (L / 2 - c / 2 * Real.sqrt L) with hRdef
  set δ := Real.exp (-(L / 2)) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEδ : δ * E = 1 := by
    rw [hδdef, hEdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hLδ1 : L * δ ≤ 1 := by
    have h1 : 1 + L / 2 + (L / 2) ^ 2 / 2 ≤ E := Real.quadratic_le_exp_of_nonneg (by linarith)
    have : L ≤ E := by nlinarith
    calc L * δ ≤ E * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = 1 := by rw [mul_comm]; exact hEδ
  set T := L - 2 * δ with hTdef
  have hT : 0 ≤ T := by linarith
  -- `δ e^T ≤ E`
  have hδT : δ * Real.exp T ≤ E := by
    have h1 : Real.exp T = E * E * Real.exp (-(2 * δ)) := by
      rw [hTdef, hEdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [h1, show δ * (E * E * Real.exp (-(2 * δ))) = (δ * E) * E * Real.exp (-(2 * δ)) by ring,
      hEδ, one_mul]
    exact mul_le_of_le_one_right hEL.le (Real.exp_le_one_iff.mpr (by linarith))
  -- `√T ≥ √L − 1`, hence `e^{−c√T} ≤ e^{c} e^{−c√L}`
  have hsL : 2 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0]; nlinarith
  have hsqT : Real.sqrt L - 1 ≤ Real.sqrt T := by
    rw [Real.le_sqrt (by linarith) hT]
    nlinarith [Real.sq_sqrt hL0]
  have hexpT : Real.exp (-c * Real.sqrt T) ≤ Real.exp c * Real.exp (-c * Real.sqrt L) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsqT hc.le])
  -- `L e^{−c√L} ≤ e^{−(c/2)√L}`
  have hLsmall : L * Real.exp (-c * Real.sqrt L) ≤ Real.exp (-(c / 2 * Real.sqrt L)) := by
    have hsplit : Real.exp (-c * Real.sqrt L) =
        Real.exp (-(c / 2 * Real.sqrt L)) * Real.exp (-(c / 2 * Real.sqrt L)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hLe : L * Real.exp (-(c / 2 * Real.sqrt L)) ≤ 1 := by
      calc L * Real.exp (-(c / 2 * Real.sqrt L))
          ≤ Real.exp (c / 2 * Real.sqrt L) * Real.exp (-(c / 2 * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_right hLexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hsplit, ← mul_assoc]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hLe
  have hER : E * Real.exp (-(c / 2 * Real.sqrt L)) = R := by
    rw [hEdef, hRdef, ← Real.exp_add, sub_eq_add_neg]
  have hp2 : L * Real.exp (-c * Real.sqrt T) ≤ Real.exp c * Real.exp (-(c / 2 * Real.sqrt L)) :=
    calc L * Real.exp (-c * Real.sqrt T)
        ≤ L * (Real.exp c * Real.exp (-c * Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left hexpT hL0
      _ = Real.exp c * (L * Real.exp (-c * Real.sqrt L)) := by ring
      _ ≤ Real.exp c * Real.exp (-(c / 2 * Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left hLsmall (Real.exp_pos _).le
  have hDabs := abs_ccmLogChebyshevDeficitPrimitive_le_dlvp hK hψ hT
  have hq := mul_le_mul hδT hp2 (by positivity) hEL.le
  have h0 : 0 ≤ K * Real.exp (c ^ 2 / 2) * (Real.exp T * Real.exp (-c * Real.sqrt T)) + B := by
    have := abs_nonneg (ccmLogChebyshevDeficitPrimitive T)
    rcases hT.lt_or_eq with hT' | hT'
    · exact nonneg_of_mul_nonneg_right (this.trans hDabs) hT'
    · rw [← hT']
      have h2 := hψ 0 le_rfl
      simp only [Real.sqrt_zero, mul_zero, Real.exp_zero, mul_one, one_mul] at h2 ⊢
      exact (abs_nonneg _).trans h2
  calc 2 * δ * |ccmLogChebyshevDeficitPrimitive T|
      ≤ 2 * δ * (T * (K * Real.exp (c ^ 2 / 2) *
          (Real.exp T * Real.exp (-c * Real.sqrt T)) + B)) :=
        mul_le_mul_of_nonneg_left hDabs (by positivity)
    _ ≤ 2 * δ * (L * (K * Real.exp (c ^ 2 / 2) *
          (Real.exp T * Real.exp (-c * Real.sqrt T)) + B)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h0) (by positivity)
        linarith
    _ = 2 * K * Real.exp (c ^ 2 / 2) *
          ((δ * Real.exp T) * (L * Real.exp (-c * Real.sqrt T))) + 2 * B * (L * δ) := by ring
    _ ≤ 2 * K * Real.exp (c ^ 2 / 2) *
          (E * (Real.exp c * Real.exp (-(c / 2 * Real.sqrt L)))) + 2 * B * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hq (by positivity))
          (mul_le_mul_of_nonneg_left hLδ1 (by positivity))
    _ = 2 * (K * Real.exp (c ^ 2 / 2) * Real.exp c) *
          (E * Real.exp (-(c / 2 * Real.sqrt L))) + 2 * B := by ring
    _ = 2 * (K * Real.exp (c ^ 2 / 2) * Real.exp c) * R + 2 * B := by rw [hER]

/-- **The polar test attains the pole to de la Vallée Poussin precision.** Unconditionally there
are `C ≥ 0`, `κ > 0` such that for all large `L` some window deviation at length `L` is
`≥ e^{L/2} − C e^{L/2 − κ√L}`. -/
theorem exists_eventually_exists_windowDeviation_ge_exp_half_sub_remainder :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop, ∃ x ∈ windowDeviations L,
      Real.exp (L / 2) - C * Real.exp (L / 2 - κ * Real.sqrt L) ≤ x := by
  classical
  obtain ⟨K, c, B, hK, hc, hB, hψ⟩ := exists_abs_psi_exp_sub_le_dlvp
  set K' := K * Real.exp (c ^ 2 / 2) * Real.exp c with hK'def
  have hK' : 0 ≤ K' := by positivity
  set C := K' + B + 4 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, c / 2, hC0, by positivity, ?_⟩
  filter_upwards [eventually_le_exp_mul_sqrt (κ := c / 2) (by positivity),
    eventually_add_sq_le_exp_half_sub_sqrt (B := 0) (κ := c / 2) (by positivity),
    eventually_ge_atTop (4 : ℝ), eventually_ge_atTop C] with L hLexp hpoly hL4 hLC
  rw [zero_add] at hpoly
  have hL0 : 0 ≤ L := by linarith
  have hD := two_mul_exp_neg_half_mul_abs_deficit_le hK hc hψ hL4 hLexp
  -- the polar test of the window `(0, L)` with cutoff `δ = e^{−L/2}`
  set E := Real.exp (L / 2) with hEdef
  have hEL : 0 < E := Real.exp_pos _
  set R := Real.exp (L / 2 - c / 2 * Real.sqrt L) with hRdef
  have hR0 : 0 < R := Real.exp_pos _
  set δ := Real.exp (-(L / 2)) with hδdef
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hLδ : 2 * δ < L := by linarith
  have hEδ : δ * E = 1 := by
    rw [hδdef, hEdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hδneg : Real.exp (-L / 2) = δ := by rw [hδdef]; congr 1; ring
  set T := L - 2 * δ with hTdef
  have hT : 0 ≤ T := by linarith
  set f := polarTestFn hδ hLδ
  set cf : WeilTestFn →₀ ℝ := Finsupp.single f 1
  have hcf : ∀ g, 0 ≤ cf g := fun g => by
    simp only [cf]; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  have hsupp : ∀ g ∈ cf.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L) := fun g hg => by
    have : g = f := by
      by_contra hne; exact (Finsupp.mem_support_iff.mp hg) (by simp [cf, Ne.symm hne])
    exact ⟨0, this ▸ polarTestFn_supp hδ hLδ⟩
  have hm := massOf_polarTest_pos hδ hLδ
  have hM := massOf_polarTest_le hδ hLδ
  rw [hδneg] at hM
  have hdev : nodeArchEnergy cf - weilEnergy cf =
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
    rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_single_test]
  have hP := primeSide_polarTest_ge hδ hLδ
  rw [riesz_eq_deficit hT, hδneg, ← hdev] at hP
  have hP' : 2 * δ * (Real.exp T - 1 - ccmLogChebyshevDeficitPrimitive T) ≤
      nodeArchEnergy cf - weilEnergy cf := hP
  refine ⟨(nodeArchEnergy cf - weilEnergy cf) / massOf cf, ⟨cf, hcf, hsupp, hm, rfl⟩, ?_⟩
  -- the pole: `2δ e^T ≥ 2E − 4`
  have heT : 2 * E - 4 ≤ 2 * δ * Real.exp T := by
    have h1 : Real.exp T = E * E * Real.exp (-(2 * δ)) := by
      rw [hTdef, hEdef, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have h2 : 1 - 2 * δ ≤ Real.exp (-(2 * δ)) := Real.one_sub_le_exp_neg _
    rw [h1]
    have : 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * E * Real.exp (-(2 * δ)) := by
      rw [show 2 * δ * (E * E * Real.exp (-(2 * δ))) = 2 * (δ * E) * E * Real.exp (-(2 * δ)) by
        ring, hEδ]; ring
    rw [this]
    nlinarith
  -- the prime side is at least `2E − 4 − 2δ − 2K'R − 2B`
  have hnum : 2 * E - 4 - 2 * δ - (2 * K' * R + 2 * B) ≤ nodeArchEnergy cf - weilEnergy cf := by
    have habs := mul_le_mul_of_nonneg_left (neg_abs_le (ccmLogChebyshevDeficitPrimitive T))
      (by positivity : (0 : ℝ) ≤ 2 * δ)
    linarith [hP', heT, hD, habs]
  -- `C R ≤ E`, since `C ≤ L ≤ e^{(c/2)√L}`
  have hER : E * Real.exp (-(c / 2 * Real.sqrt L)) = R := by
    rw [hEdef, hRdef, ← Real.exp_add, sub_eq_add_neg]
  have hECR : 0 ≤ E - C * R := by
    have h1' : C * Real.exp (-(c / 2 * Real.sqrt L)) ≤ 1 := by
      calc C * Real.exp (-(c / 2 * Real.sqrt L))
          ≤ Real.exp (c / 2 * Real.sqrt L) * Real.exp (-(c / 2 * Real.sqrt L)) :=
            mul_le_mul_of_nonneg_right (hLC.trans hLexp) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2' : C * R = E * (C * Real.exp (-(c / 2 * Real.sqrt L))) := by
      rw [mul_left_comm, hER]
    have h3' := mul_le_mul_of_nonneg_left h1' hEL.le
    rw [mul_one] at h3'
    linarith
  have hpoly' : B + 3 + L ≤ (B + 4) * R := by
    have h1' : 1 + L ≤ (1 + L) ^ 2 := by nlinarith
    have hB4 : (0 : ℝ) ≤ B + 4 := by linarith
    linarith [mul_le_mul_of_nonneg_left h1' hB4, mul_le_mul_of_nonneg_left hpoly hB4,
      mul_nonneg hB hL0]
  have hLEδ : E * L * δ = L := by
    rw [show E * L * δ = L * (δ * E) by ring, hEδ, mul_one]
  -- conclude: if the deviation were below `E − C R`, the prime side would be below its floor
  by_contra hcon
  push_neg at hcon
  rw [div_lt_iff₀ hm] at hcon
  have hmass : (E - C * R) * massOf cf ≤ (E - C * R) * (2 + 2 * L * δ) :=
    mul_le_mul_of_nonneg_left hM hECR
  linarith [hcon, hmass, hnum, hpoly', hLEδ, hδ1,
    mul_nonneg (mul_nonneg hC0 hR0.le) (mul_nonneg hL0 hδ.le)]

/-- **The ceiling from below.** `c(L) ≥ e^{L/2} − C e^{L/2 − κ√L}` for all large `L`. -/
theorem exists_eventually_exp_half_sub_remainder_le_windowCeiling :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      Real.exp (L / 2) - C * Real.exp (L / 2 - κ * Real.sqrt L) ≤ windowCeiling L := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_exists_windowDeviation_ge_exp_half_sub_remainder
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  obtain ⟨x, hx, hxge⟩ := hL
  exact hxge.trans (le_csSup (bddAbove_windowDeviations hL0) hx)

/-- **The window ceiling is the pole to de la Vallée Poussin precision:**
`|c(L) − e^{L/2}| ≤ C e^{L/2 − κ√L}` for all large `L`. -/
theorem exists_eventually_abs_windowCeiling_sub_exp_half_le :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      |windowCeiling L - Real.exp (L / 2)| ≤ C * Real.exp (L / 2 - κ * Real.sqrt L) := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, h₁⟩ := exists_eventually_windowCeiling_le_exp_half_add_remainder
  obtain ⟨C₂, κ₂, hC₂, hκ₂, h₂⟩ := exists_eventually_exp_half_sub_remainder_le_windowCeiling
  refine ⟨max C₁ C₂, min κ₁ κ₂, le_max_of_le_left hC₁, lt_min hκ₁ hκ₂, ?_⟩
  filter_upwards [h₁, h₂] with L h1 h2
  have hs := Real.sqrt_nonneg L
  have e1 : Real.exp (L / 2 - κ₁ * Real.sqrt L) ≤ Real.exp (L / 2 - min κ₁ κ₂ * Real.sqrt L) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left κ₁ κ₂])
  have e2 : Real.exp (L / 2 - κ₂ * Real.sqrt L) ≤ Real.exp (L / 2 - min κ₁ κ₂ * Real.sqrt L) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right κ₁ κ₂])
  have m1 := mul_le_mul (le_max_left C₁ C₂) e1 (Real.exp_pos _).le (le_max_of_le_left hC₁)
  have m2 := mul_le_mul (le_max_right C₁ C₂) e2 (Real.exp_pos _).le (le_max_of_le_left hC₁)
  rw [abs_le]; constructor <;> linarith

/-- **The window floor is minus the pole to de la Vallée Poussin precision:**
`|floor(L) + e^{L/2}| ≤ C e^{L/2 − κ√L}` for all large `L`, by the Liouville mirror
`|c(L) + floor(L)| ≤ 2T(N) = O(L)`. -/
theorem exists_eventually_abs_windowFloor_add_exp_half_le :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      |windowFloor L + Real.exp (L / 2)| ≤ C * Real.exp (L / 2 - κ * Real.sqrt L) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowCeiling_sub_exp_half_le
  refine ⟨C + 28, κ, by positivity, hκ, ?_⟩
  filter_upwards [hev, eventually_add_sq_le_exp_half_sub_sqrt (B := 0) hκ,
    eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl,
    eventually_ge_atTop (0 : ℝ)] with L hcl hpoly hne hL0
  rw [zero_add] at hpoly
  obtain ⟨x, hx, -⟩ := hne
  set N := ⌈Real.exp L⌉₊ with hN
  have hNpos : 0 < N := Nat.ceil_pos.mpr (Real.exp_pos L)
  have hLN : L ≤ Real.log N :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  have hlogN : Real.log N ≤ L + 1 := by
    have h1 : (N : ℝ) < Real.exp L + 1 := Nat.ceil_lt_add_one (Real.exp_pos L).le
    have h2 : Real.exp L + 1 ≤ Real.exp (L + 1) := by
      rw [Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (1 : ℝ)) (Real.exp_pos L).le,
        Real.one_le_exp hL0]
    calc Real.log N ≤ Real.log (Real.exp (L + 1)) :=
          Real.log_le_log (by exact_mod_cast hNpos) (h1.le.trans h2)
      _ = L + 1 := Real.log_exp _
  have hmir := abs_windowCeiling_add_windowFloor_le hL0 ⟨x, hx⟩ hLN
  have hdef := mirrorDefect_le hNpos
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hmir' := abs_le.mp hmir
  have hcl' := abs_le.mp hcl
  have h1' : 1 + L ≤ (1 + L) ^ 2 := by nlinarith
  have h28 : 4 * L + 28 ≤ 28 * Real.exp (L / 2 - κ * Real.sqrt L) := by linarith
  rw [abs_le]; constructor <;> linarith [hmir'.1, hmir'.2, hcl'.1, hcl'.2, hdef, hlogN, hlog4, h28]

end

end GaloisForLFunctions.BiScaleUncertainty
