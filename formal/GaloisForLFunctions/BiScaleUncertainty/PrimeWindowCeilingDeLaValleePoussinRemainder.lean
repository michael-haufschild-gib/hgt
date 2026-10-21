import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowFloorPolarAsymptotics
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The window ceiling with a de la Vallée Poussin remainder

The prime-side ceiling on windows of length `L` is `c(L) = e^{L/2}(1 + o(1))`
(`tendsto_windowCeiling_div_exp`); on the lag side the corpus's strongest unconditional envelope
is `P_v ≥ −|φ(0)| − C e^{v/2 − √v/10}` (`zeta_lag_envelope`). This module gives the window
spectrum the same strength. Unconditionally there are `C ≥ 0`, `κ > 0` with

`|x| ≤ e^{L/2} + C e^{L/2 − κ√L}`  for every window deviation `x` at every large length `L`

(`exists_eventually_abs_windowDeviations_le_exp_half_add_remainder`); hence
`c(L) ≤ e^{L/2} + C e^{L/2 − κ√L}`, `floor(L) ≥ −e^{L/2} − C e^{L/2 − κ√L}` and
`c(L)/e^{L/2} − 1 ≤ C e^{−κ√L}`.

**Mechanism.** The prime number theorem with error term, `|ψ(x) − x| ≤ K x e^{−c√(log x)}`
(`RHTower.exists_psi_error_eventually`), enters the polar Schur bound of
`PrimeWindowCeilingWidthLaw` through the majorant `ψ(e^y) ≤ e^y + K e^y e^{−c√y} + B`
(`exists_psi_exp_le_dlvp`). At the point `τ` of a window of length `L` the error at distance
`τ` costs `K e^{L/2} e^{−(L−τ)/2} e^{−c√τ}` against the polar weight
`φ = e^{−τ/2} + e^{−(L−τ)/2}`. Near the ends (`τ < L/4`) the factor
`e^{−(L−τ)/2} ≤ e^{−L/4} e^{−τ/2}` pays; in the bulk (`τ ≥ L/4`) the error `e^{−c√τ} ≤ e^{−c√L/2}`
pays (`exp_neg_half_mul_exp_neg_sqrt_le`). The Schur constant is therefore
`e^{L/2}(1 + 2K(e^{−c√L/2} + e^{−L/4})) + B + (1 + L)²` (`abs_nodeArchEnergy_sub_weilEnergy_le_dlvp`):
the polar weight loses at the midpoint only against power errors `x^γ` (the loss
`1/4 + β/2` of the width law), not against the de la Vallée Poussin error.

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

end

end GaloisForLFunctions.BiScaleUncertainty
