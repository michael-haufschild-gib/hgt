import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingDeLaValleePoussinRemainder
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontierVK

/-!
# The window spectrum with a Vinogradov–Korobov remainder

The window ceiling `c(L)` and floor `f(L)` of the prime side on windows of length `L` are the
pole `±e^{L/2}` up to a remainder, and the remainder is governed by the error term of the prime
number theorem through the polar Schur bound. `PrimeWindowCeilingDeLaValleePoussinRemainder`
obtains the remainder `C e^{L/2 − κ√L}` from `ψ(x) − x = O(x e^{−c√(log x)})`. This module feeds
the Vinogradov–Korobov prime number theorem `|ψ(x) − x| ≤ C x e^{−c (log x)^ex}` for every
`ex < 3/5` (`RHTower.chebyshevError_bound_rpow`) through the same mechanism. For every
`0 < ex < 3/5` there are `C ≥ 0`, `κ > 0` with, for all large `L`,

* `|x| ≤ e^{L/2} + C e^{L/2 − κ L^ex}` for every window deviation `x` at length `L`
  (`exists_eventually_abs_windowDeviations_le_exp_half_add_vk`);
* some window deviation is `≥ e^{L/2} − C e^{L/2 − κ L^ex}`
  (`exists_eventually_exists_windowDeviation_ge_exp_half_sub_vk`);
* `|c(L) − e^{L/2}| ≤ C e^{L/2 − κ L^ex}` and `|f(L) + e^{L/2}| ≤ C e^{L/2 − κ L^ex}`
  (`exists_eventually_abs_windowCeiling_sub_exp_half_le_vk`,
  `exists_eventually_abs_windowFloor_add_exp_half_le_vk`);
* the integrated Chebyshev deficit `D(T) = ∫₀^T (e^t − ψ(e^t)) dt` satisfies
  `|D(T)| ≤ C e^{T − κ T^ex}` (`exists_eventually_abs_ccmLogChebyshevDeficitPrimitive_le_vk`).

**Mechanism.** The polar Schur bound is proved for an arbitrary nonincreasing error profile
`0 ≤ E ≤ 1`: the error at distance `τ` of a window of length `L` costs `K e^{L/2} e^{−(L−τ)/2} E(τ)`
against the polar weight `φ = e^{−τ/2} + e^{−(L−τ)/2}`. Near the ends (`τ < L/4`) the weight pays,
`e^{−(L−τ)/2} ≤ e^{−L/4} e^{−τ/2}`; in the bulk (`τ ≥ L/4`) the profile pays, `E(τ) ≤ E(L/4)`
(`exp_neg_half_mul_profile_le`). The Schur constant is
`e^{L/2}(1 + 2K(E(L/4) + e^{−L/4})) + B + (1 + L)²` (`abs_nodeArchEnergy_sub_weilEnergy_le_profile`),
and with `E(y) = e^{−c y^ex}` the gain `e^{−c (L/4)^ex}` is at most `e^{−(c/4) L^ex}`. On the lower
side the polar test with cutoff `δ = e^{−L/2}` reads the integrated deficit, and
`e^{t − c t^ex} ≤ e · e^{T − c T^ex}` on `[0, T]` for `c ≤ 1` by the subadditivity
`T^ex ≤ (T − t)^ex + t^ex` of `x ↦ x^ex` (`exp_sub_mul_rpow_le_of_le`).

The polar weight loses only against power errors `x^γ` (the loss `1/4 + β/2` of the width law), so
the window remainder carries exactly the strength of the prime number theorem that enters. The gap
to RH is unchanged: RH is `c(L) ≤ e^{L/2} + O(L)` (`riemannHypothesis_of_windowCeiling_le`), and
`e^{L/2 − κ L^ex}` is `O(e^{θL})` for no `θ < 1/2`.
-/

open MeasureTheory Set Complex Finsupp Filter Topology
open RHTower RHTower.WeilOneSided
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The polar Schur bound for a nonincreasing error profile -/

/-- The Schur gain of an error profile `E` on a window of length `L`: `E(L/4) + e^{−L/4}`. -/
def profileSchurGain (E : ℝ → ℝ) (L : ℝ) : ℝ := E (L / 4) + Real.exp (-(L / 4))

/-- **The error at distance `s` pays the polar weight.** For a profile with `0 ≤ E ≤ 1`,
nonincreasing on `[0, ∞)`, and `s ≥ 0`:
`e^{−(L−s)/2} E(s) ≤ (E(L/4) + e^{−L/4}) (e^{−s/2} + e^{−(L−s)/2})`. In the bulk `s ≥ L/4` the
profile is at most `E(L/4)`; near the ends `s < L/4` the weight itself satisfies
`e^{−(L−s)/2} ≤ e^{−L/4} e^{−s/2}`. -/
theorem exp_neg_half_mul_profile_le {E : ℝ → ℝ} (hE0 : ∀ s, 0 ≤ s → 0 ≤ E s)
    (hE1 : ∀ s, 0 ≤ s → E s ≤ 1) (hanti : ∀ s t, 0 ≤ s → s ≤ t → E t ≤ E s)
    {L s : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s) :
    Real.exp (-(L - s) / 2) * E s ≤
      profileSchurGain E L * (Real.exp (-s / 2) + Real.exp (-(L - s) / 2)) := by
  unfold profileSchurGain
  have h1 : 0 < Real.exp (-s / 2) := Real.exp_pos _
  have h2 : 0 < Real.exp (-(L - s) / 2) := Real.exp_pos _
  have h3 : 0 ≤ E (L / 4) := hE0 _ (by positivity)
  have h4 : 0 < Real.exp (-(L / 4)) := Real.exp_pos _
  by_cases hbulk : L / 4 ≤ s
  · have herr : E s ≤ E (L / 4) := hanti _ _ (by positivity) hbulk
    calc Real.exp (-(L - s) / 2) * E s ≤ Real.exp (-(L - s) / 2) * E (L / 4) :=
          mul_le_mul_of_nonneg_left herr h2.le
      _ ≤ _ := by nlinarith [mul_nonneg h3 h1.le, mul_pos h4 h1, mul_pos h4 h2]
  · have hend : s < L / 4 := not_le.mp hbulk
    have hsplit : Real.exp (-(L - s) / 2) = Real.exp (-s / 2) * Real.exp (-(L - 2 * s) / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmid : Real.exp (-(L - 2 * s) / 2) ≤ Real.exp (-(L / 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-(L - s) / 2) * E s ≤ Real.exp (-(L - s) / 2) * 1 :=
          mul_le_mul_of_nonneg_left (hE1 s hs) h2.le
      _ = Real.exp (-s / 2) * Real.exp (-(L - 2 * s) / 2) := by rw [mul_one, hsplit]
      _ ≤ Real.exp (-s / 2) * Real.exp (-(L / 4)) := mul_le_mul_of_nonneg_left hmid h1.le
      _ ≤ _ := by nlinarith [mul_nonneg h3 h1.le, mul_nonneg h3 h2.le, mul_pos h4 h2]

/-- **The polar Schur bound for a nonincreasing error profile.** If
`ψ(e^y) ≤ e^y + K e^y E(y) + B` for `y ≥ 0`, with `0 ≤ E ≤ 1` nonincreasing on `[0, ∞)`, then on
windows of length `L`
`|A − W| ≤ (e^{L/2}(1 + 2K·gain) + B + (1 + L)²) ‖c‖²`, `gain = E(L/4) + e^{−L/4}`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_profile {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {L : ℝ} (hL : 0 ≤ L) (hsupp : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L))
    {K B : ℝ} (hK : 0 ≤ K) {E : ℝ → ℝ} (hE0 : ∀ s, 0 ≤ s → 0 ≤ E s)
    (hE1 : ∀ s, 0 ≤ s → E s ≤ 1) (hanti : ∀ s t, 0 ≤ s → s ≤ t → E t ≤ E s)
    (hψ : ∀ y : ℝ, 0 ≤ y →
      Chebyshev.psi (Real.exp y) ≤ Real.exp y + K * (Real.exp y * E y) + B) :
    |nodeArchEnergy c - weilEnergy c| ≤
      (Real.exp (L / 2) * (1 + 2 * K * profileSchurGain E L) + B + (1 + L) ^ 2) * massOf c := by
  set C := Real.exp (L / 2) * (1 + 2 * K * profileSchurGain E L) + B + (1 + L) ^ 2 with hCdef
  have hN : L ≤ Real.log ⌈Real.exp L⌉₊ :=
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log ⌈Real.exp L⌉₊ := Real.log_le_log (Real.exp_pos L) (Nat.le_ceil _)
  have hψe : ∀ y : ℝ, 0 ≤ y → y ≤ L → Chebyshev.psi (Real.exp y) ≤
      Real.exp y + K * (Real.exp y * E y) + B := fun y hy _ => hψ y hy
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
    have hp1 := exp_neg_half_mul_profile_le hE0 hE1 hanti hL hτ0
    have hp2 := exp_neg_half_mul_profile_le hE0 hE1 hanti hL (s := L - τ) (by linarith)
    rw [show L - (L - τ) = τ by ring] at hp2
    rw [hφ]
    have e1 : Real.exp (-τ / 2) * (Real.exp τ + K * (Real.exp τ * E τ) + B) =
        Real.exp (L / 2) * Real.exp (-(L - τ) / 2) +
          K * Real.exp (L / 2) * (Real.exp (-(L - τ) / 2) * E τ) + B * Real.exp (-τ / 2) := by
      linear_combination (1 + K * E τ) * hc1
    have e2 : Real.exp (-(L - τ) / 2) *
        (Real.exp (L - τ) + K * (Real.exp (L - τ) * E (L - τ)) + B) =
        Real.exp (L / 2) * Real.exp (-τ / 2) +
          K * Real.exp (L / 2) * (Real.exp (-τ / 2) * E (L - τ)) + B * Real.exp (-(L - τ) / 2) := by
      linear_combination (1 + K * E (L - τ)) * hc2
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

/-! ### 2. The Vinogradov–Korobov majorant in the logarithmic variable -/

/-- **The two-sided Vinogradov–Korobov majorant.** For `0 < ex < 3/5` there are `K ≥ 0`,
`0 < c ≤ 1`, `B ≥ 0` with `|ψ(e^y) − e^y| ≤ K e^y e^{−c y^ex} + B` for every `y ≥ 0`; `B` absorbs
the finitely many small `y` through Chebyshev's bound `ψ(x) ≤ (log 4 + 4) x`. -/
theorem exists_abs_psi_exp_sub_le_vk {ex : ℝ} (hex0 : 0 < ex) (hex : ex < 3 / 5) :
    ∃ K c B : ℝ, 0 ≤ K ∧ 0 < c ∧ c ≤ 1 ∧ 0 ≤ B ∧ ∀ y : ℝ, 0 ≤ y →
      |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
        K * (Real.exp y * Real.exp (-c * y ^ ex)) + B := by
  obtain ⟨c, hc, K, hK, hev⟩ := chebyshevError_bound_rpow hex0 hex
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hev
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmax : 0 < max X₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨K, min c 1, (Real.log 4 + 5) * max X₀ 1, hK, lt_min hc one_pos, min_le_right _ _,
    mul_nonneg (by linarith) hmax.le, fun y hy => ?_⟩
  have hx0 : 0 < Real.exp y := Real.exp_pos y
  have hterm : 0 ≤ K * (Real.exp y * Real.exp (-min c 1 * y ^ ex)) := by positivity
  have hB : 0 ≤ (Real.log 4 + 5) * max X₀ 1 := mul_nonneg (by linarith) hmax.le
  by_cases hge : X₀ ≤ Real.exp y
  · have hb := hX₀ (Real.exp y) hge
    rw [Real.log_exp] at hb
    simp only [chebyshevError] at hb
    -- a smaller rate constant gives a weaker bound
    have hmono : Real.exp (-c * y ^ ex) ≤ Real.exp (-min c 1 * y ^ ex) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.rpow_nonneg hy ex, min_le_left c 1]
    have : K * (Real.exp y * Real.exp (-c * y ^ ex)) ≤
        K * (Real.exp y * Real.exp (-min c 1 * y ^ ex)) := by gcongr
    linarith
  · have hlt : Real.exp y < X₀ := not_le.mp hge
    have h1 : Chebyshev.psi (Real.exp y) ≤ (Real.log 4 + 4) * Real.exp y :=
      Chebyshev.psi_le_const_mul_self hx0.le
    have h0 := Chebyshev.psi_nonneg (Real.exp y)
    have h2 : (Real.log 4 + 5) * Real.exp y ≤ (Real.log 4 + 5) * max X₀ 1 :=
      mul_le_mul_of_nonneg_left (hlt.le.trans (le_max_left _ _)) (by linarith)
    have h3 : Real.exp y ≤ (Real.log 4 + 5) * Real.exp y := by nlinarith
    rw [abs_le]; constructor <;> linarith

/-! ### 3. Eventual inequalities for the power-of-logarithm saving -/

/-- `κ L^ex ≤ L/8` for all large `L` when `ex < 1`. -/
theorem eventually_mul_rpow_le_div_eight {κ ex : ℝ} (hex : ex < 1) :
    ∀ᶠ L in atTop, κ * L ^ ex ≤ L / 8 := by
  have ht := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ex)).eventually
    (eventually_ge_atTop (8 * κ))
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with L h1 hL0
  have hmul : L ^ ex * L ^ (1 - ex) = L := by
    rw [← Real.rpow_add hL0, show ex + (1 - ex) = (1 : ℝ) by ring, Real.rpow_one]
  have hpow : 0 ≤ L ^ ex := Real.rpow_nonneg hL0.le ex
  calc κ * L ^ ex ≤ (L ^ (1 - ex) / 8) * L ^ ex :=
        mul_le_mul_of_nonneg_right (by linarith) hpow
    _ = (L ^ ex * L ^ (1 - ex)) / 8 := by ring
    _ = L / 8 := by rw [hmul]

/-- `B + (1 + L)² ≤ e^{L/2 − κ L^ex}` for all large `L` when `ex < 1`. -/
theorem eventually_add_sq_le_exp_half_sub_rpow {B κ ex : ℝ} (hex : ex < 1) :
    ∀ᶠ L in atTop, B + (1 + L) ^ 2 ≤ Real.exp (L / 2 - κ * L ^ ex) := by
  filter_upwards [eventually_mul_rpow_le_div_eight (κ := κ) hex,
    eventually_ge_atTop (8 * Real.log (|B| + 66)), eventually_ge_atTop (0 : ℝ)] with L hs h2 h0
  have hexp : Real.exp (3 * L / 8) ≤ Real.exp (L / 2 - κ * L ^ ex) :=
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

/-- `L^ex/4 ≤ (L/4)^ex` for `L ≥ 0` and `0 ≤ ex ≤ 1`. -/
theorem rpow_div_four_le {L ex : ℝ} (hL : 0 ≤ L) (hex1 : ex ≤ 1) :
    L ^ ex / 4 ≤ (L / 4) ^ ex := by
  rw [Real.div_rpow hL (by norm_num)]
  have h4 : (4 : ℝ) ^ ex ≤ 4 := Real.rpow_le_self_of_one_le (by norm_num) hex1
  have h4pos : 0 < (4 : ℝ) ^ ex := Real.rpow_pos_of_pos (by norm_num) ex
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hL ex) h4pos h4

/-- `L ≤ e^{κ L^ex}` for all large `L` (`κ > 0`, `ex > 0`), from `e^u ≥ u^N/N!` with `N ex ≥ 2`. -/
theorem eventually_le_exp_mul_rpow {κ ex : ℝ} (hκ : 0 < κ) (hex : 0 < ex) :
    ∀ᶠ L in atTop, L ≤ Real.exp (κ * L ^ ex) := by
  set N := ⌈2 / ex⌉₊ with hN
  set F : ℝ := (Nat.factorial N : ℝ) with hF
  have hF0 : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos N
  have hκN : 0 < κ ^ N := pow_pos hκ N
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (F / κ ^ N)] with L hL1 hLN
  have hL0 : 0 < L := by linarith
  have h := exp_neg_rpow_le_inv_sq hκ hex hL1
  rw [← hN, ← hF] at h
  have key : L * Real.exp (-κ * L ^ ex) ≤ 1 := by
    have h1 : L * Real.exp (-κ * L ^ ex) ≤ L * (F / (κ ^ N * L ^ 2)) :=
      mul_le_mul_of_nonneg_left h hL0.le
    have h2 : L * (F / (κ ^ N * L ^ 2)) = (F / κ ^ N) / L := by
      field_simp
    have h3 : (F / κ ^ N) / L ≤ 1 := by rw [div_le_one hL0]; exact hLN
    linarith
  calc L = L * Real.exp (-κ * L ^ ex) * Real.exp (κ * L ^ ex) := by
        rw [mul_assoc, ← Real.exp_add, show -κ * L ^ ex + κ * L ^ ex = 0 by ring, Real.exp_zero,
          mul_one]
    _ ≤ 1 * Real.exp (κ * L ^ ex) := mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := one_mul _

/-! ### 4. The window spectrum from above -/

/-- **The window spectrum with a Vinogradov–Korobov remainder.** For `0 < ex < 3/5` there are
`C ≥ 0`, `κ > 0` such that for all large `L` every window deviation `x` at length `L` satisfies
`|x| ≤ e^{L/2} + C e^{L/2 − κ L^ex}`. -/
theorem exists_eventually_abs_windowDeviations_le_exp_half_add_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L,
      |x| ≤ Real.exp (L / 2) + C * Real.exp (L / 2 - κ * L ^ ex) := by
  obtain ⟨K, c, B, hK, hc, -, -, hψ⟩ := exists_abs_psi_exp_sub_le_vk hex0 hex
  have hex1 : ex < 1 := by linarith
  -- the profile `E(y) = e^{−c y^ex}` and the one-sided majorant
  set E : ℝ → ℝ := fun y => Real.exp (-c * y ^ ex) with hEdef
  have hE0 : ∀ s, 0 ≤ s → 0 ≤ E s := fun s _ => (Real.exp_pos _).le
  have hE1 : ∀ s, 0 ≤ s → E s ≤ 1 := fun s hs => by
    simp only [hEdef]
    rw [Real.exp_le_one_iff]
    nlinarith [Real.rpow_nonneg hs ex]
  have hanti : ∀ s t, 0 ≤ s → s ≤ t → E t ≤ E s := fun s t hs hst => by
    simp only [hEdef]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.rpow_le_rpow hs hst hex0.le])
  have hψ1 : ∀ y : ℝ, 0 ≤ y →
      Chebyshev.psi (Real.exp y) ≤ Real.exp y + K * (Real.exp y * E y) + B := fun y hy => by
    have := hψ y hy
    simp only [hEdef]
    linarith [le_abs_self (Chebyshev.psi (Real.exp y) - Real.exp y)]
  refine ⟨4 * K + 1, c / 4, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_add_sq_le_exp_half_sub_rpow (B := B) (κ := c / 4) hex1,
    eventually_mul_rpow_le_div_eight (κ := c / 4) hex1, eventually_ge_atTop (0 : ℝ)]
    with L hpoly h8 h0 x hx
  obtain ⟨cf, hcf, hs, hm, rfl⟩ := hx
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_profile hcf h0 hs hK hE0 hE1 hanti hψ1
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  -- the two pieces of the Schur gain against `e^{L/2 − (c/4) L^ex}`
  have hE : Real.exp (L / 2) * E (L / 4) ≤ Real.exp (L / 2 - c / 4 * L ^ ex) := by
    simp only [hEdef]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [mul_le_mul_of_nonneg_left (rpow_div_four_le h0 hex1.le) hc.le]
  have hq : Real.exp (L / 2) * Real.exp (-(L / 4)) ≤ Real.exp (L / 2 - c / 4 * L ^ ex) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hgain : Real.exp (L / 2) * (2 * K * profileSchurGain E L) ≤
      4 * K * Real.exp (L / 2 - c / 4 * L ^ ex) := by
    have h1 : Real.exp (L / 2) * (2 * K * profileSchurGain E L) =
        2 * K * (Real.exp (L / 2) * E (L / 4)) +
          2 * K * (Real.exp (L / 2) * Real.exp (-(L / 4))) := by
      unfold profileSchurGain; ring
    rw [h1]
    have hK2 : (0 : ℝ) ≤ 2 * K := by positivity
    linarith [mul_le_mul_of_nonneg_left hE hK2, mul_le_mul_of_nonneg_left hq hK2]
  have hC : Real.exp (L / 2) * (1 + 2 * K * profileSchurGain E L) + B + (1 + L) ^ 2 ≤
      Real.exp (L / 2) + (4 * K + 1) * Real.exp (L / 2 - c / 4 * L ^ ex) := by
    linarith [hgain, hpoly]
  calc |nodeArchEnergy cf - weilEnergy cf| ≤ _ := h
    _ ≤ (Real.exp (L / 2) + (4 * K + 1) * Real.exp (L / 2 - c / 4 * L ^ ex)) * massOf cf :=
      mul_le_mul_of_nonneg_right hC hm.le

/-- **The ceiling.** `c(L) ≤ e^{L/2} + C e^{L/2 − κ L^ex}` for all large `L`. -/
theorem exists_eventually_windowCeiling_le_exp_half_add_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      windowCeiling L ≤ Real.exp (L / 2) + C * Real.exp (L / 2 - κ * L ^ ex) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowDeviations_le_exp_half_add_vk hex0 hex
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl] with L hL hne
  obtain ⟨x, hx, -⟩ := hne
  exact csSup_le ⟨x, hx⟩ fun y hy => (le_abs_self y).trans (hL y hy)

/-- **The floor.** `f(L) ≥ −e^{L/2} − C e^{L/2 − κ L^ex}` for all large `L`. -/
theorem exists_eventually_windowFloor_ge_neg_exp_half_sub_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      -(Real.exp (L / 2) + C * Real.exp (L / 2 - κ * L ^ ex)) ≤ windowFloor L := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowDeviations_le_exp_half_add_vk hex0 hex
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_exists_windowDeviation_ge (η := 1) one_pos le_rfl] with L hL hne
  obtain ⟨x, hx, -⟩ := hne
  exact le_csInf ⟨x, hx⟩ fun y hy => (neg_le_neg (hL y hy)).trans (neg_abs_le y)

/-- **The rate of `c(L)/e^{L/2} → 1`.** `c(L)/e^{L/2} − 1 ≤ C e^{−κ L^ex}` for all large `L`. -/
theorem exists_eventually_windowCeiling_div_exp_sub_one_le_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      windowCeiling L / Real.exp (L / 2) - 1 ≤ C * Real.exp (-(κ * L ^ ex)) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_windowCeiling_le_exp_half_add_vk hex0 hex
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev] with L hL
  have hE : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hsplit : Real.exp (L / 2 - κ * L ^ ex) =
      Real.exp (L / 2) * Real.exp (-(κ * L ^ ex)) := by
    rw [← Real.exp_add, sub_eq_add_neg]
  rw [sub_le_iff_le_add, div_le_iff₀ hE]
  rw [hsplit] at hL
  linarith

/-! ### 5. The lower side: the polar test attains the pole to Vinogradov–Korobov precision -/

/-- `e^{t − c t^ex} ≤ e · e^{T − c T^ex}` for `0 ≤ t ≤ T`, `0 ≤ c ≤ 1`, `0 ≤ ex ≤ 1`:
`T^ex ≤ (T − t)^ex + t^ex` by subadditivity of `x ↦ x^ex`, and `c (T − t)^ex ≤ (T − t) + 1`. -/
theorem exp_sub_mul_rpow_le_of_le {c ex t T : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hex0 : 0 ≤ ex)
    (hex1 : ex ≤ 1) (ht : 0 ≤ t) (htT : t ≤ T) :
    Real.exp t * Real.exp (-c * t ^ ex) ≤
      Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hTt : 0 ≤ T - t := sub_nonneg.mpr htT
  have hsub : T ^ ex ≤ (T - t) ^ ex + t ^ ex := by
    have := Real.rpow_add_le_add_rpow hTt ht hex0 hex1
    rwa [sub_add_cancel] at this
  have hu : (T - t) ^ ex ≤ (T - t) + 1 := by
    rcases le_or_gt 1 (T - t) with h1 | h1
    · linarith [Real.rpow_le_self_of_one_le h1 hex1]
    · linarith [Real.rpow_le_one hTt h1.le hex0]
  have hcu : c * (T - t) ^ ex ≤ (T - t) + 1 := by
    have h0 : 0 ≤ (T - t) ^ ex := Real.rpow_nonneg hTt ex
    nlinarith [mul_le_mul_of_nonneg_right hc1 h0]
  nlinarith [mul_le_mul_of_nonneg_left hsub hc0]

/-- **The integrated Chebyshev deficit to Vinogradov–Korobov precision.** With the two-sided
majorant `|ψ(e^y) − e^y| ≤ K e^y e^{−c y^ex} + B`, `0 ≤ c ≤ 1`, `0 ≤ ex ≤ 1`,
`|D(T)| ≤ T (K e · e^T e^{−c T^ex} + B)` for `T ≥ 0`, where `D(T) = ∫₀^T (e^t − ψ(e^t)) dt`. -/
theorem abs_ccmLogChebyshevDeficitPrimitive_le_vk {K c B ex : ℝ} (hK : 0 ≤ K) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hex0 : 0 ≤ ex) (hex1 : ex ≤ 1)
    (hψ : ∀ y : ℝ, 0 ≤ y → |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
      K * (Real.exp y * Real.exp (-c * y ^ ex)) + B) {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T| ≤
      T * (K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B) := by
  unfold ccmLogChebyshevDeficitPrimitive
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp t - Chebyshev.psi (Real.exp t)) volume 0 T :=
    (Real.continuous_exp.intervalIntegrable 0 T).sub
      ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)
  set M := K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B with hM
  calc |∫ t in (0 : ℝ)..T, Real.exp t - Chebyshev.psi (Real.exp t)|
      ≤ ∫ t in (0 : ℝ)..T, |Real.exp t - Chebyshev.psi (Real.exp t)| :=
        intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ _t in (0 : ℝ)..T, M := by
        refine intervalIntegral.integral_mono_on hT hi.abs intervalIntegrable_const
          fun t ht => ?_
        rw [abs_sub_comm]
        refine (hψ t ht.1).trans ?_
        have := mul_le_mul_of_nonneg_left
          (exp_sub_mul_rpow_le_of_le hc0 hc1 hex0 hex1 ht.1 ht.2) hK
        rw [hM]
        linarith
    _ = T * M := by rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- **The deficit against the polar cutoff.** For `L ≥ 4` with `L ≤ e^{(c/2) L^ex}`, `0 < c ≤ 1`,
`0 < ex ≤ 1`, the integrated deficit at `T = L − 2δ`, `δ = e^{−L/2}`, satisfies
`2δ |D(T)| ≤ 2 K e^{1 + c} e^{L/2 − (c/2) L^ex} + 2B`: `L^ex ≤ T^ex + 1`, `δ e^T ≤ e^{L/2}`,
`Lδ ≤ 1` and `L e^{−c L^ex} ≤ e^{−(c/2) L^ex}`. -/
theorem two_mul_exp_neg_half_mul_abs_deficit_le_vk {K c B ex : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hc1 : c ≤ 1) (hex0 : 0 < ex) (hex1 : ex ≤ 1) (hB : 0 ≤ B)
    (hψ : ∀ y : ℝ, 0 ≤ y → |Chebyshev.psi (Real.exp y) - Real.exp y| ≤
      K * (Real.exp y * Real.exp (-c * y ^ ex)) + B)
    {L : ℝ} (hL4 : 4 ≤ L) (hLexp : L ≤ Real.exp (c / 2 * L ^ ex)) :
    2 * Real.exp (-(L / 2)) *
        |ccmLogChebyshevDeficitPrimitive (L - 2 * Real.exp (-(L / 2)))| ≤
      2 * (K * Real.exp 1 * Real.exp c) * Real.exp (L / 2 - c / 2 * L ^ ex) + 2 * B := by
  have hL0 : 0 ≤ L := by linarith
  set E := Real.exp (L / 2) with hEdef
  have hEL : 0 < E := Real.exp_pos _
  set R := Real.exp (L / 2 - c / 2 * L ^ ex) with hRdef
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
  -- `2δ ≤ 1`, hence `L^ex ≤ T^ex + (2δ)^ex ≤ T^ex + 1` and `e^{−c T^ex} ≤ e^{c} e^{−c L^ex}`
  have h2δ : 2 * δ ≤ 1 := by
    have h1 : δ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h3 : Real.exp (-2) * Real.exp 2 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-2 : ℝ)).le]
  have hTex : L ^ ex ≤ T ^ ex + 1 := by
    have := Real.rpow_add_le_add_rpow hT (by positivity : (0 : ℝ) ≤ 2 * δ) hex0.le hex1
    rw [show T + 2 * δ = L by rw [hTdef]; ring] at this
    have h1 : (2 * δ) ^ ex ≤ 1 := Real.rpow_le_one (by positivity) h2δ hex0.le
    linarith
  have hexpT : Real.exp (-c * T ^ ex) ≤ Real.exp c * Real.exp (-c * L ^ ex) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hTex hc.le])
  -- `L e^{−c L^ex} ≤ e^{−(c/2) L^ex}`
  have hLsmall : L * Real.exp (-c * L ^ ex) ≤ Real.exp (-(c / 2 * L ^ ex)) := by
    have hsplit : Real.exp (-c * L ^ ex) =
        Real.exp (-(c / 2 * L ^ ex)) * Real.exp (-(c / 2 * L ^ ex)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hLe : L * Real.exp (-(c / 2 * L ^ ex)) ≤ 1 := by
      calc L * Real.exp (-(c / 2 * L ^ ex))
          ≤ Real.exp (c / 2 * L ^ ex) * Real.exp (-(c / 2 * L ^ ex)) :=
            mul_le_mul_of_nonneg_right hLexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [hsplit, ← mul_assoc]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hLe
  have hER : E * Real.exp (-(c / 2 * L ^ ex)) = R := by
    rw [hEdef, hRdef, ← Real.exp_add, sub_eq_add_neg]
  have hp2 : L * Real.exp (-c * T ^ ex) ≤ Real.exp c * Real.exp (-(c / 2 * L ^ ex)) :=
    calc L * Real.exp (-c * T ^ ex)
        ≤ L * (Real.exp c * Real.exp (-c * L ^ ex)) := mul_le_mul_of_nonneg_left hexpT hL0
      _ = Real.exp c * (L * Real.exp (-c * L ^ ex)) := by ring
      _ ≤ Real.exp c * Real.exp (-(c / 2 * L ^ ex)) :=
          mul_le_mul_of_nonneg_left hLsmall (Real.exp_pos _).le
  have hDabs := abs_ccmLogChebyshevDeficitPrimitive_le_vk hK hc.le hc1 hex0.le hex1 hψ hT
  have hq := mul_le_mul hδT hp2 (by positivity) hEL.le
  have h0 : 0 ≤ K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B := by positivity
  calc 2 * δ * |ccmLogChebyshevDeficitPrimitive T|
      ≤ 2 * δ * (T * (K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B)) :=
        mul_le_mul_of_nonneg_left hDabs (by positivity)
    _ ≤ 2 * δ * (L * (K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ h0) (by positivity)
        linarith
    _ = 2 * K * Real.exp 1 * ((δ * Real.exp T) * (L * Real.exp (-c * T ^ ex))) +
          2 * B * (L * δ) := by ring
    _ ≤ 2 * K * Real.exp 1 * (E * (Real.exp c * Real.exp (-(c / 2 * L ^ ex)))) + 2 * B * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hq (by positivity))
          (mul_le_mul_of_nonneg_left hLδ1 (by linarith))
    _ = 2 * (K * Real.exp 1 * Real.exp c) * (E * Real.exp (-(c / 2 * L ^ ex))) + 2 * B := by ring
    _ = 2 * (K * Real.exp 1 * Real.exp c) * R + 2 * B := by rw [hER]

/-- **The polar test attains the pole to Vinogradov–Korobov precision.** For `0 < ex < 3/5` there
are `C ≥ 0`, `κ > 0` such that for all large `L` some window deviation at length `L` is
`≥ e^{L/2} − C e^{L/2 − κ L^ex}`. -/
theorem exists_eventually_exists_windowDeviation_ge_exp_half_sub_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop, ∃ x ∈ windowDeviations L,
      Real.exp (L / 2) - C * Real.exp (L / 2 - κ * L ^ ex) ≤ x := by
  classical
  obtain ⟨K, c, B, hK, hc, hc1, hB, hψ⟩ := exists_abs_psi_exp_sub_le_vk hex0 hex
  have hex1 : ex ≤ 1 := by linarith
  set K' := K * Real.exp 1 * Real.exp c with hK'def
  have hK' : 0 ≤ K' := by positivity
  set C := K' + B + 4 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, c / 2, hC0, by positivity, ?_⟩
  filter_upwards [eventually_le_exp_mul_rpow (κ := c / 2) (by positivity) hex0,
    eventually_add_sq_le_exp_half_sub_rpow (B := 0) (κ := c / 2) (ex := ex) (by linarith),
    eventually_ge_atTop (4 : ℝ), eventually_ge_atTop C] with L hLexp hpoly hL4 hLC
  rw [zero_add] at hpoly
  have hL0 : 0 ≤ L := by linarith
  have hD := two_mul_exp_neg_half_mul_abs_deficit_le_vk hK hc hc1 hex0 hex1 hB hψ hL4 hLexp
  rw [← hK'def] at hD
  -- the polar test of the window `(0, L)` with cutoff `δ = e^{−L/2}`
  set E := Real.exp (L / 2) with hEdef
  have hEL : 0 < E := Real.exp_pos _
  set R := Real.exp (L / 2 - c / 2 * L ^ ex) with hRdef
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
    have habs := mul_le_mul_of_nonneg_left (le_abs_self (ccmLogChebyshevDeficitPrimitive T))
      (by positivity : (0 : ℝ) ≤ 2 * δ)
    linarith [hP', heT, hD, habs]
  -- `C R ≤ E`, since `C ≤ L ≤ e^{(c/2) L^ex}`
  have hER : E * Real.exp (-(c / 2 * L ^ ex)) = R := by
    rw [hEdef, hRdef, ← Real.exp_add, sub_eq_add_neg]
  have hECR : 0 ≤ E - C * R := by
    have h1' : C * Real.exp (-(c / 2 * L ^ ex)) ≤ 1 := by
      calc C * Real.exp (-(c / 2 * L ^ ex))
          ≤ Real.exp (c / 2 * L ^ ex) * Real.exp (-(c / 2 * L ^ ex)) :=
            mul_le_mul_of_nonneg_right (hLC.trans hLexp) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2' : C * R = E * (C * Real.exp (-(c / 2 * L ^ ex))) := by
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
  have hcon' := not_le.mp hcon
  rw [div_lt_iff₀ hm] at hcon'
  have hmass : (E - C * R) * massOf cf ≤ (E - C * R) * (2 + 2 * L * δ) :=
    mul_le_mul_of_nonneg_left hM hECR
  linarith [hcon', hmass, hnum, hpoly', hLEδ, hδ1,
    mul_nonneg (mul_nonneg hC0 hR0.le) (mul_nonneg hL0 hδ.le)]

/-- **The ceiling from below.** `c(L) ≥ e^{L/2} − C e^{L/2 − κ L^ex}` for all large `L`. -/
theorem exists_eventually_exp_half_sub_vk_le_windowCeiling {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      Real.exp (L / 2) - C * Real.exp (L / 2 - κ * L ^ ex) ≤ windowCeiling L := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_exists_windowDeviation_ge_exp_half_sub_vk hex0 hex
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  obtain ⟨x, hx, hxge⟩ := hL
  exact hxge.trans (le_csSup (bddAbove_windowDeviations hL0) hx)

/-! ### 6. The two-sided window spectrum and the deficit at Vinogradov–Korobov strength -/

/-- **The window ceiling is the pole to Vinogradov–Korobov precision:** for `0 < ex < 3/5`,
`|c(L) − e^{L/2}| ≤ C e^{L/2 − κ L^ex}` for all large `L`. -/
theorem exists_eventually_abs_windowCeiling_sub_exp_half_le_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      |windowCeiling L - Real.exp (L / 2)| ≤ C * Real.exp (L / 2 - κ * L ^ ex) := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, h₁⟩ := exists_eventually_windowCeiling_le_exp_half_add_vk hex0 hex
  obtain ⟨C₂, κ₂, hC₂, hκ₂, h₂⟩ := exists_eventually_exp_half_sub_vk_le_windowCeiling hex0 hex
  refine ⟨max C₁ C₂, min κ₁ κ₂, le_max_of_le_left hC₁, lt_min hκ₁ hκ₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop (0 : ℝ)] with L h1 h2 hL0
  have hp := Real.rpow_nonneg hL0 ex
  have e1 : Real.exp (L / 2 - κ₁ * L ^ ex) ≤ Real.exp (L / 2 - min κ₁ κ₂ * L ^ ex) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left κ₁ κ₂])
  have e2 : Real.exp (L / 2 - κ₂ * L ^ ex) ≤ Real.exp (L / 2 - min κ₁ κ₂ * L ^ ex) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right κ₁ κ₂])
  have m1 := mul_le_mul (le_max_left C₁ C₂) e1 (Real.exp_pos _).le (le_max_of_le_left hC₁)
  have m2 := mul_le_mul (le_max_right C₁ C₂) e2 (Real.exp_pos _).le (le_max_of_le_left hC₁)
  rw [abs_le]; constructor <;> linarith

/-- **The window floor is minus the pole to Vinogradov–Korobov precision:** for `0 < ex < 3/5`,
`|f(L) + e^{L/2}| ≤ C e^{L/2 − κ L^ex}` for all large `L`, by the Liouville mirror
`|c(L) + f(L)| ≤ 2T(N) = O(L)`. -/
theorem exists_eventually_abs_windowFloor_add_exp_half_le_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ L in atTop,
      |windowFloor L + Real.exp (L / 2)| ≤ C * Real.exp (L / 2 - κ * L ^ ex) := by
  obtain ⟨C, κ, hC, hκ, hev⟩ := exists_eventually_abs_windowCeiling_sub_exp_half_le_vk hex0 hex
  refine ⟨C + 28, κ, by positivity, hκ, ?_⟩
  filter_upwards [hev,
    eventually_add_sq_le_exp_half_sub_rpow (B := 0) (κ := κ) (ex := ex) (by linarith),
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
  have h28 : 4 * L + 28 ≤ 28 * Real.exp (L / 2 - κ * L ^ ex) := by linarith
  rw [abs_le]; constructor <;> linarith [hmir'.1, hmir'.2, hcl'.1, hcl'.2, hdef, hlogN, hlog4, h28]

/-- **The integrated Chebyshev deficit at Vinogradov–Korobov strength.** For `0 < ex < 3/5` there
are `C ≥ 0`, `κ > 0` with `|D(T)| ≤ C e^{T − κ T^ex}` for all large `T`, where
`D(T) = ∫₀^T (e^t − ψ(e^t)) dt`. -/
theorem exists_eventually_abs_ccmLogChebyshevDeficitPrimitive_le_vk {ex : ℝ} (hex0 : 0 < ex)
    (hex : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ᶠ T in atTop,
      |ccmLogChebyshevDeficitPrimitive T| ≤ C * Real.exp (T - κ * T ^ ex) := by
  obtain ⟨K, c, B, hK, hc, hc1, hB, hψ⟩ := exists_abs_psi_exp_sub_le_vk hex0 hex
  refine ⟨K * Real.exp 1 + B, c / 2, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_le_exp_mul_rpow (κ := c / 2) (by positivity) hex0,
    eventually_mul_rpow_le_div_eight (κ := c / 2) (ex := ex) (by linarith),
    eventually_ge_atTop (0 : ℝ)] with T hTexp h8 hT0
  have h := abs_ccmLogChebyshevDeficitPrimitive_le_vk hK hc.le hc1 hex0.le (by linarith) hψ hT0
  set R := Real.exp (T - c / 2 * T ^ ex) with hRdef
  -- `T e^{−c T^ex} ≤ e^{−(c/2) T^ex}` and `T ≤ e^{(c/2) T^ex} ≤ e^{T − (c/2) T^ex}`
  have hsplit : Real.exp (-c * T ^ ex) =
      Real.exp (-(c / 2 * T ^ ex)) * Real.exp (-(c / 2 * T ^ ex)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hTe : T * Real.exp (-(c / 2 * T ^ ex)) ≤ 1 := by
    calc T * Real.exp (-(c / 2 * T ^ ex))
        ≤ Real.exp (c / 2 * T ^ ex) * Real.exp (-(c / 2 * T ^ ex)) :=
          mul_le_mul_of_nonneg_right hTexp (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h1 : T * (Real.exp T * Real.exp (-c * T ^ ex)) ≤ R := by
    rw [hRdef, sub_eq_add_neg, Real.exp_add, hsplit]
    calc T * (Real.exp T * (Real.exp (-(c / 2 * T ^ ex)) * Real.exp (-(c / 2 * T ^ ex))))
        = Real.exp T * Real.exp (-(c / 2 * T ^ ex)) * (T * Real.exp (-(c / 2 * T ^ ex))) := by
          ring
      _ ≤ Real.exp T * Real.exp (-(c / 2 * T ^ ex)) * 1 :=
          mul_le_mul_of_nonneg_left hTe (by positivity)
      _ = _ := mul_one _
  have h2 : T ≤ R := by
    refine hTexp.trans (Real.exp_le_exp.mpr ?_)
    linarith
  calc |ccmLogChebyshevDeficitPrimitive T|
      ≤ T * (K * Real.exp 1 * (Real.exp T * Real.exp (-c * T ^ ex)) + B) := h
    _ = K * Real.exp 1 * (T * (Real.exp T * Real.exp (-c * T ^ ex))) + B * T := by ring
    _ ≤ K * Real.exp 1 * R + B * R :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 hB)
    _ = (K * Real.exp 1 + B) * R := by ring

end

end GaloisForLFunctions.BiScaleUncertainty
