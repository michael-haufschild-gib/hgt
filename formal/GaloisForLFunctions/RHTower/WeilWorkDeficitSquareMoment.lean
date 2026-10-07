import GaloisForLFunctions.RHTower.WeilWorkDeficitSquareWindow
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.WeilWorkDeficitRecovery
/-!
# Sublinear horizontal square displacement of the actual Xi divisor

Uniform admissible-window estimates, logarithmic endpoint counts, and a geometric prefix
argument give the linear-scale square-moment limit, with every multiplicity copy retained.
-/

open Complex Set Filter
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

private theorem copy_square_le_quarter (q : XiZeroCopy) :
    ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
  have h := xi_divisor_support_re_mem_open_unit q.1
  nlinarith [mul_nonneg h.1.le (le_of_lt (sub_pos.mpr h.2))]

private theorem card_unit_le (F : Finset XiZeroCopy) (t : ℝ)
    (hF : ∀ q ∈ F, |(q.1 : ℂ).im - t| ≤ 1) :
    (F.card : ℝ) ≤ 16 * (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) := by
  have hsub : F ⊆ (finite_xiOrdinateWindow 1 t).toFinset := by
    intro q hq
    rw [Set.Finite.mem_toFinset]
    exact hF q hq
  have hcard : (F.card : ℝ) ≤ (xiOrdinateWindow 1 t).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (finite_xiOrdinateWindow 1 t)]
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (ncard_xiOrdinateWindow_one_le_log t)

private theorem square_sum_le_inner_add_endpoints {U a b : ℝ} (hU : 16 ≤ U)
    (ha : a ∈ Ioo (U / 4) (U / 4 + 1)) (hb : b ∈ Ioo (U / 2 - 1) (U / 2))
    (F : Finset XiZeroCopy) (hF : ∀ q ∈ F, U / 4 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ U / 2) :
    ∑ q ∈ F, ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤
      (∑ q ∈ F.filter (fun q => a ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b),
        ((q.1 : ℂ).re - 1 / 2) ^ 2) +
      8 * (xiLineTwoLogDerivConstant + Real.log U) := by
  classical
  let A := F.filter (fun q => (q.1 : ℂ).im < a)
  let B := F.filter (fun q => b < (q.1 : ℂ).im)
  have hA : (A.card : ℝ) ≤ 16 * (xiLineTwoLogDerivConstant + Real.log U) := by
    have h := card_unit_le A (U / 4) (by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hh := hF q hq'.1
      exact abs_le.mpr ⟨by linarith, by linarith [ha.2]⟩)
    rw [abs_of_pos (by linarith : 0 < U / 4)] at h
    have hl : Real.log (U / 4 + 4) ≤ Real.log U :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hB : (B.card : ℝ) ≤ 16 * (xiLineTwoLogDerivConstant + Real.log U) := by
    have h := card_unit_le B (U / 2) (by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hh := hF q hq'.1
      exact abs_le.mpr ⟨by linarith [hb.1], by linarith⟩)
    rw [abs_of_pos (by linarith : 0 < U / 2)] at h
    have hl : Real.log (U / 2 + 4) ≤ Real.log U :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  have hpt (q : XiZeroCopy) : ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤
      (if a ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b then ((q.1 : ℂ).re - 1 / 2) ^ 2 else 0) +
      (1 / 4) * (if (q.1 : ℂ).im < a then (1 : ℝ) else 0) +
      (1 / 4) * (if b < (q.1 : ℂ).im then (1 : ℝ) else 0) := by
    have hh := copy_square_le_quarter q
    by_cases h1 : a ≤ (q.1 : ℂ).im
    · by_cases h2 : (q.1 : ℂ).im ≤ b
      · simp [h1, h2, not_lt.mpr h1, not_lt.mpr h2]
      · simp [h1, h2, not_lt.mpr h1, lt_of_not_ge h2]; simpa only [one_div] using hh
    · by_cases h2 : (q.1 : ℂ).im ≤ b
      · simp [h1, h2, lt_of_not_ge h1, not_lt.mpr h2]; simpa only [one_div] using hh
      · simp [h1, h2, lt_of_not_ge h1, lt_of_not_ge h2]; linarith
  have hs := Finset.sum_le_sum (s := F) (fun q _ => hpt q)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  change _ ≤ _ + (1 / 4) * (A.card : ℝ) + (1 / 4) * (B.card : ℝ) at hs
  linarith

private theorem exists_copy_band_card_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in atTop, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, U / 4 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ U / 2) →
      (F.card : ℝ) ≤ C * U * Real.log U := by
  obtain ⟨C, hC, T₀, hT₀, hc⟩ := exists_card_window_le
  refine ⟨1 / (8 * Real.pi) + 2 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * T₀), eventually_ge_atTop (4 : ℝ)] with U hUT hU
  intro F hF
  have h := hc (U / 4) (by linarith) (U / 4) (by linarith) F (by
    intro q hq
    have hh := hF q hq
    exact ⟨hh.1, by linarith [hh.2]⟩)
  have hlog : 0 ≤ Real.log (U / 4 + U / 4) := Real.log_nonneg (by linarith)
  have hlog' : Real.log (U / 4 + U / 4) ≤ Real.log U :=
    Real.log_le_log (by linarith) (by linarith)
  rw [← add_mul] at h
  have hcoef : U / 4 / (2 * Real.pi) + 2 * C ≤ (1 / (8 * Real.pi) + 2 * C) * U := by
    have heq : U / 4 / (2 * Real.pi) = 1 / (8 * Real.pi) * U := by ring
    rw [heq]
    nlinarith
  exact h.trans (mul_le_mul hcoef hlog' hlog (by positivity))

private theorem eventually_square_band_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ U : ℝ in atTop, ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, U / 4 < (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ U / 2) →
      ∑ q ∈ F, ((q.1 : ℂ).re - 1 / 2) ^ 2 ≤ ε * U := by
  classical
  obtain ⟨D, K, hD, hK, hwindow⟩ := exists_deficit_square_window_bound
  obtain ⟨C, hC, hcard⟩ := exists_copy_band_card_bound
  let c : ℝ := 2 + (D + 1) / ε
  have hc : 2 ≤ c := by
    dsimp [c]
    have : 0 ≤ (D + 1) / ε := div_nonneg (by linarith) hε.le
    linarith
  have hcpos : 0 < c := by linarith
  have hceq : ε * c = 2 * ε + D + 1 := by dsimp [c]; field_simp [hε.ne']; ring
  have hbase : D / (4 * c) < ε := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hnear : Tendsto (fun U : ℝ => C * c ^ 2 / Real.log U) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hlog : Tendsto (fun U : ℝ => Real.log U / U) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlog2 : Tendsto (fun U : ℝ => K * Real.log U ^ 2 / U) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero, mul_zero, mul_div_assoc] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul K
  have hconst : Tendsto (fun U : ℝ => xiLineTwoLogDerivConstant / U) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hend : Tendsto (fun U : ℝ => 8 * (xiLineTwoLogDerivConstant + Real.log U) / U)
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, zero_add, mul_zero] using (hconst.add hlog).const_mul 8
  let E : ℝ → ℝ := fun U => C * c ^ 2 / Real.log U + D / (4 * c) +
    K * Real.log U ^ 2 / U + 8 * (xiLineTwoLogDerivConstant + Real.log U) / U
  have hlim : Tendsto E atTop (𝓝 (D / (4 * c))) := by
    simpa only [zero_add, add_zero] using ((hnear.add tendsto_const_nhds).add hlog2).add hend
  filter_upwards [hwindow, hcard, hlim.eventually_lt_const hbase,
    eventually_ge_atTop (16 : ℝ)] with U hw hn hsmall hU
  intro F hF
  have hUpos : 0 < U := by linarith
  have hLpos : 0 < Real.log U := Real.log_pos (by linarith)
  obtain ⟨a, ha, b, hb, hwin⟩ := hw
  let G := F.filter (fun q => a ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ b)
  have hi := hwin c hc G (fun _ hq => (Finset.mem_filter.mp hq).2)
  have hGcard : (G.card : ℝ) ≤ C * U * Real.log U := by
    have hle : (G.card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ F)
    exact hle.trans (hn F hF)
  have hnearterm : (c / Real.log U) ^ 2 * G.card ≤ C * c ^ 2 / Real.log U * U := by
    calc
      (c / Real.log U) ^ 2 * G.card ≤ (c / Real.log U) ^ 2 * (C * U * Real.log U) :=
        mul_le_mul_of_nonneg_left hGcard (sq_nonneg _)
      _ = C * c ^ 2 / Real.log U * U := by field_simp [hLpos.ne']
  have htailterm : D / c * (b - a) ≤ D / (4 * c) * U := by
    calc
      D / c * (b - a) ≤ D / c * (U / 4) :=
        mul_le_mul_of_nonneg_left (by linarith [ha.1, hb.2]) (div_nonneg hD hcpos.le)
      _ = D / (4 * c) * U := by ring
  have he := square_sum_le_inner_add_endpoints hU ha hb F hF
  have hbound : (∑ q ∈ F, ((q.1 : ℂ).re - 1 / 2) ^ 2) ≤
      C * c ^ 2 / Real.log U * U + D / (4 * c) * U + K * Real.log U ^ 2 +
        8 * (xiLineTwoLogDerivConstant + Real.log U) := by
    change _ ≤ (∑ q ∈ G, _) + _ at he
    linarith
  have heq : C * c ^ 2 / Real.log U * U + D / (4 * c) * U + K * Real.log U ^ 2 +
      8 * (xiLineTwoLogDerivConstant + Real.log U) = E U * U := by
    dsimp [E]
    field_simp [hUpos.ne', hLpos.ne', hcpos.ne']
  rw [heq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right hsmall.le hUpos.le)


private theorem tendsto_prefix_div_of_dyadic_bound (Q : ℝ → ℝ) (hQ : ∀ T, 0 ≤ Q T) (hmono : Monotone Q)
    (hstep : ∀ ε > 0, ∀ᶠ T : ℝ in atTop, Q (2 * T) ≤ Q T + ε * T) :
    Tendsto (fun T => Q T / T) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact ha.trans_le (div_nonneg (hQ T) (by linarith))
  · intro ε hε
    obtain ⟨V₀, hV₀⟩ := eventually_atTop.mp (hstep (ε / 4) (by positivity))
    let V := max V₀ 1
    have hV1 : 1 ≤ V := le_max_right _ _
    have hV0 : V₀ ≤ V := le_max_left _ _
    have hVpos : 0 < V := by linarith
    have hpow (n : ℕ) : Q ((2 : ℝ) ^ n * V) ≤ Q V + (ε / 4) * ((2 : ℝ) ^ n * V) := by
      induction n with
      | zero => simp only [pow_zero, one_mul]; exact le_add_of_nonneg_right (by positivity)
      | succ n ih =>
        have hn : V₀ ≤ (2 : ℝ) ^ n * V := by
          have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
          nlinarith
        have hh := hV₀ _ hn
        rw [pow_succ]
        have heq : (2 : ℝ) ^ n * 2 * V = 2 * ((2 : ℝ) ^ n * V) := by ring
        rw [heq]
        nlinarith
    have hc : Tendsto (fun T : ℝ => Q V / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [eventually_ge_atTop V, hc.eventually_lt_const (show 0 < ε / 2 by positivity)] with T hT hcT
    have hTpos : 0 < T := hVpos.trans_le hT
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near
      (show 1 ≤ T / V by exact (le_div_iff₀ hVpos).mpr (by simpa using hT))
      (show (1 : ℝ) < 2 by norm_num)
    have hl : (2 : ℝ) ^ n * V ≤ T := (le_div_iff₀ hVpos).mp hlo
    have hu : T ≤ (2 : ℝ) ^ (n + 1) * V := ((div_lt_iff₀ hVpos).mp hhi).le
    have hp : (2 : ℝ) ^ (n + 1) * V ≤ 2 * T := by rw [pow_succ]; nlinarith
    have h := (hmono hu).trans (hpow (n + 1))
    have hbound : Q T ≤ Q V + ε / 2 * T := by nlinarith
    have hdiv := (div_le_div_of_nonneg_right hbound hTpos.le)
    have heq : (Q V + ε / 2 * T) / T = Q V / T + ε / 2 := by field_simp [hTpos.ne']
    rw [heq] at hdiv
    linarith

/-- Squared horizontal displacement, counting all actual positive-ordinate zero copies. -/
def deficitSquareCount (T : ℝ) : ℝ :=
  ∑ q ∈ (finite_deficitWindow T).toFinset, ((q.1 : ℂ).re - 1 / 2) ^ 2

/-- Horizontal displacement is negligible in square mean on the linear height scale. -/
theorem tendsto_deficitSquareCount_div :
    Tendsto (fun T : ℝ => deficitSquareCount T / T) atTop (𝓝 0) := by
  classical
  apply tendsto_prefix_div_of_dyadic_bound deficitSquareCount
  · intro T
    exact Finset.sum_nonneg (fun q _ => sq_nonneg _)
  · intro T U hTU
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact ⟨hq.1, hq.2.trans hTU⟩
    · intro q _ _
      exact sq_nonneg _
  · intro ε hε
    obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp (eventually_square_band_small (ε / 4) (by positivity))
    filter_upwards [eventually_ge_atTop (max U₀ 1)] with T hT
    have hT1 : 1 ≤ T := (le_max_right U₀ 1).trans hT
    have hTU : U₀ ≤ T := (le_max_left U₀ 1).trans hT
    let F := (finite_deficitWindow (2 * T)).toFinset
    let G := F.filter (fun q => (q.1 : ℂ).im ≤ T)
    let H := F.filter (fun q => ¬ (q.1 : ℂ).im ≤ T)
    have hG : G = (finite_deficitWindow T).toFinset := by
      ext q
      simp only [G, F, Finset.mem_filter, Set.Finite.mem_toFinset, deficitWindow, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hpos, _⟩, hle⟩
        exact ⟨hpos, hle⟩
      · rintro ⟨hpos, hle⟩
        exact ⟨⟨hpos, by linarith⟩, hle⟩
    have hsum : deficitSquareCount (2 * T) = deficitSquareCount T +
        ∑ q ∈ H, ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
      calc
        deficitSquareCount (2 * T) = (∑ q ∈ G, ((q.1 : ℂ).re - 1 / 2) ^ 2) +
            ∑ q ∈ H, ((q.1 : ℂ).re - 1 / 2) ^ 2 :=
          (Finset.sum_filter_add_sum_filter_not F (fun q => (q.1 : ℂ).im ≤ T)
            (fun q => ((q.1 : ℂ).re - 1 / 2) ^ 2)).symm
        _ = _ := by rw [hG]; rfl
    have hb := hU₀ (4 * T) (by linarith) H (by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqin, hnot⟩
      have hwin : q ∈ deficitWindow (2 * T) := by
        simpa only [F, Set.Finite.mem_toFinset] using hqin
      exact ⟨by linarith [lt_of_not_ge hnot], by linarith [hwin.2]⟩)
    rw [hsum]
    linarith

end RHTower.WeilSpectral

end
