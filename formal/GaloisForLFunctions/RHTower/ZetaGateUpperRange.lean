import GaloisForLFunctions.RHTower.ZetaGateFromDyadicMeanSquare
import GaloisForLFunctions.RHTower.ZetaTwoThirdsOffLineMomentConstant
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.HighBlockAsymptotics

/-!
# The mean-square gate on the upper range `[U^α, U]`

`ZetaMollifiedMeanSquareGate` asks for one mollifier whose mean square on the Levinson line is
controlled on a window `[T₁, T₂]` with `T₁ ≈ 20`, so the blocks far below `U` enter with a mollifier
that is long for them.  The zeros below `U^α`, `α < 1`, are `O(U^α log U) = o(U)` in number and
carry off-line moment at most half their count, so the window may start at `U^α` instead:

* `ZetaUpperDyadicMeanSquareLaw α R c` is the dyadic law on the blocks above `U^α` only;
* it yields `ZetaMollifiedMeanSquareGateFrom α R c`, the gate with `T₁ ∈ [20, U^α + 1]`
  (`zetaMollifiedMeanSquareGateFrom_of_upperLaw`);
* with the unconditional two-thirds proportion of simple critical zeros this gives
  `4π Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c − (5/3)R + η)V` eventually
  (`eventually_offLineMoment_le_of_zetaGateFrom_twoThirds`).

The proportion enters cumulatively: `N₀(T₂) − N₀(T₁) ≥ (2/3 − ε)N(T₂) − N(T₁)`, and `N(T₁) = o(U)`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The window conditions on `U^α` hold for all large `U`. -/
theorem eventually_upper_window {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᶠ U : ℝ in atTop, 20 ≤ U ^ α ∧ U ^ α + 1 < U - 1 ∧ U ^ α + 1 ≤ U / 4 := by
  have h1 : ∀ᶠ U : ℝ in atTop, 20 ≤ U ^ α :=
    (tendsto_rpow_atTop hα0).eventually (eventually_ge_atTop 20)
  have h2 := eventually_const_mul_rpow_neg_le 8 (1 - α) (by linarith) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [h1, h2, eventually_ge_atTop (8 : ℝ)] with U hU1 hU2 hU8
  have hU0 : 0 < U := by linarith
  have hsplit : U ^ α = U ^ (-(1 - α)) * U := by
    rw [← Real.rpow_add_one hU0.ne', show -(1 - α) + 1 = α by ring]
  have hle : U ^ α ≤ U / 8 := by
    rw [hsplit]
    have : U ^ (-(1 - α)) ≤ 1 / 8 := by linarith
    calc U ^ (-(1 - α)) * U ≤ 1 / 8 * U := mul_le_mul_of_nonneg_right this hU0.le
      _ = U / 8 := by ring
  refine ⟨hU1, by linarith, by linarith⟩

/-- **The mollified mean-square gate on the upper range.**  As `ZetaMollifiedMeanSquareGate`, with
the window starting at a height `T₁ ∈ [20, U^α + 1]`. -/
def ZetaMollifiedMeanSquareGateFrom (α R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (T₁ T₂ σ₀ Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    T₁ ∈ Set.Icc (20 : ℝ) (U ^ α + 1) ∧ T₂ ∈ Set.Ioc (U - 1) U ∧
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log T₂ ∧
    1 / 4 ≤ σ₀ ∧ σ₀ < 1 / 2 ∧ (1 / 2 - σ₀) * Real.log T₂ = R ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
    (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
    (∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ (c + ε) * (T₂ - T₁)

/-- **The upper dyadic mean-square law** for `ζΨ`: the dyadic law of `ZetaDyadicMeanSquareLaw`
required only on the blocks above `U^α`. -/
def ZetaUpperDyadicMeanSquareLaw (α R c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop, ∃ (Mb : ℝ) (b : ℕ → ℂ) (N : ℕ),
    1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧
    (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) ∧
    1 ≤ Mb ∧ (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb ∧
    Real.log Mb ≤ 5 * Real.log (U - 1) ∧
    ∀ σ₀ : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 →
      R ≤ (1 / 2 - σ₀) * Real.log U → (1 / 2 - σ₀) * Real.log (U - 1) ≤ R →
      ∀ a v : ℝ, 20 ≤ a → U ^ α ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
        (∫ t in a..v,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ))
          ≤ (c + ε) * (v - a) + ε * (a + U / Real.log U)

/-- **The gate from the upper dyadic law.**  The window starts at a height `T₁ ∈ (U^α, U^α + 1)`
with zero-free horizontal edges, so only the blocks above `U^α` are summed. -/
theorem zetaMollifiedMeanSquareGateFrom_of_upperLaw {α R c : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hR : 0 < R) (hlaw : ZetaUpperDyadicMeanSquareLaw α R c) :
    ZetaMollifiedMeanSquareGateFrom α R c := by
  classical
  intro ε hε
  have hε' : 0 < ε / 13 := by positivity
  filter_upwards [hlaw (ε / 13) hε', eventually_ge_atTop (max 100 (Real.exp (4 * R) + 1)),
    eventually_upper_window hα0 hα1]
    with U hU hUbig hUα
  obtain ⟨Mb, b, N, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb, hdy⟩ := hU
  have hU100 : (100 : ℝ) ≤ U := le_trans (le_max_left _ _) hUbig
  have hUexp : Real.exp (4 * R) + 1 ≤ U := le_trans (le_max_right _ _) hUbig
  have hU0 : (0 : ℝ) < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos (by linarith)
  have hlogU1 : 1 ≤ Real.log U := by
    have he : Real.exp 1 ≤ U := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at this
  set lam : ℝ := 0 with hlam
  have hlamC : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by simp [hlam]
  have hG0 : ∀ z : ℂ, levinsonG ((lam : ℝ) : ℂ) z = riemannZeta z := by
    intro z
    simp [levinsonG, hlam]
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1mem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  set Ψ : ℂ → ℂ := edPoly b (Finset.Icc 1 N) with hΨdef
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  set F : ℂ → ℂ := fun z => levinsonGEntire ((lam : ℝ) : ℂ) z * Ψ z with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz =>
    ((analyticOnNhd_levinsonGEntire _) z hz).mul (hΨan z hz)
  have hΨright : Ψ (((15 / 2 : ℝ) : ℂ)) ≠ 0 := by
    intro h0
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ)) (by simp; norm_num)
    rw [← hΨdef, h0] at h
    norm_num at h
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ), mul_ne_zero
      (levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)) hΨright⟩
  -- zero-free horizontal edges
  obtain ⟨T₁, hT₁, T₂, hT₂, hF1, hF2⟩ :=
    exists_horizontal_slices_avoiding_entire_zeros hFan hFne (c := (1 / 4 : ℝ)) (d := 15 / 2)
      (by norm_num) (by linarith : U ^ α < U ^ α + 1) (by linarith [hUα.2.1] : U ^ α + 1 < U - 1)
      (by linarith : U - 1 < U)
  have hT₁20 : 20 < T₁ := lt_of_le_of_lt hUα.1 hT₁.1
  have hT₁α : U ^ α < T₁ := hT₁.1
  have hT₁21 : T₁ < U ^ α + 1 := hT₁.2
  have hT₂U : T₂ < U := hT₂.2
  have hT₂lo : U - 1 < T₂ := hT₂.1
  have hT12 : T₁ < T₂ := by linarith [hUα.2.1]
  have hT₂pos : 0 < T₂ := by linarith
  have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
  have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log hT₂pos hT₂U.le
  have hlogU1T₂ : Real.log (U - 1) ≤ Real.log T₂ := Real.log_le_log (by linarith) hT₂lo.le
  have hlogT₂4R : 4 * R ≤ Real.log T₂ := by
    have := Real.log_le_log (Real.exp_pos (4 * R)) (by linarith : Real.exp (4 * R) ≤ T₂)
    rwa [Real.log_exp] at this
  -- the abscissa
  set σ₀ : ℝ := 1 / 2 - R / Real.log T₂ with hσ₀
  have hσ₀R : (1 / 2 - σ₀) * Real.log T₂ = R := by
    rw [hσ₀]
    field_simp
    try ring
  have hσ₀a : 1 / 4 ≤ σ₀ := by
    rw [hσ₀]
    have : R / Real.log T₂ ≤ 1 / 4 := by
      rw [div_le_iff₀ hlogT₂]
      linarith
    linarith
  have hσ₀b : σ₀ < 1 / 2 := by
    rw [hσ₀]
    have : 0 < R / Real.log T₂ := by positivity
    linarith
  have hσ₀lawU : R ≤ (1 / 2 - σ₀) * Real.log U := by
    have hw : 1 / 2 - σ₀ = R / Real.log T₂ := by rw [hσ₀]; ring
    rw [hw, div_mul_eq_mul_div, le_div_iff₀ hlogT₂]
    nlinarith [hlogT₂U, hR]
  have hσ₀lawU1 : (1 / 2 - σ₀) * Real.log (U - 1) ≤ R := by
    have hw : 1 / 2 - σ₀ = R / Real.log T₂ := by rw [hσ₀]; ring
    rw [hw, div_mul_eq_mul_div, div_le_iff₀ hlogT₂]
    nlinarith [hlogU1T₂, hR]
  -- edge nonvanishing from `F`
  have hedge : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2), F ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
        riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) ∧
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), Ψ ((x : ℂ) + (T : ℂ) * I) ≠ 0) := by
    intro T hT hF
    have hmem : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), x ∈ Set.uIcc (1 / 4 : ℝ) (15 / 2) := by
      intro x hx
      rw [uIcc_of_le (by norm_num)]
      exact ⟨le_trans hσ₀a hx.1, hx.2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · intro h0
      apply hF x (hmem x hx)
      have hne1 : ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
        intro h
        have := congrArg Complex.im h
        simp at this
        linarith
      simp only [hFdef]
      rw [levinsonGEntire_eq _ hne1, hG0, h0]
      ring
    · intro h0
      apply hF x (hmem x hx)
      simp only [hFdef]
      rw [h0, mul_zero]
  obtain ⟨hG1, hP1⟩ := hedge T₁ hT₁20.le hF1
  obtain ⟨hG2, hP2⟩ := hedge T₂ (by linarith) hF2
  -- the mean square via dyadic blocks
  set f : ℝ → ℝ := fun t =>
    ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ) with hfdef
  have hcont : ∀ t : ℝ, 20 ≤ t → ContinuousAt f t := by
    intro t ht
    have hz : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hA := ((analyticAt_riemannZeta_of_ne_one hz).mul
      ((analyticOnNhd_edPoly b hs) _ (Set.mem_univ _))).continuousAt
    have hmap : ContinuousAt (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact (ContinuousAt.comp (f := fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I) hA hmap).norm.pow 2
  have hint : ∀ a v : ℝ, 20 ≤ a → a ≤ v → IntervalIntegrable f volume a v := by
    intro a v ha hav
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hav] at ht
    exact (hcont t (le_trans ha ht.1)).continuousWithinAt
  have hblock : ∀ a v : ℝ, 20 ≤ a → U ^ α ≤ a → a ≤ v → v ≤ 2 * a → v ≤ U →
      (∫ t in a..v, f t) ≤ (c + ε / 13) * (v - a) + ε / 13 * (a + U / Real.log U) :=
    fun a v ha haα hav hv2 hvU => hdy σ₀ hσ₀a hσ₀b hσ₀lawU hσ₀lawU1 a v ha haα hav hv2 hvU
  -- dyadic scale
  set A : ℕ → ℝ := fun k => T₁ * (2 : ℝ) ^ k with hAdef
  have hA0 : A 0 = T₁ := by simp [hAdef]
  have hAsucc : ∀ k, A (k + 1) = 2 * A k := by intro k; simp [hAdef]; ring
  have hApos : ∀ k, 20 ≤ A k := by
    intro k
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h2 : T₁ ≤ T₁ * 2 ^ k := le_mul_of_one_le_right (by linarith) h1
    simp only [hAdef]
    linarith
  have hAα : ∀ k, U ^ α ≤ A k := by
    intro k
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h2 : T₁ ≤ T₁ * 2 ^ k := le_mul_of_one_le_right (by linarith) h1
    simp only [hAdef]
    linarith
  have hAmono : ∀ k, A k ≤ A (k + 1) := by
    intro k; rw [hAsucc]; linarith [hApos k]
  have hexK : ∃ k : ℕ, T₂ < A (k + 1) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T₂ / T₁) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [hAsucc]
    have h1 : T₂ < T₁ * 2 ^ n := by
      rw [div_lt_iff₀ (by linarith)] at hn
      linarith
    have h2 : A n = T₁ * 2 ^ n := rfl
    linarith [hApos n]
  set K : ℕ := Nat.find hexK with hKdef
  have hKspec : T₂ < A (K + 1) := Nat.find_spec hexK
  have hKle : A K ≤ T₂ := by
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · rw [h0, hA0]; exact hT12.le
    · obtain ⟨K', hK'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
      have hmin : ¬ (T₂ < A (K' + 1)) := Nat.find_min hexK (by omega)
      rw [hK']
      exact le_of_not_gt hmin
  -- K is at most 2 log U
  have hKlog : (K : ℝ) ≤ 2 * Real.log U := by
    have h2K : T₁ * (2 : ℝ) ^ K ≤ U := le_trans hKle hT₂U.le
    have hpow : (2 : ℝ) ^ K ≤ U := by
      have : (2 : ℝ) ^ K ≤ T₁ * 2 ^ K :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      linarith
    have hlogpow : (K : ℝ) * Real.log 2 ≤ Real.log U := by
      have := Real.log_le_log (by positivity) hpow
      rwa [Real.log_pow] at this
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have := mul_le_mul_of_nonneg_left hlog2 hK0
    linarith
  -- split the integral
  have hsplit : (∫ t in T₁..T₂, f t)
      = (∑ k ∈ Finset.range K, ∫ t in A k..A (k + 1), f t) + ∫ t in A K..T₂, f t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hint _ _ (hApos k) (hAmono k))]
    rw [hA0]
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _ (by linarith) (by
      have : T₁ = A 0 := hA0.symm
      rw [this]
      exact monotone_nat_of_le_succ hAmono (Nat.zero_le K))) (hint _ _ (hApos K) hKle)]
  have hterm : ∀ k ∈ Finset.range K,
      (∫ t in A k..A (k + 1), f t)
        ≤ (c + ε / 13) * (A (k + 1) - A k) + ε / 13 * (A k + U / Real.log U) := by
    intro k hk
    have hkK : k < K := Finset.mem_range.mp hk
    refine hblock (A k) (A (k + 1)) (hApos k) (hAα k) (hAmono k) (by rw [hAsucc]) ?_
    have : A (k + 1) ≤ A K := monotone_nat_of_le_succ hAmono (by omega)
    linarith
  have hlast : (∫ t in A K..T₂, f t)
      ≤ (c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U) := by
    refine hblock (A K) T₂ (hApos K) (hAα K) hKle ?_ hT₂U.le
    rw [hAsucc] at hKspec
    exact hKspec.le
  have hsumA : ∑ k ∈ Finset.range K, A k = T₁ * ((2 : ℝ) ^ K - 1) := by
    simp only [hAdef]
    rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    ring
  have htele : ∑ k ∈ Finset.range K, (A (k + 1) - A k) = A K - A 0 :=
    Finset.sum_range_sub (fun k => A k) K
  have hsum_le := Finset.sum_le_sum hterm
  have hRHS : (∑ k ∈ Finset.range K,
      ((c + ε / 13) * (A (k + 1) - A k) + ε / 13 * (A k + U / Real.log U)))
      = (c + ε / 13) * (A K - A 0)
        + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htele, ← Finset.mul_sum,
      Finset.sum_add_distrib, hsumA, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hRHS] at hsum_le
  -- assemble the numeric bound
  have hAK : A K = T₁ * 2 ^ K := rfl
  have hAKle : T₁ * (2 : ℝ) ^ K ≤ T₂ := hKle
  have hUlog : U / Real.log U ≤ U := by
    rw [div_le_iff₀ hlogU]
    exact le_mul_of_one_le_right hU0.le hlogU1
  have hK1 : (K : ℝ) + 1 ≤ 3 * Real.log U := by linarith
  have hslack : ε / 13 * ((T₁ * ((2 : ℝ) ^ K - 1) + A K) + ((K : ℝ) + 1) * (U / Real.log U))
      ≤ ε / 13 * (5 * U) := by
    apply mul_le_mul_of_nonneg_left _ hε'.le
    have h1 : T₁ * ((2 : ℝ) ^ K - 1) + A K ≤ 2 * U := by
      rw [hAK]
      have hexp : T₁ * ((2 : ℝ) ^ K - 1) + T₁ * 2 ^ K = 2 * (T₁ * 2 ^ K) - T₁ := by ring
      rw [hexp]
      linarith
    have h2 : ((K : ℝ) + 1) * (U / Real.log U) ≤ 3 * U := by
      calc ((K : ℝ) + 1) * (U / Real.log U) ≤ (3 * Real.log U) * (U / Real.log U) :=
            mul_le_mul_of_nonneg_right hK1 (by positivity)
        _ = 3 * U := by field_simp
    linarith
  have hU2 : U ≤ 2 * (T₂ - T₁) := by linarith [hUα.2.2]
  refine ⟨T₁, T₂, σ₀, Mb, b, N, ⟨hT₁20.le, hT₁21.le⟩, ⟨hT₂lo, hT₂U.le⟩, hN, hb1, hbn, hbreal,
    hMb1, hmass, ?_, hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, ?_⟩
  · calc Real.log Mb ≤ 5 * Real.log (U - 1) := hlogMb
      _ ≤ 5 * Real.log T₂ := by linarith
  · show (∫ t in T₁..T₂, f t) ≤ (c + ε) * (T₂ - T₁)
    rw [hsplit]
    have hεU : ε / 13 * (5 * U) ≤ 10 * (ε / 13) * (T₂ - T₁) := by
      have := mul_le_mul_of_nonneg_left hU2 hε'.le
      linarith
    have hεT : 0 ≤ ε * (T₂ - T₁) := mul_nonneg hε.le (by linarith)
    have hfin : (c + ε / 13) * (A K - A 0)
        + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U))
        + ((c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U))
        ≤ (c + ε) * (T₂ - T₁) := by
      have hexp : (c + ε / 13) * (A K - A 0)
          + ε / 13 * (T₁ * ((2 : ℝ) ^ K - 1) + (K : ℝ) * (U / Real.log U))
          + ((c + ε / 13) * (T₂ - A K) + ε / 13 * (A K + U / Real.log U))
          = (c + ε / 13) * (T₂ - A 0)
            + ε / 13 * ((T₁ * ((2 : ℝ) ^ K - 1) + A K) + ((K : ℝ) + 1) * (U / Real.log U)) := by
        ring
      rw [hexp, hA0]
      linarith only [hslack, hεU, hεT]
    linarith only [hsum_le, hlast, hfin]


/-- Every zero right of the line has `Re ρ − ½ < ½`: `Σ m_ρ (Re ρ − ½)⁺ ≤ N(T)/2`. -/
theorem offLineMoment_le_half_xiPosZeroCount (T : ℝ) :
    offLineMoment T ≤ 1 / 2 * (xiPosZeroCount T : ℝ) := by
  classical
  unfold offLineMoment xiPosZeroCount
  have hsub : boxFinsetLe T ⊆ stripFinsetPos T := by
    intro z hz
    rw [mem_boxFinsetLe] at hz
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    rw [mem_stripFinsetPos]
    refine ⟨by linarith, h2, ?_, h4, h5⟩
    rcases lt_or_eq_of_le h3 with h | h
    · exact h
    · exfalso
      have hz : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [← h]
      rw [hz] at h5
      exact xi_ne_zero_of_real z.re h5
  push_cast
  rw [Finset.mul_sum]
  calc ∑ z ∈ boxFinsetLe T, ((analyticOrderAt xi z).toNat : ℝ) * (z.re - 1 / 2)
      ≤ ∑ z ∈ boxFinsetLe T, 1 / 2 * ((analyticOrderAt xi z).toNat : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        rw [mem_boxFinsetLe] at hz
        obtain ⟨h1, h2, -, -, -⟩ := hz
        have h0 : (0 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ ≤ ∑ z ∈ stripFinsetPos T, 1 / 2 * ((analyticOrderAt xi z).toNat : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => by positivity

/-- `K · N(U^α + 1) ≤ δ (U − 1)` for all large `U`, `α < 1`. -/
theorem eventually_count_upper_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (K : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ U : ℝ in atTop, K * (xiPosZeroCount (U ^ α + 1) : ℝ) ≤ δ * (U - 1) ∧
      (20 ≤ U ^ α ∧ U ^ α + 1 < U - 1 ∧ U ^ α + 1 ≤ U / 4) := by
  obtain ⟨T₀, hT₀4, hrvm⟩ := exists_xiZeroCount_close 1 one_pos
  set K' : ℝ := |K| * (1 / (2 * Real.pi) + 1) * 8 with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hsmall := eventually_const_mul_rpow_neg_mul_log_pow_le K' (1 - α) (by linarith) 1
    (show 0 < δ / 2 by positivity)
  have hbig : ∀ᶠ U : ℝ in atTop, T₀ ≤ U ^ α :=
    (tendsto_rpow_atTop hα0).eventually (eventually_ge_atTop T₀)
  filter_upwards [hsmall, hbig, eventually_upper_window hα0 hα1, eventually_ge_atTop (4 : ℝ)]
    with U hU hUT₀ hwin hU4
  refine ⟨?_, hwin⟩
  have hU0 : 0 < U := by linarith
  have hUα0 : 0 < U ^ α := Real.rpow_pos_of_pos hU0 α
  set X : ℝ := U ^ α + 1 with hX
  have hX0 : 0 ≤ X := by positivity
  have hX1 : 1 ≤ X := by linarith
  have hXT₀ : T₀ ≤ X := by linarith
  have hcount : (xiPosZeroCount X : ℝ) ≤ (1 / (2 * Real.pi) + 1) * (X * Real.log X) := by
    have h := hrvm X hXT₀
    have hcast : ((xiZeroCount X : ℤ) : ℝ) = (xiPosZeroCount X : ℝ) := by
      rw [← xiPosZeroCount_eq_xiZeroCount hX0]
      simp
    rw [hcast] at h
    have := (abs_le.mp h).2
    linarith
  have hXU : X ≤ 2 * U ^ α := by
    have : (1 : ℝ) ≤ U ^ α := by linarith [hwin.1]
    linarith
  have hlogX : Real.log X ≤ 2 * Real.log U := by
    have h1 : X ≤ U * U := by nlinarith [hwin.2.2]
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul hU0.ne' hU0.ne'] at h2
    linarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hlogU0 : 0 ≤ Real.log U := Real.log_nonneg (by linarith)
  have hprod : X * Real.log X ≤ 4 * (U ^ α * Real.log U) := by
    calc X * Real.log X ≤ (2 * U ^ α) * (2 * Real.log U) :=
          mul_le_mul hXU hlogX hlogX0 (by positivity)
      _ = 4 * (U ^ α * Real.log U) := by ring
  have hsplit : U ^ α * Real.log U = (U ^ (-(1 - α)) * Real.log U ^ 1) * U := by
    rw [pow_one, show U ^ (-(1 - α)) * Real.log U * U = Real.log U * (U ^ (-(1 - α)) * U) by ring,
      ← Real.rpow_add_one hU0.ne', show -(1 - α) + 1 = α by ring]
    ring
  have hK : K * (xiPosZeroCount X : ℝ) ≤ |K| * (xiPosZeroCount X : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (Nat.cast_nonneg _)
  calc K * (xiPosZeroCount X : ℝ) ≤ |K| * (xiPosZeroCount X : ℝ) := hK
    _ ≤ |K| * ((1 / (2 * Real.pi) + 1) * (4 * (U ^ α * Real.log U))) :=
        mul_le_mul_of_nonneg_left (hcount.trans
          (mul_le_mul_of_nonneg_left hprod (by positivity))) (abs_nonneg K)
    _ = K' / 2 * (U ^ (-(1 - α)) * Real.log U ^ 1) * U := by
        rw [hsplit, hK']; ring
    _ ≤ δ / 2 / 2 * U := by
        have := mul_le_mul_of_nonneg_right hU hU0.le
        nlinarith
    _ ≤ δ * (U - 1) := by nlinarith

/-- **The `(L)` ceiling from the upper-range gate and the two-thirds proportion.**

`4π · Σ_{Im ρ ≤ V} m_ρ (Re ρ − ½) ≤ (log c₁ − (5/3) R + η) · V`  eventually, for every `η > 0`. -/
theorem eventually_offLineMoment_le_of_zetaGateFrom_twoThirds {α R c₁ η : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hR : 0 < R) (hc₁ : 1 ≤ c₁) (hη : 0 < η)
    (hg₁ : ZetaMollifiedMeanSquareGateFrom α R c₁) :
    ∀ᶠ V in atTop,
      4 * Real.pi * offLineMoment V ≤ (Real.log c₁ - (5 / 3) * R + η) * V := by
  classical
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨C, K, hC, hK, hceil⟩ :=
    exists_zetaOffLineFirstMoment_add_lineCount_le_of_mollified_meanSquare
  -- the slack in the two-thirds proportion
  obtain ⟨ε₀, hε₀0, hε₀third, hε₀R⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 3 ∧ ε₀ * R ≤ η / 16 := by
    refine ⟨min (1 / 3) (η / (16 * R)), lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
    have h1 : min (1 / 3) (η / (16 * R)) ≤ η / (16 * R) := min_le_right _ _
    have h2 : η / (16 * R) * R = η / 16 := by field_simp
    calc min (1 / 3) (η / (16 * R)) * R ≤ η / (16 * R) * R :=
          mul_le_mul_of_nonneg_right h1 hR.le
      _ = η / 16 := h2
  have hκ₀ : (0 : ℝ) ≤ 2 / 3 - ε₀ := by linarith
  have hε0 : 0 < c₁ * (η / 8) := by positivity
  have hlogε := log_gate_slack_le hc₁ hη
  have hε'0 : 0 < η / (60 * Real.pi * R) := by positivity
  have hε'bound := twoThirds_eps'_bound (ε₀ := ε₀) hR hη hε₀0
  obtain ⟨T₀, _, hrvm⟩ := exists_xiZeroCount_close (η / (60 * Real.pi * R)) hε'0
  obtain ⟨U₁, hU₁⟩ := two_thirds_simpleCritical_epsilon ε₀ hε₀0
  have hev : ∀ᶠ U : ℝ in atTop,
      4 * Real.pi * offLineMoment (U - 1) ≤ (Real.log c₁ - (5 / 3) * R + η) * (U - 1) := by
    filter_upwards [hg₁ (c₁ * (η / 8)) hε0, eventually_ge_atTop (max (T₀ + 1) (max (U₁ + 1) 23)),
      eventually_mul_log_le_quarter hK hη,
      eventually_const_le_quarter_sub_one (|Real.log c₁ - (5 / 3) * R + η / 4| + 2 * C)
        (show 0 < η / 2 by positivity),
      eventually_count_upper_le hα0 hα1 (2 * Real.pi + 4 * Real.pi * R / Real.log 20)
        (show 0 < η / 8 by positivity)]
      with U hU hUbig hlogU hDU₀ hcountU
    obtain ⟨T₁, T₂, σ₀, Mb, b, N, hT₁, hT₂, hN, hb1, hbn, hbreal, hMb1, hmass, hlogMb,
      hσ₀a, hσ₀b, hσ₀R, hG1, hG2, hP1, hP2, hMsq⟩ := hU
    have hU23 : 23 ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hUbig
    have hUT₀ : T₀ + 1 ≤ U := le_trans (le_max_left _ _) hUbig
    have hUU₁ : U₁ + 1 ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hUbig
    have hT₂big : U - 1 < T₂ := hT₂.1
    have hT₂U : T₂ ≤ U := hT₂.2
    have hT₁20 : 20 ≤ T₁ := hT₁.1
    have hT₁21 : T₁ ≤ U ^ α + 1 := hT₁.2
    have hUα := hcountU.2
    have hT12 : T₁ < T₂ := by linarith [hUα.2.1]
    have hT₂T₀ : T₀ ≤ T₂ := by linarith
    have hT₂U₁ : U₁ ≤ T₂ := by linarith
    have hlogT₂ : 0 < Real.log T₂ := Real.log_pos (by linarith)
    obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
    have hc := hceil b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂
      ((c₁ + c₁ * (η / 8)) * (T₂ - T₁)) hσ₀a hσ₀b hT₁20 hT12 hG1 hG2 hP1 hP2 hMsq Z hZ
    have hlogMsq : Real.log ((c₁ + c₁ * (η / 8)) * (T₂ - T₁) / (T₂ - T₁))
        = Real.log (c₁ + c₁ * (η / 8)) := by
      rw [mul_div_assoc, div_self (by linarith : T₂ - T₁ ≠ 0), mul_one]
    rw [hlogMsq] at hc
    -- the count credit, from the unconditional two-thirds theorem
    have hbridge1 := rightHalfOrderSum_sub_le_zetaZeroSum hT12.le Z hZ
    have hbridge2 := offLineMoment_le_add_zetaZeroMoment hT12.le Z hZ
    have hrefl₂ : (2 * rightHalfOrderSum T₂ : ℝ)
        = (xiPosZeroCount T₂ : ℝ) + (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast two_mul_rightHalfOrderSum T₂
    have hR₁nat : rightHalfOrderSum T₁ ≤ xiPosZeroCount T₁ := by
      unfold rightHalfOrderSum xiPosZeroCount
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hR₁ : (rightHalfOrderSum T₁ : ℝ) ≤ (xiPosZeroCount T₁ : ℝ) := by exact_mod_cast hR₁nat
    have hprop : (2 / 3 - ε₀) * (xiPosZeroCount T₂ : ℝ) ≤ (xiSimpleCriticalZeroCount T₂ : ℝ) :=
      hU₁ T₂ hT₂U₁
    have hsimple : (xiSimpleCriticalZeroCount T₂ : ℝ) ≤ (xiPosCriticalZeroCount T₂ : ℝ) := by
      exact_mod_cast xiSimpleCriticalZeroCount_le_xiPosCriticalZeroCount T₂
    have hS : (1 + (2 / 3 - ε₀) + 0) * (xiPosZeroCount T₂ : ℝ) / 2 - (xiPosZeroCount T₁ : ℝ)
        ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      linarith only [hbridge1, hrefl₂, hR₁, hprop, hsimple]
    -- Riemann–von Mangoldt
    have hN₂ : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
        ≤ (xiPosZeroCount T₂ : ℝ) := by
      have h := hrvm T₂ hT₂T₀
      have hcast : ((xiZeroCount T₂ : ℤ) : ℝ) = (xiPosZeroCount T₂ : ℝ) := by
        rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)]
        simp
      rw [hcast] at h
      have h1 := (abs_le.mp h).1
      have hid : (1 / (2 * Real.pi) - η / (60 * Real.pi * R)) * (T₂ * Real.log T₂)
          = 1 / (2 * Real.pi) * (T₂ * Real.log T₂)
            - η / (60 * Real.pi * R) * (T₂ * Real.log T₂) := by
        ring
      linarith only [h1, hid]
    have harith := offLineMoment_window_arith hR hlogT₂ hσ₀R (by linarith) hT12.le hK.le hlogMb
      (Real.log_nonneg (by linarith)) hκ₀ (le_refl (0 : ℝ)) hε'0.le (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hc hS hbridge2 hN₂
    have hmono := offLineMoment_mono (le_of_lt hT₂big)
    have hbr : Real.log (c₁ + c₁ * (η / 8))
        - R * (1 + (2 / 3 - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
        ≤ Real.log c₁ - (5 / 3) * R + η / 4 := by
      have hid : R * (1 + (2 / 3 - ε₀) + 0) * (1 - 2 * Real.pi * (η / (60 * Real.pi * R)))
          = (5 / 3) * R - ε₀ * R
            - 2 * Real.pi * (η / (60 * Real.pi * R)) * R * (1 + (2 / 3 - ε₀) + 0) := by ring
      linarith only [hlogε, hε'bound, hid, hε₀R]
    have hN₁nat : xiPosZeroCount T₁ ≤ xiPosZeroCount (U ^ α + 1) :=
      Finset.sum_le_sum_of_subset (stripFinsetPos_mono hT₁21)
    have hN₁ : (xiPosZeroCount T₁ : ℝ) ≤ (xiPosZeroCount (U ^ α + 1) : ℝ) := by
      exact_mod_cast hN₁nat
    have hM₁ : 4 * Real.pi * offLineMoment T₁
        ≤ 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (offLineMoment_le_half_xiPosZeroCount T₁).trans (by linarith only [hN₁])
    have hlog20 : Real.log 20 ≤ Real.log T₂ := Real.log_le_log (by norm_num) (by linarith)
    have hlog20pos : 0 < Real.log 20 := Real.log_pos (by norm_num)
    have hlast : 4 * Real.pi * R * (xiPosZeroCount T₁ : ℝ) / Real.log T₂
        ≤ 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 := by
      apply div_le_div₀ (by positivity) _ hlog20pos hlog20
      exact mul_le_mul_of_nonneg_left hN₁ (by positivity)
    have hlogT₂U : Real.log T₂ ≤ Real.log U := Real.log_le_log (by linarith) hT₂U
    have hKlog : 12 * K * Real.log T₂ ≤ η / 4 * U :=
      le_trans (mul_le_mul_of_nonneg_left hlogT₂U (by positivity)) hlogU
    have hmono' : 4 * Real.pi * offLineMoment (U - 1) ≤ 4 * Real.pi * offLineMoment T₂ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have hfinal := twoThirds_tail_arith (by linarith) hT₂big hT₂U harith hbr hM₁ hlast hKlog
      hmono'
    have hηU : η / 4 * U = η / 4 * (U - 1) + η / 4 := by ring
    have hη1 : η / 4 ≤ η / 4 * (U - 1) := by
      have h0 : 0 ≤ η / 4 * (U - 2) := mul_nonneg (by positivity) (by linarith only [hU23])
      have hid : η / 4 * (U - 1) = η / 4 + η / 4 * (U - 2) := by ring
      linarith only [h0, hid]
    have hBη : (Real.log c₁ - (5 / 3) * R + η) * (U - 1)
        = (U - 1) * (Real.log c₁ - (5 / 3) * R + η / 4) + 3 * (η / 4 * (U - 1)) := by
      ring
    have hDU : |Real.log c₁ - (5 / 3) * R + η / 4| + 2 * C
        + 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ))
        + 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20 ≤ η / 4 * (U - 1) := by
      have h1 := hcountU.1
      have hid : 4 * Real.pi * (1 / 2 * (xiPosZeroCount (U ^ α + 1) : ℝ))
          + 4 * Real.pi * R * (xiPosZeroCount (U ^ α + 1) : ℝ) / Real.log 20
          = (2 * Real.pi + 4 * Real.pi * R / Real.log 20) * (xiPosZeroCount (U ^ α + 1) : ℝ) := by
        ring
      have hηsplit : η / 2 / 4 * (U - 1) + η / 8 * (U - 1) = η / 4 * (U - 1) := by ring
      linarith only [hDU₀, h1, hid, hηsplit]
    rw [hBη]
    linarith only [hfinal, hDU, hηU, hη1]
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have := hshift.eventually hev
  simpa using this


end

end RHTower
