import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw

/-!
# High zeros carry a bounded critical deficit

The unconditional explicit formula
`exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le` writes the incoming critical prime
deficit as `Re Σ_q e^{T(ρ_q − 1/2)}/ρ_q²` up to `O((1+T)e^{−T/2})`. This module shows that, for
every `0 < α < 2/3`, the zero copies with `|γ| ≥ e^{T/(2α)}` contribute a bounded amount,
uniformly in `T ≥ 0` (`exists_highZero_deficitZeroWeight_tsum_le`).

Mechanism: on a dyadic shell `U ≤ |γ| ≤ 2U` with `U ≥ e^{T/(2α)}` the aperture `T/2` is at most
`α log U`, so the folded Guth–Maynard shell bound
`exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log` gives `Σ e^{T(β−1/2)} ≪ U^{3/2}`;
against `|ρ|^{−2} ≤ U^{−2}` each shell weighs `O(U^{−1/2})`, and the shells sum geometrically.

Consequently the incoming deficit at scale `x = e^T` is, up to a bounded error, the finite
exponential sum `lowZeroDeficitSum α T` over zeros of height below `x^{1/(2α)}`, any exponent
above `3/4` (`exists_abs_incoming_sub_lowZeroDeficitSum_le`), and the critical energy is
controlled by that finite sum (`exists_ccmPrimeDeficitCriticalEnergy_le_lowZeroDeficitSum`).
Through the coprime balance the same bound controls `−ccmPrimeDeficitCoprimeCrossWork`
(`exists_neg_coprimeCrossWork_le_lowZeroDeficitSum`). The Weil lag function, whose weights are
at most twice the deficit weights, has the same finite low-zero form
(`exists_abs_weilLagFunctionReal_sub_lowZeroLagSum_le`). These statements bound the high-zero
parts only; they give no bound for the low-zero sums.
-/

open Set Filter Finset
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open _root_.RHTower

noncomputable section
set_option autoImplicit false

/-- Weight of a zero copy in the reciprocal-square deficit series at aperture `T`. -/
def deficitZeroWeight (T : ℝ) (q : XiZeroCopy) : ℝ :=
  Real.exp (T * ((q.1 : ℂ).re - 1 / 2)) / ‖(q.1 : ℂ)‖ ^ 2

theorem deficitZeroWeight_nonneg (T : ℝ) (q : XiZeroCopy) : 0 ≤ deficitZeroWeight T q := by
  unfold deficitZeroWeight; positivity

/-- One dyadic shell `U ≤ |γ| ≤ 2U` above `e^{T/(2α)}` carries weight `O(U^{-1/2})`. -/
theorem exists_shell_deficitZeroWeight_le {α : ℝ} (hα0 : 0 < α) (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ T₀ : ℝ, 4 ≤ T₀ ∧
      ∀ T : ℝ, 0 ≤ T → ∀ U : ℝ, T₀ ≤ U → Real.exp (T / (2 * α)) ≤ U →
        ∀ G : Finset XiZeroCopy,
          (∀ q ∈ G, U ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * U) →
          ∑ q ∈ G, deficitZeroWeight T q ≤ C * U ^ (-(1 / 2) : ℝ) := by
  obtain ⟨C, hC, T₀, hT₀, hshell⟩ :=
    exists_sum_exp_foldedRe_le_subpower_up_to_two_thirds_log hα0.le hα
      (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨C, hC, T₀, hT₀, fun T hT U hU hUe G hG => ?_⟩
  have hU0 : 0 < U := by linarith
  have hA : T / 2 ≤ α * Real.log U := by
    have h := Real.log_le_log (Real.exp_pos _) hUe
    rw [Real.log_exp, div_le_iff₀ (by positivity)] at h
    linarith
  have hsum := hshell U hU (T / 2) (by linarith) hA G hG
  have hpt : ∀ q ∈ G, deficitZeroWeight T q ≤
      Real.exp (2 * (T / 2) * (foldedRe q - 1 / 2)) / U ^ 2 := by
    intro q hq
    have hnorm : U ≤ ‖(q.1 : ℂ)‖ := (hG q hq).1.trans (Complex.abs_im_le_norm _)
    have hexp : Real.exp (T * ((q.1 : ℂ).re - 1 / 2)) ≤
        Real.exp (2 * (T / 2) * (foldedRe q - 1 / 2)) := by
      apply Real.exp_le_exp.mpr
      have := re_le_foldedRe q
      nlinarith
    exact div_le_div₀ (Real.exp_pos _).le hexp (by positivity)
      (pow_le_pow_left₀ hU0.le hnorm 2)
  calc ∑ q ∈ G, deficitZeroWeight T q
      ≤ ∑ q ∈ G, Real.exp (2 * (T / 2) * (foldedRe q - 1 / 2)) / U ^ 2 := sum_le_sum hpt
    _ = (1 / U) * ((1 / U) * ∑ q ∈ G, Real.exp (2 * (T / 2) * (foldedRe q - 1 / 2))) := by
        rw [← Finset.sum_div]; field_simp
    _ ≤ (1 / U) * (C * U ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * U ^ (-(1 / 2) : ℝ) := by
        rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hU0, Real.rpow_one]
        ring

/-- The ratio `2^{-1/2}` of the dyadic shell series. -/
theorem shellRatio_bounds : 0 ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) ∧ (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
  set r : ℝ := (2 : ℝ) ^ (-(1 / 2) : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr2 : r ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact ⟨hr0, by nlinarith⟩

/-- `(2^k U)^{-1/2} = (2^{-1/2})^k U^{-1/2}`. -/
theorem two_pow_mul_rpow_neg_half (k : ℕ) {U : ℝ} (hU : 0 ≤ U) :
    ((2 : ℝ) ^ k * U) ^ (-(1 / 2) : ℝ) =
      ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ k * U ^ (-(1 / 2) : ℝ) := by
  rw [Real.mul_rpow (by positivity) hU, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm (k : ℝ)]

/-- **High zeros carry a bounded deficit weight.** For every `0 < α < 2/3` the zero copies
with `|γ| ≥ e^{T/(2α)}` have total weight `Σ e^{T(β−1/2)}/|ρ|²` bounded uniformly in `T ≥ 0`.
Shells above `max(e^{T/(2α)}, T₀)` are summed geometrically; the finitely many zeros below `T₀`
occur only for `T < 2α log T₀`, where `e^{T/2} ≤ T₀^α`. -/
theorem exists_highZero_deficitZeroWeight_tsum_le {α : ℝ} (hα0 : 0 < α) (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ∑' q : XiZeroCopy,
        (if Real.exp (T / (2 * α)) ≤ |(q.1 : ℂ).im| then deficitZeroWeight T q else 0) ≤ C := by
  obtain ⟨C₁, hC₁, T₀, hT₀, hshell⟩ := exists_shell_deficitZeroWeight_le hα0 hα
  obtain ⟨hr0, hr34⟩ := shellRatio_bounds
  set r : ℝ := (2 : ℝ) ^ (-(1 / 2) : ℝ)
  set W : ℝ := reciprocalSquareWeightTotal
  have hW : 0 ≤ W := reciprocalSquareWeightTotal_nonneg
  refine ⟨4 * C₁ + T₀ ^ α * W, by positivity, fun T hT => ?_⟩
  set e : ℝ := Real.exp (T / (2 * α))
  set H : ℝ := max e T₀
  have hH0 : 0 < H := lt_of_lt_of_le (by linarith) (le_max_right e T₀)
  have hH1 : 1 ≤ H := le_trans (by linarith) (le_max_right e T₀)
  -- shells above `H`
  have hhigh : ∀ G : Finset XiZeroCopy, (∀ q ∈ G, H ≤ |(q.1 : ℂ).im|) →
      ∑ q ∈ G, deficitZeroWeight T q ≤ 4 * C₁ := by
    intro G hG
    classical
    have hx (q : XiZeroCopy) (hq : q ∈ G) : 1 ≤ |(q.1 : ℂ).im| / H :=
      (one_le_div hH0).mpr (hG q hq)
    let kf : XiZeroCopy → ℕ := fun q =>
      if h : 1 ≤ |(q.1 : ℂ).im| / H then Classical.choose (exists_nat_pow_near h one_lt_two)
      else 0
    have hkf (q : XiZeroCopy) (hq : q ∈ G) :
        (2 : ℝ) ^ kf q * H ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| ≤ 2 * ((2 : ℝ) ^ kf q * H) := by
      have hspec := Classical.choose_spec (exists_nat_pow_near (hx q hq) one_lt_two)
      have hk : kf q = Classical.choose (exists_nat_pow_near (hx q hq) one_lt_two) := by
        simp only [kf, dif_pos (hx q hq)]
      rw [hk]
      constructor
      · exact (le_div_iff₀ hH0).mp hspec.1
      · have := (div_lt_iff₀ hH0).mp hspec.2
        rw [pow_succ] at this
        linarith
    rw [← Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem kf hq)]
    have hfib : ∀ k ∈ G.image kf,
        ∑ q ∈ G with kf q = k, deficitZeroWeight T q ≤ C₁ * r ^ k := by
      intro k _
      have hUk : T₀ ≤ (2 : ℝ) ^ k * H :=
        (le_max_right e T₀).trans (le_mul_of_one_le_left hH0.le (one_le_pow₀ one_le_two))
      have hUe : e ≤ (2 : ℝ) ^ k * H :=
        (le_max_left e T₀).trans (le_mul_of_one_le_left hH0.le (one_le_pow₀ one_le_two))
      have h := hshell T hT ((2 : ℝ) ^ k * H) hUk hUe (G.filter (fun q => kf q = k))
        (fun q hq => by
          rw [Finset.mem_filter] at hq
          simpa only [hq.2] using hkf q hq.1)
      rw [two_pow_mul_rpow_neg_half k hH0.le] at h
      have hHr : H ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hH1 (by norm_num)
      calc ∑ q ∈ G with kf q = k, deficitZeroWeight T q
          ≤ C₁ * (r ^ k * H ^ (-(1 / 2) : ℝ)) := h
        _ ≤ C₁ * (r ^ k * 1) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hHr (pow_nonneg hr0 k)) hC₁
        _ = C₁ * r ^ k := by ring
    have hgeom : ∑ k ∈ G.image kf, r ^ k ≤ 4 := by
      have hsum := summable_geometric_of_lt_one hr0 (by linarith)
      calc ∑ k ∈ G.image kf, r ^ k ≤ ∑' k : ℕ, r ^ k :=
            hsum.sum_le_tsum _ (fun k _ => pow_nonneg hr0 k)
        _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 (by linarith)
        _ ≤ 4 := by
            rw [inv_le_comm₀ (by linarith) (by norm_num)]
            linarith
    calc ∑ k ∈ G.image kf, ∑ q ∈ G with kf q = k, deficitZeroWeight T q
        ≤ ∑ k ∈ G.image kf, C₁ * r ^ k := sum_le_sum hfib
      _ = C₁ * ∑ k ∈ G.image kf, r ^ k := (Finset.mul_sum _ _ _).symm
      _ ≤ C₁ * 4 := mul_le_mul_of_nonneg_left hgeom hC₁
      _ = 4 * C₁ := by ring
  -- the finitely many zeros between `e` and `T₀`
  have hlow : ∀ G : Finset XiZeroCopy,
      (∀ q ∈ G, e ≤ |(q.1 : ℂ).im| ∧ |(q.1 : ℂ).im| < T₀) →
      ∑ q ∈ G, deficitZeroWeight T q ≤ T₀ ^ α * W := by
    intro G hG
    have hpt : ∀ q ∈ G, deficitZeroWeight T q ≤ T₀ ^ α * (1 / ‖(q.1 : ℂ)‖ ^ 2) := by
      intro q hq
      have heT : e < T₀ := (hG q hq).1.trans_lt (hG q hq).2
      have hT2 : T / 2 ≤ α * Real.log T₀ := by
        have h := Real.log_lt_log (Real.exp_pos _) heT
        rw [Real.log_exp, div_lt_iff₀ (by positivity)] at h
        linarith
      have hexp : Real.exp (T * ((q.1 : ℂ).re - 1 / 2)) ≤ T₀ ^ α := by
        rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log T₀)]
        apply Real.exp_le_exp.mpr
        have := xiZeroCopy_re_lt_one q
        nlinarith
      unfold deficitZeroWeight
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hexp (by positivity)
    calc ∑ q ∈ G, deficitZeroWeight T q ≤ ∑ q ∈ G, T₀ ^ α * (1 / ‖(q.1 : ℂ)‖ ^ 2) :=
          sum_le_sum hpt
      _ = T₀ ^ α * ∑ q ∈ G, 1 / ‖(q.1 : ℂ)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ T₀ ^ α * W :=
          mul_le_mul_of_nonneg_left
            (summable_inv_norm_sq_xiZeroCopy.sum_le_tsum _ (fun q _ => by positivity))
            (by positivity)
  apply Real.tsum_le_of_sum_le
  · intro q
    dsimp only
    split_ifs
    · exact deficitZeroWeight_nonneg T q
    · exact le_rfl
  · intro s
    classical
    rw [← Finset.sum_filter]
    set G := s.filter (fun q => e ≤ |(q.1 : ℂ).im|)
    rw [← Finset.sum_filter_add_sum_filter_not G (fun q => H ≤ |(q.1 : ℂ).im|)]
    refine add_le_add (hhigh _ fun q hq => (Finset.mem_filter.mp hq).2) (hlow _ fun q hq => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at hq
    refine ⟨hq.1.2, ?_⟩
    have h : |(q.1 : ℂ).im| < max e T₀ := not_le.mp hq.2
    rcases le_total e T₀ with h' | h'
    · rwa [max_eq_right h'] at h
    · rw [max_eq_left h'] at h
      exact absurd hq.1.2 (not_le.mpr h)

/-- Norm of one term of `spectralDeficitSum`. -/
theorem norm_spectralDeficitTerm (T : ℝ) (q : XiZeroCopy) :
    ‖(1 / (q.1 : ℂ) ^ 2) * Complex.exp ((T : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ =
      deficitZeroWeight T q := by
  rw [norm_mul, Complex.norm_exp, norm_div, norm_one, norm_pow, deficitZeroWeight]
  have hre : ((T : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = T * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  ring

theorem summable_deficitZeroWeight {T : ℝ} (hT : 0 ≤ T) :
    Summable (deficitZeroWeight T) := by
  refine (summable_inv_norm_sq_xiZeroCopy.mul_left (Real.exp (T / 2))).of_nonneg_of_le
    (deficitZeroWeight_nonneg T) fun q => ?_
  unfold deficitZeroWeight
  rw [mul_one_div]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
  have := xiZeroCopy_re_lt_one q
  nlinarith

/-- The reciprocal-square deficit series restricted to zero copies with `|γ| < e^{T/(2α)}`. -/
def lowZeroDeficitSum (α T : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, if |(q.1 : ℂ).im| < Real.exp (T / (2 * α)) then
    (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((T : ℂ) * ((q.1 : ℂ) - 1 / 2)) else 0

/-- `lowZeroDeficitSum` is a finite exponential sum over the zeros below `e^{T/(2α)}`. -/
theorem lowZeroDeficitSum_eq_sum (α T : ℝ) :
    lowZeroDeficitSum α T =
      ∑ q ∈ (finite_xiOrdinateWindow (Real.exp (T / (2 * α))) 0).toFinset,
        if |(q.1 : ℂ).im| < Real.exp (T / (2 * α)) then
          (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((T : ℂ) * ((q.1 : ℂ) - 1 / 2)) else 0 := by
  unfold lowZeroDeficitSum
  refine tsum_eq_sum fun q hq => ?_
  rw [Set.Finite.mem_toFinset, mem_xiOrdinateWindow_iff, sub_zero] at hq
  rw [if_neg fun h => hq h.le]

/-- **The incoming critical deficit is a finite low-zero sum up to a bounded error.** For every
`0 < α < 2/3` there is `C` with
`|ccmPrimeDeficitIncoming T − Re lowZeroDeficitSum α T| ≤ C` for all `T ≥ 0`: the zeros of height
at least `e^{T/(2α)}` contribute boundedly (`exists_highZero_deficitZeroWeight_tsum_le`), and the
explicit-formula remainder `C₀(1+T)e^{−T/2}` is at most `2C₀`. -/
theorem exists_abs_incoming_sub_lowZeroDeficitSum_le {α : ℝ} (hα0 : 0 < α) (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitIncoming T - (lowZeroDeficitSum α T).re| ≤ C := by
  obtain ⟨Ch, hCh, hhigh⟩ := exists_highZero_deficitZeroWeight_tsum_le hα0 hα
  obtain ⟨C₀, hC₀, hexpl⟩ := exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le
  refine ⟨2 * C₀ + Ch, by positivity, fun T hT => ?_⟩
  classical
  have hhighT := hhigh T hT
  set e : ℝ := Real.exp (T / (2 * α))
  set f : XiZeroCopy → ℂ := fun q =>
    (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((T : ℂ) * ((q.1 : ℂ) - 1 / 2))
  have hfw (q : XiZeroCopy) : ‖f q‖ = deficitZeroWeight T q := norm_spectralDeficitTerm T q
  have hw := summable_deficitZeroWeight hT
  have hsl : Summable fun q => if |(q.1 : ℂ).im| < e then f q else 0 :=
    Summable.of_norm_bounded hw fun q => by
      by_cases h : |(q.1 : ℂ).im| < e
      · rw [if_pos h, hfw]
      · rw [if_neg h, norm_zero]; exact deficitZeroWeight_nonneg T q
  have hhigh_pt (q : XiZeroCopy) :
      ‖if ¬ |(q.1 : ℂ).im| < e then f q else 0‖ =
        if e ≤ |(q.1 : ℂ).im| then deficitZeroWeight T q else 0 := by
    by_cases h : |(q.1 : ℂ).im| < e
    · rw [if_neg (not_not.mpr h), if_neg (not_le.mpr h), norm_zero]
    · rw [if_pos h, if_pos (not_lt.mp h), hfw]
  have hhn : Summable fun q => ‖if ¬ |(q.1 : ℂ).im| < e then f q else 0‖ :=
    hw.of_nonneg_of_le (fun _ => norm_nonneg _) fun q => by
      rw [hhigh_pt]
      split_ifs
      · exact le_rfl
      · exact deficitZeroWeight_nonneg T q
  have hsplit : spectralDeficitSum T = lowZeroDeficitSum α T +
      ∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0) := by
    rw [lowZeroDeficitSum, ← hsl.tsum_add hhn.of_norm]
    unfold spectralDeficitSum
    congr 1
    funext q
    by_cases h : |(q.1 : ℂ).im| < e
    · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]
  have hhigh_le : ‖∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)‖ ≤ Ch :=
    (norm_tsum_le_tsum_norm hhn).trans (le_of_eq_of_le (tsum_congr hhigh_pt) hhighT)
  have hbump : (1 + T) * Real.exp (-T / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (T / 2)
    have h2 : Real.exp (T / 2) * Real.exp (-T / 2) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    nlinarith [Real.exp_pos (-T / 2)]
  have hre : |(∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)).re| ≤ Ch :=
    (Complex.abs_re_le_norm _).trans hhigh_le
  have hdec : ccmPrimeDeficitIncoming T - (lowZeroDeficitSum α T).re =
      (ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re) +
        (∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)).re := by
    rw [hsplit, Complex.add_re]; ring
  rw [hdec]
  calc _ ≤ |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| +
        |(∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)).re| := abs_add_le _ _
    _ ≤ C₀ * (1 + T) * Real.exp (-T / 2) + Ch := add_le_add (hexpl T hT) hre
    _ ≤ 2 * C₀ + Ch := by nlinarith

/-- **Critical energy is controlled by the low-zero sum.** For every `0 < α < 2/3` there is `C`
with `ccmPrimeDeficitCriticalEnergy T ≤ 2 (Re lowZeroDeficitSum α T)² + C` for all `T ≥ 0`. -/
theorem exists_ccmPrimeDeficitCriticalEnergy_le_lowZeroDeficitSum {α : ℝ} (hα0 : 0 < α)
    (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ccmPrimeDeficitCriticalEnergy T ≤ 2 * (lowZeroDeficitSum α T).re ^ 2 + C := by
  obtain ⟨C, hC, h⟩ := exists_abs_incoming_sub_lowZeroDeficitSum_le hα0 hα
  refine ⟨2 * C ^ 2, by positivity, fun T hT => ?_⟩
  rw [← ccmPrimeDeficitIncoming_sq]
  have hd := abs_le.mp (h T hT)
  nlinarith [sq_nonneg (ccmPrimeDeficitIncoming T - 2 * (lowZeroDeficitSum α T).re)]

/-- **Coprime cross-work is bounded below by the low-zero sum.** By the coprime balance
`|E + coprimeCrossWork| ≤ 49/4`, for every `0 < α < 2/3` there is `C` with
`−ccmPrimeDeficitCoprimeCrossWork T ≤ 2 (Re lowZeroDeficitSum α T)² + C` for all `T ≥ 0`. -/
theorem exists_neg_coprimeCrossWork_le_lowZeroDeficitSum {α : ℝ} (hα0 : 0 < α)
    (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      -ccmPrimeDeficitCoprimeCrossWork T ≤ 2 * (lowZeroDeficitSum α T).re ^ 2 + C := by
  obtain ⟨C, hC, h⟩ := exists_ccmPrimeDeficitCriticalEnergy_le_lowZeroDeficitSum hα0 hα
  refine ⟨C + 49 / 4, by positivity, fun T hT => ?_⟩
  have hb := (abs_le.mp (abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le hT)).1
  linarith [h T hT]

/-! ## The Weil lag function -/

/-- The lag weight is at most twice the deficit weight: `|ρ| ≤ 1 + |1−ρ| ≤ 2|1−ρ|`. -/
theorem norm_weilLagTerm_le_two_mul_deficitZeroWeight (T : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp (T * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      2 * deficitZeroWeight T q := by
  have h4 := four_lt_norm_one_sub_xiZeroCopy q
  have h4' := four_lt_norm_xiZeroCopy q
  have htri : ‖(q.1 : ℂ)‖ ≤ 2 * ‖1 - (q.1 : ℂ)‖ := by
    have h := norm_sub_le (1 : ℂ) (1 - (q.1 : ℂ))
    rw [sub_sub_cancel, norm_one] at h
    linarith
  have hre : ((T : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = T * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [norm_div, norm_mul, Complex.norm_exp, hre, deficitZeroWeight, mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hE := Real.exp_pos (T * ((q.1 : ℂ).re - 1 / 2))
  have ha : 0 < ‖(q.1 : ℂ)‖ := by linarith
  have := mul_le_mul_of_nonneg_left htri (mul_pos hE ha).le
  nlinarith

/-- The Weil lag series restricted to zero copies with `|γ| < e^{L/(2α)}`. -/
def lowZeroLagSum (α L : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, if |(q.1 : ℂ).im| < Real.exp (L / (2 * α)) then
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) else 0

/-- **The Weil lag function is a finite low-zero sum up to a bounded error.** For every
`0 < α < 2/3` there is `C` with `|weilLagFunctionReal L − Re lowZeroLagSum α L| ≤ C` for all
`L ≥ 0`; the zeros above `e^{L/(2α)}` carry at most twice the bounded high-zero deficit weight. -/
theorem exists_abs_weilLagFunctionReal_sub_lowZeroLagSum_le {α : ℝ} (hα0 : 0 < α)
    (hα : α < 2 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
      |weilLagFunctionReal L - (lowZeroLagSum α L).re| ≤ C := by
  obtain ⟨Ch, hCh, hhigh⟩ := exists_highZero_deficitZeroWeight_tsum_le hα0 hα
  refine ⟨2 * Ch, by positivity, fun L hL => ?_⟩
  classical
  have hhighL := hhigh L hL
  set e : ℝ := Real.exp (L / (2 * α))
  set f : XiZeroCopy → ℂ := fun q =>
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
  have hfw (q : XiZeroCopy) : ‖f q‖ ≤ 2 * deficitZeroWeight L q :=
    norm_weilLagTerm_le_two_mul_deficitZeroWeight L q
  have hw := (summable_deficitZeroWeight hL).mul_left 2
  have hsl : Summable fun q => if |(q.1 : ℂ).im| < e then f q else 0 :=
    Summable.of_norm_bounded hw fun q => by
      by_cases h : |(q.1 : ℂ).im| < e
      · rw [if_pos h]; exact hfw q
      · rw [if_neg h, norm_zero]; exact mul_nonneg zero_le_two (deficitZeroWeight_nonneg L q)
  have hhigh_pt (q : XiZeroCopy) :
      ‖if ¬ |(q.1 : ℂ).im| < e then f q else 0‖ ≤
        2 * (if e ≤ |(q.1 : ℂ).im| then deficitZeroWeight L q else 0) := by
    by_cases h : |(q.1 : ℂ).im| < e
    · rw [if_neg (not_not.mpr h), if_neg (not_le.mpr h), norm_zero, mul_zero]
    · rw [if_pos h, if_pos (not_lt.mp h)]; exact hfw q
  have hind : Summable fun q =>
      2 * (if e ≤ |(q.1 : ℂ).im| then deficitZeroWeight L q else 0) :=
    hw.of_nonneg_of_le
      (fun q => mul_nonneg zero_le_two (by split_ifs <;> simp [deficitZeroWeight_nonneg]))
      (fun q => mul_le_mul_of_nonneg_left
        (by split_ifs <;> simp [deficitZeroWeight_nonneg]) zero_le_two)
  have hhn : Summable fun q => ‖if ¬ |(q.1 : ℂ).im| < e then f q else 0‖ :=
    hind.of_nonneg_of_le (fun _ => norm_nonneg _) hhigh_pt
  have hsplit : weilLagFunction L = lowZeroLagSum α L +
      ∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0) := by
    rw [lowZeroLagSum, ← hsl.tsum_add hhn.of_norm]
    unfold weilLagFunction
    congr 1
    funext q
    by_cases h : |(q.1 : ℂ).im| < e
    · rw [if_pos h, if_neg (not_not.mpr h), add_zero]
    · rw [if_neg h, if_pos h, zero_add]
  have hhigh_le : ‖∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)‖ ≤ 2 * Ch := by
    refine (norm_tsum_le_tsum_norm hhn).trans ((hhn.tsum_le_tsum hhigh_pt hind).trans ?_)
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hhighL zero_le_two
  have hdec : weilLagFunctionReal L - (lowZeroLagSum α L).re =
      (∑' q, (if ¬ |(q.1 : ℂ).im| < e then f q else 0)).re := by
    rw [weilLagFunctionReal, hsplit, Complex.add_re]; ring
  rw [hdec]
  exact (Complex.abs_re_le_norm _).trans hhigh_le

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
