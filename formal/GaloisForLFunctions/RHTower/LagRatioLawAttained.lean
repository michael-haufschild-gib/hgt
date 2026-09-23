import GaloisForLFunctions.HTGeometry.TrigonometricSumWindowMean
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import GaloisForLFunctions.RHTower.PrimeLagLandauWeights

/-!
# The lag ratio law when the supremum of the real parts is attained

If some zero attains the maximal real part `β₀ > ½`, the lag function `Φ(L)` is, after the
normalisation `e^{−L(β₀−½)}`, a real almost periodic sum over the top level plus a tail that tends to
zero.  A finite truncation of the top sum is a real trigonometric polynomial with coefficients of
positive real part; its window mean is small and its window mean square is bounded below, so it
exceeds a fixed positive constant somewhere in every long window, and by its Lipschitz bound on a
fixed neighbourhood of that point.  Any set of integers whose logarithms are eventually `δ`-dense
for every `δ > 0` therefore carries lag values `≥ c · n^{β₀−½}`, hence unbounded above.
-/

open Complex Filter Topology Set TrigSum

namespace RHTower

noncomputable section

variable {β₀ : ℝ}

/-! ## The top coefficients and the two tails -/

/-- The top-level coefficient: `lagWeight q` when `Re ρ_q = β₀`, else `0`. -/
def lagTopCoeff (β₀ : ℝ) (q : XiZeroCopy) : ℂ := if (q.1 : ℂ).re = β₀ then lagWeight q else 0

theorem norm_lagTopCoeff_le (β₀ : ℝ) : ∀ q : XiZeroCopy, ‖lagTopCoeff β₀ q‖ ≤ ‖lagWeight q‖ := fun q => by
  by_cases h : (q.1 : ℂ).re = β₀ <;> simp [lagTopCoeff, h]

theorem summable_norm_lagTopCoeff (β₀ : ℝ) : Summable fun q => ‖lagTopCoeff β₀ q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_lagTopCoeff_le β₀) summable_norm_lagWeight

/-- The tail of the top coefficients outside a finite set. -/
def topTail (β₀ : ℝ) (F : Finset XiZeroCopy) : ℝ := ∑' q : ↥((F : Set XiZeroCopy)ᶜ), ‖lagTopCoeff β₀ q‖

theorem tendsto_topTail (β₀ : ℝ) : Tendsto (topTail β₀) atTop (𝓝 0) :=
  tendsto_tsum_compl_atTop_zero fun q => ‖lagTopCoeff β₀ q‖

/-- The lower term of the copy `q` at scale `L`. -/
def lowerTerm (β₀ L : ℝ) (q : XiZeroCopy) : ℝ :=
  if (q.1 : ℂ).re = β₀ then 0 else ‖lagWeight q‖ * Real.exp (-(L * (β₀ - (q.1 : ℂ).re)))

theorem lowerTerm_nonneg (β₀ L : ℝ) (q : XiZeroCopy) : 0 ≤ lowerTerm β₀ L q := by
  unfold lowerTerm; split_ifs <;> positivity

theorem lowerTerm_le (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) {L : ℝ} (hL : 0 ≤ L)
    (q : XiZeroCopy) : lowerTerm β₀ L q ≤ ‖lagWeight q‖ := by
  unfold lowerTerm
  split_ifs with h
  · exact norm_nonneg _
  · have : Real.exp (-(L * (β₀ - (q.1 : ℂ).re))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := hmax q
      nlinarith
    calc ‖lagWeight q‖ * Real.exp (-(L * (β₀ - (q.1 : ℂ).re))) ≤ ‖lagWeight q‖ * 1 := by gcongr
      _ = ‖lagWeight q‖ := mul_one _

theorem summable_lowerTerm (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) {L : ℝ} (hL : 0 ≤ L) :
    Summable (lowerTerm β₀ L) :=
  Summable.of_nonneg_of_le (lowerTerm_nonneg β₀ L) (lowerTerm_le hmax hL) summable_norm_lagWeight

/-- The lower tail at scale `L`. -/
def lowerTailReal (β₀ L : ℝ) : ℝ := ∑' q : XiZeroCopy, lowerTerm β₀ L q

theorem lowerTailReal_nonneg (β₀ L : ℝ) : 0 ≤ lowerTailReal β₀ L :=
  tsum_nonneg (lowerTerm_nonneg β₀ L)

/-- Below an attained maximum the lower tail tends to zero. -/
theorem tendsto_lowerTailReal (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) :
    Tendsto (lowerTailReal β₀) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (L : ℝ) (q : XiZeroCopy) => lowerTerm β₀ L q) (g := fun _ => 0)
    (bound := fun q : XiZeroCopy => ‖lagWeight q‖) summable_norm_lagWeight ?_ ?_
  · unfold lowerTailReal
    rw [tsum_zero] at h
    exact h
  · intro q
    unfold lowerTerm
    split_ifs with hq
    · exact tendsto_const_nhds
    · have hpos : 0 < β₀ - (q.1 : ℂ).re := lt_of_le_of_ne (by linarith [hmax q]) (Ne.symm (sub_ne_zero.mpr (Ne.symm hq)))
      have h1 : Tendsto (fun L : ℝ => -(L * (β₀ - (q.1 : ℂ).re))) atTop atBot := by
        have := (tendsto_id.atTop_mul_const hpos)
        exact tendsto_neg_atTop_atBot.comp this
      have h2 := Real.tendsto_exp_atBot.comp h1
      simpa using h2.const_mul ‖lagWeight q‖
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL q
    rw [Real.norm_eq_abs, abs_of_nonneg (lowerTerm_nonneg β₀ L q)]
    exact lowerTerm_le hmax hL q

/-! ## The scaled lag function -/

/-- The term of the lag function at scale `L`, renormalised by `e^{−L(β₀−½)}`. -/
def scaledTerm (β₀ L : ℝ) (q : XiZeroCopy) : ℂ :=
  lagWeight q * cexp (L * ((q.1 : ℂ) - 1 / 2)) * (Real.exp (-(L * (β₀ - 1 / 2))) : ℂ)

theorem scaledTerm_top {L : ℝ} {q : XiZeroCopy} (hq : (q.1 : ℂ).re = β₀) :
    scaledTerm β₀ L q = lagTopCoeff β₀ q * cexp (I * (zeroOrdinate q * L)) := by
  unfold scaledTerm lagTopCoeff
  rw [if_pos hq, exp_lag_top hq]
  have e1 : ((Real.exp (L * (β₀ - 1 / 2)) : ℝ) : ℂ) * ((Real.exp (-(L * (β₀ - 1 / 2))) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have e2 : cexp (I * ((L * zeroOrdinate q : ℝ) : ℂ)) = cexp (I * ((zeroOrdinate q : ℂ) * L)) := by
    congr 1; push_cast; ring
  rw [e2]
  linear_combination (lagWeight q * cexp (I * ((zeroOrdinate q : ℂ) * L))) * e1

theorem norm_scaledTerm_eq (β₀ L : ℝ) (q : XiZeroCopy) :
    ‖scaledTerm β₀ L q‖ = ‖lagWeight q‖ * Real.exp (-(L * (β₀ - (q.1 : ℂ).re))) := by
  unfold scaledTerm
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
  congr 2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im]
  norm_num
  ring

theorem norm_scaledTerm_le (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) {L : ℝ} (hL : 0 ≤ L)
    (q : XiZeroCopy) : ‖scaledTerm β₀ L q‖ ≤ ‖lagWeight q‖ := by
  rw [norm_scaledTerm_eq]
  have : Real.exp (-(L * (β₀ - (q.1 : ℂ).re))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := hmax q
    nlinarith
  calc ‖lagWeight q‖ * Real.exp (-(L * (β₀ - (q.1 : ℂ).re))) ≤ ‖lagWeight q‖ * 1 := by gcongr
    _ = ‖lagWeight q‖ := mul_one _

theorem norm_scaledTerm_le_lagTopCoeff_add_lowerTerm (β₀ L : ℝ) (q : XiZeroCopy) :
    ‖scaledTerm β₀ L q‖ ≤ ‖lagTopCoeff β₀ q‖ + lowerTerm β₀ L q := by
  rw [norm_scaledTerm_eq]
  unfold lagTopCoeff lowerTerm
  by_cases h : (q.1 : ℂ).re = β₀
  · rw [if_pos h, if_pos h, h, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one, add_zero]
  · rw [if_neg h, if_neg h, norm_zero, zero_add]

theorem summable_scaledTerm (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) {L : ℝ} (hL : 0 ≤ L) :
    Summable (scaledTerm β₀ L) :=
  Summable.of_norm_bounded summable_norm_lagWeight (norm_scaledTerm_le hmax hL)

theorem tsum_scaledTerm_eq (β₀ L : ℝ) :
    ∑' q, scaledTerm β₀ L q = (weilLagFunctionReal L : ℂ) * (Real.exp (-(L * (β₀ - 1 / 2))) : ℂ) := by
  unfold scaledTerm
  rw [tsum_mul_right, ← weilLagFunction_eq_tsum_lagWeight, weilLagFunction_eq_ofReal]

/-- **The decomposition.**  For `L ≥ 0` the scaled lag function differs from the truncated top
trigonometric sum by at most `topTail F + 2 · lowerTail L`. -/
theorem abs_scaledLag_sub_trigSum_le (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀)
    (F : Finset XiZeroCopy) {L : ℝ} (hL : 0 ≤ L) :
    |weilLagFunctionReal L * Real.exp (-(L * (β₀ - 1 / 2)))
        - (trigSum F (lagTopCoeff β₀) zeroOrdinate L).re|
      ≤ topTail β₀ F + 2 * lowerTailReal β₀ L := by
  classical
  have hsum := summable_scaledTerm hmax (β₀ := β₀) hL
  have hsplit := hsum.sum_add_tsum_compl (s := F)
  have hreal : weilLagFunctionReal L * Real.exp (-(L * (β₀ - 1 / 2)))
      = (∑' q, scaledTerm β₀ L q).re := by
    rw [tsum_scaledTerm_eq, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hreal, ← hsplit, Complex.add_re, Complex.re_sum]
  unfold trigSum
  rw [Complex.re_sum]
  -- the finite part: differences vanish on the top level and are lower terms elsewhere
  have hfin : |∑ q ∈ F, (scaledTerm β₀ L q).re - ∑ q ∈ F, (lagTopCoeff β₀ q * cexp (I * (zeroOrdinate q * L))).re|
      ≤ lowerTailReal β₀ L := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun q _ => ?_) ((summable_lowerTerm hmax hL).sum_le_tsum F
      fun q _ => lowerTerm_nonneg β₀ L q)
    by_cases hq : (q.1 : ℂ).re = β₀
    · rw [scaledTerm_top hq, sub_self, abs_zero]
      exact lowerTerm_nonneg β₀ L q
    · have h0 : lagTopCoeff β₀ q = 0 := by unfold lagTopCoeff; rw [if_neg hq]
      rw [h0, zero_mul, Complex.zero_re, sub_zero]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_scaledTerm_eq]
      unfold lowerTerm
      rw [if_neg hq]
  -- the infinite part
  have hinf : |(∑' q : ↥((F : Set XiZeroCopy)ᶜ), scaledTerm β₀ L q).re| ≤ topTail β₀ F + lowerTailReal β₀ L := by
    refine (Complex.abs_re_le_norm _).trans ?_
    have hs1 : Summable fun q : ↥((F : Set XiZeroCopy)ᶜ) => ‖scaledTerm β₀ L q‖ := (hsum.norm).subtype _
    have hs2 : Summable fun q : ↥((F : Set XiZeroCopy)ᶜ) => ‖lagTopCoeff β₀ q‖ + lowerTerm β₀ L q :=
      ((summable_norm_lagTopCoeff β₀).add (summable_lowerTerm hmax hL)).subtype _
    calc ‖∑' q : ↥((F : Set XiZeroCopy)ᶜ), scaledTerm β₀ L q‖ ≤ ∑' q : ↥((F : Set XiZeroCopy)ᶜ), ‖scaledTerm β₀ L q‖ :=
          norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : ↥((F : Set XiZeroCopy)ᶜ), (‖lagTopCoeff β₀ q‖ + lowerTerm β₀ L q) :=
          hs1.tsum_le_tsum (fun q => norm_scaledTerm_le_lagTopCoeff_add_lowerTerm β₀ L q) hs2
      _ = ∑' q : ↥((F : Set XiZeroCopy)ᶜ), ‖lagTopCoeff β₀ q‖ + ∑' q : ↥((F : Set XiZeroCopy)ᶜ), lowerTerm β₀ L q :=
          Summable.tsum_add ((summable_norm_lagTopCoeff β₀).subtype _) ((summable_lowerTerm hmax hL).subtype _)
      _ ≤ topTail β₀ F + lowerTailReal β₀ L := by
          gcongr
          · exact le_rfl
          · exact Summable.tsum_subtype_le _ _ (lowerTerm_nonneg β₀ L) (summable_lowerTerm hmax hL)
  calc |∑ q ∈ F, (scaledTerm β₀ L q).re + (∑' q : ↥((F : Set XiZeroCopy)ᶜ), scaledTerm β₀ L q).re
        - ∑ q ∈ F, (lagTopCoeff β₀ q * cexp (I * (zeroOrdinate q * L))).re|
      = |(∑ q ∈ F, (scaledTerm β₀ L q).re - ∑ q ∈ F, (lagTopCoeff β₀ q * cexp (I * (zeroOrdinate q * L))).re)
        + (∑' q : ↥((F : Set XiZeroCopy)ᶜ), scaledTerm β₀ L q).re| := by congr 1; ring
    _ ≤ |∑ q ∈ F, (scaledTerm β₀ L q).re - ∑ q ∈ F, (lagTopCoeff β₀ q * cexp (I * (zeroOrdinate q * L))).re|
        + |(∑' q : ↥((F : Set XiZeroCopy)ᶜ), scaledTerm β₀ L q).re| := abs_add_le _ _
    _ ≤ lowerTailReal β₀ L + (topTail β₀ F + lowerTailReal β₀ L) := add_le_add hfin hinf
    _ = topTail β₀ F + 2 * lowerTailReal β₀ L := by ring

/-! ## The pair main terms on the top level -/

theorem lagWeight_eq_of_eq {q q' : XiZeroCopy} (h : (q.1 : ℂ) = (q'.1 : ℂ)) : lagWeight q = lagWeight q' := by
  unfold lagWeight; rw [h]

theorem lagWeight_conj {q q' : XiZeroCopy} (h : (q'.1 : ℂ) = starRingEnd ℂ (q.1 : ℂ)) :
    lagWeight q' = starRingEnd ℂ (lagWeight q) := by
  unfold lagWeight
  rw [h, map_div₀, map_one, map_mul, map_sub, map_one]

theorem pairMain_lagTopCoeff_nonneg (β₀ : ℝ) (q q' : XiZeroCopy) :
    0 ≤ pairMain (lagTopCoeff β₀) zeroOrdinate q q' := by
  by_cases hq : (q.1 : ℂ).re = β₀
  · by_cases hq' : (q'.1 : ℂ).re = β₀
    · refine pairMain_nonneg _ _ q q' ?_ ?_
      · intro hγ
        unfold lagTopCoeff
        rw [if_pos hq, if_pos hq']
        apply lagWeight_eq_of_eq
        apply Complex.ext
        · rw [hq, hq']
        · exact hγ
      · intro hγ
        unfold lagTopCoeff
        rw [if_pos hq, if_pos hq']
        apply lagWeight_conj
        apply Complex.ext
        · rw [Complex.conj_re, hq, hq']
        · rw [Complex.conj_im]
          unfold zeroOrdinate at hγ
          linarith
    · rw [pairMain_zero_right _ _ q q' (by unfold lagTopCoeff; rw [if_neg hq'])]
  · rw [pairMain_zero_left _ _ q q' (by unfold lagTopCoeff; rw [if_neg hq])]

theorem pairMain_lagTopCoeff_self (β₀ : ℝ) (q : XiZeroCopy) :
    ‖lagTopCoeff β₀ q‖ ^ (2 : ℕ) ≤ pairMain (lagTopCoeff β₀) zeroOrdinate q q :=
  le_of_eq (pairMain_self_of_ne _ _ q (zeroOrdinate_ne_zero' q)).symm

/-! ## The attained-case ratio law -/

/-- **The lag ratio law when the top is attained.**  If some zero attains the maximal real part
`β₀ > ½` and the logarithms of `N` are eventually `δ`-dense for every `δ > 0`, the lag values on `N`
are unbounded above. -/
theorem exists_lag_gt_of_attainedTop_of_logDense (hβ : 1 / 2 < β₀) (h : AttainedTop β₀)
    {N : Set ℕ} (hN : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ L : ℝ, X ≤ L → ∃ n ∈ N, |Real.log n - L| ≤ δ)
    (M : ℝ) : ∃ n ∈ N, M < integerLag n := by
  classical
  obtain ⟨⟨q₀, hq₀⟩, hmax⟩ := h
  have hW0 := lagWeightTotal_nonneg
  have hw0 : 0 < ‖lagWeight q₀‖ := by
    rw [norm_pos_iff]
    unfold lagWeight
    exact one_div_ne_zero (mul_ne_zero (xiZeroCopy_ne_zero q₀) (xiZeroCopy_one_sub_ne_zero q₀))
  have hwW : ‖lagWeight q₀‖ ≤ lagWeightTotal :=
    summable_norm_lagWeight.le_tsum q₀ fun q _ => norm_nonneg _
  have hWpos : 0 < lagWeightTotal := lt_of_lt_of_le hw0 hwW
  set m₁ : ℝ := ‖lagWeight q₀‖ ^ (2 : ℕ) / 2 with hm₁
  have hm₁pos : 0 < m₁ := by positivity
  set c₀ : ℝ := m₁ / (8 * lagWeightTotal) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  -- a finite set of copies containing `q₀` with small top tail
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Finset XiZeroCopy, ∀ F, F₀ ≤ F → topTail β₀ F ≤ c₀ / 8 := by
    have := (tendsto_order.1 (tendsto_topTail β₀)).2 (c₀ / 8) (by positivity)
    obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.mp this
    exact ⟨F₀, fun F hF => (hF₀ F hF).le⟩
  set F : Finset XiZeroCopy := insert q₀ F₀ with hF
  have hq₀F : q₀ ∈ F := Finset.mem_insert_self _ _
  have hFtail : topTail β₀ F ≤ c₀ / 8 := hF₀ F (Finset.subset_insert _ _)
  set w : XiZeroCopy → ℂ := lagTopCoeff β₀ with hw
  set γ : XiZeroCopy → ℝ := zeroOrdinate with hγ
  have hwq₀ : w q₀ = lagWeight q₀ := by rw [hw]; unfold lagTopCoeff; rw [if_pos hq₀]
  set W' : ℝ := ∑ q ∈ F, ‖w q‖ with hW'
  have hW'pos : 0 < W' := by
    have : ‖w q₀‖ ≤ W' := Finset.single_le_sum (fun q _ => norm_nonneg (w q)) hq₀F
    rw [hwq₀] at this
    linarith
  have hW'le : W' ≤ lagWeightTotal := by
    calc W' = ∑ q ∈ F, ‖w q‖ := rfl
      _ ≤ ∑ q ∈ F, ‖lagWeight q‖ := Finset.sum_le_sum fun q _ => norm_lagTopCoeff_le β₀ q
      _ ≤ lagWeightTotal := summable_norm_lagWeight.sum_le_tsum F fun q _ => norm_nonneg _
  set B : ℝ := ∑ q ∈ F, ‖w q‖ * (2 / |γ q|) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun q _ => by positivity
  set E : ℝ := ∑ q ∈ F, ∑ q' ∈ F, pairError w γ q q' with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun q' _ => pairError_nonneg w γ q q'
  set Λ : ℝ := ∑ q ∈ F, ‖w q‖ * |γ q| with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun q _ => by positivity
  set c : ℝ := m₁ / (8 * W') with hc
  have hcpos : 0 < c := by positivity
  have hc₀c : c₀ ≤ c := by
    rw [hc₀, hc]
    apply div_le_div_of_nonneg_left hm₁pos.le (by positivity)
    linarith
  -- the window length
  set ℓ : ℝ := max 1 (max (4 * W' * B / m₁) (4 * E / m₁)) with hℓ
  have hℓ1 : 1 ≤ ℓ := le_max_left _ _
  have hℓpos : 0 < ℓ := by linarith
  have hℓB : B ≤ m₁ / (4 * W') * ℓ := by
    have h1 : 4 * W' * B / m₁ ≤ ℓ := (le_max_left _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hm₁pos] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hℓE : E ≤ m₁ / 4 * ℓ := by
    have h1 : 4 * E / m₁ ≤ ℓ := (le_max_right _ _).trans (le_max_right _ _)
    rw [div_le_iff₀ hm₁pos] at h1
    linarith
  -- the Lipschitz radius and the density threshold
  set δ : ℝ := min 1 (c / (2 * (Λ + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδΛ : Λ * δ ≤ c / 2 := by
    have h1 : δ ≤ c / (2 * (Λ + 1)) := min_le_right _ _
    have h2 : Λ * δ ≤ Λ * (c / (2 * (Λ + 1))) := by gcongr
    have h3 : Λ * (c / (2 * (Λ + 1))) ≤ c / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨X, hX⟩ := hN δ hδpos
  -- the lower tail threshold
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → lowerTailReal β₀ L ≤ c / 16 := by
    have := (tendsto_order.1 (tendsto_lowerTailReal hmax)).2 (c / 16) (by positivity)
    obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp this
    exact ⟨L₀, fun L hL => (hL₀ L hL).le⟩
  -- the height threshold for `M`
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, ∀ L, A₁ ≤ L → M < c / 4 * Real.exp (L * (β₀ - 1 / 2)) := by
    refine ⟨Real.log (4 * (|M| + 1) / c) / (β₀ - 1 / 2), fun L hL => ?_⟩
    have hpos : 0 < 4 * (|M| + 1) / c := by positivity
    have h1 : Real.log (4 * (|M| + 1) / c) ≤ L * (β₀ - 1 / 2) := by
      rw [div_le_iff₀ (by linarith)] at hL
      linarith
    have h2 : 4 * (|M| + 1) / c ≤ Real.exp (L * (β₀ - 1 / 2)) := by
      rw [← Real.exp_log hpos]
      exact Real.exp_le_exp.mpr h1
    have h3 : 4 * (|M| + 1) ≤ c * Real.exp (L * (β₀ - 1 / 2)) := by
      rw [div_le_iff₀ hcpos] at h2; linarith
    linarith [le_abs_self M]
  -- the window start
  set A : ℝ := max (max L₀ X) (max 2 A₁) + 1 with hA
  have hAL₀ : L₀ + 1 ≤ A := by have := le_max_left L₀ X; have := le_max_left (max L₀ X) (max 2 A₁); linarith
  have hAX : X + 1 ≤ A := by have := le_max_right L₀ X; have := le_max_left (max L₀ X) (max 2 A₁); linarith
  have hA2 : 3 ≤ A := by have := le_max_left 2 A₁; have := le_max_right (max L₀ X) (max 2 A₁); linarith
  have hAA₁ : A₁ + 1 ≤ A := by have := le_max_right 2 A₁; have := le_max_right (max L₀ X) (max 2 A₁); linarith
  -- positivity extraction on the window `[A, A + ℓ]`
  set f : ℝ → ℝ := fun L => (trigSum F w γ L).re with hf
  have hfc : Continuous f := Complex.continuous_re.comp (continuous_trigSum F w γ)
  have hfW : ∀ x ∈ Icc A (A + ℓ), |f x| ≤ W' := fun x _ =>
    (Complex.abs_re_le_norm _).trans (norm_trigSum_le F w γ x)
  have hγne : ∀ q ∈ F, γ q ≠ 0 := fun q _ => zeroOrdinate_ne_zero' q
  have hmean : -(m₁ / (4 * W') * ℓ) ≤ ∫ x in A..A + ℓ, f x := by
    have h1 := norm_integral_trigSum_le F w γ hγne A ℓ
    have h2 : (∫ x in A..A + ℓ, f x) = (∫ x in A..A + ℓ, trigSum F w γ x).re := by
      have hint := (continuous_trigSum F w γ).intervalIntegrable (μ := MeasureTheory.volume) A (A + ℓ)
      have := Complex.reCLM.intervalIntegral_comp_comm hint
      simpa only [Complex.reCLM_apply] using this
    rw [h2]
    have h3 := Complex.abs_re_le_norm (∫ x in A..A + ℓ, trigSum F w γ x)
    have h4 := (abs_le.mp (h3.trans h1)).1
    linarith
  have hsq : 3 * m₁ / 4 * ℓ ≤ ∫ x in A..A + ℓ, f x ^ (2 : ℕ) := by
    have h1 := integral_re_trigSum_sq_ge F w γ (fun q _ q' _ => pairMain_lagTopCoeff_nonneg β₀ q q')
      (fun q _ => pairMain_lagTopCoeff_self β₀ q) A ℓ hℓpos.le
    have h2 : ‖w q₀‖ ^ (2 : ℕ) ≤ ∑ q ∈ F, ‖w q‖ ^ (2 : ℕ) :=
      Finset.single_le_sum (f := fun q => ‖w q‖ ^ (2 : ℕ)) (fun q _ => by positivity) hq₀F
    rw [hwq₀] at h2
    have h3 : m₁ * ℓ ≤ (∑ q ∈ F, ‖w q‖ ^ (2 : ℕ)) * ℓ / 2 := by
      rw [hm₁]
      have := mul_le_mul_of_nonneg_right h2 hℓpos.le
      linarith
    linarith
  obtain ⟨Lstar, hLstar, hfL⟩ := exists_ge_of_integral_bounds hℓpos hfc.continuousOn hfW hmean hsq hW'pos
    (by rw [show W' * (m₁ / (4 * W')) = m₁ / 4 by field_simp]; linarith)
  have hfLc : c ≤ f Lstar := by
    refine le_trans (le_of_eq ?_) hfL
    rw [hc, show W' * (m₁ / (4 * W')) = m₁ / 4 by field_simp]
    ring
  -- a point of `N` near `Lstar`
  obtain ⟨n, hnN, hn⟩ := hX Lstar (by linarith [hLstar.1])
  set L : ℝ := Real.log n with hL
  have hLA : A - 1 ≤ L := by
    have := (abs_le.mp hn).1
    linarith [hLstar.1]
  have hL0 : 0 ≤ L := by linarith
  -- the truncated sum is still large at `L`
  have hfLn : c / 2 ≤ f L := by
    have h1 := norm_trigSum_sub_le F w γ L Lstar
    have h2 : |f L - f Lstar| ≤ Λ * δ := by
      have := (Complex.abs_re_le_norm (trigSum F w γ L - trigSum F w γ Lstar)).trans h1
      rw [Complex.sub_re] at this
      calc |f L - f Lstar| ≤ Λ * |L - Lstar| := this
        _ ≤ Λ * δ := by gcongr
    have := (abs_le.mp h2).1
    linarith
  -- the decomposition at `L`
  have hdec := abs_scaledLag_sub_trigSum_le hmax F hL0
  have htail : lowerTailReal β₀ L ≤ c / 16 := hL₀ L (by linarith)
  have hlow := (abs_le.mp hdec).1
  have hscaled : c / 4 ≤ weilLagFunctionReal L * Real.exp (-(L * (β₀ - 1 / 2))) := by
    have : (trigSum F w γ L).re = f L := rfl
    linarith
  -- conclude
  refine ⟨n, hnN, ?_⟩
  have hM := hA₁ L (by linarith)
  have hexp : 0 < Real.exp (L * (β₀ - 1 / 2)) := Real.exp_pos _
  have hprod : Real.exp (-(L * (β₀ - 1 / 2))) * Real.exp (L * (β₀ - 1 / 2)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : c / 4 * Real.exp (L * (β₀ - 1 / 2)) ≤ weilLagFunctionReal L := by
    have := mul_le_mul_of_nonneg_right hscaled hexp.le
    rw [mul_assoc, hprod, mul_one] at this
    exact this
  unfold integerLag
  linarith

/-- **Bounded lags on a log-dense set force RH or a non-attained supremum of real parts.** -/
theorem riemannHypothesis_or_not_attained_of_logDense_bddAbove {N : Set ℕ}
    (hN : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ L : ℝ, X ≤ L → ∃ n ∈ N, |Real.log n - L| ≤ δ)
    {M : ℝ} (hM : ∀ n ∈ N, integerLag n ≤ M) :
    RiemannHypothesis ∨ ¬ ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  · right
    rintro ⟨β₀, hβ, h⟩
    obtain ⟨n, hn, hlt⟩ := exists_lag_gt_of_attainedTop_of_logDense hβ h hN M
    linarith [hM n hn]

end

end RHTower
