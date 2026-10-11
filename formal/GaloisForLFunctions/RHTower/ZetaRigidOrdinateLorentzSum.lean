import GaloisForLFunctions.RHTower.ZetaRigidOrdinateLocalRH
import GaloisForLFunctions.RHTower.MontgomeryZeroSumWindow
import GaloisForLFunctions.HTGeometry.WeightedPhaseSumSeparatedIncrements

/-!
# The Lorentzian zero sum of rigid ordinates is bounded

Montgomery's Lorentzian zero sum is
`S(x,t) = Σ_ρ x^{ρ−½}/(1 + (t + i(ρ−½))²)` (`lorentzZeroSumAll`). If the ordered ordinates are
`h`-rigid, then for some fixed `α ∈ (0, 1/8]` the sum `S(T^α, t)` is bounded uniformly in large `T`
and `t ∈ [T^{3/4}, T]` (`RigidOrdinates.exists_norm_lorentzZeroSumAll_le`).

**Proof.**
* *Block.* The zeros with `T^{1/2} < γ ≤ T²` lie on the line (`RigidOrdinates.re_eq_half`). They
  contribute `Σ w_n e^{iλγ_n}` with `λ = α log T` and `w_n = 1/(1 + (t − γ_n)²)`.
* *Increments.* The normalized gap bounds give increments `λ g_n ∈ [αc₁/2, 2αc₂] ⊂ [δ, π/2]`.
  Their variation is `O(1/log T)` because `|e^s − 1| ≤ 2|s|`.
* *Block bound.* The Lorentzian mass is `O(log T)`, so `norm_sum_lorentzWeight_phase_le` bounds
  the block by a constant.
* *Rest.* The remaining zeros sit at distance at least `T^{3/4}/2` from `t`. Their total mass is
  `O(log T / T^{3/4})`, which beats the amplitude factor `√x ≤ T^{1/16}`.
-/

open Complex Filter Topology Set Finset
open GaloisForLFunctions.HTGeometry (lorentzWeight lorentzWeight_nonneg lorentzWeight_le_one
  norm_sum_lorentzWeight_phase_le)

namespace RHTower

noncomputable section

/-- `lorentzMassW (√(1 + u²)) y ≤ (16/(1 + u)) (C + log(1 + u + |y| + 4))`. -/
theorem lorentzMassW_sqrt_le {u : ℝ} (hu : 0 ≤ u) (y : ℝ) :
    lorentzMassW (Real.sqrt (1 + u ^ 2)) y ≤
      16 / (1 + u) * (xiLineTwoLogDerivConstant + Real.log (1 + u + |y| + 4)) := by
  have hw : 1 ≤ Real.sqrt (1 + u ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith [sq_nonneg u]
  refine (lorentzMassW_le_log hw y).trans ?_
  have h1 := div_sqrt_one_add_sq_le u hu
  have hs := sqrt_one_add_sq_le u hu
  have h2 : Real.log (Real.sqrt (1 + u ^ 2) + |y| + 4) ≤ Real.log (1 + u + |y| + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hpos : 0 ≤ xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |y| + 4) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ Real.sqrt (1 + u ^ 2) + |y| + 4 by
      linarith [Real.sqrt_nonneg (1 + u ^ 2), abs_nonneg y])
    linarith
  calc 8 / Real.sqrt (1 + u ^ 2) *
        (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |y| + 4))
      ≤ 16 / (1 + u) * (xiLineTwoLogDerivConstant + Real.log (Real.sqrt (1 + u ^ 2) + |y| + 4)) :=
        mul_le_mul_of_nonneg_right h1 hpos
    _ ≤ 16 / (1 + u) * (xiLineTwoLogDerivConstant + Real.log (1 + u + |y| + 4)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- An on-line zero copy contributes `w e^{iγ log x}` to the Lorentzian zero sum. -/
theorem zeroSumTerm_of_eq_half_add {x t γ : ℝ} (hx : 0 < x) {q : XiZeroCopy}
    (hq : (q.1 : ℂ) = 1 / 2 + (γ : ℂ) * I) :
    zeroSumTerm x t q = (lorentzWeight t γ : ℂ) * cexp (I * ((Real.log x * γ : ℝ) : ℂ)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e1 : (q.1 : ℂ) - 1 / 2 = (γ : ℂ) * I := by rw [hq]; ring
  have e2 : (t : ℂ) + lorentzCentre (q.1 : ℂ) = ((t - γ : ℝ) : ℂ) := by
    rw [lorentzCentre, e1]; push_cast; linear_combination (γ : ℂ) * I_sq
  rw [zeroSumTerm, e1, cpow_def_of_ne_zero hx0, lorentzShift, e2, lorentzWeight,
    ← ofReal_log hx.le]
  push_cast
  rw [mul_comm]
  congr 2
  ring

/-- Counting by the ordered ordinates: `n < N(X)` iff `γ_n ≤ X`. -/
theorem lt_toNat_xiZeroCount_iff {n : ℕ} {X : ℝ} :
    n < (xiZeroCount X).toNat ↔ xiOrderedPositiveOrdinate n ≤ X := by
  rw [xiOrderedPositiveOrdinate_le_iff]
  have h0 := xiZeroCount_nonneg X
  omega

/-- An index whose ordinate exceeds `γ_{N₀}` is larger than `N₀`. -/
theorem lt_of_ordinate_lt {N₀ n : ℕ}
    (h : xiOrderedPositiveOrdinate N₀ < xiOrderedPositiveOrdinate n) : N₀ < n := by
  by_contra hle
  push Not at hle
  have := xiOrderedPositiveOrdinate_monotone hle
  linarith

/-- **The rest of the Lorentzian zero sum.** If every copy outside `s` lies at or below `B` or
above `T'`, its contribution is at most `16√x` times the two tail masses. -/
theorem norm_tsum_compl_zeroSumTerm_le {x t B T' : ℝ} (hx : 1 ≤ x) (s : Finset XiZeroCopy)
    (hs : ∀ q, q ∉ s → (q.1 : ℂ).im ≤ B ∨ T' < (q.1 : ℂ).im) (hBt : B ≤ t) (htT : t ≤ T') :
    ‖∑' q : ↑((s : Set XiZeroCopy)ᶜ), zeroSumTerm x t q‖ ≤
      16 * Real.sqrt x * (lorentzMassW (Real.sqrt (1 + (t - B) ^ 2)) B +
        lorentzMassW (Real.sqrt (1 + (T' - t) ^ 2)) T') := by
  classical
  set g : XiZeroCopy → ℝ := fun q => 16 * Real.sqrt x * lorentzMassTerm t q with hg
  have hgs : Summable g := (summable_lorentzMassTerm t).mul_left _
  have hnorm : Summable (fun q : ↑((s : Set XiZeroCopy)ᶜ) => ‖zeroSumTerm x t q‖) :=
    (summable_norm_zeroSumTerm hx t).subtype _
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  have h1 : ∑' q : ↑((s : Set XiZeroCopy)ᶜ), ‖zeroSumTerm x t q‖ ≤
      ∑' q : ↑((s : Set XiZeroCopy)ᶜ), g q :=
    Summable.tsum_le_tsum (fun q => norm_zeroSumTerm_le hx t q) hnorm (hgs.subtype _)
  refine h1.trans ?_
  rw [tsum_subtype ((s : Set XiZeroCopy)ᶜ) g]
  have hlow := tsum_indicator_le_le_lorentzMassW (t := t) hBt
  have hhigh := tsum_indicator_gt_le_lorentzMassW (t := t) htT
  have hpt : ∀ q, ((s : Set XiZeroCopy)ᶜ).indicator g q ≤
      16 * Real.sqrt x * ({q : XiZeroCopy | (q.1 : ℂ).im ≤ B}.indicator (lorentzMassTerm t) q +
        {q : XiZeroCopy | T' < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q) := by
    intro q
    have hm := lorentzMassTerm_nonneg t q
    unfold Set.indicator
    by_cases hq : q ∈ ((s : Set XiZeroCopy)ᶜ)
    · rw [if_pos hq]
      rcases hs q (by simpa using hq) with hlo | hhi
      · rw [if_pos (show q ∈ {q : XiZeroCopy | (q.1 : ℂ).im ≤ B} from hlo)]
        split_ifs <;> simp only [hg] <;> nlinarith [Real.sqrt_nonneg x]
      · rw [if_pos (show q ∈ {q : XiZeroCopy | T' < (q.1 : ℂ).im} from hhi)]
        split_ifs <;> simp only [hg] <;> nlinarith [Real.sqrt_nonneg x]
    · rw [if_neg hq]
      split_ifs <;> nlinarith [Real.sqrt_nonneg x]
  have hsum1 := (summable_lorentzMassTerm t).indicator {q : XiZeroCopy | (q.1 : ℂ).im ≤ B}
  have hsum2 := (summable_lorentzMassTerm t).indicator {q : XiZeroCopy | T' < (q.1 : ℂ).im}
  calc ∑' q, ((s : Set XiZeroCopy)ᶜ).indicator g q
      ≤ ∑' q, 16 * Real.sqrt x *
          ({q : XiZeroCopy | (q.1 : ℂ).im ≤ B}.indicator (lorentzMassTerm t) q +
            {q : XiZeroCopy | T' < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q) :=
        Summable.tsum_le_tsum hpt (hgs.indicator _) ((hsum1.add hsum2).mul_left _)
    _ = 16 * Real.sqrt x *
          (∑' q, {q : XiZeroCopy | (q.1 : ℂ).im ≤ B}.indicator (lorentzMassTerm t) q +
            ∑' q, {q : XiZeroCopy | T' < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) q) := by
        rw [tsum_mul_left, hsum1.tsum_add hsum2]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith


/-- The two tail masses seen from `t ∈ [T^{3/4}, T]`, with cut heights `T^{1/2}` and `T²`. -/
theorem tailMasses_le {T t : ℝ} (hT : 16 ≤ T) (ht1 : T ^ (3 / 4 : ℝ) ≤ t) (ht2 : t ≤ T) :
    lorentzMassW (Real.sqrt (1 + (t - T ^ (1 / 2 : ℝ)) ^ 2)) (T ^ (1 / 2 : ℝ)) +
        lorentzMassW (Real.sqrt (1 + (T ^ 2 - t) ^ 2)) (T ^ 2) ≤
      64 * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) / T ^ (3 / 4 : ℝ) := by
  have hT0 : 0 < T := by linarith
  set B := T ^ (1 / 2 : ℝ) with hB
  set Q := T ^ (3 / 4 : ℝ) with hQ
  have hB0 : 0 ≤ B := Real.rpow_nonneg hT0.le _
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hT0 _
  -- `Q = B · T^{1/4}` and `T^{1/4} ≥ 2`
  have h14 : (2 : ℝ) ≤ T ^ (1 / 4 : ℝ) := by
    have : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [← this]; exact Real.rpow_le_rpow (by norm_num) hT (by norm_num)
  have hQB : Q = B * T ^ (1 / 4 : ℝ) := by
    rw [hQ, hB, ← Real.rpow_add hT0]; norm_num
  have hQ2B : 2 * B ≤ Q := by rw [hQB]; nlinarith
  have hQT : Q ≤ T := by
    rw [hQ]; exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have hBt : B ≤ t := by linarith
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hlogpos : 0 ≤ Real.log (2 * T ^ 2 + 5) := Real.log_nonneg (by nlinarith)
  have hK0 : 0 ≤ xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5) := by linarith
  -- low tail
  have hlow := lorentzMassW_sqrt_le (u := t - B) (by linarith) B
  rw [abs_of_nonneg hB0] at hlow
  have hl1 : Real.log (1 + (t - B) + B + 4) ≤ Real.log (2 * T ^ 2 + 5) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hl2 : 16 / (1 + (t - B)) ≤ 32 / Q := by
    rw [div_le_div_iff₀ (by linarith) hQ0]; nlinarith
  have hlow' : lorentzMassW (Real.sqrt (1 + (t - B) ^ 2)) B ≤
      32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) := by
    refine hlow.trans ?_
    calc 16 / (1 + (t - B)) * (xiLineTwoLogDerivConstant + Real.log (1 + (t - B) + B + 4))
        ≤ 16 / (1 + (t - B)) * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) :=
          mul_le_mul_of_nonneg_right hl2 hK0
  -- high tail
  have hhigh := lorentzMassW_sqrt_le (u := T ^ 2 - t) (by nlinarith) (T ^ 2)
  rw [abs_of_nonneg (by positivity)] at hhigh
  have hh1 : Real.log (1 + (T ^ 2 - t) + T ^ 2 + 4) ≤ Real.log (2 * T ^ 2 + 5) :=
    Real.log_le_log (by nlinarith) (by linarith)
  have hh2 : 16 / (1 + (T ^ 2 - t)) ≤ 32 / Q := by
    rw [div_le_div_iff₀ (by nlinarith) hQ0]; nlinarith
  have hhigh' : lorentzMassW (Real.sqrt (1 + (T ^ 2 - t) ^ 2)) (T ^ 2) ≤
      32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) := by
    refine hhigh.trans ?_
    calc 16 / (1 + (T ^ 2 - t)) *
          (xiLineTwoLogDerivConstant + Real.log (1 + (T ^ 2 - t) + T ^ 2 + 4))
        ≤ 16 / (1 + (T ^ 2 - t)) * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by
            have : 0 < 1 + (T ^ 2 - t) := by nlinarith
            positivity)
      _ ≤ 32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) :=
          mul_le_mul_of_nonneg_right hh2 hK0
  have e : 64 * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) / Q =
      32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) +
        32 / Q * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) := by
    field_simp; ring
  rw [e]
  linarith

/-- The tail factor `1024 T^{α/2}(C + log(2T² + 5))` is eventually at most `T^{3/4}`. -/
theorem eventually_tailFactor_le {α : ℝ} (hα0 : 0 < α) (hα8 : α ≤ 1 / 8) :
    ∀ᶠ T : ℝ in atTop, 1024 * Real.sqrt (T ^ α) *
      (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) ≤ T ^ (3 / 4 : ℝ) := by
  have hC := xiLineTwoLogDerivConstant_nonneg
  have e1 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).eventually_ge_atTop
    (xiLineTwoLogDerivConstant + 2)
  have e2 := (tendsto_rpow_atTop (show (0 : ℝ) < 9 / 16 by norm_num)).eventually_ge_atTop
    (17408 : ℝ)
  filter_upwards [e1, e2, eventually_ge_atTop (3 : ℝ)] with T h1 h2 hT3
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  -- `√(T^α) ≤ T^{1/16}`
  have hs : Real.sqrt (T ^ α) ≤ T ^ (1 / 16 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  -- `log(2T² + 5) ≤ 2 + 16 T^{1/8}`
  have hlogT : Real.log T ≤ 8 * T ^ (1 / 8 : ℝ) := by
    have := Real.log_le_rpow_div hT0.le (show (0 : ℝ) < 1 / 8 by norm_num)
    linarith [show T ^ (1 / 8 : ℝ) / (1 / 8) = 8 * T ^ (1 / 8 : ℝ) by ring]
  have hlog3 : Real.log (2 * T ^ 2 + 5) ≤ 2 + 2 * Real.log T := by
    have h3 : Real.log (2 * T ^ 2 + 5) ≤ Real.log (3 * T ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h3
    have : Real.log 3 < 2 := by
      have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
      linarith
    push_cast at h3
    linarith
  have hK : xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5) ≤ 17 * T ^ (1 / 8 : ℝ) := by
    linarith
  have hsplit : T ^ (3 / 4 : ℝ) = T ^ (1 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (9 / 16 : ℝ) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; norm_num
  have hp1 : 0 ≤ T ^ (1 / 16 : ℝ) := Real.rpow_nonneg hT0.le _
  have hp2 : 0 ≤ T ^ (1 / 8 : ℝ) := Real.rpow_nonneg hT0.le _
  have hKnn : 0 ≤ xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * T ^ 2 + 5 by nlinarith); linarith
  rw [hsplit]
  calc 1024 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5))
      ≤ 1024 * T ^ (1 / 16 : ℝ) * (17 * T ^ (1 / 8 : ℝ)) := by
        gcongr
    _ = T ^ (1 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * 17408 := by ring
    _ ≤ T ^ (1 / 16 : ℝ) * T ^ (1 / 8 : ℝ) * T ^ (9 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)


/-- The ordered copies with indices in a finite set carry at most the Lorentzian mass. -/
theorem sum_lorentzWeight_orderedOrdinate_le (t : ℝ) (a m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) ≤
      lorentzMass t := by
  classical
  have hinj : Set.InjOn (fun i => xiOrderedPositiveZeroCopy (a + i)) (Finset.range (m + 1)) :=
    fun i _ j _ hij => by
      have := xiOrderedPositiveZeroCopy_injective hij
      omega
  have heq : ∑ i ∈ Finset.range (m + 1), lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) =
      ∑ q ∈ (Finset.range (m + 1)).image (fun i => xiOrderedPositiveZeroCopy (a + i)),
        lorentzMassTerm t q := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lorentzMassTerm, xiOrderedPositiveZeroCopy_im_eq, lorentzWeight]
  rw [heq]
  exact (summable_lorentzMassTerm t).sum_le_tsum _ fun q _ => lorentzMassTerm_nonneg t q

/-- Increments of normalized gaps lie in `[δ, 2π − δ]`. -/
theorem increment_mem_of_gap_bounds {α L c₁ c₂ δ g : ℝ} (hα : 0 < α) (hL : 0 < L)
    (hδc : δ ≤ α * c₁ / 2) (hαc : α * c₂ ≤ Real.pi / 4) (hδ2 : δ ≤ Real.pi / 2)
    (hg1 : c₁ / (2 * L) ≤ g) (hg2 : g ≤ 2 * c₂ / L) :
    δ ≤ α * L * g ∧ α * L * g ≤ 2 * Real.pi - δ := by
  have hαL : 0 ≤ α * L := by positivity
  constructor
  · calc δ ≤ α * c₁ / 2 := hδc
      _ = α * L * (c₁ / (2 * L)) := by field_simp
      _ ≤ α * L * g := mul_le_mul_of_nonneg_left hg1 hαL
  · calc α * L * g ≤ α * L * (2 * c₂ / L) := mul_le_mul_of_nonneg_left hg2 hαL
      _ = 2 * (α * c₂) := by field_simp
      _ ≤ 2 * Real.pi - δ := by linarith [Real.pi_pos]

/-- Variation of rigid normalized gaps: `αL|g' − g| ≤ 16αc₂²/(hL)`. -/
theorem increment_variation_le {α L c₂ h g g' : ℝ} (hα : 0 < α) (hL : 0 < L) (hh : 0 < h)
    (hc₂ : 0 < c₂) (hLc : 4 * c₂ / h ≤ L) (hg : 0 ≤ g) (hg' : 0 ≤ g')
    (hg2 : g ≤ 2 * c₂ / L) (hg2' : g' ≤ 2 * c₂ / L)
    (hup : g' ≤ g * Real.exp ((g + g') / h)) (hdown : g ≤ g' * Real.exp ((g + g') / h)) :
    α * L * |g' - g| ≤ 16 * α * c₂ ^ 2 / (h * L) := by
  set sv := (g + g') / h with hsv
  have hs0 : 0 ≤ sv := by positivity
  have hsum : g + g' ≤ 4 * c₂ / L := by
    have := add_le_add hg2 hg2'
    calc g + g' ≤ 2 * c₂ / L + 2 * c₂ / L := this
      _ = 4 * c₂ / L := by ring
  have hs1 : sv ≤ 4 * c₂ / (h * L) := by
    rw [hsv, div_le_div_iff₀ hh (by positivity)]
    calc (g + g') * (h * L) = h * ((g + g') * L) := by ring
      _ ≤ h * (4 * c₂) := by
          refine mul_le_mul_of_nonneg_left ?_ hh.le
          rw [le_div_iff₀ hL] at hsum; exact hsum
      _ = 4 * c₂ * h := by ring
  have hs1' : sv ≤ 1 := by
    refine hs1.trans ?_
    rw [div_le_one (by positivity)]
    rw [div_le_iff₀ hh] at hLc
    linarith
  have hexp := Real.abs_exp_sub_one_le (x := sv) (by rw [abs_of_nonneg hs0]; exact hs1')
  rw [abs_of_nonneg hs0] at hexp
  have hexp' : Real.exp sv - 1 ≤ 2 * sv := (le_abs_self _).trans hexp
  have e1 : g * (Real.exp sv - 1) = g * Real.exp sv - g := by ring
  have e2 : g' * (Real.exp sv - 1) = g' * Real.exp sv - g' := by ring
  have f1 : g * (Real.exp sv - 1) ≤ g * (2 * sv) := mul_le_mul_of_nonneg_left hexp' hg
  have f2 : g * (2 * sv) ≤ 2 * c₂ / L * (2 * sv) := mul_le_mul_of_nonneg_right hg2 (by positivity)
  have f3 : g' * (Real.exp sv - 1) ≤ g' * (2 * sv) := mul_le_mul_of_nonneg_left hexp' hg'
  have f4 : g' * (2 * sv) ≤ 2 * c₂ / L * (2 * sv) :=
    mul_le_mul_of_nonneg_right hg2' (by positivity)
  have hd1 : g' - g ≤ 2 * c₂ / L * (2 * sv) := by linarith
  have hd2 : g - g' ≤ 2 * c₂ / L * (2 * sv) := by linarith
  have hd : |g' - g| ≤ 2 * c₂ / L * (2 * (4 * c₂ / (h * L))) := by
    rw [abs_le]
    have h3 : 2 * c₂ / L * (2 * sv) ≤ 2 * c₂ / L * (2 * (4 * c₂ / (h * L))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    constructor <;> linarith
  calc α * L * |g' - g| ≤ α * L * (2 * c₂ / L * (2 * (4 * c₂ / (h * L)))) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 16 * α * c₂ ^ 2 / (h * L) := by field_simp; ring

/-- **The block of rigid on-line zeros.** If the zeros with indices `a, …, a + m` are on-line
copies with normalized gaps in `[c₁/(2L), 2c₂/L]`, their Lorentzian phase sum at `x = e^{αL}` is
bounded by `1 + 8/σ + 512αc₂²/(hσ²)`. -/
theorem RigidOrdinates.norm_block_le {h : ℝ} (hh : 0 < h) {N₀ : ℕ} (H : RigidOrdinates h N₀)
    {α L c₁ c₂ δ x t : ℝ} (hα : 0 < α) (hL : 0 < L) (hc₂ : 0 < c₂) (hLc : 4 * c₂ / h ≤ L)
    (hδ0 : 0 < δ) (hδc : δ ≤ α * c₁ / 2) (hαc : α * c₂ ≤ Real.pi / 4) (hδ2 : δ ≤ Real.pi / 2)
    (hx : 0 < x) (hlogx : Real.log x = α * L) (a m : ℕ)
    (hgap : ∀ n, a ≤ n → n ≤ a + m →
      N₀ < n ∧ c₁ / (2 * L) ≤ ordinateGap n ∧ ordinateGap n ≤ 2 * c₂ / L)
    (hmass : ∑ i ∈ Finset.range (m + 1), lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) ≤
      16 * L) :
    ‖∑ i ∈ Finset.range (m + 1), zeroSumTerm x t (xiOrderedPositiveZeroCopy (a + i))‖ ≤
      1 + 8 / (2 * Real.sin (δ / 2)) + 512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by
  have hδπ : δ ≤ Real.pi := hδ2.trans (by linarith [Real.pi_pos])
  have hterm : ∀ i ∈ Finset.range (m + 1), zeroSumTerm x t (xiOrderedPositiveZeroCopy (a + i)) =
      (lorentzWeight t (xiOrderedPositiveOrdinate (a + i)) : ℂ) *
        cexp (I * ((Real.log x * xiOrderedPositiveOrdinate (a + i) : ℝ) : ℂ)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact zeroSumTerm_of_eq_half_add hx
      (H.orderedPositiveZeroCopy_eq (hgap (a + i) (by omega) (by omega)).1)
  rw [Finset.sum_congr rfl hterm]
  have hu : Monotone (fun i => xiOrderedPositiveOrdinate (a + i)) := fun i j hij =>
    xiOrderedPositiveOrdinate_monotone (by omega)
  have hθ : ∀ k < m, δ ≤ Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
      xiOrderedPositiveOrdinate (a + k)) ∧ Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
      xiOrderedPositiveOrdinate (a + k)) ≤ 2 * Real.pi - δ := by
    intro k hk
    obtain ⟨-, hg1, hg2⟩ := hgap (a + k) (by omega) (by omega)
    have e : xiOrderedPositiveOrdinate (a + (k + 1)) - xiOrderedPositiveOrdinate (a + k) =
        ordinateGap (a + k) := by rw [ordinateGap, show a + (k + 1) = a + k + 1 by ring]
    rw [e, hlogx]
    exact increment_mem_of_gap_bounds hα hL hδc hαc hδ2 hg1 hg2
  have hηb : ∀ k, k + 1 < m →
      |Real.log x * (xiOrderedPositiveOrdinate (a + (k + 2)) -
          xiOrderedPositiveOrdinate (a + (k + 1))) -
        Real.log x * (xiOrderedPositiveOrdinate (a + (k + 1)) -
          xiOrderedPositiveOrdinate (a + k))| ≤ 16 * α * c₂ ^ 2 / (h * L) := by
    intro k hk
    obtain ⟨hN0, -, hg0⟩ := hgap (a + k) (by omega) (by omega)
    obtain ⟨-, -, hg1⟩ := hgap (a + k + 1) (by omega) (by omega)
    have e0 : xiOrderedPositiveOrdinate (a + (k + 1)) - xiOrderedPositiveOrdinate (a + k) =
        ordinateGap (a + k) := by rw [ordinateGap, show a + (k + 1) = a + k + 1 by ring]
    have e1 : xiOrderedPositiveOrdinate (a + (k + 2)) - xiOrderedPositiveOrdinate (a + (k + 1)) =
        ordinateGap (a + k + 1) := by
      rw [ordinateGap, show a + (k + 2) = a + k + 1 + 1 by ring,
        show a + (k + 1) = a + k + 1 by ring]
    rw [e0, e1, hlogx, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
    exact increment_variation_le hα hL hh hc₂ hLc (ordinateGap_nonneg _) (ordinateGap_nonneg _)
      hg0 hg1 (H.up (a + k) hN0.le) (H.down (a + k) hN0.le)
  have hmain := norm_sum_lorentzWeight_phase_le hδ0 hδπ (t := t) (lam := Real.log x)
    (η := 16 * α * c₂ ^ 2 / (h * L)) (M := 16 * L) hu m hθ hηb (by positivity) hmass
  refine hmain.trans (le_of_eq ?_)
  field_simp
  ring


/-- Block membership: `n ∈ [N(B), N(T²))` iff `B < γ_n ≤ T²`. -/
theorem mem_Ico_toNat_iff {B T' : ℝ} (n : ℕ) :
    n ∈ Finset.Ico (xiZeroCount B).toNat (xiZeroCount T').toNat ↔
      B < xiOrderedPositiveOrdinate n ∧ xiOrderedPositiveOrdinate n ≤ T' := by
  rw [Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, lt_toNat_xiZeroCount_iff.mp h2⟩
    by_contra hle; push Not at hle
    have := lt_toNat_xiZeroCount_iff.mpr hle
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨?_, lt_toNat_xiZeroCount_iff.mpr h2⟩
    by_contra hlt; push Not at hlt
    have := lt_toNat_xiZeroCount_iff.mp hlt
    linarith

/-- Gap facts for block indices: an index with `T^{1/2} < γ_n ≤ T²` exceeds `N₀` and its gap
lies in `[c₁/(2L), 2c₂/L]`. -/
theorem block_gap_facts {N₀ : ℕ} {T₂ T₃ c₁ c₂ T L : ℝ} (hT0 : 0 < T) (hL : L = Real.log T)
    (hU : ∀ n, N₀ ≤ n → T₂ ≤ xiOrderedPositiveOrdinate n →
      ordinateGap n * Real.log (xiOrderedPositiveOrdinate n) ≤ c₂)
    (hLo : ∀ n, N₀ ≤ n → T₃ ≤ xiOrderedPositiveOrdinate n →
      c₁ ≤ ordinateGap n * Real.log (xiOrderedPositiveOrdinate n))
    (hB : max (max T₂ T₃) (xiOrderedPositiveOrdinate N₀ + 1) ≤ T ^ (1 / 2 : ℝ))
    (hL0 : 0 < L) {n : ℕ} (hn1 : T ^ (1 / 2 : ℝ) < xiOrderedPositiveOrdinate n)
    (hn2 : xiOrderedPositiveOrdinate n ≤ T ^ 2) :
    N₀ < n ∧ c₁ / (2 * L) ≤ ordinateGap n ∧ ordinateGap n ≤ 2 * c₂ / L := by
  set γ := xiOrderedPositiveOrdinate
  have hBh0 : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hBT₂ : T₂ ≤ T ^ (1 / 2 : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBT₃ : T₃ ≤ T ^ (1 / 2 : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBN : γ N₀ + 1 ≤ T ^ (1 / 2 : ℝ) := le_trans (le_max_right _ _) hB
  have hnN : N₀ < n := lt_of_ordinate_lt (by linarith)
  have hγ0 : 0 < γ n := by linarith
  have hl1 : L / 2 ≤ Real.log (γ n) := by
    have := Real.log_le_log hBh0 hn1.le
    rw [Real.log_rpow hT0, ← hL] at this; linarith
  have hl2 : Real.log (γ n) ≤ 2 * L := by
    have := Real.log_le_log hγ0 hn2
    rw [Real.log_pow, ← hL] at this; push_cast at this; linarith
  have hu := hU n hnN.le (by linarith)
  have hlo := hLo n hnN.le (by linarith)
  have hg0 := ordinateGap_nonneg n
  refine ⟨hnN, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    calc c₁ ≤ ordinateGap n * Real.log (γ n) := hlo
      _ ≤ ordinateGap n * (2 * L) := mul_le_mul_of_nonneg_left hl2 hg0
  · rw [le_div_iff₀ hL0]
    have hlpos : 0 < Real.log (γ n) := by linarith
    have : ordinateGap n * (L / 2) ≤ c₂ :=
      le_trans (mul_le_mul_of_nonneg_left hl1 hg0) hu
    linarith

/-- **The Lorentzian zero sum of rigid ordinates is bounded.** For some `α ∈ (0, 1/8]` and `C`,
eventually `‖S(T^α, t)‖ ≤ C` for all `t ∈ [T^{3/4}, T]`. -/
theorem RigidOrdinates.exists_norm_lorentzZeroSumAll_le {h : ℝ} (hh : 0 < h) {N₀ : ℕ}
    (H : RigidOrdinates h N₀) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 / 8 ∧ ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, ∀ t ∈ Icc (T ^ (3 / 4 : ℝ)) T,
      ‖lorentzZeroSumAll (T ^ α) t‖ ≤ C := by
  classical
  obtain ⟨c₂, hc₂, T₂, hU⟩ := H.exists_gap_mul_log_le hh
  obtain ⟨c₁, hc₁, T₃, hLo⟩ := H.exists_le_gap_mul_log hh
  set α : ℝ := min (Real.pi / (4 * c₂)) (1 / 8) with hαdef
  have hα0 : 0 < α := lt_min (by positivity) (by norm_num)
  have hα8 : α ≤ 1 / 8 := min_le_right _ _
  have hαc : α * c₂ ≤ Real.pi / 4 := by
    have := min_le_left (Real.pi / (4 * c₂)) (1 / 8)
    rw [← hαdef] at this
    calc α * c₂ ≤ Real.pi / (4 * c₂) * c₂ := mul_le_mul_of_nonneg_right this hc₂.le
      _ = Real.pi / 4 := by field_simp
  set δ : ℝ := min (α * c₁ / 2) (Real.pi / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ2 : δ ≤ Real.pi / 2 := min_le_right _ _
  have hδc : δ ≤ α * c₁ / 2 := min_le_left _ _
  set Cb : ℝ := 1 + 8 / (2 * Real.sin (δ / 2)) +
    512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) with hCb
  have hσ0 : 0 < 2 * Real.sin (δ / 2) :=
    GaloisForLFunctions.HTGeometry.two_sin_half_pos hδ0 (hδ2.trans (by linarith [Real.pi_pos]))
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ 8 / (2 * Real.sin (δ / 2)) +
        512 * α * c₂ ^ 2 / (h * (2 * Real.sin (δ / 2)) ^ 2) := by positivity
    linarith
  refine ⟨α, hα0, hα8, Cb + 1, ?_⟩
  have eB := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_ge_atTop
    (max (max T₂ T₃) (xiOrderedPositiveOrdinate N₀ + 1))
  have eL := Real.tendsto_log_atTop.eventually_ge_atTop
    (max (4 * c₂ / h) (2 * (xiLineTwoLogDerivConstant + 2)))
  filter_upwards [eB, eL, eventually_tailFactor_le hα0 hα8, eventually_ge_atTop (16 : ℝ)]
    with T hB hlogT hF hT16
  intro t ht
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL1 : 4 * c₂ / h ≤ L := le_trans (le_max_left _ _) hlogT
  have hL2 : 2 * (xiLineTwoLogDerivConstant + 2) ≤ L := le_trans (le_max_right _ _) hlogT
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hL0 : 0 < L := by linarith
  have hx1 : 1 ≤ T ^ α := Real.one_le_rpow (by linarith) hα0.le
  have hlogx : Real.log (T ^ α) = α * L := Real.log_rpow hT0 α
  set a := (xiZeroCount (T ^ (1 / 2 : ℝ))).toNat with ha
  set b := (xiZeroCount (T ^ 2)).toNat with hb
  set s := (Finset.Ico a b).image xiOrderedPositiveZeroCopy with hs_def
  -- the block
  have hblockS : ‖∑ q ∈ s, zeroSumTerm (T ^ α) t q‖ ≤ Cb := by
    rw [hs_def, Finset.sum_image xiOrderedPositiveZeroCopy_injective.injOn]
    rcases le_or_gt b a with hba | hab
    · rw [Finset.Ico_eq_empty_of_le hba, Finset.sum_empty, norm_zero]; linarith
    have hbm : b - a = (b - a - 1) + 1 := by omega
    rw [Finset.sum_Ico_eq_sum_range, hbm]
    refine H.norm_block_le hh hα0 hL0 hc₂ hL1 hδ0 hδc hαc hδ2 (by positivity) hlogx a
      (b - a - 1) (fun n hn1 hn2 => ?_) ?_
    · have hin := (mem_Ico_toNat_iff (B := T ^ (1 / 2 : ℝ)) (T' := T ^ 2) n).mp
        (Finset.mem_Ico.mpr ⟨hn1, by omega⟩)
      exact block_gap_facts hT0 hLdef hU hLo hB hL0 hin.1 hin.2
    · refine (sum_lorentzWeight_orderedOrdinate_le t a _).trans ?_
      refine (lorentzMass_le_log t).trans ?_
      have ht0 : 0 ≤ t := le_trans (Real.rpow_nonneg hT0.le _) ht.1
      rw [abs_of_nonneg ht0]
      have h4 : Real.log (t + 4) ≤ 1 + L := by
        have h5 : Real.log (t + 4) ≤ Real.log (2 * T) :=
          Real.log_le_log (by linarith) (by linarith [ht.2])
        rw [Real.log_mul (by norm_num) hT0.ne'] at h5
        have := Real.log_two_lt_d9; linarith
      linarith
  -- the rest
  have hs : ∀ q, q ∉ s → (q.1 : ℂ).im ≤ T ^ (1 / 2 : ℝ) ∨ T ^ 2 < (q.1 : ℂ).im := by
    intro q hq
    by_contra hcon
    push Not at hcon
    obtain ⟨hlo, hhi⟩ := hcon
    have hBpos : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
    obtain ⟨n, hn⟩ := exists_xiOrderedPositiveZeroCopy_eq (q := q) (by linarith)
    have hγn : xiOrderedPositiveOrdinate n = (q.1 : ℂ).im := by
      rw [← hn, xiOrderedPositiveZeroCopy_im_eq]
    apply hq
    rw [hs_def, Finset.mem_image]
    exact ⟨n, (mem_Ico_toNat_iff (B := T ^ (1 / 2 : ℝ)) (T' := T ^ 2) n).mpr
      ⟨by rw [hγn]; exact hlo, by rw [hγn]; exact hhi⟩, hn⟩
  have hBt : T ^ (1 / 2 : ℝ) ≤ t :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) ht.1
  have hrest := norm_tsum_compl_zeroSumTerm_le hx1 s hs hBt (show t ≤ T ^ 2 by nlinarith [ht.2])
  have htails := tailMasses_le hT16 ht.1 ht.2
  have hQ0 : 0 < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hrest1 : ‖∑' q : ↑((s : Set XiZeroCopy)ᶜ), zeroSumTerm (T ^ α) t q‖ ≤ 1 := by
    refine hrest.trans ?_
    calc 16 * Real.sqrt (T ^ α) * (lorentzMassW (Real.sqrt (1 + (t - T ^ (1 / 2 : ℝ)) ^ 2))
          (T ^ (1 / 2 : ℝ)) + lorentzMassW (Real.sqrt (1 + (T ^ 2 - t) ^ 2)) (T ^ 2))
        ≤ 16 * Real.sqrt (T ^ α) *
          (64 * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5)) / T ^ (3 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left htails (by positivity)
      _ = (1024 * Real.sqrt (T ^ α) * (xiLineTwoLogDerivConstant + Real.log (2 * T ^ 2 + 5))) /
            T ^ (3 / 4 : ℝ) := by ring
      _ ≤ 1 := by rw [div_le_one hQ0]; exact hF
  rw [lorentzZeroSumAll, ← (summable_zeroSumTerm hx1 t).sum_add_tsum_compl (s := s)]
  refine (norm_add_le _ _).trans ?_
  linarith

end

end RHTower
