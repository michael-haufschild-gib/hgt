import GaloisForLFunctions.RHTower.JointAncestryBudgetZeroFreeLaw
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.GaussianCentralGapZeroFreeRegionBudget

/-!
# The unconditional JAS producer at logarithmic budget

**Theorem** (`exists_jasProductPositive_logBudget`).  For every `0 ≤ A < 1` there is `Y` such
that the JAS product tests at any level `σ` are positive on every finite set of primes `p > y`,
`y ≥ Y`, whose prime budget satisfies `Σ_P p^{−(σ−½)} ≤ (log y)^A`.

Proof.  By the explicit zero-free region `Re ρ ≤ 1 − 1/(100 log |Im ρ|)` for `|Im ρ| ≥ 4`
(`xiZeroCopy_zero_free_from_four`) and finiteness below height `4`, every zero up to height
`T = exp((log y)^{β})`, `β = (A+1)/2`, sees `Σ_P p^{−(σ−|Re ρ−½|)} ≤ y^{−1/(100(log y)^β)}(log y)^A`,
which tends to `0`.  The zeros above `T` see at most `(log y)^A`, and their weight is
`O(log T / T) = O((log y)^β e^{−(log y)^β})`, which beats `e^{(log y)^A}`.  The hypothesis-free
zero-sum bound `jasProductAggregate_re_ge_exp` closes.

With the budget law (`R:JointAncestryBudgetZeroFreeLaw`), the unconditional JAS producer reaches
budget `(log y)^{1−ε}`.  A producer at budget `y^λ` for some `λ > 0` would be quasi-RH.
-/

open Filter

namespace RHTower

noncomputable section

/-! ## Zero widths -/

theorem exists_low_zero_width_at (H : ℝ) : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ H →
    |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - η₀ := by
  obtain ⟨K, hK⟩ : ∃ K : Set ℂ, K = Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-H) H := ⟨_, rfl⟩
  have hKc : IsCompact K := by rw [hK]; exact isCompact_Icc.reProdIm isCompact_Icc
  have hfin := finite_xiZeroSet_inter hKc
  have hmemK : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ H →
      (q.1 : ℂ) ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    intro q hq
    refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨(xiZeroCopy_re_pos q).le, (xiZeroCopy_re_lt_one q).le⟩, abs_le.mp hq⟩
  by_cases hne : (xiZeroSet_weilLagFunctionCriterion ∩ K).Nonempty
  · obtain ⟨ρ₀, hρ₀, hmax⟩ := Set.exists_max_image _ (fun ρ : ℂ => |ρ.re - 1 / 2|) hfin hne
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀.1
    have h0 := xiZeroCopy_re_pos q₀
    have h1 := xiZeroCopy_re_lt_one q₀
    rw [hq₀] at h0 h1
    have hlt : |ρ₀.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    refine ⟨1 / 2 - |ρ₀.re - 1 / 2|, by linarith, fun q hq => ?_⟩
    have := hmax _ (hmemK q hq)
    linarith
  · refine ⟨1 / 2, by norm_num, fun q hq => ?_⟩
    exact absurd ⟨_, hmemK q hq⟩ hne

theorem exists_low_zero_width : ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ 4 →
    |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - η₀ :=
  exists_low_zero_width_at 4

/-- **Explicit zero-free region on both sides.**  For `|Im ρ| ≥ 4`,
`|Re ρ − ½| ≤ ½ − 1/(100 log |Im ρ|)`. -/
theorem abs_re_sub_half_le_of_four_le (q : XiZeroCopy) (hq : 4 ≤ |(q.1 : ℂ).im|) :
    |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - 1 / 100 / Real.log |(q.1 : ℂ).im| := by
  have hup : ∀ q : XiZeroCopy, 4 ≤ |(q.1 : ℂ).im| →
      (q.1 : ℂ).re ≤ 1 - 1 / 100 / Real.log |(q.1 : ℂ).im| := by
    intro q hq
    rcases le_or_gt 0 (q.1 : ℂ).im with h | h
    · rw [abs_of_nonneg h] at hq ⊢; exact xiZeroCopy_zero_free_from_four hq
    · obtain ⟨q', hq'⟩ := exists_xiZeroCopy_conj q
      have him : (q'.1 : ℂ).im = -(q.1 : ℂ).im := by rw [hq']; simp
      have hre : (q'.1 : ℂ).re = (q.1 : ℂ).re := by rw [hq']; simp
      rw [abs_of_neg h] at hq ⊢
      have := xiZeroCopy_zero_free_from_four (q := q') (by rw [him]; exact hq)
      rwa [him, hre] at this
  have hr := hup (xiZeroCopyReflectEquiv q) (by
    rw [xiZeroCopy_reflect_val]; simpa [Complex.sub_im] using hq)
  rw [xiZeroCopy_reflect_val] at hr
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
    abs_neg] at hr
  have := hup q hq
  rw [abs_le]; constructor <;> linarith

/-! ## Asymptotics -/

theorem eventually_log_budget_conditions {A η₀ t₁ K₀ C : ℝ} (hA0 : 0 ≤ A) (hA : A < 1)
    (hη₀ : 0 < η₀) (ht₁ : 0 < t₁) (hK₀ : 0 < K₀) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ v ∧ Real.log 4 ≤ v ^ ((A + 1) / 2) ∧
      1 / (100 * v ^ ((A + 1) / 2)) ≤ η₀ ∧
      Real.exp (-(v ^ (1 - (A + 1) / 2) / 100)) * v ^ A ≤ t₁ ∧
      Real.exp (v ^ A) * (|C| + 2 + v ^ ((A + 1) / 2)) * Real.exp (-v ^ ((A + 1) / 2)) ≤ K₀ := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (A + 1) / 2 := ⟨_, rfl⟩
  rw [← hβ]
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hβ1 : β < 1 := by rw [hβ]; linarith
  have hAβ : A < β := by rw [hβ]; linarith
  have hx : Tendsto (fun v : ℝ => v ^ β) atTop atTop := tendsto_rpow_atTop hβ0
  -- (C3)
  have h3 : ∀ᶠ v : ℝ in atTop, Real.exp (-(v ^ (1 - β) / 100)) * v ^ A ≤ t₁ := by
    have hγ : 0 < 1 - β := by linarith
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / (1 - β)) (1 / 100)
      (by norm_num)).comp (tendsto_rpow_atTop hγ)
    filter_upwards [ht.eventually (ge_mem_nhds ht₁), eventually_ge_atTop (0 : ℝ)] with v hv hv0
    simp only [Function.comp] at hv
    have e : (v ^ (1 - β)) ^ (A / (1 - β)) = v ^ A := by
      rw [← Real.rpow_mul hv0]; congr 1; field_simp
    rw [e] at hv
    have e2 : -(1 / 100) * v ^ (1 - β) = -(v ^ (1 - β) / 100) := by ring
    rw [e2] at hv
    linarith
  -- (C4)
  have h4 : ∀ᶠ v : ℝ in atTop, Real.exp (v ^ A) * (|C| + 2 + v ^ β) * Real.exp (-v ^ β) ≤ K₀ := by
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = A / β := ⟨_, rfl⟩
    have hκ1 : κ < 1 := by rw [hκ, div_lt_one hβ0]; exact hAβ
    have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
    -- `x^κ ≤ x/2` eventually
    have hxk : ∀ᶠ x : ℝ in atTop, x ^ κ ≤ x / 2 := by
      filter_upwards [(tendsto_rpow_atTop (show 0 < 1 - κ by linarith)).eventually_ge_atTop 2,
        eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have e : x = x ^ κ * x ^ (1 - κ) := by
        rw [← Real.rpow_add hx0]; simp
      have hp := Real.rpow_nonneg hx0.le κ
      nlinarith
    have hdecay : Tendsto (fun x : ℝ => (|C| + 2) * Real.exp (-(1 / 2) * x) +
        x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
      have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
      simpa using (h1.const_mul (|C| + 2)).add h2
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp (x ^ κ) * (|C| + 2 + x) * Real.exp (-x) ≤ K₀ := by
      filter_upwards [hxk, hdecay.eventually (ge_mem_nhds hK₀), eventually_ge_atTop (0 : ℝ)]
        with x h1 h2 hx0
      rw [Real.rpow_one] at h2
      have e : Real.exp (x ^ κ) * (|C| + 2 + x) * Real.exp (-x) =
          ((|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x)) *
            Real.exp (x ^ κ - x / 2) := by
        have ee : Real.exp (x ^ κ) * Real.exp (-x) =
            Real.exp (-(1 / 2) * x) * Real.exp (x ^ κ - x / 2) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        linear_combination (|C| + 2 + x) * ee
      rw [e]
      have h3 : Real.exp (x ^ κ - x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h4 : 0 ≤ (|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x) := by
        positivity
      calc _ ≤ ((|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x)) * 1 :=
            mul_le_mul_of_nonneg_left h3 h4
        _ ≤ K₀ := by linarith
    filter_upwards [hx.eventually hev, eventually_ge_atTop (0 : ℝ)] with v hv hv0
    have e : (v ^ β) ^ κ = v ^ A := by
      rw [← Real.rpow_mul hv0, hκ]; congr 1; field_simp
    rw [e] at hv
    exact hv
  filter_upwards [eventually_ge_atTop (1 : ℝ), hx.eventually_ge_atTop (Real.log 4),
    hx.eventually_ge_atTop (1 / (100 * η₀)), h3, h4] with v h1 h2 h2' h3' h4'
  refine ⟨h1, h2, ?_, h3', h4'⟩
  have hp : 0 < v ^ β := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h2'
  nlinarith

/-! ## The producer -/

/-- **The height-split producer.**  If every zero up to height `T` has width
`½ − |Re ρ − ½| ≥ ω`, the primes of `P` exceed `y`, the budget is at most `B`,
`y^{−ω} B ≤ t₁` with `(e^{t₁} − 1)W ≤ Φ(0)/2`, and the tail above `T` satisfies
`(e^B − 1)·80(C + log(3T + 4))/T ≤ Φ(0)/2`, then the product test is nonnegative. -/
theorem jasProductAggregate_re_nonneg_of_heightSplit {σ y B T ω t₁ : ℝ} (hy0 : 0 < y)
    (hT : 1 ≤ T) (hω0 : 0 ≤ ω) (P : Finset Nat.Primes) (hP : ∀ p ∈ P, y < ((p : ℕ) : ℝ))
    (hB : ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ B)
    (hwidth : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T → ω ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2|)
    (ht₁ : 0 ≤ t₁) (hexpt : (Real.exp t₁ - 1) * lagWeightTotal ≤ poleSharpConstant / 2)
    (hlow : Real.exp (-(ω * Real.log y)) * B ≤ t₁)
    (htail : (Real.exp B - 1) * (80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T) ≤
      poleSharpConstant / 2)
    (z : Nat.Primes → ℂ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hlogp : ∀ p ∈ P, Real.log y ≤ Real.log ((p : ℕ) : ℝ) := fun p hp =>
    Real.log_le_log hy0 (hP p hp).le
  have hlogy : ∀ p ∈ P, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p _ => log_prime_pos p |>.le
  have hb12 : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := fun q => by
    rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le) hB
  have hlowsum : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T →
      ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤ t₁ := by
    intro q hq
    have hw := hwidth q hq
    have hterm : ∀ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤
        Real.exp (-(ω * Real.log y)) * Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by
      intro p hp
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := hlogp p hp
      have h2 : ω * Real.log y ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) := by
        rcases le_or_gt 0 (Real.log y) with hly | hly
        · calc ω * Real.log y ≤ ω * Real.log ((p : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h1 hω0
            _ ≤ _ := mul_le_mul_of_nonneg_right hw (hlogy p hp)
        · have : ω * Real.log y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hω0 hly.le
          have : 0 ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) :=
            mul_nonneg (by linarith) (hlogy p hp)
          linarith
      linarith
    calc ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))
        ≤ ∑ p ∈ P, Real.exp (-(ω * Real.log y)) *
            Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := Finset.sum_le_sum hterm
      _ = Real.exp (-(ω * Real.log y)) *
            ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(ω * Real.log y)) * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
      _ ≤ t₁ := hlow
  have hhighsum : ∀ q : XiZeroCopy,
      ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤ B := by
    intro q
    refine le_trans (Finset.sum_le_sum fun p hp => Real.exp_le_exp.mpr ?_) hB
    have h1 := hlogy p hp
    have h2 := hb12 q
    nlinarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp B - 1 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; linarith [Real.one_le_exp hB0]
  have hterm : ∀ q : XiZeroCopy, (Real.exp (∑ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (Real.exp t₁ - 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
        E * {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q := by
    intro q
    have hn := norm_nonneg (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))
    have ht0 : 0 ≤ Real.exp t₁ - 1 := by linarith [Real.one_le_exp ht₁]
    by_cases hq : T < |(q.1 : ℂ).im|
    · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]
      have : Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
          Real.log ((p : ℕ) : ℝ))) - 1 ≤ E := by
        rw [hEdef]; linarith [Real.exp_le_exp.mpr (hhighsum q)]
      nlinarith
    · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq),
        mul_zero, add_zero]
      push Not at hq
      exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_le_exp.mpr (hlowsum q hq)]) hn
  have hsumR : Summable fun q : XiZeroCopy =>
      (Real.exp t₁ - 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ +
        E * {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q :=
    (summable_inv_mul_one_sub.norm.mul_left _).add
      ((summable_inv_mul_one_sub.norm.indicator _).mul_left _)
  have hsumL : Summable fun q : XiZeroCopy => (Real.exp (∑ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg ?_ (norm_nonneg _)) hterm hsumR
    linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
      (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))).le)]
  have hZ := hsumL.tsum_le_tsum hterm hsumR
  rw [(summable_inv_mul_one_sub.norm.mul_left _).tsum_add
    ((summable_inv_mul_one_sub.norm.indicator _).mul_left _), tsum_mul_left, tsum_mul_left] at hZ
  have hWt : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = lagWeightTotal := rfl
  rw [hWt] at hZ
  have htl := tsum_indicator_abs_im_gt_weight_le hT
  have htailb : E * ∑' q : XiZeroCopy, {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
      (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q ≤ poleSharpConstant / 2 := by
    rw [← hEdef] at htail
    exact (mul_le_mul_of_nonneg_left htl hE0).trans htail
  refine le_trans (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) ?_)
    (jasProductAggregate_re_ge_exp (σ := σ) P z)
  linarith

/-- **The unconditional JAS producer at logarithmic budget.**  For `0 ≤ A < 1` there is `Y > 1`
such that, at every level `σ`, the product tests are positive on every finite set of primes
`p > y`, `y ≥ Y`, with prime budget `Σ_P p^{−(σ−½)} ≤ (log y)^A`. -/
theorem exists_jasProductPositive_logBudget {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 1) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ (σ y : ℝ), Y ≤ y → ∀ P : Finset Nat.Primes,
      (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ Real.log y ^ A →
      ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width
  have hW := lagWeightTotal_pos
  have hΦ := poleSharpConstant_pos
  obtain ⟨t₁, ht₁def⟩ : ∃ t : ℝ, t = Real.log (1 + poleSharpConstant / (2 * lagWeightTotal)) :=
    ⟨_, rfl⟩
  have ht₁ : 0 < t₁ := by
    rw [ht₁def]; exact Real.log_pos (by have := div_pos hΦ (by positivity : (0 : ℝ) < 2 * lagWeightTotal); linarith)
  have hexpt : (Real.exp t₁ - 1) * lagWeightTotal = poleSharpConstant / 2 := by
    rw [ht₁def, Real.exp_log (by have := div_pos hΦ (by positivity : (0 : ℝ) < 2 * lagWeightTotal); linarith)]
    field_simp
    ring
  obtain ⟨v₀, hv₀⟩ := eventually_atTop.mp (eventually_log_budget_conditions
    (C := xiLineTwoLogDerivConstant) hA0 hA hη₀ ht₁ (show (0 : ℝ) < poleSharpConstant / 160 by positivity))
  refine ⟨Real.exp (max v₀ 1), by linarith [Real.add_one_le_exp (max v₀ 1), le_max_right v₀ 1],
    fun σ y hy P hP hB z => ?_⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = Real.log y := ⟨_, rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hvge : max v₀ 1 ≤ v := by
    rw [hvdef, ← Real.log_exp (max v₀ 1)]; exact Real.log_le_log (Real.exp_pos _) hy
  obtain ⟨hv1, hT4, hω, hC3, hC4⟩ := hv₀ v (le_trans (le_max_left _ _) hvge)
  rw [← hvdef] at hB
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (A + 1) / 2 := ⟨_, rfl⟩
  rw [← hβ] at hT4 hω hC3 hC4
  have hv0 : 0 < v := by linarith
  have hvβ : 0 < v ^ β := Real.rpow_pos_of_pos hv0 _
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (v ^ β) := ⟨_, rfl⟩
  have hT1 : 4 ≤ T := by
    rw [hTdef, ← Real.exp_log (show (0 : ℝ) < 4 by norm_num)]; exact Real.exp_le_exp.mpr hT4
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = 1 / (100 * v ^ β) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hωdef]; positivity
  rw [← hωdef] at hω
  have hωv : ω * v = v ^ (1 - β) / 100 := by
    rw [hωdef, Real.rpow_sub hv0, Real.rpow_one]; field_simp
  -- widths
  have hwidth : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T → ω ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by
    intro q hq
    rcases le_or_gt |(q.1 : ℂ).im| 4 with h4 | h4
    · linarith [hlow q h4]
    · have h1 := abs_re_sub_half_le_of_four_le q h4.le
      have hlog0 : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
      have hlogT : Real.log |(q.1 : ℂ).im| ≤ v ^ β := by
        rw [← Real.log_exp (v ^ β), ← hTdef]; exact Real.log_le_log (by linarith) hq
      have h2 : ω ≤ 1 / 100 / Real.log |(q.1 : ℂ).im| := by
        rw [hωdef, div_div]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
  have hlog7 : Real.log (3 * T + 4) ≤ 2 + v ^ β := by
    have h1 : Real.log (3 * T + 4) ≤ Real.log (7 * T) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity),
      show Real.log T = v ^ β by rw [hTdef, Real.log_exp]] at h1
    have h7 : Real.log 7 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith [Real.exp_one_gt_d9]
    linarith
  have hTinv : 1 / T = Real.exp (-v ^ β) := by rw [hTdef, Real.exp_neg, one_div]
  have htail : (Real.exp (v ^ A) - 1) * (80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T) ≤
      poleSharpConstant / 2 := by
    have hE0 : 0 ≤ Real.exp (v ^ A) - 1 := by
      linarith [Real.one_le_exp (Real.rpow_nonneg hv0.le A)]
    have h1 : 80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T ≤
        80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) * Real.exp (-v ^ β) := by
      rw [div_eq_mul_one_div, hTinv]
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self xiLineTwoLogDerivConstant])
        (Real.exp_pos _).le
    have h2 : 0 ≤ 80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) * Real.exp (-v ^ β) := by
      have := abs_nonneg xiLineTwoLogDerivConstant; positivity
    calc (Real.exp (v ^ A) - 1) * (80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T)
        ≤ (Real.exp (v ^ A) - 1) * (80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := mul_le_mul_of_nonneg_left h1 hE0
      _ ≤ Real.exp (v ^ A) * (80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := mul_le_mul_of_nonneg_right (by linarith) h2
      _ = 80 * (Real.exp (v ^ A) * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := by ring
      _ ≤ 80 * (poleSharpConstant / 160) := by linarith
      _ = poleSharpConstant / 2 := by ring
  refine jasProductAggregate_re_nonneg_of_heightSplit hy0 (by linarith) hω0 P hP hB hwidth ht₁.le
    hexpt.le ?_ htail z
  rw [← hvdef, hωv]
  exact hC3

/-! ## Power-of-log zero-free regions -/

theorem eventually_powerLog_budget_conditions {A θ c η₀ t₁ K₀ C H : ℝ} (hA0 : 0 ≤ A) (hθ : 0 < θ)
    (hAθ : A * θ < 1) (hc : 0 < c) (hη₀ : 0 < η₀) (ht₁ : 0 < t₁) (hK₀ : 0 < K₀) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ v ∧ Real.log H ≤ v ^ ((A + 1 / θ) / 2) ∧
      c * v ^ (-((A + 1 / θ) / 2 * θ)) ≤ η₀ ∧
      Real.exp (-(c * v ^ (1 - (A + 1 / θ) / 2 * θ))) * v ^ A ≤ t₁ ∧
      Real.exp (v ^ A) * (|C| + 2 + v ^ ((A + 1 / θ) / 2)) * Real.exp (-v ^ ((A + 1 / θ) / 2)) ≤
        K₀ := by
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (A + 1 / θ) / 2 := ⟨_, rfl⟩
  rw [← hβ]
  have hinv : 0 < 1 / θ := by positivity
  have hβ0 : 0 < β := by rw [hβ]; linarith
  have hAβ : A < β := by
    rw [hβ]
    have : A < 1 / θ := by rw [lt_div_iff₀ hθ]; linarith
    linarith
  have hβθe : β * θ = (A * θ + 1) / 2 := by rw [hβ]; field_simp
  have hβθ : β * θ < 1 := by rw [hβθe]; linarith
  have hβθ0 : 0 < β * θ := by positivity
  have hx : Tendsto (fun v : ℝ => v ^ β) atTop atTop := tendsto_rpow_atTop hβ0
  have h3 : ∀ᶠ v : ℝ in atTop, Real.exp (-(c * v ^ (1 - β * θ))) * v ^ A ≤ t₁ := by
    have hγ : 0 < 1 - β * θ := by linarith
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / (1 - β * θ)) c hc).comp
      (tendsto_rpow_atTop hγ)
    filter_upwards [ht.eventually (ge_mem_nhds ht₁), eventually_ge_atTop (0 : ℝ)] with v hv hv0
    simp only [Function.comp] at hv
    have e : (v ^ (1 - β * θ)) ^ (A / (1 - β * θ)) = v ^ A := by
      rw [← Real.rpow_mul hv0]; congr 1; field_simp
    rw [e, show -c * v ^ (1 - β * θ) = -(c * v ^ (1 - β * θ)) by ring, mul_comm] at hv
    exact hv
  have h2 : ∀ᶠ v : ℝ in atTop, c * v ^ (-(β * θ)) ≤ η₀ := by
    have ht := (tendsto_rpow_neg_atTop hβθ0).const_mul c
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (ge_mem_nhds hη₀)] with v hv
    exact hv
  have h4 : ∀ᶠ v : ℝ in atTop, Real.exp (v ^ A) * (|C| + 2 + v ^ β) * Real.exp (-v ^ β) ≤ K₀ := by
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = A / β := ⟨_, rfl⟩
    have hκ1 : κ < 1 := by rw [hκ, div_lt_one hβ0]; exact hAβ
    have hxk : ∀ᶠ x : ℝ in atTop, x ^ κ ≤ x / 2 := by
      filter_upwards [(tendsto_rpow_atTop (show 0 < 1 - κ by linarith)).eventually_ge_atTop 2,
        eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have e : x = x ^ κ * x ^ (1 - κ) := by rw [← Real.rpow_add hx0]; simp
      have hp := Real.rpow_nonneg hx0.le κ
      nlinarith
    have hdecay : Tendsto (fun x : ℝ => (|C| + 2) * Real.exp (-(1 / 2) * x) +
        x ^ (1 : ℝ) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℝ => Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
      have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 2) (by norm_num)
      simpa using (h1.const_mul (|C| + 2)).add h2
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp (x ^ κ) * (|C| + 2 + x) * Real.exp (-x) ≤ K₀ := by
      filter_upwards [hxk, hdecay.eventually (ge_mem_nhds hK₀), eventually_ge_atTop (0 : ℝ)]
        with x h1 h2 hx0
      rw [Real.rpow_one] at h2
      have ee : Real.exp (x ^ κ) * Real.exp (-x) =
          Real.exp (-(1 / 2) * x) * Real.exp (x ^ κ - x / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      have e : Real.exp (x ^ κ) * (|C| + 2 + x) * Real.exp (-x) =
          ((|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x)) *
            Real.exp (x ^ κ - x / 2) := by linear_combination (|C| + 2 + x) * ee
      rw [e]
      have h3 : Real.exp (x ^ κ - x / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h4 : 0 ≤ (|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x) := by
        positivity
      calc _ ≤ ((|C| + 2) * Real.exp (-(1 / 2) * x) + x * Real.exp (-(1 / 2) * x)) * 1 :=
            mul_le_mul_of_nonneg_left h3 h4
        _ ≤ K₀ := by linarith
    filter_upwards [hx.eventually hev, eventually_ge_atTop (0 : ℝ)] with v hv hv0
    have e : (v ^ β) ^ κ = v ^ A := by
      rw [← Real.rpow_mul hv0, hκ]; congr 1; field_simp
    rw [e] at hv
    exact hv
  filter_upwards [eventually_ge_atTop (1 : ℝ), hx.eventually_ge_atTop (Real.log H), h2, h3, h4]
    with v h1 h2' h2'' h3' h4'
  exact ⟨h1, h2', h2'', h3', h4'⟩

/-- **The JAS producer from a power-of-log zero-free region.**  If every zero with `|Im ρ| ≥ t₀`
satisfies `|Re ρ − ½| ≤ ½ − c (log |Im ρ|)^{−θ}`, then for every `0 ≤ A < 1/θ` the product tests at
every level are positive on all sets of primes `p > y ≥ Y` with budget `≤ (log y)^A`. -/
theorem exists_jasProductPositive_logBudget_of_powerLogWidth {θ c t₀ : ℝ} (hθ : 0 < θ)
    (hc : 0 < c) (ht₀ : 1 < t₀)
    (hw : ∀ q : XiZeroCopy, t₀ ≤ |(q.1 : ℂ).im| →
      |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - c * Real.log |(q.1 : ℂ).im| ^ (-θ))
    {A : ℝ} (hA0 : 0 ≤ A) (hAθ : A * θ < 1) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ (σ y : ℝ), Y ≤ y → ∀ P : Finset Nat.Primes,
      (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ Real.log y ^ A →
      ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at t₀
  have hW := lagWeightTotal_pos
  have hΦ := poleSharpConstant_pos
  have hq0 : (0 : ℝ) < poleSharpConstant / (2 * lagWeightTotal) := by positivity
  obtain ⟨t₁, ht₁def⟩ : ∃ t : ℝ, t = Real.log (1 + poleSharpConstant / (2 * lagWeightTotal)) :=
    ⟨_, rfl⟩
  have ht₁ : 0 < t₁ := by rw [ht₁def]; exact Real.log_pos (by linarith)
  have hexpt : (Real.exp t₁ - 1) * lagWeightTotal = poleSharpConstant / 2 := by
    rw [ht₁def, Real.exp_log (by linarith)]; field_simp; ring
  obtain ⟨v₀, hv₀⟩ := eventually_atTop.mp (eventually_powerLog_budget_conditions
    (C := xiLineTwoLogDerivConstant) (H := t₀) hA0 hθ hAθ hc hη₀ ht₁
    (show (0 : ℝ) < poleSharpConstant / 160 by positivity))
  refine ⟨Real.exp (max v₀ 1), by linarith [Real.add_one_le_exp (max v₀ 1), le_max_right v₀ 1],
    fun σ y hy P hP hB z => ?_⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = Real.log y := ⟨_, rfl⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hvge : max v₀ 1 ≤ v := by
    rw [hvdef, ← Real.log_exp (max v₀ 1)]; exact Real.log_le_log (Real.exp_pos _) hy
  obtain ⟨hv1, hTt, hω, hC3, hC4⟩ := hv₀ v (le_trans (le_max_left _ _) hvge)
  rw [← hvdef] at hB
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (A + 1 / θ) / 2 := ⟨_, rfl⟩
  rw [← hβ] at hTt hω hC3 hC4
  have hv0 : 0 < v := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (v ^ β) := ⟨_, rfl⟩
  have hTt0 : t₀ ≤ T := by
    rw [hTdef, ← Real.exp_log (show (0 : ℝ) < t₀ by linarith)]; exact Real.exp_le_exp.mpr hTt
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = c * v ^ (-(β * θ)) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hωdef]; positivity
  rw [← hωdef] at hω
  have hωv : ω * v = c * v ^ (1 - β * θ) := by
    rw [hωdef, mul_assoc, ← Real.rpow_add_one hv0.ne']; ring_nf
  have hwidth : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T → ω ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by
    intro q hq
    rcases le_or_gt t₀ |(q.1 : ℂ).im| with h0 | h0
    · have h1 := hw q h0
      have hlog0 : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
      have hlogT : Real.log |(q.1 : ℂ).im| ≤ v ^ β := by
        rw [← Real.log_exp (v ^ β), ← hTdef]; exact Real.log_le_log (by linarith) hq
      have h2 : (v ^ β) ^ (-θ) ≤ Real.log |(q.1 : ℂ).im| ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos hlog0 hlogT (by linarith)
      have h3 : (v ^ β) ^ (-θ) = v ^ (-(β * θ)) := by
        rw [← Real.rpow_mul hv0.le]; ring_nf
      rw [h3] at h2
      have : ω ≤ c * Real.log |(q.1 : ℂ).im| ^ (-θ) := by
        rw [hωdef]; exact mul_le_mul_of_nonneg_left h2 hc.le
      linarith
    · linarith [hlow q h0.le]
  have hlog7 : Real.log (3 * T + 4) ≤ 2 + v ^ β := by
    have hT1 : 1 ≤ T := by linarith
    have h1 : Real.log (3 * T + 4) ≤ Real.log (7 * T) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity),
      show Real.log T = v ^ β by rw [hTdef, Real.log_exp]] at h1
    have h7 : Real.log 7 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith [Real.exp_one_gt_d9]
    linarith
  have hTinv : 1 / T = Real.exp (-v ^ β) := by rw [hTdef, Real.exp_neg, one_div]
  have htail : (Real.exp (v ^ A) - 1) * (80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T) ≤
      poleSharpConstant / 2 := by
    have hE0 : 0 ≤ Real.exp (v ^ A) - 1 := by
      linarith [Real.one_le_exp (Real.rpow_nonneg hv0.le A)]
    have h1 : 80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T ≤
        80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) * Real.exp (-v ^ β) := by
      rw [div_eq_mul_one_div, hTinv]
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self xiLineTwoLogDerivConstant])
        (Real.exp_pos _).le
    have h2 : 0 ≤ 80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) * Real.exp (-v ^ β) := by
      have := abs_nonneg xiLineTwoLogDerivConstant
      have := Real.rpow_nonneg hv0.le β
      positivity
    calc (Real.exp (v ^ A) - 1) * (80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T)
        ≤ (Real.exp (v ^ A) - 1) * (80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := mul_le_mul_of_nonneg_left h1 hE0
      _ ≤ Real.exp (v ^ A) * (80 * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := mul_le_mul_of_nonneg_right (by linarith) h2
      _ = 80 * (Real.exp (v ^ A) * (|xiLineTwoLogDerivConstant| + 2 + v ^ β) *
            Real.exp (-v ^ β)) := by ring
      _ ≤ 80 * (poleSharpConstant / 160) := by linarith
      _ = poleSharpConstant / 2 := by ring
  refine jasProductAggregate_re_nonneg_of_heightSplit hy0 (by linarith) hω0 P hP hB hwidth ht₁.le
    hexpt.le ?_ htail z
  rw [← hvdef, hωv]
  exact hC3

/-! ## The Vinogradov–Korobov producer -/

/-- For `θ > 2/3`, eventually `(log t)^{−θ} ≤ (log t)^{−2/3} (log log t)^{−5/3} / 10⁸`. -/
theorem eventually_powerLog_le_vkWidth {θ : ℝ} (hθ : 2 / 3 < θ) :
    ∀ᶠ t : ℝ in atTop, Real.log t ^ (-θ) ≤ vinogradovKorobovGaussianWidth t := by
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 3 * (θ - 2 / 3) / 5 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (10 : ℝ) ^ (-(24 / 5 : ℝ)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε53 : ε ^ (5 / 3 : ℝ) = 1 / 10 ^ 8 := by
    rw [hεdef, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hlo := (isLittleO_log_rpow_atTop hr).bound hε
  have hL := Real.tendsto_log_atTop
  filter_upwards [hL.eventually hlo, hL.eventually (eventually_ge_atTop (Real.exp 1))] with t h1 h2
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log t := ⟨_, rfl⟩
  rw [← hLdef] at h1 h2
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) h2
  have hL0 : 0 < L := by linarith
  have hlogL : 1 ≤ Real.log L := by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) h2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (Real.rpow_nonneg hL0.le r)] at h1
  -- `(log L)^{5/3} ≤ 10^{−8} L^{θ−2/3}`
  have h3 : Real.log L ^ (5 / 3 : ℝ) ≤ 1 / 10 ^ 8 * L ^ (θ - 2 / 3) := by
    have := Real.rpow_le_rpow (by linarith) h1 (show (0 : ℝ) ≤ 5 / 3 by norm_num)
    rw [Real.mul_rpow hε.le (Real.rpow_nonneg hL0.le r), hε53, ← Real.rpow_mul hL0.le] at this
    rwa [show r * (5 / 3) = θ - 2 / 3 by rw [hrdef]; ring] at this
  unfold vinogradovKorobovGaussianWidth
  rw [← hLdef]
  have hp1 : 0 < Real.log L ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hneg : Real.log L ^ (-(5 : ℝ) / 3) = 1 / Real.log L ^ (5 / 3 : ℝ) := by
    rw [show (-(5 : ℝ) / 3) = -(5 / 3) by ring, Real.rpow_neg (by linarith), one_div]
  rw [hneg]
  have hsplit : L ^ (-(2 : ℝ) / 3) = L ^ (-θ) * L ^ (θ - 2 / 3) := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [hsplit]
  have hq : 0 < L ^ (-θ) := Real.rpow_pos_of_pos hL0 _
  have hq2 : 0 < L ^ (θ - 2 / 3) := Real.rpow_pos_of_pos hL0 _
  rw [le_div_iff₀ (by norm_num), mul_one_div, le_div_iff₀ hp1]
  nlinarith [mul_le_mul_of_nonneg_left h3 hq.le]

/-- **The Vinogradov–Korobov region as a power-of-log width.**  For `θ > 2/3` there is `t₀ > 1`
with `|Re ρ − ½| ≤ ½ − (log |Im ρ|)^{−θ}` whenever `|Im ρ| ≥ t₀`. -/
theorem exists_powerLog_width_vk {θ : ℝ} (hθ : 2 / 3 < θ) :
    ∃ t₀ : ℝ, 1 < t₀ ∧ ∀ q : XiZeroCopy, t₀ ≤ |(q.1 : ℂ).im| →
      |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - 1 * Real.log |(q.1 : ℂ).im| ^ (-θ) := by
  obtain ⟨t₀', -, -, hvk⟩ := exists_xiZero_re_le_vinogradovKorobov
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.mp (eventually_powerLog_le_vkWidth hθ)
  refine ⟨max (max t₀' t₁) 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun q hq => ?_⟩
  have h0 : t₀' ≤ |(q.1 : ℂ).im| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have h1 : t₁ ≤ |(q.1 : ℂ).im| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hw := ht₁ _ h1
  have hup : (q.1 : ℂ).re ≤ 1 - vinogradovKorobovGaussianWidth |(q.1 : ℂ).im| := hvk q h0
  have hr := hvk (xiZeroCopyReflectEquiv q) (by
    show t₀' ≤ |((xiZeroCopyReflectEquiv q).1 : ℂ).im|
    rw [xiZeroCopy_reflect_val]; simpa [Complex.sub_im] using h0)
  change ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤
    1 - vinogradovKorobovGaussianWidth |((xiZeroCopyReflectEquiv q).1 : ℂ).im| at hr
  rw [xiZeroCopy_reflect_val] at hr
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
    abs_neg] at hr
  rw [one_mul, abs_le]; constructor <;> linarith

/-- **The unconditional JAS producer at budget `(log y)^{3/2−ε}`** (Vinogradov–Korobov). -/
theorem exists_jasProductPositive_logBudget_vk {A : ℝ} (hA0 : 0 ≤ A) (hA : A < 3 / 2) :
    ∃ Y : ℝ, 1 < Y ∧ ∀ (σ y : ℝ), Y ≤ y → ∀ P : Finset Nat.Primes,
      (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
      ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ Real.log y ^ A →
      ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  have hden : 0 < A + 3 / 2 := by linarith
  have hθ : 2 / 3 < 2 / (A + 3 / 2) := by rw [lt_div_iff₀ hden]; linarith
  have hAθ : A * (2 / (A + 3 / 2)) < 1 := by
    rw [mul_div_assoc', div_lt_one hden]; linarith
  obtain ⟨t₀, ht₀, hw⟩ := exists_powerLog_width_vk hθ
  exact exists_jasProductPositive_logBudget_of_powerLogWidth (by positivity) one_pos ht₀ hw hA0 hAθ

end

end RHTower
