import GaloisForLFunctions.RHTower.PrimeKaramata
import GaloisForLFunctions.RHTower.MobiusPrimeApertureDifferentialOrder
import GaloisForLFunctions.HTGeometry.SteinhausWeightProfile

/-!
# The normalized regular-variation weights

The card's `(10)`.  The normalized weight of a prime `p = vX` is

`d_X a_{p,X} = π(X)·(log p)p^{−α}L(p)/W_X`,

and it factors EXACTLY as `w_α(v)` times four ratios, each of which tends to `1`:

* `π(X)/(X/log X)` — the prime number theorem for `π`;
* `log p/log X` — bounded because `log(p/X)` stays in a fixed interval;
* `L(p)/L(X)` — Karamata's uniform convergence theorem;
* `X^{1−α}L(X)/((1−α)W_X)` — the prime Karamata law.

Hence `d_X a_{p,X} → w_α(v)` uniformly on compact subintervals of `(0,1]`.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

noncomputable section

/-- The card's `d_X`. -/
def rvPrimeCount (X : ℝ) : ℝ := (Nat.primeCounting ⌊X⌋₊ : ℝ)

/-- The card's `d_X a_{p,X}`, as a function of a real point. -/
def rvNormReal (α : ℝ) (L : ℝ → ℝ) (X t : ℝ) : ℝ :=
  rvPrimeCount X * (Real.log t * rvPrimeWeight α L t) / rvWeightSum α L X

/-- The exact four-factor decomposition. -/
theorem rvNormReal_eq {α : ℝ} (hα1 : α < 1) {L : ℝ → ℝ} {X t : ℝ} (hX1 : 1 < X) (ht : 0 < t)
    (hLX : L X ≠ 0) (hW : rvWeightSum α L X ≠ 0) :
    rvNormReal α L X t
      = weightProfile α (t / X) * ((rvPrimeCount X / (X / Real.log X))
          * (Real.log t / Real.log X) * (L t / L X)
          * ((X ^ (1 - α) * L X) / ((1 - α) * rvWeightSum α L X))) := by
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hlogX : 0 < Real.log X := Real.log_pos hX1
  have hα' : (0 : ℝ) < 1 - α := by linarith
  have hpow : (t / X) ^ (-α) = t ^ (-α) * (X ^ (-α))⁻¹ := by
    rw [Real.div_rpow ht.le hX0.le, div_eq_mul_inv]
  have hXpow : X ^ (1 - α) = X * (X ^ (-α))⁻¹⁻¹ := by
    rw [inv_inv]
    have hadd := Real.rpow_add hX0 1 (-α)
    rw [Real.rpow_one] at hadd
    rw [show (1 : ℝ) - α = 1 + -α by ring, hadd]
  have hXn : (0 : ℝ) < X ^ (-α) := Real.rpow_pos_of_pos hX0 _
  rw [rvNormReal, weightProfile, rvPrimeWeight, hpow, hXpow]
  field_simp


theorem two_factor_bounds {c x y : ℝ} (hc1 : c ≤ 1)
    (h1 : 1 - c ≤ x) (h1' : x ≤ 1 + c) (h2 : 1 - c ≤ y) (h2' : y ≤ 1 + c) :
    (1 - c) ^ 2 ≤ x * y ∧ x * y ≤ (1 + c) ^ 2 := by
  have hu0 : (0 : ℝ) ≤ 1 - c := by linarith
  have hx0 : (0 : ℝ) ≤ x := le_trans hu0 h1
  have hv0 : (0 : ℝ) ≤ 1 + c := by linarith
  constructor
  · have := mul_le_mul h1 h2 hu0 hx0
    nlinarith only [this]
  · have := mul_le_mul h1' h2' (le_trans hu0 h2) hv0
    nlinarith only [this]

theorem four_factor_bounds {c x₁ x₂ x₃ x₄ : ℝ} (hc1 : c ≤ 1)
    (b₁ : 1 - c ≤ x₁) (b₁' : x₁ ≤ 1 + c) (b₂ : 1 - c ≤ x₂) (b₂' : x₂ ≤ 1 + c)
    (b₃ : 1 - c ≤ x₃) (b₃' : x₃ ≤ 1 + c) (b₄ : 1 - c ≤ x₄) (b₄' : x₄ ≤ 1 + c) :
    (1 - c) ^ 4 ≤ x₁ * x₂ * x₃ * x₄ ∧ x₁ * x₂ * x₃ * x₄ ≤ (1 + c) ^ 4 := by
  obtain ⟨p1, p2⟩ := two_factor_bounds hc1 b₁ b₁' b₂ b₂'
  obtain ⟨q1, q2⟩ := two_factor_bounds hc1 b₃ b₃' b₄ b₄'
  have hu0 : (0 : ℝ) ≤ (1 - c) ^ 2 := sq_nonneg _
  have hp0 : (0 : ℝ) ≤ x₁ * x₂ := le_trans hu0 p1
  have hv0 : (0 : ℝ) ≤ (1 + c) ^ 2 := sq_nonneg _
  have hid : x₁ * x₂ * x₃ * x₄ = (x₁ * x₂) * (x₃ * x₄) := by ring
  rw [hid]
  constructor
  · have := mul_le_mul p1 q1 hu0 hp0
    nlinarith only [this]
  · have := mul_le_mul p2 q2 (le_trans hu0 q1) hv0
    nlinarith only [this]

/-- The prime-counting ratio. -/
theorem tendsto_rvPrimeCount_ratio :
    Tendsto (fun X : ℝ => rvPrimeCount X / (X / Real.log X)) atTop (𝓝 1) :=
  tendsto_primeCounting_ratio

/-- The reciprocal Karamata ratio. -/
theorem tendsto_rvWeightSum_inv {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) :
    Tendsto (fun X : ℝ => (X ^ (1 - α) * L X) / ((1 - α) * rvWeightSum α L X)) atTop (𝓝 1) := by
  have hα' : (0 : ℝ) < 1 - α := by linarith
  have hbase := (tendsto_rvWeightSum hα0 hα1 hL).const_mul (1 - α)
  rw [show (1 - α) * (1 / (1 - α)) = 1 by field_simp] at hbase
  have hinv := hbase.inv₀ (by norm_num)
  rw [inv_one] at hinv
  refine Tendsto.congr' ?_ hinv
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX
  have hLX : 0 < L X := hL.pos _ hX0
  have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
  rw [mul_div_assoc', ← div_div, inv_div, div_div_eq_mul_div]
  ring


/-- **The card's `(10)`.**  The normalized weight is `w_α(p/X)` up to a factor `(1 ± c)^4`,
uniformly on the shell `(aX, bX]`. -/
theorem rvNormReal_bounds {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ X in atTop, ∀ t : ℝ, a * X < t → t ≤ b * X →
      (1 - c) ^ 4 * weightProfile α (t / X) ≤ rvNormReal α L X t
        ∧ rvNormReal α L X t ≤ (1 + c) ^ 4 * weightProfile α (t / X) := by
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  set C : ℝ := max |Real.log a| |Real.log b| with hC
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (le_max_left _ _)
  have hπ := tendsto_rvPrimeCount_ratio.eventually
    (Metric.closedBall_mem_nhds (1 : ℝ) hc0)
  have hWr := (tendsto_rvWeightSum_inv hα0 hα1 hL).eventually
    (Metric.closedBall_mem_nhds (1 : ℝ) hc0)
  have hLr := isSlowlyVarying_uniform hL ha (b := b) hc0
  have hWpos : ∀ᶠ X in atTop, 0 < rvWeightSum α L X := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX
  have hlogX : ∀ᶠ X in atTop, C / c ≤ Real.log X := by
    have := Real.tendsto_log_atTop.eventually_ge_atTop (C / c)
    exact this
  filter_upwards [hπ, hWr, hLr, hWpos, hlogX, eventually_gt_atTop (1 : ℝ)] with
    X hXπ hXW hXL hXWpos hXlog hX1
  intro t ht1 ht2
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hlX : 0 < Real.log X := Real.log_pos hX1
  have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht1
  have hLX : 0 < L X := hL.pos _ hX0
  have hv : t / X ∈ Set.Icc a b := by
    constructor
    · rw [le_div_iff₀ hX0]; nlinarith only [ht1]
    · rw [div_le_iff₀ hX0]; nlinarith only [ht2]
  have hvX : (t / X) * X = t := by field_simp
  -- the four ratios
  rw [Real.dist_eq, abs_le] at hXπ hXW
  have hLratio := hXL (t / X) hv
  rw [hvX, abs_le] at hLratio
  have hlogratio : |Real.log t / Real.log X - 1| ≤ c := by
    have hlt : Real.log t = Real.log X + Real.log (t / X) := by
      rw [Real.log_div ht0.ne' hX0.ne']
      ring
    have hbnd : |Real.log (t / X)| ≤ C := by
      rw [abs_le]
      constructor
      · have h1 : Real.log a ≤ Real.log (t / X) := Real.log_le_log ha hv.1
        have h2 : -|Real.log a| ≤ Real.log a := neg_abs_le _
        have h3 : |Real.log a| ≤ C := le_max_left _ _
        linarith
      · have h1 : Real.log (t / X) ≤ Real.log b :=
          Real.log_le_log (by positivity) hv.2
        have h2 : Real.log b ≤ |Real.log b| := le_abs_self _
        have h3 : |Real.log b| ≤ C := le_max_right _ _
        linarith
    have hid : Real.log t / Real.log X - 1 = Real.log (t / X) / Real.log X := by
      rw [hlt]
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hlX, div_le_iff₀ hlX]
    rw [div_le_iff₀ hc0] at hXlog
    nlinarith only [hbnd, hXlog, hc0]
  rw [abs_le] at hlogratio
  -- assemble
  have hdecomp := rvNormReal_eq hα1 (L := L) hX1 ht0 hLX.ne' hXWpos.ne'
  have f1 : 1 - c ≤ rvPrimeCount X / (X / Real.log X) := by linarith [hXπ.1]
  have f1' : rvPrimeCount X / (X / Real.log X) ≤ 1 + c := by linarith [hXπ.2]
  have f2 : 1 - c ≤ Real.log t / Real.log X := by linarith [hlogratio.1]
  have f2' : Real.log t / Real.log X ≤ 1 + c := by linarith [hlogratio.2]
  have f3 : 1 - c ≤ L t / L X := by linarith [hLratio.1]
  have f3' : L t / L X ≤ 1 + c := by linarith [hLratio.2]
  have f4 : 1 - c ≤ X ^ (1 - α) * L X / ((1 - α) * rvWeightSum α L X) := by linarith [hXW.1]
  have f4' : X ^ (1 - α) * L X / ((1 - α) * rvWeightSum α L X) ≤ 1 + c := by linarith [hXW.2]
  have hprod := four_factor_bounds (c := c) hc1.le f1 f1' f2 f2' f3 f3' f4 f4'
  have hw0 : 0 ≤ weightProfile α (t / X) :=
    weightProfile_nonneg hα1 (by positivity)
  rw [hdecomp]
  constructor
  · calc (1 - c) ^ 4 * weightProfile α (t / X)
        = weightProfile α (t / X) * (1 - c) ^ 4 := by ring
      _ ≤ weightProfile α (t / X) * (rvPrimeCount X / (X / Real.log X)
            * (Real.log t / Real.log X) * (L t / L X)
            * (X ^ (1 - α) * L X / ((1 - α) * rvWeightSum α L X))) :=
          mul_le_mul_of_nonneg_left hprod.1 hw0
  · calc weightProfile α (t / X) * (rvPrimeCount X / (X / Real.log X)
          * (Real.log t / Real.log X) * (L t / L X)
          * (X ^ (1 - α) * L X / ((1 - α) * rvWeightSum α L X)))
        ≤ weightProfile α (t / X) * (1 + c) ^ 4 := mul_le_mul_of_nonneg_left hprod.2 hw0
      _ = (1 + c) ^ 4 * weightProfile α (t / X) := by ring

end

end RHTower
