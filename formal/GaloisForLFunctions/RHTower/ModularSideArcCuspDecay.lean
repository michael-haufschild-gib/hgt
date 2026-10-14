import GaloisForLFunctions.RHTower.ModularSideArcAnnihilatingMeasure

/-!
# Annihilation forces rapid decay at the cusp

Let `μ` be a finite measure on the side-arc parameter `s ∈ [−½, ½]` (height `y(s) = √(2|s| − s²)`,
cusp `s = 0`) with `∫ C̃_n dμ = 0` for every normalized Whittaker mode
`C̃_n(s) = ρ_n(y) cos(c_n s)`, `ρ_n(y) = K₀(c_n y)/K₀(c_0 y)`, `c_n = 2π(n+1)`.  Put
`w(s) = 1/K₀(c_0 y(s))` (`sideKWeight`, `0` at the cusp).

**Shell bound** (`integral_sideKWeight_shell_le`).
`∫_{y ≤ 1/c_n} w dμ ≤ μ([−½,½]) e^{−(c_n − c_0)/√c_n} / (K₀(1) cos 1)`.

Proof.  Pointwise, `C̃_n ≥ K₀(1) cos(1) w 1_{y ≤ 1/c_n} − e^{−(c_n − c_0)/√c_n}`:
* near the cusp `|s| ≤ y²`, so `|c_n s| ≤ c_n y² ≤ 1` while `y ≤ c_n^{−1/2}`, and `C̃_n ≥ 0` there;
* for `y ≤ 1/c_n` moreover `K₀(c_n y) ≥ K₀(1)`, so `C̃_n ≥ K₀(1) cos(1) w`;
* for `y > c_n^{−1/2}`, `|C̃_n| ≤ ρ_n(y) ≤ e^{−(c_n − c_0) y}`.
Integrate against `μ` and use `∫ C̃_n dμ = 0`.

**Theorem** (`integrable_sideKWeight_div_height_sq`).  `w/y²` is `μ`-integrable.  On the shell
`1/c_{n+1} < y ≤ 1/c_n` one has `1/y² < c_{n+1}²`, and `Σ c_{n+1}² e^{−(c_n − c_0)/√c_n} < ∞`
because `e^{−x} ≤ 8!/x⁸` and `(c_n − c_0)/√c_n ≥ √(πn)`.

So the side-arc annihilating measure carries, after division by `K₀(c_0 y)`, less mass near the
cusp than any power of `y`; the `s = ½` generators attached to it are then integrable against every
weight used below.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- The weight `w(s) = 1/K₀(c_0 y(s))`, with `w = 0` at the cusp. -/
def sideKWeight (s : ℝ) : ℝ :=
  if sideArcHeight s = 0 then 0 else (kMoment 0 (arcFreq 0 * sideArcHeight s))⁻¹

theorem sideKWeight_nonneg (s : ℝ) : 0 ≤ sideKWeight s := by
  unfold sideKWeight
  split_ifs
  · exact le_refl 0
  · exact inv_nonneg.mpr (kMoment_nonneg 0 _)

theorem sideArcHeight_le {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    sideArcHeight s ≤ Real.sqrt (3 / 4) := by
  unfold sideArcHeight
  apply Real.sqrt_le_sqrt
  have h := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  rw [← sq_abs]
  nlinarith [abs_nonneg s]

theorem abs_le_sideArcHeight_sq {s : ℝ} (hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |s| ≤ sideArcHeight s ^ 2 := by
  rw [sideArcHeight_sq hs]
  have h := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  rw [← sq_abs]
  nlinarith [abs_nonneg s]

theorem kRatio_ge (n : ℕ) {y : ℝ} (hy : 0 < y) (hny : arcFreq n * y ≤ 1) :
    kMoment 0 1 * (kMoment 0 (arcFreq 0 * y))⁻¹ ≤ kRatio n y := by
  rw [kRatio_of_ne hy.ne', div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (WeilHigherDenominator.kMoment_zero_antitone (mul_pos (arcFreq_pos n) hy) hny)
    (inv_nonneg.mpr (kMoment_nonneg 0 _))

/-- The exponential shell constant `e^{−(c_n − c_0)/√c_n}`. -/
def shellExp (n : ℕ) : ℝ := Real.exp (-((arcFreq n - arcFreq 0) / Real.sqrt (arcFreq n)))

theorem shellExp_nonneg (n : ℕ) : 0 ≤ shellExp n := (Real.exp_pos _).le

/-- **Pointwise lower bound** for the normalized cosine mode. -/
theorem sideCosMode_ge (n : ℕ) (s : ArcParam) :
    Real.cos 1 * kMoment 0 1 * ({t : ArcParam | sideArcHeight t ≤ 1 / arcFreq n}.indicator
      (fun t => sideKWeight t) s) - shellExp n ≤ sideCosMode n s := by
  have hcn := arcFreq_pos n
  have hcos1 := Real.cos_one_pos
  have hK1 := kMoment_nonneg 0 1
  have hE := shellExp_nonneg n
  set y := sideArcHeight s with hydef
  have hy0 : 0 ≤ y := sideArcHeight_nonneg _
  have hsy : |(s : ℝ)| ≤ y ^ 2 := abs_le_sideArcHeight_sq s.2
  rw [sideCosMode_apply]
  rcases hy0.eq_or_lt with hyz | hypos
  · -- the cusp
    have hw : sideKWeight s = 0 := by simp [sideKWeight, ← hydef, ← hyz]
    have hs0 : (s : ℝ) = 0 := by
      have := abs_nonneg (s : ℝ)
      have h2 : |(s : ℝ)| ≤ 0 := by rw [← hyz] at hsy; simpa using hsy
      exact abs_eq_zero.mp (le_antisymm h2 this)
    rw [← hydef, ← hyz, kRatio_zero, hs0, mul_zero, Real.cos_zero]
    by_cases hmem : s ∈ {t : ArcParam | sideArcHeight t ≤ 1 / arcFreq n}
    · rw [indicator_of_mem hmem, hw]; linarith
    · rw [indicator_of_notMem hmem]; linarith
  · have hw : sideKWeight s = (kMoment 0 (arcFreq 0 * y))⁻¹ := by
      simp [sideKWeight, ← hydef, hypos.ne']
    have hR0 := kRatio_nonneg n y
    by_cases hnear : y ≤ 1 / Real.sqrt (arcFreq n)
    · -- near the cusp the cosine is nonnegative
      have hsq : 0 < Real.sqrt (arcFreq n) := Real.sqrt_pos.mpr hcn
      have hcy2 : arcFreq n * y ^ 2 ≤ 1 := by
        have h1 : y ^ 2 ≤ (1 / Real.sqrt (arcFreq n)) ^ 2 := pow_le_pow_left₀ hy0 hnear 2
        rw [div_pow, one_pow, Real.sq_sqrt hcn.le] at h1
        calc arcFreq n * y ^ 2 ≤ arcFreq n * (1 / arcFreq n) := mul_le_mul_of_nonneg_left h1 hcn.le
          _ = 1 := by field_simp
      have hcs : |arcFreq n * (s : ℝ)| ≤ 1 := by
        rw [abs_mul, abs_of_pos hcn]
        calc arcFreq n * |(s : ℝ)| ≤ arcFreq n * y ^ 2 := mul_le_mul_of_nonneg_left hsy hcn.le
          _ ≤ 1 := hcy2
      have hcosge : Real.cos 1 ≤ Real.cos (arcFreq n * s) := by
        rw [← Real.cos_abs (arcFreq n * s)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
          hcs
      have hcosnn : 0 ≤ Real.cos (arcFreq n * s) := hcos1.le.trans hcosge
      by_cases hmem : s ∈ {t : ArcParam | sideArcHeight t ≤ 1 / arcFreq n}
      · rw [indicator_of_mem hmem, hw]
        have hmem' : y ≤ 1 / arcFreq n := hmem
        have hny : arcFreq n * y ≤ 1 := by
          calc arcFreq n * y ≤ arcFreq n * (1 / arcFreq n) := mul_le_mul_of_nonneg_left hmem' hcn.le
            _ = 1 := by field_simp
        have hR := kRatio_ge n hypos hny
        have hinv : 0 ≤ (kMoment 0 (arcFreq 0 * y))⁻¹ := inv_nonneg.mpr (kMoment_nonneg 0 _)
        calc Real.cos 1 * kMoment 0 1 * (kMoment 0 (arcFreq 0 * y))⁻¹ - shellExp n
            ≤ Real.cos 1 * (kMoment 0 1 * (kMoment 0 (arcFreq 0 * y))⁻¹) := by
              rw [mul_assoc]; linarith
          _ ≤ Real.cos (arcFreq n * s) * kRatio n y :=
              mul_le_mul hcosge hR (by positivity) hcosnn
          _ = kRatio n y * Real.cos (arcFreq n * s) := mul_comm _ _
      · rw [indicator_of_notMem hmem, mul_zero, zero_sub]
        have := mul_nonneg hR0 hcosnn
        linarith
    · -- away from the cusp the ratio is exponentially small
      have hfar : 1 / Real.sqrt (arcFreq n) < y := lt_of_not_ge hnear
      have hsq : 0 < Real.sqrt (arcFreq n) := Real.sqrt_pos.mpr hcn
      have hnot : s ∉ {t : ArcParam | sideArcHeight t ≤ 1 / arcFreq n} := by
        intro hmem
        have hmem' : y ≤ 1 / arcFreq n := hmem
        have h1 : 1 / arcFreq n ≤ 1 / Real.sqrt (arcFreq n) := by
          apply one_div_le_one_div_of_le hsq
          have h2 : 1 ≤ arcFreq n := by
            have := two_pi_le_arcFreq n; nlinarith [Real.pi_gt_three]
          calc Real.sqrt (arcFreq n) ≤ Real.sqrt (arcFreq n) * Real.sqrt (arcFreq n) :=
                le_mul_of_one_le_right hsq.le (Real.one_le_sqrt.mpr h2)
            _ = arcFreq n := Real.mul_self_sqrt hcn.le
        linarith
      rw [indicator_of_notMem hnot, mul_zero, zero_sub]
      have hRle := kRatio_le_exp n hypos
      have hexp : Real.exp (-(arcFreq n * y - arcFreq 0 * y)) ≤ shellExp n := by
        unfold shellExp
        apply Real.exp_le_exp.mpr
        have hd : 0 ≤ arcFreq n - arcFreq 0 := by linarith [arcFreq_zero_le n]
        have : (arcFreq n - arcFreq 0) / Real.sqrt (arcFreq n) ≤ (arcFreq n - arcFreq 0) * y := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_left hfar.le hd
        linarith
      have habs : |kRatio n y * Real.cos (arcFreq n * s)| ≤ shellExp n := by
        rw [abs_mul, abs_of_nonneg hR0]
        calc kRatio n y * |Real.cos (arcFreq n * s)| ≤ kRatio n y * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hR0
          _ ≤ shellExp n := by rw [mul_one]; exact hRle.trans hexp
      linarith [neg_abs_le (kRatio n y * Real.cos (arcFreq n * s))]

/-- `y ↦ 1/K₀(c_0 y)`, extended by `0` at `y = 0`. -/
def kInvWeight (y : ℝ) : ℝ := if y = 0 then 0 else (kMoment 0 (arcFreq 0 * y))⁻¹

theorem sideKWeight_eq (s : ℝ) : sideKWeight s = kInvWeight (sideArcHeight s) := rfl

theorem continuousOn_kInvWeight : ContinuousOn kInvWeight (Ici 0) := by
  intro y hy
  rcases (mem_Ici.mp hy).eq_or_lt with h | h
  · rw [← h, ← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have hz : kInvWeight 0 = 0 := by simp [kInvWeight]
    rw [hz]
    have hlin : Tendsto (fun y : ℝ => arcFreq 0 * y) (𝓝[>] 0) (𝓝[>] 0) := by
      have hc : ContinuousWithinAt (fun y : ℝ => arcFreq 0 * y) (Ioi 0) 0 :=
        (continuous_const.mul continuous_id).continuousWithinAt
      have := hc.tendsto_nhdsWithin (t := Ioi 0) fun y hy => mul_pos (arcFreq_pos 0) hy
      simpa using this
    have hlim := (tendsto_kMoment_zero_nhdsGT.comp hlin).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (y : ℝ) ≠ 0 := (show (0 : ℝ) < y from hy).ne'
    simp [kInvWeight, hy0]
  · have hev : kInvWeight =ᶠ[𝓝 y] fun y => (kMoment 0 (arcFreq 0 * y))⁻¹ := by
      filter_upwards [lt_mem_nhds h] with z hz
      simp [kInvWeight, hz.ne']
    refine (ContinuousAt.congr ?_ hev.symm).continuousWithinAt
    have hc2 : ContinuousAt (fun y => kMoment 0 (arcFreq 0 * y)) y :=
      ((continuousOn_kMoment 0).continuousAt (Ioi_mem_nhds (mul_pos (arcFreq_pos 0) h))).comp
        (continuous_const.mul continuous_id).continuousAt
    exact hc2.inv₀ (kMoment_zero_pos_of_pos (mul_pos (arcFreq_pos 0) h)).ne'

theorem continuous_sideKWeight : Continuous fun s : ArcParam => sideKWeight s :=
  continuousOn_kInvWeight.comp_continuous (continuous_sideArcHeight.comp continuous_subtype_val)
    fun _ => sideArcHeight_nonneg _

/-- The shell `{y ≤ 1/c_n}` around the cusp. -/
def sideShell (n : ℕ) : Set ArcParam := {t | sideArcHeight t ≤ 1 / arcFreq n}

theorem measurableSet_sideShell (n : ℕ) : MeasurableSet (sideShell n) :=
  (isClosed_le (continuous_sideArcHeight.comp continuous_subtype_val)
    continuous_const).measurableSet

theorem integrable_sideKWeight (μ : Measure ArcParam) [IsFiniteMeasure μ] :
    Integrable (fun t : ArcParam => sideKWeight t) μ :=
  (BoundedContinuousFunction.mkOfCompact ⟨_, continuous_sideKWeight⟩).integrable μ

theorem integrable_sideShell_indicator (μ : Measure ArcParam) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable ((sideShell n).indicator fun t => sideKWeight t) μ :=
  (integrable_sideKWeight μ).indicator (measurableSet_sideShell n)

/-- **Shell bound.** -/
theorem integral_sideKWeight_shell_le (μ : Measure ArcParam) [IsFiniteMeasure μ]
    (h : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) (n : ℕ) :
    Real.cos 1 * kMoment 0 1 * ∫ s, (sideShell n).indicator (fun t => sideKWeight t) s ∂μ ≤
      shellExp n * μ.real univ := by
  have hint := integrable_sideShell_indicator μ n
  have hle : ∫ s, (Real.cos 1 * kMoment 0 1 *
      (sideShell n).indicator (fun t => sideKWeight t) s - shellExp n) ∂μ ≤
        ∫ s, sideCosMode n s ∂μ :=
    integral_mono ((hint.const_mul _).sub (integrable_const _)) ((sideCosMode n).integrable μ)
      fun s => sideCosMode_ge n s
  rw [h n, integral_sub (hint.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, smul_eq_mul] at hle
  linarith

/-- `e^{−x} ≤ 8!/x⁸` for `x > 0`. -/
theorem exp_neg_le_div_pow_eight {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 40320 / x ^ 8 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 8
  have h8 : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [h8] at h
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  have he := Real.exp_pos x
  calc (Real.exp x)⁻¹ * x ^ 8 = x ^ 8 / Real.exp x := by ring
    _ ≤ 40320 := by
        rw [div_le_iff₀ he]
        linarith [(div_le_iff₀ (by norm_num : (0 : ℝ) < 40320)).mp h]

/-- `c_{n+1}² e^{−(c_n − c_0)/√c_n} ≤ 10⁶/(n+1)²`. -/
theorem arcFreq_succ_sq_mul_shellExp_le (n : ℕ) :
    arcFreq (n + 1) ^ 2 * shellExp n ≤ 1000000 / ((n : ℝ) + 1) ^ 2 := by
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · unfold shellExp arcFreq
    simp only [Nat.cast_zero, zero_add, sub_self, zero_div, neg_zero, Real.exp_zero, mul_one]
    norm_num
    nlinarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcn : arcFreq n = 2 * Real.pi * ((n : ℝ) + 1) := rfl
    have hc0 : arcFreq 0 = 2 * Real.pi := by unfold arcFreq; simp
    set x := (arcFreq n - arcFreq 0) / Real.sqrt (arcFreq n) with hx
    have hsq : 0 < Real.sqrt (arcFreq n) := Real.sqrt_pos.mpr (arcFreq_pos n)
    have hx0 : 0 < x := by
      rw [hx, hcn, hc0]
      apply div_pos _ hsq
      nlinarith
    have hx2 : Real.pi * n ≤ x ^ 2 := by
      rw [hx, div_pow, Real.sq_sqrt (arcFreq_pos n).le, hcn, hc0,
        le_div_iff₀ (by positivity)]
      have : (2 * Real.pi * ((n : ℝ) + 1) - 2 * Real.pi) ^ 2 = 4 * Real.pi ^ 2 * n ^ 2 := by ring
      rw [this]
      have hp : 0 < Real.pi := Real.pi_pos
      nlinarith [mul_pos hp hp]
    have hexp := exp_neg_le_div_pow_eight hx0
    have hx8 : (Real.pi * n) ^ 4 ≤ x ^ 8 := by
      calc (Real.pi * n) ^ 4 ≤ (x ^ 2) ^ 4 := pow_le_pow_left₀ (by positivity) hx2 4
        _ = x ^ 8 := by ring
    have hpn : 0 < Real.pi * n := by positivity
    have hE : shellExp n ≤ 40320 / (Real.pi * n) ^ 4 := by
      unfold shellExp
      rw [← hx]
      exact hexp.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) hx8)
    have hcs : arcFreq (n + 1) = 2 * Real.pi * ((n : ℝ) + 2) := by
      unfold arcFreq; push_cast; ring
    rw [hcs]
    calc (2 * Real.pi * ((n : ℝ) + 2)) ^ 2 * shellExp n
        ≤ (2 * Real.pi * ((n : ℝ) + 2)) ^ 2 * (40320 / (Real.pi * n) ^ 4) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ 1000000 / ((n : ℝ) + 1) ^ 2 := by
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
          have hp : 0 < Real.pi := Real.pi_pos
          have h9 : 9 ≤ Real.pi ^ 2 := by nlinarith
          have hn2 : ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ 36 * (n : ℝ) ^ 4 := by
            have h3 : (n : ℝ) + 2 ≤ 3 * n := by linarith
            have h2 : (n : ℝ) + 1 ≤ 2 * n := by linarith
            calc ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2 ≤ (3 * (n : ℝ)) ^ 2 * (2 * (n : ℝ)) ^ 2 := by
                  gcongr
              _ = 36 * (n : ℝ) ^ 4 := by ring
          have key : 4 * 40320 * (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2) ≤
              1000000 * Real.pi ^ 2 * (n : ℝ) ^ 4 := by
            have : 4 * 40320 * 36 ≤ 1000000 * 9 := by norm_num
            have hn4 : 0 ≤ (n : ℝ) ^ 4 := by positivity
            nlinarith
          calc (2 * Real.pi * ((n : ℝ) + 2)) ^ 2 * 40320 * ((n : ℝ) + 1) ^ 2
              = Real.pi ^ 2 * (4 * 40320 * (((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 1) ^ 2)) := by ring
            _ ≤ Real.pi ^ 2 * (1000000 * Real.pi ^ 2 * (n : ℝ) ^ 4) :=
                mul_le_mul_of_nonneg_left key (by positivity)
            _ = 1000000 * (Real.pi * n) ^ 4 := by ring

theorem summable_arcFreq_succ_sq_mul_shellExp :
    Summable fun n : ℕ => arcFreq (n + 1) ^ 2 * shellExp n := by
  have hs : Summable fun n : ℕ => (1000000 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    have h' : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by simpa using h
    exact (h'.mul_left 1000000).congr fun n => by ring
  exact Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (shellExp_nonneg n))
    arcFreq_succ_sq_mul_shellExp_le hs

/-- Pointwise: `w/y² ≤ c_0² w + Σ_n c_{n+1}² w 1_{y ≤ 1/c_n}`. -/
theorem ofReal_sideKWeight_div_sq_le (s : ArcParam) :
    ENNReal.ofReal (sideKWeight s / sideArcHeight s ^ 2) ≤
      ENNReal.ofReal (arcFreq 0 ^ 2 * sideKWeight s) +
        ∑' n : ℕ, ENNReal.ofReal (arcFreq (n + 1) ^ 2 *
          (sideShell n).indicator (fun t => sideKWeight t) s) := by
  set y := sideArcHeight s with hy
  have hy0 : 0 ≤ y := sideArcHeight_nonneg _
  have hw0 := sideKWeight_nonneg s
  have hc0 := arcFreq_pos 0
  rcases hy0.eq_or_lt with hyz | hypos
  · rw [← hyz, zero_pow two_ne_zero, div_zero, ENNReal.ofReal_zero]; exact bot_le
  by_cases hfar : 1 / arcFreq 0 < y
  · refine le_trans ?_ le_self_add
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (pow_pos hypos 2)]
    have : 1 < arcFreq 0 * y := by
      rw [div_lt_iff₀ hc0] at hfar; linarith
    have h1 : 1 ≤ (arcFreq 0 * y) ^ 2 := by nlinarith
    calc sideKWeight s = sideKWeight s * 1 := (mul_one _).symm
      _ ≤ sideKWeight s * (arcFreq 0 * y) ^ 2 := mul_le_mul_of_nonneg_left h1 hw0
      _ = arcFreq 0 ^ 2 * sideKWeight s * y ^ 2 := by ring
  · rw [not_lt] at hfar
    set k : ℕ := ⌊1 / (arcFreq 0 * y)⌋₊ with hk
    have hA : 1 ≤ 1 / (arcFreq 0 * y) := by
      rw [le_div_iff₀ (mul_pos hc0 hypos), one_mul]
      rw [le_div_iff₀ hc0] at hfar; linarith
    have hk1 : 1 ≤ k := Nat.floor_pos.mpr hA
    set n := k - 1 with hn
    have hnk : n + 1 = k := Nat.sub_one_add_one (by omega)
    have hfl := Nat.floor_le (le_trans zero_le_one hA)
    have hfl2 := Nat.lt_floor_add_one (1 / (arcFreq 0 * y))
    rw [← hk] at hfl hfl2
    have hkcast : ((n : ℝ) + 1) = (k : ℝ) := by exact_mod_cast hnk
    have hcn : arcFreq n = ((n : ℝ) + 1) * arcFreq 0 := arcFreq_eq_mul n
    have hcs : arcFreq (n + 1) = ((k : ℝ) + 1) * arcFreq 0 := by
      rw [arcFreq_eq_mul (n + 1)]; push_cast; rw [hkcast]
    have hmem : s ∈ sideShell n := by
      show sideArcHeight s ≤ 1 / arcFreq n
      rw [← hy, hcn, hkcast, le_div_iff₀ (by positivity)]
      have h1 : (k : ℝ) ≤ 1 / (arcFreq 0 * y) := hfl
      rw [le_div_iff₀ (mul_pos hc0 hypos)] at h1
      linarith
    refine le_trans ?_ (le_add_left (ENNReal.le_tsum n))
    rw [indicator_of_mem hmem]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (pow_pos hypos 2), hcs]
    have h2 : 1 / (arcFreq 0 * y) < (k : ℝ) + 1 := hfl2
    rw [div_lt_iff₀ (mul_pos hc0 hypos)] at h2
    have h3 : 1 ≤ (((k : ℝ) + 1) * arcFreq 0 * y) ^ 2 := by nlinarith
    calc sideKWeight s = sideKWeight s * 1 := (mul_one _).symm
      _ ≤ sideKWeight s * (((k : ℝ) + 1) * arcFreq 0 * y) ^ 2 := mul_le_mul_of_nonneg_left h3 hw0
      _ = (((k : ℝ) + 1) * arcFreq 0) ^ 2 * sideKWeight s * y ^ 2 := by ring

/-- **Integrability of `w/y²`.** -/
theorem integrable_sideKWeight_div_height_sq (μ : Measure ArcParam) [IsFiniteMeasure μ]
    (h : ∀ n, ∫ s, sideCosMode n s ∂μ = 0) :
    Integrable (fun s : ArcParam => sideKWeight s / sideArcHeight s ^ 2) μ := by
  have hmeas : Measurable fun s : ArcParam => sideKWeight s / sideArcHeight s ^ 2 :=
    continuous_sideKWeight.measurable.div
      ((continuous_sideArcHeight.comp continuous_subtype_val).measurable.pow_const 2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun s =>
    div_nonneg (sideKWeight_nonneg _) (sq_nonneg _))]
  have hcos := Real.cos_one_pos
  have hK1 := kMoment_zero_pos_of_pos one_pos
  set D := Real.cos 1 * kMoment 0 1 with hD
  have hD0 : 0 < D := mul_pos hcos hK1
  have hshell : ∀ n, ∫ s, (sideShell n).indicator (fun t => sideKWeight t) s ∂μ ≤
      shellExp n * μ.real univ / D := fun n => by
    rw [le_div_iff₀ hD0, mul_comm]; exact integral_sideKWeight_shell_le μ h n
  have hmeasn : ∀ n : ℕ, AEMeasurable (fun s : ArcParam => ENNReal.ofReal (arcFreq (n + 1) ^ 2 *
      (sideShell n).indicator (fun t => sideKWeight t) s)) μ := fun n =>
    (ENNReal.measurable_ofReal.comp (measurable_const.mul
      (continuous_sideKWeight.measurable.indicator (measurableSet_sideShell n)))).aemeasurable
  calc ∫⁻ s, ENNReal.ofReal (sideKWeight s / sideArcHeight s ^ 2) ∂μ
      ≤ ∫⁻ s, (ENNReal.ofReal (arcFreq 0 ^ 2 * sideKWeight s) +
          ∑' n : ℕ, ENNReal.ofReal (arcFreq (n + 1) ^ 2 *
            (sideShell n).indicator (fun t => sideKWeight t) s)) ∂μ :=
        lintegral_mono fun s => ofReal_sideKWeight_div_sq_le s
    _ = ∫⁻ s, ENNReal.ofReal (arcFreq 0 ^ 2 * sideKWeight s) ∂μ +
          ∑' n : ℕ, ∫⁻ s, ENNReal.ofReal (arcFreq (n + 1) ^ 2 *
            (sideShell n).indicator (fun t => sideKWeight t) s) ∂μ := by
        rw [lintegral_add_left
          (f := fun s : ArcParam => ENNReal.ofReal (arcFreq 0 ^ 2 * sideKWeight s))
          (ENNReal.measurable_ofReal.comp (measurable_const.mul continuous_sideKWeight.measurable)),
          lintegral_tsum hmeasn]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
        · rw [← ofReal_integral_eq_lintegral_ofReal
            ((integrable_sideKWeight μ).const_mul _)
            (Eventually.of_forall fun s => mul_nonneg (sq_nonneg _) (sideKWeight_nonneg s))]
          exact ENNReal.ofReal_lt_top
        · have hterm : ∀ n : ℕ, ∫⁻ s, ENNReal.ofReal (arcFreq (n + 1) ^ 2 *
              (sideShell n).indicator (fun t => sideKWeight t) s) ∂μ ≤
              ENNReal.ofReal (arcFreq (n + 1) ^ 2 * shellExp n * (μ.real univ / D)) := by
            intro n
            have hnn : ∀ s, 0 ≤ arcFreq (n + 1) ^ 2 *
                (sideShell n).indicator (fun t => sideKWeight t) s := fun s =>
              mul_nonneg (sq_nonneg _)
                (indicator_nonneg (s := sideShell n) (f := fun t : ArcParam => sideKWeight t)
                  (fun t _ => sideKWeight_nonneg t) s)
            rw [← ofReal_integral_eq_lintegral_ofReal
              ((integrable_sideShell_indicator μ n).const_mul _) (Eventually.of_forall hnn)]
            apply ENNReal.ofReal_le_ofReal
            rw [integral_const_mul, mul_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            rw [← mul_div_assoc]
            exact hshell n
          refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) ?_
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
            have := shellExp_nonneg n
            have : 0 ≤ μ.real univ / D := div_nonneg measureReal_nonneg hD0.le
            positivity) (summable_arcFreq_succ_sq_mul_shellExp.mul_right _)]
          exact ENNReal.ofReal_lt_top

end

end RHTower
