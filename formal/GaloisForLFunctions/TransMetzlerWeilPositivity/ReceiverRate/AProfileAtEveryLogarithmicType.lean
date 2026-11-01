import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# A compact profile at every logarithmic Denjoy–Carleman type

The radii `(1/√log(j+3) − 1/√log(j+4))/8` telescope. Iterated Steklov
averages therefore have a smooth compactly supported unit-mass limit.
The reciprocal radius products have the logarithmic weight multiplied by
`(64/√log(q+3))^q`, allowing every positive exponential derivative constant.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ContDiff
namespace GaloisForLFunctions.TransMetzlerWeilPositivity
open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

private theorem inv_sqrt_sub_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) / (2 * b * Real.sqrt b) ≤ 1 / Real.sqrt a - 1 / Real.sqrt b := by
  have hb : 0 < b := ha.trans_le hab
  have hA := Real.sqrt_pos.mpr ha
  have hB := Real.sqrt_pos.mpr hb
  have hAB := Real.sqrt_le_sqrt hab
  have hsum : 0 < Real.sqrt b + Real.sqrt a := add_pos hB hA
  have hrat : 1 / Real.sqrt a - 1 / Real.sqrt b =
      (b - a) / (Real.sqrt a * Real.sqrt b * (Real.sqrt b + Real.sqrt a)) := by
    have hsq : (Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a) = b - a := by
      nlinarith only [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
    rw [← hsq]
    field_simp
  rw [hrat]
  apply div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (by positivity)
  have hprod : Real.sqrt a * Real.sqrt b ≤ b := by
    calc _ ≤ Real.sqrt b * Real.sqrt b := mul_le_mul_of_nonneg_right hAB hB.le
      _ = b := by rw [← sq, Real.sq_sqrt hb.le]
  calc Real.sqrt a * Real.sqrt b * (Real.sqrt b + Real.sqrt a)
      ≤ b * (2 * Real.sqrt b) :=
        mul_le_mul hprod (by linarith only [hAB]) hsum.le hb.le
    _ = 2 * b * Real.sqrt b := by ring

def beurlingRadius (m : ℕ) : ℝ :=
  (1 / Real.sqrt (Real.log ((m : ℝ) + 3)) -
    1 / Real.sqrt (Real.log ((m : ℝ) + 4))) / 8

private theorem log_add_three_ge_one (m : ℕ) : 1 ≤ Real.log ((m : ℝ) + 3) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  linarith only [he, Nat.cast_nonneg (α := ℝ) m]

theorem beurlingRadius_lower (m : ℕ) :
    1 / (16 * ((m : ℝ) + 4) * Real.log ((m : ℝ) + 4) *
      Real.sqrt (Real.log ((m : ℝ) + 4))) ≤ beurlingRadius m := by
  have hm3 : (0 : ℝ) < (m : ℝ) + 3 := by positivity
  have hm4 : (0 : ℝ) < (m : ℝ) + 4 := by positivity
  have hl3 : 0 < Real.log ((m : ℝ) + 3) := zero_lt_one.trans_le (log_add_three_ge_one m)
  have hl4 : 0 < Real.log ((m : ℝ) + 4) := Real.log_pos (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  have hlog : Real.log ((m : ℝ) + 3) ≤ Real.log ((m : ℝ) + 4) :=
    Real.log_le_log hm3 (by linarith)
  have hgap : 1 / ((m : ℝ) + 4) ≤ Real.log ((m : ℝ) + 4) - Real.log ((m : ℝ) + 3) := by
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hm4 hm3)
    rw [inv_div, Real.log_div hm4.ne' hm3.ne'] at h
    have he : 1 - ((m : ℝ) + 3) / ((m : ℝ) + 4) = 1 / ((m : ℝ) + 4) := by
      field_simp
      ring
    rwa [he] at h
  have hr := inv_sqrt_sub_ge hl3 hlog
  unfold beurlingRadius
  calc 1 / (16 * ((m : ℝ) + 4) * Real.log ((m : ℝ) + 4) * Real.sqrt (Real.log ((m : ℝ) + 4)))
      = ((1 / ((m : ℝ) + 4)) /
        (2 * Real.log ((m : ℝ) + 4) * Real.sqrt (Real.log ((m : ℝ) + 4)))) / 8 := by
          field_simp
          ring
    _ ≤ ((Real.log ((m : ℝ) + 4) - Real.log ((m : ℝ) + 3)) /
        (2 * Real.log ((m : ℝ) + 4) * Real.sqrt (Real.log ((m : ℝ) + 4)))) / 8 := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hgap (by positivity)) (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_right hr (by norm_num)

theorem beurlingRadius_pos (m : ℕ) : 0 < beurlingRadius m := by
  have hl4 : 0 < Real.log ((m : ℝ) + 4) := Real.log_pos (by linarith only [Nat.cast_nonneg (α := ℝ) m])
  exact lt_of_lt_of_le (by positivity) (beurlingRadius_lower m)


/-- The remaining radius mass is bounded by the telescoping endpoint. -/
theorem sum_Ico_beurlingRadius_le {K M : ℕ} (hKM : K ≤ M) :
    ∑ m ∈ Finset.Ico K M, beurlingRadius m ≤
      1 / (8 * Real.sqrt (Real.log ((K : ℝ) + 3))) := by
  let T : ℕ → ℝ := fun m => 1 / (8 * Real.sqrt (Real.log ((m : ℝ) + 3)))
  have hr (m : ℕ) : beurlingRadius m = T m - T (m + 1) := by
    dsimp only [beurlingRadius, T]
    push_cast
    rw [show (m : ℝ) + 1 + 3 = (m : ℝ) + 4 by ring]
    ring
  have ht : (∑ m ∈ Finset.Ico K M, beurlingRadius m) = T K - T M := by
    calc (∑ m ∈ Finset.Ico K M, beurlingRadius m) =
        ∑ m ∈ Finset.Ico K M, ((-T (m + 1)) - (-T m)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [hr]
          ring
      _ = -T M - (-T K) := Finset.sum_Ico_sub (fun m => -T m) hKM
      _ = T K - T M := by ring
  rw [ht]
  have hM : 0 ≤ T M := by dsimp only [T]; positivity
  exact sub_le_self _ hM

theorem sum_range_beurlingRadius_le_half (M : ℕ) :
    ∑ m ∈ Finset.range M, beurlingRadius m ≤ 1 / 2 := by
  rw [← Nat.Ico_zero_eq_range]
  refine (sum_Ico_beurlingRadius_le (Nat.zero_le M)).trans ?_
  have hs : 1 ≤ Real.sqrt (Real.log (3 : ℝ)) := by
    simpa only [Nat.cast_zero, zero_add, Real.sqrt_one] using
      Real.sqrt_le_sqrt (log_add_three_ge_one 0)
  simp only [Nat.cast_zero, zero_add]
  rw [div_le_iff₀ (by positivity : 0 < 8 * Real.sqrt (Real.log (3 : ℝ)))]
  linarith only [hs]

/-- Iterated Steklov approximation sequence: `beurlingSeq 0 = steklovBase`,
`beurlingSeq (m + 1) = steklovAvg (beurlingRadius m) (beurlingSeq m)`. -/
def beurlingSeq : ℕ → ℝ → ℝ
  | 0 => steklovBase
  | m + 1 => steklovAvg (beurlingRadius m) (beurlingSeq m)

theorem contDiff_beurlingSeq (m : ℕ) : ContDiff ℝ ∞ (beurlingSeq m) := by
  induction m with
  | zero => exact contDiff_steklovBase
  | succ m ih => exact contDiff_steklovAvg ih (beurlingRadius_pos m)

theorem beurlingSeq_nonneg (m : ℕ) (x : ℝ) : 0 ≤ beurlingSeq m x := by
  induction m generalizing x with
  | zero =>
    unfold beurlingSeq steklovBase dilate dcProfile dcBump
    have h0 : 0 ≤ (∫ y, dcBump 1 y)⁻¹ :=
      inv_nonneg.mpr (integral_dcBump_pos odd_one).le
    have h1 := glueR_nonneg (r := 1) (1 + 2 * x)
    have h2 := glueR_nonneg (r := 1) (1 - 2 * x)
    positivity
  | succ m ih =>
    change 0 ≤ (2 * beurlingRadius m)⁻¹ *
      ∫ t in (-beurlingRadius m)..beurlingRadius m, beurlingSeq m (x + t)
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg two_pos.le (beurlingRadius_pos m).le))
      (intervalIntegral.integral_nonneg (by linarith only [beurlingRadius_pos m])
        (fun t _ => ih (x + t)))

theorem supportedIn_beurlingSeq_sum (m : ℕ) :
    SupportedIn (1 / 2 + ∑ j ∈ Finset.range m, beurlingRadius j) (beurlingSeq m) := by
  induction m with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, add_zero, beurlingSeq] using
      supportedIn_steklovBase
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc]
    exact supportedIn_steklovAvg (beurlingRadius_pos m) ih

theorem supportedIn_one_beurlingSeq (m : ℕ) : SupportedIn 1 (beurlingSeq m) := by
  intro x hx
  have hsum := sum_range_beurlingRadius_le_half m
  exact supportedIn_beurlingSeq_sum m x (by linarith)

theorem integral_beurlingSeq (m : ℕ) : ∫ x, beurlingSeq m x = 1 := by
  induction m with
  | zero => exact integral_steklovBase
  | succ m ih =>
    have hR : 0 ≤ 1 / 2 + ∑ j ∈ Finset.range m, beurlingRadius j :=
      add_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => (beurlingRadius_pos j).le)
    rw [beurlingSeq, integral_steklovAvg (contDiff_beurlingSeq m).continuous
      (supportedIn_beurlingSeq_sum m) hR (beurlingRadius_pos m), ih]

theorem abs_iteratedDeriv_beurlingSeq_le :
    ∀ (m q : ℕ), q ≤ m → ∀ x : ℝ,
      |iteratedDeriv q (beurlingSeq m) x| ≤
        steklovBaseSup * ∏ j ∈ Finset.range q, (beurlingRadius j)⁻¹
  | 0, q, hq, x => by
      have hq0 : q = 0 := Nat.le_zero.mp hq
      subst hq0
      simpa [beurlingSeq] using abs_steklovBase_le x
  | m + 1, q, hq, x => by
      rcases Nat.of_le_succ hq with hle | rfl
      · rw [beurlingSeq, iteratedDeriv_steklovAvg (contDiff_beurlingSeq m) (beurlingRadius_pos m) q]
        exact abs_steklovAvg_le (beurlingRadius_pos m)
          (abs_iteratedDeriv_beurlingSeq_le m q hle) x
      · rw [beurlingSeq, iteratedDeriv_succ,
          iteratedDeriv_steklovAvg (contDiff_beurlingSeq m) (beurlingRadius_pos m) m]
        have hcont : Continuous (iteratedDeriv m (beurlingSeq m)) :=
          (contDiff_beurlingSeq m).continuous_iteratedDeriv m (natCast_le_infty m)
        have hd := abs_deriv_steklovAvg_le hcont (beurlingRadius_pos m)
          (abs_iteratedDeriv_beurlingSeq_le m m le_rfl) x
        rw [Finset.prod_range_succ]
        linarith

private theorem abs_iteratedDeriv_beurlingSeq_step_le {q m : ℕ} (hqm : q + 1 ≤ m) (x : ℝ) :
    |iteratedDeriv q (beurlingSeq (m + 1)) x - iteratedDeriv q (beurlingSeq m) x| ≤
      (steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (beurlingRadius j)⁻¹) * beurlingRadius m := by
  rw [beurlingSeq, iteratedDeriv_steklovAvg (contDiff_beurlingSeq m) (beurlingRadius_pos m) q]
  have hsmooth : ContDiff ℝ ∞ (iteratedDeriv q (beurlingSeq m)) := by
    rw [iteratedDeriv_eq_iterate]
    exact (contDiff_beurlingSeq m).iterate_deriv q
  refine abs_steklovAvg_sub_self_le hsmooth (beurlingRadius_pos m) (fun y => ?_) x
  rw [← iteratedDeriv_succ]
  exact abs_iteratedDeriv_beurlingSeq_le m (q + 1) hqm y

private theorem abs_iteratedDeriv_beurlingSeq_sub_le {q K M : ℕ} (hqK : q + 1 ≤ K) (hKM : K ≤ M)
    (x : ℝ) :
    |iteratedDeriv q (beurlingSeq M) x - iteratedDeriv q (beurlingSeq K) x| ≤
      (steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (beurlingRadius j)⁻¹) /
        (8 * Real.sqrt (Real.log ((K : ℝ) + 3))) := by
  set C := steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (beurlingRadius j)⁻¹
  have hC0 : 0 ≤ C := mul_nonneg steklovBaseSup_pos.le
    (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (beurlingRadius_pos j).le)
  have htel : iteratedDeriv q (beurlingSeq M) x - iteratedDeriv q (beurlingSeq K) x =
      ∑ m ∈ Finset.Ico K M,
        (iteratedDeriv q (beurlingSeq (m + 1)) x - iteratedDeriv q (beurlingSeq m) x) :=
    (Finset.sum_Ico_sub (fun m => iteratedDeriv q (beurlingSeq m) x) hKM).symm
  calc |iteratedDeriv q (beurlingSeq M) x - iteratedDeriv q (beurlingSeq K) x|
      ≤ ∑ m ∈ Finset.Ico K M,
          |iteratedDeriv q (beurlingSeq (m + 1)) x - iteratedDeriv q (beurlingSeq m) x| := by
        rw [htel]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico K M, C * beurlingRadius m :=
        Finset.sum_le_sum fun m hm =>
          abs_iteratedDeriv_beurlingSeq_step_le (hqK.trans (Finset.mem_Ico.mp hm).1) x
    _ = C * ∑ m ∈ Finset.Ico K M, beurlingRadius m := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (1 / (8 * Real.sqrt (Real.log ((K : ℝ) + 3)))) :=
        mul_le_mul_of_nonneg_left (sum_Ico_beurlingRadius_le hKM) hC0
    _ = C / (8 * Real.sqrt (Real.log ((K : ℝ) + 3))) := by ring

theorem uniformCauchySeqOn_iteratedDeriv_beurlingSeq (q : ℕ) :
    UniformCauchySeqOn (fun m => iteratedDeriv q (beurlingSeq m)) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  set C := steklovBaseSup * ∏ j ∈ Finset.range (q + 1), (beurlingRadius j)⁻¹
  have hC0 : 0 ≤ C := mul_nonneg steklovBaseSup_pos.le
    (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (beurlingRadius_pos j).le)
  have htend : Tendsto (fun K : ℕ => C / (8 * Real.sqrt (Real.log ((K : ℝ) + 3)))) atTop (𝓝 0) := by
    have hlog : Tendsto (fun K : ℕ => 8 * Real.sqrt (Real.log ((K : ℝ) + 3))) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))).const_mul_atTop (by norm_num)
    exact tendsto_const_nhds.div_atTop hlog
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨max N₀ (q + 1), fun n hn m hm x _ => ?_⟩
  set K := max N₀ (q + 1)
  have hqK : q + 1 ≤ K := le_max_right _ _
  have hKlt : C / (8 * Real.sqrt (Real.log ((K : ℝ) + 3))) < ε / 2 := hN₀ K (le_max_left _ _)
  have hn' := abs_iteratedDeriv_beurlingSeq_sub_le hqK hn x
  have hm' := abs_iteratedDeriv_beurlingSeq_sub_le hqK hm x
  rw [Real.dist_eq]
  have htri : |iteratedDeriv q (beurlingSeq n) x - iteratedDeriv q (beurlingSeq m) x| ≤
      |iteratedDeriv q (beurlingSeq n) x - iteratedDeriv q (beurlingSeq K) x| +
        |iteratedDeriv q (beurlingSeq m) x - iteratedDeriv q (beurlingSeq K) x| := by
    have h := abs_sub (iteratedDeriv q (beurlingSeq n) x - iteratedDeriv q (beurlingSeq K) x)
      (iteratedDeriv q (beurlingSeq m) x - iteratedDeriv q (beurlingSeq K) x)
    rwa [sub_sub_sub_cancel_right] at h
  linarith

/-- Uniform limit family `(G_q)_{q ≥ 0}` of `(iteratedDeriv q (beurlingSeq m))_{m ≥ 0}`. -/
private def beurlingDerivLimit (q : ℕ) : ℝ → ℝ :=
  Classical.choose (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_beurlingSeq q))

private theorem tendstoUniformly_beurlingDerivLimit (q : ℕ) :
    TendstoUniformly (fun m => iteratedDeriv q (beurlingSeq m)) (beurlingDerivLimit q) atTop :=
  Classical.choose_spec (HTGeometry.exists_tendstoUniformly_of_uniformCauchySeq
    (uniformCauchySeqOn_iteratedDeriv_beurlingSeq q))

/-- The fixed unit profile obtained from the telescoping Steklov radii. -/
def beurlingDCProfile : ℝ → ℝ :=
  beurlingDerivLimit 0

theorem contDiff_beurlingDCProfile : ContDiff ℝ ∞ beurlingDCProfile :=
  HTGeometry.contDiff_infty_of_tendstoUniformly_iteratedDeriv
    contDiff_beurlingSeq tendstoUniformly_beurlingDerivLimit

theorem iteratedDeriv_beurlingDCProfile_eq (q : ℕ) :
    iteratedDeriv q beurlingDCProfile = beurlingDerivLimit q :=
  HTGeometry.iteratedDeriv_eq_of_tendstoUniformly_iteratedDeriv
    contDiff_beurlingSeq tendstoUniformly_beurlingDerivLimit q

theorem beurlingDCProfile_nonneg (x : ℝ) : 0 ≤ beurlingDCProfile x := by
  have hpt : Tendsto (fun m => beurlingSeq m x) atTop (𝓝 (beurlingDCProfile x)) := by
    simpa only [iteratedDeriv_zero, beurlingDCProfile] using
      (tendstoUniformly_beurlingDerivLimit 0).tendsto_at x
  exact ge_of_tendsto hpt (Filter.Eventually.of_forall fun m => beurlingSeq_nonneg m x)

theorem beurlingDCProfile_vanishesOff : VanishesOff beurlingDCProfile := by
  intro x hx
  have hpt : ∀ y, Tendsto (fun m => beurlingSeq m y) atTop (𝓝 (beurlingDCProfile y)) := by
    intro y
    simpa only [iteratedDeriv_zero, beurlingDCProfile] using
      (tendstoUniformly_beurlingDerivLimit 0).tendsto_at y
  exact HTGeometry.eq_zero_of_tendsto_of_forall_eq_zero (J := Set.Icc (-1 : ℝ) 1) hpt
    (fun m y hy => supportedIn_one_beurlingSeq m y (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
    (by
      intro hmem
      have := abs_le.mpr hmem
      linarith)

private theorem integral_eq_intervalIntegral_of_supportedIn {g : ℝ → ℝ} {R L : ℝ}
    (hsupp : SupportedIn R g) (hR : 0 ≤ R) (hRL : R < L) :
    (∫ x, g x) = ∫ x in (-L)..L, g x := by
  have hL0 : 0 < L := lt_of_le_of_lt hR hRL
  rw [intervalIntegral.integral_of_le (by linarith : -L ≤ L),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hx
  refine hsupp x ?_
  rcases hx with hx | hx
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem integral_beurlingDCProfile : ∫ x, beurlingDCProfile x = 1 := by
  have hvan : SupportedIn 1 beurlingDCProfile := beurlingDCProfile_vanishesOff
  rw [integral_eq_intervalIntegral_of_supportedIn
    hvan zero_le_one (by norm_num : (1 : ℝ) < 2)]
  have hseq_int : ∀ m : ℕ, (∫ x in (-2 : ℝ)..2, beurlingSeq m x) = 1 := by
    intro m
    rw [← integral_eq_intervalIntegral_of_supportedIn
      (supportedIn_one_beurlingSeq m) zero_le_one (by norm_num : (1 : ℝ) < 2),
      integral_beurlingSeq m]
  have htend : Tendsto (fun m : ℕ => ∫ x in (-2 : ℝ)..2, beurlingSeq m x) atTop
      (𝓝 (∫ x in (-2 : ℝ)..2, beurlingDCProfile x)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hunif := Metric.tendstoUniformly_iff.mp (tendstoUniformly_beurlingDerivLimit 0) (ε / 8)
      (by positivity)
    filter_upwards [hunif] with m hm
    rw [Real.dist_eq, ← intervalIntegral.integral_sub
      ((contDiff_beurlingSeq m).continuous.intervalIntegrable (-2) 2)
      (contDiff_beurlingDCProfile.continuous.intervalIntegrable (-2) 2),
      ← Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 8)
      (f := fun x => beurlingSeq m x - beurlingDCProfile x) (a := -2) (b := 2) fun x _ => by
        have hx := hm x
        simp only [iteratedDeriv_zero, Real.dist_eq] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hx.le
    rw [show (2 : ℝ) - (-2) = 4 by norm_num, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hle
    linarith
  exact tendsto_nhds_unique htend
    (Filter.Tendsto.congr (fun m => (hseq_int m).symm) tendsto_const_nhds)

private theorem inv_beurlingRadius_le (m : ℕ) :
    (beurlingRadius m)⁻¹ ≤ 16 * ((m : ℝ) + 4) * Real.log ((m : ℝ) + 4) *
      Real.sqrt (Real.log ((m : ℝ) + 4)) := by
  have hl : 0 < Real.log ((m : ℝ) + 4) := Real.log_pos (by
    linarith only [Nat.cast_nonneg (α := ℝ) m])
  apply (inv_le_comm₀ (beurlingRadius_pos m) (by positivity)).mpr
  simpa only [one_div] using beurlingRadius_lower m

/-- The derivative type tends to zero with the derivative order. -/
theorem prod_inv_beurlingRadius_le (q : ℕ) :
    ∏ j ∈ Finset.range q, (beurlingRadius j)⁻¹ ≤
      (64 / Real.sqrt (Real.log ((q : ℝ) + 3))) ^ q * dcLogWeight q := by
  have hprod_fac : ∏ j ∈ Finset.range q, ((j : ℝ) + 1) = (q.factorial : ℝ) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Finset.prod_range_succ, ih, Nat.factorial_succ, Nat.cast_mul]
      push_cast
      ring
  let L := Real.log ((q : ℝ) + 3)
  have hL : 0 < L := zero_lt_one.trans_le (log_add_three_ge_one q)
  have hS : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hLS : L / Real.sqrt L = Real.sqrt L := by
    rw [div_eq_iff hS.ne', ← sq, Real.sq_sqrt hL.le]
  calc ∏ j ∈ Finset.range q, (beurlingRadius j)⁻¹
      ≤ ∏ j ∈ Finset.range q, ((64 / Real.sqrt L) * ((j : ℝ) + 1) * L ^ 2) := by
        apply Finset.prod_le_prod (fun j _ => (inv_pos.mpr (beurlingRadius_pos j)).le)
        intro j hj
        have hjq : (j : ℝ) + 4 ≤ (q : ℝ) + 3 := by
          have hh : (j : ℝ) + 1 ≤ q := by
            exact_mod_cast Nat.add_one_le_of_lt (Finset.mem_range.mp hj)
          linarith only [hh]
        have hlog0 : 0 < Real.log ((j : ℝ) + 4) := Real.log_pos (by
          linarith only [Nat.cast_nonneg (α := ℝ) j])
        have hlog : Real.log ((j : ℝ) + 4) ≤ L := Real.log_le_log (by positivity) hjq
        have hlin : 16 * ((j : ℝ) + 4) ≤ 64 * ((j : ℝ) + 1) := by
          linarith only [Nat.cast_nonneg (α := ℝ) j]
        have hco : 16 * ((j : ℝ) + 4) * Real.log ((j : ℝ) + 4) *
            Real.sqrt (Real.log ((j : ℝ) + 4)) ≤ 64 * ((j : ℝ) + 1) * L * Real.sqrt L :=
          mul_le_mul (mul_le_mul hlin hlog hlog0.le (by positivity))
            (Real.sqrt_le_sqrt hlog) (Real.sqrt_nonneg _) (by positivity)
        have he : (64 / Real.sqrt L) * ((j : ℝ) + 1) * L ^ 2 =
            64 * ((j : ℝ) + 1) * L * Real.sqrt L := by
          calc _ = 64 * ((j : ℝ) + 1) * L * (L / Real.sqrt L) := by ring
            _ = _ := by rw [hLS]
        exact (inv_beurlingRadius_le j).trans (hco.trans_eq he.symm)
    _ = (64 / Real.sqrt L) ^ q * dcLogWeight q := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_const, Finset.card_range, ← pow_mul, hprod_fac]
      unfold dcLogWeight
      ring

theorem abs_iteratedDeriv_beurlingDCProfile_le (q : ℕ) (x : ℝ) :
    |iteratedDeriv q beurlingDCProfile x| ≤ steklovBaseSup *
      (64 / Real.sqrt (Real.log ((q : ℝ) + 3))) ^ q * dcLogWeight q := by
  have hpt : Tendsto (fun m => |iteratedDeriv q (beurlingSeq m) x|) atTop
      (𝓝 |iteratedDeriv q beurlingDCProfile x|) := by
    rw [iteratedDeriv_beurlingDCProfile_eq q]
    exact ((tendstoUniformly_beurlingDerivLimit q).tendsto_at x).abs
  refine le_of_tendsto hpt ?_
  filter_upwards [eventually_ge_atTop q] with m hqm
  exact (abs_iteratedDeriv_beurlingSeq_le m q hqm x).trans
    ((mul_le_mul_of_nonneg_left (prod_inv_beurlingRadius_le q) steklovBaseSup_pos.le).trans_eq
      (by ring))

theorem integral_abs_iteratedDeriv_beurlingDCProfile_le (q : ℕ) :
    ∫ t, |iteratedDeriv q beurlingDCProfile t| ≤ (2 * steklovBaseSup) *
      (64 / Real.sqrt (Real.log ((q : ℝ) + 3))) ^ q * dcLogWeight q := by
  have hd : Continuous (iteratedDeriv q beurlingDCProfile) :=
    contDiff_beurlingDCProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hvan : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → beurlingDCProfile t = 0 := fun t ht =>
    beurlingDCProfile_vanishesOff t (by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  have hdR : SupportedIn 1 (iteratedDeriv q beurlingDCProfile) := fun t ht =>
    iteratedDeriv_eq_zero_of_vanish hvan q fun h => by
      have := abs_le.mpr ⟨h.1, h.2⟩
      linarith
  have hb := integral_abs_le_of_bound hd (hasCompactSupport_of_vanishes hdR)
    (abs_iteratedDeriv_beurlingDCProfile_le q) hdR zero_le_one
  linarith only [hb]

/-- One fixed smooth unit profile satisfies the logarithmic derivative bound
with every positive exponential constant. -/
theorem exists_beurlingDCProfile_bound {B : ℝ} (hB : 0 < B) :
    ∃ A : ℝ, 0 < A ∧ ∀ q : ℕ,
      ∫ t, |iteratedDeriv q beurlingDCProfile t| ≤ A * B ^ q * dcLogWeight q := by
  let R : ℕ → ℝ := fun q => 64 / Real.sqrt (Real.log ((q : ℝ) + 3))
  have hR0 (q : ℕ) : 0 ≤ R q := by dsimp only [R]; positivity
  have hR64 (q : ℕ) : R q ≤ 64 := by
    have hs : 1 ≤ Real.sqrt (Real.log ((q : ℝ) + 3)) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (log_add_three_ge_one q)
    dsimp only [R]
    rw [div_le_iff₀ (zero_lt_one.trans_le hs)]
    linarith only [hs]
  have ht : Tendsto R atTop (𝓝 0) := tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hB))
  let D := max 1 (64 / B)
  have hD : 1 ≤ D := le_max_left _ _
  have hDJ : 1 ≤ D ^ J := one_le_pow₀ hD
  have h64 : 64 ≤ D * B := (div_le_iff₀ hB).mp (le_max_right _ _)
  have hp (q : ℕ) : R q ^ q ≤ D ^ J * B ^ q := by
    by_cases hq : J ≤ q
    · exact (pow_le_pow_left₀ (hR0 q) (hJ q hq).le q).trans
        (by nlinarith only [hDJ, pow_nonneg hB.le q])
    · calc R q ^ q ≤ (D * B) ^ q :=
          pow_le_pow_left₀ (hR0 q) ((hR64 q).trans h64) q
        _ = D ^ q * B ^ q := mul_pow _ _ _
        _ ≤ D ^ J * B ^ q := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hD (Nat.le_of_lt (not_le.mp hq))) (pow_nonneg hB.le q)
  refine ⟨(2 * steklovBaseSup) * D ^ J,
    mul_pos (mul_pos two_pos steklovBaseSup_pos) (pow_pos (zero_lt_one.trans_le hD) _),
    fun q => ?_⟩
  calc (∫ t, |iteratedDeriv q beurlingDCProfile t|)
      ≤ (2 * steklovBaseSup) * R q ^ q * dcLogWeight q :=
        integral_abs_iteratedDeriv_beurlingDCProfile_le q
    _ ≤ (2 * steklovBaseSup) * (D ^ J * B ^ q) * dcLogWeight q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hp q)
        (mul_nonneg two_pos.le steklovBaseSup_pos.le))
        (dcLogWeight_pos q).le
    _ = _ := by ring

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.contDiff_beurlingDCProfile
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.integral_beurlingDCProfile
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_beurlingDCProfile_bound
