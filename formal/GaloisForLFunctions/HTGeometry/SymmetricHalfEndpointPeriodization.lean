import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

noncomputable section

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

def symmetricHalfEndpointCutoff (A : ℝ) (G : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x ∈ Ioo (-A) A then G x
  else if x = -A ∨ x = A then G x / 2
  else 0

theorem continuousAt_symmetricHalfEndpointPair
    {A b r : ℝ} (hA : 0 < A) (hb : 0 < b) (hr : 0 ≤ r)
    {G : ℝ → ℂ} (hG : Continuous G) (heven : Function.Even G) :
    ContinuousAt (fun x =>
      symmetricHalfEndpointCutoff A G ((x + r) / b) +
        symmetricHalfEndpointCutoff A G ((x - r) / b)) 0 := by
  rcases lt_trichotomy (r / b) A with hinside | hboundary | houtside
  · have hneg_inside : -(r / b) ∈ Ioo (-A) A := by
      have hq : 0 ≤ r / b := div_nonneg hr hb.le
      constructor <;> linarith
    have hpos_inside : r / b ∈ Ioo (-A) A := by
      constructor
      · have hq : 0 ≤ r / b := div_nonneg hr hb.le
        linarith
      · exact hinside
    have hplus : ∀ᶠ x in 𝓝 (0 : ℝ), (x + r) / b ∈ Ioo (-A) A := by
      have hzero : ((0 : ℝ) + r) / b ∈ Ioo (-A) A := by simpa using hpos_inside
      exact ((continuousAt_id.add continuousAt_const).div_const b)
        (isOpen_Ioo.mem_nhds hzero)
    have hminus : ∀ᶠ x in 𝓝 (0 : ℝ), (x - r) / b ∈ Ioo (-A) A := by
      have hzero : ((0 : ℝ) - r) / b ∈ Ioo (-A) A := by
        simpa only [zero_sub, neg_div] using hneg_inside
      exact ((continuousAt_id.sub continuousAt_const).div_const b)
        (isOpen_Ioo.mem_nhds hzero)
    have hcplus : Continuous (fun x : ℝ => G ((x + r) / b)) :=
      hG.comp ((continuous_id.add continuous_const).div_const b)
    have hcminus : Continuous (fun x : ℝ => G ((x - r) / b)) :=
      hG.comp ((continuous_id.sub continuous_const).div_const b)
    apply ContinuousAt.congr_of_eventuallyEq (hcplus.add hcminus).continuousAt
    filter_upwards [hplus, hminus] with x hxplus hxminus
    simp only [symmetricHalfEndpointCutoff, if_pos hxplus, if_pos hxminus]
    simp only [Pi.add_apply]
  · have hrb : r = A * b := by
      apply (div_eq_iff hb.ne').mp
      linarith
    have hwindow : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 2 * A * b := by
      have hpos : 0 < 2 * A * b := mul_pos (mul_pos (by norm_num) hA) hb
      exact Metric.mem_nhds_iff.mpr ⟨2 * A * b, hpos, by
        intro x hx
        change dist x 0 < 2 * A * b at hx
        simpa only [Real.dist_eq, sub_zero] using hx⟩
    have hmodel : ContinuousAt (fun x : ℝ => G (A - |x| / b)) 0 := by
      have harg : Continuous (fun x : ℝ => A - |x| / b) :=
        continuous_const.sub (continuous_abs.div_const b)
      exact (hG.comp harg).continuousAt
    apply ContinuousAt.congr_of_eventuallyEq hmodel
    filter_upwards [hwindow] with x hx
    have hxlow : -2 * A * b < x := by
      have := neg_lt_of_abs_lt hx
      nlinarith
    have hxhigh : x < 2 * A * b := (lt_of_abs_lt hx)
    by_cases hx0 : x = 0
    · subst x
      have hposdiv : (A * b) / b = A := by field_simp
      have hnegdiv : (-(A * b)) / b = -A := by field_simp
      simp only [zero_add, zero_sub, hrb, hposdiv, hnegdiv, abs_zero, zero_div, sub_zero]
      simp [symmetricHalfEndpointCutoff, heven A]
    · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · have hplus_in : (x + r) / b ∈ Ioo (-A) A := by
          rw [hrb]
          constructor
          · apply (lt_div_iff₀ hb).2
            nlinarith
          · apply (div_lt_iff₀ hb).2
            linarith
        have hminus_out : (x - r) / b ∉ Icc (-A) A := by
          intro h
          have := h.1
          rw [le_div_iff₀ hb] at this
          rw [hrb] at this
          linarith
        have habs : |x| = -x := abs_of_neg hxneg
        simp only [symmetricHalfEndpointCutoff, if_pos hplus_in,
          if_neg (fun h => hminus_out (Ioo_subset_Icc_self h))]
        rw [if_neg]
        · simp only [add_zero, habs]
          congr 1
          field_simp [hb.ne']
          rw [hrb]
          ring
        · intro hend
          rcases hend with hend | hend <;> apply hminus_out
          · rw [hend]; simp [hA.le]
          · rw [hend]; simp [hA.le]
      · have hminus_in : (x - r) / b ∈ Ioo (-A) A := by
          rw [hrb]
          constructor
          · apply (lt_div_iff₀ hb).2
            linarith
          · apply (div_lt_iff₀ hb).2
            nlinarith
        have hplus_out : (x + r) / b ∉ Icc (-A) A := by
          intro h
          have := h.2
          rw [div_le_iff₀ hb] at this
          rw [hrb] at this
          linarith
        have habs : |x| = x := abs_of_pos hxpos
        simp only [symmetricHalfEndpointCutoff,
          if_neg (fun h => hplus_out (Ioo_subset_Icc_self h))]
        rw [if_neg]
        · simp only [zero_add, if_pos hminus_in, habs]
          rw [← heven ((x - r) / b)]
          congr 1
          field_simp [hb.ne']
          rw [hrb]
          ring
        · intro hend
          rcases hend with hend | hend <;> apply hplus_out
          · rw [hend]; simp [hA.le]
          · rw [hend]; simp [hA.le]
  · have hpos_out : r / b ∉ Icc (-A) A := by
      intro h
      exact (not_lt_of_ge h.2) houtside
    have hneg_out : -(r / b) ∉ Icc (-A) A := by
      intro h
      have hq : 0 ≤ r / b := div_nonneg hr hb.le
      have := h.1
      linarith
    have hplus : ∀ᶠ x in 𝓝 (0 : ℝ), (x + r) / b ∉ Icc (-A) A := by
      have hzero : ((0 : ℝ) + r) / b ∉ Icc (-A) A := by simpa using hpos_out
      exact ((continuousAt_id.add continuousAt_const).div_const b)
        (isClosed_Icc.isOpen_compl.mem_nhds hzero)
    have hminus : ∀ᶠ x in 𝓝 (0 : ℝ), (x - r) / b ∉ Icc (-A) A := by
      have hzero : ((0 : ℝ) - r) / b ∉ Icc (-A) A := by
        simpa only [zero_sub, neg_div] using hneg_out
      exact ((continuousAt_id.sub continuousAt_const).div_const b)
        (isClosed_Icc.isOpen_compl.mem_nhds hzero)
    apply ContinuousAt.congr_of_eventuallyEq continuousAt_const
    filter_upwards [hplus, hminus] with x hxplus hxminus
    have hxplusend : ¬((x + r) / b = -A ∨ (x + r) / b = A) := by
      intro hend
      apply hxplus
      rcases hend with hend | hend <;> rw [hend] <;> simp [hA.le]
    have hxminusend : ¬((x - r) / b = -A ∨ (x - r) / b = A) := by
      intro hend
      apply hxminus
      rcases hend with hend | hend <;> rw [hend] <;> simp [hA.le]
    simp only [symmetricHalfEndpointCutoff,
      if_neg (fun h => hxplus (Ioo_subset_Icc_self h)),
      if_neg (fun h => hxminus (Ioo_subset_Icc_self h)),
      if_neg hxplusend, if_neg hxminusend, add_zero]
    rfl

theorem symmetricHalfEndpointCutoff_eq_zero_of_not_mem_Icc
    {A : ℝ} (hA : 0 ≤ A) {G : ℝ → ℂ} {x : ℝ} (hx : x ∉ Icc (-A) A) :
    symmetricHalfEndpointCutoff A G x = 0 := by
  simp only [symmetricHalfEndpointCutoff,
    if_neg (fun h => hx (Ioo_subset_Icc_self h))]
  rw [if_neg]
  intro hend
  rcases hend with rfl | rfl <;> exact hx (by simp [hA])

theorem even_symmetricHalfEndpointCutoff
    (A : ℝ) {G : ℝ → ℂ} (heven : Function.Even G) :
    Function.Even (symmetricHalfEndpointCutoff A G) := by
  intro x
  have hinterior : -x ∈ Ioo (-A) A ↔ x ∈ Ioo (-A) A := by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hendpoint : -x = -A ∨ -x = A ↔ x = -A ∨ x = A := by
    constructor <;> rintro (h | h)
    · right; linarith
    · left; linarith
    · right; linarith
    · left; linarith
  simp only [symmetricHalfEndpointCutoff, hinterior, hendpoint, heven x]

theorem summable_symmetricHalfEndpointCutoff_shift_nat
    {A b x : ℝ} (hA : 0 < A) (hb : 0 < b) (G : ℝ → ℂ) :
    Summable fun n : ℕ => symmetricHalfEndpointCutoff A G ((x + n) / b) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| + A * b + 2)
  apply (summable_nat_add_iff N).1
  apply (summable_zero : Summable (fun _ : ℕ => (0 : ℂ))).congr
  intro n
  symm
  apply symmetricHalfEndpointCutoff_eq_zero_of_not_mem_Icc hA.le
  intro hmem
  have hupper := hmem.2
  rw [div_le_iff₀ hb] at hupper
  have hxlower : -|x| ≤ x := neg_abs_le x
  have hcast : |x| + A * b + 2 < (N : ℝ) := by exact_mod_cast hN
  have hn : (N : ℝ) ≤ (n + N : ℕ) := by exact_mod_cast Nat.le_add_left N n
  push_cast at hn
  have hbig : |x| + A * b + 2 < (n : ℝ) + N := lt_of_lt_of_le hcast hn
  have : A * b < x + ((n : ℝ) + N) := by linarith
  exact (not_lt_of_ge hupper) (by simpa only [Nat.cast_add] using this)

theorem summable_symmetricHalfEndpointCutoff_neg_shift_nat
    {A b x : ℝ} (hA : 0 < A) (hb : 0 < b) (G : ℝ → ℂ) :
    Summable fun n : ℕ =>
      symmetricHalfEndpointCutoff A G ((x - (n + 1 : ℝ)) / b) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|x| + A * b + 2)
  apply (summable_nat_add_iff N).1
  apply (summable_zero : Summable (fun _ : ℕ => (0 : ℂ))).congr
  intro n
  symm
  apply symmetricHalfEndpointCutoff_eq_zero_of_not_mem_Icc hA.le
  intro hmem
  have hlower := hmem.1
  rw [le_div_iff₀ hb] at hlower
  have hxupper : x ≤ |x| := le_abs_self x
  have hcast : |x| + A * b + 2 < (N : ℝ) := by exact_mod_cast hN
  have hn : (N : ℝ) ≤ (n + N : ℕ) := by exact_mod_cast Nat.le_add_left N n
  push_cast at hn
  have hbig : |x| + A * b + 2 < (n : ℝ) + N := lt_of_lt_of_le hcast hn
  have : x - ((n : ℝ) + N + 1) < -A * b := by linarith
  exact (not_lt_of_ge hlower) (by simpa only [Nat.cast_add] using this)

set_option maxHeartbeats 400000 in
theorem l1Periodization_symmetricHalfEndpointCutoff_eq_center_add_pairs
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {G : ℝ → ℂ}
    (x : ℝ) :
    l1Periodization (fun y => symmetricHalfEndpointCutoff A G (y / b)) x =
      symmetricHalfEndpointCutoff A G (x / b) +
        ∑' n : ℕ,
          (symmetricHalfEndpointCutoff A G ((x + (n + 1 : ℝ)) / b) +
            symmetricHalfEndpointCutoff A G ((x - (n + 1 : ℝ)) / b)) := by
  let f : ℤ → ℂ := fun k => symmetricHalfEndpointCutoff A G ((x + k) / b)
  have hpos : Summable fun n : ℕ => f n := by
    simpa only [f, Int.cast_natCast] using
      summable_symmetricHalfEndpointCutoff_shift_nat hA hb G (x := x)
  have hneg : Summable fun n : ℕ => f (-((n : ℤ) + 1)) := by
    simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      sub_eq_add_neg] using
      summable_symmetricHalfEndpointCutoff_neg_shift_nat hA hb G (x := x)
  have hpostail : Summable fun n : ℕ => f (n + 1) :=
    (summable_nat_add_iff 1).2 hpos
  unfold l1Periodization
  change (∑' k : ℤ, f k) = _
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  have hhead :
      (∑' n : ℕ, f n) = f 0 + ∑' n : ℕ, f (n + 1) := by
    rw [← hpos.sum_add_tsum_nat_add 1]
    simp only [Finset.sum_range_one, Nat.cast_zero]
    congr 1
  rw [hhead, add_assoc, ← hpostail.tsum_add hneg]
  have hcenter : f 0 = symmetricHalfEndpointCutoff A G (x / b) := by
    simp only [f, Int.cast_zero, add_zero]
  rw [hcenter]
  apply congrArg (fun z : ℂ => symmetricHalfEndpointCutoff A G (x / b) + z)
  apply tsum_congr
  intro n
  simp only [f, Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one]
  congr 2

theorem continuousAt_l1Periodization_symmetricHalfEndpointCutoff_zero
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {G : ℝ → ℂ}
    (hG : Continuous G) (heven : Function.Even G) :
    ContinuousAt
      (l1Periodization (fun y => symmetricHalfEndpointCutoff A G (y / b))) 0 := by
  let center : ℝ → ℂ := fun x => symmetricHalfEndpointCutoff A G (x / b)
  let pair : ℕ → ℝ → ℂ := fun n x =>
    symmetricHalfEndpointCutoff A G ((x + (n + 1 : ℝ)) / b) +
      symmetricHalfEndpointCutoff A G ((x - (n + 1 : ℝ)) / b)
  have hcenter : ContinuousAt center 0 := by
    have hzero : (0 : ℝ) / b ∈ Ioo (-A) A := by simp [hA]
    have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), x / b ∈ Ioo (-A) A := by
      exact (continuousAt_id.div_const b) (isOpen_Ioo.mem_nhds hzero)
    apply ContinuousAt.congr_of_eventuallyEq
      (hG.comp (continuous_id.div_const b)).continuousAt
    filter_upwards [hnear] with x hx
    simp only [center, symmetricHalfEndpointCutoff, if_pos hx]
    rfl
  obtain ⟨N, hN⟩ := exists_nat_gt (A * b + 3)
  have hwindow : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < 1 := by
    exact Metric.mem_nhds_iff.mpr ⟨1, by norm_num, by
      intro x hx
      change dist x 0 < 1 at hx
      simpa only [Real.dist_eq, sub_zero] using hx⟩
  have htail : ∀ᶠ x in 𝓝 (0 : ℝ),
      ∀ n : ℕ, N ≤ n → pair n x = 0 := by
    filter_upwards [hwindow] with x hx n hn
    have hxlower : -1 < x := (abs_lt.mp hx).1
    have hxupper : x < 1 := (abs_lt.mp hx).2
    have hcast : A * b + 3 < (N : ℝ) := by exact_mod_cast hN
    have hncast : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hplusout : (x + (n + 1 : ℝ)) / b ∉ Icc (-A) A := by
      intro hmem
      have := hmem.2
      rw [div_le_iff₀ hb] at this
      linarith
    have hminusout : (x - (n + 1 : ℝ)) / b ∉ Icc (-A) A := by
      intro hmem
      have := hmem.1
      rw [le_div_iff₀ hb] at this
      linarith
    simp only [pair,
      symmetricHalfEndpointCutoff_eq_zero_of_not_mem_Icc hA.le hplusout,
      symmetricHalfEndpointCutoff_eq_zero_of_not_mem_Icc hA.le hminusout, add_zero]
  have hpairs : ContinuousAt (fun x => ∑ n ∈ Finset.range N, pair n x) 0 := by
    apply tendsto_finsetSum
    intro n hn
    change ContinuousAt (pair n) 0
    simpa only [pair, Nat.cast_add, Nat.cast_one] using
      continuousAt_symmetricHalfEndpointPair hA hb (Nat.cast_nonneg (n + 1)) hG heven
  apply ContinuousAt.congr_of_eventuallyEq (hcenter.add hpairs)
  filter_upwards [htail] with x hzero
  rw [l1Periodization_symmetricHalfEndpointCutoff_eq_center_add_pairs hA hb]
  have htsum : (∑' n : ℕ, pair n x) = ∑ n ∈ Finset.range N, pair n x := by
    apply tsum_eq_sum
    intro n hn
    exact hzero n (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn))
  rw [htsum]
  rfl

/-- Real-valued half-endpoint cutoff used by Poisson--Muntz sampling. -/
def realSymmetricHalfEndpointCutoff (A : ℝ) (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Ioo (-A) A then G x
  else if x = -A ∨ x = A then G x / 2
  else 0

theorem ofReal_realSymmetricHalfEndpointCutoff
    (A : ℝ) (G : ℝ → ℝ) (x : ℝ) :
    (realSymmetricHalfEndpointCutoff A G x : ℂ) =
      symmetricHalfEndpointCutoff A (fun y => (G y : ℂ)) x := by
  simp only [realSymmetricHalfEndpointCutoff, symmetricHalfEndpointCutoff]
  split_ifs <;> norm_num

/-- Real periodization inherits collision continuity from paired complexification. -/
theorem continuousAt_realL1Periodization_symmetricHalfEndpointCutoff_zero
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {G : ℝ → ℝ}
    (hG : Continuous G) (heven : Function.Even G) :
    ContinuousAt
      (realL1Periodization (fun y => realSymmetricHalfEndpointCutoff A G (y / b))) 0 := by
  have hGc : Continuous (fun x => (G x : ℂ)) :=
    Complex.continuous_ofReal.comp hG
  have hevenGc : Function.Even (fun x => (G x : ℂ)) := by
    intro x
    simp only [heven x]
  have hc := continuousAt_l1Periodization_symmetricHalfEndpointCutoff_zero
    hA hb hGc hevenGc
  have hc' : ContinuousAt
      (l1Periodization (fun y =>
        (realSymmetricHalfEndpointCutoff A G (y / b) : ℂ))) 0 := by
    simpa only [ofReal_realSymmetricHalfEndpointCutoff] using hc
  have hre := Complex.continuous_re.continuousAt.comp hc'
  change ContinuousAt (fun x =>
    (l1Periodization (fun y =>
      (realSymmetricHalfEndpointCutoff A G (y / b) : ℂ)) x).re) 0 at hre
  simpa only [← ofReal_realL1Periodization, Complex.ofReal_re] using hre

end GaloisForLFunctions.HTGeometry
