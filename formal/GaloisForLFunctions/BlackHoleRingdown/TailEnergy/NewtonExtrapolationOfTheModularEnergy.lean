import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.ExponentialMomentsOfUnitStepRadiation
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Analytic.Binomial

/-!
# Newton extrapolation of modular scattering energy

Push the unit-time releases forward by the map k ↦ exp(-k). Integer
Laplace samples are then Hausdorff moments, as in Qi's positive moment
representation. Their signed differences are positive. The negative
binomial series extrapolates these samples to every negative real
argument at exactly the cost of the corresponding exponential moment.
Thus a single, fixed grid of damped observations gives a criterion for RH.
-/

open Finset Filter Polynomial
open scoped Topology

namespace GaloisForLFunctions.BlackHoleRingdown

noncomputable section

private def node (i : ℕ) : ℝ := Real.exp (-(i : ℝ))
private theorem node_pos (i : ℕ) : 0 < node i := Real.exp_pos _
private theorem node_le (i : ℕ) : node i ≤ 1 := Real.exp_le_one_iff.mpr (by positivity)

/-- Unit-grid Laplace samples of the nonnegative energy released in each unit interval. -/
def radiationSample (h : CompactPulse) (k : ℕ) : ℝ :=
  ∑' i : ℕ, node i^k * stepDecrement h i 1

private def mixed (h : CompactPulse) (k n : ℕ) : ℝ :=
  ∑' i : ℕ, node i^k * (1-node i)^n * stepDecrement h i 1

private theorem mixed_sum (h : CompactPulse) (k n : ℕ) :
    Summable fun i : ℕ => node i^k*(1-node i)^n*stepDecrement h i 1 := by
  have hm : Summable (fun i : ℕ => stepDecrement h i 1) := by
    simpa using (unit_decrements_have_sum h 0).summable
  apply hm.of_nonneg_of_le
  · intro i
    exact mul_nonneg (mul_nonneg (pow_nonneg (node_pos i).le _) (pow_nonneg (sub_nonneg.mpr
      (node_le i)) _)) (stepDecrement_nonneg _ _ _)
  · intro i
    apply mul_le_of_le_one_left (stepDecrement_nonneg _ _ _)
    exact mul_le_one₀ (pow_le_one₀ (node_pos i).le (node_le i)) (pow_nonneg
      (sub_nonneg.mpr (node_le i)) _) (pow_le_one₀ (sub_nonneg.mpr (node_le i))
        (sub_le_self _ (node_pos i).le))

private theorem mixed_step (h : CompactPulse) (k n : ℕ) :
    mixed h (k+1) n - mixed h k n = -mixed h k (n+1) := by
  rw [mixed, mixed, mixed, ← (mixed_sum h (k+1) n).tsum_sub (mixed_sum h k n), ← tsum_neg]
  exact tsum_congr fun i => by simp only [pow_succ]; ring

/-- The signed differences at every starting sample have an exact positive kernel. -/
theorem radiationSample_signed_difference (h : CompactPulse) (k n : ℕ) :
    (-1 : ℝ)^n * (fwdDiff 1)^[n] (radiationSample h) k =
      ∑' i : ℕ, node i^k*(1-node i)^n*stepDecrement h i 1 := by
  suffices H : ∀ k, (fwdDiff 1)^[n] (radiationSample h) k = (-1 : ℝ)^n*mixed h k n by
    rw [H, ← mul_assoc, ← mul_pow]
    simp [mixed]
  induction n with
  | zero => intro k; simp [radiationSample, mixed]
  | succ n ih =>
    intro k
    rw [Function.iterate_succ_apply']
    change (fwdDiff 1)^[n] _ (k+1) - (fwdDiff 1)^[n] _ k = _
    rw [ih, ih, ← mul_sub, mixed_step, pow_succ]
    ring

private theorem coeff_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : 0 ≤ Ring.multichoose b n := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer b n
  rw [nsmul_eq_mul, ascPochhammer_smeval_eq_eval] at h
  have hp : 0 ≤ (ascPochhammer ℝ n).eval b := by
    induction n with
    | zero => simp
    | succ n ih => rw [ascPochhammer_succ_eval]; positivity
  exact nonneg_of_mul_nonneg_right (hp.trans_eq h.symm) (by positivity : (0 : ℝ) < n.factorial)

private theorem binomial_kernel (b : ℝ) (i : ℕ) :
    HasSum (fun n : ℕ => Ring.multichoose b n * (1-node i)^n) (Real.exp (b*i)) := by
  have hn : ‖1-node i‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (node_le i))]
    linarith only [node_pos i]
  have hm : 1-node i ∈ Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff]
    exact_mod_cast hn
  have H := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero b).hasSum hm
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, ← Ring.multichoose_eq,
    zero_add, sub_sub_cancel, node, ← Real.exp_mul, one_div, ← Real.exp_neg, neg_mul, neg_neg,
    mul_comm (i : ℝ) b] using H

/-- Newton terms at a negative real argument, computed entirely from nonnegative integer samples. -/
def radiationNewtonTerm (h : CompactPulse) (b : ℝ) (n : ℕ) : ℝ :=
  Ring.multichoose b n * ((-1 : ℝ)^n * (fwdDiff 1)^[n] (radiationSample h) 0)

private theorem newton_term (h : CompactPulse) (b : ℝ) (n : ℕ) :
    radiationNewtonTerm h b n =
      ∑' i : ℕ, Ring.multichoose b n * ((1-node i)^n * stepDecrement h i 1) := by
  simp only [radiationNewtonTerm, radiationSample_signed_difference, pow_zero, one_mul, tsum_mul_left]

theorem radiationNewtonTerm_nonneg (h : CompactPulse) {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ radiationNewtonTerm h b n := by
  rw [newton_term]
  exact tsum_nonneg fun i => mul_nonneg (coeff_nonneg hb n)
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr (node_le i)) _) (stepDecrement_nonneg _ _ _))

/-- Newton extrapolation on one fixed grid has exactly the same sum and convergence
domain as the exponential moment of the physical releases. -/
theorem radiationNewton_hasSum_iff (h : CompactPulse) {b : ℝ} (hb : 0 ≤ b) (L : ℝ) :
    HasSum (radiationNewtonTerm h b) L ↔
      HasSum (fun i : ℕ => Real.exp (b*i)*stepDecrement h i 1) L := by
  let A (n i : ℕ) := Ring.multichoose b n * ((1-node i)^n * stepDecrement h i 1)
  have hpos (n i : ℕ) : 0 ≤ A n i := mul_nonneg (coeff_nonneg hb n)
    (mul_nonneg (pow_nonneg (sub_nonneg.mpr (node_le i)) _) (stepDecrement_nonneg _ _ _))
  have hrow (n : ℕ) : Summable (A n) := by
    simpa only [A, pow_zero, one_mul] using (mixed_sum h 0 n).mul_left (Ring.multichoose b n)
  have hcol (i : ℕ) : HasSum (fun n => A n i) (Real.exp (b*i)*stepDecrement h i 1) := by
    simpa only [A, mul_assoc] using (binomial_kernel b i).mul_right (stepDecrement h i 1)
  have hr := summable_prod_of_nonneg (f := fun p : ℕ × ℕ => A p.1 p.2) fun p => hpos _ _
  have hc := summable_prod_of_nonneg (f := fun p : ℕ × ℕ => A p.2 p.1) fun p => hpos _ _
  simp only [hrow, forall_true_iff, true_and] at hr
  simp only [fun i => (hcol i).summable, forall_true_iff, true_and, fun i => (hcol i).tsum_eq] at hc
  have hnew (n : ℕ) : radiationNewtonTerm h b n = ∑' i : ℕ, A n i := newton_term h b n
  rw [funext hnew]
  have exchange (hf : Summable (Function.uncurry A)) :
      (∑' i : ℕ, Real.exp (b*i)*stepDecrement h i 1) = ∑' n i : ℕ, A n i := by
    simpa only [fun i => (hcol i).tsum_eq] using hf.tsum_comm
  constructor
  · intro H
    have hf := hr.mpr H.summable
    exact ((hc.mp hf.prod_symm).hasSum_iff).mpr ((exchange hf).trans H.tsum_eq)
  · intro H
    have hf := (hc.mpr H.summable).prod_symm
    exact ((hr.mp hf).hasSum_iff).mpr ((exchange hf).symm.trans H.tsum_eq)

theorem radiationNewton_summable_iff (h : CompactPulse) {b : ℝ} (hb : 0 ≤ b) :
    Summable (radiationNewtonTerm h b) ↔
      Summable (fun i : ℕ => Real.exp (b*i)*stepDecrement h i 1) := by
  constructor <;> rintro ⟨L,hL⟩
  · exact ((radiationNewton_hasSum_iff h hb L).mp hL).summable
  · exact ((radiationNewton_hasSum_iff h hb L).mpr hL).summable

/-- RH is equivalent to summability of the positive Newton terms at every extrapolated
argument strictly between minus one half and zero, for every compact pulse. -/
theorem rh_iff_radiationNewton : RiemannHypothesis ↔
    ∀ h : CompactPulse, ∀ b : ℝ, 0 < b → b < 1/2 → Summable (radiationNewtonTerm h b) := by
  rw [rh_iff_unit_radiation_moments]
  constructor
  · exact fun H h b hb hhalf => (radiationNewton_summable_iff h hb.le).mpr (H h b hhalf)
  · intro H h b hhalf
    by_cases hb : 0 < b
    · exact (radiationNewton_summable_iff h hb.le).mp (H h b hb hhalf)
    · apply (show Summable (fun i : ℕ => stepDecrement h i 1) by
        simpa using (unit_decrements_have_sum h 0).summable).of_nonneg_of_le
      · intro i; exact mul_nonneg (Real.exp_pos _).le (stepDecrement_nonneg _ _ _)
      · intro i
        exact mul_le_of_le_one_left (stepDecrement_nonneg _ _ _)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) (Nat.cast_nonneg _)))

/-- Remove the first releases, then normalize the next node to one. -/
def radiationRemainder (h : CompactPulse) (r k : ℕ) : ℝ :=
  (radiationSample h k - ∑ i ∈ range r, node i^k*stepDecrement h i 1) / node r^k

private theorem shifted_releases (h : CompactPulse) (r : ℕ) :
    HasSum (fun i : ℕ => stepDecrement h (i+r : ℕ) 1) (tailEnergy h r) := by
  simpa only [Nat.cast_add, add_comm (r : ℝ)] using unit_decrements_have_sum h r

private theorem remainder_eq (h : CompactPulse) (r k : ℕ) :
    radiationRemainder h r k = ∑' i : ℕ, node i^k * stepDecrement h (i+r : ℕ) 1 := by
  have hs : Summable (fun i : ℕ => node i^k*stepDecrement h i 1) := by
    simpa only [pow_zero, mul_one] using mixed_sum h k 0
  have htail := hs.sum_add_tsum_nat_add r
  have hf (i : ℕ) : node (i+r) = node i*node r := by
    simp only [node, Nat.cast_add, neg_add_rev, Real.exp_add, mul_comm]
  apply (div_eq_iff (pow_ne_zero _ (node_pos r).ne')).mpr
  change radiationSample h k - _ = _
  rw [sub_eq_iff_eq_add, radiationSample, ← htail, ← tsum_mul_right, add_comm]
  congr 1
  exact tsum_congr fun i => by rw [hf, mul_pow]; ring

private theorem shifted_sum (h : CompactPulse) (k r : ℕ) :
    Summable fun i : ℕ => node i^k * stepDecrement h (i+r : ℕ) 1 :=
  (shifted_releases h r).summable.of_nonneg_of_le
    (fun i => mul_nonneg (pow_nonneg (node_pos i).le _) (stepDecrement_nonneg _ _ _))
    (fun i => mul_le_of_le_one_left (stepDecrement_nonneg _ _ _)
      (pow_le_one₀ (node_pos i).le (node_le i)))

/-- The normalized reading overestimates the next release by at most the entire
following tail times exp(-k), independently of the position of that release. -/
theorem radiationRemainder_bounds (h : CompactPulse) (r k : ℕ) :
    stepDecrement h r 1 ≤ radiationRemainder h r k ∧
    radiationRemainder h r k ≤ stepDecrement h r 1 + node 1^k * tailEnergy h (r+1 : ℕ) := by
  rw [remainder_eq, (shifted_sum h k r).tsum_eq_zero_add]
  simp only [zero_add, node, Nat.cast_zero, neg_zero, Real.exp_zero, one_pow, one_mul,
    le_add_iff_nonneg_right, add_le_add_iff_left]
  constructor
  · exact tsum_nonneg fun i => mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (stepDecrement_nonneg _ _ _)
  · have H := shifted_releases h (r+1)
    rw [← H.tsum_eq, ← tsum_mul_left]
    apply (summable_nat_add_iff 1 |>.mpr (shifted_sum h k r)).tsum_le_tsum _
      (H.summable.mul_left _)
    intro i
    rw [show i+1+r = i+(r+1) by omega]
    apply mul_le_mul_of_nonneg_right _ (stepDecrement_nonneg _ _ _)
    apply pow_le_pow_left₀ (Real.exp_pos _).le
    apply Real.exp_le_exp.mpr
    push_cast
    linarith only [Nat.cast_nonneg (R := ℝ) i]

/-- Every unit-time release can be recovered successively from arbitrarily high
integer Laplace samples. -/
theorem radiationRemainder_tendsto (h : CompactPulse) (r : ℕ) :
    Tendsto (radiationRemainder h r) atTop (𝓝 (stepDecrement h r 1)) := by
  have hn : node 1 < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (node_pos 1).le hn).mul_const
    (tailEnergy h (r+1 : ℕ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_const_nhds (x := stepDecrement h r 1)).add hlim)
    (fun k => (radiationRemainder_bounds h r k).1) (fun k => (radiationRemainder_bounds h r k).2)

/-- Equality of integer Laplace readings is equivalent to equality of every unit release. -/
theorem radiationSample_identifies_releases (g h : CompactPulse) :
    radiationSample g = radiationSample h ↔
      ∀ r : ℕ, stepDecrement g r 1 = stepDecrement h r 1 := by
  constructor
  · intro he r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      have hrem : radiationRemainder g r = radiationRemainder h r := by
        funext k
        simp only [radiationRemainder, he]
        congr 2
        exact sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi)]
      exact tendsto_nhds_unique (hrem ▸ radiationRemainder_tendsto g r) (radiationRemainder_tendsto h r)
  · intro he
    funext k
    exact tsum_congr fun i => by rw [he i]

#print axioms radiationSample_identifies_releases
#print axioms radiationSample_signed_difference
#print axioms radiationNewton_hasSum_iff
#print axioms rh_iff_radiationNewton

end

end GaloisForLFunctions.BlackHoleRingdown
