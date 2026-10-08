import GaloisForLFunctions.RHTower.WeilWorkPBAPJointProfiles
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointPhase

/-!
# Exact smooth integer-null mixtures from joint phase cancellation

Every fixed smooth profile supported in an interval shorter than `log 2`
admits finite nonnegative cosine/sine corrections at arbitrary frequency
threshold and every correction mass greater than one. At prime separation
`log p / 2`, `p >= 5`, the resulting two-cluster mixture is null at every
integer logarithm and retains its exact mass. Both positive and negative
samples, every above-cut integer and repeated mixture tests are accounted for.
No Weil-energy sign is asserted.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

theorem jointProfileSample_zero_of_radius {ι : Type} [Fintype ι]
    (f : JointSmoothTest) (w t : ι → ℝ) {W y : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hy : W < |y|) :
    jointProfileSample f w t y = 0 := by
  rw [jointProfileSample_eq, weilTest_eq_zero_outside_interval hf hy, zero_mul]

theorem joint_half_log_prime_gt_log_two (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) :
    Real.log 2 < Real.log (p : ℕ)/2 := by
  have hp' : (4 : ℝ) < (p : ℕ) := by
    exact_mod_cast (show 4 < (p : ℕ) from lt_of_lt_of_le (by norm_num) hp)
  have hl := Real.log_lt_log (by norm_num : (0:ℝ)<4) hp'
  have he : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2*2 by ring, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he] at hl
  linarith

/-- Exact all-integer nullness of the broad profile construction. -/
theorem jointClusterMixture_null {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) {W : ℝ}
    (hW : W < Real.log 2) (hf : tsupport f.1.1 ⊆ Set.Icc 0 W)
    (w t : ι → ℝ)
    (hc : ∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
      1 + (∑ i, w i * Real.cos ((Real.log n - Real.log (p : ℕ)/2)*t i)) = 0) :
    ∀ n : ℕ, 2 ≤ n →
      (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
        (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 (Real.log n)) = 0 := by
  have hL := joint_half_log_prime_gt_log_two p hp
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  intro n hn
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [jointClusterMixture_autocorrelation]
  have hzero : jointProfileSample f w t (Real.log n) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by
      rw [abs_of_pos (lt_of_lt_of_le hlog2 hlog)]; linarith)
  have hplus : jointProfileSample f w t (Real.log n + Real.log (p : ℕ)/2) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by
      rw [abs_of_pos (by linarith : 0<Real.log n + Real.log (p : ℕ)/2)]; linarith)
  have hminus : jointProfileSample f w t (Real.log n - Real.log (p : ℕ)/2) = 0 := by
    by_cases hnp : n < (p : ℕ)
    · rw [jointProfileSample_eq]
      have he := hc n hn hnp
      simp_rw [mul_comm (t _) (Real.log n - Real.log (p : ℕ)/2)]
      rw [he, Complex.ofReal_zero, mul_zero]
    · have hlp : Real.log (p : ℕ) ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast p.2.pos) (by exact_mod_cast not_lt.mp hnp)
      apply jointProfileSample_zero_of_radius f w t hf
      rw [abs_of_pos (by linarith : 0<Real.log n - Real.log (p : ℕ)/2)]
      linarith
  rw [hzero, hplus, hminus]
  ring

/-- Total mass retains the base profile and every modulation weight exactly. -/
theorem jointClusterMixture_mass {ι : Type} [Fintype ι] (f : JointSmoothTest)
    {L W : ℝ} (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L)
    (hL : 0 ≤ L) (w t : ι → ℝ) :
    (jointClusterMixture f L w t).sum (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 0) =
      ((2*(1+∑ i, w i) : ℝ) : ℂ)*EF.weilTest f.1.1 f.1.1 0 := by
  rw [jointClusterMixture_autocorrelation]
  have hminus : jointProfileSample f w t (0-L) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by simpa [abs_of_nonneg hL] using hWL)
  have hplus : jointProfileSample f w t (0+L) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by simpa [abs_of_nonneg hL] using hWL)
  rw [hminus, hplus, sub_zero, sub_zero, jointProfileSample_eq]
  simp only [mul_zero, Real.cos_zero, mul_one]
  push_cast
  ring

theorem jointClusterMixture_smooth {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) (g : WeilTestFn)
    (hg : g ∈ (jointClusterMixture f L w t).support) : ContDiff ℝ ∞ g.1 := by
  classical
  by_contra hn
  have hne : ∀ q : JointSmoothTest, q.1 ≠ g := by
    intro q he
    exact hn (he ▸ q.2)
  have hz : jointClusterMixture f L w t g = 0 := by
    simp [jointClusterMixture, hne]
  exact (Finsupp.mem_support_iff.mp hg) hz

/-- The actual symmetric real null functional is twice the real autocorrelation sample. -/
theorem joint_sum_logValue (c : WeilTestFn →₀ ℝ) (n : ℕ) :
    c.sum (fun g r => r * logValue g.1 n) =
      2 * (c.sum (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 (Real.log n))).re / Real.sqrt n := by
  simp only [Finsupp.sum, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro g _
  rw [logValue, weilTest_self_neg]
  simp only [Complex.add_re, Complex.conj_re]
  ring

private theorem sum_logValue_of_null (c : WeilTestFn →₀ ℝ) (n : ℕ)
    (hc : c.sum (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 (Real.log n)) = 0) :
    c.sum (fun g r => r * logValue g.1 n) = 0 := by
  rw [joint_sum_logValue, hc]
  simp

/-- Actual smooth, compact, nonnegative finite mixtures with every integer null constraint,
constructed from any fixed interval-supported profile. No Weil positivity is assumed. -/
theorem exists_joint_smooth_null_mixture (f : JointSmoothTest) (p : Nat.Primes)
    (hp : 5 ≤ (p : ℕ)) {W : ℝ} (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (R M : ℝ) (hM : 1 < M) :
    ∃ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ) (c : WeilTestFn →₀ ℝ),
      (∀ i, 0 ≤ w i) ∧ (∀ i, R < t i) ∧ (∑ i, w i) = M ∧
      c = jointClusterMixture f (Real.log (p : ℕ)/2) w t ∧
      (∀ g, 0 ≤ c g) ∧ (∀ g ∈ c.support, ContDiff ℝ ∞ g.1) ∧
      (∀ n : ℕ, 2 ≤ n → c.sum (fun g r => r * logValue g.1 n) = 0) ∧
      c.sum (fun g r => (r : ℂ)*EF.weilTest g.1 g.1 0) =
        ((2*(1+M) : ℝ) : ℂ)*EF.weilTest f.1.1 f.1.1 0 := by
  obtain ⟨ι, hi, w, t, hw, ht, hm, hc⟩ := exists_joint_phase_correction p R M hM
  letI : Fintype ι := hi
  let c := jointClusterMixture f (Real.log (p : ℕ)/2) w t
  refine ⟨ι, hi, w, t, c, hw, ht, hm, rfl, jointClusterMixture_nonneg f _ w t hw,
    jointClusterMixture_smooth f _ w t, ?_, ?_⟩
  · intro n hn
    exact sum_logValue_of_null c n (jointClusterMixture_null f p hp hW hf w t hc n hn)
  · have hL := joint_half_log_prime_gt_log_two p hp
    have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    simpa only [hm] using jointClusterMixture_mass f hf (by linarith) (by linarith) w t

end RHTower.WeilWorkPBAP
