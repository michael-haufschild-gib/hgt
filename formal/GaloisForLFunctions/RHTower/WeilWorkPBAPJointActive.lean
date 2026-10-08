import GaloisForLFunctions.RHTower.WeilWorkPBAPJointNull
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointEscape

/-!
# Actual real nullness and active shifted nodes

For broad cosine/sine two-cluster mixtures, the literal symmetric real
integer constraints are equivalent to the phase equations precisely where
the base autocorrelation has nonzero real part. Two such distinct nodes
force logarithmic frequency cost to diverge near correction mass one.
No complex-null premise, inactive-node equation, or energy positivity
hypothesis is used. The full Weil-energy lower bound remains separate.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Exact real integer sample: inactive real autocorrelation nodes impose no phase equation. -/
theorem jointClusterMixture_logValue {ι : Type} [Fintype ι] (f : JointSmoothTest)
    {L W : ℝ} (hL : 0 ≤ L) (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (w t : ι → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (jointClusterMixture f L w t).sum (fun g r => r * logValue g.1 n) =
      -2 * (EF.weilTest f.1.1 f.1.1 (Real.log n-L)).re *
        (1 + ∑ i, w i*Real.cos ((Real.log n-L)*t i)) / Real.sqrt n := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hz : jointProfileSample f w t (Real.log n) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by
      rw [abs_of_pos (lt_of_lt_of_le hlog2 hlog)]; linarith)
  have hp : jointProfileSample f w t (Real.log n+L) = 0 :=
    jointProfileSample_zero_of_radius f w t hf (by
      rw [abs_of_pos (by linarith : 0 < Real.log n+L)]; linarith)
  rw [joint_sum_logValue, jointClusterMixture_autocorrelation, hz, hp,
    jointProfileSample_eq]
  simp only [mul_zero, zero_sub, sub_zero, Complex.neg_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  simp_rw [mul_comm (t _) (Real.log n-L)]
  ring

/-- Actual real nullness forces the phase equation at each real-active node. -/
theorem joint_phase_of_active_null {ι : Type} [Fintype ι] (f : JointSmoothTest)
    {L W : ℝ} (hL : 0 ≤ L) (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (w t : ι → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (ha : (EF.weilTest f.1.1 f.1.1 (Real.log n-L)).re ≠ 0)
    (hz : (jointClusterMixture f L w t).sum (fun g r => r * logValue g.1 n) = 0) :
    1 + ∑ i, w i*Real.cos ((Real.log n-L)*t i) = 0 := by
  rw [jointClusterMixture_logValue f hL hW hf w t n hn] at hz
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0<n from lt_of_lt_of_le (by norm_num) hn)))
  have hprod := congrArg (fun x : ℝ => x*Real.sqrt n) hz
  rw [div_mul_cancel₀ _ hs, zero_mul] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero (by norm_num) ha)

/-- Full PBAP real nullness in this family is equivalent to the actual active-node equations. -/
theorem jointClusterMixture_null_iff_active {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (p : Nat.Primes) (hp : 5 ≤ (p : ℕ)) {W : ℝ}
    (hW : W < Real.log 2) (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (w t : ι → ℝ) :
    (∀ n : ℕ, 2 ≤ n → (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
      (fun g r => r * logValue g.1 n) = 0) ↔
    (∀ n : ℕ, 2 ≤ n → n < (p : ℕ) →
      (EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2)).re ≠ 0 →
      1 + ∑ i, w i*Real.cos ((Real.log n-Real.log (p : ℕ)/2)*t i) = 0) := by
  have hL := joint_half_log_prime_gt_log_two p hp
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  constructor
  · intro hz n hn _ ha
    exact joint_phase_of_active_null f (by linarith) hW hf w t n hn ha (hz n hn)
  · intro hc n hn
    rw [jointClusterMixture_logValue f (by linarith) hW hf w t n hn]
    by_cases hnp : n < (p : ℕ)
    · by_cases ha : (EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2)).re = 0
      · rw [ha]; ring
      · rw [hc n hn hnp ha]; ring
    · have hlp : Real.log (p : ℕ) ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast p.2.pos) (by exact_mod_cast not_lt.mp hnp)
      have hz : EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2) = 0 :=
        weilTest_eq_zero_outside_interval hf (by
          rw [abs_of_pos (by linarith : 0<Real.log n-Real.log (p : ℕ)/2)]; linarith)
      rw [hz]; simp

/-- The two-node obstruction applies to the literal real null-mixture interface.
No equations at inactive nodes, complex-null premise, or Weil positivity are required. -/
theorem joint_actual_null_logCost_escape (f : JointSmoothTest) (p : Nat.Primes)
    (hp : 5 ≤ (p : ℕ)) {W : ℝ} (hW : W < Real.log 2)
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hnp : n < (p : ℕ)) (hmp : m < (p : ℕ))
    (hnm : n ≠ m)
    (han : (EF.weilTest f.1.1 f.1.1 (Real.log n-Real.log (p : ℕ)/2)).re ≠ 0)
    (ham : (EF.weilTest f.1.1 f.1.1 (Real.log m-Real.log (p : ℕ)/2)).re ≠ 0) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ι : Type) (_ : Fintype ι) (w t : ι → ℝ),
      (∀ i, 0 ≤ w i) →
      (∀ k : ℕ, 2 ≤ k → (jointClusterMixture f (Real.log (p : ℕ)/2) w t).sum
        (fun g r => r * logValue g.1 k) = 0) →
      (∑ i, w i) < 1+δ → A < ∑ i, w i*Real.log (2+|t i|) := by
  obtain ⟨δ, hδ, hcost⟩ := joint_pair_logCost_diverges_at_mass_one p
    (show 0 < n by omega) (show 0 < m by omega) hnp hmp hnm A
  refine ⟨δ, hδ, ?_⟩
  intro ι hi w t hw hz hmass
  letI : Fintype ι := hi
  have hc := (jointClusterMixture_null_iff_active f p hp hW hf w t).mp hz
  exact hcost ι hi w t hw ⟨hc n hn hnp han, hc m hm hmp ham⟩ hmass

end RHTower.WeilWorkPBAP
