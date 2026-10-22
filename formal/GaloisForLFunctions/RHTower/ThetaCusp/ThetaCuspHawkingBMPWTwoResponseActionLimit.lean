import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWTwoResponseAction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWRetardedCausalWedge

/-!
# Exhaustion of the literal two-response action

Absolute source-response admission controls the combined wave and native bulk
action. Every bounded smooth exhaustion of the physical onset wedge has the
same limit. A concrete exhaustion supplies an unconditional action realization
for the complementary physical rates.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMPWTwoResponseActionLimit
open D4BMModularCore D4BMJointSource D4BMFullAngularCausalPeierls
open D4BMGlobalAngularResponse D4BMPWRetardedTriangle D4BMPWTwoResponseAction

noncomputable section
set_option autoImplicit false

theorem fullRetardedResponse_zero_nonpositive_onset (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (t x X k : ℝ) (hx : x < 0) (hp : t + x ≤ 0) :
    fullRetardedResponse q branch b a t x X k = 0 := by
  rcases hp.lt_or_eq with hlt | heq
  · exact fullRetardedResponse_zero_outside_wedge q branch b a t x X k (by linarith)
  · have h := fullRetardedResponse_eq_triangles q branch b a 0 (t - x) X k le_rfl
      (by linarith)
    simp only [intervalIntegral.integral_same, sub_self, zero_div] at h
    rw [show (0 + (t - x)) / 2 = t by linarith,
      show (0 - (t - x)) / 2 = x by linarith] at h
    exact h

private theorem source_retarded_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      fullRetardedResponse q branch c d p.1 p.2 X k) eventMeasure := by
  apply (full_source_response_pairings_integrable q branch c b d a X k).2.congr
  exact ae_of_all _ (fun p => mul_comm _ _)

private theorem sourceTest_tendsto (chi : ℕ → Event → ℝ)
    (hs : ∀ n, ContDiff ℝ ∞ (chi n)) (hc : ∀ n, HasCompactSupport (chi n))
    (hw : ∀ n, tsupport (chi n) ⊆ physicalWedge)
    (hb : ∀ n p, 0 ≤ chi n p ∧ chi n p ≤ 1)
    (hl : ∀ p ∈ physicalWedge, Tendsto (fun n => chi n p) atTop (𝓝 1))
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        responseTest (chi n) q branch c d X k p ∂eventMeasure) atTop
      (𝓝 (∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        fullRetardedResponse q branch c d p.1 p.2 X k ∂eventMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun p : Event => ‖timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      fullRetardedResponse q branch c d p.1 p.2 X k‖)
  · intro n
    exact (responseTest_source_integrable (chi n) (hs n) (hc n) (hw n)
      q branch b c a d X k).aestronglyMeasurable
  · exact (source_retarded_integrable q branch b c a d X k).norm
  · intro n
    apply ae_of_all
    intro p
    have hn : ‖(chi n p : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb n p).1]
        using (hb n p).2
    calc
      ‖timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          responseTest (chi n) q branch c d X k p‖ =
        ‖(chi n p : ℂ)‖ * ‖timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          fullRetardedResponse q branch c d p.1 p.2 X k‖ := by
            simp only [responseTest, norm_mul]
            ring
      _ ≤ 1 * ‖timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          fullRetardedResponse q branch c d p.1 p.2 X k‖ :=
        mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  · filter_upwards [eventMeasure_physical] with p hp
    by_cases hpos : 0 < p.1 + p.2
    · have hz : p ∈ physicalWedge := ⟨hpos, hp.2⟩
      have ht : Tendsto (fun n => (chi n p : ℂ)) atTop (𝓝 (1 : ℂ)) := by
        simpa only [Function.comp_def, Complex.ofReal_one] using
          Complex.continuous_ofReal.continuousAt.tendsto.comp (hl p hz)
      simpa only [responseTest, one_mul] using
        (tendsto_const_nhds.mul (ht.mul tendsto_const_nhds))
    · have hu := fullRetardedResponse_zero_nonpositive_onset q branch c d p.1 p.2 X k
        hp.2 (le_of_not_gt hpos)
      simpa only [responseTest, hu, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The combined action is independent of the bounded smooth exhaustion. No
separate convergence of the wave cap or native bulk is assumed. -/
theorem twoResponseAction_tendsto_of_exhaustion (chi : ℕ → Event → ℝ)
    (hs : ∀ n, ContDiff ℝ ∞ (chi n)) (hc : ∀ n, HasCompactSupport (chi n))
    (hw : ∀ n, tsupport (chi n) ⊆ physicalWedge)
    (hb : ∀ n p, 0 ≤ chi n p ∧ chi n p ≤ 1)
    (hl : ∀ p ∈ physicalWedge, Tendsto (fun n => chi n p) atTop (𝓝 1))
    (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => twoResponseAction (chi n) q branch b c a d X k) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch b c a d X k)) := by
  have hH : Tendsto (fun _ : ℕ => fullAngularField q branch ![X, Real.exp k]) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k])) := tendsto_const_nhds
  have hlim := hH.mul
    ((sourceTest_tendsto chi hs hc hw hb hl q branch b c a d X k).sub
      (sourceTest_tendsto chi hs hc hw hb hl q branch c b d a X k))
  rw [fullCausalSourcePair_eq_retarded_skew]
  apply hlim.congr'
  exact Eventually.of_forall (fun n =>
    (twoResponseAction_eq_contact (chi n) (hs n) (hc n) (hw n) q branch b c a d X k).symm)

/-- Unconditional two-response action realization for the literal full kernel. -/
theorem twoResponseAction_tendsto (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => twoResponseAction (wedgeWindow n) q branch b c a d X k) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch b c a d X k)) := by
  apply twoResponseAction_tendsto_of_exhaustion wedgeWindow wedgeWindow_smooth
    wedgeWindow_compact wedgeWindow_support
    (fun n p => ⟨wedgeWindow_nonneg n p, wedgeWindow_le_one n p⟩)
    _ q branch b c a d X k
  intro p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [wedgeWindow_eventually_one p hp] with n hn
  exact hn.symm

/-- Both complementary physical rates enter the actual action with no analytic premises. -/
theorem complementary_twoResponseAction_tendsto (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (X k : ℝ) :
    Tendsto (fun n => twoResponseAction (wedgeWindow n) q branch true false a d X k) atTop
      (𝓝 (fullAngularField q branch ![X, Real.exp k] *
        fullCausalSourcePair q branch true false a d X k)) :=
  twoResponseAction_tendsto q branch true false a d X k

end
end RHTower.D4BMPWTwoResponseActionLimit
