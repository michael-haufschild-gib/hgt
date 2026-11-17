import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sharp radial Kähler parameter classification

The boundary-flux profile `s^(n+1) (1-s/(n+2))` has one critical point
on the nonnegative axis. Strict monotonicity on either side gives the
sharp parameter ceiling and an exact two-root classification below it.
This is the scalar mechanism of Chen–Ma, Lemma 2.2, expressed in positive
complex dimension `n + 1`.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.RadialKahler
open Set

/-- Boundary-flux polynomial in positive complex dimension `n + 1`. -/
def profile (n : ℕ) (s : ℝ) : ℝ := s ^ (n + 1) * (1 - s / (n + 2))

/-- The sharp parameter ceiling. -/
def peak (n : ℕ) : ℝ := (n + 1 : ℝ) ^ (n + 1) / (n + 2)

theorem hasDerivAt_profile (n : ℕ) (s : ℝ) :
    HasDerivAt (profile n) (s ^ n * ((n + 1 : ℝ) - s)) s := by
  unfold profile
  have h := ((hasDerivAt_id s).pow (n + 1)).mul
    ((hasDerivAt_const s 1).sub ((hasDerivAt_id s).div_const (n + 2 : ℝ)))
  convert h using 1 <;> try rfl
  change s ^ n * (n + 1 - s) =
    ((n + 1 : ℕ) : ℝ) * s ^ (n + 1 - 1) * 1 * (1 - s / (n + 2)) +
      s ^ (n + 1) * (0 - 1 / (n + 2))
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one, zero_sub]
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  simp only [pow_succ]
  ring

theorem continuous_profile (n : ℕ) : Continuous (profile n) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_profile n s).continuousAt

theorem profile_zero (n : ℕ) : profile n 0 = 0 := by
  simp only [profile, zero_pow (Nat.succ_ne_zero n), zero_mul]

theorem profile_endpoint (n : ℕ) : profile n (n + 2) = 0 := by
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  rw [profile, div_self hn, sub_self, mul_zero]

theorem profile_at_peak (n : ℕ) : profile n (n + 1) = peak n := by
  unfold profile peak
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The lower branch increases strictly up to its unique critical point. -/
theorem profile_strictMonoOn (n : ℕ) :
    StrictMonoOn (profile n) (Icc 0 (n + 1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_profile n).continuousOn
  intro s hs
  rw [interior_Icc] at hs
  rw [(hasDerivAt_profile n s).deriv]
  exact mul_pos (pow_pos hs.1 n) (sub_pos.mpr hs.2)

/-- The upper branch decreases strictly, including beyond the zero at `n + 2`. -/
theorem profile_strictAntiOn (n : ℕ) :
    StrictAntiOn (profile n) (Ici (n + 1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (continuous_profile n).continuousOn
  intro s hs
  rw [interior_Ici] at hs
  rw [(hasDerivAt_profile n s).deriv]
  have hs0 : 0 < s := lt_trans (by positivity : (0 : ℝ) < n + 1) hs
  exact mul_neg_of_pos_of_neg (pow_pos hs0 n) (sub_neg.mpr hs)

/-- The polynomial has the sharp global upper bound on nonnegative fluxes. -/
theorem profile_le_peak (n : ℕ) (s : NNReal) : profile n s ≤ peak n := by
  rw [← profile_at_peak]
  by_cases hs : (s : ℝ) ≤ n + 1
  · exact (profile_strictMonoOn n).monotoneOn ⟨s.2, hs⟩ ⟨by positivity, le_rfl⟩ hs
  · exact (profile_strictAntiOn n).antitoneOn
      (show (n + 1 : ℝ) ≤ (n + 1 : ℝ) from le_rfl)
      (le_of_lt (lt_of_not_ge hs))
      (le_of_lt (lt_of_not_ge hs))

/-- Equality at the sharp ceiling singles out the critical flux. -/
theorem profile_eq_peak_iff (n : ℕ) (s : NNReal) :
    profile n s = peak n ↔ (s : ℝ) = n + 1 := by
  rw [← profile_at_peak]
  constructor
  · intro h
    by_cases hs : (s : ℝ) ≤ n + 1
    · exact (profile_strictMonoOn n).injOn ⟨s.2, hs⟩ ⟨by positivity, le_rfl⟩ h
    · exact (profile_strictAntiOn n).injOn (le_of_lt (lt_of_not_ge hs))
        (show (n + 1 : ℝ) ≤ (n + 1 : ℝ) from le_rfl) h
  · intro h
    rw [h]

/-- Exactly two nonnegative fluxes solve every strictly subcritical positive level. -/
theorem profile_two_branch_classification (n : ℕ) (y : ℝ) :
    (0 < y ∧ y < peak n) ↔
      ∃ a b : ℝ, 0 < a ∧ a < n + 1 ∧ n + 1 < b ∧ b < n + 2 ∧
        profile n a = y ∧ profile n b = y ∧
        ∀ s : NNReal, profile n s = y ↔ (s : ℝ) = a ∨ (s : ℝ) = b := by
  constructor
  · intro hy
    have hc : (0 : ℝ) ≤ n + 1 := by positivity
    obtain ⟨a, ha, hay⟩ := intermediate_value_Icc hc
      (continuous_profile n).continuousOn
      (show y ∈ Icc (profile n 0) (profile n (n + 1)) by
        rw [profile_zero, profile_at_peak]
        exact ⟨hy.1.le, hy.2.le⟩)
    obtain ⟨b, hb, hby⟩ := intermediate_value_Icc' (by linarith : (n + 1 : ℝ) ≤ n + 2)
      (continuous_profile n).continuousOn
      (show y ∈ Icc (profile n (n + 2)) (profile n (n + 1)) by
        rw [profile_endpoint, profile_at_peak]
        exact ⟨hy.1.le, hy.2.le⟩)
    have ha0 : 0 < a := by
      by_contra h
      have hz : a = 0 := le_antisymm (le_of_not_gt h) ha.1
      rw [hz, profile_zero] at hay
      exact hy.1.ne' hay.symm
    have hac : a < n + 1 := by
      by_contra h
      have hz : a = n + 1 := le_antisymm ha.2 (le_of_not_gt h)
      rw [hz, profile_at_peak] at hay
      exact hy.2.ne hay.symm
    have hcb : n + 1 < b := by
      by_contra h
      have hz : b = n + 1 := le_antisymm (le_of_not_gt h) hb.1
      rw [hz, profile_at_peak] at hby
      exact hy.2.ne hby.symm
    have hb1 : b < n + 2 := by
      by_contra h
      have hz : b = n + 2 := le_antisymm hb.2 (le_of_not_gt h)
      rw [hz, profile_endpoint] at hby
      exact hy.1.ne' hby.symm
    refine ⟨a, b, ha0, hac, hcb, hb1, hay, hby, ?_⟩
    intro s
    constructor
    · intro hs
      by_cases hsc : (s : ℝ) ≤ n + 1
      · exact Or.inl ((profile_strictMonoOn n).injOn ⟨s.2, hsc⟩ ha (hs.trans hay.symm))
      · exact Or.inr ((profile_strictAntiOn n).injOn
          (le_of_lt (lt_of_not_ge hsc)) hb.1 (hs.trans hby.symm))
    · rintro (hs | hs)
      · rw [hs, hay]
      · rw [hs, hby]
  · rintro ⟨a, b, ha0, hac, _, _, hay, _, _⟩
    have hn : (0 : ℝ) < n + 2 := by positivity
    have haend : a < n + 2 := by linarith only [hac]
    have hp : 0 < profile n a := mul_pos (pow_pos ha0 _)
      (sub_pos.mpr ((div_lt_one hn).mpr haend))
    refine ⟨hay ▸ hp, ?_⟩
    rw [← hay, ← profile_at_peak]
    exact profile_strictMonoOn n ⟨ha0.le, hac.le⟩ ⟨by positivity, le_rfl⟩ hac

#print axioms profile_strictMonoOn
#print axioms profile_strictAntiOn
#print axioms profile_le_peak
#print axioms profile_eq_peak_iff
#print axioms profile_two_branch_classification
end GaloisForLFunctions.HilbertMetric.RadialKahler