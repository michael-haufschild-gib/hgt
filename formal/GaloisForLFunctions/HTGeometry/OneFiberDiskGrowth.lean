import GaloisForLFunctions.HTGeometry.ModularDiskChart
import GaloisForLFunctions.Bottcher.AnalyticRoot
import GaloisForLFunctions.HTGeometry.HolomorphicBranch

/-!
# Uniform disk growth from one omitted value and one center preimage

An analytic square root of f−a, normalized to value −1 at the center, omits both 0 and 1 when
the center is the unique preimage of its value. The compact-base Schottky theorem then gives
a universal ratio bound on the half disk. Full injectivity is not required.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- A unique center fiber and one omitted value give a universal local ratio bound. -/
theorem exists_one_fiber_omitted_value_disk_bound :
    ∃ B : ℝ, 1 < B ∧ ∀ (f : ℂ → ℂ) (c a : ℂ) (R : ℝ), 0 < R →
      DifferentiableOn ℂ f (ball c R) →
      (∀ z ∈ ball c R, f z = f c → z = c) →
      (∀ z ∈ ball c R, f z ≠ a) →
      ∀ z : ℂ, ‖z - c‖ ≤ R / 2 → ‖f z - a‖ ≤ B * ‖f c - a‖ := by
  obtain ⟨M, hM⟩ := exists_bound_of_omitting_compact_base
    (K := {(-1 : ℂ)}) (isCompact_singleton)
    (by intro v hv; have hv' : v = -1 := hv; rw [hv']; norm_num)
    (by intro v hv; have hv' : v = -1 := hv; rw [hv']; norm_num)
    (ρ := 3 / 4) (by norm_num) (by norm_num)
  let M' : ℝ := max 1 M
  have hM' : 1 ≤ M' := le_max_left _ _
  have hMM' : M ≤ M' := le_max_right _ _
  refine ⟨M' ^ 2 + 1, by nlinarith, ?_⟩
  intro f c a R hR hf hsingle homit z hz
  have hc : c ∈ ball c R := mem_ball_self hR
  have hsimply : IsSimplyConnected (ball c R) :=
    isSimplyConnected_of_convex (convex_ball c R) ⟨c, hc⟩
  have hfa : AnalyticOnNhd ℂ (fun w => f w - a) (ball c R) :=
    (hf.analyticOnNhd isOpen_ball).sub analyticOnNhd_const
  have hne : ∀ w ∈ ball c R, f w - a ≠ 0 := fun w hw => sub_ne_zero.2 (homit w hw)
  obtain ⟨s, hs, hsq⟩ := Bottcher.exists_analyticOnNhd_pow_eq hsimply isOpen_ball
    hfa hne (N := 2) (by norm_num)
  have hs0 : ∀ w ∈ ball c R, s w ≠ 0 := by
    intro w hw hzero
    have heq := hsq w hw
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at heq
    exact hne w hw heq.symm
  let ψ : ℂ → ℂ := fun w => -(s w) / s c
  have hψ : DifferentiableOn ℂ ψ (ball c R) := hs.differentiableOn.neg.div_const _
  have hψc : ψ c = -1 := by dsimp [ψ]; rw [neg_div, div_self (hs0 c hc)]
  have hψomit : ∀ w ∈ ball c R, ψ w ≠ 0 ∧ ψ w ≠ 1 := by
    intro w hw
    constructor
    · exact div_ne_zero (neg_ne_zero.2 (hs0 w hw)) (hs0 c hc)
    · intro h
      have hsc : -(s w) = s c := (div_eq_one_iff_eq (hs0 c hc)).1 h
      have hsame : f w = f c := by
        have heq : s w ^ 2 = s c ^ 2 := by rw [← hsc]; ring
        rw [hsq w hw, hsq c hc] at heq
        linear_combination heq
      have hwc := hsingle w hw hsame
      subst w
      rw [hψc] at h
      norm_num at h
  have hzsmall : z ∈ ball c ((3 / 4 : ℝ) * R) := by
    rw [mem_ball, dist_eq_norm]
    linarith
  have hψbound : ‖ψ z‖ ≤ M' :=
    (hM ψ c R hR hψ hψomit (by simp [hψc]) z hzsmall).trans hMM'
  have hsz : ‖s z‖ ≤ M' * ‖s c‖ := by
    have hscnorm : 0 < ‖s c‖ := norm_pos_iff.2 (hs0 c hc)
    dsimp [ψ] at hψbound
    rw [norm_div, norm_neg, div_le_iff₀ hscnorm] at hψbound
    exact hψbound
  have hzball : z ∈ ball c R := by rw [mem_ball, dist_eq_norm]; linarith
  have hnormz : ‖f z - a‖ = ‖s z‖ ^ 2 := by rw [← hsq z hzball, norm_pow]
  have hnormc : ‖f c - a‖ = ‖s c‖ ^ 2 := by rw [← hsq c hc, norm_pow]
  rw [hnormz, hnormc]
  have hsqbound := pow_le_pow_left₀ (norm_nonneg (s z)) hsz 2
  nlinarith [sq_nonneg ‖s c‖]

end GaloisForLFunctions.HTGeometry
