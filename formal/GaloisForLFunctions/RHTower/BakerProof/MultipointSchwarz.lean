import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryArithmetic

/-!
# A multipoint Schwarz bound for Baker extrapolation

An entire function with prescribed multiplicity at finitely many points factors globally by the
corresponding node polynomial.  Maximum modulus applied to the entire quotient gives the sharp
product-ratio estimate used to make the next algebraic-integer component value small.
-/

open scoped Classical
open BigOperators NumberField

namespace GaloisForLFunctions.RHTower.BakerProof

/-- Global removal of one zero of prescribed multiplicity from an entire function. -/
theorem exists_entire_factor_of_natCast_le_analyticOrderAt
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (c : ℂ) (n : ℕ)
    (horder : n ≤ analyticOrderAt f c) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      ∀ z, f z = (z - c) ^ n * g z := by
  obtain ⟨g₀, hg₀, hlocal⟩ := (natCast_le_analyticOrderAt (hf c)).mp horder
  let g : ℂ → ℂ := fun z => if z = c then g₀ z else f z * ((z - c) ^ n)⁻¹
  have hg : ∀ z, AnalyticAt ℂ g z := by
    intro z
    by_cases hz : z = c
    · subst z
      apply hg₀.congr
      filter_upwards [hlocal] with w hw
      by_cases hwc : w = c
      · simp [g, hwc]
      · simp only [g, if_neg hwc]
        rw [hw]
        field_simp [sub_ne_zero.mpr hwc]
        ring
    · have hU : {w : ℂ | w ≠ c} ∈ nhds z := IsOpen.mem_nhds isOpen_ne hz
      have hquot : AnalyticAt ℂ (fun w => f w * ((w - c) ^ n)⁻¹) z :=
        (hf z).mul (((analyticAt_id.sub analyticAt_const).pow n).inv
          (pow_ne_zero n (sub_ne_zero.mpr hz)))
      apply hquot.congr
      filter_upwards [hU] with w hw
      simp [g, hw]
  refine ⟨g, hg, ?_⟩
  intro z
  by_cases hz : z = c
  · subst z
    simpa [g] using hlocal.self_of_nhds
  · simp only [g, if_neg hz]
    field_simp [sub_ne_zero.mpr hz]

/-- Simultaneous global removal of a constant prescribed multiplicity at finitely many points. -/
theorem exists_entire_factor_finset_of_natCast_le_analyticOrderAt
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (points : Finset ℂ) (n : ℕ)
    (horder : ∀ c ∈ points, n ≤ analyticOrderAt f c) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      ∀ z, f z = (∏ c ∈ points, (z - c) ^ n) * g z := by
  induction points using Finset.induction_on generalizing f with
  | empty =>
      exact ⟨f, hf, fun z => by simp⟩
  | @insert a points ha ih =>
      obtain ⟨g, hg, hfg⟩ := exists_entire_factor_of_natCast_le_analyticOrderAt
        f hf a n (horder a (Finset.mem_insert_self a points))
      have horder_g : ∀ c ∈ points, n ≤ analyticOrderAt g c := by
        intro c hc
        have hac : a ≠ c := fun hac => ha (hac ▸ hc)
        let factor : ℂ → ℂ := fun z => (z - a) ^ n
        have hfactor : ∀ z, AnalyticAt ℂ factor z := by
          intro z
          unfold factor
          fun_prop
        have hfactor_ne : factor c ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hac.symm)
        have hfactor_order : analyticOrderAt factor c = 0 :=
          (hfactor c).analyticOrderAt_eq_zero.mpr hfactor_ne
        have hfun : f = factor * g := by
          funext z
          simpa [factor] using hfg z
        have heq : analyticOrderAt f c = analyticOrderAt g c := by
          rw [hfun, analyticOrderAt_mul (hfactor c) (hg c), hfactor_order, zero_add]
        rw [← heq]
        exact horder c (Finset.mem_insert_of_mem hc)
      obtain ⟨h, hh, hgh⟩ := ih g hg horder_g
      refine ⟨h, hh, ?_⟩
      intro z
      rw [hfg z, hgh z]
      rw [Finset.prod_insert ha]
      ring

/-- **Multipoint Schwarz bound.**  Boundary control of an entire function and a positive lower
bound for its node polynomial give the exact interior product-ratio estimate after all prescribed
zeros are removed. -/
theorem multipoint_schwarz_bound
    (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) (points : Finset ℂ) (n : ℕ)
    (horder : ∀ c ∈ points, n ≤ analyticOrderAt f c)
    {R M D : ℝ} (hR : 0 < R) (hD : 0 < D)
    (hboundary_f : ∀ w ∈ Metric.sphere 0 R, ‖f w‖ ≤ M)
    (hboundary_factor : ∀ w ∈ Metric.sphere 0 R,
      D ≤ ‖∏ c ∈ points, (w - c) ^ n‖)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 R) :
    ‖f z‖ ≤ ‖∏ c ∈ points, (z - c) ^ n‖ * (M / D) := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_entire_factor_finset_of_natCast_le_analyticOrderAt f hf points n horder
  have hgd : Differentiable ℂ g := fun z => (hg z).differentiableAt
  have hboundary_g : ∀ w ∈ Metric.sphere 0 R, ‖g w‖ ≤ M / D := by
    intro w hw
    have hfM := hboundary_f w hw
    have hDP := hboundary_factor w hw
    rw [hfg w, norm_mul] at hfM
    rw [le_div_iff₀ hD]
    calc
      ‖g w‖ * D ≤ ‖g w‖ * ‖∏ c ∈ points, (w - c) ^ n‖ :=
        mul_le_mul_of_nonneg_left hDP (norm_nonneg _)
      _ = ‖∏ c ∈ points, (w - c) ^ n‖ * ‖g w‖ := by ring
      _ ≤ M := hfM
  have hgz : ‖g z‖ ≤ M / D := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) R))
      hgd.diffContOnCl
    · intro w hw
      rw [frontier_ball 0 hR.ne'] at hw
      exact hboundary_g w hw
    · rw [closure_ball 0 hR.ne']
      exact hz
  rw [hfg z, norm_mul]
  exact mul_le_mul_of_nonneg_left hgz (norm_nonneg _)

end GaloisForLFunctions.RHTower.BakerProof
