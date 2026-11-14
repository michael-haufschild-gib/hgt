import GaloisForLFunctions.HTGeometry.VivantiPringsheim
import GaloisForLFunctions.Bottcher.ArcContinuation

/-!
# Rigidity of cancellation at an analytic boundary

Functions admitting analytic continuation from a fixed domain across a fixed point form a complex
vector space. Consequently an affine family `f + c * g` has either no continuable member, exactly
one, or every member. Failure of continuation of `g` is exactly the condition excluding the last
case for every `f`.

The continuation is a germ agreeing on the original domain; values of a totalized series outside
its convergence domain play no role.
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Functions admitting continuation from `D` across `z` form a vector subspace. -/
def continuationSubmodule (D : Set ℂ) (z : ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContinuesAcross f D z}
  zero_mem' := ⟨0, analyticAt_const, Filter.Eventually.of_forall fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨F, hF, heF⟩ ⟨G, hG, heG⟩
    refine ⟨F + G, hF.add hG, ?_⟩
    filter_upwards [heF, heG] with w hwF hwG
    exact congrArg₂ (· + ·) hwF hwG
  smul_mem' := by
    rintro c f ⟨F, hF, heF⟩
    refine ⟨fun w => c * F w, analyticAt_const.mul hF, ?_⟩
    filter_upwards [heF] with w hw
    exact congrArg (c * ·) hw

/-- A singular direction admits at most one cancellable coefficient, for every offset function. -/
theorem not_continuesAcross_iff_affine_coefficients_subsingleton
    (g : ℂ → ℂ) (D : Set ℂ) (z : ℂ) :
    ¬ ContinuesAcross g D z ↔
      ∀ f : ℂ → ℂ,
        {c : ℂ | ContinuesAcross (fun w => f w + c * g w) D z}.Subsingleton := by
  let S := continuationSubmodule D z
  constructor
  · intro hg f c hc d hd
    by_contra hcd
    have hsub : (fun w => (c - d) * g w) ∈ S := by
      convert S.sub_mem hc hd using 1
      ext w
      simp only [Pi.sub_apply]
      ring
    have hrec := S.smul_mem (c - d)⁻¹ hsub
    apply hg
    change g ∈ S
    convert hrec using 1
    ext w
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hcd]
  · intro h hg
    have hzero : (0 : ℂ) ∈
        {c : ℂ | ContinuesAcross (fun w => (0 : ℂ) + c * g w) D z} := by
      simpa only [zero_mul, zero_add] using S.zero_mem
    have hone : (1 : ℂ) ∈
        {c : ℂ | ContinuesAcross (fun w => (0 : ℂ) + c * g w) D z} := by
      simpa only [one_mul, zero_add] using hg
    exact zero_ne_one (h (fun _ => 0) hzero hone)

/-- The possible continuation coefficients are empty, a singleton, or the entire complex line. -/
theorem affine_continuation_coefficients_classification
    (f g : ℂ → ℂ) (D : Set ℂ) (z : ℂ) :
    {c : ℂ | ContinuesAcross (fun w => f w + c * g w) D z} = ∅ ∨
      (∃ c : ℂ, {d : ℂ | ContinuesAcross (fun w => f w + d * g w) D z} = {c}) ∨
      {c : ℂ | ContinuesAcross (fun w => f w + c * g w) D z} = univ := by
  classical
  let S := continuationSubmodule D z
  let C := {c : ℂ | ContinuesAcross (fun w => f w + c * g w) D z}
  by_cases hC : C.Nonempty
  · obtain ⟨c, hc⟩ := hC
    by_cases hg : ContinuesAcross g D z
    · right; right
      apply eq_univ_of_forall
      intro d
      have h := S.add_mem hc (S.smul_mem (d - c) hg)
      change (fun w => f w + d * g w) ∈ S
      convert h using 1
      ext w
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · right; left
      exact ⟨c, ((not_continuesAcross_iff_affine_coefficients_subsingleton g D z).mp hg f)
        .eq_singleton_of_mem hc⟩
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hC)

/-- A continuing germ has a representative on an open neighborhood. -/
theorem continuesAcross_iff_open_representative (f : ℂ → ℂ) (D : Set ℂ) (z : ℂ) :
    ContinuesAcross f D z ↔
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧
        ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U ∩ D) := by
  constructor
  · rintro ⟨F, hF, heF⟩
    obtain ⟨r, hr, hFB⟩ := hF.exists_ball_analyticOnNhd
    rw [eventually_nhdsWithin_iff] at heF
    obtain ⟨W, hWsub, hWo, hzW⟩ := mem_nhds_iff.mp heF
    refine ⟨Metric.ball z r ∩ W, Metric.isOpen_ball.inter hWo,
      ⟨Metric.mem_ball_self hr, hzW⟩, F, ?_, ?_⟩
    · intro w hw
      exact (hFB w hw.1).differentiableAt.differentiableWithinAt
    · intro w hw
      exact hWsub hw.1.2 hw.2
  · rintro ⟨U, hU, hzU, F, hF, heF⟩
    refine ⟨F, hF.analyticOnNhd hU z hzU, ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (hU.mem_nhds hzU).filter_mono nhdsWithin_le_nhds] with w hwD hwU
    exact heF ⟨hwU, hwD⟩

/-- The locus of continuation is open, even when the original domain is arbitrary. -/
theorem isOpen_continuation_locus (f : ℂ → ℂ) (D : Set ℂ) :
    IsOpen {z : ℂ | ContinuesAcross f D z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hzU, F, hF, heF⟩ :=
    (continuesAcross_iff_open_representative f D z).mp hz
  apply mem_of_superset (hU.mem_nhds hzU)
  intro w hw
  exact (continuesAcross_iff_open_representative f D w).mpr ⟨U, hU, hw, F, hF, heF⟩

/-- The disk-neighborhood and germ formulations of analytic continuation agree. -/
theorem continuesAcross_disk_iff (f : ℂ → ℂ) (z : ℂ) :
    ContinuesAcross f (Metric.ball 0 1) z ↔ Bottcher.ContinuesAcross f z :=
  continuesAcross_iff_open_representative f (Metric.ball 0 1) z

/-- Only countably many coefficients can repair any singular point of a fixed direction.
Distinct coefficients have disjoint open continuation loci on that direction's singular set. -/
theorem countable_coefficients_continuing_at_singular_points
    (f g : ℂ → ℂ) (D : Set ℂ) :
    {c : ℂ | ∃ z : ℂ, ¬ ContinuesAcross g D z ∧
      ContinuesAcross (fun w => f w + c * g w) D z}.Countable := by
  let E := {z : ℂ | ¬ ContinuesAcross g D z}
  let C := {c : ℂ | ∃ z : ℂ, ¬ ContinuesAcross g D z ∧
    ContinuesAcross (fun w => f w + c * g w) D z}
  let U : ℂ → Set E := fun c =>
    {z : E | ContinuesAcross (fun w => f w + c * g w) D z.1}
  have hdisj : C.PairwiseDisjoint U := by
    intro c _ d _ hcd
    apply Set.disjoint_left.mpr
    intro z hcz hdz
    exact hcd ((not_continuesAcross_iff_affine_coefficients_subsingleton g D z.1).mp
      z.2 f hcz hdz)
  apply hdisj.countable_of_isOpen
  · intro c _
    exact (isOpen_continuation_locus (fun w => f w + c * g w) D).preimage
      continuous_subtype_val
  · rintro c ⟨z, hgz, hcz⟩
    exact ⟨⟨z, hgz⟩, hcz⟩

end

end GaloisForLFunctions.HTGeometry
