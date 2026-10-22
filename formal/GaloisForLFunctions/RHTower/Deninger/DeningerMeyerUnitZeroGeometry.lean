import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHorizontalInterpolation

/-! # The zeros of a unitized source escape horizontally

Every unitized Mellin transform tends to one at vertical infinity on each
strip. Its full zero divisor therefore has precisely the geometry required
by original-source horizontal interpolation.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

namespace DeningerEntireMellinRegular

variable {F : ℂ → ℂ} (hF : DeningerEntireMellinRegular F)
include hF

theorem unit_tail (r : ℝ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ,
    |z.re| ≤ r → R ≤ |z.im| → (1/2 : ℝ) ≤ ‖1+F z‖ := by
  obtain ⟨C, hC, hb⟩ := hF.weighted_strip_bound r 1
  refine ⟨2*C+1, by positivity, fun z hz hzi => ?_⟩
  have hy : 1 ≤ |z.im| := by linarith
  have hsq : |z.im| ≤ z.im^2 := by nlinarith [sq_abs z.im]
  have hsmall : ‖F z‖ ≤ (1/2 : ℝ) := by
    calc ‖F z‖ ≤ C/(1+z.im^2) :=
        (le_div_iff₀ (by positivity : 0 < 1+z.im^2)).mpr (by simpa using hb z hz)
      _ ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 1+z.im^2)).mpr (by linarith)
  have hn := norm_sub_norm_le (1 : ℂ) (-F z)
  simp only [norm_one, norm_neg, sub_neg_eq_add] at hn
  linarith

theorem unit_not_identically_zero : ∃ z : ℂ, 1+F z ≠ 0 := by
  obtain ⟨R, hR, hb⟩ := hF.unit_tail 0
  refine ⟨(R : ℂ)*I, ?_⟩
  have h := hb ((R : ℂ)*I) (by simp) (by simp [abs_of_nonneg hR])
  exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) h)

theorem unit_order_ne_top (z : ℂ) :
    analyticOrderAt (fun z => 1+F z) z ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hF.unit_not_identically_zero
  have hA : AnalyticOnNhd ℂ (fun z => 1+F z) univ := fun z _ =>
    ((differentiable_const 1).add hF.differentiable).differentiableOn.analyticAt univ_mem
  intro hz
  exact hw (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) (analyticOrderAt_eq_top.mp hz) (mem_univ w))

theorem unit_zeros_strip_finite (r : ℝ) :
    {z : ℂ | 1+F z = 0 ∧ |z.re| ≤ r}.Finite := by
  obtain ⟨w, hw⟩ := hF.unit_not_identically_zero
  have hA : AnalyticOnNhd ℂ (fun z => 1+F z) univ := fun z _ =>
    ((differentiable_const 1).add hF.differentiable).differentiableOn.analyticAt univ_mem
  have hcod : ∀ᶠ z in codiscreteWithin (univ : Set ℂ), 1+F z ≠ 0 :=
    (hA.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
      (fun h => hw (h (mem_univ w)))
  obtain ⟨R, _, hb⟩ := hF.unit_tail r
  have hfin := (isCompact_closedBall (0 : ℂ) (r+R)).finite_sdiff_of_mem_codiscreteWithin
    (hcod.filter_mono (codiscreteWithin_mono (subset_univ _)))
  apply hfin.subset
  rintro z ⟨hz, hzr⟩
  have hzi : |z.im| < R := by
    by_contra h
    have hnorm := hb z hzr (le_of_not_gt h)
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  refine ⟨?_, by simpa only [mem_setOf_eq, not_not] using hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

theorem unit_zeros_countable : {z : ℂ | 1+F z = 0}.Countable := by
  apply (Set.countable_iUnion fun n : ℕ => (hF.unit_zeros_strip_finite n).countable).mono
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_ge |z.re|
  exact mem_iUnion.mpr ⟨n, hz, hn⟩

theorem unit_zeros_horizontal_escape :
    Tendsto (fun z : {z : ℂ // 1+F z = 0} => |z.val.re|) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro r
  rw [eventually_cofinite]
  have hfin := (hF.unit_zeros_strip_finite r).preimage
    (Set.injOn_of_injective (Subtype.coe_injective :
      Function.Injective (Subtype.val : {z : ℂ // 1+F z = 0} → ℂ)))
  apply hfin.subset
  intro z hz
  exact ⟨z.property, (lt_of_not_ge hz).le⟩

theorem unit_strip_bound (a b : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖1+F z‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := hF.strip_bound a b
  refine ⟨1+C, by positivity, fun z hza hzb => ?_⟩
  exact (norm_add_le _ _).trans (by simpa using add_le_add_left (hb z hza hzb) 1)

end DeningerEntireMellinRegular
end
end RHTower
