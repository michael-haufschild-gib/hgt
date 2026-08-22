import GaloisForLFunctions.HTGeometry.InvAbsTailL2

/-!
# Power tails outside a symmetric band are square integrable

For `a > 0` and `2r < -1` the kernel `1_{|u|>a} · |u|^r` lies in `L²(ℝ)`.  This is the exponent-`r`
version of `InvAbsTailL2.invAbsTail` (which is the case `r = -1`, kept separately because it is
stated with `|u|⁻¹` rather than an `rpow`).  It majorises the `χ`-kernel `(-2πui)^{s-1}` exactly
when `Re s < 1/2`, which is the regime in which Burnol's kernel identity is proved
(arXiv:math/0203120).

## Main results

* `memLp_two_powerTail`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- The tail kernel `1_{|u| > a} · |u|^r`. -/
def powerTail (a r : ℝ) : ℝ → ℝ := fun u => if a < |u| then |u| ^ r else 0

theorem measurable_powerTail (a r : ℝ) : Measurable (powerTail a r) := by
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_lt measurable_const continuous_abs.measurable
  · fun_prop

theorem integrable_sq_powerTail {a r : ℝ} (ha : 0 < a) (hr : 2 * r < -1) :
    Integrable (fun u : ℝ => ‖powerTail a r u‖ ^ 2) volume := by
  have hsq : (fun u : ℝ => ‖powerTail a r u‖ ^ 2)
      = fun u : ℝ => if a < |u| then |u| ^ (2 * r) else 0 := by
    funext u
    rw [powerTail]
    split
    · rename_i hu
      have hupos : 0 < |u| := lt_trans ha hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg u) r),
        ← Real.rpow_natCast (|u| ^ r) 2, ← Real.rpow_mul (abs_nonneg u)]
      congr 1
      push_cast
      ring
    · simp
  rw [hsq]
  set g : ℝ → ℝ := fun u : ℝ => if a < |u| then |u| ^ (2 * r) else 0 with hg
  have hgmeas : Measurable g := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const continuous_abs.measurable
    · fun_prop
  have heven : ∀ u : ℝ, g (-u) = g u := by
    intro u
    simp [hg, abs_neg]
  have hIoi : IntegrableOn g (Ioi a) volume := by
    have hbase : IntegrableOn (fun u : ℝ => u ^ (2 * r)) (Ioi a) volume := by
      rw [integrableOn_Ioi_rpow_iff ha]
      linarith
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hupos : 0 < u := lt_trans ha hu
    have hlt : a < |u| := by rwa [abs_of_pos hupos]
    show u ^ (2 * r) = g u
    simp only [hg, if_pos hlt, abs_of_pos hupos]
  have hIio : IntegrableOn g (Iio (-a)) volume := by
    have h_map_neg : ((volume : Measure ℝ).restrict (Ioi a)).map Neg.neg
        = (volume : Measure ℝ).restrict (Iio (-a)) := by
      conv_rhs => rw [← Measure.map_neg_eq_self (volume : Measure ℝ),
        measurableEmbedding_neg.restrict_map]
      congr 1
      ext x
      simp
    rw [IntegrableOn, ← h_map_neg, measurableEmbedding_neg.integrable_map_iff]
    refine hIoi.congr_fun ?_ measurableSet_Ioi
    intro u _
    exact (heven u).symm
  have hband : IntegrableOn g (Icc (-a) a) volume := by
    have hz : ∀ u ∈ Icc (-a) a, g u = 0 := by
      intro u hu
      have hnot : ¬ (a < |u|) := by
        rw [not_lt, abs_le]
        exact ⟨hu.1, hu.2⟩
      simp [hg, hnot]
    refine IntegrableOn.congr_fun ?_ (fun u hu => (hz u hu).symm) measurableSet_Icc
    exact integrableOn_zero
  have hunion : IntegrableOn g (Iio (-a) ∪ Icc (-a) a ∪ Ioi a) volume :=
    (IntegrableOn.union (IntegrableOn.union hIio hband) hIoi)
  have hcover : Iio (-a) ∪ Icc (-a) a ∪ Ioi a = univ := by
    ext u
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Icc, Set.mem_Ioi, Set.mem_univ, iff_true]
    rcases lt_trichotomy u (-a) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨le_of_eq h.symm, by linarith⟩)
    · rcases le_or_gt u a with h2 | h2
      · exact Or.inl (Or.inr ⟨le_of_lt h, h2⟩)
      · exact Or.inr h2
  rw [hcover, integrableOn_univ] at hunion
  exact hunion

theorem memLp_two_powerTail {a r : ℝ} (ha : 0 < a) (hr : 2 * r < -1) :
    MemLp (powerTail a r) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_powerTail a r).aestronglyMeasurable]
  exact integrable_sq_powerTail ha hr

end

end GaloisForLFunctions.HTGeometry
