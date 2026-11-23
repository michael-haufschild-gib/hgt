import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.DiscreteRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.PositiveMass
import GaloisForLFunctions.HTGeometry.Lattices.LatticeBallCounting

/-! # Gaussian rate for continuously shrinking first-passage deadlines -/
open MeasureTheory ProbabilityTheory Filter Real Set Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The inverse-square-time logarithmic probability converges at every
positive deadline approaching zero. Its rate is the logarithm of the
essential supremum of the radial weight on the unit-deadline event. -/
theorem gaussian_continuous_passage_rate (F : (ι → ℝ) → ℝ) (hf : Measurable F)
    (hom : ∀ a > (0:ℝ), ∀ x, a*F (a • x)=F x) :
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    Tendsto (fun t : ℝ => t^2*log (μ.real {x | F x ≤ t}))
      (𝓝[>] 0) (𝓝 (log (essSup (unitWeight F) μ))) := by
  intro μ
  let W := essSup (unitWeight F) μ
  let p (t : ℝ) := μ.real {x | F x ≤ t}
  have hp (t : ℝ) (ht : 0 < t) : 0 < p t :=
    ENNReal.toReal_pos (deadline_pos F hf hom ht).ne' (measure_ne_top _ _)
  have hmono : Monotone p := fun _ _ hab => measureReal_mono (fun _ hx => le_trans hx hab)
  let q (s : ℝ) := (sqrt (max s 0+1))⁻¹
  have hroot s : 0 < sqrt (max s 0+1) := sqrt_pos.mpr (by linarith only [le_max_right s (0:ℝ)])
  let G (s : ℝ) := -log (p (q s))
  have hG : Monotone G := by
    intro s u hsu
    apply neg_le_neg
    exact log_le_log (hp _ (inv_pos.mpr (hroot u))) (hmono (inv_anti₀ (hroot s)
      (sqrt_le_sqrt (add_le_add_left (max_le_max_right 0 hsu) 1))))
  have hG₀ (s) : 0 ≤ G s := by
    apply neg_nonneg.mpr
    apply log_nonpos (hp _ (inv_pos.mpr (hroot s))).le
    exact (measureReal_mono (μ:=μ) (subset_univ _)).trans_eq probReal_univ
  have hW : 0 < W := passage_weight_positive F hf hom
  have hmesh := (continuousAt_log hW.ne').tendsto.comp (gaussian_discrete_passage_rate F hf hom)
  have hnat : Tendsto (fun n : ℕ => G n/(n:ℝ)^1) atTop (𝓝 (-log W)) := by
    apply hmesh.neg.congr
    intro n
    dsimp only [Function.comp_apply,G,q]
    rw [max_eq_left (Nat.cast_nonneg n),pow_one,log_rpow (hp _ (inv_pos.mpr
      (sqrt_pos.mpr (by positivity))))]
    ring
  have hr := LatticeBallCounting.tendsto_real_div_pow_of_nat hG hG₀ hnat
  let u (t : ℝ) := t⁻¹^2-1
  have hi : Tendsto (fun t : ℝ => t⁻¹^2) (𝓝[>] 0) atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_inv_nhdsGT_zero
  have hu : Tendsto u (𝓝[>] 0) atTop := by
    simpa only [u,sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1:ℝ) hi
  have hz : Tendsto (fun t : ℝ => 1-t^2) (𝓝[>] 0) (𝓝 1) := by
    have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub (ht.pow 2)
  have hall := ((hr.comp hu).mul hz).neg
  rw [mul_one,neg_neg] at hall
  apply hall.congr'
  filter_upwards [self_mem_nhdsWithin,hu.eventually (eventually_gt_atTop (0:ℝ))] with t ht ht'
  have ht₀ : 0 < t := ht
  have hq : q (u t)=t := by
    dsimp only [q]
    rw [max_eq_left ht'.le,show u t+1=t⁻¹^2 by dsimp only [u]; ring,
      sqrt_sq (inv_pos.mpr ht₀).le,inv_inv]
  change -(G (u t)/(u t)^1*(1-t^2))=t^2*log (p t)
  rw [pow_one,show G (u t)= -log (p t) by rw [G,hq]]
  have hs : (u t)*t^2=1-t^2 := by dsimp only [u]; field_simp [ht₀.ne']
  rw [←hs]
  field_simp [ht'.ne']

#print axioms gaussian_continuous_passage_rate
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
