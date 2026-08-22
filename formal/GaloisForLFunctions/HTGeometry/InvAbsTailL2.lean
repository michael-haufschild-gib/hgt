import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The `1/|u|` tail kernel is square integrable

Outside a symmetric band `{|u| ≤ a}` with `a > 0` the kernel `u ↦ 1/|u|` is square integrable.
This is the majorant against which the Fourier transform of a truncated power is compared in
Burnol's route to the de Branges entirety theorem (arXiv:math/0203120, Thm. 2.1): one integration
by parts gives `‖𝓕(1_{(T,T')}t^{-s})(u)‖ = O(1/|u|)` uniformly in `T'`, and pairing that against a
Sonine function — whose Fourier transform vanishes on the band — is then a Cauchy–Schwarz estimate
with the constant below.

## Main results

* `memLp_two_invAbsTail`
* `invAbsTailNorm_nonneg`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

noncomputable section

/-- The tail kernel `1_{|u| > a} · |u|⁻¹`. -/
def invAbsTail (a : ℝ) : ℝ → ℝ := fun u => if a < |u| then |u|⁻¹ else 0

theorem measurable_invAbsTail (a : ℝ) : Measurable (invAbsTail a) := by
  refine Measurable.ite ?_ (continuous_abs.measurable.inv) measurable_const
  exact measurableSet_lt measurable_const continuous_abs.measurable

theorem invAbsTail_nonneg (a : ℝ) (u : ℝ) : 0 ≤ invAbsTail a u := by
  rw [invAbsTail]
  split
  · positivity
  · exact le_rfl

/-- The squared tail kernel is integrable outside the band. -/
theorem integrable_sq_invAbsTail {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => ‖invAbsTail a u‖ ^ 2) volume := by
  have hsq : (fun u : ℝ => ‖invAbsTail a u‖ ^ 2)
      = fun u : ℝ => if a < |u| then (|u|⁻¹) ^ 2 else 0 := by
    funext u
    rw [invAbsTail]
    split
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ |u|⁻¹)]
    · simp
  rw [hsq]
  set g : ℝ → ℝ := fun u : ℝ => if a < |u| then (|u|⁻¹) ^ 2 else 0 with hg
  have hgmeas : Measurable g := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const continuous_abs.measurable
    · exact (continuous_abs.measurable.inv).pow_const 2
  have heven : ∀ u : ℝ, g (-u) = g u := by
    intro u
    simp [hg, abs_neg]
  have hpt : ∀ u : ℝ, 0 < u → u ^ (-2 : ℝ) = (u⁻¹) ^ 2 := by
    intro u hu
    have h1 : u ^ (-2 : ℝ) = (u ^ (2 : ℝ))⁻¹ := by rw [Real.rpow_neg hu.le]
    have h2 : u ^ (2 : ℝ) = u ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast u 2]
      norm_num
    rw [h1, h2, ← inv_pow]
  have hIoi : IntegrableOn g (Ioi a) := by
    have hbase : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi a) := by
      rw [integrableOn_Ioi_rpow_iff ha]
      norm_num
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hupos : 0 < u := lt_trans ha hu
    have hlt : a < |u| := by rwa [abs_of_pos hupos]
    show u ^ (-2 : ℝ) = g u
    have hgu : g u = (u⁻¹) ^ 2 := by
      simp only [hg]
      rw [abs_of_pos hupos, if_pos (mem_Ioi.mp hu)]
    rw [hgu, hpt u hupos]
  have hIio : IntegrableOn g (Iio (-a)) := by
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
  have hband : IntegrableOn g (Icc (-a) a) := by
    have hz : ∀ u ∈ Icc (-a) a, g u = 0 := by
      intro u hu
      have hnot : ¬ (a < |u|) := by
        rw [not_lt, abs_le]
        exact ⟨hu.1, hu.2⟩
      simp [hg, hnot]
    refine IntegrableOn.congr_fun ?_ (fun u hu => (hz u hu).symm) measurableSet_Icc
    exact integrableOn_zero
  have hunion : IntegrableOn g (Iio (-a) ∪ Icc (-a) a ∪ Ioi a) := by
    refine (IntegrableOn.union (IntegrableOn.union hIio hband) hIoi)
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

theorem memLp_two_invAbsTail {a : ℝ} (ha : 0 < a) : MemLp (invAbsTail a) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_invAbsTail a).aestronglyMeasurable]
  exact integrable_sq_invAbsTail ha

/-- The `L²` norm of the tail kernel outside the band `{|u| ≤ a}`. -/
def invAbsTailNorm (a : ℝ) : ℝ := (eLpNorm (invAbsTail a) 2 volume).toReal

theorem invAbsTailNorm_nonneg (a : ℝ) : 0 ≤ invAbsTailNorm a := ENNReal.toReal_nonneg

theorem eLpNorm_invAbsTail_ne_top {a : ℝ} (ha : 0 < a) :
    eLpNorm (invAbsTail a) 2 volume ≠ ⊤ := (memLp_two_invAbsTail ha).2.ne

end

end GaloisForLFunctions.HTGeometry
