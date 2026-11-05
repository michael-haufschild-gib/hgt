import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelHasItsEndpointSlope
import GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone.TheEvaluationKernelsHaveAHamiltonianDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Absolute continuity of the precontact diagonal Weil kernels

The two actual endpoint traces give the finite right derivative everywhere.
Approximation from smaller windows gives left continuity. Monotonicity and
the one-sided fundamental theorem of calculus then recover every kernel
increment by integrating the trace energy.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
open _root_.RHTower CanonicalSystemOfTheWindowTower
open CanonicalSystemOfTheWindowTower.WeilHilbertBeforeContact

/-- The diagonal evaluation Gram, extended by zero outside the precontact interval. -/
def diagonalEvalGram (z : ℂ) : ℝ → ℝ :=
  evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => z)

/-- The actual endpoint energy, in the real aperture coordinate. -/
def diagonalEndpointEnergy (z : ℂ) (a : ℝ) : ℝ :=
  open Classical in
  if h : a ∈ precontactSet then evalEndpointEnergy (toPrecontact h) z else 0

theorem diagonalEvalGram_eq_norm (z : ℂ) (a : PrecontactAperture) :
    diagonalEvalGram z a.1.1 = ‖evalVector a z‖^2 := by
  have ha : a.1.1 ∈ precontactSet := ⟨a.1.2, a.2⟩
  simp only [diagonalEvalGram, evalGram, dif_pos ha]
  simp [evalCombination, toPrecontact]

theorem diagonalEvalGram_eq_kernel (z : ℂ) (a : PrecontactAperture) :
    diagonalEvalGram z a.1.1 = (kernel a z z).re := by
  rw [diagonalEvalGram_eq_norm]
  change ‖evalVector a z‖^2 = (eval a z (evalVector a z)).re
  rw [evalVector_self, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem diagonalEvalGram_sub_eq {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    diagonalEvalGram z b.1.1-diagonalEvalGram z a.1.1 =
      ‖evalVectorIncrement hab z‖^2 := by
  rw [diagonalEvalGram_eq_kernel, diagonalEvalGram_eq_kernel,
    ← Complex.sub_re, kernel_diagonal_sub_eq_norm_increment_sq hab]

/-- At every strictly precontact aperture the right derivative is the actual
sum of the two endpoint trace energies. -/
theorem hasDerivWithinAt_diagonalEvalGram_right (z : ℂ) {a : ℝ}
    (ha : a ∈ precontactSet) :
    HasDerivWithinAt (diagonalEvalGram z) (diagonalEndpointEnergy z a) (Ioi a) a := by
  let A := toPrecontact ha
  obtain ⟨c, hac, hc⟩ := EReal.exists_between_coe_real ha.2
  have hac' : a < c := EReal.coe_lt_coe_iff.mp hac
  let C : PrecontactAperture := ⟨⟨c, ha.1.trans hac'⟩, hc⟩
  have hshift : Tendsto (fun x : ℝ => x-a) (𝓝[>] a) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto (fun x : ℝ => x-a) (𝓝 a) (𝓝 (a-a)) := tendsto_id.sub_const a
      simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr hx
  rw [diagonalEndpointEnergy, dif_pos ha,
    hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs := hshift.eventually
    (eventually_abs_kernel_slope_sub_endpointEnergy_lt (a := A) (c := C) hac' z hε)
  filter_upwards [hs, self_mem_nhdsWithin,
    (eventually_lt_nhds hac').filter_mono nhdsWithin_le_nhds] with x hs hax hxc
  have hx : x ∈ precontactSet :=
    ⟨ha.1.trans hax, (EReal.coe_lt_coe_iff.mpr hxc).trans hc⟩
  let B := toPrecontact hx
  have hb : B.1.1 = A.1.1+(x-a) := by dsimp only [A, B, toPrecontact]; ring
  have he := hs B hax.le hb
  have hxg : diagonalEvalGram z x = (kernel B z z).re := diagonalEvalGram_eq_kernel z B
  have hag : diagonalEvalGram z a = (kernel A z z).re := diagonalEvalGram_eq_kernel z A
  rw [slope_def_field, Real.dist_eq, hxg, hag]
  simpa only [Complex.sub_re] using he

/-- Density of smaller windows rules out a left jump of the diagonal kernel. -/
theorem continuousWithinAt_diagonalEvalGram_left (z : ℂ) {a : ℝ}
    (ha : a ∈ precontactSet) : ContinuousWithinAt (diagonalEvalGram z) (Iio a) a := by
  let A := toPrecontact ha
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  obtain ⟨a₀, h₀a, hsmall⟩ := exists_left_aperture_small_evalVectorIncrement A z hs
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds h₀a).filter_mono nhdsWithin_le_nhds] with x hxa h₀x
  have hx : x ∈ precontactSet :=
    ⟨a₀.1.2.trans h₀x, (EReal.coe_lt_coe_iff.mpr hxa).trans ha.2⟩
  let B := toPrecontact hx
  have hn := hsmall B h₀x.le hxa.le
  have hprod := mul_pos (sub_pos.mpr hn)
    (add_pos_of_pos_of_nonneg hs (norm_nonneg (evalVectorIncrement (show B.1.1 ≤ A.1.1 from hxa.le) z)))
  have hnSq : ‖evalVectorIncrement (show B.1.1 ≤ A.1.1 from hxa.le) z‖^2 < ε := by
    nlinarith only [hprod, Real.sq_sqrt hε.le]
  have hmono : diagonalEvalGram z x ≤ diagonalEvalGram z a :=
    monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => z) hx ha hxa.le
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
  change diagonalEvalGram z A.1.1-diagonalEvalGram z B.1.1 < ε
  rw [diagonalEvalGram_sub_eq hxa.le]
  exact hnSq

/-- The actual diagonal kernel is continuous throughout the precontact interval. -/
theorem continuousAt_diagonalEvalGram (z : ℂ) {a : ℝ} (ha : a ∈ precontactSet) :
    ContinuousAt (diagonalEvalGram z) a :=
  continuousAt_iff_continuous_left'_right'.mpr
    ⟨continuousWithinAt_diagonalEvalGram_left z ha,
      (hasDerivWithinAt_diagonalEvalGram_right z ha).continuousWithinAt⟩

private theorem monotone_right_derivative_integral {f d : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt f (d x) (Ioi x) x) :
    IntervalIntegrable d volume a b ∧ ∫ x in a..b, d x = f b-f a := by
  have hm' : MonotoneOn f (uIcc a b) := by simpa only [uIcc_of_le hab] using hm
  have he : deriv f =ᵐ[volume.restrict (uIoc a b)] d := by
    change ∀ᵐ x ∂volume.restrict (uIoc a b), deriv f x = d x
    rw [uIoc_of_le hab, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hm.ae_differentiableWithinAt_of_mem, volume.ae_ne b] with x hx hxb hxI
    have hi : x ∈ Ioo a b := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
    have hf := (hx ⟨hi.1.le, hi.2.le⟩).differentiableAt (Icc_mem_nhds hi.1 hi.2)
    exact (hf.derivWithin (uniqueDiffWithinAt_Ioi x)).symm.trans
      ((hd x hi).derivWithin (uniqueDiffWithinAt_Ioi x))
  have hi := hm'.intervalIntegrable_deriv.congr_ae he
  exact ⟨hi, intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc hd hi⟩

private theorem monotone_right_derivative_ac {f d : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hm : MonotoneOn f (Icc a b))
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt f (d x) (Ioi x) x) :
    AbsolutelyContinuousOnInterval f a b := by
  have hi := (monotone_right_derivative_integral hab hm hc hd).1
  have he (x : ℝ) (hx : x ∈ Icc a b) : ∫ t in a..x, d t = f x-f a := by
    exact (monotone_right_derivative_integral hx.1
      (hm.mono (Icc_subset_Icc le_rfl hx.2))
      (hc.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht => hd t ⟨ht.1, ht.2.trans_le hx.2⟩)).2
  have hprim := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show a ∈ uIcc a b from left_mem_uIcc)
  rw [absolutelyContinuousOnInterval_iff] at hprim ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hprim ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hsum : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1,
        dist (∫ t in a..(E.2 i).1, d t) (∫ t in a..(E.2 i).2, d t) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hp := hE.1 i hi
    rw [uIcc_of_le hab] at hp
    rw [he _ hp.1, he _ hp.2, dist_sub_right]
  rw [hsum]
  exact hbound E hE hlen

/-- Every precontact diagonal kernel increment is exactly the integral of
the two actual endpoint trace energies. -/
theorem integral_diagonalEndpointEnergy_eq_sub (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    IntervalIntegrable (diagonalEndpointEnergy z) volume a b ∧
      (∫ x in a..b, diagonalEndpointEnergy z x) =
        diagonalEvalGram z b-diagonalEvalGram z a := by
  apply monotone_right_derivative_integral hab
  · exact (monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => z)).mono hs
  · exact fun x hx => (continuousAt_diagonalEvalGram z (hs hx)).continuousWithinAt
  · exact fun x hx => hasDerivWithinAt_diagonalEvalGram_right z (hs ⟨hx.1.le, hx.2.le⟩)

/-- Diagonal evaluation kernels have no singular growth on compact
precontact intervals. -/
theorem absolutelyContinuousOnInterval_diagonalEvalGram (z : ℂ) {a b : ℝ}
    (hab : a ≤ b) (hs : Icc a b ⊆ precontactSet) :
    AbsolutelyContinuousOnInterval (diagonalEvalGram z) a b := by
  apply monotone_right_derivative_ac (d := diagonalEndpointEnergy z) hab
  · exact (monotoneOn_evalGram (fun _ : Unit => (1 : ℂ)) (fun _ => z)).mono hs
  · exact fun x hx => (continuousAt_diagonalEvalGram z (hs hx)).continuousWithinAt
  · exact fun x hx => hasDerivWithinAt_diagonalEvalGram_right z (hs ⟨hx.1.le, hx.2.le⟩)

#print axioms hasDerivWithinAt_diagonalEvalGram_right
#print axioms continuousAt_diagonalEvalGram
#print axioms integral_diagonalEndpointEnergy_eq_sub
#print axioms absolutelyContinuousOnInterval_diagonalEvalGram
end GaloisForLFunctions.CriticalHardyTheoryOfTheWindowCone
