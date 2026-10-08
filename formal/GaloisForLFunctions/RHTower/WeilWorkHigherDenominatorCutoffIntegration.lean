import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorMellinTail
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
/-!
# Endpoint identities for smooth Mellin cutoffs

The complementary lower integral retains its constant endpoint contribution.
The upper second-derivative integral vanishes on constant primitives. Both
identities use absolutely convergent integrals and explicit endpoint limits;
no boundary regularity of the cubic quotient is assumed.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

private lemma hasDerivAt_positive_cpow' {x : ℝ} (hx : 0 < x) (s : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ s) (s * (x : ℂ) ^ (s - 1)) x := by
  by_cases hs : s = 0
  · subst s
    simpa using hasDerivAt_const x (1 : ℂ)
  exact hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs

/-- Positive real powers are smooth locally, including the zero exponent. -/
theorem contDiffAt_positive_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ s) x := by
  have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr (ne_of_gt hx))
  have he : ContDiffAt ℝ ∞ (fun y : ℝ => Complex.exp ((Real.log y : ℂ) * s)) x :=
    (hl.mul contDiffAt_const).cexp
  apply he.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hy)),
    ← Complex.ofReal_log (le_of_lt hy)]

/-- The origin buffer makes the cutoff power smooth on the entire real line. -/
theorem IsMellinTailCutoff.contDiff_mul_cpow {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (s : ℂ) :
    ContDiff ℝ ∞ (fun x : ℝ => ψ x * (x : ℂ) ^ s) := by
  obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < a
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [h0 y hy]
  · exact hψ.smooth.contDiffAt.mul
      (contDiffAt_positive_cpow (ha.trans_le (le_of_not_gt hx)) s)

/-- The complementary lower cutoff has a convergent Mellin transform for `re s > 0`. -/
theorem IsMellinTailCutoff.mellin_complement {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x => 1 - ψ x) s := by
  obtain ⟨C, hC⟩ := hψ.bounded
  obtain ⟨b, hb⟩ := hψ.one_near_infinity
  have ht : (fun x => 1 - ψ x) =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop b] with x hx
    simp [hb x hx]
  have h0 : (fun x => 1 - ψ x) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound (1 + C) (Eventually.of_forall fun x => ?_)
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (hC x) 1)
  have hc : LocallyIntegrableOn (fun x => 1 - ψ x) (Ioi 0) :=
    (continuous_const.sub hψ.smooth.continuous).continuousOn.locallyIntegrableOn measurableSet_Ioi
  exact mellinConvergent_of_isBigO_rpow hc ht (by linarith) h0 hs

/-- Integration by parts keeps the constant endpoint contribution with its exact sign. -/
theorem integral_mellinCutoff_complement {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {s : ℂ} (hs : 0 < s.re) :
    (∫ x : ℝ in Ioi 0, (1 - ψ x) * (x : ℂ) ^ (s - 1)) =
      (∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) / s := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hi1 := integrable_cutoff_deriv_cpow hψ s
  have hi2 : IntegrableOn (fun x : ℝ => (1 - ψ x) * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using hψ.mellin_complement hs
  let f : ℝ → ℂ := fun x => (1 - ψ x) * (x : ℂ) ^ s
  have hc : ContinuousAt f 0 := by
    have hpair : ContinuousAt (fun x : ℝ => ((x : ℂ), s)) 0 :=
      Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const
    have hp : ContinuousAt (fun x : ℝ => (x : ℂ) ^ s) 0 :=
      ContinuousAt.comp (f := fun x : ℝ => ((x : ℂ), s))
        (g := fun p : ℂ × ℂ => p.1 ^ p.2) (x := (0 : ℝ))
        (by simpa using Complex.continuousAt_cpow_zero_of_re_pos hs) hpair
    exact (continuousAt_const.sub hψ.smooth.continuous.continuousAt).mul hp
  have hf0 : f 0 = 0 := by simp [f, Complex.zero_cpow hs0]
  have ht : Tendsto f atTop (𝓝 0) := by
    obtain ⟨b, hb⟩ := hψ.one_near_infinity
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop b] with x hx
    simp [f, hb x hx]
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
      (-(iteratedDeriv 1 ψ x * (x : ℂ) ^ s) + s * ((1 - ψ x) * (x : ℂ) ^ (s - 1))) x := by
    intro x hx
    have h := ((hψ.smooth.differentiable (by simp) x).hasDerivAt.const_sub 1).fun_mul
      (hasDerivAt_positive_cpow' hx s)
    convert h using 1 <;> first | rfl | (simp only [iteratedDeriv_one]; ring)
  have hi : IntegrableOn (fun x : ℝ => -(iteratedDeriv 1 ψ x * (x : ℂ) ^ s) +
      s * ((1 - ψ x) * (x : ℂ) ^ (s - 1))) (Ioi 0) := hi1.neg.add (hi2.const_mul s)
  have H := integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt hd hi ht
  rw [hf0, sub_self] at H
  have hadd := integral_add (f := fun x : ℝ => -(iteratedDeriv 1 ψ x * (x : ℂ) ^ s))
    (g := fun x => s * ((1 - ψ x) * (x : ℂ) ^ (s - 1))) hi1.neg (hi2.const_mul s)
  rw [hadd, integral_neg, integral_const_mul] at H
  apply (eq_div_iff hs0).mpr
  linear_combination H

private theorem tendsto_positive_cpow_atTop {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun x : ℝ => x ^ s.re) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hs)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (Complex.norm_cpow_eq_rpow_re_of_pos hx s).symm

/-- A constant primitive contributes no upper second-derivative tail. -/
theorem integral_mellinCutoff_second_eq_zero {ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) {s : ℂ} (hs : s.re < 2) :
    (∫ x : ℝ in Ioi 0, iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) = 0 := by
  let w : ℝ → ℂ := fun x => ψ x * (x : ℂ) ^ (s - 1)
  have hw := hψ.contDiff_mul_cpow (s - 1)
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (iteratedDeriv 1 w) (iteratedDeriv 2 w x) x := by
    intro x _
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ] using
      (hw.differentiable_iteratedDeriv 1 (by simp) x).hasDerivAt
  have hi : IntegrableOn (iteratedDeriv 2 w) (Ioi 0) := by
    simpa only [one_mul] using (integral_primitive_cutoff_cpow hψ
      (F := fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ hs).1
  have ht : Tendsto (iteratedDeriv 1 w) atTop (𝓝 0) := by
    have hp : Tendsto (fun x : ℝ => (s - 1) * (x : ℂ) ^ (s - 2)) atTop (𝓝 0) := by
      simpa using (tendsto_positive_cpow_atTop (s := s - 2) (by simpa using hs)).const_mul (s - 1)
    obtain ⟨b, hb⟩ := hψ.one_near_infinity
    apply hp.congr'
    filter_upwards [eventually_gt_atTop b, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have he : w =ᶠ[𝓝 x] fun y : ℝ => (y : ℂ) ^ (s - 1) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [w, hb y hy]
    rw [he.iteratedDeriv_eq 1, iteratedDeriv_one,
      (hasDerivAt_positive_cpow' hx0 (s - 1)).deriv]
    rw [show s - 1 - 1 = s - 2 by ring]
  have hz : iteratedDeriv 1 w 0 = 0 := by
    obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
    have he : w =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds ha] with x hx
      simp [w, h0 x hx]
    simpa using he.iteratedDeriv_eq 1
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    (hw.continuous_iteratedDeriv 1 (by simp)).continuousAt.continuousWithinAt hd hi ht
  change (∫ x : ℝ in Ioi 0, iteratedDeriv 2 w x) = 0 - iteratedDeriv 1 w 0 at H
  rw [hz, sub_self] at H
  exact H
end RHTower.WeilHigherDenominator
