import GaloisForLFunctions.RHTower.WindingAmplitude
import GaloisForLFunctions.RHTower.DigammaVerticalLogAsymptotic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Exact imaginary vertical asymptotic for digamma
-/

namespace RHTower

open Complex Filter Topology intervalIntegral

noncomputable section

def verticalCauchyKernel (σ t x : ℝ) : ℝ :=
  t / ((σ + x) ^ 2 + t ^ 2)

lemma verticalCauchyKernel_nonneg {σ t x : ℝ} (ht : 0 < t) :
    0 ≤ verticalCauchyKernel σ t x := by
  unfold verticalCauchyKernel
  positivity

lemma verticalCauchyKernel_antitoneOn {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    AntitoneOn (verticalCauchyKernel σ t) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold verticalCauchyKernel
  have hx0 : 0 ≤ σ + x := by linarith
  have hy0 : 0 ≤ σ + y := by linarith
  have hsquare : (σ + x) ^ 2 ≤ (σ + y) ^ 2 := by nlinarith
  gcongr

theorem integral_verticalCauchyKernel {σ t a b : ℝ} (ht : 0 < t) :
    ∫ x in a..b, verticalCauchyKernel σ t x =
      Real.arctan ((σ + b) / t) - Real.arctan ((σ + a) / t) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hlin : HasDerivAt (fun y : ℝ => (σ + y) / t) (1 / t) x := by
      convert ((hasDerivAt_const x σ).add (hasDerivAt_id x)).div_const t using 1 <;> ring
    convert hlin.arctan using 1
    unfold verticalCauchyKernel
    field_simp [ht.ne']
    ring
  · apply Continuous.intervalIntegrable
    exact continuous_const.div
      (((continuous_const.add continuous_id).pow 2).add (continuous_const.pow 2))
      (fun x => by positivity)

def digammaImaginaryPartialSum (σ t : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, verticalCauchyKernel σ t n

theorem digammaImaginaryPartialSum_tendsto
    {σ t : ℝ} (ht : 0 < t) :
    Tendsto (digammaImaginaryPartialSum σ t) atTop
      (nhds (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im) := by
  let z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hz : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have him := congrArg Complex.im h
    dsimp [z] at him
    simp at him
    linarith
  have hshift : ∀ N : ℕ,
      (Complex.digamma z).im - (Complex.digamma (z + (N : ℂ))).im =
        digammaImaginaryPartialSum σ t N := by
    intro N
    rw [digamma_apply_add_nat z hz N, Complex.add_im, Complex.im_sum]
    rw [show ∑ n ∈ Finset.range N, ((z + (n : ℂ))⁻¹).im =
      ∑ n ∈ Finset.range N, -(verticalCauchyKernel σ t n) from
        Finset.sum_congr rfl fun n _ => by
          rw [show z = (σ : ℂ) + (t : ℂ) * Complex.I by rfl]
          rw [im_inv_shift]
          rfl]
    rw [Finset.sum_neg_distrib]
    simp [digammaImaginaryPartialSum]
  have hanchor := im_digamma_vertical_anchor_tendsto σ t
  have hanchor' : Tendsto (fun N : ℕ => (Complex.digamma (z + (N : ℂ))).im)
      atTop (nhds 0) := by
    simpa [z, add_assoc] using hanchor
  have hconst : Tendsto (fun _ : ℕ => (Complex.digamma z).im) atTop
      (nhds (Complex.digamma z).im) := tendsto_const_nhds
  have hlim := hconst.sub hanchor'
  simpa only [sub_zero] using hlim.congr hshift

theorem im_digamma_vertical_sandwich {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    Real.pi / 2 - Real.arctan (σ / t) ≤
        (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ∧
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ≤
        1 / t + (Real.pi / 2 - Real.arctan (σ / t)) := by
  let f : ℝ → ℝ := verticalCauchyKernel σ t
  have hant : AntitoneOn f (Set.Ici 0) := verticalCauchyKernel_antitoneOn hσ ht
  have hpartial := digammaImaginaryPartialSum_tendsto (σ := σ) ht
  have hInt : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..N, f x) atTop
      (nhds (Real.pi / 2 - Real.arctan (σ / t))) := by
    rw [show (fun N : ℕ => ∫ x in (0 : ℝ)..N, f x) =
      fun N : ℕ => Real.arctan ((σ + N) / t) - Real.arctan (σ / t) by
        funext N
        simpa [f] using
          (integral_verticalCauchyKernel (σ := σ) (t := t) (a := 0) (b := (N : ℝ)) ht)]
    have hadd : Tendsto (fun N : ℕ => σ + (N : ℝ)) atTop atTop := by
      exact tendsto_atTop_add_const_left atTop σ tendsto_natCast_atTop_atTop
    have harg : Tendsto (fun N : ℕ => (σ + (N : ℝ)) / t) atTop atTop :=
      hadd.atTop_div_const ht
    have hatan : Tendsto (fun N : ℕ => Real.arctan ((σ + (N : ℝ)) / t))
        atTop (nhds (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp harg
    simpa using hatan.sub_const (Real.arctan (σ / t))
  constructor
  · have hle : ∀ N : ℕ, (∫ x in (0 : ℝ)..N, f x) ≤
        digammaImaginaryPartialSum σ t N := by
      intro N
      simpa [f, digammaImaginaryPartialSum, Nat.cast_zero, zero_add] using
        (hant.mono (Set.Icc_subset_Ici_self)).integral_le_sum (x₀ := (0 : ℝ)) (a := N)
    have hdiff := hpartial.sub hInt
    have hnonneg : 0 ≤
        (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im -
          (Real.pi / 2 - Real.arctan (σ / t)) :=
      ge_of_tendsto hdiff (Filter.Eventually.of_forall fun N => sub_nonneg.mpr (hle N))
    linarith
  · have hle : ∀ N : ℕ, digammaImaginaryPartialSum σ t (N + 1) ≤
        f 0 + ∫ x in (0 : ℝ)..N, f x := by
      intro N
      have hshift : (∑ n ∈ Finset.range (N + 1), f n) =
          f 0 + ∑ n ∈ Finset.range N, f (n + 1) := by
        induction N with
        | zero => simp
        | succ N ih =>
            calc
              (∑ n ∈ Finset.range (N + 1 + 1), f n) =
                  (∑ n ∈ Finset.range (N + 1), f n) + f (N + 1) := by
                    simpa using Finset.sum_range_succ (fun n : ℕ => f (n : ℝ)) (N + 1)
              _ = (f 0 + ∑ n ∈ Finset.range N, f (n + 1)) + f (N + 1) := by rw [ih]
              _ = f 0 + ∑ n ∈ Finset.range (N + 1), f (n + 1) := by
                    rw [Finset.sum_range_succ]
                    have hend : f ((N + 1 : ℕ) : ℝ) = f ((N : ℝ) + 1) := by
                      norm_num
                    ring
      have htail := (hant.mono (Set.Icc_subset_Ici_self)).sum_le_integral
        (x₀ := (0 : ℝ)) (a := N)
      rw [digammaImaginaryPartialSum, hshift]
      simpa [Nat.cast_zero, zero_add] using add_le_add_left htail (f 0)
    have hpartialSucc : Tendsto (fun N : ℕ => digammaImaginaryPartialSum σ t (N + 1))
        atTop (nhds (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im) := by
      simpa [add_comm] using hpartial.comp (tendsto_add_atTop_nat 1)
    have hright : Tendsto (fun N : ℕ => f 0 + ∫ x in (0 : ℝ)..N, f x)
        atTop (nhds (f 0 + (Real.pi / 2 - Real.arctan (σ / t)))) :=
      tendsto_const_nhds.add hInt
    have hdiff := hright.sub hpartialSucc
    have hlimnonneg : 0 ≤ f 0 + (Real.pi / 2 - Real.arctan (σ / t)) -
        (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im :=
      ge_of_tendsto hdiff (Filter.Eventually.of_forall fun N => sub_nonneg.mpr (hle N))
    have hf0 : f 0 ≤ 1 / t := by
      dsimp [f, verticalCauchyKernel]
      rw [div_le_div_iff₀ (by positivity) ht]
      nlinarith
    linarith

/-- The missing imaginary half of the vertical digamma asymptotic. -/
theorem im_digamma_vertical_tendsto_pi_div_two (σ : ℝ) (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im)
      atTop (nhds (Real.pi / 2)) := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hratio : Tendsto (fun t : ℝ => σ / t) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul σ
  have hatan : Tendsto (fun t : ℝ => Real.arctan (σ / t)) atTop (nhds 0) := by
    simpa using Real.continuous_arctan.continuousAt.tendsto.comp hratio
  have hlower : Tendsto (fun t : ℝ => Real.pi / 2 - Real.arctan (σ / t))
      atTop (nhds (Real.pi / 2)) := by simpa using tendsto_const_nhds.sub hatan
  have hone : Tendsto (fun t : ℝ => 1 / t) atTop (nhds 0) := by
    simpa [one_div] using hinv
  have hupper : Tendsto (fun t : ℝ => 1 / t +
      (Real.pi / 2 - Real.arctan (σ / t))) atTop (nhds (Real.pi / 2)) := by
    simpa using hone.add hlower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (im_digamma_vertical_sandwich hσ ht).1
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (im_digamma_vertical_sandwich hσ ht).2

/-- Full complex vertical digamma asymptotic on every nonnegative vertical line. -/
theorem digamma_vertical_sub_log_I_tendsto_zero (σ : ℝ) (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ((Real.log t : ℂ) + (Real.pi / 2 : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hre := re_digamma_vertical_sub_log_tendsto_zero σ hσ
  have hreC : Tendsto (fun t : ℝ =>
      Complex.ofReal
        ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - Real.log t))
      atTop (nhds 0) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hre
  have him := (im_digamma_vertical_tendsto_pi_div_two σ hσ).sub_const (Real.pi / 2)
  have himC : Tendsto (fun t : ℝ =>
      Complex.ofReal
        ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im - Real.pi / 2) *
        Complex.I) atTop (nhds 0) := by
    have hcast : Tendsto (fun t : ℝ =>
        Complex.ofReal
          ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im - Real.pi / 2))
        atTop (nhds 0) := by
      simpa only [sub_self, Complex.ofReal_zero] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp him
    simpa using hcast.mul_const Complex.I
  have hsum := hreC.add himC
  simpa only [add_zero] using hsum.congr' (Filter.Eventually.of_forall fun t => by
    apply Complex.ext <;> simp <;> ring)

end

end RHTower
