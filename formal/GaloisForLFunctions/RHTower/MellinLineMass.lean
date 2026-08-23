import GaloisForLFunctions.RHTower.SoninLPropertyTheorem
import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal
import GaloisForLFunctions.HTGeometry.CauchyKernelLineMass
import GaloisForLFunctions.HTGeometry.HardyLineIsometry
import GaloisForLFunctions.HTGeometry.HardyLineMass

/-!
# The `L²` mass of the continued Mellin transform on a vertical line

Right of the strip the continued Mellin transform of a vector of `L_a` is the sum of the Hardy
transform of its tail and the explicit head `d·a^{1-s}/(1-s)`.  For `a ≥ 1` both have `L²` mass on
the line `Re s = σ` bounded *uniformly in `σ ≥ 2`*: the Hardy mass is at most the Paley--Wiener
constant `2π‖φ‖²`, and the head mass is `|d|²a^{2-2σ}·π/(σ-1) ≤ |d|²π`.  This is the estimate that
makes the right-hand vertical edge of Burnol's rectangle vanish as its half-width grows.

## Main results

* `extendedMellinContinuation_eq_right`
* `exists_integral_norm_sq_extendedMellin_line_le`
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem extendedMellinContinuation_eq_right (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    extendedMellinContinuation a c d f s = extendedMellinRight a c d f s := by
  have hne : s * (1 - s) ≠ 0 :=
    mul_ne_zero h0 (sub_ne_zero.2 fun h => h1 h.symm)
  rw [extendedMellinContinuation, extendedMellinNumerator_eq_right a c d f hs,
    extendedMellinNumeratorRight_eq a c d f h1, mul_comm (s * (1 - s)),
    mul_div_assoc, div_self hne, mul_one]

/-- The head term of the continued transform, on a vertical line. -/
theorem norm_sq_head_line (a : ℝ) (d : ℂ) (σ t : ℝ) :
    ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))
        / (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2
      = (‖d‖ ^ 2 * ‖((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2)
        * ‖(1 - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2 := by
  rw [div_eq_mul_inv, norm_mul, norm_mul, mul_pow, mul_pow]

/-- Off `{0, 1}` the continued Mellin transform is holomorphic. -/
theorem differentiableAt_extendedMellinContinuation {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (extendedMellinContinuation a c d f) s := by
  obtain ⟨hdiff, -⟩ := differentiable_extendedMellinNumerator ha hev hc hd
  refine (hdiff s).div ?_ (mul_ne_zero h0 (sub_ne_zero.2 fun h => h1 h.symm))
  exact differentiableAt_id.mul ((differentiableAt_const _).sub differentiableAt_id)

/-- **The uniform `L²` line mass.** -/
theorem exists_integral_norm_sq_extendedMellin_line_le {a : ℝ} (ha : 1 ≤ a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, 2 ≤ σ →
      Integrable (fun t : ℝ =>
        ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume ∧
      (∫ t : ℝ, ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ M := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  set φ : ℝ → ℂ := logChart a ((f : ℝ → ℂ)) with hφdef
  have hfL2 : MemLp ((f : ℝ → ℂ)) 2 (volume.restrict (Ioi a)) := (Lp.memLp f).restrict (Ioi a)
  have hφL2 : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_logChart ha0 hfL2
  have hφsq : Integrable (fun x : ℝ => ‖φ x‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hφL2.1).1 hφL2
  set MH : ℝ := 2 * Real.pi * ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2 with hMHdef
  have hMH0 : 0 ≤ MH := by
    rw [hMHdef]
    have : (0 : ℝ) ≤ ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2 := integral_nonneg fun x => by positivity
    positivity
  refine ⟨2 * MH + 2 * (‖d‖ ^ 2 * Real.pi), by positivity, ?_⟩
  intro σ hσ
  have hσ0 : (0 : ℝ) < σ := by linarith
  set A : ℝ → ℂ := fun t : ℝ =>
    ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - ((σ : ℂ) + (t : ℂ) * I))
      * laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2) with hAdef
  set B : ℝ → ℂ := fun t : ℝ =>
    d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))
      / (1 - ((σ : ℂ) + (t : ℂ) * I)) with hBdef
  -- the decomposition on the line
  have hsplit : ∀ t : ℝ,
      extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I) = A t + B t := by
    intro t
    have hsre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have h0 : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    have h1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    rw [extendedMellinContinuation_eq_right a c d f (by rw [hsre]; linarith) h0 h1,
      extendedMellinRight, extendedTailMellin_eq ha0 hc (by rw [hsre]; linarith),
      mellinTail_eq_laplaceRay ha0 _ _]
  -- the Hardy line datum
  have hHardy : IsHalfPlaneHardy (laplaceRay φ) (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2) :=
    isHalfPlaneHardy_laplaceRay hφL2
  have hlineEq : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) - 1 / 2
      = ((σ - 1 / 2 : ℝ) : ℂ) + (t : ℝ) * Complex.I := by
    intro t
    push_cast
    ring
  have hmemA : MemLp (fun t : ℝ => laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)) 2 volume := by
    have h := memLp_two_hardyLine hHardy (σ := σ - 1 / 2) (by linarith)
    refine h.ae_eq (Filter.Eventually.of_forall fun t => ?_)
    show laplaceRay φ (((σ - 1 / 2 : ℝ) : ℂ) + (t : ℝ) * Complex.I)
        = laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)
    rw [hlineEq t]
  have hAsq : Integrable (fun t : ℝ => ‖A t‖ ^ 2) volume := by
    have hcoef : Integrable (fun t : ℝ =>
        a ^ (1 - 2 * σ) * ‖laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)‖ ^ 2) volume :=
      ((memLp_two_iff_integrable_sq_norm hmemA.1).1 hmemA).const_mul _
    refine hcoef.congr ?_
    filter_upwards with t
    show a ^ (1 - 2 * σ) * ‖laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)‖ ^ 2 = ‖A t‖ ^ 2
    rw [hAdef]
    show _ = ‖((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - ((σ : ℂ) + (t : ℂ) * I))
      * laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)‖ ^ 2
    rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
    have hre : ((1 : ℂ) / 2 - ((σ : ℂ) + (t : ℂ) * I)).re = 1 / 2 - σ := by simp
    rw [hre]
    have hsq : (a ^ ((1 : ℝ) / 2 - σ)) ^ 2 = a ^ ((1 : ℝ) - 2 * σ) := by
      rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / 2 - σ)) 2, ← Real.rpow_mul ha0.le]
      congr 1
      push_cast
      ring
    rw [hsq]
  have hBsq : Integrable (fun t : ℝ => ‖B t‖ ^ 2) volume := by
    have hZ : (1 : ℂ).re < σ := by simp; linarith
    have hK := integrable_norm_sq_cauchyKernel_line hZ
    have hcoef := hK.const_mul (‖d‖ ^ 2 * (a ^ (2 - 2 * σ)))
    refine hcoef.congr ?_
    filter_upwards with t
    show ‖d‖ ^ 2 * a ^ (2 - 2 * σ) * ‖((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2 = ‖B t‖ ^ 2
    rw [hBdef]
    show _ = ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))
        / (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2
    rw [norm_sq_head_line, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
    have hre : ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ := by simp
    rw [hre]
    have hsq : (a ^ ((1 : ℝ) - σ)) ^ 2 = a ^ ((2 : ℝ) - 2 * σ) := by
      rw [← Real.rpow_natCast (a ^ ((1 : ℝ) - σ)) 2, ← Real.rpow_mul ha0.le]
      congr 1
      push_cast
      ring
    rw [hsq]
  -- the two masses
  have hAmass : (∫ t : ℝ, ‖A t‖ ^ 2) ≤ MH := by
    have hcongr : (∫ t : ℝ, ‖A t‖ ^ 2)
        = a ^ (1 - 2 * σ)
          * ∫ t : ℝ, ‖laplaceRay φ (hardyVerticalLine (σ - 1 / 2) t)‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ‖A t‖ ^ 2
          = a ^ (1 - 2 * σ) * ‖laplaceRay φ (hardyVerticalLine (σ - 1 / 2) t)‖ ^ 2
      rw [hAdef]
      show ‖((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - ((σ : ℂ) + (t : ℂ) * I))
        * laplaceRay φ (((σ : ℂ) + (t : ℂ) * I) - 1 / 2)‖ ^ 2 = _
      rw [norm_mul, mul_pow, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      have hre : ((1 : ℂ) / 2 - ((σ : ℂ) + (t : ℂ) * I)).re = 1 / 2 - σ := by simp
      rw [hre]
      have hsq : (a ^ ((1 : ℝ) / 2 - σ)) ^ 2 = a ^ ((1 : ℝ) - 2 * σ) := by
        rw [← Real.rpow_natCast (a ^ ((1 : ℝ) / 2 - σ)) 2, ← Real.rpow_mul ha0.le]
        congr 1
        push_cast
        ring
      rw [hsq, hardyVerticalLine, hlineEq t]
    rw [hcongr, integral_norm_sq_laplaceRay_vertical hφL2 (by linarith : (0:ℝ) < σ - 1 / 2)]
    have hdamp : (∫ x in Ioi (0 : ℝ), Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2)
        ≤ ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
        hφsq ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxpos : (0 : ℝ) < x := hx
      have hexp : Real.exp (-(2 * (σ - 1 / 2) * x)) ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        have hspos : (0 : ℝ) < σ - 1 / 2 := by linarith
        nlinarith [hxpos, hspos]
      nlinarith [sq_nonneg ‖φ x‖, hexp]
    have hnn : (0 : ℝ) ≤ 2 * Real.pi * ∫ x in Ioi (0 : ℝ),
        Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2 := by
      have : (0 : ℝ) ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2 :=
        integral_nonneg fun x => by positivity
      positivity
    have hpow : a ^ (1 - 2 * σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
    have hmass2 : (2 * Real.pi * ∫ x in Ioi (0 : ℝ),
        Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2) ≤ MH := by
      rw [hMHdef]
      refine mul_le_mul_of_nonneg_left hdamp (by positivity)
    calc a ^ (1 - 2 * σ) * (2 * Real.pi * ∫ x in Ioi (0 : ℝ),
          Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2)
        ≤ 1 * (2 * Real.pi * ∫ x in Ioi (0 : ℝ),
          Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hpow hnn
      _ = 2 * Real.pi * ∫ x in Ioi (0 : ℝ),
          Real.exp (-(2 * (σ - 1 / 2) * x)) * ‖φ x‖ ^ 2 := one_mul _
      _ ≤ MH := hmass2
  have hBmass : (∫ t : ℝ, ‖B t‖ ^ 2) ≤ ‖d‖ ^ 2 * Real.pi := by
    have hZ : (1 : ℂ).re < σ := by simp; linarith
    have hcongr : (∫ t : ℝ, ‖B t‖ ^ 2)
        = (‖d‖ ^ 2 * a ^ (2 - 2 * σ))
          * ∫ t : ℝ, ‖((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show ‖B t‖ ^ 2
          = ‖d‖ ^ 2 * a ^ (2 - 2 * σ) * ‖((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2
      rw [hBdef]
      show ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I))
          / (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 = _
      rw [norm_sq_head_line, Complex.norm_cpow_eq_rpow_re_of_pos ha0]
      have hre : ((1 : ℂ) - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ := by simp
      rw [hre]
      have hsq : (a ^ ((1 : ℝ) - σ)) ^ 2 = a ^ ((2 : ℝ) - 2 * σ) := by
        rw [← Real.rpow_natCast (a ^ ((1 : ℝ) - σ)) 2, ← Real.rpow_mul ha0.le]
        congr 1
        push_cast
        ring
      rw [hsq]
    rw [hcongr, integral_norm_sq_cauchyKernel_line hZ]
    have hre1 : (1 : ℂ).re = 1 := by simp
    rw [hre1]
    have hpow : a ^ (2 - 2 * σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ha (by linarith)
    have hpi : Real.pi / (σ - 1) ≤ Real.pi := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [Real.pi_pos]
    have hpow0 : (0 : ℝ) ≤ a ^ (2 - 2 * σ) := Real.rpow_nonneg ha0.le _
    have hd0 : (0 : ℝ) ≤ ‖d‖ ^ 2 := by positivity
    have hpidiv : (0 : ℝ) ≤ Real.pi / (σ - 1) := by positivity
    calc ‖d‖ ^ 2 * a ^ (2 - 2 * σ) * (Real.pi / (σ - 1))
        ≤ ‖d‖ ^ 2 * 1 * (Real.pi / (σ - 1)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hd0) hpidiv
      _ = ‖d‖ ^ 2 * (Real.pi / (σ - 1)) := by ring
      _ ≤ ‖d‖ ^ 2 * Real.pi := mul_le_mul_of_nonneg_left hpi hd0
  -- combine
  have hsum : ∀ t : ℝ, ‖A t + B t‖ ^ 2 ≤ 2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2 := by
    intro t
    have h := norm_add_le (A t) (B t)
    nlinarith [norm_nonneg (A t), norm_nonneg (B t), norm_nonneg (A t + B t),
      sq_nonneg (‖A t‖ - ‖B t‖), h]
  have hint : Integrable (fun t : ℝ =>
      ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume := by
    have hmaj : Integrable (fun t : ℝ => 2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) volume :=
      (hAsq.const_mul 2).add (hBsq.const_mul 2)
    have hmeas : AEStronglyMeasurable (fun t : ℝ =>
        ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume := by
      have hcont : Continuous fun t : ℝ =>
          extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I) := by
        have hpath : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
        refine continuous_iff_continuousAt.2 fun t => ?_
        have hsre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
        have hs0 : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
          intro h
          rw [h] at hsre
          simp at hsre
          linarith
        have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
          intro h
          rw [h] at hsre
          simp at hsre
          linarith
        have hg := (differentiableAt_extendedMellinContinuation ha0 hev hc hd hs0
          hs1).continuousAt
        exact ContinuousAt.comp (g := extendedMellinContinuation a c d f)
          (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := t) hg hpath.continuousAt
      exact (hcont.norm.pow 2).aestronglyMeasurable
    refine Integrable.mono' hmaj hmeas ?_
    filter_upwards with t
    rw [hsplit t, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsum t
  refine ⟨hint, ?_⟩
  have hle : (∫ t : ℝ, ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2)
      ≤ ∫ t : ℝ, (2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2) := by
    refine integral_mono hint ((hAsq.const_mul 2).add (hBsq.const_mul 2)) fun t => ?_
    show ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ 2 * ‖A t‖ ^ 2 + 2 * ‖B t‖ ^ 2
    rw [hsplit t]
    exact hsum t
  rw [integral_add (hAsq.const_mul 2) (hBsq.const_mul 2), integral_const_mul,
    integral_const_mul] at hle
  linarith [hle, hAmass, hBmass]

/-- **The right-hand vertical edge vanishes.**  Cauchy--Schwarz against the Cauchy kernel, whose
`L²` mass on the line `Re s = σ` is `π/(σ − Re Z)`. -/
theorem tendsto_vertical_edge_zero {a : ℝ} (ha : 1 ≤ a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (Z : ℂ) :
    Tendsto (fun σ : ℝ => ‖∫ t : ℝ,
        extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)
          * (riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹
          * (Z - ((σ : ℂ) + (t : ℂ) * I))⁻¹‖) atTop (𝓝 0) := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  obtain ⟨M, hM0, hM⟩ := exists_integral_norm_sq_extendedMellin_line_le ha hev hc hd
  set L : ℝ := Real.sqrt (16 * M) with hLdef
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hlim : Tendsto (fun σ : ℝ => L * Real.sqrt (Real.pi / (σ - Z.re))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun σ : ℝ => Real.pi / (σ - Z.re)) atTop (𝓝 0) := by
      have hsub : Tendsto (fun σ : ℝ => σ - Z.re) atTop atTop :=
        tendsto_atTop_add_const_right _ (-Z.re) tendsto_id
      exact Filter.Tendsto.div_atTop tendsto_const_nhds hsub
    have hsqrt : Tendsto (fun σ : ℝ => Real.sqrt (Real.pi / (σ - Z.re))) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hdiv
      simpa [Function.comp_def] using h
    have := hsqrt.const_mul L
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun σ => norm_nonneg _) ?_
  filter_upwards [Filter.eventually_ge_atTop (max 2 (Z.re + 1))] with σ hσ
  have hσ2 : (2 : ℝ) ≤ σ := le_trans (le_max_left _ _) hσ
  have hσZ : Z.re < σ := lt_of_lt_of_le (by linarith) (le_trans (le_max_right _ _) hσ)
  obtain ⟨hGint, hGmass⟩ := hM σ hσ2
  set F : ℝ → ℂ := fun t : ℝ =>
    extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)
      * (riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹ with hFdef
  have hzeta : ∀ t : ℝ, ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ 4 := by
    intro t
    refine norm_zeta_inv_le_of_two_le_re ?_
    simpa using hσ2
  have hFnorm : ∀ t : ℝ,
      ‖F t‖ ^ 2 ≤ 16 * ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    intro t
    rw [hFdef]
    show ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)
        * (riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2 ≤ _
    rw [norm_mul, mul_pow]
    have h4 := hzeta t
    have h0 : (0 : ℝ) ≤ ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ := norm_nonneg _
    have hG0 : (0 : ℝ) ≤ ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      positivity
    have hsq : ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ^ 2 ≤ 16 := by
      nlinarith [h4, h0]
    nlinarith [hsq, hG0]
  have hcontG : Continuous fun t : ℝ =>
      extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I) := by
    have hpath : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
    refine continuous_iff_continuousAt.2 fun t => ?_
    have hsre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    have hs0 : ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
      intro h
      rw [h] at hsre
      simp at hsre
      linarith
    have hg := (differentiableAt_extendedMellinContinuation ha0 hev hc hd hs0 hs1).continuousAt
    exact ContinuousAt.comp (g := extendedMellinContinuation a c d f)
      (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := t) hg hpath.continuousAt
  have hcontZ : Continuous fun t : ℝ => (riemannZeta ((σ : ℂ) + (t : ℂ) * I))⁻¹ := by
    have hpath : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * I) := by fun_prop
    have hne : ∀ t : ℝ, riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro t
      have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
      have h := norm_riemannZeta_ge_of_two_le_re (s := (σ : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith)
      intro hzero
      rw [hzero] at h
      simp at h
      linarith
    have hz : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) := by
      refine continuous_iff_continuousAt.2 fun t => ?_
      have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
      have hs1 : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
        intro h
        rw [h] at hre
        simp at hre
        linarith
      have hg := (differentiableAt_riemannZeta hs1).continuousAt
      exact ContinuousAt.comp (g := riemannZeta)
        (f := fun u : ℝ => ((σ : ℂ) + (u : ℂ) * I)) (x := t) hg hpath.continuousAt
    exact hz.inv₀ hne
  have hFm : AEStronglyMeasurable F volume := (hcontG.mul hcontZ).aestronglyMeasurable
  have hF2 : Integrable (fun t : ℝ => ‖F t‖ ^ 2) volume := by
    refine Integrable.mono' (hGint.const_mul 16) ((hFm.norm.pow 2)) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hFnorm t
  have hmass : (∫ t : ℝ, ‖F t‖ ^ 2) ≤ 16 * M := by
    have hle : (∫ t : ℝ, ‖F t‖ ^ 2)
        ≤ ∫ t : ℝ, 16 * ‖extendedMellinContinuation a c d f ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
      integral_mono hF2 (hGint.const_mul 16) hFnorm
    rw [integral_const_mul] at hle
    linarith [hle, hGmass]
  have hkey := norm_integral_mul_cauchyKernel_le hσZ hFm hF2 hmass
  exact hkey

end

end RHTower

