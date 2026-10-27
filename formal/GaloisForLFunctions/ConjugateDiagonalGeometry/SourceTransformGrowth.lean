import GaloisForLFunctions.ConjugateDiagonalGeometry.UniversalSourceWeight
import GaloisForLFunctions.ConjugateDiagonalGeometry.XiSourceCurrent
import Mathlib.Analysis.Complex.Liouville

/-!
# Growth of translated arithmetic source transforms

One Gaussian envelope controls each compact source transform on the entire
spectral plane. A unit-circle Cauchy estimate bounds its real translates and
ordinate modulations, together with their first holomorphic derivatives, on
an expanding disc. No zero coordinates or zero-free-disc conditions enter.
-/

open Complex Metric Set
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A global Gaussian envelope for every compact source transform. -/
theorem norm_tr_le_sourceGaussian (f : CompactTest) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := normSq_tr_le_universalSourceWeight f
  refine ⟨1 + C, by linarith only [hC], fun z => ?_⟩
  have hweight : universalSourceWeight z ≤ Real.exp (‖z‖ ^ 2) := by
    have hden : 1 ≤ (1 + z.im ^ 2) ^ 2 := by
      nlinarith only [sq_nonneg z.im, sq_nonneg (z.im ^ 2)]
    have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      nlinarith only [sq_nonneg z.im]
    calc
      universalSourceWeight z ≤ Real.exp (z.re ^ 2) := by
        unfold universalSourceWeight
        apply (div_le_iff₀ (by positivity)).2
        have h := mul_le_mul_of_nonneg_left hden (Real.exp_pos (z.re ^ 2)).le
        simpa only [mul_one] using h
      _ ≤ _ := Real.exp_le_exp.mpr hre
  have hexp : 1 ≤ Real.exp (‖z‖ ^ 2) := Real.one_le_exp (sq_nonneg _)
  have hnorm : ‖tr f.1 z‖ ≤ 1 + Complex.normSq (tr f.1 z) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [sq_nonneg (‖tr f.1 z‖ - 1 / 2)]
  have h := (hbound z).trans (mul_le_mul_of_nonneg_left hweight hC)
  nlinarith only [hnorm, h, hexp]

/-- The entire source transform after a real translation and an ordinate shift. -/
def shiftedSourceTransform (f : CompactTest) (u τ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((z - 1 / 2) * (u : ℂ)) * tr f.1 (z - (τ : ℂ) * Complex.I)

theorem differentiable_shiftedSourceTransform (f : CompactTest) (u τ : ℝ) :
    Differentiable ℂ (shiftedSourceTransform f u τ) := by
  have ht : Differentiable ℂ (tr f.1) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact f.2.1.continuous f.2.2).comp
      (by unfold gammaOf; fun_prop)
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp ((z - 1 / 2) * (u : ℂ)))).mul
    (ht.comp (by fun_prop))

/-- Translation and ordinate modulation have explicit growth costs in the spectral plane. -/
theorem norm_shiftedSourceTransform_le (f : CompactTest) {A : ℝ}
    (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2)) (u τ : ℝ) (z : ℂ) :
    ‖shiftedSourceTransform f u τ z‖ ≤
      A * Real.exp (‖z - (τ : ℂ) * Complex.I‖ ^ 2 + |u| * (‖z‖ + 1 / 2)) := by
  have hr : |z.re - 1 / 2| ≤ ‖z‖ + 1 / 2 := by
    have ht := abs_sub z.re (1 / 2)
    have hn := Complex.abs_re_le_norm z
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ht
    linarith only [ht, hn]
  have hx : u * (z.re - 1 / 2) ≤ |u| * (‖z‖ + 1 / 2) := by
    calc
      u * (z.re - 1 / 2) ≤ |u * (z.re - 1 / 2)| := le_abs_self _
      _ = |u| * |z.re - 1 / 2| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hr (abs_nonneg u)
  rw [shiftedSourceTransform, norm_mul, Complex.norm_exp]
  have hre : (((z - 1 / 2) * (u : ℂ)) : ℂ).re = u * (z.re - 1 / 2) := by
    simp
    ring
  rw [hre]
  calc
    Real.exp (u * (z.re - 1 / 2)) * ‖tr f.1 (z - (τ : ℂ) * Complex.I)‖ ≤
        Real.exp (|u| * (‖z‖ + 1 / 2)) *
          (A * Real.exp (‖z - (τ : ℂ) * Complex.I‖ ^ 2)) :=
      mul_le_mul (Real.exp_le_exp.mpr hx) (hA (z - (τ : ℂ) * Complex.I)) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add]; ring

/-- One unit-circle Cauchy step controls both the translated source and its derivative. -/
theorem shiftedSourceTransform_disc_bound (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (u τ : ℝ) {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖shiftedSourceTransform f u τ z‖ ≤
        A * Real.exp ((R + 1 + |τ|) ^ 2 + |u| * (R + 3 / 2)) ∧
      ‖deriv (shiftedSourceTransform f u τ) z‖ ≤
        A * Real.exp ((R + 1 + |τ|) ^ 2 + |u| * (R + 3 / 2)) := by
  have hb (w : ℂ) (hw : ‖w‖ ≤ R + 1) :
      ‖shiftedSourceTransform f u τ w‖ ≤
        A * Real.exp ((R + 1 + |τ|) ^ 2 + |u| * (R + 3 / 2)) := by
    refine (norm_shiftedSourceTransform_le f hA u τ w).trans ?_
    apply mul_le_mul_of_nonneg_left _ hA0
    apply Real.exp_le_exp.mpr
    have hshift : ‖w - (τ : ℂ) * Complex.I‖ ≤ R + 1 + |τ| := by
      have ht := norm_sub_le w ((τ : ℂ) * Complex.I)
      have he : ‖(τ : ℂ) * Complex.I‖ = |τ| := by simp
      rw [he] at ht
      linarith only [ht, hw]
    have hsq : ‖w - (τ : ℂ) * Complex.I‖ ^ 2 ≤ (R + 1 + |τ|) ^ 2 := by gcongr
    have hlin := mul_le_mul_of_nonneg_left hw (abs_nonneg u)
    nlinarith only [hsq, hlin]
  refine ⟨hb z (hz.trans (by linarith only [hR])), ?_⟩
  have hc : ∀ w ∈ sphere z 1,
      ‖shiftedSourceTransform f u τ w‖ ≤
        A * Real.exp ((R + 1 + |τ|) ^ 2 + |u| * (R + 3 / 2)) := by
    intro w hw
    apply hb
    have hdist : ‖w - z‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have ht : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (w - z) z
    linarith only [ht, hdist, hz]
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0 : ℝ) < 1) (differentiable_shiftedSourceTransform f u τ).diffContOnCl hc
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one, div_one, one_mul] using h

end GaloisForLFunctions.ConjugateDiagonalGeometry
