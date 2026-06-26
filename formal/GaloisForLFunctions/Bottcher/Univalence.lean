/-
# Noshiro–Warschawski univalence (hDisc cover lane)

A holomorphic map with derivative of positive real part on a **convex** set is injective there. This is
the univalence engine for the disconnected-case cover carrier: the Böttcher coordinate `φ_c = z·exp(S)`
has `Re(φ_c'/φ_c) > 0` in logarithmic coordinates (where the far field becomes a convex half-plane), so
it is locally biholomorphic with a single-valued inverse `ψ` — the object the deck transformation
`g = ψ(ζ·φ_c(·))` is built from. Absent from Mathlib; proved here from the FTC along the (convex) segment:
`f b − f a = (b−a)·∫₀¹ f'(a+t(b−a)) dt`, and the integral has positive real part hence is nonzero.
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Complex Set intervalIntegral

namespace Bottcher

/-- **Noshiro–Warschawski.** A function `f` holomorphic on a convex set `U` (`HasDerivAt`, continuous
derivative) whose derivative has positive real part throughout is injective on `U`. Proof: for `a, b ∈ U`,
`f b − f a = (b−a)·∫₀¹ f'(a+t(b−a)) dt`; the segment lies in `U` (convexity), the integrand has positive
real part, so the integral has positive real part, hence is nonzero — so `f b ≠ f a` when `a ≠ b`. -/
theorem injOn_of_re_deriv_pos {f : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U)
    (hf : ∀ z ∈ U, HasDerivAt f (deriv f z) z)
    (hcont : ContinuousOn (fun z => deriv f z) U)
    (hpos : ∀ z ∈ U, 0 < (deriv f z).re) :
    Set.InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  set d : ℂ := b - a with hd
  have hdne : d ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
  set γ : ℝ → ℂ := fun t => a + (t : ℂ) * d with hγ
  have hγmem : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ U := by
    intro t ht
    have heq : γ t = (1 - t) • a + t • b := by
      simp only [hγ, hd, Complex.real_smul]; push_cast; ring
    rw [heq]
    exact hU ha hb (by linarith [ht.2]) ht.1 (by ring)
  have hγderiv : ∀ t, HasDerivAt γ d t := by
    intro t
    have h0 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by
      simpa using Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * d) d t := by simpa using h0.mul_const d
    simpa [hγ] using h1.const_add a
  have hgderiv : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun s => f (γ s)) (deriv f (γ t) * d) t := by
    intro t ht
    have h1 := (hf (γ t) (hγmem t ht)).scomp t (hγderiv t)
    simpa [smul_eq_mul, mul_comm] using h1
  have hcontint : ContinuousOn (fun t : ℝ => deriv f (γ t)) (Icc (0:ℝ) 1) := by
    apply hcont.comp _ hγmem
    exact (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)).continuousOn
  have hintble : IntervalIntegrable (fun t => deriv f (γ t)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hsub : f (γ 1) - f (γ 0) = ∫ t in (0:ℝ)..1, deriv f (γ t) * d := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hgderiv t (by
      rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht))]
    exact hintble.mul_const d
  have hγ0 : γ 0 = a := by simp [hγ]
  have hγ1 : γ 1 = b := by simp only [hγ]; push_cast; rw [hd]; ring
  rw [hγ0, hγ1, ← hab, sub_self, intervalIntegral.integral_mul_const] at hsub
  set I : ℂ := ∫ t in (0:ℝ)..1, deriv f (γ t) with hI
  have hre : I.re = ∫ t in (0:ℝ)..1, (deriv f (γ t)).re := by
    rw [hI]
    conv_lhs => rw [← Complex.reCLM_apply]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hintble]
    simp only [Complex.reCLM_apply]
  have hintble_re : IntervalIntegrable (fun t => (deriv f (γ t)).re) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Complex.continuous_re.comp_continuousOn hcontint
  have hReI : 0 < I.re := by
    rw [hre]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hintble_re ?_ (by norm_num)
    intro t ht
    exact hpos (γ t) (hγmem t (Ioo_subset_Icc_self ht))
  have hIne : I ≠ 0 := fun h => by rw [h] at hReI; simp at hReI
  exact hdne ((mul_eq_zero.mp hsub.symm).resolve_left hIne)

end Bottcher
