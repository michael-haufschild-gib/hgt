import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.RHTower.MellinContinuationOrder
import GaloisForLFunctions.RHTower.SoninExtendedMellinPole
import GaloisForLFunctions.RHTower.SoninExtendedDilation

/-!
# The continued Mellin transform does not depend on the aperture

A vector of `L_b` is also a vector of `L_a` for every `a ≤ b`, with the *same* two band constants.
On the strip of absolute convergence `1/2 < Re s < 1` the continued transform is then the honest
Mellin integral `∫_{t>0} f(t)t^{-s}dt` at either aperture, and the identity theorem propagates the
agreement to the whole open critical strip.

## Main results

* `extendedMellinContinuation_eq_soninMellinIntegral`
* `extendedMellinContinuation_aperture_eq`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {f : SoninL2} {c d : ℂ}

/-- **On the strip of absolute convergence the continued transform is the Mellin integral.** -/
theorem extendedMellinContinuation_eq_soninMellinIntegral (ha : 0 < a) (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) :
    extendedMellinContinuation a c d f s = soninMellinIntegral f s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs1; simp at hs1; linarith
  have hsne1 : s ≠ 1 := by
    intro h; rw [h] at hs2; simp at hs2
  have hhead : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) a)), (f : ℝ → ℂ) t = d := by
    filter_upwards [ae_restrict_of_ae hd,
      self_mem_ae_restrict (measurableSet_Ioc (a := (0 : ℝ)) (b := a))] with t ht hmem
    refine ht ?_
    rcases hmem with ⟨h1, h2⟩
    exact ⟨by linarith, h2⟩
  have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Ioc (0 : ℝ) a) volume := by
    refine (integrableOn_head_cpow ha hs2 d).congr_fun_ae ?_
    filter_upwards [hhead] with t ht
    rw [ht]
  have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      (Ioi a) volume := integrableOn_cpow_mul_Ioi ha f hs1
  have hsplit : soninMellinIntegral f s
      = (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
    rw [soninMellinIntegral, ← Ioc_union_Ioi_eq_Ioi ha.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint1 hint2
  have hheadval : (∫ t in Ioc (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
      = d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
    rw [← integral_head_cpow_Ioc ha hs2 d]
    refine integral_congr_ae ?_
    filter_upwards [hhead] with t ht
    rw [ht]
  rw [extendedMellinContinuation_eq_right a c d f (le_of_lt hs1) hs0 hsne1, extendedMellinRight,
    extendedTailMellin_eq ha hc hs1, hsplit, hheadval]
  ring

/-- **The continued Mellin transform is the same at any two apertures for which the vector has the
same two band constants.** -/
theorem extendedMellinContinuation_aperture_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hev : f ∈ evenSubspace)
    (hca : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hda : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hcb : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hdb : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    extendedMellinContinuation a c d f s = extendedMellinContinuation b c d f s := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hconn : IsPreconnected {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    have h1 : Convex ℝ {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0
    have h2 : Convex ℝ {z : ℂ | z.re < 1} := convex_halfSpace_re_lt 1
    exact (h1.inter h2).isPreconnected
  have hA1 : AnalyticOnNhd ℂ (extendedMellinContinuation a c d f)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    exact analyticAt_extendedMellinContinuation_of_ne ha hev hca hda hz0 hz1
  have hA2 : AnalyticOnNhd ℂ (extendedMellinContinuation b c d f)
      {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    intro z hz
    have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    have hz1 : z ≠ 1 := by intro h; rw [h] at hz; simp at hz
    exact analyticAt_extendedMellinContinuation_of_ne hb hev hcb hdb hz0 hz1
  have hz₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by
    constructor <;> simp <;> norm_num
  have hev₀ : extendedMellinContinuation a c d f =ᶠ[𝓝 ((3 / 4 : ℝ) : ℂ)]
      extendedMellinContinuation b c d f := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hmem₀ : ((3 / 4 : ℝ) : ℂ) ∈ {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} := by
      constructor <;> simp <;> norm_num
    filter_upwards [hopen.mem_nhds hmem₀] with z hz
    rw [extendedMellinContinuation_eq_soninMellinIntegral ha hev hca hda hz.1 hz.2,
      extendedMellinContinuation_eq_soninMellinIntegral hb hev hcb hdb hz.1 hz.2]
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hconn hz₀ hev₀ ⟨hs0, hs1⟩

end

end RHTower
