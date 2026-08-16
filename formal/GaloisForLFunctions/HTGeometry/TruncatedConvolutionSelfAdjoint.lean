import GaloisForLFunctions.HTGeometry.TruncatedConvolutionCommutator
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The truncated convolution is symmetric for the `L²` pairing on the unit interval

Swapping the two variables in the double integral and using that the kernel is even turns the
pairing of `f` against `A g` into the pairing of `A f` against `g`.  This is the only place where
Fubini is used; the divided-difference law itself needs none.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Iterated interval integrals of a continuous function on the unit square commute. -/
theorem intervalIntegral_swap_unitSquare (F : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y)
      = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F x y := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  simp only [intervalIntegral.integral_of_le h01]
  have hprod : (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))
      = (volume.prod volume).restrict (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) :=
    Measure.prod_restrict _ _
  have hcpt : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    rw [hprod]
    exact (hF.continuousOn.integrableOn_compact hcpt).mono_set hsub
  exact MeasureTheory.integral_integral_swap hint

/-- The `L²` pairing on the unit interval. -/
def l2Pair (f g : ℝ → ℂ) : ℂ := ∫ x in (0 : ℝ)..1, (starRingEnd ℂ) (f x) * g x

theorem l2Pair_conj (f g : ℝ → ℂ) :
    (starRingEnd ℂ) (l2Pair f g) = l2Pair g f := by
  rw [l2Pair, intervalIntegral_conj, l2Pair]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

theorem l2Pair_add_right (f g h : ℝ → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hf : Continuous f) :
    l2Pair f (fun x => g x + h x) = l2Pair f g + l2Pair f h := by
  rw [l2Pair, l2Pair, l2Pair, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  · exact ((hf.star).mul hg).intervalIntegrable _ _
  · exact ((hf.star).mul hh).intervalIntegrable _ _

theorem l2Pair_smul_right (a : ℂ) (f g : ℝ → ℂ) :
    l2Pair f (fun x => a * g x) = a * l2Pair f g := by
  rw [l2Pair, l2Pair, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

theorem l2Pair_smul_left (a : ℂ) (f g : ℝ → ℂ) :
    l2Pair (fun x => a * f x) g = (starRingEnd ℂ) a * l2Pair f g := by
  rw [l2Pair, l2Pair, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [map_mul]
  ring

/-- **The truncated convolution is symmetric.** -/
theorem truncConv_selfAdjoint {k : ℝ → ℝ} (hkc : Continuous k) (heven : ∀ u, k (-u) = k u)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    l2Pair f (truncConv k g) = l2Pair (truncConv k f) g := by
  set F : ℝ → ℝ → ℂ := fun x y => ((k (x - y) : ℝ) : ℂ) * (starRingEnd ℂ) (f y) * g x with hFdef
  have hFcont : Continuous (Function.uncurry F) := by
    rw [hFdef]
    have h1 : Continuous fun p : ℝ × ℝ => ((k (p.1 - p.2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (hkc.comp (continuous_fst.sub continuous_snd))
    exact (h1.mul ((hf.star).comp continuous_snd)).mul (hg.comp continuous_fst)
  have hswap := intervalIntegral_swap_unitSquare F hFcont
  have hleft : l2Pair (truncConv k f) g = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F x y := by
    rw [l2Pair]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [truncConv, intervalIntegral_conj, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [map_mul, Complex.conj_ofReal, hFdef]
  have hright : l2Pair f (truncConv k g) = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F x y := by
    rw [l2Pair]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [truncConv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hflip : k (y - x) = k (x - y) := by
      rw [← heven (y - x)]
      congr 1
      ring
    rw [hFdef]
    simp only
    rw [hflip]
    ring
  rw [hleft, hright, hswap]

end

end GaloisForLFunctions.HTGeometry
