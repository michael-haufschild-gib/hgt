import GaloisForLFunctions.RHTower.CCMPrimePoleSchurDefect
import GaloisForLFunctions.HTGeometry.GaussianPolynomialPhaseDefect
import GaloisForLFunctions.HTGeometry.ModulationWeakEscape

/-!
# Modulated actual pole profiles and their full prime-edge energy

Modulation preserves physical mass while its pairings with every fixed vector
vanish at high frequency. For the positive pole profile, its complete complex
edge energy is exactly the phase defect times the corresponding row integral.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

def ccmSchurPoleVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ccmPolarApertureVector a (1/2) + ccmPolarApertureVector a (-1/2)

theorem ccmSchurPoleVector_coeFn (a : SuzukiPositiveAperture) :
    (ccmSchurPoleVector a : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x => (primePoleProfile x : ℂ)) := by
  filter_upwards [Lp.coeFn_add (ccmPolarL2Vector a (1/2)) (ccmPolarL2Vector a (-1/2)),
    ccmPolarL2Vector_coeFn a (1/2), ccmPolarL2Vector_coeFn a (-1/2)] with x ha hp hm
  change (ccmPolarL2Vector a (1/2) + ccmPolarL2Vector a (-1/2)) x = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [hp, hm]
  by_cases hx : x ∈ centralInterval a.1
  · simp only [indicator_of_mem hx, ccmPolarProfile, primePoleProfile, Complex.ofReal_add]
    congr 2 <;> congr 1 <;> ring
  · simp only [indicator_of_notMem hx, zero_add]

def ccmApertureModulation (a : SuzukiPositiveAperture) (t : ℝ)
    (f : suzukiApertureHilbert a) : suzukiApertureHilbert a := by
  refine ⟨modulationMul t f.1, ?_⟩
  change modulationMul t f.1 ∈
    physicalForbidden (centralInterval a.1) (measurableSet_centralInterval a.1)
  rw [physicalForbidden, LinearMap.mem_range]
  refine ⟨modulationMul t f.1, ?_⟩
  apply Lp.ext
  have hf := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (modulationMul t f.1), coeFn_modulationMul t f.1, hf] with x hc hm hf
  change (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
    (modulationMul t f.1) : SoninL2) x = (modulationMul t f.1) x
  rw [hc]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hm, hf, indicator_of_notMem hx, mul_zero]

theorem norm_ccmApertureModulation (a : SuzukiPositiveAperture) (t : ℝ)
    (f : suzukiApertureHilbert a) : ‖ccmApertureModulation a t f‖ = ‖f‖ :=
  GaloisForLFunctions.norm_modulationMul_eq t f.1

private theorem phase_add (t x h : ℝ) :
    modulationSymbol t (x+h) = modulationSymbol t x * modulationSymbol t h := by
  unfold modulationSymbol
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ccmPrimePoleEdgeEnergy_modulatedPole (a : SuzukiPositiveAperture) (t h : ℝ) :
    ccmPrimePoleEdgeEnergy a h (ccmApertureModulation a t (ccmSchurPoleVector a)).1 =
      ‖modulationSymbol t h - 1‖ ^ 2 *
        ∫ x : ℝ, ccmPrimePoleRowDensity a h (ccmSchurPoleVector a).1 x := by
  let w := ccmSchurPoleVector a
  let f := ccmApertureModulation a t w
  have hw := ccmSchurPoleVector_coeFn a
  have hf : (f.1 : ℝ → ℂ) =ᵐ[volume] fun x => modulationSymbol t x * w.1 x :=
    coeFn_modulationMul t w.1
  have hwt := hw.comp_tendsto
    (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
  have hft := hf.comp_tendsto
    (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
  unfold ccmPrimePoleEdgeEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hw, hf, hwt, hft] with x hw hf hwt hft
  change w.1 (x+h) =
    (centralInterval a.1).indicator (fun x => (primePoleProfile x : ℂ)) (x+h) at hwt
  change f.1 (x+h) = modulationSymbol t (x+h) * w.1 (x+h) at hft
  change ccmPrimePoleEdgeDensity a h f.1 x = _
  unfold ccmPrimePoleEdgeDensity ccmPrimePoleRowDensity
  by_cases hx : x ∈ centralInterval a.1 <;> by_cases hy : x+h ∈ centralInterval a.1
  · rw [indicator_of_mem (show x ∈ centralInterval a.1 ∩
        (fun y : ℝ => y+h) ⁻¹' centralInterval a.1 from ⟨hx,hy⟩),
      indicator_of_mem hy, hf, hft, hw, hwt, indicator_of_mem hx, indicator_of_mem hy,
      phase_add]
    have heq : (primePoleProfile x : ℂ) *
          (modulationSymbol t x * modulationSymbol t h * (primePoleProfile (x+h) : ℂ)) -
        (primePoleProfile (x+h) : ℂ) * (modulationSymbol t x * (primePoleProfile x : ℂ)) =
        ((primePoleProfile x * primePoleProfile (x+h) : ℝ) : ℂ) *
          modulationSymbol t x * (modulationSymbol t h - 1) := by push_cast; ring
    rw [heq, norm_mul, norm_mul, norm_modulationSymbol, mul_one,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (mul_pos (primePoleProfile_pos _) (primePoleProfile_pos _)).le,
      Real.norm_of_nonneg (primePoleProfile_pos _).le]
    field_simp
  · simp [hx, hy]
  · simp [hx, hy, hw]
  · simp [hx, hy]

/-- All fixed pole or source pairings vanish, despite unchanged physical norm. -/
theorem inner_ccmApertureModulation_tendsto_zero (a : SuzukiPositiveAperture)
    (f g : suzukiApertureHilbert a) :
    Tendsto (fun t : ℝ => inner ℂ g (ccmApertureModulation a t f)) atTop (𝓝 0) :=
  modulationMul_inner_tendsto f.1 g.1

end RHTower
