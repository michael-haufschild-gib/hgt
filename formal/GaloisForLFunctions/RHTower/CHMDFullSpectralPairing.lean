import GaloisForLFunctions.RHTower.CHMDGraphMixedExplicitFormula
import GaloisForLFunctions.RHTower.CHMDGraphPolarReadout
import GaloisForLFunctions.RHTower.CHMDShiftedFourierReadout

/-!
# Full spectral silence leaves exactly the two polar moments

The mixed explicit formula and compact-core density determine every pairing of
a graph source whose full Fourier samples vanish at the literal Xi zeros.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
noncomputable section
namespace RHTower.CHMDDoobGraph
open WeilSpectral

def fullSpectralNullspace : Set SourceGraph :=
  {p | ∀ z : ℂ, XiC z = 0 → graphFourierReadout p z = 0}

def polarCosine (p : SourceGraph) : ℝ := (graphCosineReadout p (I/2)).re

def polarSine (p : SourceGraph) : ℝ :=
  ((graphFourierReadout p (-I/2)).re - (graphFourierReadout p (I/2)).re)/2

theorem polarCosine_eq_half_fourier (p : SourceGraph) :
    polarCosine p = ((graphFourierReadout p (I/2)).re +
      (graphFourierReadout p (-I/2)).re)/2 := by
  rw [polarCosine, graphCosineReadout_eq_half_fourier p (by norm_num)]
  simp only [neg_div, Complex.div_ofNat_re, Complex.add_re]

theorem continuous_polarCosine : Continuous polarCosine :=
  Complex.continuous_re.comp (continuous_graphCosineReadout (I/2))

theorem continuous_polarSine : Continuous polarSine :=
  ((Complex.continuous_re.comp (continuous_graphFourierReadout (z := -I/2) (by norm_num))).sub
    (Complex.continuous_re.comp (continuous_graphFourierReadout (z := I/2) (by norm_num)))).div_const 2

theorem ground_mem_fullSpectralNullspace : constantLift 1 ∈ fullSpectralNullspace := by
  intro z hz
  rw [graphFourierReadout_ground, hz]

theorem polarCosine_ground : polarCosine (constantLift 1) = 1/2 := by
  rw [polarCosine, graphCosineReadout_ground_pole]
  norm_num

theorem polarSine_ground : polarSine (constantLift 1) = 0 := by
  rw [polarSine, neg_div, graphFourierReadout_neg_of_even evenGraphSource_ground,
    sub_self, zero_div]

theorem ground_fourier_pole : graphFourierReadout (constantLift 1) (I/2) = 1/2 := by
  rw [graphFourierReadout_eq_cosine_of_even evenGraphSource_ground (by norm_num),
    graphCosineReadout_ground_pole]

theorem graphMixedZeroTerm_eq_zero_of_full_nullspace {p : SourceGraph}
    (hp : p ∈ fullSpectralNullspace) (f : ℝ → ℝ) (ρ : zetaZeroConfig.carrier) :
    graphMixedZeroTerm p f ρ = 0 := by
  have hz := CHMDStage16.XiC_gammaOf_eq_zero ρ
  have hn : XiC (-gammaOf ρ) = 0 := by rw [XiC_even, hz]
  simp only [graphMixedZeroTerm, hp _ hz, hp _ hn, mul_zero, add_zero]

theorem full_nullspace_pair_compact {p : SourceGraph} (hp : p ∈ fullSpectralNullspace)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    sourcePair p (testLift f hf hc) =
      -((graphFourierReadout p (I/2)).re * (graphFourierReadout (testLift f hf hc) (-I/2)).re +
        (graphFourierReadout p (-I/2)).re * (graphFourierReadout (testLift f hf hc) (I/2)).re) := by
  rw [sourcePair_testLift_eq_mixed p hf hc, mixedGraphFunctional_eq p hf hc]
  simp_rw [graphMixedZeroTerm_eq_zero_of_full_nullspace hp f]
  have hplus := graphFourierReadout_real_of_re_zero p (z := I/2) (by norm_num)
  have hminus := graphFourierReadout_real_of_re_zero p (z := -I/2) (by norm_num)
  simp only [graphFourierReadout_testLift, tsum_zero, zero_div, Complex.sub_re,
    Complex.zero_re, Complex.mul_re, hplus, hminus, mul_zero, sub_zero]
  ring

theorem full_nullspace_pair_poles {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) (q : SourceGraph) :
    sourcePair p q = -((graphFourierReadout p (I/2)).re * (graphFourierReadout q (-I/2)).re +
      (graphFourierReadout p (-I/2)).re * (graphFourierReadout q (I/2)).re) := by
  have he : (fun q => sourcePair p q) =
      (fun q => -((graphFourierReadout p (I/2)).re * (graphFourierReadout q (-I/2)).re +
        (graphFourierReadout p (-I/2)).re * (graphFourierReadout q (I/2)).re)) := by
    apply Continuous.ext_on dense_compactTests
      (continuous_sourcePair.comp (continuous_const.prodMk continuous_id))
      (((continuous_const.mul (Complex.continuous_re.comp
        (continuous_graphFourierReadout (z := -I/2) (by norm_num)))).add
        (continuous_const.mul (Complex.continuous_re.comp
          (continuous_graphFourierReadout (z := I/2) (by norm_num))))).neg)
    rintro q ⟨v, hv, hc, rfl⟩
    rw [← testLift_phi v hv hc]
    exact full_nullspace_pair_compact hp (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hc)
  exact congrFun he q

/-- The two polar coordinates give the entire signed form of a zero-silent vector. -/
theorem full_nullspace_pair {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) (q : SourceGraph) :
    sourcePair p q = -2 * polarCosine p * polarCosine q + 2 * polarSine p * polarSine q := by
  rw [full_nullspace_pair_poles hp q, polarCosine_eq_half_fourier p, polarCosine_eq_half_fourier q]
  unfold polarSine
  ring

theorem full_nullspace_energy {p : SourceGraph} (hp : p ∈ fullSpectralNullspace) :
    sourceEnergy p = -2 * polarCosine p ^ 2 + 2 * polarSine p ^ 2 := by
  rw [← sourcePair_self, full_nullspace_pair hp p]
  ring

end RHTower.CHMDDoobGraph
