import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMHalfPlaneGreen

/-!
The original hyperbolic Laplacian satisfies full upper-half-plane Green integration by parts.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

def PlanarChartTest.mulSmooth (g : PlanarChartTest) (a : ℂ → ℂ) (ha : ContDiff ℝ ∞ a) :
    PlanarChartTest where
  field z := a z*g.field z
  smooth := ha.mul g.smooth
  compact := g.compact.mul_left
  support := (closure_mono (Function.support_mul_subset_right a g.field)).trans g.support

/-- One literal second derivative multiplied by the original squared height. -/
def PlanarChartTest.secondTest (g : PlanarChartTest) (v : ℂ) : PlanarChartTest :=
  ((g.derivative v).derivative v).mulSmooth (fun z => (z.im : ℂ)^(2 : ℕ))
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow 2)

private theorem PlanarChartTest.laplace_support (g : PlanarChartTest) :
    Function.support (fun z => ∑ i : Fin 2, (g.secondTest (direction i)).field z) ⊆
      tsupport g.field := by
    intro z hz
    by_contra hn
    have he (i : Fin 2) : (g.secondTest (direction i)).field z = 0 := by
      have hdd : ((g.derivative (direction i)).derivative (direction i)).field z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hi => hn
          ((tsupport_fderiv_apply_subset ℝ (direction i)).trans
            (tsupport_fderiv_apply_subset ℝ (direction i)) hi))
      change (z.im : ℂ)^(2 : ℕ)*((g.derivative (direction i)).derivative (direction i)).field z = 0
      rw [hdd,mul_zero]
    exact hz (by simp only [he,Finset.sum_const_zero])

/-- The full hyperbolic Laplacian of the test, still with compact positive-height support. -/
def PlanarChartTest.laplaceTest (g : PlanarChartTest) : PlanarChartTest where
  field z := ∑ i : Fin 2, (g.secondTest (direction i)).field z
  smooth := ContDiff.sum (fun i _ => (g.secondTest (direction i)).smooth)
  compact := HasCompactSupport.of_support_subset_isCompact g.compact g.laplace_support
  support := (closure_minimal g.laplace_support isClosed_closure).trans g.support

/-- The constructed test is exactly y² times the two original second derivatives. -/
theorem PlanarChartTest.laplaceTest_field (g : PlanarChartTest) (z : ℂ) :
    g.laplaceTest.field z = (z.im : ℂ)^(2 : ℕ) *
      ∑ i : Fin 2, fderiv ℝ (fun w => fderiv ℝ g.field w (direction i)) z (direction i) := by
  simp only [PlanarChartTest.laplaceTest,PlanarChartTest.secondTest,PlanarChartTest.mulSmooth,
    PlanarChartTest.derivative,Finset.mul_sum]

private theorem PlanarChartTest.integrable_pairing_full (g : PlanarChartTest)
    (h : UpperHalfPlane → ℂ) (hh : ChartSmooth h) :
    Integrable (fun z : UpperHalfPlane => conj (g.field z)*h z) (volume : Measure UpperHalfPlane) := by
  have hc := (Complex.conjCLE.continuous.comp (ChartSmooth.continuous g.toChartTest.smooth)).mul
    (ChartSmooth.continuous hh)
  have hk : HasCompactSupport (fun z : UpperHalfPlane => conj (g.field z)) :=
    g.toChartTest.compact.comp_left (by simp)
  exact hc.integrable_of_hasCompactSupport hk.mul_right

private theorem compact_gradient_pairing_integrable (g : CompactChartTest)
    (h : UpperHalfPlane → ℂ) (hh : ChartSmooth h) (v : ℂ) :
    Integrable (fun z => conj (weightedDeriv v g.field z)*weightedDeriv v h z)
      (volume : Measure UpperHalfPlane) := by
  have hc := (Complex.conjCLE.continuous.comp (weightedDeriv_continuous v g.field g.smooth)).mul
    (weightedDeriv_continuous v h hh)
  apply hc.integrable_of_hasCompactSupport
  apply g.compact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hn
  exact hz (by
    change conj (weightedDeriv v g.field z)*weightedDeriv v h z = 0
    rw [weightedDeriv_zero_off_support g.field z hn v]
    simp)

/-- Both original directional derivatives move onto a positive-height compact
test in the full hyperbolic integral. No modular boundary is excised. -/
theorem PlanarChartTest.directional_green (g : PlanarChartTest)
    (h : UpperHalfPlane → ℂ) (hh : ChartSmooth h) (v : ℂ) :
    (∫ z : UpperHalfPlane, conj (weightedDeriv v g.toChartTest.field z)*weightedDeriv v h z) =
      -(∫ z : UpperHalfPlane, conj ((g.secondTest v).field z)*h z) := by
  have he := weightedDeriv_full_test_identity h hh (g.derivative v).conjugate v
  have hL : (∫ z : UpperHalfPlane, conj (weightedDeriv v g.toChartTest.field z)*weightedDeriv v h z) =
      ∫ z : UpperHalfPlane, weightedDeriv v h z*((z.im : ℂ)*(g.derivative v).conjugate.field z) := by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [g.weightedDeriv_eq]
    simp only [map_mul,Complex.conj_ofReal,PlanarChartTest.conjugate,PlanarChartTest.derivative]
    ring
  have hR : (∫ z : UpperHalfPlane, h z*((z.im : ℂ)^(2 : ℕ)*
      fderiv ℝ (g.derivative v).conjugate.field (z:ℂ) v)) =
      ∫ z : UpperHalfPlane, conj ((g.secondTest v).field z)*h z := by
    apply integral_congr_ae
    filter_upwards [] with z
    rw [(g.derivative v).conjugate_deriv]
    simp only [PlanarChartTest.secondTest,PlanarChartTest.mulSmooth,PlanarChartTest.derivative,
      map_mul,map_pow,Complex.conj_ofReal,coe_im]
    ring
  rw [hL,he,hR]

/-- Full upper-half-plane Green identity for the actual hyperbolic Laplacian. -/
theorem PlanarChartTest.full_green (g : PlanarChartTest)
    (h : UpperHalfPlane → ℂ) (hh : ChartSmooth h) :
    (∫ z : UpperHalfPlane, frameEnergy g.toChartTest.field h z) =
      -(∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*h z) := by
  change (∫ z : UpperHalfPlane, ∑ i : Fin 2,
    conj (weightedDeriv (direction i) g.toChartTest.field z)*weightedDeriv (direction i) h z) = _
  rw [integral_finsetSum _
    (fun i _ => compact_gradient_pairing_integrable g.toChartTest h hh (direction i))]
  simp_rw [g.directional_green h hh]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => (g.secondTest (direction i)).integrable_pairing_full h hh)]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.laplaceTest,map_sum,Finset.sum_mul]

end
end RHTower.D4BMModularCore
