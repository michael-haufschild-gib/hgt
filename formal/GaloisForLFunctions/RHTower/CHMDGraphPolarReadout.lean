import GaloisForLFunctions.RHTower.CHMDStripFourierReadout
import GaloisForLFunctions.RHTower.CHMDPolarGraphMoments

/-!
# Ground pairing is the polar cosine sample on the full graph

The identity holds for arbitrary graph sources, including nonsmooth sources.
The ground vector's literal entire transform is Xi, and its polar sample is 1/2.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.CHMDDoobGraph

theorem graphCosineReadout_pole (p : SourceGraph) :
    graphCosineReadout p (I/2) =
      ((∫ x, phiDoobTest p.val.fst x * Real.cosh (x/2) : ℝ) : ℂ) := by
  rw [graphCosineReadout_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show (I/2)*(x : ℂ) = ((x/2 : ℝ) : ℂ)*I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh, Complex.ofReal_mul]

theorem graphCosineReadout_pole_im (p : SourceGraph) :
    (graphCosineReadout p (I/2)).im = 0 := by
  rw [graphCosineReadout_pole, Complex.ofReal_im]

/-- The polar functional is exactly negative pairing with the ground vector. -/
theorem sourcePair_ground_eq_graphCosine (p : SourceGraph) :
    sourcePair (constantLift 1) p = -(graphCosineReadout p (I/2)).re := by
  have hp : p.val.fst =ᵐ[massMeasure] phiDoobInv (phiDoobTest p.val.fst) :=
    Eventually.of_forall fun x => (phiDoobInv_phiDoobTest p.val.fst x).symm
  rw [sourcePair_ground_eq_cosh hp, graphCosineReadout_pole, Complex.ofReal_re]

theorem graphCosineReadout_ground_pole : graphCosineReadout (constantLift 1) (I/2) = 1/2 := by
  have h := sourcePair_ground_eq_graphCosine (constantLift 1)
  rw [sourcePair_self, constantLift_energy] at h
  apply Complex.ext
  · norm_num at h ⊢
    linarith
  · simp only [graphCosineReadout_pole_im]
    norm_num

theorem ground_source_eq_inverse_theta :
    (constantLift 1).val.fst =ᵐ[massMeasure] phiDoobInv riemannKernelReal := by
  have hc : (constantLift 1).val.fst =ᵐ[massMeasure] (fun _ => (1 : ℝ)) :=
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
  filter_upwards [hc] with x hx
  rw [hx, phiDoobInv, div_self (riemannKernelReal_pos x).ne']

theorem evenGraphSource_ground : EvenGraphSource (constantLift 1) := by
  have h : phiDoobTest (constantLift 1).val.fst =ᵐ[volume] riemannKernelReal := by
    filter_upwards [volume_absolutelyContinuous_mass.ae_eq ground_source_eq_inverse_theta] with x hx
    rw [phiDoobTest, hx, phiDoobInv, div_self (riemannKernelReal_pos x).ne', mul_one]
  have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  unfold EvenGraphSource
  filter_upwards [h, hn] with x hx hn
  rw [hn, hx]
  simp only [riemannKernelReal, abs_neg]

theorem graphFourierReadout_ground (z : ℂ) : graphFourierReadout (constantLift 1) z = XiC z := by
  rw [graphFourierReadout_of_source ground_source_eq_inverse_theta,
    paperFT_eq_sourceTransform_neg]
  have he : (fun x => (riemannKernelReal x : ℂ)) = thetaSourceC := by
    funext x
    simp only [thetaSourceC, thetaCuspFullSource_eq_riemannKernelReal]
  rw [he, sourceTransform_thetaSourceC, XiC_even]

theorem graphCosineReadout_ground {z : ℂ} (hz : |z.im| ≤ 1/2) :
    graphCosineReadout (constantLift 1) z = XiC z := by
  rw [graphCosineReadout_eq_half_fourier _ hz, graphFourierReadout_ground,
    graphFourierReadout_ground, XiC_even]
  ring

end RHTower.CHMDDoobGraph
