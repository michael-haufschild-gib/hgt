import GaloisForLFunctions.HTGeometry.FokasLenellsRawEndpoints
import GaloisForLFunctions.HTGeometry.FokasLenellsScattering

/-!
# The original scattering matrix at every real spectral frequency

The raw interaction equation remains traceless through k = 0. Its actual
endpoint matrices therefore have determinant one at every real k. Their
connection matrix agrees exactly with the existing positive-frequency
scattering matrix, and equals the identity at zero.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawInteractionSolution_add (q : SchwartzMap ℝ ℂ) (k : ℝ) (v w : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k (v+w) x = rawInteractionSolution q k v x+rawInteractionSolution q k w x :=
  (rawInteractionEvolution q k x).map_add v w

theorem rawInteractionSolution_smul (q : SchwartzMap ℝ ℂ) (k : ℝ) (c : ℂ) (v : SpectralVector) (x : ℝ) :
    rawInteractionSolution q k (c • v) x = c • rawInteractionSolution q k v x :=
  (rawInteractionEvolution q k x).map_smul c v

/-- Both asymptotic maps retain the linearity of the genuine evolution. -/
theorem rawAsymptoticVector_add (q : SchwartzMap ℝ ℂ) (k : ℝ) (v w : SpectralVector) (left : Bool) :
    rawAsymptoticVector q k (v+w) left = rawAsymptoticVector q k v left+rawAsymptoticVector q k w left := by
  have hh := (rawOrientedSolution_tendsto q k v left).add (rawOrientedSolution_tendsto q k w left)
  have he := rawOrientedSolution_tendsto q k (v+w) left
  have heq : rawOrientedSolution q k (v+w) left = fun x =>
      rawOrientedSolution q k v left x+rawOrientedSolution q k w left x := by
    funext x
    exact rawInteractionSolution_add q k v w (if left then -x else x)
  rw [heq] at he
  exact tendsto_nhds_unique he hh

theorem rawAsymptoticVector_smul (q : SchwartzMap ℝ ℂ) (k : ℝ) (c : ℂ) (v : SpectralVector) (left : Bool) :
    rawAsymptoticVector q k (c • v) left = c • rawAsymptoticVector q k v left := by
  have hh := (rawOrientedSolution_tendsto q k v left).const_smul c
  have he := rawOrientedSolution_tendsto q k (c • v) left
  have heq : rawOrientedSolution q k (c • v) left = fun x =>
      c • rawOrientedSolution q k v left x := by
    funext x
    exact rawInteractionSolution_smul q k c v (if left then -x else x)
  rw [heq] at he
  exact tendsto_nhds_unique he hh

private theorem rawWedge_derivative (q : SchwartzMap ℝ ℂ) (k : ℝ) (v w : SpectralVector) (x : ℝ) :
    HasDerivAt (fun y => (rawInteractionSolution q k v y).1*(rawInteractionSolution q k w y).2-
      (rawInteractionSolution q k v y).2*(rawInteractionSolution q k w y).1) 0 x := by
  have hv := rawInteractionSolution_hasDerivAt q k v x
  have hw := rawInteractionSolution_hasDerivAt q k w x
  have hv1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hv
  have hv2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hv
  have hw1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hw
  have hw2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hw
  refine ((hv1.mul hw2).sub (hv2.mul hw1)).congr_deriv ?_
  simp only [rawInteractionOperator_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_def]
  ring

/-- The actual raw flow preserves the determinant pairing, including negative and zero frequencies. -/
theorem rawInteractionSolution_wedge (q : SchwartzMap ℝ ℂ) (k : ℝ) (v w : SpectralVector) (x : ℝ) :
    (rawInteractionSolution q k v x).1*(rawInteractionSolution q k w x).2-
      (rawInteractionSolution q k v x).2*(rawInteractionSolution q k w x).1 = v.1*w.2-v.2*w.1 := by
  have hh := is_const_of_deriv_eq_zero
    (fun y => (rawWedge_derivative q k v w y).differentiableAt)
    (fun y => (rawWedge_derivative q k v w y).deriv) x 0
  simpa only [rawInteractionSolution_initial] using hh

theorem rawAsymptoticVector_wedge (q : SchwartzMap ℝ ℂ) (k : ℝ) (v w : SpectralVector) (left : Bool) :
    (rawAsymptoticVector q k v left).1*(rawAsymptoticVector q k w left).2-
      (rawAsymptoticVector q k v left).2*(rawAsymptoticVector q k w left).1 = v.1*w.2-v.2*w.1 := by
  have hv := rawOrientedSolution_tendsto q k v left
  have hw := rawOrientedSolution_tendsto q k w left
  have hv1 := ((ContinuousLinearMap.fst ℝ ℂ ℂ).continuous.tendsto _).comp hv
  have hv2 := ((ContinuousLinearMap.snd ℝ ℂ ℂ).continuous.tendsto _).comp hv
  have hw1 := ((ContinuousLinearMap.fst ℝ ℂ ℂ).continuous.tendsto _).comp hw
  have hw2 := ((ContinuousLinearMap.snd ℝ ℂ ℂ).continuous.tendsto _).comp hw
  have hh := (hv1.mul hw2).sub (hv2.mul hw1)
  change Tendsto (fun x => (rawOrientedSolution q k v left x).1*(rawOrientedSolution q k w left x).2-
    (rawOrientedSolution q k v left x).2*(rawOrientedSolution q k w left x).1) atTop _ at hh
  simp only [rawOrientedSolution,rawInteractionSolution_wedge] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

def rawFundamentalMatrix (q : SchwartzMap ℝ ℂ) (k x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawInteractionSolution q k (1,0) x).1, (rawInteractionSolution q k (0,1) x).1;
     (rawInteractionSolution q k (1,0) x).2, (rawInteractionSolution q k (0,1) x).2]

def rawAsymptoticMatrix (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rawAsymptoticVector q k (1,0) left).1, (rawAsymptoticVector q k (0,1) left).1;
     (rawAsymptoticVector q k (1,0) left).2, (rawAsymptoticVector q k (0,1) left).2]

theorem rawFundamentalMatrix_det (q : SchwartzMap ℝ ℂ) (k x : ℝ) :
    (rawFundamentalMatrix q k x).det = 1 := by
  have hh := rawInteractionSolution_wedge q k (1,0) (0,1) x
  simpa [rawFundamentalMatrix,Matrix.det_fin_two,mul_comm] using hh

theorem rawAsymptoticMatrix_det (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    (rawAsymptoticMatrix q k left).det = 1 := by
  have hh := rawAsymptoticVector_wedge q k (1,0) (0,1) left
  simpa [rawAsymptoticMatrix,Matrix.det_fin_two,mul_comm] using hh

theorem rawAsymptoticMatrix_mul_inverse (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    rawAsymptoticMatrix q k left*(rawAsymptoticMatrix q k left)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [rawAsymptoticMatrix_det]
  exact isUnit_one

theorem rawAsymptoticMatrix_inverse_mul (q : SchwartzMap ℝ ℂ) (k : ℝ) (left : Bool) :
    (rawAsymptoticMatrix q k left)⁻¹*rawAsymptoticMatrix q k left = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [rawAsymptoticMatrix_det]
  exact isUnit_one

theorem rawAsymptoticMatrix_zero_frequency (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawAsymptoticMatrix q 0 left = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rawAsymptoticMatrix,rawAsymptoticVector_zero_frequency]

theorem rawAsymptoticMatrix_exp_right (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    rawAsymptoticMatrix q (Real.exp κ) false = rightAsymptoticMatrix q κ := by
  simp only [rawAsymptoticMatrix,rightAsymptoticMatrix,rawAsymptoticVector_exp_right]

theorem rawAsymptoticMatrix_exp_left (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    rawAsymptoticMatrix q (Real.exp κ) true = leftAsymptoticMatrix q κ := by
  simp only [rawAsymptoticMatrix,leftAsymptoticMatrix,rawAsymptoticVector_exp_left]

/-- The original scattering connection, now defined by actual endpoint solutions at every real k. -/
def rawScatteringMatrix (q : SchwartzMap ℝ ℂ) (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rawAsymptoticMatrix q k false*(rawAsymptoticMatrix q k true)⁻¹

theorem rawScatteringMatrix_det (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    (rawScatteringMatrix q k).det = 1 := by
  rw [rawScatteringMatrix,Matrix.det_mul,Matrix.det_nonsing_inv,rawAsymptoticMatrix_det,
    rawAsymptoticMatrix_det]
  simp

/-- This extension is an exact equality with the previously constructed scattering data. -/
theorem rawScatteringMatrix_exp_eq (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    rawScatteringMatrix q (Real.exp κ) = scatteringMatrix q κ := by
  rw [rawScatteringMatrix,rawAsymptoticMatrix_exp_right,rawAsymptoticMatrix_exp_left]
  rfl

theorem rawScatteringMatrix_zero_frequency (q : SchwartzMap ℝ ℂ) :
    rawScatteringMatrix q 0 = 1 := by
  simp only [rawScatteringMatrix,rawAsymptoticMatrix_zero_frequency,inv_one,mul_one]

/-- The endpoint connection law holds through zero without an invertibility premise. -/
theorem rawScatteringMatrix_connection (q : SchwartzMap ℝ ℂ) (k : ℝ) :
    rawScatteringMatrix q k*rawAsymptoticMatrix q k true = rawAsymptoticMatrix q k false := by
  rw [rawScatteringMatrix,Matrix.mul_assoc,rawAsymptoticMatrix_inverse_mul,mul_one]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
