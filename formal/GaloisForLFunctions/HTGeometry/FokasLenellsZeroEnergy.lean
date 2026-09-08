import GaloisForLFunctions.HTGeometry.FokasLenellsRegularizedData

/-!
# Exact zero-energy transport for derivative-profile data

At spectral parameter zero the paper's uniformized potential with coefficients
(f,p',f') is a pure gauge. A lower shear in f and an upper shear in p give the
entire fundamental matrix explicitly. For arbitrary Schwartz f and p both gauges
tend to the identity at both spatial ends. Thus the zero-energy scattering matrix
is exactly the identity, with no smallness assumption or transmission hypothesis.
-/

open MeasureTheory Complex Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The zero-energy gauge acts by two elementary shears. -/
def zeroEnergyAction (f p : ℂ) (v : SpectralVector) : SpectralVector :=
  (v.1-I*p*v.2/2,f*(v.1-I*p*v.2/2)+v.2)

def zeroEnergyInverseAction (f p : ℂ) (v : SpectralVector) : SpectralVector :=
  (v.1+I*p*(v.2-f*v.1)/2,v.2-f*v.1)

theorem zeroEnergyAction_inverse (f p : ℂ) (v : SpectralVector) :
    zeroEnergyAction f p (zeroEnergyInverseAction f p v) = v := by
  apply Prod.ext <;> simp [zeroEnergyAction,zeroEnergyInverseAction]

theorem zeroEnergyInverseAction_inverse (f p : ℂ) (v : SpectralVector) :
    zeroEnergyInverseAction f p (zeroEnergyAction f p v) = v := by
  apply Prod.ext <;> simp [zeroEnergyAction,zeroEnergyInverseAction]

def zeroEnergyGauge (f p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1,-I*p/2;f,1-I*f*p/2]

def zeroEnergyInverseGauge (f p : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1-I*f*p/2,I*p/2;-f,1]

/-- The matrix gauge has determinant one for arbitrary complex profile values. -/
theorem zeroEnergyGauge_det (f p : ℂ) : (zeroEnergyGauge f p).det = 1 := by
  simp [zeroEnergyGauge,Matrix.det_fin_two]
  ring

theorem zeroEnergyGauge_mul_inverse (f p : ℂ) :
    zeroEnergyGauge f p*zeroEnergyInverseGauge f p = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zeroEnergyGauge,zeroEnergyInverseGauge,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem zeroEnergyGauge_action (f p : ℂ) (v : SpectralVector) :
    matrixVector (zeroEnergyGauge f p) v = zeroEnergyAction f p v := by
  apply Prod.ext <;>
    simp [zeroEnergyGauge,zeroEnergyAction,matrixVector,Matrix.mulVec,dotProduct,Fin.sum_univ_two] <;> ring

/-- The explicit gauge orbit solves the actual zero-energy ODE for arbitrary Schwartz derivative data. -/
theorem zeroEnergyAction_hasDerivAt (f p : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    HasDerivAt (fun y => zeroEnergyAction (f y) (p y) v)
      (spectralKernel f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 x x
        (zeroEnergyAction (f x) (p x) v)) x := by
  have hp := ((p.hasDerivAt x).const_mul I).mul_const v.2 |>.div_const 2
  have h1 := (hasDerivAt_const x v.1).fun_sub hp
  have h2 := ((f.hasDerivAt x).fun_mul h1).fun_add (hasDerivAt_const x v.2)
  refine (h1.prodMk h2).congr_deriv ?_
  apply Prod.ext <;>
    simp [spectralKernel,spectralEntries,pairOperator,zeroEnergyAction,SchwartzMap.derivCLM_apply] <;> ring

/-- The exact transport from the prescribed initial vector at x=0. -/
def zeroEnergySolution (f p : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) : SpectralVector :=
  zeroEnergyAction (f x) (p x) (zeroEnergyInverseAction (f 0) (p 0) v)

theorem zeroEnergySolution_initial (f p : SchwartzMap ℝ ℂ) (v : SpectralVector) :
    zeroEnergySolution f p v 0 = v := zeroEnergyAction_inverse _ _ _

/-- Uniqueness identifies the explicit shear transport with the corpus's Volterra construction. -/
theorem spectralSolution_zero_derivative_data (f p : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    spectralSolution f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 v x =
      zeroEnergySolution f p v x := by
  have hs := spectralSolution_existsUnique_differential f (SchwartzMap.derivCLM ℂ ℂ p)
    (SchwartzMap.derivCLM ℂ ℂ f) 0 v
  apply congrFun (hs.unique
    ⟨spectralSolution_initial _ _ _ _ _,spectralSolution_hasDerivAt _ _ _ _ _⟩
    ⟨zeroEnergySolution_initial f p v,fun y => zeroEnergyAction_hasDerivAt f p
      (zeroEnergyInverseAction (f 0) (p 0) v) y⟩) x

/-- A closed formula for the complete fundamental matrix at zero energy. -/
theorem uniformizedFundamentalMatrix_zero_derivative_data (f p : SchwartzMap ℝ ℂ) (x : ℝ) :
    uniformizedFundamentalMatrix f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 x =
      zeroEnergyGauge (f x) (p x)*zeroEnergyInverseGauge (f 0) (p 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizedFundamentalMatrix,spectralSolution_zero_derivative_data,zeroEnergySolution,
      zeroEnergyAction,zeroEnergyInverseAction,zeroEnergyGauge,zeroEnergyInverseGauge,
      Matrix.mul_apply,Fin.sum_univ_two] <;> ring

private theorem schwartz_oriented_tendsto_zero (f : SchwartzMap ℝ ℂ) (b : Bool) :
    Tendsto (fun x : ℝ => f (if b then -x else x)) atTop (𝓝 0) := by
  cases b
  · exact f.tendsto_cocompact.mono_left atTop_le_cocompact
  · exact (f.tendsto_cocompact.mono_left atBot_le_cocompact).comp tendsto_neg_atTop_atBot

/-- Both ends of the zero-energy orbit have the same explicitly computed limit. -/
theorem uniformizedAsymptoticVector_zero_derivative_data (f p : SchwartzMap ℝ ℂ)
    (v : SpectralVector) (b : Bool) :
    uniformizedAsymptoticVector f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 v b =
      zeroEnergyInverseAction (f 0) (p 0) v := by
  have hc : Continuous (fun ab : ℂ × ℂ =>
      zeroEnergyAction ab.1 ab.2 (zeroEnergyInverseAction (f 0) (p 0) v)) := by
    unfold zeroEnergyAction
    fun_prop
  have ht := (hc.tendsto (0,0)).comp
    ((schwartz_oriented_tendsto_zero f b).prodMk_nhds (schwartz_oriented_tendsto_zero p b))
  have ho := uniformizedOrbit_tendsto f (SchwartzMap.derivCLM ℂ ℂ p)
    (SchwartzMap.derivCLM ℂ ℂ f) 0 v b
  have he : uniformizedOrbit f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 v b =
      (fun x => zeroEnergyAction (f (if b then -x else x)) (p (if b then -x else x))
        (zeroEnergyInverseAction (f 0) (p 0) v)) := by
    funext x
    simp [uniformizedOrbit,uniformizedInteractionSolution,spectralSolution_zero_derivative_data,
      zeroEnergySolution,rotatingFrame,FDNLS.staggerPhase]
  rw [he] at ho
  have hz : zeroEnergyAction 0 0 (zeroEnergyInverseAction (f 0) (p 0) v) =
      zeroEnergyInverseAction (f 0) (p 0) v := by simp [zeroEnergyAction]
  rw [hz] at ht
  exact tendsto_nhds_unique ho ht

/-- The two endpoint matrices coincide, without any smallness assumption. -/
theorem uniformizedAsymptoticMatrix_zero_derivative_data (f p : SchwartzMap ℝ ℂ) (b : Bool) :
    uniformizedAsymptoticMatrix f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 b =
      zeroEnergyInverseGauge (f 0) (p 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizedAsymptoticMatrix,uniformizedAsymptoticVector_zero_derivative_data,
      zeroEnergyInverseAction,zeroEnergyInverseGauge]
  all_goals ring

/-- Exact zero-energy transparency for every pair of Schwartz profiles (f,p). -/
theorem uniformizedScatteringMatrix_zero_derivative_data (f p : SchwartzMap ℝ ℂ) :
    uniformizedScatteringMatrix f (SchwartzMap.derivCLM ℂ ℂ p) (SchwartzMap.derivCLM ℂ ℂ f) 0 = 1 := by
  have he : uniformizedAsymptoticMatrix f (SchwartzMap.derivCLM ℂ ℂ p)
      (SchwartzMap.derivCLM ℂ ℂ f) 0 false =
      uniformizedAsymptoticMatrix f (SchwartzMap.derivCLM ℂ ℂ p)
        (SchwartzMap.derivCLM ℂ ℂ f) 0 true := by
    rw [uniformizedAsymptoticMatrix_zero_derivative_data,uniformizedAsymptoticMatrix_zero_derivative_data]
  rw [uniformizedScatteringMatrix,he]
  apply Matrix.mul_nonsing_inv
  rw [uniformizedAsymptoticMatrix_det]
  exact isUnit_one

end
end GaloisForLFunctions.HTGeometry.FokasLenells
