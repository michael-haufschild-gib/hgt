import GaloisForLFunctions.HTGeometry.FokasLenellsSpectralVolterra

/-!
# Original Fokas–Lenells eigenfunctions and determinant conservation

The inverse of the gauge in equation (2.6) of Yan–Zhang–Zhu,
arXiv:2607.19649v1, transports the constructed Volterra eigenfunction to
the original spatial Lax equation (1.8). Exponential spectral parameters
discharge every denominator condition. Initial vectors are arbitrary and
the potential is an arbitrary Schwartz function.

Actual derivatives verify both scalar components of the system. Their
Wronskian is constant, and the canonical fundamental matrix has determinant
one, realizing the mechanism of equation (2.61) with normalization at zero.
Jost asymptotics and the nonlinear inverse-scattering problem are separate.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


def matrixVector (A : Matrix (Fin 2) (Fin 2) ℂ) (v : SpectralVector) : SpectralVector :=
  ((A *ᵥ ![v.1,v.2]) 0, (A *ᵥ ![v.1,v.2]) 1)

def gaugeVector (u k : ℂ) (v : SpectralVector) : SpectralVector :=
  (v.1, u*v.1-2*k*v.2)

def inverseGaugeVector (u k : ℂ) (v : SpectralVector) : SpectralVector :=
  (v.1, (u*v.1-v.2)/(2*k))

theorem inverseGaugeVector_gauge_exp (u a : ℂ) (v : SpectralVector) :
    inverseGaugeVector u (Complex.exp a) (gaugeVector u (Complex.exp a) v) = v := by
  apply Prod.ext
  · rfl
  · simp [inverseGaugeVector,gaugeVector]

/-- The differentiated inverse gauge sends the uniformized ODE back to the original one. -/
theorem inverseGaugeVector_derivative (u v w a : ℂ) (ψ : SpectralVector) :
    (let d := matrixVector (uniformizedLax u v w ((Complex.exp a)^2)) ψ
     (d.1, (w*ψ.1+u*d.1-d.2)/(2*Complex.exp a))) =
      matrixVector (spatialLax u v (Complex.exp a))
        (inverseGaugeVector u (Complex.exp a) ψ) := by
  apply Prod.ext <;>
    simp [matrixVector, uniformizedLax, effectivePotential, spatialLax,
      inverseGaugeVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf

/-- An eigenfunction of the original x-Lax operator, normalized by arbitrary initial data. -/
def spatialEigenfunction (q : SchwartzMap ℝ ℂ) (a : ℂ) (v : SpectralVector)
    (x : ℝ) : SpectralVector :=
  inverseGaugeVector (deriv q x) (Complex.exp a)
    (initialSpectralSolution q ((Complex.exp a)^2)
      (gaugeVector (deriv q 0) (Complex.exp a) v) x)

theorem spatialEigenfunction_initial (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) : spatialEigenfunction q a v 0 = v := by
  rw [spatialEigenfunction, initialSpectralSolution_initial, inverseGaugeVector_gauge_exp]

/-- Global solutions of the spatial part of equation (1.8), with the actual reflected derivative and no
regularity or nonvanishing side hypotheses. -/
theorem spatialEigenfunction_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (spatialEigenfunction q a v)
      (matrixVector (spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x)
        (Complex.exp a)) (spatialEigenfunction q a v x)) x := by
  let ψ := initialSpectralSolution q ((Complex.exp a)^2)
    (gaugeVector (deriv q 0) (Complex.exp a) v)
  let d := matrixVector
    (uniformizedLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x)
      (deriv (deriv q) x) ((Complex.exp a)^2)) (ψ x)
  have hd : HasDerivAt ψ d x := initialSpectralSolution_hasDerivAt q _ _ x
  have hd1 : HasDerivAt (fun y => (ψ y).1) d.1 x :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hd
  have hd2 : HasDerivAt (fun y => (ψ y).2) d.2 x :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hd
  have hq : HasDerivAt (deriv q) (deriv (deriv q) x) x := by
    have heq : (SchwartzMap.derivCLM ℂ ℂ q : ℝ → ℂ) = deriv q := by
      funext y
      exact SchwartzMap.derivCLM_apply ℂ q y
    rw [← heq]
    exact (SchwartzMap.derivCLM ℂ ℂ q).hasDerivAt x
  have h := hd1.prodMk (((hq.mul hd1).sub hd2).div_const (2*Complex.exp a))
  exact h.congr_deriv (inverseGaugeVector_derivative (deriv q x)
    (deriv (fun y : ℝ => q (-y)) x) (deriv (deriv q) x) a (ψ x))

theorem spatialEigenfunction_continuous (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) : Continuous (spatialEigenfunction q a v) :=
  (show Differentiable ℝ (spatialEigenfunction q a v) from
    fun x => (spatialEigenfunction_hasDerivAt q a v x).differentiableAt).continuous

theorem spatialEigenfunction_first_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (fun y => (spatialEigenfunction q a v y).1)
      (I*(Complex.exp a)^2*(spatialEigenfunction q a v x).1 +
        I*Complex.exp a*deriv (fun y : ℝ => q (-y)) x*(spatialEigenfunction q a v x).2) x := by
  refine ((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
    (spatialEigenfunction_hasDerivAt q a v x)).congr_deriv ?_
  simp [matrixVector, spatialLax, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem spatialEigenfunction_second_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (fun y => (spatialEigenfunction q a v y).2)
      (I*Complex.exp a*deriv q x*(spatialEigenfunction q a v x).1 -
        I*(Complex.exp a)^2*(spatialEigenfunction q a v x).2) x := by
  refine ((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x
    (spatialEigenfunction_hasDerivAt q a v x)).congr_deriv ?_
  simp [matrixVector, spatialLax, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

def spatialWedge (q : SchwartzMap ℝ ℂ) (a : ℂ) (v w : SpectralVector) (x : ℝ) : ℂ :=
  (spatialEigenfunction q a v x).1*(spatialEigenfunction q a w x).2 -
    (spatialEigenfunction q a v x).2*(spatialEigenfunction q a w x).1

/-- Traceless Lax evolution preserves the determinant pairing. -/
theorem spatialWedge_hasDerivAt_zero (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v w : SpectralVector) (x : ℝ) : HasDerivAt (spatialWedge q a v w) 0 x := by
  refine (((spatialEigenfunction_first_hasDerivAt q a v x).mul
    (spatialEigenfunction_second_hasDerivAt q a w x)).sub
    ((spatialEigenfunction_second_hasDerivAt q a v x).mul
    (spatialEigenfunction_first_hasDerivAt q a w x))).congr_deriv ?_
  ring

theorem spatialWedge_constant (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (v w : SpectralVector) (x : ℝ) : spatialWedge q a v w x = v.1*w.2-v.2*w.1 := by
  have h := is_const_of_deriv_eq_zero
    (fun y => (spatialWedge_hasDerivAt_zero q a v w y).differentiableAt)
    (fun y => (spatialWedge_hasDerivAt_zero q a v w y).deriv) x 0
  simpa only [spatialWedge, spatialEigenfunction_initial] using h

def spatialFundamentalMatrix (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(spatialEigenfunction q a (1,0) x).1, (spatialEigenfunction q a (0,1) x).1;
     (spatialEigenfunction q a (1,0) x).2, (spatialEigenfunction q a (0,1) x).2]

/-- The determinant-one property used in Section 2.2 holds for the constructed
fundamental matrix at every real position. -/
theorem spatialFundamentalMatrix_det (q : SchwartzMap ℝ ℂ) (a : ℂ) (x : ℝ) :
    (spatialFundamentalMatrix q a x).det = 1 := by
  have h := spatialWedge_constant q a (1,0) (0,1) x
  simpa [spatialFundamentalMatrix, Matrix.det_fin_two, spatialWedge, mul_comm] using h

end
end GaloisForLFunctions.HTGeometry.FokasLenells
