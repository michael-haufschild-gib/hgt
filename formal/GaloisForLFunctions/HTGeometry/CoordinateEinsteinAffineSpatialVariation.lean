import GaloisForLFunctions.HTGeometry.CoordinateEinsteinQuadraticSpatialDerivative

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet
open Filter Topology
noncomputable section
variable {d : ℕ}
local notation "Space" => ComplexMetricTwoJetSpace d

/-- Affine amplitude path through the original complete metric jet. -/
def amplitudeJet (q p : Space) (z : ℂ) : Space := q+z • p

/-- Actual spatial first variation along the affine amplitude path.
The spatial jet derivative varies with amplitude as well. -/
def affineSpatialEinstein (q p qx px : Space) (i j : Fin d) (z : ℂ) : ℂ :=
  fderiv ℂ (einsteinComponent i j) (amplitudeJet q p z) (amplitudeJet qx px z)

/-- Full first amplitude derivative of the spatial first variation. -/
def affineSpatialSlope (q p qx px : Space) (i j : Fin d) (z : ℂ) : ℂ :=
  secondVariation (amplitudeJet q p z) i j p (amplitudeJet qx px z)+
    fderiv ℂ (einsteinComponent i j) (amplitudeJet q p z) px

theorem amplitudeJet_hasDerivAt (q p : Space) (z : ℂ) :
    HasDerivAt (amplitudeJet q p) p z := by
  convert! ((hasDerivAt_id z).smul_const p).const_add q using 1
  simp

/-- Both amplitude-varying jet factors are differentiated. -/
theorem affineSpatialEinstein_hasDerivAt (q p qx px : Space) (i j : Fin d) (z : ℂ)
    (hdet : Matrix.det (amplitudeJet q p z).1 ≠ 0) :
    HasDerivAt (affineSpatialEinstein q p qx px i j)
      (affineSpatialSlope q p qx px i j z) z := by
  have hA := (contDiffAt_einsteinComponent (n := 3) (amplitudeJet q p z) hdet i j).fderiv_right
    (m := 2) (by norm_num)
  have hD := (hA.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z
    (amplitudeJet_hasDerivAt q p z)
  convert! hD.clm_apply (amplitudeJet_hasDerivAt qx px z) using 1

/-- Second amplitude derivative retains both identical mixed terms. -/
theorem affineSpatialSlope_hasDerivAt (q p qx px : Space) (i j : Fin d) (z : ℂ)
    (hdet : Matrix.det (amplitudeJet q p z).1 ≠ 0) :
    HasDerivAt (affineSpatialSlope q p qx px i j)
      (thirdVariation (amplitudeJet q p z) i j p p (amplitudeJet qx px z)+
        2*secondVariation (amplitudeJet q p z) i j p px) z := by
  have hA := contDiffAt_einsteinComponent (n := 3) (amplitudeJet q p z) hdet i j
  have hD := ((hA.fderiv_right (m := 2) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt z (amplitudeJet_hasDerivAt q p z)
  have hH := (((hA.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z
      (amplitudeJet_hasDerivAt q p z)
  have h1 := (hH.clm_apply (hasDerivAt_const z p)).clm_apply (amplitudeJet_hasDerivAt qx px z)
  have h2 := hD.clm_apply (hasDerivAt_const z px)
  convert! h1.add h2 using 1
  simp only [secondVariation,thirdVariation,Function.comp_def,map_zero,add_zero]
  ring

/-- The amplitude second derivative of the original spatial Einstein variation. -/
theorem affineSpatialEinstein_second (q p qx px : Space) (i j : Fin d)
    (hdet : Matrix.det q.1 ≠ 0) :
    deriv (deriv (affineSpatialEinstein q p qx px i j)) 0 =
      thirdVariation q i j p p qx+2*secondVariation q i j p px := by
  have hc : Continuous (fun z => Matrix.det (amplitudeJet q p z).1) := by
    simp only [Matrix.det_apply',amplitudeJet,Prod.fst_add]
    fun_prop
  have hd : Matrix.det (amplitudeJet q p 0).1 ≠ 0 := by
    simpa [amplitudeJet] using hdet
  have he : deriv (affineSpatialEinstein q p qx px i j) =ᶠ[𝓝 0]
      affineSpatialSlope q p qx px i j := by
    filter_upwards [hc.continuousAt.eventually_ne hd] with z hz
    exact (affineSpatialEinstein_hasDerivAt q p qx px i j z hz).deriv
  rw [he.deriv_eq,(affineSpatialSlope_hasDerivAt q p qx px i j 0 hd).deriv]
  simp [amplitudeJet]

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet
