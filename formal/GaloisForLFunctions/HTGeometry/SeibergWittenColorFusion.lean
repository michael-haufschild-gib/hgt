import GaloisForLFunctions.HTGeometry.ColorGramNullFusion
import GaloisForLFunctions.HTGeometry.SeibergWittenColorGramBridge

/-!
# Fusion of finite Seiberg--Witten curvature records

The two closed gauge-inequivalent Higgs vacua from the finite Seiberg--Witten skeleton give two
future-null colour Gram records.  Placing their conjugate spinor rows in two distinct colour
channels adds those curvature records.  The result is strictly timelike, so it cannot equal the
quadratic curvature `q(ψ)` of any single two-spinor, whose determinant always vanishes.

This is an exact finite record statement, not a nonlinear superposition principle for solutions of
the continuum Seiberg--Witten equations.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Two-colour aggregate of the two closed finite Seiberg--Witten vacuum records. -/
def seibergWittenVacuumFusionEvent : ColorEventMatrix :=
  twoNullRootEvent (star abelianHiggsSpinorVacuum)
    (star abelianHiggsSpinorOrthogonalVacuum)

/-- Its Gram matrix is exactly the sum of the two finite Seiberg--Witten curvatures. -/
theorem seibergWittenVacuumFusionEvent_gram :
    colorGramMatrix seibergWittenVacuumFusionEvent =
      seibergWittenQuadraticMap abelianHiggsSpinorVacuum +
        seibergWittenQuadraticMap abelianHiggsSpinorOrthogonalVacuum := by
  rw [seibergWittenVacuumFusionEvent, twoNullRootEvent_gram_eq_add]
  change
    colorGramMatrix (seibergWittenColorEvent abelianHiggsSpinorVacuum) +
        colorGramMatrix (seibergWittenColorEvent abelianHiggsSpinorOrthogonalVacuum) =
      seibergWittenQuadraticMap abelianHiggsSpinorVacuum +
        seibergWittenQuadraticMap abelianHiggsSpinorOrthogonalVacuum
  rw [← seibergWittenQuadraticMap_eq_colorGram,
    ← seibergWittenQuadraticMap_eq_colorGram]

/-- The aggregate has strictly positive Lorentz mass squared. -/
theorem seibergWittenVacuumFusion_lorentzMassSq_pos :
    0 < colorGramLorentzMassSq seibergWittenVacuumFusionEvent := by
  apply twoNullRootEvent_lorentzMassSq_pos
  norm_num [abelianHiggsSpinorVacuum, abelianHiggsSpinorOrthogonalVacuum]

/-- The fused Gram record has nonzero determinant. -/
theorem seibergWittenVacuumFusion_det_ne_zero :
    (colorGramMatrix seibergWittenVacuumFusionEvent).det ≠ 0 := by
  rw [colorGramMatrix_det]
  exact_mod_cast ne_of_gt seibergWittenVacuumFusion_lorentzMassSq_pos

/-- No single finite Seiberg--Witten spinor has the fused two-colour curvature record. -/
theorem seibergWittenVacuumFusion_ne_quadraticMap (psi : SeibergWittenSpinor) :
    colorGramMatrix seibergWittenVacuumFusionEvent ≠ seibergWittenQuadraticMap psi := by
  intro h
  apply seibergWittenVacuumFusion_det_ne_zero
  rw [h]
  exact higgsSpinorEventMatrix_det psi

end GaloisForLFunctions.HTGeometry
