import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamRadialProfiles
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalScalarMetric

/-! Actual smooth radial fields realizing both stream profile jets. -/

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMVectorStream D4BMScalarLinearEquation D4BMFundamentalScalarMetric
noncomputable section

/-- The original two radial factors as actual time-dependent fields. -/
def streamRadialField (w a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  let E := envelope w a x
  let U := (x 1 : ℂ)⁻¹
  if square then E*(U*U) else E

/-- The explicit first radial derivative as an actual field. -/
def streamRadialDerivative (w a : ℂ) (square : Bool) (x : Fin 4 → ℝ) : ℂ :=
  let E := envelope w a x
  let R := (x 1 : ℂ)
  let U := R⁻¹
  let F := R*R+(-1)
  let D := (w*E)*(U*F⁻¹)
  if square then D*(U*U)+((-2)*E)*(U*(U*U)) else D

private theorem radial_domain (p : D4BMBackground.ExteriorPoint) :
    (p.val 1 : ℂ) ≠ 0 ∧ (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
  constructor
  · exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  · exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)

/-- Both original radial fields and their displayed derivatives have every local smoothness order. -/
theorem streamRadialFields_smooth (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint)
    (m : WithTop ℕ∞) : ContDiffAt ℝ m (streamRadialField w a square) p.val ∧
      ContDiffAt ℝ m (streamRadialDerivative w a square) p.val := by
  have hE := envelope_contDiffAt w a p m
  have hR : ContDiffAt ℝ m (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hU := hR.inv (radial_domain p).1
  have hF : ContDiffAt ℝ m (fun x : Fin 4 → ℝ => (x 1 : ℂ)*(x 1 : ℂ)+(-1)) p.val :=
    (hR.mul hR).add contDiffAt_const
  have hF0 : (p.val 1 : ℂ)*(p.val 1 : ℂ)+(-1) ≠ 0 := by
    simpa only [← pow_two,← sub_eq_add_neg] using (radial_domain p).2
  have hD := ((contDiffAt_const (c := w)).mul hE).mul (hU.mul (hF.inv hF0))
  cases square
  · exact ⟨hE,hD⟩
  · exact ⟨hE.mul (hU.mul hU), (hD.mul (hU.mul hU)).add
      (((contDiffAt_const (c := (-2 : ℂ))).mul hE).mul (hU.mul (hU.mul hU)))⟩

private theorem actual_product_jets (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ofField (streamRadialField w a square) p.val =
      streamRadialProductJet w (p.val 1) (envelope w a p.val) square ∧
    ofField (streamRadialDerivative w a square) p.val =
      streamRadialDerivativeJet w (p.val 1) (envelope w a p.val) square := by
  let R := fun x : Fin 4 → ℝ => (x 1 : ℂ)
  let E := envelope w a
  let U := fun x => (R x)⁻¹
  let F := fun x => R x*R x+(-1)
  let D := fun x => (w*E x)*(U x*(F x)⁻¹)
  have hE : ContDiffAt ℝ 2 E p.val := envelope_contDiffAt w a p 2
  have hR : ContDiffAt ℝ 2 R p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  have hU : ContDiffAt ℝ 2 U p.val := hR.inv (radial_domain p).1
  have hF : ContDiffAt ℝ 2 F p.val := (hR.mul hR).add contDiffAt_const
  have hF0 : F p.val ≠ 0 := by
    simpa only [F,R,← pow_two,← sub_eq_add_neg] using (radial_domain p).2
  have hFi : ContDiffAt ℝ 2 (fun x => (F x)⁻¹) p.val := hF.inv hF0
  have hD : ContDiffAt ℝ 2 D p.val := (contDiffAt_const.mul hE).mul (hU.mul (hF.inv hF0))
  have hjE : ofField E p.val = temporalRadial w (p.val 1) (E p.val) := envelope_jet w a p
  have hjR : ofField R p.val = coord (p.val 1) 1 := coordinate_jet p.val 1
  have hjU : ofField U p.val = (coord (p.val 1) 1).inv := by
    rw [ofField_inv hR (radial_domain p).1,hjR]
  have hjF : ofField F p.val = ((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1)) := by
    rw [ofField_add (hR.mul hR) contDiffAt_const,ofField_mul hR hR,ofField_constant,hjR]
  have hjD : ofField D p.val =
      ((constant w).mul (temporalRadial w (p.val 1) (E p.val))).mul
        ((coord (p.val 1) 1).inv.mul
          (((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1))).inv) := by
    dsimp only [D]
    rw [ofField_mul ((contDiffAt_const (c := w)).mul hE) (hU.mul hFi),
      ofField_mul (contDiffAt_const (c := w)) hE,ofField_constant,ofField_mul hU hFi,
      ofField_inv hF hF0,hjE,hjU,hjF]
  cases square
  · exact ⟨hjE,hjD⟩
  · constructor
    · change ofField (fun x => E x*(U x*U x)) p.val = _
      rw [ofField_mul hE (hU.mul hU),ofField_mul hU hU,hjE,hjU]
      rfl
    · change ofField (fun x => D x*(U x*U x)+((-2)*E x)*(U x*(U x*U x))) p.val = _
      rw [ofField_add (hD.mul (hU.mul hU)) (((contDiffAt_const (c := (-2 : ℂ))).mul hE).mul (hU.mul (hU.mul hU))),
        ofField_mul hD (hU.mul hU),ofField_mul ((contDiffAt_const (c := (-2 : ℂ))).mul hE) (hU.mul (hU.mul hU)),
        ofField_mul (contDiffAt_const (c := (-2 : ℂ))) hE,ofField_constant,ofField_mul hU (hU.mul hU),
        ofField_mul hU hU,hjE,hjU,hjD]
      rfl

/-- The radial-factor table is the actual complete second coordinate jet. -/
theorem streamRadialField_jet (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ofField (streamRadialField w a square) p.val =
      radialJet w (streamRadialValue w (p.val 1) (envelope w a p.val) square)
        (streamRadialFirst w (p.val 1) (envelope w a p.val) square)
        (streamRadialSecond w (p.val 1) (envelope w a p.val) square) := by
  rw [(actual_product_jets w a square p).1,
    streamRadialProductJet_eq _ _ _ _ (radial_domain p).1 (radial_domain p).2]

/-- The derivative-field table is its actual complete jet, including the original third radial derivative. -/
theorem streamRadialDerivative_jet (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    ofField (streamRadialDerivative w a square) p.val =
      radialJet w (streamRadialFirst w (p.val 1) (envelope w a p.val) square)
        (streamRadialSecond w (p.val 1) (envelope w a p.val) square)
        (streamRadialThird w (p.val 1) (envelope w a p.val) square) := by
  rw [(actual_product_jets w a square p).2,
    streamRadialDerivativeJet_eq _ _ _ _ (radial_domain p).1 (radial_domain p).2]

/-- The field used by the metric reconstruction is the actual radial derivative, not an independent slot. -/
theorem streamRadialDerivative_actual (w a : ℂ) (square : Bool) (p : D4BMBackground.ExteriorPoint) :
    streamRadialDerivative w a square p.val = coordDeriv 1 (streamRadialField w a square) p.val := by
  have hv := congrArg (fun j => j.value) (streamRadialDerivative_jet w a square p)
  have hd := congrArg (fun j => j.first 1) (streamRadialField_jet w a square p)
  exact hv.trans hd.symm

/-- The doubled envelope is exactly the square of the original amplitude and time-radial factor. -/
theorem envelope_double (s a : ℂ) (x : Fin 4 → ℝ) :
    envelope (2*s) (a^(2 : ℕ)) x = envelope s a x^(2 : ℕ) := by
  simp only [envelope_eq_exp,mul_pow]
  congr 1
  rw [pow_two,← Complex.exp_add]
  congr 1
  ring

end
end RHTower.D4BMModularCore
