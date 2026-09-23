import GaloisForLFunctions.HTGeometry.ComplexCoordinateDerivativeRules
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Navier-Stokes normalized cylindrical curl

This file formalizes the exact incompressibility part of Lemma 7.7 in the supplied
Navier-Stokes paper.  It defines the normalized cylindrical divergence and curl from equation
(3.11) as actual coordinate derivatives of complex fields on `ℝ³`, then proves
`div* (curl* A) = 0` away from the cylindrical axis.

The proof retains the frame terms involving `R⁻¹`: differentiating `R⁻¹` cancels the extra
radial-divergence term, and the remaining terms cancel by symmetry of second derivatives.
-/

open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry.NavierStokesCylindricalCurl

noncomputable section

open ScalarTwoJet

/-- Real normalized cylindrical coordinate space, ordered `(R, θ, Z)`. -/
abbrev Point := Fin 3 → ℝ

/-- Complex vector fields in the cylindrical frame `(eᵣ, eθ, ez)`. -/
abbrev ComplexVectorField := Point → Fin 3 → ℂ

/-- Radial coordinate as a complex-valued scalar field. -/
def radialCoordinate (x : Point) : ℂ := x 0

/-- Reciprocal radial coefficient occurring in normalized cylindrical operators. -/
def radialInverse (x : Point) : ℂ := (radialCoordinate x)⁻¹

theorem radialCoordinate_contDiff : ContDiff ℝ 2 radialCoordinate := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 3))

/-- Coordinate derivatives of the radial coordinate are the first coordinate covector. -/
theorem coordDeriv_radialCoordinate (x : Point) (i : Fin 3) :
    coordDeriv i radialCoordinate x = if i = 0 then 1 else 0 := by
  have h := Complex.ofRealCLM.hasFDerivAt.comp x
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) x)
  unfold coordDeriv
  rw [show fderiv ℝ radialCoordinate x = _ from h.fderiv]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi]

/-- The reciprocal radial coefficient is differentiable off the axis. -/
theorem radialInverse_differentiableAt {x : Point} (hx : x 0 ≠ 0) :
    DifferentiableAt ℝ radialInverse x := by
  unfold radialInverse
  exact (radialCoordinate_contDiff.differentiable (by norm_num) x).inv
    (by simpa [radialCoordinate])

/-- Only the radial derivative of `R⁻¹` is nonzero. -/
theorem coordDeriv_radialInverse {x : Point} (hx : x 0 ≠ 0) (i : Fin 3) :
    coordDeriv i radialInverse x = if i = 0 then -(radialInverse x) ^ (2 : ℕ) else 0 := by
  have hbase : ContDiffAt ℝ 2 radialCoordinate x := radialCoordinate_contDiff.contDiffAt
  have hinv := ScalarTwoJet.ofField_inv hbase (by simpa [radialCoordinate])
  have h := congrArg (fun J : ScalarTwoJet (Fin 3) ℂ => J.first i) hinv
  change coordDeriv i (fun y => (radialCoordinate y)⁻¹) x =
    -(radialCoordinate x)⁻¹ ^ (2 : ℕ) * coordDeriv i radialCoordinate x at h
  rw [coordDeriv_radialCoordinate] at h
  change coordDeriv i (fun y => (radialCoordinate y)⁻¹) x =
    if i = 0 then -((radialCoordinate x)⁻¹) ^ (2 : ℕ) else 0
  by_cases hi : i = 0
  · simpa [hi] using h
  · simpa [hi] using h

/-- Normalized cylindrical curl from equation (3.11). -/
def cylindricalCurl (A : ComplexVectorField) : ComplexVectorField := fun x i =>
  if i = 0 then
    radialInverse x * coordDeriv 1 (fun y => A y 2) x - coordDeriv 2 (fun y => A y 1) x
  else if i = 1 then
    coordDeriv 2 (fun y => A y 0) x - coordDeriv 0 (fun y => A y 2) x
  else
    coordDeriv 0 (fun y => A y 1) x + radialInverse x * A x 1 -
      radialInverse x * coordDeriv 1 (fun y => A y 0) x

/-- Normalized cylindrical divergence from equation (3.11). -/
def cylindricalDivergence (V : ComplexVectorField) (x : Point) : ℂ :=
  coordDeriv 0 (fun y => V y 0) x + radialInverse x * V x 0 +
    radialInverse x * coordDeriv 1 (fun y => V y 1) x +
      coordDeriv 2 (fun y => V y 2) x

/-- **Lemma 7.7, exact incompressibility.** The normalized cylindrical curl of every `C²`
complex vector potential is divergence-free away from the cylindrical axis. -/
theorem cylindricalDivergence_cylindricalCurl (A : ComplexVectorField) (x : Point)
    (hx : x 0 ≠ 0) (hA : ∀ i, ContDiffAt ℝ 2 (fun y => A y i) x) :
    cylindricalDivergence (cylindricalCurl A) x = 0 := by
  have hinv : DifferentiableAt ℝ radialInverse x := radialInverse_differentiableAt hx
  have hD (i j : Fin 3) :
      DifferentiableAt ℝ (coordDeriv j (fun y => A y i)) x :=
    ((coordDeriv_contDiffAt (m := 1) (hA i) (by norm_num) j).differentiableAt
      (by norm_num))
  have h0 (i : Fin 3) : DifferentiableAt ℝ (fun y => A y i) x :=
    (hA i).differentiableAt (by norm_num)
  have hcurlR :
      coordDeriv 0 (fun y => cylindricalCurl A y 0) x =
        coordDeriv 0 radialInverse x * coordDeriv 1 (fun y => A y 2) x +
          radialInverse x * coordDeriv 0 (coordDeriv 1 (fun y => A y 2)) x -
            coordDeriv 0 (coordDeriv 2 (fun y => A y 1)) x := by
    change coordDeriv 0 (fun y =>
      radialInverse y * coordDeriv 1 (fun z => A z 2) y -
        coordDeriv 2 (fun z => A z 1) y) x = _
    calc
      _ = coordDeriv 0 (fun y => radialInverse y * coordDeriv 1 (fun z => A z 2) y) x -
          coordDeriv 0 (coordDeriv 2 (fun z => A z 1)) x :=
        coordDeriv_sub (hinv.mul (hD 2 1)) (hD 1 2) 0
      _ = _ := by rw [coordDeriv_mul hinv (hD 2 1)]
  have hcurlTheta :
      coordDeriv 1 (fun y => cylindricalCurl A y 1) x =
        coordDeriv 1 (coordDeriv 2 (fun y => A y 0)) x -
          coordDeriv 1 (coordDeriv 0 (fun y => A y 2)) x := by
    change coordDeriv 1 (fun y =>
      coordDeriv 2 (fun z => A z 0) y - coordDeriv 0 (fun z => A z 2) y) x = _
    rw [coordDeriv_sub (hD 0 2) (hD 2 0)]
  have hcurlZ :
      coordDeriv 2 (fun y => cylindricalCurl A y 2) x =
        coordDeriv 2 (coordDeriv 0 (fun y => A y 1)) x +
          (coordDeriv 2 radialInverse x * A x 1 +
            radialInverse x * coordDeriv 2 (fun y => A y 1) x) -
          (coordDeriv 2 radialInverse x * coordDeriv 1 (fun y => A y 0) x +
            radialInverse x * coordDeriv 2 (coordDeriv 1 (fun y => A y 0)) x) := by
    have hpA : coordDeriv 2 (fun y => radialInverse y * A y 1) x =
        coordDeriv 2 radialInverse x * A x 1 +
          radialInverse x * coordDeriv 2 (fun y => A y 1) x :=
      coordDeriv_mul hinv (h0 1) 2
    have hpD : coordDeriv 2
        (fun y => radialInverse y * coordDeriv 1 (fun z => A z 0) y) x =
        coordDeriv 2 radialInverse x * coordDeriv 1 (fun y => A y 0) x +
          radialInverse x * coordDeriv 2 (coordDeriv 1 (fun y => A y 0)) x :=
      coordDeriv_mul hinv (hD 0 1) 2
    have hsum : coordDeriv 2 (fun y =>
        coordDeriv 0 (fun z => A z 1) y + radialInverse y * A y 1) x =
        coordDeriv 2 (coordDeriv 0 (fun y => A y 1)) x +
          coordDeriv 2 (fun y => radialInverse y * A y 1) x :=
      coordDeriv_add (hD 1 0) (hinv.mul (h0 1)) 2
    have hsub : coordDeriv 2 (fun y =>
        (coordDeriv 0 (fun z => A z 1) y + radialInverse y * A y 1) -
          radialInverse y * coordDeriv 1 (fun z => A z 0) y) x =
        coordDeriv 2 (fun y =>
          coordDeriv 0 (fun z => A z 1) y + radialInverse y * A y 1) x -
        coordDeriv 2
          (fun y => radialInverse y * coordDeriv 1 (fun z => A z 0) y) x :=
      coordDeriv_sub ((hD 1 0).add (hinv.mul (h0 1))) (hinv.mul (hD 0 1)) 2
    change coordDeriv 2 (fun y =>
      coordDeriv 0 (fun z => A z 1) y + radialInverse y * A y 1 -
        radialInverse y * coordDeriv 1 (fun z => A z 0) y) x = _
    calc
      _ = coordDeriv 2 (fun y =>
            coordDeriv 0 (fun z => A z 1) y + radialInverse y * A y 1) x -
          coordDeriv 2 (fun y => radialInverse y * coordDeriv 1 (fun z => A z 0) y) x := hsub
      _ = _ := by rw [hsum, hpA, hpD]
  rw [cylindricalDivergence, hcurlR, hcurlTheta, hcurlZ,
    coordDeriv_radialInverse hx, coordDeriv_radialInverse hx]
  norm_num [cylindricalCurl]
  simp only [show (2 : Fin 3) ≠ 0 by decide, if_false]
  rw [coordDeriv_comm (hA 2) 0 1, coordDeriv_comm (hA 1) 0 2,
    coordDeriv_comm (hA 0) 1 2]
  ring

end

end GaloisForLFunctions.HTGeometry.NavierStokesCylindricalCurl
