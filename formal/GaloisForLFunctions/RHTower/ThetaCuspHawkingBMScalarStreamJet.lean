import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarJetQuadraticEinstein
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamSimpSets

/-!
# The scalar-stream metric jet

A scalar-type second-order metric ansatz on the Birmingham–Mokhtari background in the
Kodama–Ishibashi gauge: an orbit block `f_ab Ψ` with three free radial two-jets at a fixed time
rate `w`, no mixed components, and an angular block `2 r² H Ψ γ_ij` with a fourth free radial
two-jet, all multiplied by one free angular two-jet `Ψ`. No angular eigen-equation and no radial
field equation is imposed; the linearized Einstein operator on this jet is the scalar analogue of
the vector master curl and is the object the scalar–scalar `++` source is matched against.
-/

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section

private abbrev Jet := ScalarTwoJet (Fin 4) ℂ

/-- Time-separated radial two-jet at rate `w` with free radial derivatives. -/
def orbitJet (w F F1 F2 : ℂ) : Jet where
  value := F
  first := ![w * F, F1, 0, 0]
  second := !![w ^ (2 : ℕ) * F, w * F1, 0, 0; w * F1, F2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

/-- Free angular two-jet. -/
def angularJet (P Px Py Pxx Pxy Pyy : ℂ) : Jet where
  value := P
  first := ![0, 0, Px, Py]
  second := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, Pxx, Pxy; 0, 0, Pxy, Pyy]

/-- The Kodama–Ishibashi-gauge scalar-stream metric jet. -/
def metricJet (w r y F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 P Px Py Pxx Pxy Pyy : ℂ) :
    CoordinateMetricTwoJet 4 ℂ :=
  let R := coord r 1
  let Y := coord y 3
  let A := angularJet P Px Py Pxx Pxy Pyy
  let O0 := (orbitJet w F0 F01 F02).mul A
  let O1 := (orbitJet w F1 F11 F12).mul A
  let O2 := (orbitJet w F2 F21 F22).mul A
  let L := ((((ScalarTwoJet.constant 2).mul (R.mul R)).mul (Y.inv.mul Y.inv)).mul
    (orbitJet w H H1 H2)).mul A
  let Z : Jet := ScalarTwoJet.constant 0
  let M := !![O0, O1, Z, Z; O1, O2, Z, Z; Z, Z, L, Z; Z, Z, Z, L]
  ⟨fun i j => (M i j).value, fun k i j => (M i j).first k, fun k l i j => (M i j).second k l⟩

end
end RHTower.D4BMScalarStream
