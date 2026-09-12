import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamJet

/-!
# The gradient-tensor stream jet

The second angular structure of the scalar–scalar `++` response: the trace-free part of
`∇S ⊗ ∇S` for the fundamental angular profile `S` (Laplace eigen-relation
`y²(S_xx + S_yy) = (s+1)(s+2) S` and its two derivatives inserted), carried by one free radial
two-jet `G` at rate `w`, in the angular block only. The angular jet of `S` is taken to third
order with `S_xxx`, `S_xxy` free; the remaining third derivatives follow from the eigen-relation.
-/

namespace RHTower.D4BMScalarStream
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation
noncomputable section

private abbrev Jet := ScalarTwoJet (Fin 4) ℂ

/-- Two-jet of `∂_x S` under the eigen-relation. -/
def gradXJet (s y Sx Sxx Sxy Sxxx Sxxy : ℂ) : Jet where
  value := Sx
  first := ![0, 0, Sxx, Sxy]
  second := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, Sxxx, Sxxy;
    0, 0, Sxxy, (s + 1) * (s + 2) * Sx / y ^ 2 - Sxxx]

/-- Two-jet of `∂_y S` under the eigen-relation. -/
def gradYJet (s y S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : Jet where
  value := Sy
  first := ![0, 0, Sxy, (s + 1) * (s + 2) * S / y ^ 2 - Sxx]
  second := !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, Sxxy, (s + 1) * (s + 2) * Sx / y ^ 2 - Sxxx;
    0, 0, (s + 1) * (s + 2) * Sx / y ^ 2 - Sxxx,
    (s + 1) * (s + 2) * Sy / y ^ 2 - 2 * (s + 1) * (s + 2) * S / y ^ 3 - Sxxy]

/-- The gradient-tensor stream metric jet: angular block `2 r² G · (∇S⊗∇S)^{tf}_{ij}`. -/
def gradientJet (w r y s G G1 G2 S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) : CoordinateMetricTwoJet 4 ℂ :=
  let R := coord r 1
  let X := gradXJet s y Sx Sxx Sxy Sxxx Sxxy
  let Y := gradYJet s y S Sx Sy Sxx Sxy Sxxx Sxxy
  let C := ((ScalarTwoJet.constant 2).mul (R.mul R)).mul (orbitJet w G G1 G2)
  let half : Jet := ScalarTwoJet.constant (1 / 2)
  let Txx := half.mul ((X.mul X).add (Y.mul Y).neg)
  let Txy := X.mul Y
  let Tyy := half.mul ((Y.mul Y).add (X.mul X).neg)
  let Z : Jet := ScalarTwoJet.constant 0
  let M := !![Z, Z, Z, Z; Z, Z, Z, Z; Z, Z, C.mul Txx, C.mul Txy; Z, Z, C.mul Txy, C.mul Tyy]
  ⟨fun i j => (M i j).value, fun k i j => (M i j).first k, fun k l i j => (M i j).second k l⟩

end
end RHTower.D4BMScalarStream
