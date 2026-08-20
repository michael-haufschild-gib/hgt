import GaloisForLFunctions.RHTower.XiReciprocalCliffordSquare

namespace RHTower

/-- Terminal audit for the reciprocal-Xi Clifford route: a bare splitting is equivalent to RH,
so an unconditional source construction would itself prove RH. -/
theorem superPoincareXiCliffordEndpoint_iff_riemannHypothesis :
    XiReciprocalCliffordPolarization ↔ RiemannHypothesis :=
  xiReciprocalCliffordPolarization_iff_riemannHypothesis

end RHTower
