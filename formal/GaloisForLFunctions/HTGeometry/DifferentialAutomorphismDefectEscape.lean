import GaloisForLFunctions.HTGeometry.KolchinExchangeGaugeObstruction

/-!
# Differential-automorphism defect escape

If an element is differentially algebraic over a coefficient field, then so is the defect between
the element and any coefficient-fixing differential automorphic image.  Contrapositively, a
hypertranscendental automorphism defect forces the source itself to be hypertranscendental.

This is the additive counterpart of the exchange-gauge obstruction: an automorphism cannot create
an infinite differential source by subtracting two images of one finite differential source.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DifferentialAlgEquiv

/-- A coefficient-fixing differential automorphism sends a DA source to a DA additive defect. -/
theorem differentialAlgebraicOver_sub_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (sigma : DifferentialAlgEquiv F E) {x : E}
    (hx : DifferentialAlgebraicOver F x) :
    DifferentialAlgebraicOver F (sigma.toAlgEquiv x - x) :=
  differentialAlgebraicOver_sub
    ((sigma.differentialAlgebraicOver_map_iff x).mpr hx) hx

/-- **Automorphism-defect escape law.**  A hypertranscendental additive defect under a
coefficient-fixing differential automorphism forces the original source to be
hypertranscendental. -/
theorem hypertranscendentalOver_of_sub_self
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    (sigma : DifferentialAlgEquiv F E) {x : E}
    (hdefect : HypertranscendentalOver F (sigma.toAlgEquiv x - x)) :
    HypertranscendentalOver F x := by
  intro hx
  exact hdefect (sigma.differentialAlgebraicOver_sub_self hx)

end DifferentialAlgEquiv

end

end GaloisForLFunctions.HTGeometry
