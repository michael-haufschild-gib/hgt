import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# A vanishing polynomial in the jets witnesses differential algebraicity

The bridge from a counting argument to the corpus's differential-algebraicity predicate: an
element whose jets satisfy one nonzero polynomial relation over the base is differentially
algebraic over it.  This is the interface a Siegel-type bound lands on — the bound produces a
nonzero polynomial annihilating `G, δG, δ²G, …`, and this turns that into
`DifferentialAlgebraicOver`.

* **`differentialAlgebraicOver_of_aeval_eq_zero`**.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- **One nonzero polynomial relation among the jets gives differential algebraicity.** -/
theorem differentialAlgebraicOver_of_aeval_eq_zero
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K] {x : K}
    (P : MvPolynomial (Unit × ℕ) F) (hP : P ≠ 0)
    (heval : aeval (R := F) (fun p : Unit × ℕ => differentialJet p.2 x) P = 0) :
    DifferentialAlgebraicOver F x := by
  intro hindep
  refine hP ?_
  have hzero : aeval (R := F)
        (fun p : Unit × ℕ => differentialJet p.2 ((fun _ : Unit => x) p.1)) P
      = aeval (R := F)
        (fun p : Unit × ℕ => differentialJet p.2 ((fun _ : Unit => x) p.1)) 0 := by
    simpa using heval
  exact hindep hzero

end GaloisForLFunctions
