import GaloisForLFunctions.LatticeSectionTheory.HeckeCorrespondencesAreSimilitudesOfThePrimitiveH1
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# Over finite fields the Stepanov count pays the primitive `h¹`

The open core of the programme is the primitive `h¹ = ½δ` as a count. Over a function field it is
one: for the curve `y² = f(x)` over a finite field `F` of odd characteristic (`f` squarefree of odd
degree, every genus), unitarity of the curve datum is proved by counting — Stepanov's auxiliary
sections and the Gauss-sum modulus `|τ|² = q` (AET `hyperellipticDatum_unitary`). In the language
of sections:

* **Künneth effectivity on every Frobenius window** (`hyperelliptic_kunneth_effectivity`): the
  Künneth count satisfies the Riemann inequality and is bounded on degree levels.
* **The primitive `h¹` is nonnegative** (`hyperelliptic_primitiveH1_nonneg`) on every class of
  every window: the Castelnuovo–Severi defect is half a count-certified quantity.

So the function-field version of the open core is solved, and solved by counts; the missing piece
over `ℤ` is the analogue of Stepanov's auxiliary sections on the scaling surface.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.LatticeSectionTheory

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory

variable {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
  (hodd : Odd f.natDegree)

/-- The Hodge index on every Frobenius window of `y² = f(x)`, from Stepanov's count. -/
theorem hyperelliptic_window_hodgeIndex (W : Finset ℕ) :
    ((hyperellipticDatum hF hsq hodd).windowSurface W).HodgeIndex :=
  (hyperellipticDatum hF hsq hodd).windowSurface_hodgeIndex_iff_unitary.mpr
    (hyperellipticDatum_unitary hF hsq hodd) W

/-- **Künneth effectivity on actual curves**: on every Frobenius window of `y² = f(x)` the Künneth
count satisfies the Riemann inequality and is bounded on degree levels. -/
theorem hyperelliptic_kunneth_effectivity (W : Finset ℕ) :
    RiemannInequality ((hyperellipticDatum hF hsq hodd).windowSurface W) 0 0
        (kunnethH0 ((hyperellipticDatum hF hsq hodd).windowSurface W)) ∧
      DegreeBounded ((hyperellipticDatum hF hsq hodd).windowSurface W)
        (kunnethH0 ((hyperellipticDatum hF hsq hodd).windowSurface W)) :=
  (kunneth_effectivity_iff _).mpr (hyperelliptic_window_hodgeIndex hF hsq hodd W)

/-- **The primitive `h¹` of an actual curve is nonnegative**, on every class of every Frobenius
window. -/
theorem hyperelliptic_primitiveH1_nonneg (W : Finset ℕ) (x : SpanCycle) :
    0 ≤ primitiveH1 ((hyperellipticDatum hF hsq hodd).windowSurface W) x := by
  set S := (hyperellipticDatum hF hsq hodd).windowSurface W
  have h := S.castelnuovoSeveri_iff_defect_nonneg.mp
    (S.hodgeIndex_iff_castelnuovoSeveri.mp (hyperelliptic_window_hodgeIndex hF hsq hodd W)) x
  rw [primitiveH1_eq]
  linarith

end GaloisForLFunctions.LatticeSectionTheory
