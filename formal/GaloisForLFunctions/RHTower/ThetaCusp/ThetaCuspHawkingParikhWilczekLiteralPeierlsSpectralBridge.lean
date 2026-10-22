import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# Literal Peierls spectral bridge and bare Borel-coefficient obstruction

The literal two-branch cyclic Peierls source has physical rates

`r₊ = q - 2`, `r₋ = -q - 1`.

The physical damping shift therefore gives the exact functional-equation pair

`(r₊ + 2, r₋ + 2) = (q, 1-q)`

at every actual `XiZeroCopy`, and transports every Parikh--Wilczek Borel recoil edge to its
literal source branch. This closes the spectral-coordinate part of the desired CTP-to-PW bridge.

The same source also exposes a sharp obstruction. Its bare metric square numerator is
`r₊(r₊-1)=(q-2)(q-3)`. It cannot equal the natural-grade PW edge
`(q+2k)(q+2k+1)` at any `k : Nat`: equality forces `Im q = 0`, excluded on the Xi divisor.
Thus the raw metric coefficient cannot be silently reidentified as the PW Borel recurrence.

Proof-chain role:
`literal Peierls CTP branches -> exact q/(1-q) PW spectral pairing -> ordered contact coefficient
transmutation -> fixed-grade partner balance -> Xi occurrence -> RH`. The spectral pairing is
now source-derived. The remaining contact law must change the displayed coefficient defect; a
bare metric/source identification is retired.

`[NEW] [PW-B SOURCE BRIDGE] [PW-B ROUTE-CLASS NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- PW spectral coordinate carried by the forward literal Peierls branch after its physical
damping shift. -/
def d4BMPeierlsFunctionalEquationCoordinate (q : XiZeroCopy) : ℂ :=
  D4BMModularCore.physicalRate q true + 2

/-- Both shifted literal source branches. -/
def d4BMPeierlsFunctionalEquationPair (q : XiZeroCopy) : ℂ × ℂ :=
  (D4BMModularCore.physicalRate q true + 2,
    D4BMModularCore.physicalRate q false + 2)

/-- The forward source branch recovers the literal Xi coordinate exactly. -/
theorem d4BMPeierlsFunctionalEquationCoordinate_eq_xi (q : XiZeroCopy) :
    d4BMPeierlsFunctionalEquationCoordinate q = (q.1 : ℂ) := by
  simp [d4BMPeierlsFunctionalEquationCoordinate, D4BMModularCore.physicalRate]

/-- The reverse physical branch is the functional-equation partner of the shifted forward branch. -/
theorem d4BMPeierlsFunctionalEquationPartner_eq
    (q : XiZeroCopy) :
    D4BMModularCore.physicalRate q false + 2 =
      1 - d4BMPeierlsFunctionalEquationCoordinate q := by
  simp [d4BMPeierlsFunctionalEquationCoordinate, D4BMModularCore.physicalRate]
  ring

/-- **Literal source spectral bridge.** Damping-shifted Peierls branches are exactly the
functional-equation pair of the actual Xi coordinate. -/
theorem d4BMPeierlsFunctionalEquationPair_eq_xi_reflected
    (q : XiZeroCopy) :
    d4BMPeierlsFunctionalEquationPair q = ((q.1 : ℂ), 1 - (q.1 : ℂ)) := by
  apply Prod.ext
  · simp [d4BMPeierlsFunctionalEquationPair, D4BMModularCore.physicalRate]
  · simp [d4BMPeierlsFunctionalEquationPair, D4BMModularCore.physicalRate]
    ring

/-- Every PW recoil grade consequently has a literal source pair with its exact functional-
equation reverse. -/
theorem d4BMPeierlsFunctionalEquationPair_borelEdge
    (q : XiZeroCopy) (k : ℕ) :
    (schwarzschildParikhWilczekBorelRecoilEdge
      (d4BMPeierlsFunctionalEquationPair q).1 k,
      schwarzschildParikhWilczekBorelRecoilEdge
        (d4BMPeierlsFunctionalEquationPair q).2 k) =
      (schwarzschildParikhWilczekBorelRecoilEdge (q.1 : ℂ) k,
        schwarzschildParikhWilczekBorelRecoilEdge (1 - (q.1 : ℂ)) k) := by
  rw [d4BMPeierlsFunctionalEquationPair_eq_xi_reflected]

/-- Raw numerator of the literal Peierls square-metric coefficient. The physical coefficient is
this expression divided by four. -/
def d4BMPeierlsMetricSquareNumerator (q : XiZeroCopy) : ℂ :=
  D4BMModularCore.physicalRate q true *
    (D4BMModularCore.physicalRate q true - 1)

/-- **Bare-coefficient PW no-go.** The raw Peierls metric numerator cannot be a natural-grade PW
Borel recoil edge at an actual Xi copy. Equality would force the forbidden real Xi zero. -/
theorem d4BMPeierlsMetricSquareNumerator_ne_forwardBorelEdge
    (q : XiZeroCopy) (k : ℕ) :
    d4BMPeierlsMetricSquareNumerator q ≠
      schwarzschildParikhWilczekBorelRecoilEdge
        (d4BMPeierlsFunctionalEquationCoordinate q) k := by
  intro h
  have him := congrArg Complex.im h
  norm_num [d4BMPeierlsMetricSquareNumerator,
    d4BMPeierlsFunctionalEquationCoordinate,
    D4BMModularCore.physicalRate,
    schwarzschildParikhWilczekBorelRecoilEdge,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at him
  have hzero : (4 * (k : ℝ) + 6) * (q.1 : ℂ).im = 0 := by
    nlinarith [him]
  have hfactor : 4 * (k : ℝ) + 6 ≠ 0 := by positivity
  have hqim : (q.1 : ℂ).im = 0 := (mul_eq_zero.mp hzero).resolve_left hfactor
  exact xi_divisor_support_im_ne_zero q.1 hqim

end

end RHTower
