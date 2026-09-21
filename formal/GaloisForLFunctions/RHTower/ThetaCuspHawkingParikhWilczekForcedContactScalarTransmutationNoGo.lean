import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMasterCurrent

/-!
# Literal cyclic-Peierls scalar-contact transmutation no-go

The literal corrected-future Peierls contact has, at its compact horizon
vertex, the full-minus-square coefficient ratio
`1 : -r₊(r₊-1)/4`, multiplied by the forced nonzero source parameter
`parameter`.  This leaf tests exactly the remaining scalar-normalization
proposal after the direct Peierls spectral bridge:

```
common nonzero scalar × (full - r₊(r₊-1)/4 · square)
  = common nonzero scalar × (full - PWedge(q,k)/4 · square).
```

It is false at every actual Xi copy and every natural grade.  The proof does
not claim linear independence of the two fields or rule out a field-valued
lift defect.  It eliminates only mechanisms that preserve their displayed
relative coefficient and try to repair the PW mismatch by a common contact
prefactor.

Proof-chain role:
`literal cyclic Peierls CTP contact -> relative Borel coefficient -> fixed-grade
PW balance -> Xi occurrence -> RH`.  The scalar relative-coefficient subroute
is retired; a surviving source bridge must change that relative coefficient
through the explicit, field-valued lift defect.

`[NEW] [PW-B SOURCE NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

open D4BMGlobalAngularResponse D4BMModularCore D4BMQuadraticMixedSource

noncomputable section

/-- PW coordinate retained by the forward physical Peierls branch. -/
def d4BMPeierlsScalarContactCoordinate (q : XiZeroCopy) : ℂ :=
  physicalRate q true + 2

/-- Intrinsic full-minus-square numerator of the literal Peierls source vertex. -/
def d4BMPeierlsScalarContactSquareNumerator (q : XiZeroCopy) : ℂ :=
  physicalRate q true * (physicalRate q true - 1)

/-- The intrinsic source numerator is never a natural-grade PW recoil edge. -/
theorem d4BMPeierlsScalarContactSquareNumerator_ne_borelEdge
    (q : XiZeroCopy) (k : ℕ) :
    d4BMPeierlsScalarContactSquareNumerator q ≠
      schwarzschildParikhWilczekBorelRecoilEdge
        (d4BMPeierlsScalarContactCoordinate q) k := by
  intro h
  have him := congrArg Complex.im h
  norm_num [d4BMPeierlsScalarContactSquareNumerator,
    d4BMPeierlsScalarContactCoordinate, physicalRate,
    schwarzschildParikhWilczekBorelRecoilEdge,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im] at him
  have hzero : (4 * (k : ℝ) + 6) * (q.1 : ℂ).im = 0 := by
    nlinarith [him]
  have hfactor : 4 * (k : ℝ) + 6 ≠ 0 := by positivity
  have hqim : (q.1 : ℂ).im = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hfactor
  exact xi_divisor_support_im_ne_zero q.1 hqim

/-- The literal source's forced common horizon-contact prefactor is nonzero at
every actual Xi copy. -/
theorem d4BMPeierlsScalarContactParameter_ne_zero (q : XiZeroCopy) :
    parameter q true ≠ 0 := by
  rw [D4BMModularCore.parameter_physicalRate]
  intro h
  apply (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1
  simpa [physicalRate] using congrArg Complex.im h

/-- Full/square coefficients after an arbitrary common scalar contact multiplier. -/
def d4BMPeierlsScalarContactCoefficients (q : XiZeroCopy) (c : ℂ) : ℂ × ℂ :=
  (c, -(c * (d4BMPeierlsScalarContactSquareNumerator q / 4)))

/-- PW-normalized comparison coefficients with the same full-field multiplier. -/
def d4BMPeierlsScalarContactBorelCoefficients
    (q : XiZeroCopy) (k : ℕ) (c : ℂ) : ℂ × ℂ :=
  (c, -(c *
    (schwarzschildParikhWilczekBorelRecoilEdge
      (d4BMPeierlsScalarContactCoordinate q) k / 4)))

/-- **Scalar-contact no-go.** A nonzero common multiplier cannot change the
literal source's intrinsic full/square ratio into a PW Borel ratio. -/
theorem d4BMPeierlsScalarContactCoefficients_ne_borel
    (q : XiZeroCopy) (k : ℕ) (c : ℂ) (hc : c ≠ 0) :
    d4BMPeierlsScalarContactCoefficients q c ≠
      d4BMPeierlsScalarContactBorelCoefficients q k c := by
  intro h
  have hsquare := congrArg Prod.snd h
  simp only [d4BMPeierlsScalarContactCoefficients,
    d4BMPeierlsScalarContactBorelCoefficients] at hsquare
  have hraw : d4BMPeierlsScalarContactSquareNumerator q =
      schwarzschildParikhWilczekBorelRecoilEdge
        (d4BMPeierlsScalarContactCoordinate q) k := by
    apply mul_left_cancel₀ hc
    linear_combination -4 * hsquare
  exact d4BMPeierlsScalarContactSquareNumerator_ne_borelEdge q k hraw

/-- Source-specialized form: the forced literal horizon contact cannot acquire
the PW Borel ratio through its own scalar `parameter` prefactor. -/
theorem d4BMPeierlsForcedContactCoefficients_ne_borel
    (q : XiZeroCopy) (k : ℕ) :
    d4BMPeierlsScalarContactCoefficients q (parameter q true) ≠
      d4BMPeierlsScalarContactBorelCoefficients q k (parameter q true) :=
  d4BMPeierlsScalarContactCoefficients_ne_borel q k (parameter q true)
    (d4BMPeierlsScalarContactParameter_ne_zero q)

end

end RHTower
