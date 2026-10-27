# Polar gluing of Lorentzian forms

Status: formalized. The algebraic construction is complete; application to the full arithmetic
intersection form remains open.

## Question and corpus boundary

Finite symmetric forms can each have at most one positive square while their sum has several.
What exact compatibility cost separates local Hodge inequalities from a global one, and can it
be repaired by a construction compatible with grouping and restriction?

`HTGeometry.schurComplement_sum_eq`, in `HTGeometry/QuotientFusionProjectionGenesis.lean`,
already establishes the scalar weighted-variance identity. The ALG development reuses it.
The added results concern its matrix correction, exact signature criterion, constructed
hyperbolic assembly, composition and sharp calibration. No novelty is claimed for the scalar
variance identity itself.

## Objects and proof

Let `Q_i` be symmetric real matrices with a common vector `e` of positive square. Write
`a_i=Q_i[e]`, `b_i(x)=Q_i(e,x)`, `A=Σa_i`, `b=Σb_i`, and
`R_i(x)=b_i(x)^2/a_i−Q_i[x]`.

The weighted variance
`V(x)=Σ a_i(b_i(x)/a_i−b(x)/A)^2`
is the quadratic form of
`C=Σ (Q_i e)(Q_i e)^T/a_i−(Σ Q_i e)(Σ Q_i e)^T/A`.
The scalar identity gives `R_(ΣQ_i)=ΣR_i−V`. A positive anchor makes hyperbolicity equivalent
to nonnegativity of its reserve, proving the sharp summation criterion.

The matrix `C` is positive semidefinite and pairs to zero with `e`. Therefore `ΣQ_i−C` has the
same anchor row and reserve `ΣR_i`, hence is hyperbolic for hyperbolic local inputs. This proves
a signature for the constructed form; it does not establish the signature of `ΣQ_i`.

The correction telescopes under grouping into within-group and between-group parts. Preservation
of polar rows and addition of reserves prove associativity of corrected assembly as a quadratic
form. The bilinear pullback formula proves that correction and assembly commute with linear
restriction carrying the anchor along.

When all local reserves vanish, uncorrected addition is hyperbolic exactly when normalized polar
rows agree. For `Q_(t,r)=[[1,t],[t,t²−r]]`, each plane is hyperbolic exactly when `r≥0`; the sum
of opposite slopes is hyperbolic exactly when `r≥t²`. Its correction is `diag(0,2t²)`.
This is the positive survivor of unrestricted-summation failure: an exact threshold, rigidity
condition and replacement construction. The canonical correction need not be a minimal repair
when local reserves already pay some dispersion.

## Lean declarations

Module: `formal/GaloisForLFunctions/ArithmeticLorentzianGeometry/PolarGluingAndDispersion.lean`.

- `isHyperbolic_iff_anchorReserve_nonneg`
- `qf_polarGluingCorrection`, `polarGluingCorrection_nonneg`
- `anchorReserve_sum`, `isHyperbolic_sum_iff_dispersion_le`
- `bil_polarGluingCorrection_anchor`, `bil_polarGlue_anchor`
- `anchorReserve_polarGlue`, `isHyperbolic_polarGlue`
- `polarDispersion_eq_zero_iff`, `isHyperbolic_sum_iff_alignment_of_zero_reserve`
- `polarGluingCorrection_group`, `qf_polarGlue_group`
- `qf_polarGluingCorrection_pullback`, `qf_polarGlue_pullback`
- `isHyperbolic_tiltedPlane_iff`, `isHyperbolic_opposite_tiltedPlanes_iff`
- `polarGluingCorrection_opposite_tiltedPlanes`

Final audit from `formal/`:
`lake --old env lean GaloisForLFunctions/ArithmeticLorentzianGeometry/PolarGluingAndDispersion.lean`
passed without errors or warnings. The ten main signature/composition/calibration declarations
printed only `propext`, `Classical.choice`, and `Quot.sound` as axioms. No olean was produced;
no downstream module being developed imports this file. Its import is wired into the programme
umbrella, which was not compiled.

## Arithmetic question still open

Construct the local forms, pole allocation and anchor from arithmetic, then prove an identity
or correctly directed comparison with the actual Weil intersection form. Pay the dispersion
from an independently established source energy, including overlap and the infinite place.
No such full-form comparison is assumed or proved by this module. An exhaustive signed transfer
also remains necessary.
