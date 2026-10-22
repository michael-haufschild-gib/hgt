# Actual quadratic angular Einstein source and correction

- **Stage:** 3-formalized; exact-source leaf and new-theorem axiom audits passed.
- **Type:** `[BRIDGE]`; no novelty claim.
- **Goal:** literal theta cusp → Xi occurrence → retained spin-two source → physical
  causal response and left-QNM pairing → fixed Hawking-clock extinction → RH.
- **Result:** the complete fundamental scalar/coexact-vector two-jet has an explicit
  quadratic angular Einstein source. A constructed second-order correction removes
  its two Hessian channels, leaving a determined gradient-square source.

## Source calculation

Use the corpus's massless BM metric
`diag(-(r²-1),(r²-1)^-1,r²/y²,r²/y²)` and the previously constructed complete
fundamental scalar and coexact-vector metric jets. Let `f=r²-1`, and let `B` denote
their common temporal/radial envelope. Its logarithmic derivatives are `s` in time
and `s/(r*f)` radially. Scalar and vector amplitudes `aS,aV` remain independent.

The scalar angular jet satisfies
`Syy=(s+1)(s+2)S/y²-Sxx`; its coexact partner is `(Sy,-Sx)`. The full metric jet
retains all ordered coordinate second derivatives, including the third scalar
angular derivatives needed for the coexact-vector reconstruction.

Represent a trace-free symmetric angular tensor by `(Txx-Tyy,Txy)`. Put

```
H = (S*(2*Sxx-(s+1)*(s+2)*S/y²-2*Sy/y), S*(Sxy+Sx/y))
G = (Sx²-Sy², Sx*Sy)
rotation(T) = (2*T.2, -T.1/2)

C = s²*((s+1)²-4r²)/(8r⁴)
D = s²*(3s²+12s+11)/(2r⁴)
F = s²*(s+1)/r³.
```

Here `H=(S Hess_gamma S)_TF`, `G=(dS tensor dS)_TF`. The normalized actual
quadratic Einstein coefficient is exactly

`Q = B²[aS² C(2H+G) + aS*aV F rotation(H+G) + aV² D G]`.

The identity holds for all complex parameters with `r!=0`, `y!=0`, `r²!=1`.
No sign, Xi-zero restriction, supplied nonlinear source map, or computed certificate
enters its proof. In particular, every second and third scalar angular derivative
cancels in the vector--vector channel. The mixed channel is a rotated Hessian of
the squared scalar, since `(Hess_gamma(S²))_TF=2(H+G)`.

## Independent proof mechanism

`HTGeometry.CoordinateEinsteinComplexQuadratic` differentiates the corpus's actual
first Einstein variation. It retains both inverse variations, every spatial
inverse derivative, both mixed connection products, and the scalar contraction.
Derivative uniqueness identifies this finite expression with the actual complex
Hessian of the complete Einstein metric-jet function.

`RHTower.ThetaCuspHawkingBMQuadraticAngularSource` substitutes the complete scalar
and coexact-vector jets into that finite contraction. Exact field algebra proves
both angular components at arbitrary height. The scalar and cosmological
contractions cancel in this trace-free pair because the angular metric is conformal;
they are retained until this cancellation is proved.

An independent hand check of SS uses the scalar temporal/radial matrix `T`.
Its background trace is zero and
`Tr((g_orbit^-1*T)²)=s²((s+1)²-4r²)/(2r⁴)`.
The angular block Ricci formula therefore gives `B² C(2H+G)`.

The [RunPod experiment](../2-fully-proven/computations/hb-quadratic-angular-source-2026-09-07/REPORT.md)
motivated the SV/VV factorization. It ran for 9.91 seconds with three workers and
passed 96 background/first-order consistency checks. It evaluated y=1. The Lean
proof instead derives the all-y identity from the original contraction and uses
no experimental result as proof evidence.

## Explicit correction and exact remaining source

Define a symmetric second-order correction by the following nonzero components:

```
k_tt = -2*f*aS²*B²*C*S²
k_tA = f*aS*aV*B²*s*(s+1)/(2r³) * S * (coexact S)_A.
```

The correction's complete two-jet is constructed using the full product and
inverse jet rules, rather than assigning only these metric values. The envelope
square carries time rate `2s` and every mixed radial/time derivative.

`RHTower.ThetaCuspHawkingBMQuadraticAngularCorrection` evaluates the actual first
Einstein variation of this correction. Its angular coefficient is exactly

`Lk = -B²[2*aS²*C(H+G)+aS*aV*F*rotation(H+G)]`.

Insert the correction into the actual nonlinear metric-jet path
`g+epsilon*h+epsilon²*k`. The existing differentiated path theorem gives its
normalized quadratic source as `Lk+Q`. Thus its angular component is exactly

`B²*(aV²*D-aS²*C)*G`.

Its radial factor is explicitly
`B²*s²*[aS²*(4r²-(s+1)²)+4*aV²*(3s²+12s+11)]/(8r⁴)`.

This is an explicit correction and a computed-by-proof remainder. No assumption
that a left test kills the Hessian terms was used. Their removal is achieved by
the displayed correction's actual linear Einstein image.

## Physical obligations retained

This result evaluates two angular tensor components and constructs a particular
correction of them. It does not solve all sixteen Einstein equations. In particular,
the other source components, the correction's global field realization, nonlinear
gauge completion, horizon and boundary admission, and causal turn-on remain open.
No physical retarded/advanced response map has been identified with this correction.
The original affine-source pairing still contains the correction's linear image
unless the actual left test kills it on the physical domain, including boundary
terms. The corrected-jet identity alone does not justify replacing that original
source by the gradient remainder in a causal cut.

The gradient-square remainder must now be carried through the complete constrained
master-source reduction and paired with the actual left test, retaining its angular
and radial boundary terms. Its correspondence with the retained spin-two/AIME
source and any independent fixed-clock extinction law are still unproved. The
nonzero scalar metric boundary charge from the prior calculation remains relevant.

RH is not proved or falsified by this result. The frontier map is read-only.

## Validation

All source and correction identities passed foreground `lake env lean` checks.
Exact-source final audits compiled only the three requested new leaves against
cached dependencies:

- `lake build GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexQuadratic`: 5.1 seconds; 9 public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticAngularSource`: 221 seconds; 2 public theorems.
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuadraticAngularCorrection`: 24 seconds; 3 public theorems.

All fourteen new public theorems were axiom-audited once in a scratch file; each
uses only `propext`, `Classical.choice`, and `Quot.sound`. No added axioms or
experimental certificates occur. The statements retain their explicit local
nondegeneracy conditions; no unconditional RH theorem is claimed.

Main-tree and audit sources match byte-for-byte. Each leaf is imported once by
its area umbrella. Only the three new olean/ilean pairs were installed; no full,
umbrella, or existing dependency build ran. One owned foreground Lean/Lake check
ran at a time. Corpus index generation and scoped whitespace checks passed.
The final `scripts/formal_tools.py lint --check-generated` check has one unrelated
concurrent error: `HTGeometry.SmoothBlockWindow` is missing its area-umbrella import.
It also reports 141 existing large-file warnings. Generated files are current and
all three new HB leaves are reachable; the other task's module was preserved.

All owned Lean/Lake processes completed. The exact 95-entry local scratch tree
was inventoried without symlinks and removed; its absence is verified. The RunPod
experiment and remote cleanup are complete. Other tasks' files and processes
were preserved. The frontier map received no edits from this work.
