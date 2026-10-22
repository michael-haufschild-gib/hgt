# Higher-degree sections with three labeled lattice fibers

- **ID:** RH-TLCS-20261007
- **Stage:** 1-in-progress
- **Type:** THEOREM (algebraic family and entire-section consequence in Lean); novelty unverified
- **Source:** `xi-marked-joint-monodromy.md`, C2 hostile audit
- **Statement:** An infinite exact family of reciprocal degree-three rational maps has all three cube-root fibers simple and supported on their prescribed residue classes modulo three.

## Goal

Test C2's proposed rigidity before treating its most elementary models as a
classification. The stronger guess that the labeled cancellation geometry
forces a degree-one rational parameter is false. The construction below
retains the exact labels, every cancellation, reciprocal symmetry and real
structure. It remains differentially algebraic and therefore does not
disprove C2 or the actual Xi cubic no-lift assertion.

## Exact family and paper proof

For any integer m set

```
q=5m+2,
t=-45m^2-36m-8=-(9q^2+4)/5,
A0(w)=w*(w-3q)*(w+3q),
A1(w)=(w-1)*(w-4)*(w-t),
A2(w)=-A1(-w)=(w+1)*(w+4)*(w+t).
```

Expansion, using `5t+9q^2+4=0`, proves

```
A1+A2=2A0.
```

The root sets have respective labels

```
A0: {0,3q,-3q},       all congruent 0 modulo3;
A1: {1,4,t},          all congruent 1 modulo3;
A2: {-1,-4,-t},       all congruent 2 modulo3.
```

All roots are distinct. Here q cannot vanish since q=2 modulo5. Also t=1
modulo3, so it is not zero and no differently labeled roots coincide.
For the remaining same-label comparisons, `t=1` would imply
`5m^2+4m+1=0`, whose reductions at m=0,1,2 modulo3 are nonzero.
The equation `t=4` would imply `15m^2+12m+4=0`, impossible modulo3.
Finally 1 and4 are different, and the three roots of A0 are distinct since
q is nonzero in characteristic zero. These are exact congruence arguments,
not estimates or sign arguments.

Let `omega=exp(2*pi*i/3)` and define the rational map

```
V_m=(omega*A2-A1)/(A2-omega*A1).
```

The numerator and denominator have no common zero: a common zero would
give A1=A2=0 since omega is not plus or minus one, contradicting the
disjoint labeled root sets. Both polynomials have degree three, with
nonzero leading coefficients omega-1 and1-omega. Therefore V_m has
degree three and V_m(infinity)=-1, outside the cube roots of unity.

Direct subtraction gives the exact fiber identities

```
(A2-omega*A1)*(V_m-1)       = 2*(omega-1)*A0,
(A2-omega*A1)*(V_m-omega)   = (omega^2-1)*A1,
(A2-omega*A1)*(V_m-omega^2) = (omega-omega^2)*A2.
```

The coefficients are nonzero and the denominator is nonzero at every
listed root. Thus these are the complete fibers and all are simple.
The formulas `A1(-w)=-A2(w)` and `A2(-w)=-A1(w)` imply
`V_m(-w)=1/V_m(w)` as rational maps. Since all A_j are real and
conjugation sends omega to omega^2, one also has
`V_m(conj w)=1/conj(V_m(w))` on P1.

The family is infinite. Equality of two maps would equate their zero-label
fibers and hence q_m^2=q_n^2. The plus case gives m=n, while the minus case
would give `5(m+n)=-4`, impossible modulo5. Thus all V_m are distinct.

For m=0 this specializes to

```
A0=w^3-36w,
A1=w^3+3w^2-36w+32,
A2=w^3-3w^2-36w-32,
V_0=(omega*A2-A1)/(A2-omega*A1).
```

Its complete fiber lists are `{0,6,-6}`, `{1,4,-8}` and `{-1,-4,8}`.
The previously proved power-of-three degree restriction is therefore
sharp at degree three, not merely at degree one. This does not establish
existence at every degree 3^e.

## Actual holomorphic sections, verified consequence

Fix real L nonzero, let z=s-1/2, `w=Lz/(pi*i)`, and
`r=exp(-2Lz/3)`. Substitute `v=V_m(w)` into

```
h=(2v^3-3rv+1)/(v^3-1),
F(s)=exp(Ls)*(h(s)^3-3h(s)-2)/4.
```

At every point in a distinguished fiber, w is an integer k and
`v=omega^k`, so rv=1. The denominator has a simple zero, the numerator
vanishes, and the singularity is removable. At a pole of v, use its
reciprocal u=1/v: `h=(2-3ru^2+u^3)/(1-u^3)`, which is holomorphic.
These account for every possible finite singularity. Thus h and F are
entire. The reciprocal and conjugation laws give F's reflection and real
structure exactly as in the parent normalization.

Moreover every pole of V_m gives an off-line zero of F, with order twice
the pole order. The denominator is a cubic and has a complex root. None
of its roots is real: at a real root, taking imaginary parts of
`A2=omega*A1` would force A1=A2=0. Under the coordinate w, nonreal w
means `Re(s)!=1/2`. The identity
`h-2=3u^2*(u-r)/(1-u^3)` gives the exact even order since r is a unit.
No growth, positivity, or simplicity assumption about Xi enters this.

### Exact division formula for the analytic formalization

Write N and D for the verified polynomial coordinates, and put
`K=6*(omega-omega^2)`. Multiplying the three fiber identities gives

```
N^3-D^3 = K*A0*A1*A2.
E(w)=D(w)-exp((-2*pi*i/3)*w)*N(w).
Q(w)=E(w)/(A0(w)*A1(w)*A2(w)), with all nine singularities removed.
h(w)=2+(3/K)*D(w)^2*Q(w).
```

All nine roots are distinct, so nine successive exact divided differences
construct Q as an entire function. This avoids a limit of rational maps.
At a denominator root, N and the exponential are nonzero; hence E and Q
are nonzero there. The displayed identity then gives the exact doubled
zero order without an inequality. This is the verified Lean construction:
general finite-root division, exact exponential values at the labeled
integer roots, reflection/conjugation transport, then analytic-order
factorization. The algebraic leaf already supplies the complete fiber and
disjointness certificates needed for these steps.

## No-go closure

- **Exact failure:** labeled lattice fibers and reciprocal symmetry do not
  force a Möbius parameter. They admit the full degree-three family above.
- **Strongest positive survivor:** infinite distinct reciprocal degree-three
  maps with fully specified simple fibers, inducing actual entire reflected
  cubic sections and off-line even zeros.
- **New insight:** the characteristic-three restriction allows genuine
  higher-degree sections. The missing step for C2 is control of unbounded
  degree or transcendental sections, not elimination of all finite branching.
- **Status:** paper proof complete; algebraic family formalized in
  `H:TernaryLatticeCubic`; entire-section consequence and exact doubled
  off-line zero orders formalized in `H:TernaryLatticeSections` and
  `H:TernaryLatticeCountermodel`.
  Classical ingredients; significant novelty unverified. C2 itself remains open.

## First failed extension and next open core

Iteration of one rational parameter is not justified: a subsequent inverse
fiber would require complete splitting over new integer values, not only
over the initial three distinguished values. No claim of an infinite
compatible tower follows from the infinite family of degree-three examples.

Allowing q to be a nonconstant entire even function creates moving fiber
equations `w=+/-3q(w)` and `w=t(w)`. Their full preimages would still have
to lie in the prescribed integer classes and remain simple. Ordinary
interpolation at the known lattice points does not prevent additional
off-lattice preimages. Construct such a hypertranscendental parameter or
prove it impossible: this remains the OPEN CORE.

### Exact jet obstruction at every exceptional fiber

The missing infinite geometry includes jets, not only the locations of the
fibers. Write the lattice-coordinate mark as `r(w)=exp(c*w)`, where
`c=-2*pi*i/3`. Suppose a meromorphic parameter and a holomorphic lift satisfy
`(v^3-1)h=2v^3-3rv+1` near w0 with `v0^3=1`. Evaluation first forces
`r0*v0=1`. Differentiating this identity at w0 then gives exactly

```
(h(w0)-1)*v'(w0) = -c*v0.
```

Its right side is nonzero. Consequently every distinguished fiber is
automatically unramified and the section cannot pass through `h=1` on
its exceptional line. More precisely, `h=2` requires `v'/v0=-c`, and
`h=-1` requires `v'/v0=c/2`. These are algebraic jet identities, not
derivative estimates. The proof differentiates a holomorphic identity;
v is finite at such a fiber, so no meromorphic differentiation issue occurs.

This is a local geometric constraint, not a classification: infinitely
many conditions on a discrete set do not force a global differential
equation. A putative infinite-section argument must preserve these exact
jets as well as exclude all unwanted preimages. No limiting construction
has yet met both requirements. Paper-only; no novelty claim.

## Gates and log

### Corpus and literature audit

The deep corpus query `integer split polynomial three residue classes rational
function fiber Frobenius degree` completed without partial coverage or reported
errors. Its fiber-degree hits concern ordinary polynomial fibers; the suggested
ingredient set concerns splitting an integer sum into residue classes and does
not prove the present assertion. No claim of corpus-wide absence follows.

Two nearby primary sources were inspected:

- Bergweiler--Eremenko, [Meromorphic functions with linearly distributed values
  and Julia sets of rational functions](https://www.math.purdue.edu/~eremenko/dvi/real.pdf)
  (2008): three line-supported fibers force a real-circle alternative or a
  specific exponential form. The real-circle alternative includes these models
  and leaves the hard case unresolved. Their argument uses characteristic
  estimates, so it supplies neither an admissible proof mechanism nor C2.
- Hajdu--Papp--Tijdeman, [The Prouhet--Tarry--Escott problem, indecomposability
  of polynomials and Diophantine equations](https://link.springer.com/article/10.1007/s11139-022-00555-7)
  (2022): an adjacent parent theory for polynomial splitting and equal symmetric
  functions. The present identity is a three-polynomial pencil relation, not
  an established new instance of that paper's main theorems.

**Verdicts:** degree-one rigidity `FALSE`; explicit family `BRIDGE`. The
construction is useful for attacking C2, but significant novelty is not
certified. No bounded-growth, positivity or spectral argument is imported.

- [x] Exact statement and dependency-closed symbolic proof.
- [x] Hostile check of fiber completeness, simplicity and all removable points.
- [x] Preliminary internal/external audit; verdict BRIDGE, novelty unverified.
- [x] Formalize the exact algebraic family, complete simple fibers, symmetries,
  distinctness as rational maps, and existence of nonreal poles.
- [x] Formalize the entire-section consequence and exact zero orders.
- [ ] Formalize the local exceptional-fiber jet identity.
- [ ] Resolve the transcendental-section obstruction required by C2.

- 2026-10-07 — derived the family during the C2 hostile audit. No numerical
  search or numerical zero test was used.
- 2026-10-07 — `formal/GaloisForLFunctions/HTGeometry/TernaryLatticeCubic.lean`
  passes direct `lake env lean` without warnings. Targeted
  `lake build --old +GaloisForLFunctions.HTGeometry.TernaryLatticeCubic`
  succeeds (leaf 3.5 seconds; 2,888 dependency jobs reported). Wired into
  HTGeometry once; generated indexes refreshed. No full or umbrella build.
  Exported theorem `degree_three_family` certifies coprime coordinates of
  exact degree three; `rational_map_equality_iff` certifies injectivity of the
  integer-indexed family even under projective rescaling.
- Final completion of the algebraic certificate adds `leading_coordinates`
  and `infinity_not_distinguished`: no fiber point was lost at infinity.
  Direct leaf audit passes without warnings; refreshed targeted build passes
  (leaf 55 seconds). All 14 audited exports use exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- Final `scripts/formal_tools.py lint --check-generated` fails only on six
  unrelated unreachable modules: `R:ZetaLineTwistedSeriesMoment` and
  `H:ApertureConeCalculus`, `H:ApertureConeWinding`,
  `H:ApertureLogTranslation`, `H:ApertureOpenHistoryIdeal`,
  `H:BoundaryCoronaCStarAlgebra`. No stale generated file or error in the new
  leaf is reported. The global gate is not clean; those files were not edited.
- Research assessment: degree-one rigidity is false, but the family has
  verdict BRIDGE and has not discharged an actual Xi premise. Entire-section
  formalization was required for this obstruction's positive closure and is
  now complete. The next scientific core is still the transcendental section
  with exact labeled fibers and exceptional jets, not more finite examples.

- 2026-10-07 — completed the analytic survivor. `TernaryLatticeSections`
  constructs the removable quotient by nine successive divided differences,
  proves its reflection and conjugation laws, and proves the exact factor
  `P(h)=D^2*sourceUnit`, with the unit nonzero at each denominator root.
  The Lean quotient includes division by K (the Q in the displayed paper
  formula above does not); both conventions give the same h.
  `TernaryLatticeCountermodel.reflected_integer_marked_family` is an
  unconditional theorem for every integer parameter: entire source and lift,
  reflection, real structure, integer mark two, and an off-line reflected
  zero pair of exact nonzero even order. Distinctness is proved for rational
  parameters, not asserted for the resulting entire sources. Differential
  algebraicity of these explicit expressions remains a classical paper
  consequence, not an exported Lean theorem.
- Both new leaves pass direct `lake env lean` without warnings and targeted
  `lake build --old +...` (2,889 and 8,659 reported dependency jobs).
  Both are imported exactly once by HTGeometry. All nine audited results
  use only `propext`, `Classical.choice`, and `Quot.sound`.
  The subsequent global lint reports seven unrelated unreachable modules
  (the previous six plus `R:ZetaSquareMobiusDetilting`) and generated-index
  drift in LEAN_API/LEAN_OVERVIEW. No new-leaf error is reported; the global
  gate is not clean. Refresh and final lint status are recorded separately.
- Analytic-construction corpus audit: the deep finite-root/divided-difference
  query completed with partial=false and no errors. Candidate statements and
  source arguments concern ordinary finite-root or Weierstrass division.
  The inventory was complete at its snapshot, but compiler coverage was not
  globally fresh. Existing `AnalyticRootFactor` supplies finite zero order;
  no search hit or formalization is treated as a novelty certificate.
- Final index refresh completed. The following lint still fails as the
  shared tree changes: eight unrelated unreachable modules (the seven above
  plus `R:WeilZetaSquareRegularPartRigidity`) and drift in all three generated
  reports. The two new leaves remain directly verified; a clean global gate
  is not claimed and unrelated files are not edited.
- Next hostile test is recorded in `periodic-lattice-branched-sections.md`:
  correctly labeled infinite fibers can coexist with infinitely many simple
  critical points. This rejects finite-branching/rational-Schwarzian rigidity
  on paper; exact positive-survivor formalization is in progress. C2 remains open.
