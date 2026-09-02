# Dyadic relative-reflection lattice completion

- **ID:** `ULF-DRRLC-1`
- **Stage:** 1-in-progress
- **Type:** higher-mechanism construction programme
- **Status:** retired as producer programme after full-frontier audit; exact rigidity and integral
  Laurent fusion survive, but copywise compact/integral reduction is already a wall receiver

## 1. Big-picture higher law

Horizontal anomaly is not primarily a scalar. It is relative position of two involutions on one
rank-two formation double:

`R = [[0,1],[1,0]]`,

`R_a = [[0,exp(a),exp(-a),0]]` (off-diagonal notation),

with relative monodromy `R_a R = diag(exp(a),exp(-a))`. Their framed difference is

`C_a=R_a-R=[[0,exp(a)-1],[exp(-a)-1,0]]`.

This one matrix is the common source of mixed inertia, reciprocal boost, paired Gamma curvature,
quadratic Laurent ghost, and failure of fixed-frame self-adjointness. New law sought is:

> Proper source completion carries `C_(a log 2)` on a finite rank-two integral lattice on every
> canonical local divisor layer.

Then `det C_(a log 2)` is an integer. But for `|a|<1` it lies in `[0,1/2)`, hence is zero and
`a=0`. Properness is therefore integral monodromy finiteness of the relative reflection double,
not shell summability, positivity, or an integer declared equal to a real character.

## 2. Corpus audit before conjecture

Searches:

- `difference two involutions determinant Lorentz boost quadratic ghost`
- `relative reflection framing determinant curvature holonomy`
- `integral hyperbolic monodromy reciprocal eigenvalues trace dyadic strip`
- `Xi local divisor filtration conormal layer multiplicity one dimensional jet quotient`
- `proper integral local system monodromy Xi conormal`

Facts found:

1. `SourceHorizontalGammaSixRelativeReflectionFraming` already constructs `R`, `R_a`, proves both
   involutive, proves `C_a=R_a-R`, and proves unframed trace/determinant blindness.
2. `SourceHorizontalGammaSixCurvedSuspensionHodgeTrace` proves
   `det C_a=2(cosh a-1)`, exactly positive Gamma curvature.
3. `FrankensteinXiFullIntegralGammaEvaluationProducer` proves the Laurent identity
   `(T-1)(T^-1-1)` evaluates to `-det C_a`; this is already a genuine integral source class.
4. `DenseArithmeticLorentzLatticeRigidity` proves a common lattice for the full dense all-prime
   boost action forces grade zero. It does not exploit the open-strip aperture at one prime.
5. `DeningerArithmeticAssociatedGraded` already constructs the global source jet-depth filtration;
   every multiplicity layer is a canonical coordinate and Frobenius becomes diagonal on the
   associated graded. Multiplicity splitting is not missing over `C`.
6. `RoutePCompletedXiConormalMultiplicitySplit` gives canonical analytic copy resolution, but it
   divides by multiplicity over `C` and supplies no integral lattice.
7. `XiReflectionTateConormalLocalization` and `IntegralOrbitTateExtension` prove fixed/free
   reflection separation modulo two, but a free unit pair is a Tate boundary. Integral residue
   existence alone therefore does not force a fixed orbit; a conservative landing remains open.
8. `FESchwarzGermGluingTrivialization` kills scalar germ phases: all flat rank-one gluing is gauge
   trivial inside either orbit type. Required invariant must be higher-rank and arithmetic.
9. `CCMRationalClosedKappaLefschetzParityNoGo` forbids identifying an anti-Real character with the
   untwisted Real-even Lefschetz map. The quadratic relative-reflection determinant is Real-even,
   so it avoids that type mismatch without inventing a Clifford phase.

No searched theorem constructs an integral lattice for the one-prime relative reflection matrix.

## 3. Genuine fusion law

Over `Z[T,T^-1]`, form the two-periodic relative-reflection complex

`L+ --(T-1)--> L- --(T^-1-1)--> L+`.

Its odd differential is the universal matrix

`C_T=[[0,T-1],[T^-1-1,0]]`,

and `det C_T=-(T-1)(T^-1-1)`. Functional-equation inversion exchanges the two arrows and fixes
the determinant. Physical dyadic realization `T -> 2^a` gives exactly `C_(a log 2)`.

Thus three previously separate organs are one object:

1. integral Laurent formation supplies the two arrows;
2. functional equation supplies reflection exchange and reciprocal determinant one;
3. Gamma completion supplies the real holonomy realization.

The fourth organ is the Xi jet associated graded. It supplies canonical one-copy fibres where the
rank-two complex must land. The needed source theorem is a global integral comparison from the
universal Laurent complex to those fibres, not a zero-by-zero fitted basis.

## 4. Exact RH closure

For every Xi support point `rho`, let `a=2 Re(rho)-1`; open strip gives `|a|<1`. If source
completion produces one relative-reflection integral frame on any canonical local-length layer,
`ULF-DRRIF-1` gives `a=0`. Constructing frames for all support points therefore proves RH.

Only one prime and one determinant are required. No dense prime action, two odd ghosts, total
multiplicity division, positivity, ghost erasure, or continuous Fredholm index is used.

## 5. Construction target

1. Start with global integral two-periodic Laurent complex `C_T`, before divisor specialization.
2. Fuse it with existing global Xi source jet filtration, not the Hilbert divisor-copy carrier.
3. Prove dyadic Gamma comparison sends `C_T` to `C_(a log 2)` on every associated-grade layer.
4. Prove completion is proper in the precise sense that each layer inherits a finite free
   `Z`-lattice preserved by this relative differential.

Step 4 is the global formation/properness theorem. Hypertranscendence should appear as obstruction
to extending nonneutral real holonomy over this finite integral mapping torus; recurrence is its
characteristic-polynomial shadow; positivity forgets the relative framing and therefore sees only
the nonnegative determinant.

## 6. Immediate falsifiers

1. Comparison only yields a `Z[T,T^-1]`-module or `Z[2^a,2^-a]`-module, not a finite `Z`-lattice.
2. Lattice is chosen after reading `rho` or diagonalizing `R_a`.
3. Only the determinant class is integral before evaluation; no integral coordinates survive
   physical completion.
4. Properness reduces to existing shell closability, fixed-metric self-adjointness, or Tate
   conservativity, each already RH-equivalent.
5. Associated-grade landing retains total multiplicity rather than one intrinsic jet layer.

## 7. Current boundary

`ULF-DRRIF-1` is Lean-certified. `ULF-IRRCF-1` now constructs the global integral Laurent
two-periodic differential, proves its Clifford square/determinant law, and proves exact Gamma
evaluation to the curved suspension. Construction targets 1 and 3 are complete. Remaining open
theorem is targets 2 and 4: land this one source complex on the existing Xi jet associated graded
and prove its completed fibres retain finite free `Z`-lattices.

## 8. Retirement

Fresh audit of the completed Meyer--Tate/Green and relative Gamma-local-system corpus shows that
each Xi fibre already has a unique coefficient-faithful relative local system, flat even off line,
while positive compact real-form reduction exists exactly at neutral grade. Therefore demanding a
finite integral frame copywise is not a new producer; it renames this existing RH-equivalent
compact-reduction wall.

Positive survivor: `ULF-IRRCF-1` remains a genuine source law. Its matrix must instead be fused
with the literal cofinal Tate naturality defect before divisor specialization. That completion-level
programme is `ULF-CTCA-1`.
