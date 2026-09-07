# HB reduced radial boundary uniqueness

- **Stage:** 3-formalized
- **Goal:** unconditional closed Lean proof/falsification of RH through HB; not achieved.

## Full chain and exact target

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → fixed Hawking-clock extinction → RH.

The continuous reduced BM Green action already solves its actual forced equation. The target
here is its uniqueness under the regular-horizon and normalizable-AdS phase conditions, and
the resulting forced boundary coefficient. This removes arbitrary choice of a reduced radial
response or projection. It does not identify the full Einstein source or time-retarded operator.

Corpus searches for `green uniqueness`, `source radial profile`, `Wronskian source`, and
`ricci coordinate` distinguish this missing characterization from existing exact Wronskian
conservation, Cramer phase reconstruction, and coordinate Einstein tensor definitions. The
physical source cannot be replaced by a scalar radial specialization or a restricted pure-spin
jet: the corpus requires full two-coordinate reconstruction.

## Dependency-closed paper proof

Let R and V be the exact regular horizon and normalizable AdS solutions. Their normalized
Wronskian D is nonzero when Re(chi) is nonzero, which holds on every actual Xi fibre.
For continuous f and interior anchors a,b, the constructed response u solves L u=f and
has W(R,u)(a)=0 and W(u,V)(b)=0. Here W(y,v)=p(y v'-y' v).

For any other twice differentiable solution y with the same equation and boundary phase
conditions, h=y-u solves the homogeneous equation. W(R,h) and W(h,V) are constant on
the connected radial interior. Their values vanish at a and b respectively. Cramer's rule
in the nondegenerate R,V basis therefore gives h=h'=0 throughout the interior.

Consequently every such response has at b the phase vector
(V(b),V'(b)) times integral_a^b R(t) w(t) f(t)/D dt. The coefficient is extracted without
division by V(b), which can vanish: W(R,y)(b)/D equals that integral. Since the V phase
vector is nonzero, the entire boundary phase vanishes exactly when this moment vanishes.
This distinguishes unique inversion of the full field from possible cancellation of one
boundary coefficient. It is not the final opposite-QNM projection of the full third-order source.

## Lean result

`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicRadialBoundaryUniqueness.lean`
contains a boundary-problem predicate, the canonical coefficient definition, and nine public
theorems. The predicate requires actual first and second derivatives and the literal forced BM
expression. Uniqueness itself does not assume continuity of the source. Existence and equality
with the integral action use continuity on the radial interior. The Xi theorem supplies the
nonzero Wronskian from the existing source geometry, without an inverse-map premise.

- `d4BMPlusPlusRadialBoundaryProblem_homogeneous_eq_zero`
- `d4BMPlusPlusRadialBoundaryProblem_unique`
- `d4BMPlusPlusContinuousGreenResponse_boundaryProblem`
- `d4BMPlusPlusRadialBoundaryProblem_eq_green`
- `d4BMPlusPlusContinuousGreenResponse_normalizableCoefficient`
- `d4BMPlusPlusRadialBoundaryProblem_rightBoundaryJet`
- `d4BMPlusPlusRadialBoundaryProblem_normalizableCoefficient`
- `d4BMPlusPlusRadialBoundaryProblem_boundary_eq_zero_iff`
- `d4BMXiPlusPlusRadialBoundaryProblem_exists_unique_phase`

## Verification

Scratch `lake env lean` passed without warnings. Final
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicRadialBoundaryUniqueness`
passed in **8.2 seconds**, **2 jobs**, in an isolated exact-source leaf package using the
project's toolchain and cached import directories. No dependency or umbrella build ran.
Only the new leaf's olean/ilean were installed in the workspace cache. Source bytes matched
exactly. The leaf is wired into the RH umbrella.

One subsequent `lake env lean` scratch audit checked all nine new theorems: dependencies were
only `propext`, `Classical.choice`, and `Quot.sound`. Existing theorem axioms were not re-audited.
Formal index generation and `scripts/formal_tools.py lint --check-generated` passed. The first
generated-file check caught a concurrently stale overview; one refresh and retry passed. No
proof-debt or wiring finding remained. Scratch files and owned processes were cleaned up.
No route retired; RH remains unproved here.
