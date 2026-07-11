# Route B semilocal Sonin interim verdict

- **ID:** route-b-semilocal-sonin-interim-verdict
- **Stage:** 2-fully-proven
- **Type:** ROUTE VERDICT / BRIDGE
- **Scope:** Route B in `docs/reports/rhtower_status_1107.md`

## Verdict

`[SEARCH; CONSTRUCTION CLOSED IN THE LITERATURE]` The requested genuine compact-support semilocal
explicit-formula operator is not an unknown scientific object. Connes's proved semilocal trace formula
uses the scaling representation on the semilocal adele-class space and the cutoff defect

`1 - P_T^S - Fourier(P_W^S)`

to realize the sum of the local Weil distributions, including the finite-prime factors `log(p)`.
The logarithmic scale is an orbital/fixed-point length in the semilocal quotient, not a normalization
of a uniformly bounded principal/residual Gram response.

`[PROVED IN LEAN; OLD SCALARIZATION CLOSED]` The repository's projection-correction pairing is a
different operator. Its uniformly bounded geometric response cannot equal `log(p^m)`. The theorem
`not_soninSemilocalFluxNormalization` correctly kills that pairing, but it does not refute Connes's
semilocal trace operator.

`[BRIDGE; EARLIER CANDIDATE DEMOTED]` The unnormalized cyclic mass has a strictly positive two-prime
cross-effect, but cyclic normalization erases this scalar and leaves the Jacobi grading unchanged.
The card `semilocal-sonin-two-place-positive-association.md` remains a true inequality but fails the
Route-B significance gate.

`[PROVED ON PAPER; CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Normalization does not erase the Jacobi
grading. The card `semilocal-all-even-jacobi-prolate-residue-tower.md` proves an alternating nonzero
ground-state residue in every positive even archimedean Jacobi degree for every finite nonempty prime
set. Its first member strictly contracts the first Jacobi coefficient below `1/sqrt(2)`. This turns
the source's qualitative grading nonintertwining into an infinite explicitly signed tower of formal
prolate naturality-defect coefficients.

`[OPEN CORE]` What is not known is whether this positive low-mode prolate residue survives compression
to the exact semilocal Sonin sector in a trace-ideal or relative-resolvent determinant boundary, and
whether the resulting form is positive on the cofinal class required by Weil's criterion.

`[DIRECT METRIC/FREDHOLM VARIANTS CLOSED]` The forward Euler metric, its inverse cyclic density, and
both polar square roots have noncompact corners across the actual Sonin projection. In particular the
exact bounded Sonin identification cannot be unitarized modulo compacts by its canonical polar
decomposition. Only genuinely additional prolate-resolvent smoothing remains live.

`[RESOLVENT DOMAIN GATE SHARPENED]` All finite semilocal Jacobi coefficients satisfy explicit
two-sided linear growth, so the formal prolate parity blocks have quadratic Jacobi coefficients.
The corresponding reciprocal off-diagonal series converges, so the elementary Carleman divergence
criterion cannot select a self-adjoint realization. A source-defined boundary condition and its
Schatten resolvent estimates are mandatory, not technical cleanup.

`[RAW DEFECT DETERMINANTS CLOSED]` The pulled-back grading defect strictly lowers the cyclic
polynomial filtration. All finite truncations are nilpotent with determinant one; any compact
extension is quasinilpotent, and any trace-class extension has Fredholm determinant one. The new
alternating residue tower proves nonvanishing but cannot evade this determinant blindness.

Therefore Route B has two different verdicts:

1. **As an explicit-formula operator-construction project:** closed as SEARCH/BRIDGE; formalization and
   project integration remain useful engineering, not new scientific knowledge.
2. **As an RH mechanism:** alive but sharply narrowed. The target is no longer to manufacture the
   von-Mangoldt trace. It is to prove that the already source-defined, genuinely mixed finite-place
   normalized Jacobi/prolate datum survives Sonin compression and acquires unconditional cofinal
   positivity.

Route B has not proved RH.

## Why the old formulation was misleading

The report's open core asks for a log-coordinate convolution/test operator whose trace is the
prime--archimedean explicit-formula functional. That equality is already the content of the semilocal
trace formula. Rebuilding it from the real `L2` principal/residual Gram decomposition conflates three
objects:

- the formal cutoff defect used in the trace formula;
- the exact orthogonal Sonin projection and its Hilbert--Schmidt correction;
- the principal-subtracted prime dilation residual.

Only the first is the proved explicit-formula trace operator. The second controls archimedean Sonin
positivity. The third supplies valid Calkin and residual invariants but its fixed Hilbert--Schmidt
pairing cannot carry the logarithmic orbital length.

## Candidate moves and attack

1. `[SEARCH]` Insert the logarithmic-coordinate position/translation commutator. This is the known
   Burnol conductor-operator mechanism and is not new knowledge.
2. `[SEARCH]` Use `theta_S(f)(1-P-P_hat)`. This is Connes's proved semilocal trace formula and closes
   the construction request, but not RH.
3. `[REFUTED IN LEAN]` Recover `log(p^m)` from the fixed projection-correction Hilbert--Schmidt pairing.
   Uniform boundedness kills it.
4. `[BRIDGE]` The positive unnormalized two-place partition cross-ratio is removable cyclic-vector
   normalization and does not change the number operator.
5. `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` Every finite nonempty prime set strictly contracts the
   normalized first Jacobi edge and gives a positive low-mode matrix coefficient of the formal
   prolate naturality defect.
6. `[OPEN CORE]` Prove or refute survival of that residue under the source-defined semilocal
   prolate/Sonin cutoff and relative-resolvent smoothing.
7. `[REFUTED]` Obtain a Fredholm comparison by inserting the Euler metric, its inverse, or the polar
   square-root correction. Every corresponding actual-Sonin corner is noncompact.

## Kill and promotion conditions

- **Kill:** the normalized prolate defect corner vanishes after Sonin compression, is outside
  every admissible trace ideal even after relative-resolvent smoothing, or becomes an arbitrary
  vertexwise gauge coboundary.
- **Promote:** construct the closed semilocal prolate operators and compatible Sonin projections;
  prove the mixed corner is trace class or has a canonical perturbation determinant; prove a nonzero
  presentation-invariant two-place boundary; then derive unconditional cofinal Weil positivity.
- **RH promotion:** only an unconditional Lean theorem supplying the full positivity/cofinality input
  and invoking an existing machine-checked RH equivalence can close RH.

## Literature basis

- Alain Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*,
  Selecta Mathematica 5 (1999), Sections VII--VIII.
- Alain Connes and Caterina Consani, *Weil positivity and trace formula, the archimedean place*,
  Selecta Mathematica 27 (2021).
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta zeros and prolate wave operators*,
  Annals of Functional Analysis 15 (2024), Section 4.
- Alain Connes, Caterina Consani, and Henri Moscovici, *On q-series and the moment problem associated
  to local factors*, arXiv:2403.01247.
- Jean-Francois Burnol, *The explicit formula and the conductor operator*, 1999.
