# Route L: original Green poles and complete boundary residues

- **ID:** L-C50
- **Date:** 2026-09-12
- **Stage:** 3-formalized; both modules checked at default Lean limits
- **Depends on:** C44 actual weighted source; C48 complete original jump; C49 actual Green Mellin identity
- **RH status:** unproved

Chain: complete original Green/BV source → fixed physical-reader agreement
→ conormal vanishing → RH. C49 now identifies the actual weighted primitive
and preserves the native Xi coefficient. The hard gap remains the fixed
physical comparison, including every boundary face and normalization.

## Closed source and boundary comparison

For the actual damping-two source f, original prime p, and L=log(p), set
`Q(s)=M(f)(s)/(1-exp(-sL))`. C49 identifies Q with the literal original
Green transform on `0<Re(s)<2`; C44/C45 admit the numerator on `-1<Re(s)<2`.
For every integer k, let `s_k=-2*pi*i*k/L`. Lean proves: Q is meromorphic
on the latter strip, has a simple pole at every s_k, and

`residue(Q,s_k)=M(f)(s_k)/L=Fourier(f)(k/L)/L`.

The last quantity is nonzero and precisely C48's k-th original Fourier coefficient of
the complete two-ended jump. The frequency sign and original measure are
part of the identity. No circle rescaling or boundary subtraction is allowed.

## Direct proof mechanism

The numerator is analytic and nonzero at each s_k by the actual source
results. The denominator vanishes there and has derivative L. The
original-denominator Laurent coefficient and order theorems then apply.
C44's literal Fourier/Mellin equality and C48's original coefficient
formula identify the residue with the same complete boundary. Both generic
and actual-source scratch proofs pass at default Lean limits, including
the exact meromorphic order, sign, and original cell measure.

The proof constructs the analytic divided difference `d(s)=dslope D s_k s`.
It has value `L` at the pole, and `D(s)=(s-s_k)*d(s)` holds even at the
totalized value at the pole. Thus the quotient is exactly
`(N(s)/d(s))/(s-s_k)`. The already audited analytic simple-pole coefficient
theorem gives `N(s_k)/L`. The analytic orders of numerator and denominator
are respectively zero and one, giving meromorphic order minus one. The
only simple zero used is that of the explicit exponential denominator.

## Comparison obligation

Even equality of every residue and jump coefficient does not identify the
fixed Burnol/Deninger physical reader on the degree-six Green/BV boundary.
The next step must assemble these same contributions with Tate depth,
multiplicity, native Xi coefficient, Gamma normalization, and horizontal
anchor retained. A residue deletion, a fitted reader, or an assumed
conservation law cannot supply that comparison.

The full zero-indexed norm bound for the reciprocal prime denominator is
now proved by [C51](route-l-original-green-full-xi-bound.md), including
literal Green-field convergence in the original Xi norm and native Tate
graph admission. Literal polynomial-moment formulas for all Green
derivatives remain separate. C49 proves the derivatives of the actual integral
function and native Xi response; it does not identify all those derivatives
with integrals of polynomially weighted Green representatives.
The C51 bound uses the actual unconditional zero-free margin and Gaussian
source moments. It does not identify the complete BV and physical readers.

## Corpus and method audit

[Residue search](../1-in-progress/route-l-green-boundary-residue-search.json): generation
878003, partial at the deadline/ranking stage, coverage pending. All 20
candidate statements and 20 source arguments were inspected; no proof
ideas or ingredient groups returned. Compiler applicability is unchecked.

The method in `shiftedXiQuotient_residue_tendsto` in `ShiftedXiResidueMode`
applies `tendsto_residue_of_simple_zero` to an actual denominator derivative
and numerator continuity. Its application there assumes a simple Xi zero,
which is not transferred. Here the zero to prove simple belongs to the
explicit exponential prime denominator. The source file was read through
the exact application. `laurentCoeff_analytic_div_sub` in
`SimplePoleResidueValue` supplies the coefficient after constructing the
local analytic factor; both steps now pass Lean. Burnol quotient candidates require their Sonin
domain and divisor premises and do not independently supply the physical
comparison.

[Simple-zero search](../1-in-progress/route-l-green-simple-zero-search.json): query
generation 878083; inventory snapshot 878087 covers 56999/56999 files
(47394 Lean, 9605 prose). Text/source retrieval and three iterative queries
are partial; compiler applicability is source-only and unchecked. All 20
candidate statements and 20 source arguments were inspected. No proof
ideas returned. The proposed negative-Laurent-coefficient vanishing group
requires analyticity or a nonnegative order bound and cannot be applied
at these actual poles. The selected divided-difference and Laurent
coefficient methods were checked against their exact source definitions
and then applied in the passing generic scratch proof.

[Reader search](../1-in-progress/route-l-green-residue-reader-search.json): query generation
878139, inventory snapshot 878145 with 57005/57005 files (47400 Lean,
9605 prose). Results remain partial at the deadline and semantic-coverage
stage, with applicability source-only and unchecked. All 20 candidate
statements and 20 source methods were inspected. The proposed Laurent
pairing/coboundary group contains a pairing definition and a residue-zero
equivalence, not an unconditional physical cancellation theorem.

The actual `FokasLenellsRHBoundary` construction was read through its
Hardy pair and original jump identities. It solves a specific L2 matrix
jump using the inverse for its normalized scattering source. No equality
with Route L's original source, jump, or physical reader has been proved.
Its projection cancellation therefore cannot be transferred. The exact
`DeningerOrdinaryIntegerBVGreenStokesRadialComparison` reflected-difference
law and zero criterion were also read: they retain the radial conormal
defect, and vanishing is exactly critical-line placement. Neither method
closes the fixed physical-reader gap.

## Lean implementation and optimization

`DeningerOriginalGreenPoleCalculus` contains the divided-difference proof
and original exponential denominator calculus. The separate
`DeningerOriginalGreenBoundaryResidues` applies it to the actual source.
Both are wired once into `RHTower.lean`; no umbrella build is run.

Explicit derivative coefficients, a named exponential value at the pole,
explicit source-strip inequalities, and one real-to-complex inverse
rewrite resolve elaboration failures. No heartbeat or recursion-limit
increase, axiom printing, or numerical experiment was used. The generic
profile records import 72.2s, elaboration 108ms, and tactic execution 222ms.
This separates the measured import cost from proof cost; it is not a
claimed end-to-end speedup. Both scratch files pass without warnings.

## Broad recent-paper audit

Single-word arXiv query `interface`, newest first, found
[Hyperbolic distance matrix completion](https://arxiv.org/html/2609.10403v1)
(9 September 2026). Theorem A characterizes a Lorentz Gram kernel by
positivity of its anchored kernel `P_ij=k_i0*k_j0-k_ij`; Theorem B supplies
completion for chordal graphs under the corresponding local clique
conditions. Neither identifies Route L's prescribed physical measurements
with such a kernel or derives its positivity from the actual source.
Choosing a different anchor or fitted kernel cannot supply the fixed
reader comparison. This is an audited method candidate, not a theorem
transferred to Route L. No numerical example or completion algorithm ran.

The final leaf audit
`lake build GaloisForLFunctions.RHTower.Deninger.DeningerOriginalGreenBoundaryResidues`
passed. Only the two new modules built: pole calculus 46s, actual-source
application 8.3s; existing dependency warnings were replayed. Index
regeneration passed, and all 15 public declarations are present in the
API index. Global lint outcome is recorded separately below.

Logs: [core profile](route-l-green-pole-core-profile.log),
[final leaf audit](route-l-green-boundary-residue-build.log),
[index](route-l-green-boundary-residue-index.log),
[global lint](route-l-green-boundary-residue-lint.log).

Global lint failed on four unrelated modules unreachable from their own
umbrellas: `RHTower.ThetaCuspHawkingBMHorizonCoordinateJets`,
`HTGeometry.ElementaryHorizonJets`,
`HTGeometry.SecondEndpointMellinLaurentInterchange`, and
`HTGeometry.UniformSecondOrderJet`. None was edited or compiled for C50.
Both C50 imports are present; this is not a passed global lint gate.
All owned Lean processes terminated normally.
