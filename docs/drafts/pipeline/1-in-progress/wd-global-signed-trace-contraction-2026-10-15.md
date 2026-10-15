# WD global signed trace contraction

Status: IN PROGRESS. No global contraction proved.

## Exact task

Prove the global signed source-to-divisor trace contraction required by route WD,
unconditionally. The prior parabolic source landing is local and finite-packet only;
it cannot be substituted for this task. Do not assume positivity, an infinite-packet
interchange, or source shorting. No numerical computation, web search, or external
novelty audit; use the current Lean corpus. Paper proof before new Lean declarations.

## Working plan

1. Identify the exact current global signed pairing, target theorem, and proved no-go laws.
2. Conjecture structural mechanisms on the literal arithmetic source; attack each against
   the entire corpus and exact algebra. Record failures and positive survivors.
3. Complete a dependency-closed paper proof of the actual global statement.
4. Formalize, audit leaf modules and axioms, wire umbrellas, lint, and clean scratch.

## Corpus frontier

`XiWardGlobalCapRightZeroSum` already proves absolute convergence and exact global cap
evaluation as `-8*pi*tau` times the right-zero Stieltjes sum. For `0<tau<=12` its real
part is nonnegative, strictly positive if a zero lies right of the cap. Vanishing of
the almost-everywhere cap family is equivalent to RH. There is no missing cap convergence
lemma that can by itself prove the desired sign.

`XiWardCubicPrimeGammaSecantFundamentalSymmetryGap` proves that replacing the literal
Weil cup by its positive fundamental-symmetry energy costs half the reflection-difference
energy; even one fixed nondegenerate secant has zero gap iff RH. The quadratic opposite-radial
current has a negative norm-square boundary signature (`XiWardCubicOppositeRadialBoundarySignature`).
Scalar reflection-compatible shorting preserves that signature.

The prior parabolic source averaging extracts linear multiplicity and realizes the cubic
directional mask on finite packets. It proves neither the global sign nor infinite interchange.

## Conjecture ledger

1. Continue the zero cap from the absolute-Euler chamber through the strip. **REJECTED:**
   the global cap identity records exactly the residues crossed; analyticity in the level
   is the unproved/false intermediate. The positive survivor is the already-proved exact
   Stieltjes jump accounting, not a new theorem.
2. Insert the unconditional Weil fundamental symmetry and apply Hilbert contraction.
   **CIRCULAR:** its erased defect is already RH-equivalent for one fixed source secant.
   Any survivor must keep this defect in the source comparison.
3. Integrability in the logarithmic transverse level would force cap vanishing, since each
   strict-right zero contributes a positive constant on a half-line of levels. **OPEN / NOT
   A SOLUTION:** no source proof of that stronger integrability; ordinary cap integrability
   concerns height, not logarithmic level. This only relocates the hard core.
4. Differentiate the exact theta Doob identity `M Phi=-cosh(x/2)` and use `-Phi'` as a
   positive odd-sector supersolution. **OBSTRUCTION FOUND:** folding prime jumps produces
   reflected sum squares, not a positivity-preserving half-line generator. A ground-state
   transform cannot discard those signed off-diagonal terms. Investigating corpus coverage.
5. Diagonalize the all-prime Doob form on divisor graphs: prime-power ratio edges form
   complete graphs along exponent coordinates, with complement reflection `m -> N/m`.
   **OPEN CORE:** the exact theta product fibers are signed, so finite graph positivity
   alone does not yield the integrated source sign. Need an exact modular reassembly of
   those fibers, not another spectral-gap estimate. Investigating this mechanism.

## Open core

[OPEN CORE] The global signed arithmetic pairing and its residue trace must be related
with the required orientation, retaining the polar/Gamma/prime coupling.
