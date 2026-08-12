# Cofinal formation depth alone implies positive selection -- failed

- **ID:** ULF-PFRM-FAIL-2
- **Status:** `[FALSIFIED] [EXPLICIT COUNTERTHEOREM] [POSITIVE SURVIVOR PAPER-PROVED]`
  `[LEAN PENDING] [NOT RH]`
- **Parent programme:**
  `../../../1-in-progress/universal-law-field/primitive-formation-rigidity-mechanics/field-programme.md`
- **Positive survivor:**
  `../../../2-fully-proven/universal-law-field/primitive-formation-rigidity-mechanics/conjugate-formation-work-reporter-capacity-reciprocity-recovery-isometry-and-depth-invisibility-law.md`

## Failed conjecture

If a completed current needs polynomial formation depth tending to infinity on every cofinal packet,
then its distance from every bounded-depth positive/Hilbert formation should stay uniformly positive.

## Counterexample

On the packet with nodes `1,...,N`, unit weights and source amplitudes, take the resolvent target

\[
 r_i=-1/i.
\]

Its least exact polynomial formation depth is `N-1`. Nevertheless its squared distance from the
degree-`N-2` formation space is

\[
 \frac1{N^2\binom{2N-2}{N-1}}\longrightarrow0.
\]

Thus exact source history diverges while one-step-below positive work vanishes.

## Exact killing mechanism

The order-`N-1` divided difference stays nonzero, but the norm of the normalized divided-difference
reporter tends to infinity. Algebraic formation depth records nonmembership; it does not control the
condition number of the separating functional.

## Positive survivor

For every Hilbert formation subspace `L` and target `x notin L`,

\[
 \operatorname{dist}(x,L)^2
 \inf_{\varphi|_L=0,\,\varphi(x)=1}\|\varphi\|^2=1.
\]

For resolvent packets this becomes an explicit barycentric divided-difference formula, is preserved
by common recovery and functional-equation isometries, and predicts the exact last Gram/Schur
innovation.

## Representation lesson

Formation depth is only the primal half of the mechanism. The viable field variable is the
conjugate pair:

1. least positive work needed to leave the formation space;
2. least normalized dual capacity needed to certify that departure.

A source-level selector must control both. Merely strengthening the topology or counting more jets
cannot repair the failure.

## Lean status

The positive survivor has a dependency-closed Stage-2 paper proof. No Lean was written or built in
this research continuation, so project rules do not accept it yet as proved.

## Log

- 2026-08-12 -- conjecture killed by the consecutive-node resolvent family; exact conjugate
  formation/coformation reciprocity extracted as positive survivor.
