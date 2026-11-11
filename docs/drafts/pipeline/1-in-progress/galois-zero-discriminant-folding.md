# Discriminants before and after folding the zero symmetry

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §§10.3(F), 10.5(7).
- **Question:** Which information about conjugation survives the discriminant of
  the full, symmetry-paired Jensen equation, uniformly in degree?

## Target

For the centered Jensen sections `R_d(Ξ)`, prove that the non-real root count
is divisible by four. Identify the discriminant sign lost by retaining both
members of each `z ↦ −z` pair, and recover the sharper invariant on the folded
equation. Connect the resulting counts to the entire off-line divisor through
the existing monotone Jensen exhaustion. No assumption of RH or simplicity.

## Mechanism

Parity gives `R_d(−z) = (−1)^d R_d(z)`. The theta-integral coefficients exclude
nonzero purely imaginary roots. Conjugation and negation therefore partition
non-real roots, with multiplicity, into free four-point orbits.

For `P(X)=Q(X²)`, the anticipated identity is
`disc(P) = (−1)^n 4^n a₀ a_n disc(Q)²`, where `n=deg Q`.
The odd case multiplies this by `a₀²`. Thus the full discriminant loses the
conjugation parity of the folded roots. Repeated roots must be handled rather
than excluded by premise.

## Proof obligations

- Exact arbitrary-degree discriminant identities, including degree zero.
- Imaginary-axis exclusion for every centered Jensen degree.
- Multiplicity-preserving orbit decomposition and folded count.
- Passage to the infinite ξ divisor, reusing `JensenCountsOffLineZeros`.
- Final Lean checks and transitive axiom audit.

## Scope

The centered sections are not all shifted Jensen families. A theorem here
must state that boundary explicitly. It does not decide RH; its positive
content is the precise folded invariant retained after the symmetry quotient.
