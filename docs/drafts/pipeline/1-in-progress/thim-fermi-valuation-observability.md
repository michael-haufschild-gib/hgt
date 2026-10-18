# Fermi valuation sampling in the reciprocal-cell norm

- **ID:** thim-fermi-valuation-observability
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Statement:** For arbitrary Möbius-twisted coefficients, selected physical Fermi
  jumps recover the complete sieve sequence, with sharp uniform reciprocal-cell
  energy constants 1/4 and 1, at every horizon and beyond every octave.

## Native problem and prior work

The corpus gives the all-octave boundary jump
`J(n)=2 1_(2|n) s(n/2)-s(n)` and generic dyadic prefix inversion, as well as
squarefree sieve saturation `s(2n)=s(n)` when `2|n`. It does not yet connect
these into a uniformly conditioned observation schedule in the physical
reciprocal-cell norm. This addresses Pillars 1–3: preserve arithmetic source
information across valuation depth without using a full period.

Searches used hybrid, lexical, and deep corpus modes. Deep search was partial
(unfinished prime-deletion/reranking stages); all applicability requires Lean
verification. Relevant source arguments: `AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization`,
`TransHorizonGramMatrixAndRadicalProjection`, and
`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation`.
No claim of global mathematical novelty follows from these searches.

## Exact paper proof

Write `s(n)=sieveSeq N c n`, `F(n)=fermiCellResponse N c n`,
`J(n)=F(n)-F(n-1)`, and `w(n)=1/[n(n+1)]`. Take
`c(d)=mu(d) a(d)` for arbitrary real coefficients `a`, so squarefree support
is proved rather than assumed.

For each `m>=0`, put `o=2m+1`, `e=2m+2`. The universal jump formula and
squarefree saturation give `J(o)=-s(o)` and `J(2e)=s(e)`.
Thus observations at odd boundaries and boundaries divisible by four recover
all positive sieve observations with coefficient magnitude one.

For any finite set S of m, define
`P=sum_S [w(o)s(o)^2+w(e)s(e)^2]` and
`Q=sum_S [w(o)J(o)^2+w(2e)J(2e)^2]`.
Since `w(e)/4 <= w(2e) <= w(e)`, `P/4 <= Q <= P`.
More precisely,
`4Q-P=sum_S [3w(o)s(o)^2+s(e)^2/(e(e+1)(2e+1))]`.
This identity retains the exact positive slack and proves the lower bound.

The constant four in `P<=4Q` is optimal uniformly in S: at horizon two,
choose c(2)=1 and all other coefficients zero. On singleton sets with
e tending to infinity, `P/Q=2(2e+1)/(e+1)` tends to four.
The upper constant one is attained by c(1)=1,c(2)=-1 (odd indicator).

### Failed stronger conjecture and positive survivor

Dropping squarefree support fails already at horizon four: c(2)=c(4)=1,
other coefficients zero, and m=0 give s(1)=0,s(2)=1,s(4)=2, hence
J(1)=J(4)=0 but P=1/6. No finite uniform inverse constant exists for this
selected schedule on unrestricted coefficients. The positive survivor is the
complete saturation-based reconstruction and sharp pronic stability above.
This failure does not assert that the complete unsampled Fermi trace loses data.

## Scope and significance gate

This recovers sieve observations from Fermi *jumps*. It does not bound the
Fermi response itself or establish uniform Nyman tail boundedness, Möbius
half-power cancellation, or RH. The weighted stability is a native candidate
advance; assess external novelty and significance before counting it.

## Verification plan

- [x] Dependency-closed paper proof.
- [ ] Lean source audit, no warnings or new axioms.
- [ ] Sharpness and unrestricted-weight obstruction formalized.
- [ ] Umbrella wiring, generated index, formal lint.
- [ ] Independent novelty/significance audit; ledger count decision.
