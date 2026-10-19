# Fermi valuation sampling in the reciprocal-cell norm

- **ID:** thim-fermi-valuation-observability
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** At each horizon, exact selected Fermi-jump recovery holds
  precisely when admitted coefficients divisible by four vanish. This class
  has reciprocal-cell energy constants 1/4 and 1, already sharp on Möbius twists.

## Native problem and prior work

The corpus gives the all-octave boundary jump
`J(n)=2 1_(2|n) s(n/2)-s(n)` and generic dyadic prefix inversion, as well as
squarefree sieve saturation `s(2n)=s(n)` when `2|n`. The proposed new connection
is a uniformly conditioned observation schedule in the physical
reciprocal-cell norm. This addresses Pillars 1–3: preserve arithmetic source
information across valuation depth without using a full period.

Searches used hybrid, lexical, and deep corpus modes. Deep search was partial
(unfinished prime-deletion/reranking stages); all applicability requires Lean
verification. Relevant source arguments: `AllOctaveFermiJumpReciprocityAndDyadicSiblingPolarization`,
`TransHorizonGramMatrixAndRadicalProjection`, and
`RadicalInvariancePrimePowerAbsorptionAndSubHorizonFermiEvaluation`.
No claim of global mathematical novelty follows from these searches.

### Expanded overlap audit, 2026-10-18

- Exhausted both pages of `fermiCellResponse` lexical results (39 declarations,
  eight modules); read the all-octave jump/reconstruction module and closest
  reciprocal-cell, radical-invariance, and second-octave source arguments.
- Searched the whole corpus for `dyadic pronic`, `Fermi jump norm`,
  `reciprocal observability`, `sieveSeq four`, `sieveSeq squarefree`, and
  semantically for local saturation, coefficient recovery, and pronic receivers.
  Excluded the new candidate module from subsequent overlap searches.
- The four-divisibility query returned 24 declarations; both pages were reviewed.
  Its closest zero theorem has a restricted first-band hypothesis and does not
  give an all-horizon coefficient classification.
- Deep searches are not exhaustive: some hit their time budgets, and compiler
  coverage contains pending/stale entries. Search is discovery evidence; source
  statements and leaf compilation decide applicability.
- Existing pronic receiver theorems control *centered prefix discrepancies*.
  The present raw sieve/jump norm does not discharge those premises.

## Stronger conjecture exposed by the support audit

Squarefree support is sufficient but unnecessarily restrictive. The proposed
maximal coefficient class for this exact reading rule is

`(forall N m, J_N(4m+4)=s_N(2m+2)) iff (forall m, c(4m+4)=0)`.

This is an unconditional classification, including arbitrary coefficients at
odd prime squares. For sufficiency, a divisor of `4m+4` which does not divide
`2m+2` must be divisible by four. Thus deleting only the four-divisible
coefficients gives saturation. For necessity, subtract the identities at
horizons `4m+4` and `4m+3`: the newly admitted coefficient divides `4m+4`
but not `2m+2`, so the jump of the recovery error is `-c(4m+4)`.

The sharper identity to formalize is
`E_(4m+4)(m)-E_(4m+3)(m)=-c(4m+4)`, where
`E_N(m)=J_N(4m+4)-s_N(2m+2)`.
This makes the support obstruction directly observable through the existing
Buchstab horizon filtration. The horizon-step identity is a paper consequence;
the stronger fixed-horizon classification below is the theorem formalized.
Treat classification and norm theorem as one connected candidate advance,
not separate contribution counts.

### Stronger fixed-horizon classification

The all-horizon hypothesis can also be removed. At each fixed horizon N,

`(forall m, J_N(4m+4)=s_N(2m+2)) iff
 (forall m, 4m+4<=N -> c(4m+4)=0)`.

Necessity uses induction on the admitted multiple `d=4m+4`. In
`s_N(d)-s_N(d/2)`, every surviving divisor is four-divisible. Every proper
such divisor has already vanished by induction; the remaining term is c(d).
Exact recovery forces that term to zero. Sufficiency is the same divisor
comparison as above. This is the sharp finite-cutoff statement: coefficients
outside the horizon and coefficients at odd prime squares remain unrestricted.

Additional audit: reviewed all 185 `sieveSeq horizon` lexical hits, both pages
of `sieveSeq two_mul`, the prime-chain saturation statements, and the concurrent
`PronicCausalQuadratureInteriorSawtoothAndFermiGramBridge` source. These provide
building blocks or different energies; no equivalent classification was found.
Deep local-class search was partial and returned mostly unrelated results, so
it is not evidence of absence.

The named leaf source audit passed with exit 0 and no diagnostics on 2026-10-18:
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiValuationSamplingAndPronicObservability.olean GaloisForLFunctions/TransHorizonIncidenceMechanics/FermiValuationSamplingAndPronicObservability.lean`.
The fixed-horizon equivalence, all-horizon corollary, canonical four-free
projection bounds, Möbius-twist sharp constants, and explicit alias all passed.
The module is wired into the THIM umbrella. The scratch axiom audit passed
for all 19 public declarations with only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axiom dependency. No contribution has
been counted against the significance goal.

THIM was absent from `THEOREM_AREAS` and `ALLOWED_ROOT_LEAN` in
`scripts/formal_tools.py`; those metadata entries were added and the generated
indexes refreshed. The follow-up `lint --check-generated` reports only three
concurrent unwired modules (`ClosedCycleAmbiguityDecay`, `FiniteGridNullCorrector`,
`RamanujanGapChainExactPrefixGram`) and a concurrently stale `formal/LEAN_API.md`.
The global lint gate remains failed. No full or umbrella build was run.

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
- [x] Lean source audit, no warnings or new axioms.
- [x] Sharpness and unrestricted-weight obstruction formalized.
- [x] Umbrella wiring, area registration, generated index.
- [ ] Global formal lint passes (unrelated concurrent failures listed above).
- [ ] Independent novelty/significance audit; ledger count decision.
