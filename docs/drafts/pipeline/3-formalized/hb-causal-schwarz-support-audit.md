# HB causal Schwarz support audit

- **ID:** HB-CAUSAL-SCHWARZ-SUPPORT
- **Stage:** 3-formalized
- **Type:** source-semantics theorem
- **Goal:** unconditional Lean proof/falsification of RH through HB. No RH claim here.

## Full chain and exact gap

Literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → extinction on the fixed Hawking clock → RH.

The canonical angular normalization is closed. The remaining causal action must use the
correct involution on actual time-supported sources. An abstract channel conjugation must
not be identified with time reversal without a support-level theorem.

## Current corpus evidence

- `ThetaCuspHawkingBMCausalChannelEvaluation` defines the actual damped BM frequencies
  `omegaPlus(n,chi)=chi-i(2n+3/2)` and `omegaMinus(n,chi)=-chi-i(2n+3/2)`.
- `ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization` proves the negative-conjugate
  frequency law and corresponding Jost/projective-response identities. These are frequency
  block statements, with no time-support identification.
- `ThetaCuspHawkingBMGaugeFixedCausalQNMCokernel` defines the literal turn-on multiplier
  `i/(target-source)`. Its source/action inputs remain abstract.
- `ThetaCuspHawkingRetardedAdvancedReciprocitySchwarzCausalRigidity` assumes channel Schwarz
  exchanges retarded and advanced maps; it explicitly leaves PDE inverse and support laws open.
- The original Schwarz-odd card explicitly says it does not prove that physical time
  reflection equals the corpus channel involution. The existing no-go theorem is valid in
  its stated class; applying it to ordinary causal reality needs that additional identification.
- The old BM testing-leg zero obstruction remains valid for arbitrary response and is
  independent of this audit.

Whole-corpus queries include `hawking physical source action`, `spin two causal`,
`plebanski green`, `third order invariant source`, `hawking schur source`,
`nonlinear peierls reciprocity`, `causal cut phase`, `retarded reality`, `schwarz retarded`,
`causal wavepacket`, `retarded exponential`, `time reversal retarded`, and
`schwarz even propagator`.

## Exact theorem and dependency-closed paper proof

Define actual time functions

`r_omega(t)=1_(t>=0) exp(-i omega t)` and
`a_omega(t)=1_(t<=0) exp(-i omega t)`.

The exponential never vanishes, so their exact nonzero supports are the two closed half-lines.
Pointwise conjugation leaves time support unchanged and gives
`conj(r_omega(t))=r_(-conj omega)(t)`.
Time reversal instead gives `r_omega(-t)=a_(-omega)(t)`.
At `t=1`, every conjugated retarded mode is nonzero and every advanced mode is zero. Thus
pointwise conjugation never exchanges these nonzero causal orientations, for any frequencies.

For BM frequencies, `omegaMinus(n,conj chi)=-conj(omegaPlus(n,chi))`. Therefore channel
conjugation at the transported angular parameter remains retarded, including on real chi.
The existing second-harmonic frequency law gives the same conclusion for the retained
radiative source grade. This uses no Xi zero or RH premise.

For `Im(target)>Im(source)`, the literal positive-time transform is

`integral_(0,infinity) exp(i target t) r_source(t) dt = i/(target-source)`.

The proof combines exponentials and applies the complex exponential half-line integral.
Simultaneous negative conjugation of target and source preserves the convergence chamber
and conjugates this same retarded multiplier. This identifies the time-domain support law
with the exact multiplier already used by the HB causal convolution.

On the distinct chamber `Im(target)<Im(source)`, the negative-time source instead satisfies

`integral_(-infinity,0] exp(i target t) a_source(t) dt = -i/(target-source)`.

The exponent has positive real rate on this chamber, so the complex exponential integral
over the negative half-line gives the stated sign. Neither formula asserts an inverse Green
equation, and the two convergent integrals do not share a frequency chamber.

## Scope and primary-source check

This audits ordinary pointwise reality and literal time reversal. It does not identify either
operation with a full augmented Einstein Green operator, and does not disprove the algebraic
Schwarz-exchanged no-go or supply extinction. An independently derived operation that reverses
time orientation may still exchange retarded and advanced propagation.

[Bär, Green-hyperbolic operators](https://arxiv.org/pdf/1310.0738) fixes future/past support
and uniqueness of Green operators. For a real operator, preservation of conjugation follows
from conjugation preserving support and solution uniqueness; this is an inference from those
properties, not a quoted BM theorem. The explicit wave-kernel formulas in
[Fitzpatrick's wave-equation derivation](https://farside.ph.utexas.edu/teaching/jk1/Electromagnetism/node7.html)
separate retarded and advanced time support. All BM claims above are proved from corpus
definitions in Lean. No external novelty claim is made.

## Lean result and verification

`ThetaCuspHawkingBMCausalSchwarzSupport` contains 16 new public theorems: seven support,
conjugation, and time-reversal laws; four fundamental/second-harmonic BM transport laws;
and five transform/convergence identities. Its only own-corpus import is
`ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization`. The transform is proved as the
explicit expression `i/(target-source)`, definitionally the existing multiplier, without
importing the large augmented-cokernel dependency tree.

- Scratch and direct leaf checks passed with `lake env lean <file>`.
- Preflight `lake --old --no-build build
  GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCausalSchwarzSupport` selected only this
  new leaf. Final `lake --old build` of the same module passed in 45 seconds; dependencies
  used their existing artifacts. No umbrella or large dependency rebuild was run.
- A single scratch `#print axioms` audit of these 16 new theorems passed. Each depends
  only on `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or computational
  certificate is used. Previously audited declarations were not rechecked.
- The leaf is imported by `GaloisForLFunctions/RHTower.lean`.
- Corpus index was refreshed. The subsequent `lint --check-generated` snapshot reported
  an unrelated unreachable `HTGeometry.RankThreeHankelMixture` and concurrently stale
  `LEAN_API.md` / `LEAN_OVERVIEW.md`; it reported no error in this leaf. Whole-corpus lint
  is therefore not claimed green. No unrelated source or umbrella wiring was changed.

The current route map scopes the earlier no-go to its stated Schwarz-odd/exchanged class.
Universal ledger F20i-c records the route-independent support distinction. The remaining
producer is an actual causal radial/left-QNM action on retained source data with the correct
time-support involution, followed by extinction on the fixed Hawking clock. RH is not proved.

## Tracking

- [x] Recover precise causal-cut and conjugation assumptions; audit prior work.
- [x] Dependency-closed paper proof and bounded primary-source check.
- [x] Scratch proof and direct leaf check.
- [x] Umbrella wiring, final leaf build, new-only axiom audit, and recorded lint snapshot.
- [x] Correct current route scope and record route-independent support law.
