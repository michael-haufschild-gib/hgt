# HB radiation-dressed source-FE coherent-cancellation no-go

- **ID:** HC89
- **Stage:** 3-formalized
- **Type:** CONJECTURE / SOURCE-NATIVE WEIGHT-SELECTION NO-GO
- **Source:** read-only `rh-current-frontier-map.md` · HC88 bright-pair cancellation · literal BM source-FE cocycle and exact retarded Green transfer

## Goal

Attack the hardest survivor after HC88: perhaps its cancelling cross-weights are mathematically
available but not source-native, while literal source functional-equation transport selects a
different physical ratio. Dress the existing literal-source anti-linear FE cocycle by the actual
nonzero retarded ingoing Green transfer. Determine whether this radiative cocycle transports the
actual nonlinear BM mixed-horizon Ward amplitude and whether it canonically realizes the HC88
cancelling ratio.

The decisive target is not another abstract existence statement. Construct explicit weights only
from one raw physical amplitude, its source-FE cocycle, and retarded Green propagation. Prove that
at every off-line copy they are nonzero, cancel two individually bright physical channels, and
satisfy the unique HC88 cancellation equation.

## Gates

- [x] 0 → 1 in-progress: corpus audit; exact conjecture frozen
- [x] 1 → 2 fully-proven: dependency-closed paper proof and bounded primary-literature audit
- [x] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready: independent mathematical/physical review and broader novelty search

## Corpus audit

- `[CORPUS]` the unit-source FE cocycle is the reflected literal nonlinear source divided by the
  conjugate source off wall; it transports that source exactly and is an anti-linear involution.
- `[CORPUS]` source-transported diagonal Peierls weights solve full packet Ward covariance
  unconditionally, while identifying them with fixed unit weights is exactly RH.
- `[CORPUS]` the actual raw mixed-horizon Ward amplitude equals angular mixing times the retarded
  ingoing Green coefficient times the self-dual Einstein carrier. The Green factor is nonzero at
  every Xi copy.
- `[CORPUS]` HC88 classifies every off-line reflected-pair cancellation by one exact weighted-
  multiplier equation and exhibits physical-multiplier cross-weights.
- `[CORPUS NEGATIVE]` mandatory searches found no propagation-dressed source-FE cocycle for the
  actual raw Ward channel, no proof of its involution/transport law, and no identification of its
  canonical weights with the unique HC88 cancelling ratio.

## Conjecture HC89-A: exact radiative source-FE cocycle

First prove the raw unit-seed amplitude identity

`P(q) = G(q) S(q)`,

where `S` is the literal polarized source and `G` the actual retarded ingoing Green coefficient.
Define

`κrad(q) = G(Rq) κsource(q) / conj(G(q))`.

Prove exact anti-linear transport

`κrad(q) conj(P(q)) = P(Rq)`

and involution

`κrad(Rq) conj(κrad(q)) = 1`.

## Conjecture HC89-B: source-native bright-pair cancellation

Define canonical coherent weights

`a(q) = -κrad(q) conj(P(q))`,  `b(q)=P(q)`.

The transport law makes `a(q)=-P(Rq)`. Prove

`a(q)P(q)+b(q)P(Rq)=0`

for every copy. At every off-line copy, prove `a`, `b`, `P(q)`, and `P(Rq)` are all nonzero.

## Conjecture HC89-C: exact match with HC88 unique ratio

At every off-line copy, prove the source-native weights satisfy

`a(q) M(q) = b(q) M(Rq)`,

the unique HC88 cancellation equation. Thus literal source transport plus actual causal propagation
constructs—not merely permits—the divisor-dependent cancelling ratio.

Package universal off-line source-native bright-pair cancellation as a closed proposition and
theorem with no external premise.

## Paper proof

The raw BM projection and literal source have the same mixing and Einstein-carrier factors; the
former has one additional Green factor, proving `P=GS`. Conjugating this identity and multiplying
by `κrad` cancels the nonzero conjugate Green factor; literal-source FE transport then gives
`G(Rq)S(Rq)=P(Rq)`.

For involution, expand `κrad(Rq) conj(κrad(q))`. Reflection is involutive; nonzero Green factors
cancel, and the remaining product is the existing source-cocycle involution. The canonical weight
identity `a=-P(Rq)` makes coherent cancellation commutative algebra. Off-line brightness follows
from the corpus pointwise-darkness classification. Finally HC88's off-line iff theorem converts
the already proved cancellation into the unique weighted-multiplier equality.

## Hostile checks

- Use the actual retarded hypergeometric Green coefficient, literal BM source amplitude, and raw
  nonlinear horizon projection; no free abstract transport scalar.
- Prove transport and involution as exact complex equalities.
- Prove nonzero weights and two nonzero raw channels off line.
- Prove the constructed source-native weights satisfy HC88's unique ratio, not only that their sum
  happens to cancel.
- Do not claim weights are divisor-independent or reflection-real. Those are precisely the
  surviving constraints.
- No RH hypothesis, computation, numerical bound, new axiom, `sorry`, or `admit`.

## Expected route impact

If proved, HC89 kills the objection that HC88 cancellation uses nonphysical arbitrary weights.
Literal nonlinear source FE plus exact causal Green propagation canonically builds an involutive
radiative transport and a cancelling bright-pair weight ratio. Remaining HB/FZZ-P/PW-B/RBH burden
becomes narrower: derive divisor-independent or reflection-real detector weights from local source
dynamics, or enforce copywise darkness before any FE aggregation.

## Bounded primary-literature audit (2026-08-28)

- `[LITERATURE]` Aros--Martinez--Troncoso--Zanelli,
  [*Quasinormal modes for massless topological black holes*](https://arxiv.org/abs/hep-th/0211024),
  derives exact scalar hypergeometric QNM data, not this Xi-source radiative cocycle.
- `[LITERATURE]` Birmingham--Mokhtari,
  [*Exact Gravitational Quasinormal Frequencies of Topological Black Holes*](https://arxiv.org/abs/hep-th/0609028),
  derives exact gravitational hypergeometric modes, without a nonlinear source-FE Ward transport
  or coherent cancellation classification.
- `[LITERATURE]` Henry,
  [*Furry's Theorem and Interference of Electrodynamic Amplitudes*](https://doi.org/10.1103/PhysRev.166.1553),
  relates amplitudes under charge conjugation, not this arithmetic source/Green-dressed involution
  and RH-bearing copywise distinction.
- `[NOVELTY CLAIM, BOUNDED]` Targeted primary-source and exact corpus searches found no theorem
  combining actual topological-black-hole retarded Green propagation, literal Xi source-FE
  transport, unique reflected Ward-weight classification, and bright-pair cancellation. This is a
  bounded audit, not an exhaustive literature claim.

## Formalization result

Formalized in
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFECoherentCancellationNoGo`.

- The actual raw unit-seed BM Ward projection is proved exactly equal to retarded Green transfer
  times the literal polarized nonlinear source.
- `hbXiPhaseSensitiveUnitRadiativeSourceFECocycle` dresses literal source FE by the reflected and
  unreflected Green coefficients; it is nowhere zero, transports the actual raw channel exactly,
  and satisfies an exact anti-linear involution law.
- Canonical weights are constructed from one raw channel and this radiative cocycle. The left
  weight is proved exactly equal to the negative reflected raw channel.
- These source/propagation-native weights cancel every reflected pair identically.
- Off line, their cancellation satisfies HC88's unique weighted-multiplier equation.
- The closed theorem `hbXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation` proves that at
  every off-line Xi copy both weights and both actual nonlinear BM channels are nonzero while the
  coherent return vanishes and the unique ratio law holds.

Audit: direct `lake env lean` passed; targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRadiativeSourceFECoherentCancellationNoGo`
passed all 12,018 jobs. Representative `#print axioms` outputs contain only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint reports only pre-existing unreachable modules and
no HC89 finding. Module is wired into the `GaloisForLFunctions.RHTower` umbrella without running a
full umbrella build.

## Open core after HC89

Source nativeness and causal Green propagation are dead as objections to reflected bright-pair
cancellation: they canonically construct the unique cancelling ratio. Remaining producer must
forbid divisor-dependent coherent weights. Exact surviving conditions are now fixed or
reflection-real physical weights, already known corpus-side to turn packet Ward covariance into
RH. Hardest next audit is whether local detector/source algebra forces reflection-real weights, or
whether the radiative cocycle admits an explicit positive/Hermitian transported form evading that
condition too.
