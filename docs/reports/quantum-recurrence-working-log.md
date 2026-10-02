# Static local quantum recurrence: working log

## Objective

Prove the complete same-draw Brown–Susskind growth–plateau–first-circuit-return
law for ordinary fixed-locality, time-independent Hamiltonians, together with
permanent distinguishability of locality from Haar randomness at maximal
complexity. This objective is not complete.

## 2026-09-29: remove an artificial time-union loss

Proof chain: ordinary source measure → return-excised incidence-action bound
→ continuous complete-circuit exclusion → growth, plateau, first return.
The decisive growing-replica incidence-action estimate is still missing.

Previous verified correction: nonzero radial rescaling of target vectors
does not change their replica span or the bare projected pair action.
Target norm suppression must remain in the capture threshold or in an
explicit norm-weighted reporter. See `ReplicaTargetRadialGaugeLaw.lean`.

Corpus investigation found a different avoidable loss:
`PauliReturnExcisedCircuitContinuumLaw.lean` charges a time grid and an energy
cap even though `PauliCommutatorReturnTubeLaw.lean` maps every hitting time
into the same static commutator small-ball set.

Conjecture: the existing incidence-weighted finite-target bound holds for
the union over all real times, without the energy tail or time-grid factor.
Proof: choose a hitting time and target, apply the deterministic commutator
inequality, then apply the already-proven static Gaussian union estimate.
Exact endpoint-image compression is retained. This is a strengthening of
the existing corpus result, not an externally established novelty claim.

Adversarial boundary: the error is energy-normalized; identity and weak
centralizers remain difficult; the complete surviving circuit-image sum
still needs suppression. Low-incidence target excision is not equivalent to
the circuit-budget-dependent initial-time cutoff. No source-fibre coarea
multiplicity has been estimated or discarded by this argument.

Implemented `HTGeometry/PauliAllTimeCircuitExclusionLaw.lean`, wired into
`HTGeometry.lean`. All eight initial theorems passed both scratch verification
and `lake --old env lean` on the integrated source. Three headline axiom
audits cover all helper proofs: only `propext`, `Classical.choice`, `Quot.sound`.
No full or umbrella build, no heartbeat increase, no new oleans required.

Second conjecture tested: removing the time-grid penalty might let the static
incidence certificate handle arbitrarily large occupied circuit images.
The verified boundary disproves that extrapolation: each incidence is at
most the number `m` of two-local Pauli directions, hence the unweighted
incidence partition function is at least `N * exp(-a*m)`, with
`a = gaussianIntervalActivationMass^2 / 2`. Taking the family to be the
occupied endpoint subtype makes `N` the number of distinct endpoints.
This is a lower bound on the certificate, NOT on the actual return probability
and NOT a counterexample to Brown–Susskind. The all-time exclusion estimate
above is the positive result retained from this test. Both new ceiling
theorems passed a separate scratch check and standard-axiom audit. The final
combined-source check, `lake --old env lean
GaloisForLFunctions/HTGeometry/PauliAllTimeCircuitExclusionLaw.lean`, exited 0
without warnings. All owned Lean and search processes terminated normally.

Further corpus inspection found the all-time operator-norm Ward reduction
already in `StaticEvolutionProjectiveWardTrichotomyLaw.lean`. It must not be
rediscovered or called the missing probability bound. The weighted carrier
law in `PauliWeightedCommutatorCarrierLaw.lean` avoids cardinality only for
events with design mass at least a threshold `κ`; one adaptively chosen
captured endpoint does not itself provide that lower bound.

Next live conjecture: source-conditioned growing-replica geometry supplies
enough occupied capture mass after the budget-dependent initial cutoff to
close the incidence-action receiver. This remains unproved. Preserve both
source variables in the return-free square and all fibre-sheet multiplicity.
Do not substitute Haar mixing, norm-rescaling of target spans, or the static
unweighted incidence sum for this missing estimate. A coefficient-energy /
operator-norm transfer is a possible normalization improvement, not yet a
proof of complete-circuit exclusion.

Project lint fails on 15 unrelated unwired RHTower modules at the latest
check. No proof-debt error or wiring error was reported for the new leaf.

Search evidence: hybrid and deep corpus queries inspected declarations,
candidate lemmas and source arguments. Coverage reports unavailable semantic
coverage statistics and some stale compiler metadata; source inspection is
the authority. A deep search confused Hamiltonian dynamics with Hamiltonian
graph paths; those candidates were rejected.

Broad recent literature checks: arXiv:2609.05386 describes determinantal
geometry of iterated 2×2 commutators; arXiv:2609.14585 describes single
commutators in C*-algebras. Neither abstract supplies a lower-tail estimate
for a prescribed random local generator or the surviving circuit image.
No transfer from these papers is claimed.

## 2026-09-29: optimize exclusion-proof elaboration

Maintenance only; the growing-replica incidence-action frontier remains open.
Changed four proof bodies in `PauliReturnExcisedCircuitContinuumLaw.lean`
and `PauliAllTimeCircuitExclusionLaw.lean`, preserving every statement and import.
Restricted constant-sum simplification to explicit lemmas; replaced nonlinear
arithmetic, congruence search and ring normalization with order/associativity
lemmas. Broad simplification had attempted expensive failed typeclass searches
on unitary endpoint subtypes.

Same combined-source scratch, synchronous elaboration and native profiler:

- Continuum exclusion proof value: 51,509,745 → 4,703,540 raw heartbeat ticks.
- All-time return-excised exclusion: 36,505,575 → 3,085,771.
- Combined two dominant proofs: 88,015,320 → 7,789,311, a 91.2% reduction.
- Incidence ceiling: 5,271,834 → 1,144,590.
- Certificate-floor proof now falls below the 1,000,000-tick logging threshold.

These are proof-elaboration counters, not whole-project wall-clock speedups.
The profiler threshold filters output only; no proof heartbeat or recursion
limits were changed. Both integrated sources matched the measured combined
scratch byte-for-byte. Final combined-source `lake --old env lean` audit passed
without warnings. Exactly the four changed proofs were axiom-audited: only
`propext`, `Classical.choice`, `Quot.sound`. Existing umbrella wiring retained;
no builds, new oleans, git operations or agents. Global lint still reports 15
unrelated unwired RHTower modules and no failures for the edited leaves.
Owned Lean/search/lint processes exited; temporary optimization files removed.

## 2026-10-02: return-free near-diagonal coherence test

Full ordinary-ensemble incidence-action producer remains open. Hybrid and deep
corpus searches inspected candidate lemmas, source methods, and ingredient sets.
Coverage metadata lacks semantic statistics; source inspection checked actual
applicability. StaticChoiCentralizerCarrierReplicaLaw and
StaticChoiKurtosisNearActionLaw suppress transverse individual targets but leave
the occupied high-centralizer circuit carrier unpaid. No complete-circuit bound
follows from their conditional receivers.

Conjecture under test: for every spectrum in positive dimension, every replica
order r, cutoff a, and T >= max(1,4|a|), the return-excised full pair purity P is
at least g^2/(16 sqrt(r+1) S T), where g=gaussianFloorTwo and S=staticChoiSpeed.
Public unconditional specialization uses T=1+4|a|+u^2 and dimension n+1.

Dependency-closed mathematical proof: set delta=1/(4 sqrt(r+1) S T).
S,T,sqrt(r+1) >=1 imply 0<delta<=1/4. Restrict outer time x to [3/4,1]
and inner time y to [x-delta,x+delta]. Both times lie above 1/2 and hence
outside [-|a|/T,|a|/T]. Speed gives trace distance <=1/(4 sqrt(r+1)),
so fidelity >=1-1/(16(r+1)). Bernoulli gives fidelity^r >=1-r/(16(r+1))
>=1/2. The shifted Gaussian interval lower bound gives inner mass >=2g delta
and outer mass >=g/4. Positivity, restriction monotonicity and Fubini yield
P >= (1/2)(2g delta)(g/4)=g^2/(16 sqrt(r+1) S T).
No nonresonance, ensemble mixing, lost source sheet, or target assumption enters.

At errors epsn=1/2, epsw=3/4, receiver threshold is
g^2(7/16)^(2r)/(64 S^2 T^2). Since sqrt(r+1)<=r+1<=2^r and
2(7/16)^2<1, the purity lower bound strictly exceeds this threshold for
every r, including r varying with T. This only falsifies full-purity substitution;
it does not falsify actual projected action suppression or Brown--Susskind.

Positive survivor to formalize: actual carrier compression ratio A/P must
satisfy an explicit bound proportional to sqrt(r+1)(7/16)^(2r)/(N S T)
whenever the exact incidence-action receiver succeeds. This is a necessary
quantitative requirement, not a new ordinary-ensemble producer. Short-time
coherence and Bernoulli are known ingredients; no external novelty or Nature
claim is assigned to this diagnostic without a further novelty audit.
