# TG-C9.3: bounded recovery fails on the full maximal-domain jet model

- **ID:** TG-C9.3-20261001-01a0
- **Stage:** 5-failed
- **Candidate retired:** a bounded ambient physical-output map recovers the first input
  coordinate for every maximal-domain Fourier–jet source pair.
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.lean`

## Exact obstruction

`primeBurnolFourierJet_no_bounded_first_recovery` proves there is no bounded linear map
R:H×H→H satisfying R(E(f,g))=f for all f,g in D(M), with actual Fourier F,
maximal multiplication M by x², and E(f,g)=(f+F g,M f+F M g).

The actual Schwartz operator W=C²+B² has no bounded L2 left inverse. If T were one,
u=T* h_0 would annihilate W h_(n+2) for every n. The proved Hermite-tail theorem forces
u=0, while testing at h_0 forces its positive squared norm to vanish.

Both coordinates of the exact pair (Fφ,-φ) lie in D(M), and the proved identity
E(Fφ,-φ)=(0,-(8π²)^-1 F(Wφ)) turns any proposed R into such a bounded T. No spectral
asymptotic, numerical experiment, or assumed inverse estimate enters the proof.

## Positive survivor — paper and Lean complete

The actual graph closure of E has injective input and output projections. Thus the source
is closable and the closed extension retains unique physical inputs despite this bounded
recovery obstruction. Its weak kernel is excluded without assuming separate integrability
of the limiting jets. The stronger invariant is that the Hermite tail starting at mode two
already has dense testing range in the orthogonality sense proved by the kernel theorem.

This positive statement and the negative theorem pass production `lake --old env lean`.
All five public theorems pass the separate axiom audit with only propext, Classical.choice
and Quot.sound. The precise proof/audit record is `../3-formalized/tg-fourier-jet-closed-graph.md`.

## Scope boundary and surviving route

This retires bounded recovery on the full maximal-domain model. It does not by itself
retire bounded recovery on the literal finite even prime-depth core. That transfer needs
graph-core density and the correct even-carrier restriction, addressed next in
`../1-in-progress/tg-fourier-jet-prime-graph-core.md`. Ordinary L2 density supplies neither.
TG's provenance-retaining unbounded mapping-cone problem, Gamma–Xi identification,
Hardy-index transfer and sub-unit source action remain open. RH remains unproved.
