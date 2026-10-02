# TG-C9.2: the closed Fourier–jet graph has no collisions

- **ID:** TG-C9.2-20261001-01a0
- **Stage:** 3-formalized
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.lean`

## Exact positive theorem

For actual physical L2, actual Fourier F, and maximal multiplication M by x², take the
topological closure of the literal graph of `E(f,g)=(f+F g,M f+F M g)` on D(M)×D(M).
Both coordinate projections of this closed graph are injective. Thus E is closable and
its closed extension has no nonzero zero-output input. Separate integrability of the
limiting jets is not assumed.

The proof gives the stronger Hermite-tail theorem: an L2 vector orthogonal to
`(C²+B²)h_(n+2)` for every n is zero, where C and B are the actual creation and
annihilation maps on Schwartz functions. The normalized coefficient energies satisfy
`a_(n+4)=(n+1)(n+2)a_n/((n+3)(n+4))`. Every nonzero nonnegative solution violates Bessel
summability by the exact harmonic-tail argument. No initial-mode test or residue-case
split is needed. Continuous Schwartz test equations pass this exclusion to graph closure.

## Exact recovery boundary

The same module proves no bounded L2 left inverse of C²+B² exists. Its adjoint would give
a nonzero weak preimage of h_0, contradicting the stronger tail theorem.
For the actual admitted Schwartz source pair `(Fφ,-φ)`, exact differentiation gives
`E(Fφ,-φ)=(0,-(8π²)^-1 F((C²+B²)φ))`.
Consequently no bounded map from physical outputs H×H to H recovers the first input
coordinate for every maximal-domain source pair. Unique recovery on the actual range
survives, but it has no bounded ambient extension of this kind.

The later C9.5 theorem proves the even maximal-domain obstruction independently using
actual Hermite parity and the even projection. C9.4 identifies the literal prime-depth
graph core, allowing exact transfer of the obstruction to every single-prime finite core.
Ordinary L2 density is not substituted for either step. The exact record is
`../5-failed/tg-fourier-jet-even-bounded-recovery.md`.

## Audit

- Scratch and production `lake --old env lean` checks: exit 0, no warnings.
- Production command: `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.olean GaloisForLFunctions/RHTower/PrimeBurnolFourierJetClosure.lean`.
- Separate final axiom audit of all six public theorems, including even recovery: exit 0; each uses only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Umbrella wired; API/search index refreshed. No full or umbrella build.
- Final C9.4–C9.5 authoritative lint exits 1 on twelve unrelated unwired RHTower leaves,
  listed in the working log. No new TG leaf error.
- New-leaf whitespace check is clean. No added axiom/hole, heartbeat increase, numerical
  experiment, subagent, commit or push.

## Frontier

Graph-closure collision exclusion and the arithmetic-domain core are proved; see
`tg-fourier-jet-prime-graph-core.md`. Neutral projection continuity in the stronger
input-and-output graph norm is the next distinct source-projection target.
Gamma–Xi identification, Hardy-index transfer, and the sub-unit source action remain open.
No RH proof or falsification is claimed.
