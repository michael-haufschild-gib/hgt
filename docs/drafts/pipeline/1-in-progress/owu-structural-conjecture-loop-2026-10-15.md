# OWU structural conjecture loop

Status: in progress. Objective: one unconditional structural contribution overcoming an OWU obstacle; no new bound, RH receiver, or unproved producer premise.

## Source discipline

Use current Lean sources and corpus search. No external search, numerical experiments, or old research notes. The requested frontier entry identifies odd-only arbitrary-weight uniqueness as open. Read its cited Lean modules before trusting the summary.

## Plan

1. Identify exact odd-cone obstruction and reusable structures across the corpus.
2. State competing falsifiable structural conjectures; attack, prove, or record failure and successor.
3. Finish a dependency-closed mathematical proof before adding Lean.
4. Audit new modules individually in foreground, wire umbrella imports, run lint, inspect axioms, clean owned scratch files.

## Established source facts

- `OddSectorRiemannKernelRigidity`: vanishing of atom pairings on Riemann-kernel convolutions with even mean-zero tests determines every weight; no constant transform escapes detection.
- `WeilOddConeMinorantRigidity`: an odd-positive minorant of von Mangoldt equals von Mangoldt.
- `OddSectorAnyPoleWeightJointRigidity`: adding even pole-free positivity closes arbitrary-weight uniqueness. That even condition cannot be assumed here.
- `WeilOddBlindPoleWeightWindow`: odd Farkas is already proved, so another separation/receiver theorem does not meet the objective.

## Conjecture ledger

1. **Unrestricted parity transfer by translating odd tests — rejected.** The current odd cosine-shift measure lives on `rho`, with `z^2 = rho^2 - 2`. Its spectral square is `z^2 A A#`. Dividing by `z^2` to recover even positivity changes sign on the imaginary segment. This is a structural sign obstruction, not a missing decay estimate. Source: `OddSectorPoleFreeResonatorPositivity`, especially `specSq_oddLift` and the final resonator theorem.
2. **Reuse the full twisted-arc blind certificate unchanged — rejected.** The existing even null argument integrates a positive lift against an even representing measure. In the odd representation the same expression acquires `1/z^2`; positive real and imaginary contributions can balance. No vanishing follows.
3. **Replace each shifted-Gamma test by an odd test preserving its spectral modulus — false.** At frequency zero an odd transform vanishes, whereas `XiC(0) * shiftedGammaPoly j 0` is nonzero. Every nonzero nonnegative diagonal mixture retains that constant mode. This does not refute correlated, off-diagonal combinations or a different null construction.
4. **Next conjecture:** a correlated Gamma covariance can annihilate the constant mode while retaining prime blindness and the Xi factor. First open core: construct the covariance with the required two constraints; neither may be assumed as a new producer premise.

## Search limitations

The first acronym search found no OWU declarations. Deep natural-language searches returned partial results and weak semantic matches; exact lexical queries and source reads recovered the actual odd spectral machinery. The indexed corpus includes stale/uncompiled entries, so source discovery is not a Lean audit. Serena symbol lookup rejects Lean paths as ignored; use exact `rg` discovery and source reads for Lean.

## Audit

No new mathematical result or completion claim yet.
