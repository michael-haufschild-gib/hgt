# W4 — canonical monodromy compression

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `DeningerDivisorSchwarzMonodromy.lean`; W4.
- **Question:** Can the invariant part of the canonical symmetry `ρ ↦ 1 − conj(ρ)` supply a pure arithmetic spectrum independently of RH?

## Existing boundary

The corpus proves that this symmetry commutes with the divisor generator exactly when RH holds (`deningerDivisorMonodromy_comm_iff_riemannHypothesis`). Commutation therefore cannot be assumed as a property of a newly named base.

## Sharper target

On each symmetry orbit, write `u = δ_ρ + δ_(1−conj ρ)`, `v = δ_ρ − δ_(1−conj ρ)`, `a = 1/2 + i Im(ρ)`, and `b = Re(ρ) − 1/2`. Prove the exact decomposition

`Θu = a u + b v`, `Θv = b u + a v`.

The invariant compression has pure diagonal `a` unconditionally; the coupling to the anti-invariant part is exactly `b`. Prove that preservation of the invariant subspace alone is equivalent to RH. This would distinguish purity of a compressed operator from purity of an actual invariant restriction.

## Remaining obligation

Formalize the orbit decomposition and stability equivalence. Neither a new arithmetic base nor a global trace estimate follows from the candidate symmetry.
