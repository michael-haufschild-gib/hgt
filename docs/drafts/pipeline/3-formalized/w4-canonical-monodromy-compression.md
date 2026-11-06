# W4 — canonical monodromy compression

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `DeningerDivisorSchwarzMonodromy.lean`; W4.
- **Statement:** Canonical invariant compression has pure point spectrum unconditionally; Frobenius preserves the invariant subspace exactly when RH holds.

## Existing boundary

The corpus proves that this symmetry commutes with the divisor generator exactly when RH holds (`deningerDivisorMonodromy_comm_iff_riemannHypothesis`). Commutation therefore cannot be assumed as a property of a newly named base.

## Exact decomposition

On each symmetry orbit, write `u = δ_ρ + δ_(1−conj ρ)`, `v = δ_ρ − δ_(1−conj ρ)`, `a = 1/2 + i Im(ρ)`, and `b = Re(ρ) − 1/2`. Then

`Θu = a u + b v`, `Θv = b u + a v`.

The invariant compression has pure diagonal `a` unconditionally; coupling to the anti-invariant part is exactly `b`. At a fixed orbit, `v=0`; no two-dimensional basis is asserted there.

For an arbitrary invariant finitely supported vector `x`, `P₊Θx = diag(a)x`, where `P₊=(1+D)/2`. The compressed point spectrum is exactly `{1/2 + i Im(ρ) : ρ is a Xi-divisor copy}`.

**Proof.** The copy permutation is an involution, and `Θδ_ρ=ρδ_ρ`. Adding and subtracting the two orbit equations gives the displayed identities. For invariant `x`, paired coordinates agree, so averaging the generator replaces `ρ` by `(ρ+1−conj ρ)/2`. Every `u_ρ` is nonzero and realizes this eigenvalue. Conversely, evaluation at any nonzero coordinate of a compressed eigenvector identifies its eigenvalue with the corresponding `a`.

## Stability boundary

`Θ(Fix D) ⊆ Fix D  ↔  RH`.

**Proof.** Apply stability to `u_ρ`. If its two indices differ, evaluate the resulting invariance equation at one of them to obtain `ρ=1−conj ρ`. If they coincide, this equality already follows from equality of their eigenvalues. In both cases `Re(ρ)=1/2`. Conversely RH gives the existing commutation law, hence stability.

## Lean

Module: `ArithmeticKunnethTheory/WeightFamilies/CanonicalMonodromyCompression.lean`.

- `theta_orbitEven`, `theta_orbitOdd`: exact coupling formulas.
- `compressed_theta_on_invariants`, `compressed_eigenvalue_iff`: full algebraic compression and point spectrum.
- `compressed_eigenvalues_pure`: unconditional compressed purity.
- `invariant_subspace_stable_iff_riemannHypothesis`: stability boundary.

Checked with `lake --old env lean`. The existing commutation equivalence is reused, not claimed as new. The stronger stability equivalence and exact compressed spectrum expose the distinction between a pure compression and an invariant restriction carrying the actual spectrum. No new arithmetic base or global trace estimate is supplied.
