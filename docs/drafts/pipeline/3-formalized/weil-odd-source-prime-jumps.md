# Odd Weil pole source: aligned prime jumps

- **ID:** weil-odd-source-prime-jumps
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` RW; `CCMRestrictedWeilPolarParitySourceProfile`
- **Statement:** At every interior spatial point, the actual odd parity prime–Gamma pole source has a nonnegative two-sided jump. Each visible prime power contributes the same positive weight at its two reflected sites.

## Goal

Identify exact arithmetic orientation of the actual forced ground source, retaining every prime power and the Gamma boundary. A successful theorem confines odd-source sign loss to continuous drift between prime sites. It does not by itself sign a selected ground pairing or prove RH.

## Gates

- [x] 0 → 1: exact source, finite aperture, explicit jump candidates
- [x] 1 → 2: dependency-closed paper proof below, including collisions and endpoint exclusions
- [x] 2 → 3: direct Lean theorem, named build, axiom audit, umbrella import (MUST-1331)

## Conjecture and attack

Let `K_a(x)=e^(x/2)[B(a−x,a+x)−E_psi(e^(a−x))−E_M(a+x)]`, and `O_a(x)=K_a(x)−K_a(−x)`. Write `E=e^(a/2)`, `F=e^(−a/2)`. Expected jump at interior `x`:

`ΔO_a(x) = (E−F) Σ_{2≤n≤e^(2a)} Λ(n)/√n · (1_{x=a−log n}+1_{x=log n−a}) ≥ 0`.

The two sites may coincide or collide with other indices; the sum must retain multiplicity. Attack: expand both Chebyshev and reciprocal-Mangoldt cumulatives as finite indicator sums, prove the continuous remainder has zero two-sided jump, then prove each indicator atom contributes the stated positive weight. Compare against existing aperture-entry slope laws, which concern a different variable.

## Paper proof [PROVED HERE]

Fix `a>0` and `x∈(−a,a)`. Put `R=a−x`, `L=a+x`, `S={2,…,⌊e^(2a)⌋}`, and `ℓ_n=log n`. The finite Chebyshev and reciprocal cumulative definitions give

`ψ(e^R)=Σ_{n∈S} Λ(n)1_{ℓ_n≤R}` and `Σ_{2≤n≤e^L}Λ(n)/n=Σ_{n∈S}(Λ(n)/n)1_{ℓ_n≤L}`.

Expanding both source errors and subtracting the reflection yields `O_a(x)=G_a(x)+Σ_{n∈S}A_{a,n}(x)`, where

`G_a(x)=e^(x/2)[B(R,L)+L]−e^(−x/2)[B(L,R)+R]`,

`A_{a,n}(x)=−Λ(n)[(e^(x/2)−e^(−x/2)/n)1_{ℓ_n≤R}+(e^(x/2)/n−e^(−x/2))1_{ℓ_n≤L}]`.

The terms `e^(x/2)e^R` and `e^(−x/2)e^L` cancel exactly. `G_a` is continuous on the open aperture because both Gamma boundary arguments stay positive. For fixed `n`, the first indicator drops from 1 to 0 as `x` increases through `r_n=a−ℓ_n`; its jump is `Λ(n)(e^(r_n/2)−e^(−r_n/2)/n)=(E−F)Λ(n)/√n`. The second indicator rises from 0 to 1 through `−r_n=ℓ_n−a`; its jump is `−Λ(n)(e^(−r_n/2)/n−e^(r_n/2))=(E−F)Λ(n)/√n`. Both equalities use `e^(ℓ_n)=n`. Finite sums commute with the two one-sided limits. If the two sites coincide, both jumps are counted; other collisions add with the same sign. Since `Λ(n)≥0` and `E>F`, the total jump is nonnegative, and positive exactly at a visible prime-power site. No zero hypothesis or numerical calculation enters.

## No-go closure

If the jump conjecture fails, identify the exact sign-changing term and strongest surviving oriented atomic statement before retiring it.

## Log

- 2026-10-10 — Started after endpoint-rank theorem failed to control the selected constrained ground. No web or literature novelty test per user instruction.

- 2026-10-12 — Formalized (MUST-1331): `RHTower/CCMPolarOddPrimeJumps` (`ccmPolarOddSource_jump`, `ccmPolarOddSource_jump_nonneg`), standard axioms, wired.
  - **Correction to the paper proof.** The claim "the terms `e^(x/2)e^R` and `e^(−x/2)e^L` cancel exactly" is false: their difference is `e^a(e^(−x/2) − e^(x/2)) = −2e^a sinh(x/2)`. The continuous core is therefore `G_a(x) = e^(x/2)[B(R,L) + e^R + L] − e^(−x/2)[B(L,R) + e^L + R]`. The previous Lean statement omitted the exponentials, was false, and carried the corpus's only `sorry`. The jump law is unchanged, since the extra term is continuous.
