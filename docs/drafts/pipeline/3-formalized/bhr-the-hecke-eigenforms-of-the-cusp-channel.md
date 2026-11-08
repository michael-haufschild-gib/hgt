# BHR — the Hecke eigenforms of the cusp channel

- **ID:** bhr-hecke-eigenforms-cusp-channel
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ASH README §11, open topic 4 ("the cuspidal sectors of the adelic bulk: Maass forms, where Hecke is
  independent of the wave group and there are no resonances"); `bhr-the-cusp-forms-of-the-modular-horizon-exist.md`.
- **Statement:** Let `S(λ)` be the `SL₂(ℤ)`-invariant Maass eigenfunctions of eigenvalue `λ` that vanish at the cusp
  and have zero constant term, and `T_p f(z) = f(pz) + Σ_{b mod p} f((z+b)/p)`.
  1. Every `f ∈ S(λ)` is a cuspidal `L²` Laplace eigenfunction, and its `L²` class determines it.
  2. `S(λ)` is finite-dimensional, of dimension at most the multiplicity of `λ` in the cusp spectrum.
  3. `T_p S(λ) ⊆ S(λ)` and `T_p T_q = T_q T_p` for distinct primes.
  4. For every eigenvalue `λ` of the cusp spectrum there is `0 ≠ f ∈ S(λ)` with `T_p f = c_p f` for every prime `p`;
     the set of such `λ` is infinite.
  5. `|c_p| ≤ p + 1`: the normalized eigenvalue `λ_p = c_p/√p` obeys `|λ_p| ≤ √p + 1/√p`.

## Paper proof
1. `f` is bounded (continuity on `𝒟 ∩ {y ≤ Y}`, decay above, invariance), so `f·𝟙 ∈ L²(𝒟)`. Incomplete Eisenstein
   series unfold to the constant term, which vanishes, so `f·𝟙` is cuspidal. If its class is zero, a narrow unit
   point-pair average of it vanishes identically; by Selberg's principle that average is `h(s)f` with
   `|h(s) − 1| ≤ ½`, so `f = 0`.
2. Distinct Laplace eigenvalues are orthogonal; expanding in the cuspidal eigenbasis, `f·𝟙` lies in the span of the
   finitely many basis vectors of eigenvalue `λ`. The class map is linear and injective.
3. `T_p` preserves invariance, the eigenvalue equation and cusp decay (rational `GL₂⁺` pullbacks); the zeroth Fourier
   coefficient of `T_p f` at `y` is that of `f` at `py` plus `p` times that at `y/p`. For `p ≠ q`, expanding both
   compositions over `P¹(𝔽_p) × P¹(𝔽_q)`: the terms `f(pqz)` agree; `Σ_c f((pz+c)/q)` and `Σ_c f(p(z+c)/q)` agree after
   `c ↦ pc mod q` and periodicity; the same with `p, q` exchanged; the last terms are both `Σ_{m<pq} f((z+m)/pq)`
   (`b + pc` and `c + qb` enumerate `[0, pq)`).
4. Commuting endomorphisms of a nonzero finite-dimensional complex space have a common eigenvector (strong induction
   on dimension: restrict to an eigenspace of an operator that is not scalar). `S(λ) ≠ 0` since it contains the basis
   eigenfunction. Infinitely many eigenvalues by `bhr-the-cusp-forms-of-the-modular-horizon-exist.md`.
5. `|T_p f| ≤ (p+1) sup|f|`, so `|c_p| sup|f| ≤ (p+1) sup|f|`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheHeckeEigenformsOfTheCuspChannel.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages. Axioms of `exists_heckeMaassForm`,
`infinite_heckeMaass_eigenvalues`, `norm_heckeEigenvalue_le`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.HeckeCusp`) |
|---|---|
| (1) | `cuspSpace`, `exists_bound`, `isCuspLaplaceEigen_vecOf`, `cuspidal_vecOf`, `eq_zero_of_toDeckL2_eq_zero` |
| (2) | `eigSpan`, `toDeckL2_vecOf_mem`, `toSpan`, `toSpan_injective`, finite-dimensionality instance |
| (3) | `heckeH_mem_cuspSpace`, `heckeLin`, `sum_twist`, `sum_double`, `heckeT_comm`, `heckeH_comm` |
| (4) | `exists_common_eigenvector`, `exists_heckeEigenform`, `cuspSpace_ne_bot`, `exists_heckeMaassForm`, `infinite_heckeMaass_eigenvalues` |
| (5) | `norm_heckeEigenvalue_le` |

## Scope
Self-adjointness of `T_p` (Petersson), multiplicity one and the Ramanujan bound `|λ_p| ≤ 2` are not treated. On the
graph black holes Hecke separates the cusp forms of one eigenvalue (`heckeTwo_separates`); here whether `T_p` acts on
`S(λ)` by a scalar is the simplicity of the cusp spectrum, which is open.

## Log
- 2026-11-08 — created and formalized.
