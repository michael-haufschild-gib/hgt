# P. Hall's solvable-group theorem (E_pi, C_pi, and the solvability converse)

- **ID:** hall-solvable
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** user goal 2026-08-21 (mathlib gap: mathlib owns only Hall's *marriage* theorem)
- **Statement:** For a finite solvable `G` and any factorisation `card G = m * n` with `Nat.Coprime m n`
  there is a subgroup of order `m` (E_pi); any two such are conjugate (C_pi); and conversely, if a
  finite `G` has a Hall `p'`-subgroup for every prime `p`, then `G` is solvable.

## Goal
Closes a genuine mathlib gap. The converse contains **Burnside's `p^a q^b` theorem** as its two-prime
case (for `card G = p^a q^b` the Hall `p'`-subgroups are exactly the Sylow subgroups, so the
hypothesis is vacuous), so the project necessarily builds complex character theory of finite groups:
class sums, the central character, integrality of `chi(g)` and of `|K| chi(g) / chi(1)`, and column
orthogonality. All of that is reusable corpus infrastructure.

## Gates
- [ ] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven on paper
- [ ] 2 → 3  formalized: Lean theorems below, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready

## Corpus / mathlib audit (2026-08-21)
mathlib **has**: `Subgroup.exists_right_complement'_of_coprime` (Schur–Zassenhaus, existence half,
normal `N`, no solvability needed); `IsSolvable.commutator_lt_of_ne_bot`; `Subgroup.commutator_normal`;
`powCoprime`; Sylow theory; `Maschke`; `FDRep.char_orthonormal`;
`FDRep.scalar_product_char_eq_finrank_equivariant`.
mathlib **lacks**: any `IsHall` predicate; minimal normal subgroups; conjugacy half of
Schur–Zassenhaus; class functions; count of irreducibles; column orthogonality; integrality of
character values; Burnside `p^a q^b`; Wielandt's three-subgroup solvability theorem.
corpus **lacks** all of the above (only `RHTower/ArtinVirtualCharacter.lean` touches `FDRep`
characters; no Sylow/solvable material at all).

## Approach
**Phase A — E_pi and C_pi.** Induct on `card G` through a minimal normal subgroup `N` of the solvable
group `G`; `N` is elementary abelian, so `card N = p ^ a`.
- `p ∣ m` branch: lift a Hall subgroup of `G ⧸ N`.
- `p ∣ n` branch: the preimage `K` of a Hall subgroup of `G ⧸ N` has order `m * p ^ a`; if `K < G`
  recurse into `K`, else `N` is a normal Hall `pi'`-subgroup and Schur–Zassenhaus supplies a complement.
Conjugacy needs the conjugacy half of Schur–Zassenhaus for **abelian** `N`, proved here by the
explicit cocycle-averaging argument: a complement is `{ gamma h * h }` for a 1-cocycle `gamma`, and
`u := (prod over H of gamma)^(-1/m)` conjugates it back, using bijectivity of `x ↦ x ^ m` on `N`.

**Phase B — complex character theory.** Regular representation, multiplicities via
`scalar_product_char_eq_finrank_equivariant`, column orthogonality
`∑_chi chi 1 * chi g = 0 (g ≠ 1)`; trace of a finite-order operator is a sum of roots of unity, hence
an algebraic integer; class sums span the centre of the group algebra, giving integrality of the
central character `omega_chi(K) = |K| chi(g) / chi(1)`.

**Phase C — Burnside `p^a q^b`.** From `gcd(|K|, chi(1)) = 1` and `chi(g) ≠ 0` conclude `rho g` scalar
(algebraic-integer norm argument through `Q(zeta_n)` embeddings), then the class of size `p^k` in a
Sylow-centre element gives a proper nontrivial normal subgroup.

**Phase D — the converse.** Induct on `card G`. Each Hall `p_i'`-subgroup inherits the hypothesis and is
proper, hence solvable; a proper nontrivial normal subgroup and its quotient inherit the hypothesis;
so a minimal counterexample is simple with at least three prime divisors, and Wielandt's
three-subgroup theorem (to be built) closes it. Two prime divisors is Burnside.

## Log
- 2026-08-21 — created; mathlib/corpus audit done; Phase A started.
- 2026-08-21 — **Phase A complete and Lean-closed** (axioms: only `propext`, `Classical.choice`,
  `Quot.sound`):
  `HTGeometry/HallSolvable/MinimalNormal.lean` (`exists_abelian_normal_prime_pow_card`),
  `ComplementConjugacy.lean` (`exists_conj_eq_of_isComplement'` — the conjugacy half of
  Schur–Zassenhaus for abelian `N`, a mathlib gap), `Existence.lean`
  (`exists_subgroup_card_of_coprime` = **E_pi**), `Conjugacy.lean`
  (`conj_eq_of_card_eq_of_coprime` = **C_pi**), `PiSubgroup.lean` (`IsHallPiSubgroup`,
  `exists_isHallPiSubgroup`, `conj_of_isHallPiSubgroup`).  All wired into `HTGeometry.lean`.
- 2026-08-21 — Phase B in progress under `HTGeometry/GroupCharacter/`:
  `RegularDecomposition.lean` (`IsGStable`, `exists_simple_decomposition`, `trace_regLeft`),
  `Character.lean` (`rho`, `chi`, `sum_chi` = raw column orthogonality),
  `Schur.lean` (`schur`, `sumRho_dichotomy`), `TrivialSummand.lean`
  (`existsUnique_isTrivialOn`), `Eigenvalues.lean` (`exists_eigen_multiset`),
  `Integrality.lean` (`chi_isIntegral`, `chi_conj`, `exists_classSum_scalar`).
  Remaining: the algebraic-integer norm bound (`|chi x| = finrank` when `chi x / finrank` is an
  algebraic integer), the scalar criterion, Burnside `p^a q^b`, and Hall's converse.

## CLOSED — 2026-08-21 (stage 3)

All three parts are Lean-proved, unconditional, and axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only); `scripts/formal_tools.py lint` reports no
`sorry`/`admit`/`axiom`/`opaque`/`unsafe` and every module is reachable from
`GaloisForLFunctions.HTGeometry`.

### Capstones

| Statement | Lean name | Module |
|---|---|---|
| **E_π** (existence) | `exists_subgroup_card_of_coprime`, `exists_isHallPiSubgroup` | `HallSolvable/Existence.lean`, `HallSolvable/PiSubgroup.lean` |
| **C_π** (conjugacy) | `conj_eq_of_card_eq_of_coprime`, `conj_of_isHallPiSubgroup` | `HallSolvable/Conjugacy.lean`, `HallSolvable/PiSubgroup.lean` |
| **Converse** | `isSolvable_of_hasHallProperty` | `HallSolvable/Converse.lean` |
| **Characterisation** | `isSolvable_iff_hasHallProperty`, `isSolvable_iff_forall_exists_isHallPiSubgroup` | `HallSolvable/Converse.lean` |

### New mathlib gaps closed along the way

* `exists_conj_eq_of_isComplement'` — the **conjugacy half of Schur–Zassenhaus** for an abelian
  normal subgroup of coprime index (mathlib exports only the existence half).
* `exists_abelian_normal_prime_pow_card` — **minimal normal subgroups** of finite solvable groups.
* A complete **complex character theory of finite groups** in
  `HTGeometry/GroupCharacter/`: regular-representation decomposition into minimal `G`-stable
  subspaces, `chi`, raw column orthogonality (`sum_chi`), Schur's lemma (`schur`), the unique
  trivial summand (`existsUnique_isTrivialOn`), characters as sums of roots of unity
  (`exists_eigen_multiset`), integrality of characters and of the central character
  (`chi_isIntegral`, `exists_classSum_scalar`), the Kronecker norm lemma
  (`eq_const_of_isIntegral_avg`), the scalar criterion (`exists_rho_eq_smul`), the bridge to
  mathlib's `FDRep` orthogonality (`simple_fdRepOf`) and the multiplicity theorem
  (`card_iso_eq_finrank`).
* **Burnside's `p ^ a q ^ b` theorem** (`isSolvable_of_card_dvd_prime_pow_mul_prime_pow`, and
  `isSolvable_of_card_dvd_two_prime_powers` in an arbitrary universe).
* **Wielandt's theorem** (`isSolvable_of_three_coprime_index`): three solvable subgroups of pairwise
  coprime indices force solvability.
* `mul_eq_univ_of_coprime_index`, `index_inf_eq_mul` — subgroups of coprime index.
