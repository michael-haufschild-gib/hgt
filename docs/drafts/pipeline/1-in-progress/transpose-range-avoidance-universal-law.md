# Transpose-range avoidance universal law

- **ID:** transpose-range-avoidance-universal-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `4-publication-ready/two-sided-singular-gelfand-defects/main.tex` · universal-law extraction
- **Statement:** `[CONJECTURE; NOVELTY UNVERIFIED]` Closed subspaces whose images are dense under every member of an observer family are classified, under annihilator duality, by weak-star closed subspaces avoiding every transpose range; finite injective dense noncoercive Hilbert observers therefore admit common blind defects of every finite codimension.

## Goal

Identify one source-pure operator law from which graph-coordinate classification, the two-sided singularity criterion, hyperplane construction, the explicit rigged-Hilbert counterexample, and all finite-codimensional extensions follow as corollaries.  This card concerns bounded observer maps only; it must not assume any spectral conclusion, rigged-space conjecture, or HGT/RH target.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Competing conjectures

### C1 — annihilator classification for arbitrary Banach observer families

`[CONJECTURE; PRIORITY OPEN]` Let `E` and `F_i` be Banach spaces and let
`T_i : E → F_i` be bounded maps with dense range.  For every norm-closed subspace `M ≤ E`,

```text
closure(T_i(M)) = F_i for every i
  iff
M^perp ∩ range(T_i') = {0} for every i.
```

Moreover `M ↦ M^perp` is an inclusion-reversing bijection from common dense-image closed
subspaces onto weak-star closed subspaces of `E*` disjoint from every transpose range.

### C2 — exact hyperplane threshold for arbitrary families

`[CONJECTURE; PRIORITY OPEN]` A proper common dense-image hyperplane exists exactly when

```text
E* ≠ union_i range(T_i').
```

For a finite nonempty family over `R` or `C`, this is equivalent to failure of surjectivity of every
`T_i'`, hence to failure of a lower bound for every `T_i`.

### C3 — finite blindness hierarchy for Hilbert embeddings

`[CONJECTURE; HARD CORE]` Let `T_1,...,T_r : E → F_i` be bounded injective maps between Hilbert
spaces, each with dense range and no lower bound.  For every finite `n ≥ 1` there is a closed
codimension-`n` subspace `M ≤ E` such that every `T_i(M)` is dense in `F_i`.

Proposed mechanism: every `range(T_i*)` is a proper nonclosed operator range and therefore has
infinite algebraic codimension; construct an `n`-plane `D` with
`D ∩ range(T_i*) = {0}` for all `i`, then take `M = D^perp`.

### C4 — infinite-dimensional strengthening

`[CONJECTURE; EXPECTED FALSE WITHOUT EXTRA SPECTRAL HYPOTHESES]` Under C3 there is always an
infinite-dimensional closed `D` disjoint from all adjoint ranges.  Operator-range literature must
decide this.  If false, extract exact spectral criterion and extremal finite-rank survivor.

### C5 — Pythagorean observer all-or-infinite law

`[CONJECTURE; HARD CORE; PRIORITY OPEN]` Let `P : G → H₁` and `Q : G → H₂` be bounded,
injective, densely ranged Hilbert operators, and assume the joint observer is stable:

```text
∃ c > 0,  c‖x‖² ≤ ‖Px‖² + ‖Qx‖²  for every x ∈ G.
```

Then exactly one of the following holds.

1. One marginal observer is bounded below, and the only closed `M ≤ G` with both images dense is
   `M = G`.
2. Neither marginal is bounded below, and there is a closed infinite-dimensional `D ≤ G` with
   `D ∩ range(P*) = D ∩ range(Q*) = {0}`.  Consequently `M = D^perp` has infinite codimension
   and both `P(M)` and `Q(M)` are dense.

After normalizing `P*P + Q*Q` to the identity, put `C=P*P`; then `Q*Q=I-C`, the two adjoint
ranges are `range(C^(1/2))` and `range((I-C)^(1/2))`, and marginal noncoercivity is exactly
`0,1 ∈ spectrum(C)`.  Disjoint spectral bands accumulating at both endpoints should produce an
orthonormal sequence whose closed span avoids both square-root ranges.

## Door passport sketch

- **Allowed source data:** Banach/Hilbert spaces; bounded maps; dense range; injectivity; lower-bound
  failure; annihilators; transpose/adjoint ranges; finite-dimensional linear avoidance.
- **Forbidden target data:** quasi-Gelfand conclusion, canonical graph equality, zeta/RH spectral
  input, hidden completeness assumption.
- **Non-circularity:** observer maps are fixed before defect `M` is selected; every conclusion is
  expressed through their independently defined transpose ranges.
- **Door-2 obligation:** distinguish standard annihilator identities and closed-range theorems from
  any genuinely new simultaneous-family classification or finite-rank hierarchy.

## Internal prior-art audit

- `finite-observable-conormal-corona.md` proves an algebraic finite-coordinate conormal vanishing
  law, but not the bounded-operator-family theorem.
- `ccm-exterior-range-observability-law.md` records standard one-operator Hilbert range duality and
  is explicitly classified as not new knowledge.
- `PreQuasiGelfandTwoSidedSingularDefect.lean` proves the two-observer hyperplane instance only.
- `resolved-test-completeness-law.md` already cites that two-leg result; it does not contain the
  arbitrary-family annihilator lattice or finite blindness hierarchy.

## External prior-art audit

- Fillmore--Williams, *Adv. Math.* 7 (1971), supplies classical operator-range structure,
  including infinite algebraic codimension of a nonclosed Hilbert operator range and complementary
  square-root range technology; no exact C5 statement was located.
- Drewnowski (1984) proves spaceability of the complement of one nonclosed Fréchet operator range.
- Kitson--Timoney, *JMAA* 378 (2011), prove spaceability when the linear span of a countable family
  of operator ranges is nonclosed.  This does not apply to a graph pair: its two adjoint ranges sum
  to the whole graph Hilbert space.
- Araújo--Barbosa--Raposo--Ribeiro, *Mathematika* 71 (2025), treat unions under additional
  subspace/infinite-codimension hypotheses, not the complementary pair in C5.
- Ribeiro, arXiv:2510.11332v2 (2025), Remark 4.1 claims an arbitrary-family extension.  Its last
  inference only proves disjointness from a countable subfamily: from
  `F ⊂ Xtilde \ Y₀` and `Y₀ ⊂ Y` it incorrectly concludes `F ⊂ X \ Y`.  A nonclosed algebraic
  hyperplane, written as the span of its one-dimensional bounded operator ranges, is an immediate
  counterexample: its complement contains no two-dimensional subspace.

## Approach

1. Prove C1 directly by Hahn–Banach separation and transpose injectivity.
2. Derive C2 using finite-union avoidance and prove `T'` surjective iff `T` is bounded below.
3. Prove that a bounded operator range of finite algebraic codimension is closed.  Apply this to
   each nonclosed adjoint range in C3, then inductively avoid finitely many sums
   `range(T_i*) + D_k`.
4. Audit C4 against Fillmore–Williams/Dixmier operator-range theory and construct a sharp no-go or
   spectral classification.
5. Prove C5 by joint-observer normalization, Douglas range equality, and a two-endpoint spectral
   block construction.  Specialize to canonical graph coordinates, where the stability identity is
   exact.
6. Formalize exact dependency-closed core and specialize it to graph-coordinate observers.

## Open core

- External priority of C1–C3.
- Exact operator-range theorem governing C4.
- Full verification of spectral block construction and its nonseparable edge cases in C5.
- Whether C3 extends from Hilbert spaces to a useful reflexive Banach class.
- Lean representation of finite-dimensional common transverse subspaces without choice leaks or
  forbidden axioms.

## Log

- 2026-08-03 — created directly in `1-in-progress` after internal corpus audit; C1–C4 frozen before proof; all novelty labels remain open.
- 2026-08-03 — external audit separated known one-range/nonclosed-span spaceability from C5; found fatal inclusion reversal in arXiv:2510.11332v2 Remark 4.1 and froze hyperplane counterexample.
