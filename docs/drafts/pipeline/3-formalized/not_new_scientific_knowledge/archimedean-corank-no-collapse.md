# The archimedean corank does NOT collapse — the seam is the flow-dim(1) vs corank(∞) gap

- **ID:** archimedean-corank-no-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — Door-2 grade **BRIDGE** (classical valuation theory + product formula)
- **Priority:** FOUNDATIONAL (settles the archimedean-generator "decision card")
- **Source:** the proven negative half of `../5-failed/archimedean-corank-collapse.md` (Professor, 2026-06-19);
  builds on `function-field-holonomicity-degeneration.md` (#121, corank=1 over F_q), the product formula
  (#70/#90), `corank-seam-invariant.md` (#125).

## Statement
> **Theorem.** Let `Λ` be the relation lattice of the prime-multiplier datum `{g_p=1/p}` over ℚ
> (`corank = rank` of the value group `⟨log p⟩ = ∞`), and `Λ⁺` its enrichment by the archimedean generator
> `∂_s = −Σ_p(log p)θ_p` (and, optionally, the FE involution `s↦1−s`). Then **`corank(Λ⁺) = ∞`**: no finite
> archimedean enrichment collapses the corank. In particular the "missing single Frobenius" is **NOT** `∂_s`.

## Proof (three equivalent forms)
1. **Valuation.** The product formula `log|x|_∞ = −Σ_p(ord_p x)log p` makes the archimedean value a
   *dependent* function of the prime data ⟹ the enriched value group has the same rank `∞`.
2. **Lattice/Lie.** `∂_s = −Σ(log p)θ_p ∈` completion of `⟨θ_p⟩`, so `⟨θ_p,∂_s⟩=⟨θ_p⟩` (∞-dim); the single
   product-formula relation eliminates `∂_s`, returning ∞ independent `{θ_p}`.
3. **Impossibility core.** Collapsing `∞→1` needs `∞−1` independent relations among `{θ_p}`; the archimedean
   enrichment supplies only finitely many. Finitely many relations cannot collapse an ∞-independent system
   (the `{log p}` are ℚ-independent by unique factorization, and `∂_s` *uses* that independence). ∎

## The sharp structural content
- **Two orthogonal invariants:** the **flow-dimension** (#archimedean derivations = 1, one `∂_s`) and the
  **multiplier-corank** (prime value-group rank = ∞). They **coincide over F_q** (`=1`, the rank-1 value
  group ⟨q⟩, a genuine single Frobenius) and **split over ℚ** (`1` vs `∞`).
- **The seam = the gap** between flow-dim (1) and corank (∞): `0` over F_q (coincidence), `∞` over ℚ. `∂_s`
  realizes the `1`; it never collapses the `∞`. So the seam is **worse than "one missing Frobenius"** — a
  genuinely ∞-dimensional object. Realizing a single base would require the F₁/absolute object (the open D5
  frontier), which `∂_s` is not.
- **Door-5 (F_q recovery):** corank stays 1 over F_q (value group ⟨q⟩, rank 1) — consistent; F_q is the
  rank-1 coincidence.

## Gates
- [x] 0 → 1 / 1 → 2: proved (exact linear algebra over the ℚ-independent `{log p}` + product formula). BRIDGE.
- [x] 2 → 3 formalized: Lean — reuse `linearIndependent_log_primes` and #121's `Λ_ff = ker deg`; the theorem
  is `rank(value group ⟨log p⟩ ∪ {archimedean, dependent}) = ∞`. Clean Tier-A candidate.

## Cross-references
- `../5-failed/archimedean-corank-collapse.md` — the falsified conjecture this is the proven negative half of.
- `corank-seam-invariant.md` (#125), `corank-transcendence-continuation-bridge.md` (#122),
  `bucket-the-seam-archimedean-obstruction.md`, `bucket-archimedean-generator.md`.

## Log
- 2026-06-19 — Professor: split from the falsified `archimedean-corank-collapse` decision card. The collapse
  `∞→1` is impossible (finite archimedean relations cannot collapse ∞-independent primes); the seam is the
  flow-dim(1)/corank(∞) gap, F_q being the rank-1 coincidence. BRIDGE; confirms the charter's "seam worse than
  one missing Frobenius" and the F₁/D5-open-frontier picture.

## Cross-ref addendum — 2026-06-19 (Professor + DeWitt synthesis, chat 400/401)
The flow-dim/corank gap is one half of a clean **F₁ criterion**: `F₁ ⟺ (D=0, flow/realization face) ∧
(corank finite, DSS face)`. Over F_q both → 1 (single Frobenius, coincide); over ℚ they split (flow-dim 1 via
∂_s, corank ∞), with the **corank-∞ face strictly dominant** — even with D=0 (DeWitt's ω/index flow face
solved), F₁ fails because corank stays ∞ (this card). So the realization axis (#191, flow) is necessary but
not sufficient; the binding obstruction is the DSS/corank-∞ side. This card is the corank half; DeWitt's
ω/one-sided-ladder/index is the flow half (#191). Together they make the #191 RH↔DSS decoupling precise.

## Lean certification - 2026-06-19 (Leaner)

Formalized in `formal/GaloisForLFunctions/RHTower/ArchimedeanCorank.lean` and imported by `formal/GaloisForLFunctions.lean`.

Lean theorem surface matching the paper proof:
- `primeLogFiniteSlice_linearIndependent`: finite prime-log slices remain `Q`-linearly independent.
- `primeLogFiniteSlice_finrank`: every finite prime slice has full rational rank.
- `archimedeanFiniteGenerator_mem_primeLogSpan` and `primeLogSpan_insert_archimedean_eq`: a finite archimedean/product-formula generator already lies in the prime-log span and adjoining it does not change that span.
- `primeLogFiniteSlice_finrank_with_archimedean_unbounded`: finite-slice ranks remain unbounded after adjoining a dependent archimedean generator.
- `primeLogFullSpan_rank` and `primeLogFullSpan_rank_with_archimedean`: the full prime-log span has rank `Cardinal.mk Nat.Primes`, and adjoining a finite dependent archimedean generator leaves that rank unchanged.

Verification run:
- `cd formal && lake env lean GaloisForLFunctions/RHTower/ArchimedeanCorank.lean`
- `cd formal && lake build GaloisForLFunctions`
- `bash scripts/check_axioms.sh` (PASS: 335 audited theorem outputs; only `[propext, Classical.choice, Quot.sound]`; no `sorry`)
