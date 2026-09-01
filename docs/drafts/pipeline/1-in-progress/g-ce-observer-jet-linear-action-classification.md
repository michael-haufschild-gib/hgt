# G-CE observer-jet linear-action classification

- **ID:** GCE-OJ-L1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `rh-current-frontier-map.md` · G-CE
- **Statement:** `CompletedSourceObserverJetLinearActionBounded ↔ RiemannHypothesis`.

## Goal

Kill absolute observer-jet action as an independent G-CE producer. Existing forward implication
closes RH; reverse implication would show the producer is exactly RH, forcing any surviving G-CE
proof to use signed Green cancellation rather than an absolute `ℓ¹` history envelope.

## Gates

- [x] 0 → 1 in-progress: literal source, exact chain, discrete Hardy attack, internal/external audit
- [ ] 1 → 2 fully-proven: complete dependency-closed paper proof
- [ ] 2 → 3 formalized: Lean theorem, targeted build, axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Write harmonic charge `q_k` as `a_k r_k`, where `a_k` is the square-root-clock source edge and
`r_k` is harmonic-edge/square-root-edge. `RH ↔ MobiusDivisorSquareRootAbelBounded` gives
`|Σ_{k≤N} a_k|=O(N)`. Prove the new discrete Hardy–Green estimate

`|Σ k q_k| + Σ_{j<N}|Σ_{k>j}(k-j-1)q_k|/√(j+1)=O(N)`.

Use finite Abel summation, `r_k=O(k^{-3/2})`,
`|r_{k+1}-r_k|=O(k^{-5/2})`, and `Σ_{k≤N}k^{-1/2}=O(√N)`.

## Novelty audit

- Internal corpus: no observer-action converse or exact tail-kernel theorem found; only the forward
  G-CE consumer, second-formation completion, and RH-equivalent square-root Abel prefix.
- Literature through 2026-08: weighted Hardy/Copson theory covers generic positive operators, but
  no collision found for this signed completed prime–polar–Gamma source or this exact equivalence.

## Log

- 2026-09-01 — exact conjecture frozen after corpus and literature audit.
