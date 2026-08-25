# Route-P irregular-RH det₂ correction ideal wall

- **ID:** IRH-P-DET2-CORRECTION-WALL
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION
- **Source:** full all-depth Route-P balanced Stokes carrier; Xi ordered reciprocal spectrum;
  irregular-RH regularized Fredholm transport
- **Statement:** Every additive correction relocating an arbitrary bounded channel image of full
  Route P to Xi is Hilbert--Schmidt but lies outside weak Schatten-one.

## Goal

Identify exact operator ideal forced on surviving irregular-RH transport after closure of all
trace-class relocation mechanisms. This is source-specific: no Xi-derived data may enter Route-P
carrier or bounded channel maps.

## Gates

- [x] 0 → 1 in-progress: exact correction fixed; corpus and primary-literature audits complete
- [x] 1 → 2 fully-proven: dependency-closed proof and hostile audit
- [x] 2 → 3 formalized: Lean theorem, direct module check, umbrella wiring, new-axiom audit
- [ ] 3 → 4 publication-ready: standalone note and external novelty review pending

## Audit

- `[CORPUS]` Full Route-P balanced carrier and every bounded left/right channel image belong to
  weak `S₁` by `routePPrimitiveGammaJuliaLogBalancedOperator_boundedChannel_memWeakSchattenClass_one`.
- `[CORPUS]` Weak `S₁` embeds into every ordinary `S_q`, `q>1`, by
  `MemWeakSchattenClass.memSchattenClass_of_lt`; hence every bounded channel image is `S₂`.
- `[CORPUS]` Xi belongs to `S₂` by `xiOrderedSignedPrimeOperator_memSchattenClass_two`, but not
  weak `S₁` by `xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one`.
- `[CORPUS]` Searches for `Xi RouteP Hilbert Schmidt correction`, `weak Schatten correction det2`,
  and `full RouteP correction ideal` found no exact correction-classification theorem.
- `[LITERATURE]` Bertola--Cafasso's Riemann--Hilbert treatment records ordinary Fredholm
  determinants for trace-class kernels and Carleman `det₂` for Hilbert--Schmidt kernels, including
  the trace-class multiplicative anomaly.
- `[LITERATURE]` Bertola's Malgrange-form construction identifies RH tau functions with Fredholm
  determinants of integrable operators. Bothner--Baik-type block RHPs use regularized determinants
  when off-diagonal blocks are Hilbert--Schmidt.
- `[LITERATURE]` No paper located classifies a Route-P-to-Xi correction or its weak-`S₁` boundary.
- `[NOVELTY STATUS]` `[BRIDGE]`: standard ideal algebra applied to corpus-specific irregular-RH
  carrier and actual Xi reciprocal spectrum; no external-priority claim.

## Exact theorem `[PROVED HERE]`

Let `B` be full balanced Route-P operator on `H_P`, and let `X` be ordered signed reciprocal-Xi
operator on `H_X`. For every bounded `A : H_P → H_X` and `C : H_X → H_P`, define

```text
K(A,C) = X - A B C.
```

Then

```text
K(A,C) ∈ S₂  and  K(A,C) ∉ S_{1,∞}.
```

Thus every exact additive irregular-RH weld is genuinely genus-one: it admits `det₂`-scale
regularization but cannot be reduced to ordinary weak-trace or trace-class transport.

## Complete paper proof `[PROVED HERE]`

Fix bounded `A,C`, and write `S=A B C` and `K=X-S`. Full-carrier theorem gives
`S∈S_{1,∞}`. Weak-endpoint embedding with `1<2` gives `S∈S₂`. Independently, exact Xi
approximation-number asymptotics give `X∈S₂`. Since ordinary Schatten classes are additive and
closed under negation,

```text
K = X + (-S) ∈ S₂.
```

Suppose `K∈S_{1,∞}`. Weak `S₁` is additive, so `S+K∈S_{1,∞}`. But

```text
S + K = S + (X-S) = X,
```

contradicting `X∉S_{1,∞}`. Therefore `K∉S_{1,∞}`. Both conclusions hold for every bounded
`A,C`; no spectral alignment or diagonal structure is used.

## Hostile audit

- Arbitrary mixing: closed for bounded non-diagonal, non-unitary, infinite-rank `A,C`.
- Positive depth: closed because `B` is literal all-depth carrier.
- Hilbert--Schmidt scale: `S₂` is proved from ideal membership, not compactness.
- Endpoint sharpness: correction itself is outside weak `S₁`, stronger than non-trace-class.
- Source purity: `A,B,C` contain Route-P data only; Xi appears solely in demanded target.
- Nonlinear monodromy escape: survives; claim concerns exact additive correction.
- Xi-derived source escape: excluded by source-purity rule, not claimed impossible mathematically.

## Positive survivor

- **Exact new insight:** Any viable additive irregular-RH weld has a forced nonzero genus-one
  counterterm. It cannot hide in positive-depth Stokes tail or ordinary Fredholm renormalization.
- **Remaining open core:** Construct this Hilbert--Schmidt/non-weak-`S₁` correction from intrinsic
  irregular monodromy or enhanced-sheaf data, prove its `det₂` tau function equals completed Xi,
  and obtain RH-bearing self-adjointness/positivity without importing Xi spectral data.
- **Status:** formalized in
  `RoutePPrimitiveGammaJuliaLogDetTwoCorrectionIdealWall.lean`; direct module check and
  new-declaration axiom audit pass. Separate Lake target build omitted because immediately prior
  exact-target build demonstrated a 13,283-job dependency replay; no large rebuild repeated.

## References

- Marco Bertola and Marco Cafasso, *Riemann--Hilbert approach to multi-time processes: the Airy
  and the Pearcey case*, Appendix B, regularized Fredholm determinants.
- Marco Bertola, *The Malgrange Form and Fredholm Determinants*, SIGMA 13 (2017), 046,
  https://doi.org/10.3842/SIGMA.2017.046

## Log

- 2026-08-24 — corpus and primary-literature audit; exact correction ideal conjecture stated;
  moved to `1-in-progress`.
- 2026-08-24 — complete ideal-theoretic proof and hostile audit; moved to `2-fully-proven`.
- 2026-08-24 — formalized forced `S₂ \ S_{1,∞}` correction classification and Hilbert--Schmidt
  corollary; direct Lean check passes; all four new theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`; wired into `RHTower.lean`; moved to `3-formalized`.
