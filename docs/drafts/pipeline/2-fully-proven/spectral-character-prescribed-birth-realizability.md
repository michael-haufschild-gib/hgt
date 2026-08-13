# Spectral-character activity has exact prescribed-birth realizability

- **ID:** spectral-character-prescribed-birth-realizability
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `formal/GaloisForLFunctions/HTGeometry/ValuatedSpectralCharacterLaw.lean`
- **Statement:** For every projective character `k` and every `r : ℕ`, a spectral jet making `k` active with birth order exactly `r` exists iff `k ≠ 0`.

## Goal

Close the existential side of the `SpectralCharacterActive` interface sharply. Activity cannot be
proved for arbitrary supplied jets, but every and only nonzero projective character can be realized
as active, at any prescribed temporal depth.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Classification

- **Tag:** `[BRIDGE] [PROVED HERE]`
- **Novelty verdict:** `REDISCOVERED` as mathematics. The construction is a coordinate functional;
  corpus value is the sharp universal interface law.
- **Dependency status:** closed; only finite support and injectivity of `ℤ → ℂ` are used.

## Paper proof

Let `k` be a projective character.

If a jet makes `k` active, then `k ≠ 0`: evaluation of every additive character functional at the
zero character is zero, contradicting activity.

Conversely suppose `k ≠ 0`. Since `k` is finitely supported, choose a label `i₀` with coefficient
`k(i₀) ≠ 0`. For prescribed `r`, define

`jet(n,i) = 1` when `n = r` and `i = i₀`, and `jet(n,i) = 0` otherwise.

For every `n < r`, pairing this jet with `k` is zero. At `n = r`, pairing is exactly the complex
cast of `k(i₀)`, hence is nonzero. Therefore `k` is active and the least nonvanishing order is
exactly `r`. This proves both directions. `[PROVED HERE]`

## Hostile review

- **Zero-character obstruction:** retained exactly; no false universal activity theorem is claimed.
- **Projective-charge condition:** irrelevant to construction but preserved because `k` remains in
  the projective-character subtype.
- **Infinite label type:** harmless; only one selected coordinate is used.
- **Birth-order exactness:** all earlier jets vanish, not merely the selected coefficient.
- **Overclaim check:** law realizes an abstract spectral jet. It does not assert that an arbitrary
  analytic or physical model realizes every character.

## Door passport

- **Door-1:** classifies the second-highest live Prop interface from the corpus audit.
- **Door-2:** no external novelty claim; elementary coordinate separation.
- **Door-3:** exact Lean construction identified; formalization pending.

## Log

- 2026-08-13 — source audit found 24 consumers and no activity producer.
- 2026-08-13 — corpus search found structural activity consequences but no realizability theorem.
- 2026-08-13 — complete paper proof and hostile review; advanced to `2-fully-proven`.
