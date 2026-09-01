# FZZ torus holonomy Fourier zero-mode no-go

- **ID:** fzz-torus-holonomy-fourier-zero-mode-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · FZZ-P source-specific torus Ward core
- **Statement:** Squared cycle-`n` odd β/γ holonomy has exact compact support `{0,±2n}`. Haar zero mode is `-1/2` for `n≠0`; every continuous weighted average depends only on source charges `0,±2n`; normalized marked coefficients recover the reciprocal radial holonomies. `[PROVED HERE]`

## Goal

Kill this proposed RH chain:

`literal parity-Mellin Γζ divisor ρ`
→ `canonical torus twist`
→ `unmarked physical torus replica-area holonomy average`
→ `cycle-(1,2) averaged Krein chamber`
→ `pointwise cycle-(1,2) chamber`
→ `Re ρ = 1/2`
→ `RH`.

The intended killing theorem is that the averaged chamber is automatic at every radial twist, so it cannot imply the pointwise chamber. The required positive survivor is the exact minimal Fourier marking that retains radial information.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact attack, RH-chain passport
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axioms audited
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate

## Corpus basis

- `higherGenusBetaTwist_mul_gammaTwist`: β/γ multipliers are reciprocal.
- `fzzHigherGenusOddHolonomy_eq_sinh`: odd response is `sinh(2πin·twist)`.
- `torusJacobianTwist`: `twist=s₁τ+s₂`; `torusJacobianTwist_im`: radial component is `s₁τ.im`.
- `fzzHigherGenusCyclePairKreinSign_iff_im_eq_zero`: pointwise cycles `n,2n` select zero radial twist.
- `torusReplicaTangent_monodromy_invariant_iff_neutral`: physical torus replica tangent descends exactly in neutral sectors.
- Corpus searches found no compact-holonomy Fourier classification or averaged selector theorem.

## Literature audit through 2026-08

- Hikida–Schomerus, arXiv:0805.3931, (4.14)–(4.15), (A.4)–(A.6): genus-`g` cigar correlators integrate all complex twists `d²λ_l`; twists are gauge holonomies and must be integrated out.
- Halder–Jafferis, arXiv:2402.00932v3, §3.2.3: leading entropy computation is genus zero; torus one-point of the nonlocal area operator is only expected, and branch-cut issues are avoided through the exponentiated operator.
- Targeted primary-source searches found no torus area Ward law, no squared odd-holonomy zero-mode theorem, and no marked-mode classification.

## Theorem `[PROVED HERE]`

Let

`H_n(s₂)=sinh(2πin(s₁τ+s₂))`, `n∈ℤ`.

For Fourier charge `m∈ℤ`, including the colliding case `n=0`,

`∫₀¹ exp(-2πims₂) H_n(s₂)^2 ds₂`

equals

`(B_n²/4)·1_{m=2n} + (G_n²/4)·1_{m=-2n} - (1/2)·1_{m=0}`,

where `B_n=exp(2πin s₁τ)` and `G_n=B_n⁻¹`.

Hence for `n≠0`: zero mode is `-1/2`; normalized marked coefficients are `B_n²,G_n²`, multiply to `1`, and positive marked coefficient has unit norm iff radial monodromy vanishes.

For continuous background `A`,

`∫₀¹ A H_n² = (B_n²/4) Â(-2n) + (G_n²/4) Â(2n) - (1/2) Â(0)`.

Hostile tests:

1. Full coefficient formula handles `n=0` frequency collisions; only nonzero-cycle corollaries exclude it.
2. Complex `τ` and arbitrary real `s₁` must remain allowed.
3. Both `n` and `-n` must obey the same case classification.
4. Zero mode must make cycles `n,2n` automatically real/nonpositive off wall.
5. Marked coefficient modulus selects zero radial monodromy for `n≠0`, rather than merely being nonzero.

## Proof

Reciprocity `B_nG_n=1` and `H_n=(B_n-G_n)/2` give

`H_n(s₂)^2 = (B_n²χ_{2n}(s₂)+G_n²χ_{-2n}(s₂)-2)/4`.

Integer-character orthogonality on `[0,1]` proves the coefficient formula, including frequency collision at `n=0`. Linearity gives the weighted resonance law. For `n≠0`, zero-mode projection gives `-1/2` at cycles `n,2n` for every twist; choosing `(n,s₁,τ)=(1,1,i)` supplies explicit nonzero radial monodromy. Marked coefficients are the reciprocal radial squares; their product and norm criterion follow from β/γ reciprocity and the existing radial-monodromy norm equivalence.

## No-go closure

- **Killed arrow:** unmarked Haar-averaged squared holonomy Ward `→` pointwise cycle chamber. Averaged chamber holds at explicit nonzero radial monodromy.
- **Killed class:** every continuous torus background with Fourier gaps at `±2n`; only blind zero mode remains.
- **Strongest positive survivor:** exact resonant charges `±2n`; normalized coefficients retain reciprocal radial holonomy and unit norm selects wall.
- **RH consequence:** cycles `1,2` require physical replica-area source modes at `±2,±4` with required signs, or a singular/branch-cut source outside continuous-background law; then reflected divisor incidence remains.
- **Novelty audit:** corpus and targeted primary literature through 2026-08 contain no exact three-frequency classification, weighted resonance law, or this no-go/survivor boundary.
- **Lean certificate:** `GaloisForLFunctions.RHTower.FZZCigarParityTorusHolonomyFourierResonanceNoGo`; targeted `lake build` PASS; key declarations use only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.

## Log

- 2026-09-01 — C1 (all neutral observables twist-blind) rejected: interacting neutral determinants may depend on twist.
- 2026-09-01 — C2 (charge-conjugation symmetry kills selector) rejected: selector uses an even square.
- 2026-09-01 — C3 frozen after corpus-first reconstruction and primary-literature audit.
- 2026-09-01 — C3 proved, strengthened to weighted resonance law, formalized, and targeted-build audited.
