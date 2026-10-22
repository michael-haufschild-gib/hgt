# HB physical-Jost biorthogonal normalization no-go

- **ID:** HB-PJBN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / route-class no-go
- **Statement:** Canonical left-QNM projection of every coefficient-linear BM connection state recovers only its input horizon coordinates; in particular it erases the literal Birmingham--Mokhtari Gamma/Jost coefficient and cannot supply missing HB orientation.

## Killed RH chain

`exact BM Gamma/Jost coefficient → canonical left-QNM response phase → reflected Peierls-current cancellation → RH`.

No divisor-placement, Ward, passivity, or RH premise is used.

## Audited frontier

- `[CORPUS]` `d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq` identifies Wronskian/Cramer normalizable entry with literal decaying Gamma/Jost coefficient.
- `[CORPUS]` Canonical regular/complementary left covectors are inverse rows of exact invertible horizon-to-AdS matrix.
- `[CORPUS]` Nonzero source-independent response leaves exactly critical-wall current zero locus.
- `[LITERATURE]` Birmingham--Mokhtari, arXiv:hep-th/0609028: exact hypergeometric topological-AdS QNM boundary problem, without nonlinear source projection or arithmetic FE reflection.
- `[LITERATURE]` Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935v3, Eq. (57): QNM excitation coefficient is a bilinear projection divided by mode bilinear norm and is normalization-independent; completeness is not established.
- `[LITERATURE]` Spiers--Pound--Moxon, arXiv:2305.19332 (2026 revision), Ma--Yang, arXiv:2401.15516, and Singh--Suneeta, arXiv:2512.00943 (2026 revision): nonlinear source/amplitude calculations do not derive universal FE-odd source law.

## Paper theorem and proof

Write exact connection columns as `v_R=(a_R,b_R)`, `v_C=(a_C,b_C)` with
`D=a_R b_C-b_R a_C≠0`, and canonical dual rows

`ell_R(S,T)=(S b_C-T a_C)/D`,

`ell_C(S,T)=(a_R T-b_R S)/D`.

For all `c_R,c_C∈ℂ`, direct determinant expansion gives

`ell_R(c_R v_R+c_C v_C)=c_R`,

`ell_C(c_R v_R+c_C v_C)=c_C`.

For regular matching mode, exact Gauss theorem identifies `b_R` with literal Gamma/Jost coefficient. Taking `c_C=0` proves matching projection is `c_R` and cross projection is zero, so its phase and modulus disappear. For global `c_R`, corrected reflected current is existing source-independent current:

`current(q)=0 ↔ c_R=0 ∨ Re(q)=1/2`,

and universally `current=0 ↔ c_R=0 ∨ RH`. Thus nonzero physical Jost response is only a receiver.

## Hostile verdict and positive survivor

- Abstract normalization cancellation is known linear algebra and explicit in QNM projection literature.
- Exact BM Gamma/Jost specialization plus full coefficient-linear HB route elimination is new local delta.
- **Killing mechanism:** inverse-row biorthogonality cancels complete connection matrix.
- **Positive survivor:** exact horizon-coordinate recovery. Any genuine selector must occur in source-dependent horizon coordinates before dual normalization, or use nonlinear/cross-channel/renormalized pairing not reducible to inverse-row extraction.
- Verdict: `[LEAN-PROVED]` route-class kill; broader scientific priority not claimed.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMPhysicalJostBiorthogonalNormalizationNoGo.lean`
- Final theorem: `RHTower.d4HBPhysicalJostBiorthogonalNormalizationRouteKilled`
- Premise-free closed proposition: `RHTower.D4HBPhysicalJostBiorthogonalNormalizationRouteKilled`
- Direct `lake env lean` passed.
- Targeted build passed: `11916/11916` jobs.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Wired into `GaloisForLFunctions/RHTower.lean`; no umbrella build run.
- Formal lint finds module reachable and no forbidden declarations; unrelated shared-worktree unreachable-module errors remain.

## Gates

- [x] 0 → 1 exact conjecture and RH chain
- [x] 1 → 2 dependency-closed paper proof
- [x] 2 → 3 exact Lean theorem, direct check, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: not claimed

