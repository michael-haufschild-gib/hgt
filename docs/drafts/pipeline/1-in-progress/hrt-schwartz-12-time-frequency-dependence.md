# Twelve time-frequency shifts of a Schwartz function are linearly dependent

- **ID:** `hrt-schwartz-12-time-frequency-dependence`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Faulhuber--Petersen--van Velthoven--Voigtlaender, arXiv:2608.05044v1
- **Statement:** `[LITERATURE]` There exist twelve pairwise distinct points `z : Fin 12 → ℝ × ℝ`, twelve nonzero coefficients `c : Fin 12 → ℂ`, and a nonzero `f : SchwartzMap ℝ ℂ` such that the corresponding time-frequency shifts satisfy `∀ t : ℝ, ∑ k, c k * exp (2 * π * I * (z k).2 * t) * f (t - (z k).1) = 0`.

## Goal

Formalize the exact counterexample to the Heil--Ramanathan--Topiwala conjecture as an unconditional, closed Lean theorem. No route assumptions, unchecked external certificates, new axioms, `sorry`, `admit`, `opaque`, or `unsafe` declarations are permitted.

## Gates

- [x] 0 → 1  in-progress: exact source theorem and fixed twelve-point construction identified
- [ ] 1 → 2  fully-proven: complete paper proof hostile-audited and every analytic/certificate dependency closed
- [ ] 2 → 3  formalized: Lean theorem `<pending>`, targeted module build green, lint and axiom audit pass
- [ ] 3 → 4  publication-ready: standalone theorem, proof map, and Lean certificate

## Approach

Audit existing Schwartz, modulation, translation, Fourier, fixed-point, and torus-Fourier infrastructure first. Reconstruct the paper's vector-Zak proof only after closing its quantitative matrix estimate without an external computational premise. Formalize exact Theorem 1.1, not a conditional support wrapper.

## Active proof state

- `[LITERATURE]` The paper proves the theorem through an explicit eleven-term Weyl polynomial with a Schwartz eigenfunction.
- `[OPEN CORE]` Replace Theorem 5.1's Arb-certified bound `sup_z ||B_*(z)-B_0(z)|| < 1/3` by a dependency-closed non-computational proof. The published proof verifies `B(x_j) < 0.328813` at 2048 rational centers using 256-bit Arb ball arithmetic; the paper does not supply a symbolic analytic replacement.
- `[CORPUS]` `SchwartzMap.compSubConstCLM` supplies translation on Schwartz space; `FieldOneArchimedeanWeylMultiplier.lean` supplies unit-modulus modulation; `Topology/MetricSpace/Contracting.lean` supplies Banach fixed points; `TorusTrigPolynomial.lean`, `TorusCharacterMean.lean`, and `SoninRapidFourierDecay.lean` supply relevant torus/Fourier pieces.
- `[LOCAL-RESEARCH]` Exact searches of `formal/`, Stages 2--3, and Stage 5 found no HRT theorem, scalar/vector Zak transform, or proof of the paper's certificate.
- `[LITERATURE]` Oussa, arXiv:2604.21228, provides Lean files for four-point HRT results only as consequences of an `HRTContext`; its eight analytic inputs are class fields explicitly left unproved, so it cannot satisfy this card's unconditionality gate.
- `[OPEN CORE]` After the quantitative bound closes, remaining Lean obligations are scalar/vector Zak unitarity and covariance, smooth compactly supported reference window, matrix cocycle and graph transform, smoothness of the fixed point, the two-torus small-divisor cohomological equation, and the smooth-Zak/Schwartz equivalence.
- `[BRIDGE]` Local Stone--Weierstrass infrastructure could yield an unspecified finite Weyl polynomial approximating the rank-one field. It does not control support cardinality by eleven and therefore cannot prove the exact twelve-shift theorem.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Not applicable; active route.
- **Strongest positive survivor:** Not applicable; active route.
- **New insight:** Pending.
- **Status:** Stage 1; paper theorem identified, quantitative certificate audit open.

## Log

- 2026-08-09 — created directly in Stage 1 after identifying arXiv:2608.05044v1 Theorems 1.1, 2.2, and the certified bound in Theorem 5.1.
- 2026-08-09 — internal/external frontier audited. Exact twelve-point route is blocked at the paper's computational certificate under the explicit no-computation rule; no Lean code was started before paper-proof closure.
