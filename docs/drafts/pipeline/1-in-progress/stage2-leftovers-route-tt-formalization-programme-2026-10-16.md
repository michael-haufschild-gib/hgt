# Programme: formalize every stage-2 card in `2-fully-proven/leftovers` and `2-fully-proven/route TT`

- **ID:** stage2-leftovers-route-tt-formalization-programme-2026-10-16
- **Stage:** 1-in-progress (tracker; it is not itself a theorem card)
- **Goal:** every proven theorem on the eleven cards below gets an unconditional Lean proof (standard
  axioms only, no premises standing for analytic inputs), wired into its umbrella and audited with
  `lake env lean`; then each card moves to `3-formalized`.

## Rules in force
- Build one Lean process at a time, foreground; `lake env lean <file>` for audit, `lake build --old +M`
  only when an olean is needed; no umbrella or full builds; wire by `cat >>` append.
- No computations; no heartbeat raising; scratch files in the session scratchpad.
- Search the corpus before writing any new declaration.

## Card ledger

| # | card | paper content | Lean state at start (2026-10-16) | next step |
|-|-|-|-|-|
| 1 | leftovers/finite-weil-adjacent-nodal-transport | adjacent coupling for every strictly increasing node family | canonical log nodes only (`WeilLogShift*` chain, ~1400 lines); general prefix sign `finiteWeilNodalPrefix_sign` | general-node modules |
| 2 | leftovers/lee-yang-prime-pivot-dual-spectrum | spin partition, spectrum, converse chain, wall bound, signed coefficient | two-wall arithmetic core + spin-word forcing | spectrum classification, converse, `2^r < M`, coefficient polynomial |
| 3 | route TT/tt-boundary-quadratic-norm-orientation | C78 norm/trace orientation at the boundary | `/tmp` drafts lost; C75–C77 modules exist | rebuild modules from C75/C76/C77 |
| 4 | route TT/route-tt-structural-theorems-2026-10-14 | T1–T7, L1–L14 | T4 corpus lemma, T1 at convexity rung, T7, L10, L12 §2, L13 | audit each item; T3, T2, L1, L3 … |
| 5 | leftovers/weil-cone-pole-duality-anatomy | (A) modular/Dirichlet fat cones, (B) factorization, (C) function fields | Krein–Milman reduction; Dirichlet symbol positivity (CANNOT-539) | Weil functionals for L(s,f), L(s,χ), curves |
| 6 | leftovers/twisted-minimum-principle | primal TMP construction (C1)–(C4), Steps 1–6 | TMP proved by dual route; Steps 1, 5 pieces | Dirichlet problem on modular strip, corner Martin kernel, Green identity |
| 7 | leftovers/smooth-stein-order-two-autonomous-ade-frequency-rank | Stein surface minimal hull dim ≤ 2 | none | CR/contact geometry, Levi-flat obstruction, Weinstein (Taubes) |
| 8 | leftovers/nonvacuous-independence-and-polarization-import-law | B′ clauses 1–3 | clauses 1–2 proved (`exists_finiteIndex_small_eigenvalue`) | clause 3: Selberg zeta zero at s_j |
| 9 | leftovers/verified-height-one-zero-turing-extension | RH through T₁ = T₀ + 111/256 | consumer theorems only | conflicts with "no computations" (needs Platt–Trudgian + Turing certificate) |
| 10 | leftovers/route-e-cofactor-amplified-e3-token-supply | E₃ token supply | elementary layers, MT mean-square bricks | Matomäki–Teräväinen Thm 1.2 |
| 11 | leftovers/route-e-forbidden-support-e3-stability | MT all-interval E₃ with forbidden support | elementary perturbation layer | Matomäki–Teräväinen Thm 1.2 |

## Log
- 2026-10-16 — ledger created after reading all eleven cards. Started card 1.
