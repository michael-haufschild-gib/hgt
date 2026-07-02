# Open problems — external statements

Self-contained mathematical problems extracted from the formal Böttcher programme. Each is
stated for a mathematician with no project context; solving one (paper mathematics
suffices) completes an unconditional machine-checked theorem, since every reduction to
these statements is already formalized or in verified preparation (Lean 4, axiom-clean,
zero sorries).

| # | File | Status | One-line statement | Unlocks |
|---|------|--------|--------------------|---------|
| 1 | [01-fixed-scale-sector-connector.md](01-fixed-scale-sector-connector.md) | **REFUTED** ([01-answer.md](01-answer.md), verified) | Fixed-scale sector connector at the β landing point of a real dendrite Julia set. False: pulled-back Julia hairs bulge outward and crosscut every scale. A weakened factor-2 basis-family form survives as **fallback** (see banner in the file). | — (superseded by #3) |
| 2 | [02-cantor-julia-steering.md](02-cantor-julia-steering.md) | **ANSWERED** ([02-answer.md](02-answer.md), verified) | Statement A (angular steering past a Cantor Julia set) is TRUE for all disconnected pairs; Statement B (one-parameter foliation model) is FALSE. | Disconnected lane fully unblocked; remaining work is formalization only. |
| 3 | [03-hole-free-accessible-tip.md](03-hole-free-accessible-tip.md) | **ANSWERED** ([03-amswer.md](03-amswer.md), verified) | Hole-free accessible tip proven for the subclass `(c, −2)`, `−2 < c ≤ 1/4` real, via Janiszewski (connected `K₁∩K₂` ⟹ no holes) + the explicit tip `z₀ = i√(β+c)`. Correct — but the partner `−2` is exceptional, so this class feeds no independence pair; see banner in the file. | Two reusable methods (Janiszewski reduction; explicit imaginary-axis tip). Load-bearing case restated as #4. |
| 4 | [04-nonexceptional-hole-free-tip.md](04-nonexceptional-hole-free-tip.md) | **ANSWERED** ([04-answer.md](04-answer.md), verified) | Hole-free tip proven for the nonexceptional both-connected class `−3/4 < c₂ < c₁ < 0`: tip `z₀ = i·√(β₁+c₁)`, Jordan-curve (quasicircle) Julia set + Schoenflies exterior collar + imaginary escape ray ⟹ `B(z₀,r) ∖ (K₁∪K₂) ⊆ W`. | Both-connected pairs unblocked on an explicit class — **no open-math input remains in the q62 programme**; the rest is formalization (collar + rigidity endgame). |

The remaining *deep-but-proven* literature inputs (not open problems, tracked as task
epics): smooth-piece rigidity for quadratic Julia sets (Eremenko–van Strien / Montel
blow-up + Fatou) — now needed only for the interior-interior both-connected endgame, since
the dendrite-side endgame and the full single-coordinate transcendence
(`phiMero_transcendental_of_mem_mandelbrot`, all `c ∈ M ∖ {0,−2}`) are already
machine-checked via the disk-model natural boundary.
