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
| 3 | [03-hole-free-accessible-tip.md](03-hole-free-accessible-tip.md) | **OPEN** | For overlapping filled Julia sets `K₁ ∩ K₂ ≠ ∅`, find a point of `J₁ ∖ K₂` on the boundary of the unbounded component of `ℂ ∖ (K₁ ∪ K₂)` with a neighborhood free of holes of the union. Automatic when `K₁ ∩ K₂ = ∅`. | Algebraic independence of Böttcher germs, connected and mixed pairs (via the root-limit pigeonhole route). |

The one remaining *deep-but-proven* literature input (not an open problem): smooth-piece
rigidity for quadratic Julia sets — a relatively open subset of `J_c` inside a smooth curve
forces `c ∈ {0, −2}` (Eremenko–van Strien; alternatively Montel blow-up + Fatou
classification). Formalizing it is large but standard execution, tracked as a task epic,
not listed here.
