# Open problems — external statements

Self-contained mathematical problems extracted from the formal Böttcher programme. Each is
stated for a mathematician with no project context; solving one (paper mathematics
suffices) completes an unconditional machine-checked theorem, since every reduction to
these statements is already formalized (Lean 4, axiom-clean, zero sorries).

| # | File | One-line statement | Unlocks |
|---|------|--------------------|---------|
| 1 | [01-fixed-scale-sector-connector.md](01-fixed-scale-sector-connector.md) | At ONE fixed scale near the repelling landing point β of a real dendrite Julia set, every shell basin point connects to the external-ray sector inside the disk of that scale. | Algebraic independence of Böttcher germs, both-connected (dendrite) pairs. |
| 2 | [02-cantor-julia-steering.md](02-cantor-julia-steering.md) | An analytic level-curve foliation admits a leaf avoiding a given Cantor quadratic Julia set (open case: dim ≥ 1). | Algebraic independence, general disconnected + mixed pairs. |

Both problems come with: known partial results (dimension counting solves the thin case of
#2; the ∀-scale → one-scale collapse of #1 is proven), closed-off dead ends, and concrete
attack routes (distortion/porosity — being attacked in-tree in parallel).
