# Positive annihilator accuracy forces left growth

- **Stage:** 1-in-progress
- **Source:** `logs/aal-conjecture-loop-2026-11-07.md`, Cycle 341.
- **Candidate:** If `P(s)=1+Σ a_n n^(-s)`, `a_n≥0`, is finite and `P(β+iγ)=0`, put `H(σ)=Σ a_n n^(-σ)`. For `σ₋<β<σ₊`, with `λ=(β−σ₋)/(σ₊−σ₋)`,
  `1≤H(β)≤H(σ₊)^λ H(σ₋)^(1−λ)`.
  Consequently `H(σ₊)≤ε` forces `H(σ₋)≥ε^(−λ/(1−λ))`.

The first inequality is the triangle inequality; the second is logarithmic convexity of a positive exponential sum. The corpus supplies `HTGeometry.expSum_le_rpow_mul_rpow` and positive two-prime annihilators. The remaining bridge must use their literal polynomial evaluations.

The worklog's strict claim `H(β)>1` is false for general positive Dirichlet polynomials: `1+2^β 2^(-s)` vanishes at `β+iπ/log 2` and has `H(β)=1`. Equality and the exact exponent should be retained in the formal statement. This obstruction limits positive annihilator amplification; it does not prove AAL.

- **Paper status:** elementary proof identified; literal polynomial bridge and equality example require audit.
- **Lean status:** not formalized.
