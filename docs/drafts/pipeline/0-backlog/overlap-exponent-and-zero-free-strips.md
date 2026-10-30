# Overlap exponent and zero-free strips

- **ID:** overlap-exponent-and-zero-free-strips
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** fixed-overlap positivity (CACT/RAPT) and the SHA overlap laws; CAF Q8 (strip precision).
- **Statement:** For a profile with `|φ̂(ξ)|² ≍ |ξ|^{-2k}`, eventual complete-Weil positivity at overlap
  `c_N = (log N)^θ` is equivalent to the absence of zeros with `Re ρ > 1/2 + δ(θ)`, for an explicit
  decreasing `δ(θ)`; unconditionally it holds for `θ < 1/(2k + 1/2)` (the trivial strip).

## Mechanism (heuristic)
Top-localized smooth vectors carry alias energy `A(c) log N`, `A(c) = (c/M) Σ_{j≠0} |φ̂(2πjc)|² = −cE'(c)`,
and smooth energy `cq W(h)/∫h²` with `h` supported on the window `n ≥ N/c` of log-length `log c`.
An off-line zero `1/2 + δ + iγ` gives `W(h)/∫h² ≍ −c^{2δ}` on that window, visible once
`A(c) log N ≲ c^{1+2δ}`. The reserve/quasimode proof of positivity needs `log N ≫ C(c)/β(c)`, which
with the trivial bound `δ ≤ 1/2` reproduces the same exponent: any unconditional gain in `θ` is a
zero-free strip.

## Log
- 2026-10-30 — recorded.
