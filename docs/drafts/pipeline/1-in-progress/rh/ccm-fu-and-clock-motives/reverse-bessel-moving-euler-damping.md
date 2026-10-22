# Moving-degree reverse-Bessel packets recover Euler damping

- **ID:** ccm-reverse-bessel-moving-euler-damping
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `rh-current-frontier-map.md` · CCM moving-degree source compactness core
- **Statement:** For the normalized reverse-Bessel polynomial `R_n`, the Euler-damped packet obeys
  a two-rate bound
  `exp(-x) R_n(x) <= 2^r exp(-x/2) + (3/2)^r exp(-x/3)`,
  where `r = ceil(n/2)`; hence at `x = 6n log m` every Euler atom is exponentially small in degree
  while retaining a summable positive power of `m`.

## Goal

Close the exact obstruction left by fixed-frequency blindness.  The corpus bound `R_n(x) <= exp x`
cancels all Euler damping and cannot be summed after multiplication by `Lambda(m)m^{-1/2}`.  This
moving-degree estimate retains one-half or one-third of the damping and is designed to combine with
the new Gamma half-log reserve.

## Gates

- [x] 0 → 1 in-progress: corpus searched first; source-pure recurrence; dependency-closed paper proof
- [ ] 1 → 2 fully-proven: hostile constant/index audit and completed-source assembly
- [ ] 2 → 3 formalized: closed Lean theorem, targeted leaf build and axiom audit
- [ ] 3 → 4 publication-ready: integrate into source-modular superselection manuscript

## Corpus boundary

Existing Lean has only `R_n(x) <= exp x`, fixed-`x` convergence to `exp x`, the exact coefficient
recurrence, and positive integral representation.  Targeted corpus search found no bound at
`x proportional to n`, no two-rate low/high coefficient split, and no retained Euler damping.
General large-degree reverse-Bessel asymptotics in the literature do not state this elementary
finite two-rate inequality.

## Proof

Put `p(n,j) = (b(n,j)/b(n,0)) j!`.  Then `0 <= p(n,j) <= 1` and

`p(n,j+1) / p(n,j) = 2(n-j)/(2n-j)`.

Let `r = ceil(n/2)`.  For `r <= j < n`, `n <= 2j`, so the displayed ratio is at most `2/3`.
Therefore `p(n,j) <= (2/3)^(j-r)` for every `r <= j <= n`.

Split `R_n(x) = sum_j p(n,j)x^j/j!` at `r` for `x >= 0`.

- On `j < r`, use `p <= 1` and `2^j <= 2^r`:
  `sum_{j<r} p x^j/j! <= 2^r exp(x/2)`.
- On `j >= r`, use geometric contraction:
  `sum_{j>=r} p x^j/j! <= (3/2)^r exp(2x/3)`.

Multiplication by `exp(-x)` gives the claimed two-rate law.  At `x = 6n log m`, the two terms are
`2^r m^(-3n)` and `(3/2)^r m^(-2n)`, so the prime-power sum retains strong absolute convergence
and decays exponentially with degree.  No asymptotic interchange or computation is used.

## Scientific consequence

Fixed-frequency blindness is not uniform on the moving Euler scale.  Reverse-Bessel coefficients
develop a deterministic geometric phase after half the degree, forcing Euler damping to reappear.
Together with the Gamma half-log reserve this makes a linear-in-degree completed-source positivity
horizon plausible; that would replace the current quadratic parabolic horizon.

## Log

- 2026-08-16 — Corpus-first audit isolated moving Euler damping; two-rate finite proof obtained;
  Lean formalization started.
