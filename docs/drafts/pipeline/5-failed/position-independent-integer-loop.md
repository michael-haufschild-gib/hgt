# Position-independent integer with an independent bound — conjecturing loop, closed

- **ID:** ULF-MUST130-001
- **Stage:** 5-failed (loop closed 2026-09-02; survivors in Lean)
- **Type:** CONSTRUCTION ATTEMPT (MUST-130) → NO-GO LAW
- **Task:** name an integer `I` defined without reference to zero positions, prove `I ≥ 1` at an
  off-line zero, and bound `I ≤ s < 1` by an estimate not passing through the target inequality
  (the Ferrero–Washington shape).
- **Verdict:** [NOT CONSTRUCTED] — every candidate class is killed by a theorem; the loop
  produced one new unconditional theorem (Li coefficients are never eventually negative) and
  the law that there is no archimedean universality.

## The Ferrero–Washington mechanism, exactly

`μ ≥ 1` is a *universal* statement (every coefficient of the Iwasawa series is divisible by `p`)
refuted by *one* explicit instance (a coefficient that is a unit, found by digit equidistribution).
Three ingredients: an integer defined independently of the conclusion (a valuation), a universal
consequence of the negation of the theorem, and one independent instance refuting it. The
`p`-adic world supplies the discontinuity (valuations jump) and the universality (a power series
divisible by `p` has all coefficients divisible).

## The loop (each candidate against the three ingredients)

| candidate `I` | position-independent | `I ≥ 1` off line | independent bound | killed by |
|---|---|---|---|---|
| zero counts in windows or half-planes; argument-principle / Toeplitz indices | ✓ | ✓ | slack `≥ log t` per integer | crowd (C1–C4, Selberg ledger) |
| Nyman–Beurling codimension `dim L²/closure(span{ρ(θ/x)})` | ✓ (a dimension) | ✓ (`= #` right zeros) | `< 1` is density, which is RH | receiver |
| signature (negative index) of Toeplitz forms of the Li moments | ✓ | ✓ | nonnegativity is the Carathéodory criterion, RH | receiver |
| escape multiplicity, ladder height, any indicator | ✗ (position) | ✓ | — | `EscapeMultiplicityOffLineIndicator` |
| `M(x)`, `lcm(1..n) = e^{ψ(n)}`, `⌊x⌋` and other arithmetic integers | ✓ | only through growth `Ω(x^β)`, *infinitely often* | bounding growth is RH | no universality (Landau gives `Ω`, not `∀x`) |
| sign of the Li coefficient `λ_n` (a `{±1}` datum computable from primes) | ✓ | `λ_n < 0` for a positive density of `n` | `λ_n ≥ 0 ∀n` is RH | **no universality**: off the line `λ_n > 0` for arbitrarily large `n` too (Lean, this loop) |
| Galois integers (`ζ_K(ρ) = 0 ∀K`, class numbers, ranks) | ✓ | ✓ | family averages return ζ's own explicit formula | family blindness |
| weights (`2θ ∈ ℤ` for the growth exponent of `M(x)`) | ✓ | ✓ | needs a cohomological degree | torsion law, six exponentials |
| continuous integer invariants of the divisor (indices of continuous families) | ✓ | — | constant on connected classes | `eq_of_continuous_int_valued` (corpus): locally constant integers cannot separate members of a path-connected class containing RH-true and RH-false divisors |

## The law extracted

**No archimedean universality.** The negation of RH implies statements of the form "infinitely
often" or "with positive density" (Landau's `Ω`-theorem; the sign pattern of `λ_n`; oscillation
of `ψ(x) − x`), never "for all `n`". The reason is structural: a real Dirichlet series or a real
sequence with a non-real dominant singularity oscillates, because the dominant contribution is a
mean-zero almost-periodic function. A `p`-adic power series with a dominant divisibility does not
oscillate. Hence the Ferrero–Washington shape has no archimedean transfer for ζ: a hypothesis
"off-line zero" is never over-determined in a way that one independent instance refutes.

**Theorem (Lean, `RHTower.LiSignOscillation`).** If RH fails then the paired Li coefficients
`2λ_n` are positive for arbitrarily large `n` (as well as negative for some `n`, the hard half of
Li's criterion). Unconditionally, the sequence `(2λ_n)` is never eventually negative. *Proof.*
Among the finitely many zeros whose Cayley representatives exceed a threshold, the dominant ones
have modulus `R > 1` and non-real directions `u_ρ`; simultaneous recurrence gives `n₀` with all
`u_ρ^{n₀} ≈ 1`, and the geometric sum `Σ_{k≤n₀} u^k = u(u^{n₀} − 1)/(u − 1)` is then small, so the
weighted cosine sum is negative at some `k₀ < n₀` (mean value on the torus). At exponents
`n + k₀` with `n` a recurrence time the dominant part of `−Σ m_ρ Re(v_ρ^{n+k₀})` is
`R^{n+k₀}` times a positive constant while all other zeros contribute a smaller exponential rate.

## No-go closure
- **Exact killing theorem/mechanism:** the table; the no-universality law (mean-zero oscillation
  of the dominant term), certified on the Li sequence by `not_eventually_re_xiLiPaired_neg`.
- **Strongest positive survivor:** `RHTower.LiSignOscillation` (`exists_re_sum_pow_neg`, mean
  value on the torus; `exists_ge_re_tsum_liTerm_pos`; `exists_ge_re_xiLiPaired_pos_of_not_riemannHypothesis`;
  `not_eventually_re_xiLiPaired_neg`).
- **New insight:** the archimedean obstruction to a direct anchor is oscillation, not size: the
  off-line signal in every integer-valued or sign-valued arithmetic datum is almost periodic with
  mean zero, so no single instance can refute it.
- **Status:** closed; a direct anchor would need a datum whose off-line signal is one-signed,
  and the dominant-singularity structure of real Dirichlet data forbids it (MUST-131).

## Log
- 2026-09-02 — loop run; law extracted; Li sign oscillation proved in Lean.

## Addendum 2026-09-02 — why one-signedness and position-independence conflict (MUST-132)

A one-signed off-line signal is obtained only by isolating a single zero, i.e. by twisting the
arithmetic datum with the zero's own frequency (`Λ(n) n^{−iγ}`: the term of `ρ` becomes
`x^{β}/β`, real and positive, and Turán's power-sum theorem makes it large in every window of
scales). That twist is position-dependent, and its "independent bound" at one scale is the
zero-free region at height `γ`, the target itself. So the two requirements of MUST-130 are
jointly unsatisfiable for data built from ζ: position-independent data oscillate with mean zero
(CANNOT-194); one-signed data are position-dependent twists. MUST-132: a producer must supply a
one-signed signal *without* knowing the frequency, which no functional of ζ's values does.
