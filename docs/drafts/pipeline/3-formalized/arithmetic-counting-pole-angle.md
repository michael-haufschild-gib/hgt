# Harmonic counts transport the prime gap through the pole angle

- **ID:** ACP-ANGLE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean checked)
- **Source:** arithmetic-counting-positivity.md; obstacles-summary.md §2.8, positive content of parity.
- **Statement:** Uniformly over sign gauges, the atomic prime gap retains the square of the normalized harmonic correlation; sparse prime flips therefore retain positive gaps.

## Goal

Supply a quantitative count-to-energy tool and determine whether a positive
selective margin alone identifies the untwisted source. This is an atomic-prime
theorem, not positivity of the complete continuous Weil form.

## Gates

- [x] 0 → 1: source-pure construction; corpus novelty search completed.
- [x] 1 → 2: dependency-closed paper proof below.
- [x] 2 → 3: Lean checks, transitive axiom audit and umbrella wiring.

## Paper proof [PROVED HERE]

Write `b_n = 1/sqrt(n)`, `H = sum_{n<=N} 1/n`, `S = sum omega(n)/n`,
`c = S/H`, and `M = sum x_n^2`. Let `omega(n)^2 = 1` and `x` be orthogonal
to `b`. The projected gauge vector `v = omega b - c b` has squared norm
`H - S^2/H`, and

`<omega x,b> = <x,v>`.

Cauchy–Schwarz gives

`<omega x,b>^2 <= M (H - S^2/H)`.

Consequently the harmonic variance of `sqrt(n) omega(n) x_n` is at least
`c^2 M`. This geometric factor is exact: the projected gauge vector attains
the Cauchy inequality whenever it is nonzero. It is not a claim that the
arithmetic gap itself attains this lower bound.

The corpus proves, for every positive `delta`, eventually uniformly in all
vectors `y`,

`D_N(y) >= (2 log 2 - delta) Var(y)`

and

`P_N(y) + (1 - delta) D_N(y) <= (log N - gamma + delta) ||y||^2`.

Apply both to `y = omega x`. Since `0 <= c^2 <= 1`, choosing `delta` small
relative to a prescribed `epsilon` proves

`P_N(omega x) <= (log N - gamma - (2 log 2)c^2 + epsilon) M`.

The horizon depends only on `epsilon`, not on the gauge, vector or harmonic
correlation. No convergence of `c` is assumed.

For the completely multiplicative gauge flipping a single prime `p`, the
negative coefficients occur only at multiples of `p`. The exact incidence
count gives

`sum_{n<=N, p|n} 1/n = H_{floor(N/p)}/p <= H_N/p`.

Thus `S >= (1 - 2/p) H_N`. For `p >= 3` this is positive, and the previous
inequality gives the unconditional hyperplane gap

`(2 log 2)(1 - 2/p)^2`.

Each such gauge is nontrivial at `p`, is multiplicative, and has the same
polar matching coefficient as the untwisted source (existing corpus theorem).
As primes grow, these certified gaps approach `2 log 2`. Therefore no fixed
threshold strictly below `2 log 2`, even together with multiplicativity and
polar matching, selects the untwisted source.

### Stronger parity pairing [PROVED HERE]

For a prime `p`, put `omega(n)=(-1)^{v_p(n)}`. Its negative coordinates are
exactly `p` times its positive coordinates. The inverse pairing divides a
negative coordinate by `p`, preserves the cutoff, and multiplies harmonic
weight by `p`. Therefore

`p(H_N-S_N) = H_{floor(N/p)}+S_{floor(N/p)} <= H_N+S_N`.

The last inequality counts the nonnegative summands `(1+omega(n))/n` on a
larger interval. Rearrangement gives the sharper floor

`S_N/H_N >= (p-1)/(p+1)`

for every positive horizon. Thus the gap paid by this count is

`(2 log 2)((p-1)/(p+1))^2`.

In particular the prime-two flip, unlike the Liouville flip at every prime,
retains gap `2 log 2/9`. The exact excess over the correlation floor is the
positive boundary count

`(p+1)S_N-(p-1)H_N = sum_{N/p < n <= N} (1+omega(n))/n`.

It lies between zero and `2(1+log p)`, by the corpus harmonic interval
bound. Dividing by `(p+1)H_N` proves that the harmonic correlation tends
exactly to `(p-1)/(p+1)`. This is sharpness of the counting floor, not a
claim that the resulting arithmetic gap lower bound is optimal.

This stronger branch was separately checked against the finite-flip and
harmonic-correlation searches. Existing finite-part theorems concern prime
Mertens sums and do not supply this finite-horizon pairing identity.

### Complete-source obstruction [PROVED HERE]

For the actual arithmetic weight `lambda_p(n)=omega_p(n) Lambda(n)`,
`|lambda_p(n)|=Lambda(n)` and `lambda_p(p)=-log p`. The corpus's unconditional
full-cone uniqueness theorem says a full-Weil-positive weight must equal
`Lambda` at every `n>=2`. Since `log p>0`, `lambda_p` is not full-Weil-positive.
Thus the near-maximal-gap examples fail the literal complete Weil sign, not
merely a proposed source-identification rule. This conjunction is new; the
full-cone uniqueness theorem itself is an imported result whose transitive
axioms must be checked before the conjunction is accepted.

## Novelty audit

The corpus already proves the sharp untwisted gap, zero Liouville gap,
preservation under full harmonic correlation and finite *coefficient* flips.
It also constructs finite *prime* flips and proves their polar matching and
finite-part deficits. Those are inputs, not new claims here. Searches for
intermediate harmonic correlation and sparse-prime hyperplane gaps did not
surface the uniform squared-angle transfer or its near-maximal nontrivial
multiplicative counterexamples. No claim of novelty relative to all literature
is made.

External context: comparison of multiplicative mean values is classical;
[Tenenbaum, *On effective mean-values of arithmetic functions*](https://arxiv.org/abs/2507.10483)
discusses that theory. The contribution here is the uniform transfer of a
literal harmonic count into the corpus's sharp prime-form gap and the
complete-source counterexample it yields, not a claim to have invented
multiplicative mean values or the elementary projection inequality.

## No-go closure

- **Rejected mechanism:** positive hyperplane gap plus multiplicativity and polar matching uniquely selects the von Mangoldt source.
- **Strongest positive survivor:** uniform squared-angle count-to-gap inequality, including a concrete nontrivial completely multiplicative family with gaps approaching the untwisted maximum.
- **New insight:** separation from Liouville is weaker than selection; finite-part rigidity or another arithmetic reading is still needed even after a gap has been paid.
- **Status:** paper proof and exact Lean formalization complete. The overall programme remains active.

## Lean declarations and verification

All modules are in `GaloisForLFunctions/ArithmeticCountingPositivity/`.

| Module | Principal declarations |
|---|---|
| `HarmonicCorrelationPaysThePrimeGap.lean` | `harmonicCorrelation_sq_mul_mass_le_variance`, `gaugeWitness_attains_variance_bound`, `eventually_prime_gap_ge_squared_correlation` |
| `SparsePrimeFlipsRetainPositiveGaps.lean` | `harmonicMass_multiples`, `every_submaximal_gap_has_a_nontrivial_multiplicative_twin` |
| `PrimeParityPairing.lean` | `prime_parity_pairing`, `prime_parity_boundary_bounds`, `primeFlip_harmonicCorrelation_tendsto`, `primeFlip_hasHyperplaneGap`, `two_adic_parity_has_gap_but_liouville_does_not` |
| `NearMaximalGapsDoNotForceWeilPositivity.lean` | `primeFlip_exists_negative_complete_test`, `near_maximal_gaps_do_not_force_weil_positivity` |

Each leaf passed its final canonical `lake --old env lean <file>` check,
with no diagnostics. All 28 theorem transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. The own umbrella imports all
four leaves and `MainTheorems.lean` imports the umbrella; no umbrella build
was run. Commands, source hashes and axiom output are retained in
`arithmetic-counting-pole-angle-audit.txt`.
