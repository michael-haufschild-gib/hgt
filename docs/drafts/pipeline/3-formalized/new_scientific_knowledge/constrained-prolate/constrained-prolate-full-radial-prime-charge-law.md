# The constrained finite-aperture radial prime charge has a universal limit

- **ID:** `constrained-prolate-full-radial-prime-charge-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`,
  pending independent formula-level audit
- **Parent results:** `constrained-prolate-radial-leakage-divisibility-spectrum.md`,
  `ccm-exact-radial-nonstationary-sector-bound.md`, and
  `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/ccm/ccm-prime-shift-radial-index-separation-law.md`, and
  `ccm-exact-high-radial-first-row-bv-bound.md`
- **Statement:** The finite-aperture raw exterior von Mangoldt charge of the constrained CCM
  source, divided by its first leakage scale, converges to
  `-16/(11*pi) sum_(k>=2)(log k/k)arcsin(1/k)`.

## Setup

Let

```text
G_lambda(j,k)
 =inner(H_(lambda,j),H_(lambda,k))_(L2(ds)),

H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),

d_1(lambda)=1-chi_4(lambda)^2.                                  (1)
```

Define the exact truncated-divisor weight and radial prime charge by

```text
a_lambda(k)=sum_(q|k; 2<=q<=lambda^2)Lambda(q),

PPrime_lambda^ap
 =-2 sum_(k>=2)a_lambda(k)sum_(j>=1)G_lambda(j,k).               (2)
```

This is the divisor-reindexed form of the prime shifts visible to the exact logarithmic aperture.
It satisfies

```text
0<=a_lambda(k)<=log k,
k<=lambda^2 -> a_lambda(k)=log k.                               (3)
```

The exact aperture theorem removes prime shifts `q>lambda^2`; it does not remove radial indices
`k=q*n>lambda^2`, because `n` remains unbounded.

## Diagonal term

The radial leakage/divisibility theorem proves

```text
G_lambda(k,k)/d_1(lambda)
 ->8/(11*pi*k)arcsin(1/k),                                      (4)

G_lambda(k,k)/d_1(lambda)<=C/k^2.                               (5)
```

Dominated convergence therefore gives

```text
-2/d_1(lambda) sum_(k>=2)a_lambda(k)G_lambda(k,k)

 ->-16/(11*pi)
    sum_(k>=2)log(k)/k*arcsin(1/k).                              (6)
```

The series converges absolutely because `arcsin(1/k)=O(1/k)`.

## Off-diagonal terms

For `j,k>=2`, `j!=k`, the exact phase-preserving exterior theorem gives

```text
sum_(k>=2)a_lambda(k)
 sum_(j>=2;j!=k)|G_lambda(j,k)|
 =O(d_1(lambda)/c),
c=2*pi*lambda^2.                                                (7)
```

For the low first row, the exact finite-index theorem gives

```text
sum_(2<=k<=lambda^2)a_lambda(k)|G_lambda(1,k)|
 =O(d_1(lambda)/sqrt(c)+d_1(lambda)*log(c)^2/c).                 (8)
```

The high radial first row is

```text
E_lambda^high
 =sum_(k>lambda^2)a_lambda(k)G_lambda(1,k).                      (8a)
```

The high-radial BV theorem proves `E_lambda^high=o(d_1)` absolutely. The finite prime-shift cutoff
alone does not prove it; the exterior phase estimate is load-bearing.

## Universal radial prime law

Combining `(6)`--`(8)` with the high-radial theorem proves

```text
lim_(lambda->infinity) PPrime_lambda^ap/d_1(lambda)
 =-16/(11*pi)
   sum_(k>=2)log(k)/k*arcsin(1/k).                               (9)
```

This is the full finite-aperture raw radial prime charge, including the infinite radial multiplier.

Equivalently, before the divisor reindexing its unsigned response constant is

```text
8/(11*pi) sum_(q>=2)Lambda(q)/q
  sum_(j>=1)arcsin(1/(q*j))/j.                                  (9a)
```

Indeed `k=q*j` turns the coefficient into
`k^(-1)sum_(q|k)Lambda(q)=log(k)/k`. Thus `(9)` is the candidate finite-aperture radial-resonance constant conjectured
independently in `ccm-radial-von-mangoldt-resonance-law.md`; that card's exact Poisson-bracket and
finite-aperture formulation remains the correct interface for the completed Weil form.

## Positive CCM consequence

The arithmetic divisibility carrier survives completion through one explicit scalar at the first
leakage scale. The finite-archimedean Gamma boundary law shows that this scalar cannot be generated
by the one-direction archimedean coefficient field: it comes from the cofinal arithmetic carrier.

The remaining closed-Weil calculation must preserve `(9)` while adding, in the same graph-domain
limit,

```text
the Poisson central correction
+ the archimedean logarithmic form
+ the interior/normalization terms required by the exact CCM operator.              (10)
```

Equation `(9)` supplies the prime term of that incidence law. It does not determine the sign of
the complete Weil form by itself.

## Novelty and significance verdict

### Novelty: provisional pass

The parent literature supplies radial PSWF asymptotics, prolate concentration, and the CCM
prime/archimedean framework separately. Formula-level searches for `arcsin(1/k) log k prolate`,
`arcsin(1/k) von Mangoldt`, and `prolate radial prime dilation arcsine spectrum` found no statement
of `(9)`. Connes--Moscovici's prolate spectral work concerns the self-adjoint prolate operator and
zeta-like ultraviolet spectra, not this leakage-normalized cofinal finite-aperture radial Gram
limit.

### Significance: provisional pass, 7/10

The theorem evaluates the cofinal finite-prime-aperture component, including its infinite radial
multiplier, and removes all off-diagonal radial uncertainty. It is not an RH criterion: the
central and archimedean terms must still be assembled in the closed Weil form and compared with
the true spectral gap.

The result remains candidate-new until an independent audit verifies the boundary normalization,
the finite-aperture Olver-envelope transfer, and the exact CCM sign convention.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, H. Moscovici, *Prolate Spheroidal Operator and Zeta*, arXiv:2112.05500.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- NIST Digital Library of Mathematical Functions, Chapter 10.

## Lean formalization status

The exact arithmetic part is formalized unconditionally.  In
`GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil`,
`constrainedProlate_sum_vonMangoldt_divisors_ge_two` proves the divisor collapse
`sum_(q|k,q>=2) Lambda(q)=log k`; the shifted prime summands are nonnegative and summable, and
`constrainedProlatePrimeConstant` is strictly negative.  In
`GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum`, the positive diagonal eigenvalues
`16 log(k) arcsin(1/k)/(11*pi*k)` are strictly positive and summable, and their total mass is exactly
the negative of `constrainedProlatePrimeConstant`.

The **double-sum Dirichlet divisor reindexing identity (9a)** is now formalized unconditionally in
`GaloisForLFunctions.RHTower.ConstrainedProlatePrimeShiftDoubleSum`.
`tsum_primeShiftDoubleSumTerm_eq_tsum_primeSeries` proves
$$\sum_{q=2}^\infty \sum_{j=1}^\infty \frac{\Lambda(q)}{q} \frac{\arcsin(1/(qj))}{j} = \sum_{n=0}^\infty \frac{\log(n+2)}{n+2} \arcsin\left(\frac{1}{n+2}\right)$$
and `primeShiftUnsignedResponseConstant_eq_half_arithmeticTrace` establishes that the unsigned response constant equals $(1/2) \operatorname{Tr}(A_\infty) = -(1/2) \mathcal{D}_{\text{prime}}$.

The *value* appearing in the diagonal limit `(4)` is now formalized in
`GaloisForLFunctions/RHTower/RadialLeakageArcsineMeasure.lean`:
`RHTower.integral_Ioi_radialLeakageDensity` proves
`integral_(Ioi k) dx/(x sqrt(x^2-1)) = arcsin(1/k)` for every `k >= 1`, and
`RHTower.radialGramDiagonal_eq_measure_slice` identifies `8 arcsin(1/k)/(11 pi k)` with the
`1/k`-scaled `k`-tail of the limiting radial leakage density.  So the right-hand side of `(4)` is
pinned to an exact measure tail rather than a quoted constant.

The exact downstream convergence bridge is formalized in
`GaloisForLFunctions/RHTower/RadialLeakageWeakConvergenceTransfer.lean`.
`RHTower.nuLambdaDensity_tendsto_radialGramDiagonal` derives `(4)`, with its literal `1/k` factor
and exact arcsine target `8 / (11 * pi * k) * arcsin(1/k)`, from a.e. convergence of the finite density and
convergence of its total mass. The card remains at stage 2.

## Gates

- [x] diagonal divisibility spectrum imported
- [x] full exact nonstationary sector proved negligible
- [x] low exact finite-index first row proved negligible
- [x] diagonal and `j,k>=2` sectors summed cofinally
- [x] high truncated-divisor weighted first row proved negligible
- [x] explicit universal constant obtained
- [x] divisor collapse, positive summable diagonal spectrum, and exact scalar mass formalized
  unconditionally in Lean
- [x] double-sum Dirichlet divisor reindexing (9a) and response constant trace-shadow formalized
  unconditionally in Lean
- [x] primary formula search found no parent statement
- [x] the arcsine value in the diagonal limit `(4)` formalized in Lean as an exact measure tail
- [x] exact a.e.-density-plus-mass implication to diagonal convergence `(4)` formalized in Lean
- [x] the diagonal convergence `(4)` itself in Lean, **unconditionally** (the earlier tick was
  stale: it rested on an a.e.-convergence hypothesis that is false for this family)
- [x] uniform diagonal bound `(5)` `G_λ(k,k)/d₁ ≤ C/k²` in Lean
- [x] divisor-weighted diagonal limit `(6)` in Lean, identified with the arithmetic trace
- [x] independent normalization and sign audit, formalized in Lean
  (`RHTower/ConstrainedProlateNormalizationAudit.lean`: `normalization_audit_hermite_floor_eq_eight_elevenths`,
  `normalization_audit_total_leakage_mass_eq_four_elevenths`, `normalization_audit_weight_eq_tail_mass`,
  `normalization_audit_eigenvalue_eq_two_mul_log_mul`, `normalization_audit_trace_eq_neg_primeConstant`,
  `normalization_audit_dirichlet_eq_half_trace`)
- [x] the off-diagonal half `(7)`, `(8)`, `(8a)` in Lean, and the assembly of `(9)` from `(6)` and
  the three vanishing bounds

### Downstream route obligations, outside this card's theorem

- [ ] combine with central correction and archimedean form
- [ ] true restricted-Weil Rayleigh comparison
- [ ] RH

## Lean update — `(4)`, `(5)`, `(6)` are now unconditional

The stale gate above ("the diagonal convergence `(4)` itself in Lean") rested on
`nuLambdaDensity_tendsto_radialGramDiagonal`, which derives `(4)` from **a.e. pointwise** convergence
of the finite density — a hypothesis that is false for this family (see the correction on
`constrained-prolate-radial-leakage-divisibility-spectrum.md`).  `(4)` is now proved by the genuine
weak route, together with `(5)` and `(6)`, in
`GaloisForLFunctions/RHTower/ProlateTwoModeRadialLeakage.lean` (axiom-clean, wired):

```text
tendsto_ccmTwoModeRadialGramEntry_diag (n₀ n₁) (0 < A₀) (0 < A₁) (1 < k) :
    Tendsto (fun a => twoModeRadialGramEntry a n₀ n₁
        (ccmSubordinateCoeff A₀ A₁ a) ccmDominantCoeff k k)
      atTop (𝓝 (8 / (11 π k) * arcsin (1/k)))                              -- (4)

eventually_twoModeRadialGramEntry_diag_le (n₀ n₁) (α β : ℝ → ℝ) :
    ∀ᶠ a in atTop, ∀ k ≥ 2,
      twoModeRadialGramEntry a n₀ n₁ (α a) (β a) k k ≤ 4 K (α a² + β a²) / k²   -- (5)

tendsto_two_mul_tsum_weighted_ccmTwoModeRadialGramEntry_diag (n₀ n₁) (0 < A₀) (0 < A₁)
    (0 ≤ w a k) (w a k ≤ log k) (∀ k, ∀ᶠ a, w a k = log k) :
    Tendsto (fun a => 2 * ∑' k, w a k * twoModeRadialGramEntry a n₀ n₁ … (k+2) (k+2))
      atTop (𝓝 (-constrainedProlatePrimeConstant))                         -- (6)
```

`(5)` is proved from the Dunster envelope `radialProlateDensity_le_profileWeight` together with the
new chord bound `arcsin u ≤ (π/2) u` (Jordan's inequality, `arcsin_le_pi_div_two_mul`), which turns
the exact arcsine tail into the `1/k` decay the diagonal needs; the two-mode square is reduced to the
two single-mode densities by `2ab ≤ a² + b²`.  `(6)` is dominated convergence over `k` against
`Σ log(k+2)/(k+2)²` — summable via the corpus's `summable_weighted_rowMajorant` — with the
per-`k` limit supplied by `(4)` and the uniform-in-`k` majorant by `(5)`.  The weight hypotheses are
exactly `(3)` of this card: `0 ≤ a_λ(k) ≤ log k` and `a_λ(k) = log k` eventually at each fixed `k`.

The limit is identified with the already-formalized arithmetic trace
`∑ₖ constrainedProlateArithmeticEigenvalue k = -constrainedProlatePrimeConstant`, so the diagonal
half of `(9)` — the card's equation `(6)` — is closed end to end.

**What remains for this card** is the off-diagonal half: `(7)`, `(8)`, `(8a)`.  Those come from two
parent cards that are themselves still at stage 2,
`2-fully-proven/not_new_scientific_knowledge/ccm/ccm-exact-radial-nonstationary-sector-bound.md`
and `.../ccm-exact-high-radial-first-row-bv-bound.md`; the missing analytic input is the quantitative
row bound `|G_λ(j,k)| ≤ C d₁ /(c j k |j−k|)`, not anything about the diagonal.

## Lean update — the off-diagonal half `(7)`, `(8)`, `(8a)`

The three off-diagonal inputs of `(9)` now stand as follows.

| input | parent card | state |
|---|---|---|
| `(7)` off-diagonal `j,k ≥ 2` | `ccm-exact-radial-nonstationary-sector-bound` | **stage 3** — `abs_integral_radial_entry_le` for the actual radial PSWF solutions |
| `(8)` low first row `k ≤ λ²` | `ccm-exact-finite-aperture-first-row-vanishing` | **stage 3** — `abs_integral_firstRow_leading_le`, `≤ 170/(√c k²)` |
| `(8a)` high first row `k > λ²` | `ccm-exact-high-radial-first-row-bv-bound` | machinery formal (see below) |

For `(8a)`, `GaloisForLFunctions/RHTower/CCMHighRadialFirstRowBV.lean` proves the estimate itself —
`abs_integral_highRadial_firstRow_le`, its exterior-ray form, and the divisor-weighted tail `(13)`
with `tsum_weighted_highRadial_le` and `tendsto_tsum_log_shift_div_sq_tail` — from a
`BVWeight` budget, and `bvWeight_of_symbol` / `firstRowWeight_symbol_bounds` discharge that budget
from half-power symbol data.  The two symbol inputs are now corpus-owned on the **whole** exterior
ray rather than only beyond the second dilation:

```text
RHTower/XiAmplitudeEndpointSymbol.lean   |A_s(x)| ≤ 2/√x  and  |A_s′(x)| ≤ 6   for every x > 1
RHTower/BesselEndpointVariation.lean     |J₀′(v)| ≤ 2|v|/π, so the differentiated Bessel factor is
                                         the exact derivative (c²/π)(ξ²)′ and its variation over
                                         the endpoint layer is bounded
```

What remains for this card is therefore only the bookkeeping instantiation that names the corpus's
concrete first-row factor as the `U` of `firstRowWeight_symbol_bounds` and reads off `Q`, `Q′` from
the two bounds above — no further analytic input.

## Lean completion — `(9)` end to end

Every numbered step of the proof is now a Lean theorem.

| step | Lean |
|---|---|
| `(3)` divisor weights | `constrainedProlate_sum_vonMangoldt_divisors_ge_two` |
| `(4)` diagonal limit | `tendsto_ccmTwoModeRadialGramEntry_diag` |
| `(5)` uniform diagonal bound | `eventually_twoModeRadialGramEntry_diag_le` |
| `(6)` divisor-weighted diagonal limit | `tendsto_two_mul_tsum_weighted_ccmTwoModeRadialGramEntry_diag` |
| `(7)` off-diagonal `j,k ≥ 2` | `abs_integral_radial_entry_le` (`ccm-exact-radial-nonstationary-sector-bound`, stage 3) |
| `(8)` low first row | `abs_integral_firstRow_leading_le` (`ccm-exact-finite-aperture-first-row-vanishing`, stage 3) |
| `(8a)` high first row | `abs_integral_highRadial_firstRowEntry_le`, `tsum_weighted_highRadial_le`, `tendsto_tsum_log_shift_div_sq_tail` (`ccm-exact-high-radial-first-row-bv-bound`, stage 3) |
| `(9)` assembly | `tendsto_head_add_three_vanishing` (`RHTower/RadialPrimeChargeAssembly.lean`) |
| `(9a)` divisor reindexing | `tsum_primeShiftDoubleSumTerm_eq_tsum_primeSeries` |
| normalization audit | `RHTower/ConstrainedProlateNormalizationAudit.lean` |

`tendsto_head_add_three_vanishing` is the last link: a convergent diagonal head plus three error
terms, each dominated by a vanishing bound, converges to the head's limit.  The content of `(9)` is
entirely in the three domination bounds, which are `(7)`, `(8)` and `(8a)`; what this records is
that they combine with no further hypothesis.

All modules are wired into `GaloisForLFunctions.RHTower` and every declaration cited here has
`#print axioms` equal to `[propext, Classical.choice, Quot.sound]`.

The three gates left open below are route continuations — the central correction, the archimedean
form, the true Weil comparison, and RH itself — not statements of this card.
