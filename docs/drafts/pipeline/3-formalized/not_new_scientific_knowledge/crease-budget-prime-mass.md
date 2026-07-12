# The line budget carries the Mertens mass

- **ID:** `crease-budget-prime-mass`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The Lipschitz variation budget that transfers a square-dilated carrier
  floor from a certified line `re = σ₂` to the critical line must carry the prime
  reciprocal mass up to `√N`; consequently any line-crossing transfer datum forces the
  cutoff's Mertens mass under the explicit cap `2(1 + 1/(2σ₂-1))`.  Stated positively
  throughout: what the budget must contain, what the cutoff must satisfy.

## Exact relations

```text
sum_{p <= sqrt N} 1/p <= lineBudget σ₂ N + (1 + 1/(2σ₂-1))                        (1)
lineBudget σ₂ · -> ∞  with the cutoff                                             (2)
line floor at σ₂  ∧  budget condition to 1/2
    ==>  sum_{p <= sqrt N} 1/p < 2·(1 + 1/(2σ₂-1))                                (3)
sum_{k ∈ [1,M]} k^(-c) <= 1 + 1/(c-1)                 for c > 1, uniform in M     (4)
|dpoly2 sqrtMoebiusCoeff (Icc 1 N) z| <= 1 + 1/(2σ₂-1)   on re z >= σ₂ > 1/2      (5)
sum_{n <= M} 1/n <= prod_{p <= M} (1 - 1/p)^(-1)          (Euler domination)      (6)
log log(M+1) <= 2·sum_{p <= M} 1/p                        (effective Mertens)     (7)
line floor at σ₂  ∧  budget condition to 1/2
    ==>  sqrt(N) + 1 < exp exp(4·(1 + 1/(2σ₂-1)))         (closed-form cutoff)    (8)
sum_{p <= sqrt y} 1/p <= sum_{n <= y} (sqrtMoebiusCoeff n · n^(-1/4))²            (9)
detCoeffW y y σ (p²) = -(p^(-σ))²                for sqrt y < p <= y             (10)
sum_{sqrt y < p <= y} 1/p <= sum_k detCoeffW y y (1/4) k ²                       (11)
|b(p²)| >= δ·p^(-1/2) on P  ==>  δ²·sum_P 1/p <= sum_S b²   (abstract law)       (12)
|a(p²)| >= δ on primes  ==>  δ²·sum_{p<=sqrt y} 1/p
    <= sum_{n<=y} (a n · n^(-1/4))²                      (quarter-weighted form) (13)
sum_{k ∈ [1,M]} 1/k <= 1 + log M                          (harmonic upper)       (14)
lineBudget σ₂ N = sum_{k <= sqrt N} |μ(k)|·|k⁻¹ - k^(-2σ₂)|   (square coords)    (15)
(1/2)·log log(sqrt N + 1) - (1 + 1/(2σ₂-1)) <= lineBudget σ₂ N
    <= 1 + log(sqrt N)                                    (the budget bracket)   (16)
```

`(12)`–`(13)` are the abstract forced-content law: both instances `(9)` and `(11)` are
now derived from `(12)` (proofs refactored), and any future square-supported carrier
inherits it.  `(16)` with the meter reading
`(1/2)·log log(√N+1) ≤ ∑_{p≤√N} 1/p ≤ lineBudget + cap` makes the budget a certified
Mertens-mass meter: its forced content is log-log (primes), its total is log
(squarefree); the gap between the two laws is exactly the non-prime squarefree mass.

The prime-mass upper law and the rung tower complete the picture:

```text
sum_{p <= n} log p <= n·log 4                        (Chebyshev, from primorial)  (17)
sum_{p <= x} 1/p <= 4·(1 + log(Nat.log 2 x))         (dyadic-block upper law)     (18)
sum_{p <= x} 1/p <= 4 + 4·log(2·log x)               (log-log form, x >= 2)       (19)
|a(p^m)| >= δ on primes  ==>  δ²·sum_{p^m <= y} 1/p
    <= sum_{n <= y} (a n · n^(-1/(2m)))²             (the tower, rung m)          (20)
sum_{p^m <= y} 1/p <= sum_{n <= y} (mPartMoebiusCoeff m n · n^(-1/(2m)))²         (21)
```

`(18)` is elementary and effective: the `j`-th dyadic block holds at most `2^(j+2)/j`
primes by `(17)`, each of reciprocal at most `2^(-j)`, so blocks carry mass at most
`4/j` and the harmonic bound closes.  With `(7)` the prime mass is pinned between two
explicit log-log laws — the meter is two-sided.  `(20)`–`(21)` are the forced-content
tower: the square rung's threshold `1/4` generalizes to `1/(2m)` at dilation `m`
(`p^m`-supported coefficients of size `δ` force `δ²·(rung prime mass)` at weight
`1/(2m)`), with the `mPart m` Möbius carrier as the instance at every rung — the
`m`-free ladder's spectral fingerprint, machine-checked.

## Proof

`(1)` the budget's square-only support evaluates exactly at prime squares:
`|μ(p)|·|(p²)^(-1/2) − (p²)^(-σ₂)| = p⁻¹ − p^(-2σ₂)`; summing over the injection
`p ↦ p²` into `[1, N]` and controlling `∑ p^(-2σ₂)` by the partial zeta cap `(4)` leaves
the prime reciprocal sum.  `(2)` is `(1)` plus the divergence of `∑ 1/p` (mathlib's
`not_summable_one_div_on_primes`, converted to partial-sum form).  `(3)`: the line floor
`t₀` is capped by the uniform carrier sup bound `(5)` (finite dilation identity plus the
Möbius sup bound), so the budget condition `lineBudget ≤ t₀ − ε₁ < t₀` traps the prime
mass between `(1)` and twice the cap.  `(4)` splits off `k = 1` and applies the banked
integral-test partial bound; `(5)` reduces to the Möbius carrier at `2z` by the finite
dilation identity.

## Parent classification

`[SEARCH]` The ingredients — Möbius square support, Mertens divergence, triangle-
inequality sup bounds — are classical.  The assembled delimitation is lab-internal: it
quantifies which cutoffs the tree's own `dpoly2_chart_floor` budget technology can carry
to the critical line.  Not new scientific knowledge; the positive-constraint packaging
(forced prime mass, not a negation) is the shipped form.

## Reuse audit

- `SqrtCarrierCertificate.lean`: `dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt` (both the sup
  bound `(5)` and the term evaluation route), `sum_range_add_rpow_neg_le` (the cap `(4)`);
- `MFreeLadder.lean` / `Mollifier.lean`: `sqrtMoebiusCoeff`, `moebiusCoeff`,
  `abs_moebiusCoeff_le_one`;
- `SquarefreeMoebiusNormalization.lean`: `sqrtPart_apply_sq`;
- mathlib: `not_summable_one_div_on_primes`,
  `not_summable_iff_tendsto_nat_atTop_of_nonneg`, `Nat.primesBelow`,
  `Nat.pow_left_injective`, `Nat.le_sqrt`.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/CreaseBudgetPrimeMass.lean`.

- `natCast_sq_rpow`, `sum_Icc_rpow_neg_le`: the real dilation and the partial zeta
  cap `(4)`;
- `norm_dpoly2_moebiusCoeff_le`, `norm_dpoly2_sqrtMoebius_le`: the uniform sup
  bounds `(5)`;
- `lineBudget`, `lineBudget_term_sq_prime`: the budget and its prime-square terms;
- `primeMass_le_lineBudget_add`: the forced Mertens content `(1)`;
- `tendsto_primeMass_atTop`, `tendsto_lineBudget_atTop`: the growth law `(2)`;
- `line_crossing_cutoff_primeMass_lt`: the forced constraint `(3)`;
- `recipHom`, `harmonic_le_prod_primesBelow`: Euler's finite product domination `(6)`,
  via mathlib's geometric Euler product over smooth numbers — applied directly at
  `s = 1`, where only `‖f p‖ < 1` at primes is needed;
- `log_inv_one_sub_le`, `mertens_lower`: the effective Mertens lower bound `(7)` with
  explicit constant `2`, from `(6)`, the banked harmonic bound
  (`SecondMoment.harmonic_Icc_ge_log`), and `log(1-t)⁻¹ ≤ 2t` on `[0, 1/2]`;
- `line_crossing_cutoff_lt_expexp`: the closed-form cutoff constraint `(8)` — the
  explicit double-exponential reach of budget technology.

Companion file: `formal/GaloisForLFunctions/RHTower/SquareSupportPrimeMass.lean` — the
same square-support mechanism in the tree's other quadratic functionals:

- `primeMass_le_sqrtQuarter_diagonal`: the quarter-weighted mollifier second-moment
  diagonal must carry the Mertens mass `(9)` (each prime square contributes exactly
  `p⁻¹`);
- `filter_mul_eq_prime_sq`, `detCoeffW_prime_sq`: the detection coefficient at prime
  squares in the window `√y < p ≤ y` — the convolution fiber collapses to the diagonal
  pair `(10)`;
- `windowPrimeMass_le_detection_diagonal`: the detection diagonal at weight `1/4` must
  carry the window prime mass `(11)` — detection mass is not free below weight
  `1/4 + ε`;
- `primeMass_le_sq_sum_of_forced`, `primeMass_le_quarter_weighted_sq_sum`: the abstract
  law `(12)`–`(13)`, from which `(9)` and `(11)` are re-derived;
- (back in `CreaseBudgetPrimeMass.lean`) `sum_Icc_one_div_le`: the harmonic upper
  `(14)`; `lineBudget_eq_sum_sqrt`: the exact square-coordinates form `(15)`;
  `lineBudget_le_one_add_log`, `lineBudget_measures_primeMass`, `lineBudget_bracket`:
  the meter and the two-sided bracket `(16)`;
- `sum_primesBelow_log_le`: Chebyshev `(17)` from mathlib's `primorial_le_four_pow`;
- `primeMass_upper`, `primeMass_upper_log_log`: the upper laws `(18)`–`(19)`;
- (in `SquareSupportPrimeMass.lean`) `primeMass_le_pow_sum_of_forced`: the tower core
  (the square core is now its `m = 2` instance); `natCast_pow_rpow`;
  `primeMass_le_rung_weighted_sq_sum`: rung `m` of the tower `(20)`;
  `primeMass_le_mPart_weighted_diagonal`: the `mPart` carrier instance `(21)`.

Both modules are imported by `GaloisForLFunctions.RHTower` and `GaloisForLFunctions`.

## Gates

- [x] all statements positive (forced quantity + explicit bound), no negation shipped
- [x] unconditional; hypotheses are the transfer datum itself
- [x] carrier sup bound uniform in cutoff and height
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts both modules; the sole independent existing
failure is `SummableEulerCalkinInjectivity.lean`.  All thirty-three public declarations
across the two files use only `propext`, `Classical.choice`, and `Quot.sound`.

## Opens

The meter is now two-sided (`(7)` + `(19)`), so the prime mass of any cutoff is a
certified interval `[½·log log, 4·log log + C]` — the constants `2` (below) and `4`
(above) both trace to single elementary estimates (`log(1-t)⁻¹ ≤ 2t`; dyadic block width
`2`): base-`e` blocks and the `t + t²` bound would drive both toward `1 + o(1)`, an
optimization pass on two lemmas.  The tower `(20)` prices every rung: forced mass at
weight `1/(2m)` — read across the mixed-radix telescope, a product carrier over moduli
`m₀, m₁, …` carries forced mass at the harmonic-mean weight of its rungs, suggesting the
next object: the forced-content law for *convolutions* of dilated carriers, where the
`mFreeIndicator` telescope should compound the rung fingerprints into a single
mixed-radix spectral signature.
