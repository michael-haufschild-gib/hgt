# The constrained prolate prime response has an arithmetic trace-class spectrum

- **ID:** `constrained-prolate-arithmetic-dilation-operator-limit`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `constrained-prolate-full-radial-prime-charge-law.md` and the weighted projective
  convergence proved in
  `universal-radial-prolate-arithmetic-dilation-spectrum.md`
- **Statement:** The symmetrized finite-aperture von Mangoldt dilation matrix of the constrained
  CCM prolate source converges in trace norm, after leakage normalization, to the positive diagonal
  operator with eigenvalues
  `16 log(k) arcsin(1/k)/(11*pi*k)`. The full raw radial prime charge is the negative trace of this
  limiting operator, and the associated Fredholm determinants converge locally uniformly.

## Setup

Let

```text
G_lambda(j,k)=inner(H_(lambda,j),H_(lambda,k)),

a_lambda(k)=sum_(q|k; 2<=q<=lambda^2)Lambda(q),

d_lambda=1-chi_4(lambda)^2.                                    (1)
```

The weighted nuclear diagonalization theorem gives, with

```text
w_k=8/(11*pi*k)arcsin(1/k),
Omega_k=1+log k,
W=diag(w_k),                                                    (2)
```

the projective convergence

```text
sum_(j,k>=1)(Omega_j+Omega_k)
 |G_lambda(j,k)/d_lambda-delta_(j,k)w_k| ->0.                   (3)
```

The finite-aperture divisor weights satisfy

```text
0<=a_lambda(k)<=log k,
a_lambda(k)=log k for k<=lambda^2.                              (4)
```

Define on the finite-sequence core of `ell^2(N_+)` the symmetric arithmetic dilation matrix

```text
A_lambda(j,k)
 =(a_lambda(j)+a_lambda(k))G_lambda(j,k).                       (5)
```

Equivalently, in form notation,

```text
A_lambda=M_(a_lambda)G_lambda+G_lambda M_(a_lambda).            (6)
```

Although `M_(a_lambda)` is unbounded as an operator on `ell^2`, equation `(3)` implies that the
matrix in `(5)` is absolutely projective and therefore defines a trace-class operator. This direct
matrix definition is the canonical one; no independent domain assertion for the two products in
`(6)` is required.

## Arithmetic trace-class limit

Put

```text
A_infinity=diag(kappa_k),

kappa_k=2(log k)w_k
       =16/(11*pi) *log(k)/k*arcsin(1/k).                       (7)
```

Then

```text
||A_lambda/d_lambda-A_infinity||_(S1)->0.                      (8)
```

In fact the stronger projective convergence holds:

```text
sum_(j,k>=1)
 |A_lambda(j,k)/d_lambda-delta_(j,k)kappa_k| ->0.               (9)
```

### Proof

Write

```text
E_lambda(j,k)
 =G_lambda(j,k)/d_lambda-delta_(j,k)w_k.                       (10)
```

By `(4)`,

```text
a_lambda(j)+a_lambda(k)<=Omega_j+Omega_k.                       (11)
```

Hence `(3)` gives

```text
sum_(j,k)(a_lambda(j)+a_lambda(k))|E_lambda(j,k)| ->0.          (12)
```

The remaining diagonal discrepancy is

```text
2sum_k |a_lambda(k)-log k|w_k.                                 (13)
```

For every fixed `k`, the summand is eventually zero by `(4)`. It is dominated by
`2(log k)w_k`, whose series converges because

```text
w_k=8/(11*pi*k^2)+O(k^(-4)).                                  (14)
```

Dominated convergence makes `(13)` tend to zero. Combining `(12)` and `(13)` proves `(9)`.
Every matrix unit has trace norm one, so the projective matrix norm dominates the trace norm.
This proves `(8)`. `QED`

## Spectral and determinant consequences

The limit operator is positive and trace class. Trace-norm convergence gives

```text
Tr[(A_lambda/d_lambda)_-] ->0,                                (15)
```

where the left side is the total negative spectral mass, and it gives locally uniform Fredholm
determinant convergence

```text
det(I+z A_lambda/d_lambda)
 ->D_arith(z):=product_(k>=2)(1+z kappa_k)                     (16)
```

on the whole complex plane. Thus the complete nonzero limiting spectrum, including multiplicity,
is the explicit sequence `(kappa_k)_(k>=2)`.

Since

```text
kappa_k~16/(11*pi) *log k/k^2,                                (17)
```

the exponent of convergence of the zeros of `D_arith` is `1/2`. In particular
`D_arith` is an entire function of order `1/2`; its zeros, counted with the multiplicities of the
values `kappa_k`, are the negative real points

```text
z_k=-1/kappa_k.                                               (18)
```

## Recovery of the full radial prime charge

The finite-aperture raw radial prime charge is

```text
PPrime_lambda
 =-2sum_(k>=2)a_lambda(k)sum_(j>=1)G_lambda(j,k).              (19)
```

Symmetry of the Gram matrix gives the exact identity

```text
PPrime_lambda=-sum_(j,k>=1)A_lambda(j,k).                      (20)
```

Projective convergence `(9)`, not trace convergence alone, permits pairing with the all-ones
matrix. Therefore

```text
PPrime_lambda/d_lambda
 ->-sum_(k>=2)kappa_k
 =-16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k).                  (21)
```

Thus the previously obtained scalar response is the negative trace of a canonical positive
arithmetic operator. The limiting prime term has acquired an intrinsic spectrum and determinant,
not merely a total mass.

## Positive CCM consequence

The constrained radial source transports the finite-prime divisor weights through the cofinal
aperture limit in the following exact chain:

```text
von Mangoldt divisor mask
 -> symmetrized dilation anticommutator
 -> positive trace-class arithmetic spectrum
 -> locally uniform Fredholm determinant.                    (22)
```

The polar--prime critical Mellin graph theorem remains necessary before `(22)` can be inserted into
the complete restricted Weil form. The present theorem does not assert Weil positivity or RH.
It proves that the raw radial prime module already has a canonical quantized limit and that its
total negative charge is the trace shadow of that limit.

## Novelty and significance verdict

The PSWF literature supplies the radial asymptotics but not the integer-dilation trace-class limit.
The CCM literature supplies the prime-shifted prolate source but not the spectrum `(7)` or the
determinant `(16)`. Searches for the arcsine spectrum and its von Mangoldt weighting found no parent
statement. This theorem strengthens the scalar cofinal prime response to operator, spectral, and
determinant convergence.

It remains candidate-new until independent formula-level review of the parent radial theorem. Its
mathematical proof from `(3)`--`(4)` is complete.

## Lean formalization status

The unconditional scalar spectrum is formalized in
`GaloisForLFunctions.RHTower.ArcsineZetaDerivativeSpectrum`.  With Lean index `n` corresponding to
the paper index `k=n+2`, the declaration `constrainedProlateArithmeticEigenvalue` is exactly

```text
16 log(k) arcsin(1/k)/(11*pi*k).
```

The declarations `constrainedProlateArithmeticEigenvalue_pos` and
`summable_constrainedProlateArithmeticEigenvalue` prove that every eigenvalue is strictly positive
and that the sequence is summable.  The exact total-mass identities
`tsum_constrainedProlateArithmeticEigenvalue` and
`tsum_constrainedProlateArithmeticEigenvalue_eq_neg_diagonalConstant` identify its sum with the
negative radial prime constant in `(21)`.  This is the complete scalar diagonal/trace-class core of
the limiting operator.

The **matrix argument of `(9)`--`(13)` and `(20)`--`(21)` is now formalized unconditionally** in
`GaloisForLFunctions/RHTower/ArithmeticDilationProjectiveLimit.lean`, as the implication the card's
proof actually establishes.  `RHTower.arithmeticDilation_projective_tendsto` takes the weighted
projective hypothesis `(3)` (with an abstract weight `Ω ≥ L`, absolute summability included), the
divisor-weight trap `0 ≤ a ≤ L` of `(4)`, pointwise stabilization `a_λ(k) → L k` at every fixed `k`,
and summability of `L·w`, and concludes the plain projective convergence

```text
sum_(j,k) |A_lambda(j,k)/d_lambda - delta_(j,k) kappa_k| -> 0,
kappa_k = 2 L k w k.
```

The proof is the card's own two-term split: `RHTower.arithmeticDilation_abs_le` is the pointwise
bound `|D| ≤ (Ω_j+Ω_k)|E| + 2(L k − a k) w k` of `(11)`--`(12)`, and
`RHTower.tendsto_tsum_of_eventually_pointwise_zero` discharges the diagonal defect `(13)` by a
tail-truncation argument (cut the dominating series `2 L k w k` at `N`, then the finitely many
indices below `N` vanish eventually) rather than by an appeal to dominated convergence.

`RHTower.arithmeticDilation_total_tendsto` is the pairing with the all-ones matrix, i.e. exactly
`(20)`--`(21)`: the total mass converges to the trace `∑_k κ_k`, so the raw prime charge converges
to its negative.  `RHTower.constrainedProlateArithmeticEigenvalue_eq_two_mul_log_mul` identifies
`κ_k = 2 log(k) w_k` with the already-formalized `constrainedProlateArithmeticEigenvalue`.  All of
these are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

What remains genuinely open in Lean is the *hypothesis* `(3)` itself: the PSWF weighted projective
convergence of the radial Gram matrix.  It is supplied as an explicit hypothesis, not asserted, so
nothing here claims the unconditional operator convergence `(8)` or the Fredholm determinant limit
`(16)` for the actual prolate source.

The missing trace-class interface is now formalized in
`GaloisForLFunctions/RHTower/ArithmeticDilationTraceClass.lean`.
`RHTower.absoluteMatrixOperator` realizes every absolutely summable matrix as the literal sum of
its rank-one matrix units.  `RHTower.traceNorm_absoluteMatrixOperator_le` proves that its genuine
Schatten trace norm is bounded by the entrywise projective norm, and
`RHTower.arithmeticDilation_traceClass_traceNorm_limit` upgrades the exact implication already
proved in `ArithmeticDilationProjectiveLimit` to `(8)`: every stage and the limit are Schatten-1,
and the operators converge in trace norm.

The same module constructs the actual limiting operator
`RHTower.constrainedProlateArithmeticLimitOperator` and proves unconditionally that it is
Schatten-1, positive, self-adjoint, and diagonal on the canonical `ell^2` basis with precisely the
eigenvalues `(7)`.  Its ordinary operator trace is proved equal to `sum_k kappa_k`, hence to the
negative constrained-prolate prime constant.  Finally,
`RHTower.constrainedProlateArithmeticFredholmDeterminant` is the global bare product in `(16)`;
the product converges uniformly on every compact subset of `C`, agrees near the origin with the
existing Hilbert--Schmidt `fredholmDet1`, and vanishes at every point `-1/kappa_k`.

`GaloisForLFunctions.RHTower.ArithmeticDilationNegativeMass.lean` now formalizes the spectral
consequence.  It proves that a Hermitian absolutely projective matrix gives a self-adjoint
operator, that the limiting arithmetic diagonal is positive, and the sharp general estimate

```text
sum_n (sgVal_n(S))^- <= ||S - T||_1
```

for every positive comparator `T` whenever `S-T` is trace class.  Applied to the trace-norm limit
above and the Gram symmetry of `E`, this proves that every arithmetic stage is self-adjoint and
its complete signed-greedy negative spectral mass tends to zero.  This remains an unconditional
Lean implication from the card's explicit weighted projective hypothesis `(3)`; it does not claim
that the actual PSWF source has yet discharged that hypothesis.

`GaloisForLFunctions.RHTower.ArithmeticDilationDeterminantZeros.lean` proves the converse missing
from the initial product construction: an absolutely summable bare Fredholm product vanishes iff
one of its linear factors vanishes.  Consequently

```text
D_arith(z) = 0  iff  exists k >= 2, z = -1/kappa_k.
```

Thus the global zero *set* in `(18)` is exact in Lean.  The same module now proves more: the real
profile `log(x) arcsin(1/x)/x` is strictly decreasing on `[2,infinity)`, hence the `kappa_k` are
pairwise distinct; the locally uniform limit of finite characteristic polynomials is entire; and
factoring out each linear term leaves a nonzero entire cofactor at its reciprocal point.  Therefore
every zero is uniquely indexed and simple (`D_arith'(z_k) != 0`).

`GaloisForLFunctions.RHTower.ArithmeticDilationEntireOrder.lean` completes the determinant growth
block unconditionally.  `RHTower.constrainedProlateArithmeticFredholmZero_hasExponentOfConvergence_half`
proves that the reciprocal zero divisor has exact convergence exponent `1/2`.  The reusable
predicate `RHTower.HasExactEntireOrder` uses the standard global characterization: every power
strictly above `rho` gives a global exponential growth envelope and every power strictly below
`rho` fails to do so.  The declaration
`RHTower.constrainedProlateArithmeticFredholmDeterminant_hasExactEntireOrder_half` proves this at
`rho=1/2`.  Its upper bound comes from summability of `kappa_k^p` for every `p>1/2`; its lower bound
is a direct positive-axis estimate, not an inference from zeros alone: at radius `10(N+2)^2`, the
first `N` positive factors are each at least `2`, so the determinant norm is at least `2^N`.  Both
capstones are axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

`GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant.lean` closes the remaining
nondiagonal determinant-continuity gate without replacing stages by diagonal or finite-rank
models.  It proves `|sgVal_n(S)|=s_n(S)`, upgrades trace-norm convergence to `ell^1` convergence
of full signed spectra using counting-measure Scheffe plus the sharp negative-mass estimate, and
passes an explicit finite-product Lipschitz bound to the infinite products.  Consequently
`RHTower.arithmeticDilationStageFredholmDeterminant_tendstoUniformlyOn` proves `(16)` uniformly on
every compact subset of `C` for the literal nondiagonal arithmetic operators under the card's
weighted projective hypothesis, Gram symmetry, and exact `kappa` identification.  The limit
signed-greedy product is proved equal to the existing global arithmetic determinant.  Axiom audit
contains only `propext`, `Classical.choice`, and `Quot.sound`.

`GaloisForLFunctions.RHTower.ArithmeticDilationWeightedProjectiveDischarge.lean` completes the
analytic discharge of the weighted projective Gram hypothesis `(3)` unconditionally.
`RHTower.tendsto_weighted_projective_of_rowBound` proves that an inverse-bandwidth off-diagonal decay
envelope against a summable 2D majorant (from the partial-fraction row bounds) together with a
dominated diagonal pointwise defect forces the full weighted projective error sum to zero.
`RHTower.arithmeticDilation_projective_tendsto_discharged` and
`RHTower.arithmeticDilation_traceClass_traceNorm_limit_discharged` establish the projective and
Schatten-1 trace-norm convergence unconditionally from these raw inputs without external hypotheses.
`GaloisForLFunctions.RHTower.RadialPSWFArithmeticDilationDischarge.lean` formalizes the exact
convergence of the radial PSWF Dunster leading arclength density integrals to the arithmetic
weights and eigenvalues `κ_k = 16 log(k) arcsin(1/k) / (11 π k)`.
`GaloisForLFunctions.RHTower.ConstrainedProlateNormalizationAudit.lean` formalizes the independent
PSWF normalization audit, verifying the consistency of all floor ratios (`8/11`), total leakage mass
(`4/11`), dilation weights `w_k`, arithmetic eigenvalues `κ_k`, trace-shadow `- \mathcal{D}_{prime}`,
and double-sum Dirichlet divisor reindexing. Axiom audit contains only standard axioms.

## Gates

- [x] symmetrized finite-aperture arithmetic operator defined
- [x] weighted projective convergence upgraded to arithmetic projective convergence
- [x] trace-norm operator limit proved
- [x] vanishing total negative spectral mass proved
- [x] Fredholm determinant limit and limiting spectrum obtained
- [x] full scalar prime response recovered as negative trace
- [x] limiting positive arithmetic eigenvalue sequence, summability, and exact total mass formalized
  unconditionally in Lean
- [x] arithmetic projective convergence `(9)` formalized in Lean as an unconditional implication
  from the weighted hypothesis `(3)` and the divisor trap `(4)`
- [x] total-charge-as-trace recovery `(20)`--`(21)` formalized in Lean
- [x] `kappa_k = 2 log(k) w_k` identified with the formalized arithmetic eigenvalue
- [x] discharge the weighted projective hypothesis `(3)` from PSWF asymptotics in Lean
- [x] trace-class operator realization and projective-norm-to-trace-norm interface in Lean
- [x] limiting positive arithmetic operator, exact trace, and compact-uniform Fredholm product in Lean
- [x] vanishing full negative spectral mass from trace-norm convergence to the positive limit in Lean
- [x] nondiagonal stage determinant convergence in Lean
- [x] exact determinant zero set, unique indexing, and simple multiplicity in Lean
- [x] determinant proved entire in Lean
- [x] exact zero exponent of convergence `1/2` in Lean
- [x] exact entire order `1/2` in Lean
- [x] independent PSWF normalization audit
### Downstream route obligations, outside this card's theorem

As the card states above, "the polar--prime critical Mellin graph theorem remains necessary before
`(22)` can be inserted into the complete restricted Weil form.  The present theorem does not assert
Weil positivity or RH."

- [ ] polar--prime critical Mellin graph-domain assembly
- [ ] complete Weil-form lower bound
- [ ] RH

## Lean correction — the diagonal hypothesis of the projective discharge was too strong

`RHTower/ArithmeticDilationWeightedProjectiveDischarge.lean` discharged the weighted projective
hypothesis `(3)` from raw inputs, but one of those inputs was

```text
hdiag_ev : ∀ k, ∀ᶠ x in L, E x k k = 0
```

— the diagonal defect *exactly zero* eventually.  For the actual PSWF family that is false: `(4)`
gives `G_λ(k,k)/d_λ → w_k`, so `E x k k → 0`, but it never vanishes.  The discharge therefore could
not be applied to the family it was written for, even though the corresponding gate was ticked.

The hypothesis is used only to make the diagonal series vanish termwise, so it has been weakened in
place to the true statement

```text
hdiag_tendsto : ∀ k, Tendsto (fun x => E x k k) L (𝓝 0)
```

and the diagonal step reproved by Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`): pointwise convergence to zero plus the summable
majorant `Σ 2 Ω_k M_k` gives convergence of the sum.  The three affected declarations —
`tendsto_weighted_projective_of_rowBound`, `arithmeticDilation_projective_tendsto_discharged`,
`arithmeticDilation_traceClass_traceNorm_limit_discharged` — now take the weakened hypothesis, which
is exactly what `(4)` supplies.  Nothing else in the tree referred to them.

With this, the discharge of `(3)` accepts the card's own inputs: the diagonal convergence `(4)`, the
uniform diagonal bound `(5)`, and the inverse-bandwidth off-diagonal envelope `(7)`/`(8)`/`(8a)` of
`constrained-prolate-full-radial-prime-charge-law` (now at stage 3).

## Lean completion

The card states that its "mathematical proof from `(3)`--`(4)` is complete".  Both inputs are now
Lean theorems, and so is every step from them.

| step | Lean |
|---|---|
| `(3)` weighted projective convergence | `tendsto_weighted_projective_of_rowBound` — discharged from the raw off-diagonal envelope and the dominated diagonal defect, with the corrected hypothesis `hdiag_tendsto` |
| `(4)` divisor trap `0 ≤ a_λ(k) ≤ log k`, eventually `= log k` | `constrainedProlate_sum_vonMangoldt_divisors_ge_two` |
| off-diagonal envelope feeding `(3)` | `abs_integral_radial_entry_le`, `abs_integral_firstRow_leading_le`, `abs_integral_highRadial_firstRowEntry_le` — all three parent cards now at stage 3 |
| diagonal defect feeding `(3)` | `tendsto_ccmTwoModeRadialGramEntry_diag` `(4)`, `eventually_twoModeRadialGramEntry_diag_le` `(5)` |
| `(9)` arithmetic projective convergence | `arithmeticDilation_projective_tendsto_discharged` |
| trace-norm operator limit | `arithmeticDilation_traceClass_traceNorm_limit_discharged` |
| limiting spectrum, trace, total charge `(20)`--`(21)` | `ArcsineZetaDerivativeSpectrum`, `ArithmeticDilationProjectiveLimit`, `ArithmeticDilationTraceClass` |
| Fredholm determinant `(16)`, entirety, order and zero exponent `1/2` | `ArithmeticDilationStageDeterminant` |
| normalization audit | `ConstrainedProlateNormalizationAudit` |

The one correction made while completing this chain is recorded in the section above: the projective
discharge previously required the diagonal defect to be *exactly* zero eventually, which the actual
PSWF family does not satisfy.  It now requires only `E_λ(k,k) → 0`, which is what `(4)` gives, and
the diagonal step is reproved by Tannery's theorem.  All three affected declarations are
axiom-clean.
