# Gamma odd-Jacobi capacity saturation law

- **ID:** `gamma-odd-jacobi-capacity-saturation-law`
- **Stage:** 3-formalized / needs external novelty audit
- **Type:** SOURCE-SPECIFIC EXACT MERCER LAW / COHERENT CAPACITY THEOREM
- **Scientific status:** `[ADVANCE] [LEAN-FORMALIZED] [EXTERNAL NOVELTY PROVISIONAL]`
  `[NOT RH]`
- **Frontier rows discharged:** odd-capacity and inclusion-coherence parts of `SR-37`, now
  recorded as `SR-37`--`SR-38`.
- **Successor:** `SR-39`, actual Green--Schur/Euler operator placement.
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/AdaptiveMercerCapacity.lean`;
  - `formal/GaloisForLFunctions/RHTower/GammaOddJacobiCapacity.lean`;
  - `formal/GaloisForLFunctions/RHTower/GammaOddJacobiCoherentCapacity.lean`.

## Corpus boundary

Already known and excluded from novelty:

1. Gamma sine Gram
   `O(t,u)=(phi(t-u)-phi(t+u))/2`;
2. all-degree Jacobi Fourier law
   `F_n(t)=i^n c_n phi(t)tanh(t)^n`;
3. Gamma-Jacobi orthonormality;
4. all-even finite-prime residue tower;
5. capacity-independent odd floor against even corrections (`SR-36`);
6. generic Gram positivity, Schur complements, trace-class residual kernels, clock capacities,
   and positive finite-packet assembly throughout `HTGeometry`, `RHTower`, and `HilbertMetric`.

The generic adaptive-Mercer lemma in this increment is therefore `FORMAL-CLOSURE`, not claimed as
new science. Three-tree collision search found no prior theorem composing items 1--3 into the
literal odd projection kernel, its exact residual tail, a prime-adaptive summable schedule, and a
common-coordinate cross-prime kernel.

## General problem solved

The containing problem is **isotypic capacity saturation of symmetry-protected Schur residuals**.
For a protected Gram kernel and an orthonormal source ladder in the correct symmetry sector, one
must distinguish:

1. a true infinite-capacity obstruction;
2. a wrong-isotypic-sector obstruction;
3. pointwise exhaustion which loses packet coherence;
4. coherent exhaustion whose source-weighted diagonal is globally summable.

This theorem puts the actual Gamma odd floor in case 4.

## Exact theorem

Put

```text
c_n=sqrt((2n)!)/(2^n n!),
phi(t)=cosh(t)^(-1/2),
a_k(t)=(-1)^k c_(2k+1) phi(t)tanh(t)^(2k+1).
```

For `t,u>0`, the literal odd Jacobi coefficient of `sin(ts)` in the normalized Gamma space is
`a_k(t)`, and

```text
O(t,u)=sum_(k>=0) a_k(t)a_k(u).                         (1)
```

For every finite rank `K`,

```text
O_K(t,u)=O(t,u)-sum_(k<K)a_k(t)a_k(u)
        =sum_(k>=K)a_k(t)a_k(u),                        (2)
O_K(t,t)>=0,                 O_K(t,t)->0.               (3)
```

Let `R_p` be the actual Gamma conductor Schur cost. Define `K(p)` as the least rank satisfying

```text
R_p O_(K(p))(log p,log p)<=p^(-2).                      (4)
```

Then

```text
sum_p R_p O_(K(p))(log p,log p)<infinity.               (5)
```

No Xi character, zero divisor, target sign, asymptotic estimate, or numerical experiment enters
`(1)`--`(5)`.

## Coherent cutoff law

Prime-dependent ranks do not by themselves define one cross-prime operator if each tail is
reindexed separately. The theorem retains the common absolute odd-Jacobi coordinate:

```text
r_p(k)=0       if k<K(p),
r_p(k)=a_k(log p) otherwise,
C(p,q)=sum_k r_p(k)r_q(k).                              (6)
```

For every finite prime packet `F` and real coefficients `z`,

```text
sum_(p,q in F) z_p z_q C(p,q)
 =sum_k (sum_(p in F) z_p r_p(k))^2 >=0.                (7)
```

Moreover `C(p,p)=O_(K(p))(log p,log p)`, so `(5)` is exactly summability of the
Gamma-conductor-weighted diagonal of the coherent positive kernel `C`.

This answers the hostile control “pointwise cutoffs need not assemble under inclusion.” They do,
provided deleted modes are zero-padded in the common source coordinate rather than locally
reindexed.

## Proof

The normalization square is the normalized central-binomial coefficient:

```text
c_n^2=binom(2n,n)/4^n.
```

Generalized binomial expansion and odd extraction give, for `0<=x<1`,

```text
sum_(k>=0)c_(2k+1)^2 x^(2k+1)
 =((1-x)^(-1/2)-(1+x)^(-1/2))/2.                       (8)
```

Set `x=tanh(t)tanh(u)`. The exact Gamma characteristic factorizations at `t-u` and `t+u`
turn `(8)` into `(1)`. The existing all-degree Jacobi Fourier transform, followed by taking
imaginary parts at odd degree, proves that these are literal `L2(dmu_Gamma)` sine coefficients.
Splitting a convergent series at `K` proves `(2)`--`(3)`. Convergence to zero and positivity of
`p^-2` give `(4)` by least-number selection; comparison with the convergent p-series gives `(5)`.
Finally `(7)` is the exact finite Gram square identity and passage to the infinite kernel follows
from absolute convergence of cross-products of square-summable rows.

## Lean theorem surface

Universal closure:

- `HTGeometry.adaptiveMercerResidualKernel_self_eq_diagonalTail`;
- `HTGeometry.adaptiveMercerFiniteResidualKernel_quadraticForm_eq_sum_sq`;
- `HTGeometry.adaptiveMercerResidualKernel_psd`;
- `HTGeometry.exists_adaptiveMercerPositiveKernelCapacity_of_summableBudget`.

Actual source theorem:

- `RHTower.integral_oddJacobi_mul_sin_semilocalArchimedeanGammaMeasure`;
- `RHTower.hasSum_gammaOddJacobiCoefficient_mul`;
- `RHTower.gammaOddJacobiResidualKernel_eq_tail`;
- `RHTower.tendsto_gammaOddJacobiResidualKernel_self`;
- `RHTower.summable_gammaOddJacobiPrimeResidualCost`.

Coherent source connector:

- `RHTower.gammaOddJacobiPrimeCoherentResidualKernel_self`;
- `RHTower.gammaOddJacobiPrimeCoherentResidualKernel_psd`;
- `RHTower.summable_gammaOddJacobiPrimeCoherentResidualDiagonal`;
- `RHTower.sum_gammaOddJacobiPrimeCoherentResidualDiagonal_le_tsum_inv_sq`.

## Scientific consequence and exact limit

`SR-36` is sharp. Reflection-even capacity can never touch the odd floor, but actual odd Jacobi
capacity exhausts it exactly and can be scheduled coherently to turn its nonsummable protected
diagonal into a summable one. Thus positive growing boundary capacity survives, but its symmetry
sector and cutoff geometry are forced.

This does **not** prove RH and does not yet realize Suzuki's completed source producer. Remaining
frontier is not “more capacity”:

```text
coherent odd Gamma-Jacobi boundary kernel             CLOSED
prime-adaptive inclusion coherence                    CLOSED
placement in actual singular/local Green--Schur map   OPEN
completed Euler multiplication/trace identity         OPEN
fibre-pointed RH orientation                          OPEN
```

## Novelty boundary

Central-binomial series, Jacobi transforms, Parseval/Mercer expansions, p-series comparison, and
Gram positivity are classical. Internal audit across all three formal trees found the parents but
not their exact Gamma odd-sector/source-weighted composition. Targeted primary-source audit of
Suzuki 2026 and the two CCM parent papers found the parity and orthogonal-polynomial ingredients,
not equations `(1)`--`(7)`. External expert/literature audit remains required; no categorical
novelty claim is made.

## Scientific-method log

- **2026-07-22 — hostile parity control.** Claim “even cyclic density kills odd boundary” was
  rejected: odd Jacobi modes are actual nonzero source vectors and couple directly to sine modes.
- **2026-07-22 — exact source prediction.** Odd central-binomial extraction predicted `(1)`;
  normalization, literal Fourier coefficient, and tail identity all survived formal proof.
- **2026-07-22 — global falsifier.** Pointwise ranks might fail to define one operator. Absolute
  source-coordinate zero-padding proves `(6)`--`(7)`, closing this falsifier without a common rank.
- **2026-07-22 — anti-rediscovery audit.** Generic capacity/Gram layer demoted to formal closure.
  Scientific advance is only actual odd Gamma-Jacobi exhaustion plus source-weighted coherent
  schedule. Next admissible work must change Green--Schur/Euler placement, not reprove positivity.
