# An exact Xi determinant forces logarithmically enhanced weak-trace singular values

- **ID:** `xi-determinant-logarithmic-singular-value-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HILBERT--POLYA IDEAL LAW / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** If a compact self-adjoint operator has a genus-one regularized characteristic
  determinant equal to the centered completed zeta function up to a zero-free entire factor, then
  its singular values satisfy `s_n~(log n)/(pi n)` in the two-sided convention.  Thus every exact
  compact Hilbert--Polya realization must live in all Schatten classes `S_(1+epsilon)` but not in
  trace class, with partial trace growth asymptotic to `(log n)^2/(2pi)`.

## Exact determinant hypothesis

Let `A` be a compact self-adjoint operator on a separable Hilbert space and assume `A in S_2`.  Put

```text
D_A(z)=det_2(1-zA).                                        (1)
```

Assume that there is a zero-free entire function `H` such that

```text
XiC(z)=H(z)D_A(z).                                         (2)
```

Here `XiC(z)=xi(1/2+iz)` is the centered completed zeta function.  The normalization and the
zero-free factor are unrestricted; only the divisor identity is used.

Since `A` is self-adjoint, every nonzero zero of `D_A` is real and is the reciprocal of a nonzero
eigenvalue of `A`, with algebraic multiplicity.  Therefore `(2)` already implies RH and gives the
multiset identity

```text
{1/lambda:lambda in Spec(A),lambda!=0}=Div(XiC).            (3)
```

The theorem below extracts the ideal class forced by this exact divisor transport.

## Reciprocal spectral counting `[PROVED]`

Let

```text
n_A(s)=#{k:s_k(A)>=s},  s>0,                               (4)
```

where singular values include multiplicity and are ordered decreasingly.  The divisor of `XiC` is
even.  With the two-sided convention, `(3)` gives

```text
n_A(1/T)=2N_zeta(T)+O(1),                                  (5)
```

where `N_zeta(T)` counts nontrivial zeta zeros with ordinates in `(0,T]`, including multiplicity.
The `O(1)` allows endpoint conventions and a finite exceptional prefix.

The Riemann--von Mangoldt formula is

```text
N_zeta(T)
 =T/(2pi) log(T/(2pi))-T/(2pi)+O(log T).                   (6)
```

Substituting `T=1/s` in `(5)` gives

```text
n_A(s)
 =1/(pi s) log(1/(2pi s))-1/(pi s)+O(log(1/s))             (7)
```

as `s->0+`.  In particular,

```text
n_A(s)~(1/(pi s))log(1/s).                                 (8)
```

## Singular-value inversion `[PROVED]`

The monotone inverse of `(8)` satisfies

```text
s_n(A)~(log n)/(pi n).                                     (9)
```

A direct squeeze proves this without a Tauberian theorem.  Fix `epsilon>0`.  For large `1/s`,
`n_A(s)` lies between `(1-epsilon)(pi s)^(-1)log(1/s)` and
`(1+epsilon)(pi s)^(-1)log(1/s)`.  Evaluate these inequalities at

```text
s=(1+/-2epsilon)log n/(pi n).
```

Since `log(1/s)=log n+O(log log n)`, monotonicity of `n_A` squeezes `s_n` between the two trial
values.  Letting `epsilon->0` proves `(9)`.

## Exact ideal consequences `[PROVED]`

Equation `(9)` yields

```text
A in S_q for every q>1,
A notin S_1,
A in S_2.                                                   (10)
```

It also gives the partial trace asymptotic

```text
sum_(k<=n) s_k(A)~(log n)^2/(2pi),                          (11)
```

by comparison with `sum_(k<=n)(log k)/k`.

In particular, `A` is not in the usual weak trace class `S_(1,infinity)`, because

```text
n s_n(A)~(log n)/pi->infinity.                              (12)
```

Define the logarithmically enhanced weak-trace ideal

```text
I_Xi={B compact:sup_(n>=2) n s_n(B)/log n<infinity}.        (13)
```

Then `(9)` says that every exact realization `(2)` lies on the nonzero boundary of `I_Xi`:

```text
lim_(n->infinity) n s_n(A)/log n=1/pi.                      (14)
```

Thus the correct Hilbert--Polya carrier is neither trace class nor merely Hilbert--Schmidt.  It has
a distinguished logarithmically enhanced weak-trace law fixed by the completed divisor.

## Genus-one compatibility `[PROVED]`

The ideal law explains the canonical determinant order.  Since `A in S_2`, the regularized product

```text
det_2(1-zA)=product_k (1-z lambda_k)exp(z lambda_k)          (15)
```

converges.  Since `A notin S_1`, the unregularized product need not converge.  The exponent of
convergence of the reciprocal spectrum is exactly one, so the genus-one factors in `(15)` are
minimal.  This matches the genus-one Hadamard factorization of `XiC`.

The zero-free factor `H` in `(2)` must still be fixed by completion.  Equation `(15)` determines the
divisor but not the exponential normalization.

## Consequence for polynomial Fock incidence `[PROVED]`

For the critical-prime polynomial-Fock Toeplitz operator `T_m` with finite `m>4`,
`critical-prime-fock-schatten-threshold-law.md` proves

```text
T_m in S_q iff q>m/(m-4).                                  (16)
```

The threshold `m/(m-4)` is strictly greater than one.  Choose

```text
1<q<=m/(m-4).
```

Then `(16)` gives `T_m notin S_q`, whereas every exact `Xi` determinant carrier satisfies `(10)`.
Therefore

```text
XiC != H det_n(1-zT_m)                                     (17)
```

for every zero-free `H`, every determinant order, and every finite polynomial degree `m`, whenever
the determinant zeros are the reciprocal eigenvalues of `T_m`.

The positive conclusion is:

> A viable analytic RKHS incidence must be modified until its compact spectral carrier has
> `s_n asymp (log n)/n`, or the Hilbert--Polya operator must be constructed from a different
> non-Toeplitz incidence.  Polynomial confinement can host the prime samples but cannot supply the
> exact completed spectral density.

## Attacks and exact boundary

1. **Zero-free gauge attack.** Multiplication by `H` does not change the divisor, so it cannot alter
   `(7)`--`(14)`.
2. **Multiplicity attack.** Both Riemann--von Mangoldt counting and the determinant count include
   multiplicity.
3. **Finite-prefix attack.** Adding or deleting finitely many eigenvalues changes `(5)` by `O(1)`
   and leaves every asymptotic unchanged.
4. **Sign attack.** Singular values forget the signs of reciprocal eigenvalues.  Evenness of `XiC`
   supplies the factor `2` in `(5)`.  A positive-ordinate-only convention changes the leading
   constant from `1/pi` to `1/(2pi)` but not the ideal.
5. **General determinant attack.** An arbitrary holomorphic operator pencil can manufacture any
   entire determinant.  The theorem applies to the characteristic form `det_2(1-zA)` of one fixed
   compact self-adjoint operator, which is the spectral content required by Hilbert--Polya.
6. **Converse attack.** The singular-value law is necessary, not sufficient.  Many self-adjoint
   compact operators have the same singular-value asymptotic but the wrong signed eigenvalues and
   determinant.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The proof is an immediate synthesis of the classical
Riemann--von Mangoldt formula, spectral mapping for compact self-adjoint operators, and canonical
regularized determinants.  The ideal `I_Xi` and its RH-architecture interpretation are useful, but
the parent mechanism is standard and the conclusion follows directly once an exact determinant is
assumed.

## Lean status

The main determinant law is now formalized on the actual infinite-dimensional Hilbert--Carleman
carrier.  `XiDeterminantLogarithmicSingularValueLaw.lean` proves the reciprocal-spectrum counting
law and the sharp approximation-number asymptotic.  `XiDeterminantIdealConsequences.lean` proves
membership in every `S_q`, `q>1`, failure of `S_1`, the exact logarithmically enhanced weak-trace
residue, failure of ordinary weak `S_1`, and the partial-trace asymptotic.
`XiDeterminantGenusOneMinimality.lean` proves exact genus-one minimality.

`PositiveXiDeterminantExclusion.lean` proves unconditionally that no positive Hilbert--Schmidt
operator can be an exact `XiC` Hilbert--Carleman determinant carrier: Hardy's positive zero and
evenness produce a negative determinant zero, whose reciprocal eigenvalue contradicts positivity.
`PolynomialFockCriticalPrimeDeterminantExclusion.lean` specializes this to the literal polynomial
critical-prime incidence operator.  Its targeted leaf build and axiom audit passed with only
`propext`, `Classical.choice`, and `Quot.sound`.

The same modules define the regularization-order-independent interface
`HasReciprocalEigenvalueZeroSet` and prove the closed theorem
`polynomialCriticalPrimeSamplingIncidence_not_exists_exactXiSpectralZeroFunction`: no finite
polynomial degree admits any zero-free-gauge Xi determinant function whose nonzero zeros are
exactly the reciprocal eigenvalues of the actual incidence operator.  This is precisely the
“every determinant order, whenever determinant zeros are reciprocal eigenvalues” scope of `(17)`;
it does not assume an implementation-specific determinant formula.

The card is not yet dependency-closed.  Equation `(16)` is still represented only by
`HasCriticalPrimeFockSchattenLaw`; no theorem supplies that interface for
`polynomialCriticalPrimeSamplingIncidence`.  The actual incidence is already constructed and is
proved positive, compact for `m>4`, and non-trace-class, but its exact all-`q` Schatten threshold
still requires the doubling-Fock Toeplitz averaging theorem and the adapted-tube comparison.
Therefore this card remains at Stage 2.

## Gates

- [x] exact divisor-to-reciprocal-spectrum identity stated
- [x] Riemann--von Mangoldt converted to singular-value counting
- [x] monotone inversion proved
- [x] Schatten and partial-trace consequences proved
- [x] minimal genus-one determinant class identified
- [x] every finite polynomial-Fock incidence excluded as the exact determinant carrier
- [x] positive target ideal stated
- [x] parent-theory novelty claim rejected
- [ ] complete unconditional Lean formalization
