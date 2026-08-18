# Every exact Hilbert--Polya operator is trace-class over a prime-indexed RVM skeleton

- **ID:** `prime-indexed-rvm-trace-class-hp-normal-form`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HILBERT--POLYA NORMAL FORM / BRIDGE
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The prime basis and the smooth archimedean Riemann--von Mangoldt quantiles define
  a source-marked compact self-adjoint skeleton with the exact two-term zero-counting law.  Under
  RH, the reciprocal-zero operator differs from this skeleton by trace class.  Thus a direct
  Hilbert--Polya construction may be normalized to one source-defined backbone plus one
  trace-class divisor correction.

## 1. Prime phase space and archimedean quantiles

Let `p_n` be the `n`th prime and put

```text
H_P=ell^2({primes}),
U_t e_(p_n)=p_n^(-it)e_(p_n).                              (1)
```

At prime cutoff `N`, the restricted unitary flow has exactly `pi(N)` rationally independent
frequencies.  Thus `(1)` transports the full finite-prime phase carrier rather than attaching only
an unmarked Hilbert-space dimension.

Define the smooth Riemann--von Mangoldt function

```text
M(T)=T/(2pi) log(T/(2pi e))+7/8.                           (2)
```

It is strictly increasing for `T>2pi`.  For every `n>=1`, let `t_n>2pi e` be the unique solution
of

```text
M(t_n)=n.                                                  (3)
```

On `H_P`, define

```text
Q_+ e_(p_n)=t_n^(-1)e_(p_n),
Q=Q_+ directSum (-Q_+) on H_P directSum H_P.               (4)
```

The prime clock `U_t` commutes with `Q_+`.  Completion therefore assigns a smooth spectral scale to
each marked prime channel without identifying or deleting the independent prime phases.

## 2. Exact smooth RVM spectral law `[PROVED]`

Since `M` is increasing, the positive reciprocal-spectrum count of `Q` is

```text
#{n:t_n<=T}=floor(M(T))                                    (5)
```

after the harmless initial convention.  Thus the two-sided reciprocal spectrum of `Q` has count

```text
2 floor(M(T))
 =T/pi log(T/(2pi e))+7/4+O(1).                            (6)
```

Inverting `(3)` gives

```text
t_n~2pi n/log n,
t_n^(-1)~log n/(2pi n).                                   (7)
```

The singular values of the signed double occur twice, so

```text
s_k(Q)~log k/(pi k).                                      (8)
```

Consequently

```text
Q in S_q for every q>1,
Q notin S_1,
Q in S_2.                                                  (9)
```

The regularized determinant is the source-defined all-real entire function

```text
det_2(1-zQ)=product_(n>=1)(1-z^2/t_n^2).                  (10)
```

At cutoff `N`, `Q_+` has rank exactly `pi(N)` and `Q` has rank `2pi(N)`.  Equations `(1)` and `(4)`
therefore realize simultaneously the prime-rank floor and the exact logarithmically enhanced
weak-trace ideal required by an `Xi` determinant.

## 3. Trace-class reciprocal divisor relocation `[PROVED]`

Let `gamma_n` be the positive ordinates of the nontrivial zeta zeros, ordered with multiplicity.
The classical Riemann--von Mangoldt formula is

```text
N(T)=M(T)+O(log T).                                       (11)
```

At an ordinate `gamma_n`, the endpoint convention and a possible multiplicity change the count by
at most `O(log gamma_n)`, also by `(11)`.  Hence

```text
M(gamma_n)=n+O(log gamma_n).                              (12)
```

Both `gamma_n` and `t_n` are asymptotic to `2pi n/log n`.  On the interval between them,

```text
M'(T)=1/(2pi) log(T/(2pi)) asymp log n.                   (13)
```

The mean-value theorem applied to `(3)` and `(12)` gives

```text
gamma_n-t_n=O(1).                                         (14)
```

Therefore

```text
|gamma_n^(-1)-t_n^(-1)|
 =O(t_n^(-2))
 =O((log n)^2/n^2),                                      (15)
```

and in particular

```text
sum_n |gamma_n^(-1)-t_n^(-1)|<infinity.                  (16)
```

Assume RH and define the target-ordered reciprocal-zero operator

```text
A_Xi,+ e_(p_n)=gamma_n^(-1)e_(p_n),
A_Xi=A_Xi,+ directSum (-A_Xi,+).                          (17)
```

Then `(16)` says exactly

```text
A_Xi-Q in S_1.                                            (18)
```

Moreover, the even Hadamard product gives

```text
det_2(1-z A_Xi)=XiC(z)/XiC(0).                            (19)
```

Multiplicity is already included in `(17)`--`(19)`.

More invariantly, let `A` be any compact self-adjoint exact Hilbert--Polya operator whose nonzero
reciprocal spectrum is the centered `Xi` divisor.  On the closure of its nonzero spectral
subspace, the spectral theorem supplies a unitary `V` which orders the positive and negative
eigenvectors as in `(17)`.  Equation `(18)` then becomes

```text
V A V^* - Q in S_1.                                      (20)
```

An arbitrary zero eigenspace is irrelevant and may be split off.

## 4. Positive normal form

Every exact compact Hilbert--Polya architecture can therefore be sought in the form

```text
A=Q+K,
K=K^*,
K in S_1,                                                 (21)
```

where:

1. `Q` transports the marked infinite prime phase carrier;
2. the quantile rule `(2)` supplies the one smooth archimedean spectral direction;
3. `K` relocates the smooth real atoms to the exact completed divisor;
4. the identity

   ```text
   det_2(1-z(Q+K))=XiC(z)/XiC(0)                          (22)
   ```

   is the remaining RH-bearing incidence theorem.

Conversely, a source-defined self-adjoint `K in S_1` satisfying `(22)` proves RH immediately,
because the characteristic determinant of `Q+K` has only real zeros.

The positive law is:

> Finite-degree completion need only build the smooth Riemann--von Mangoldt skeleton.  The
> all-prime source must separately build a trace-class, phase-faithful divisor relocation on the
> same marked prime Hilbert space.

Trace class is small enough to leave the complete RVM Weyl law unchanged, but large enough to move
every individual atom.  Thus the leading spectral density is no longer the open problem.

## 5. Relation to the Hedenmalm metric classification

`hedenmalm-theta-pair-divisor-supported-metric-law.md` proves that every positive source-core metric
symmetrizing the 2026 theta pair is a nonlocal Fourier measure supported on real `Xi` zeros.  The
present skeleton supplies smooth real atoms `t_n`; the operator `K` in `(21)` is the reciprocal
trace-class version of relocating those atoms to the divisor measure.

Together the two laws isolate one common open object:

```text
weighted all-prime Euler tail
  -> source-defined trace-class relocation K
  -> conservative divisor-supported theta metric.         (23)
```

Constructing `K` by first listing `gamma_n` gives `(17)` and is target-fed.  A proof must instead
derive `(21)`--`(23)` from the completed Euler source and preserve the prime labels cofinally.

## 6. Attacks and exact boundary

1. **This is a normal form, not an RH proof.**  Under RH, `(17)` manufactures the correction from
   the target divisor.  The source-defined construction of `K` remains open.
2. **The prime basis is not the spectrum.**  The prime labels carry the independent phases through
   `(1)`; the archimedean quantiles assign the smooth reciprocal eigenvalue scale through `(4)`.
3. **Unitary ordering can lose provenance.**  Equation `(20)` alone does not prove that an arbitrary
   exact operator was built from primes.  A viable construction must define `K` on the marked basis
   before the determinant identity, not transport prime labels onto an already-known spectrum.
4. **Trace class is in reciprocal coordinates.**  The ordinate displacement is only `O(1)`, while
   the reciprocal displacement is summable by `(15)`.
5. **Finite prefixes do not matter.**  Altering the first finitely many `t_n` changes `Q` by finite
   rank and leaves every conclusion intact.
6. **Simplicity is not assumed.**  Repeated ordinates are repeated eigenvalues and `(16)` remains
   valid.
7. **The completion law is zeta-specific here.**  Other finite-degree completed `L`-functions use
   their own conductor and Gamma Weyl term, but the same quantile construction applies whenever a
   Riemann--von Mangoldt formula with `O(log T)` remainder is available.

## 7. Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The proof composes the classical
Riemann--von Mangoldt formula, monotone quantile inversion, the spectral theorem, and the elementary
criterion for a diagonal difference to be trace class.  Searches through 11 July 2026 did not
locate this exact prime-indexed normal form, but the mathematical content is directly derivable
from standard parents and does not clear the novelty gate.

Its research value is architectural: it removes both the prime-rank and leading-Weyl-law
bottlenecks and identifies the exact remaining carrier as a trace-class source-to-divisor
incidence.

## Gates

- [x] prime basis carries exactly `pi(N)` cutoff phases
- [x] archimedean quantile skeleton defined without zero input
- [x] full smooth two-term RVM count proved
- [x] exact `Xi` singular ideal proved for the signed skeleton
- [x] reciprocal zero-to-quantile displacement proved trace class under RH
- [x] invariant unitary normal form stated
- [x] source provenance separated from target-fed ordering
- [x] novelty claim rejected as a bridge
- [ ] source-defined trace-class correction `K`
- [ ] cofinal zero-preserving determinant identity
