# Infinite shell codiagonals are closable exactly in the square-summable regime

- **ID:** `high-shell-codiagonal-closability-dichotomy`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED PARENT THEORY] [NOT AN RH PROOF]`
- **Parents:** closed operators on Hilbert direct sums, the Riesz representation theorem, and
  `../high-exponent-shell-zero-free-common-divisor-law.md`

## Statement

Let `H` be a nonzero complex Hilbert space, let `a=(a_m)_(m>=0)` be a scalar sequence, and let

```text
D=c_00(N;H) subset ell^2(N;H).
```

On `D` define the weighted shell codiagonal

```text
C_a(x)=sum_m a_m x_m.                                    (1)
```

Then the following are equivalent:

```text
(i)   C_a is closable as an operator ell^2(N;H)->H;
(ii)  a belongs to ell^2(N);
(iii) C_a extends uniquely to a bounded operator
      ell^2(N;H)->H.                                     (2)
```

In the square-summable case,

```text
||C_a||=||a||_2.                                         (3)
```

Consequently the unweighted codiagonal `C_1` is not closable.  More generally, there is no
genuinely unbounded closed scalar row which erases infinitely many orthogonal shell labels while
acting by one fixed scalar weight on each label.

## Proof

Assume first that `a in ell^2`.  Cauchy--Schwarz gives, for every finitely supported `x`,

```text
||C_a x||
 <=sum_m |a_m| ||x_m||
 <=||a||_2 (sum_m ||x_m||^2)^(1/2).                      (4)
```

Thus `C_a` extends uniquely by density to a bounded operator of norm at most `||a||_2`.  Choose a
unit vector `v in H`.  For each finite set `F`, put

```text
x_m=conj(a_m)v/(∑_(j in F)|a_j|^2)^(1/2),  m in F,
x_m=0,                                      m notin F.  (5)
```

Then `||x||=1` and

```text
||C_a x||=(sum_(m in F)|a_m|^2)^(1/2).                  (6)
```

Taking an increasing exhaustion proves the reverse norm inequality and hence `(3)`.  A bounded
operator is closed, so `(ii)` implies `(iii)` and `(i)`.

Conversely, suppose `a` is not square-summable.  Put

```text
S_N=sum_(m<N)|a_m|^2 ->+infinity                        (7)
```

after discarding an initial segment on which `S_N=0`, and choose a nonzero `v in H`.  Define

```text
x^(N)_m=conj(a_m)v/S_N,   m<N,
x^(N)_m=0,                m>=N.                          (8)
```

Then `x^(N) in D` and

```text
||x^(N)||^2=||v||^2/S_N ->0,
C_a x^(N)=v.                                             (9)
```

If `C_a` were closable, every graph sequence with input converging to zero and output converging
would have output limit zero.  Equation `(9)` contradicts this because `v!=0`.  Thus `(i)` implies
`(ii)`, completing `(2)`.

## Application to the common-divisor shell family

For every `m>=12`, the high-exponent shell theorem constructs an orthogonal positive four-unit
source sector whose completed logarithmic current has the same strict Xi divisor.  A scalar row
which sends every normalized shell sector to the same current has weights `a_m=1`.  The theorem
shows that this row has no closed extension from the Hilbert direct sum; calling it an unbounded
closed codifferential is false.

The prime-two amplitude in the unnormalized shell multiplier behaves like `2^(-ms)`.  On every
strict half-plane this is square-summable in `m`, so the corresponding *linear amplitude* row is
bounded.  But logarithmic differentiation removes the factor `2^(-ms)` up to the additive clock
constant `m log 2`; it returns the common divisor current with unit residue.  Hence amplitude
summability does not make the fixed-current row closable.

The positive structural conclusion is exact:

```text
shell label retained through pole cancellation
  -> operator-valued multiplication graph
  -> fixed-current quotient only after graph incidence. (10)
```

Any scalar-weighted Hilbert codiagonal either has square-summable weights and is already bounded,
or is nonclosable.  The surviving charged graph must therefore retain a non-scalar shell/source
coordinate or change the ambient bornology before taking the logarithmic quotient.

## Classification and Lean decision

The dichotomy is standard Hilbert-space operator theory, so it is not new scientific knowledge.
Its proof value is route-selective: it strengthens the existing bounded-codiagonal no-go to a
closed-graph no-go and prevents the live RH card from hiding the common current in an unspecified
unbounded scalar row.

The theorem is dependency-closed on paper.  A faithful Lean formalization should use the existing
`lp` and `Finsupp` coefficient carriers and prove the singular graph sequence `(8)`--`(9)`.  No
Lean build is warranted until the current formal corpus is checked for the required closability
interface.

## Gates

- [x] square-summable weighted codiagonal extended boundedly
- [x] exact operator norm computed
- [x] nonsummable weights shown nonclosable by an explicit graph-null sequence
- [x] unweighted shell codiagonal ruled out as a closed operator
- [x] natural prime-two amplitude separated from the logarithmic fixed current
- [x] operator-valued multiplication graph forced as the positive successor
- [ ] formalize the exact closability dichotomy in Lean
- [ ] construct the shell-label-preserving charged multiplication graph
- [ ] RH

