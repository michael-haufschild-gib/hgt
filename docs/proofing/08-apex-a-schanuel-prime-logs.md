# APEX-A Proof Attempt: Schanuel-For-Prime-Logs

Source: `docs/consolidated/08-conjectures-required.md` §3.

Claim status: `[OPEN CORE]`.

## Target Claim

For the prime logarithms,

```text
corank^(T) = infinity for all T >= 2
<=> {log p} are Q-algebraically independent
<=> trdeg = infinity
<=> DSS value-axis target.
```

The first genuinely open rung is already degree 2 beyond the known homogeneous
two-prime bottom.

## Proof Attempt

The proven floor is Q-linear independence. If

```text
sum_i a_i log p_i = 0,  a_i in Z,
```

then exponentiating gives

```text
prod_i p_i^{a_i} = 1,
```

so unique factorization forces all `a_i = 0`. This proves the `T=1`
corank floor.

Try degree 2 for two primes. Put

```text
x = log p,  y = log q,  alpha = x / y.
```

First `alpha` is transcendental. If `alpha` were rational, say `a/b`, then
`p^b = q^a`, impossible for distinct primes. If `alpha` were algebraic
irrational, then

```text
p = q^alpha
```

would contradict Gelfond-Schneider, since `q` is algebraic not 0 or 1 and
`alpha` is algebraic irrational, making `q^alpha` transcendental.

Now suppose a homogeneous degree-2 relation exists:

```text
A x^2 + B x y + C y^2 = 0,  A,B,C in Q.
```

Dividing by `y^2 != 0` gives

```text
A alpha^2 + B alpha + C = 0.
```

Since `alpha` is transcendental, `A = B = C = 0`.

The same argument proves every homogeneous relation in two prime logs:

```text
sum_{k=0}^d c_k x^k y^{d-k} = 0
=> sum_{k=0}^d c_k alpha^k = 0
=> all c_k = 0.
```

## Weakened Theorem Proved Here

**Theorem APEX-A-W.** For two distinct primes `p,q`, every fixed-degree
homogeneous family

```text
{ (log p)^k (log q)^(d-k) : 0 <= k <= d }
```

is Q-linearly independent.

Proof: the Gelfond-Schneider argument above.

## Where The Full Proof Fails

The full apex needs nonhomogeneous and many-prime algebraic independence. A
general degree-`<=T` relation for two logs has the form

```text
sum_{d=0}^T y^d P_d(alpha) = 0.
```

The transcendence of `alpha = log p / log q` does not exclude algebraic
relations involving both `alpha` and `y = log q`. Proving no such relation is
essentially Schanuel-level.

For three or more primes, even homogeneous degree-2 relations such as

```text
sum_{i,j} c_ij log p_i log p_j = 0
```

are not killed by a single ratio argument. Baker controls only linear forms in
the logarithms, not polynomial forms.

## Missing Input

1. A new transcendence theorem upgrading Baker linear independence to algebraic
   independence for prime logarithms.
2. At minimum, a proof that all quadratic monomials `log p_i log p_j` are
   Q-linearly independent for arbitrarily many primes.
3. A bridge from that algebraic independence to the DSS/Stieltjes value column.
