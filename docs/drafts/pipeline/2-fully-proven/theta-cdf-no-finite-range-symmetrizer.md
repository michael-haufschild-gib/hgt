# Theta CDF quotient has no coercive finite-range Fourier symmetrizer

- **ID:** `theta-cdf-no-finite-range-symmetrizer`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM and structural no-go
- **Routes:** STC, CSB, U, K-RVM, MPLF, theta source transport
- **Status:** `[PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** [exact CDF-action quotient](../1-in-progress/theta-quantile-fourier-action-quotient.md), [theta action growth](theta-cdf-crossfrequency-rvm-capacity.md), strict log-concavity and double-exponential tails of the literal theta density.

## Theorem

Let `D` be the exact theta quotient on the mean-zero Fourier space
`ℓ²(ℤ\{0})`:

```text
D_(m,n) = (Φ_m−Φ_(n−m))/(2πn),
Φ_n = ∫₀¹ q(t)(1−cos(2πnt))dt,
Φ_−n = Φ_n.
```

There is **no** bounded self-adjoint operator `G` and constants
`c>0`, `W∈ℕ` such that

```text
⟨u,Gu⟩ ≥ c‖u‖²                    for every u,
G_(m,n)=0                         when ||m|−|n||>W,
GD=D*G.
```

The range condition allows arbitrary mixing between `+n` and `−n`
at each absolute frequency and arbitrary mixing of finitely many
neighboring absolute frequencies. Thus it includes all uniformly
bounded block-local repairs of the positive opposite-frequency
metric. A symmetrizing metric, if one exists, must have unbounded
absolute-frequency range, fail boundedness, or fail uniform
coercivity. This theorem does not decide whether any such metric
exists and does not establish RH.

## Fixed-shift action lemma

For every fixed `a∈ℤ`, the literal theta action satisfies

```text
Φ_(n+a)−Φ_n = o(1/n)             as n→+∞.                 (1)
```

Here is an endpoint proof that does not differentiate the coarse
`Φ_n=log log n+O(log log n/log n)` asymptotic. Let `k` be the positive
even theta density, `M=∫k`, `F(x)=M⁻¹∫_(−∞)^x k`, `Q=F⁻¹`, and
`q(t)=M/k(Q(t))`. Write `I(x)=∫_(−∞)^x k`. Then

```text
t q(t) = I(x)/k(x)              when t=F(x).               (2)
```

On the left half-line, strict log-concavity makes `I/k`
nondecreasing. Indeed, with `g=log k`,

```text
I(x)/k(x) = ∫₀^∞ exp(g(x−v)−g(x))dv,
```

and each integrand is nondecreasing in `x`, because
`g'(x−v)≥g'(x)`. The double-exponential left tail forces
`g'(x)→+∞` as `x→−∞`. Concavity gives the tangent bound
`I(x)/k(x)≤1/g'(x)` there. Consequently `tq(t)` increases from
zero on a left-end interval and has finite total variation and an
integrable derivative. Reflection gives the same endpoint property
for `(1−t)q(t)` on a right-end interval. Both functions are smooth
on compact subintervals.

For integral `a`, set

```text
g_a(t)=q(t)(1−exp(2πiat)).
```

Near zero, write `g_a(t)=[tq(t)](1−exp(2πiat))/t`; the second
factor extends smoothly to zero. Near one, use `(1−t)q(t)` and
the fact `exp(2πia)=1`. The preceding bounded-variation argument
shows `g_a∈W¹,¹(0,1)` with zero endpoint traces. Hence integration
by parts and the Riemann–Lebesgue lemma give

```text
Φ_(n+a)−Φ_n
  = Re ∫₀¹ g_a(t) exp(2πint)dt
  = Re [−1/(2πin) ∫₀¹ g_a'(t) exp(2πint)dt]
  = o(1/n).
```

The existing sharp action law also gives `Φ_n→+∞`. The proof of
(1) uses only endpoint cancellation, log-concavity and the tail
hazard; it does not use a zero-location statement.

## Symmetrizer contradiction

Suppose `G` has the stated properties. Fix a nonzero row index `m`
and put `S_m=Σ_k G_(m,k)`. This is a finite sum because of the
range condition. For `n→+∞`, every `k` in this fixed row is fixed,
so (1), the matrix formula and `Φ_n→∞` yield

```text
(GD)_(m,n)
 = Σ_k G_(m,k)(Φ_k−Φ_(n−k))/(2πn)
 = −S_m Φ_n/(2πn) + O_m(1/n).                             (3)
```

In the opposite product, only `k` with `||k|−n|≤W` occur. Each is
`+n+O(W)` or `−n+O(W)`. For fixed `m`, evenness and (1) imply

```text
D_(k,m)=(Φ_k−Φ_(m−k))/(2πm)=o(1/n)
```

uniformly over these finitely many shifts. Boundedness of `G`
bounds every matrix entry by `‖G‖`, so

```text
(D*G)_(m,n)=o_m(1/n).                                      (4)
```

Comparing (3) and (4) under `GD=D*G`, and multiplying by `n`,
gives `S_m Φ_n=O_m(1)+o(1)`. Since `Φ_n→∞`, **every row sum of
`G` is zero**.

Let `u_N` have coefficient one at every index with `1≤|n|≤N`
and zero elsewhere. For rows with `|m|≤N−W`, the entire row of
`G` lies inside the support of `u_N`; hence `(Gu_N)_m=S_m=0`.
Only the at most `2W` boundary rows inside the support can
contribute to `⟨u_N,Gu_N⟩`. Their entries are bounded by `‖G‖`,
and each has at most `4W+2` nonzero columns, so this quadratic
form is bounded independently of `N`. Coercivity would instead
give `⟨u_N,Gu_N⟩≥2cN`, a contradiction.

## What changes at the frontier

The earlier paired-block result showed that its particular
frequency-folded metric leaves a cross-frequency defect. This
theorem rules out **every** bounded uniformly positive metric of
fixed absolute-frequency range, even one optimized with arbitrary
off-diagonal entries within that range. The obstruction is an
asymptotic direction mismatch in the exact quotient, followed by
the impossibility of a coercive finite-range operator with zero
row sums. It is independent of spectral mass and of hypothetical
off-line zeros.

The positive survivor is a precise architectural requirement:
any source-faithful Hilbert symmetrization of this quotient must
couple arbitrarily distant absolute Fourier frequencies, or use
a singular/noncoercive metric. This does not supply the required
theta-specific orientation of that nonlocal coupling. The generic
endpoint argument can hold for off-line positive-source
countermodels too, so it must not be promoted to a sufficient RH
criterion.

The canonical source metric `T=PM_hP` already occupies the allowed
class: multiplication by the quantile speed reciprocal `h` becomes
long-range in Fourier space, and `h→0` at the endpoints makes `T`
noncoercive. Its rank-one feedback remains the unresolved global
phase condition. The theorem explains why replacing that singular
source geometry by a uniformly positive finite-frequency repair
cannot close the proof chain.

**Audit:** The proof is dependency-closed on paper given the cited
source identities and standard one-dimensional Fourier analysis.
The action quotient, fixed-shift lemma and infinite-operator no-go
are not yet formalized in Lean. External novelty has not been
established. No frontier-map change was made.
