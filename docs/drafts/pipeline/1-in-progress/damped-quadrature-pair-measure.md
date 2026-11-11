# A damped quadrature candidate for the all-bandwidth ceiling

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Positivity ceiling](../3-formalized/fable-route-closures.md).

## Candidate

Write `c=1/√2`. For `B>√2`, `k>0`, and
`c + (k/2) asin(√2/B) < π/2`, set

```
w(t) = (√(t²+B²)−t)/B,
q = c tan(c + (k/2) asin(√2/B)),
R(t) = exp(−t) (t−2q)/(t+2q) w(t)^k,
S(t) = π(1+2/t²) (1+R(t))/(1−R(t)).
```

Branches are analytic in `Re t>0`, with positive square root and positive `w`
on the positive real axis. Interpret `S(2πy)` as the imaginary Cauchy transform
of a proposed even measure at `iy`.

The delayed factor suggests exact form factor `F(α)=α` for `0<α<1`.
The prescribed `q` puts the first boundary pole at `t=i√2`, where `1+2/t²`
vanishes. The candidate mass at the origin is

```
A = (1 + 1/q + k/B)/2.
```

At `k=0`, this is the bandlimited quadrature value
`1/2 + cot(1/√2)/√2`. That undamped candidate has a negative form factor
immediately above frequency one. Damping replaces its first Fourier atom by
a Bessel kernel: the inverse Laplace transform of `w(t)^ν` is
`ν J_ν(Bu)/u`. The candidate is intended to repair the negative interval while
retaining `A>13/10`. The concrete parameter conjecture is `B=6`, `k=1/5`;
both the mass inequality and global Fourier positivity still require proof.

## Exact sign problem

Put `Kν(u)=ν Jν(Bu)/u` for `u>0` and `r(t)=(t−2q)/(t+2q)`.
The proposed form factor has the delayed expansion

```
F(α) = α + Σ_{1≤n≤α} L⁻¹[(1+2/t²) r(t)^n w(t)^(kn)](α−n).
```

In particular, on `1<α<2`, writing `u=α−1`, its sign reduces to

```
F(1+u) = 1+u + Kk(u) + ∫₀ᵘ Kk(v) h(u−v) dv,
h(u) = −2u + 2/q − (4q+2/q) exp(−2qu).
```

The Bessel transform follows from the Laplace formula
[DLMF 10.22.49](https://dlmf.nist.gov/10.22.E49), or by integrating the
Laplace transform of `Jν` in its transform variable. Positivity of `Kk`
near zero does not determine the sign of this convolution. Later intervals
include every delayed term; checking the first interval alone is insufficient.

## Obligations

1. Prove that the Cauchy transform represents a positive measure, including
   the cancelled first pole and the continuous spectrum above `B`.
2. Choose exact parameters and prove `A>13/10`.
3. Prove nonnegativity of the entire form factor. This is unresolved;
   positive pair measure alone is insufficient.
4. Prove the sinc-testing identity and regularize within the continuous,
   integrable-perturbation class for each finite bandwidth.

No numerical search, complete paper proof, or Lean theorem. Neither the
candidate transform nor its proposed positivity is an admitted input.
