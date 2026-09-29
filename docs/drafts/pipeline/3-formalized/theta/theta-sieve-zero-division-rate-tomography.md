# Cofinal prime deletion exposes the oscillatory rate kernel of zero division

- **ID:** `theta-sieve-zero-division-rate-tomography`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean); certificate
  [`theta-sieve-zero-division-rate-tomography-formalized.md`](theta-sieve-zero-division-rate-tomography-formalized.md)
- **Routes:** STC, CSB, U, MPLF, RG-HF, RHist
- **Status:** `[PROVED HERE ON PAPER] [NOT AN RH PROOF]`
- **Dependencies:** [zero-division seed transfer](../../3-formalized/theta/theta-euler-zero-division-seed-transfer.md), [prime-deletion source identity](../../3-formalized/theta/theta-prime-deletion-spectral-escape.md), [all-sieve seed projector](../../3-formalized/theta/theta-all-sieve-seed-projector-translation-cone.md). The positive-measure abscissa argument is formalized for these kernels in `ThetaZeroDivisionRateTomography` (`not_eventually_nonneg_of_pole`).

## Statement

Use the Fourier coordinate `z` of `F(z)=XiC(z)` and let `P(w)` be a nonconstant real polynomial formed from finitely many zero factors `(1-w/α²)(1-w/conj(α)²)`, with multiplicities, where `F(α)=0`, `α≠0`, and `Re α≠0`. Let `r(w)=N(w)/P(w)` be a nonzero real rational function with `N(0)=0` and `deg N≤deg P`; cancel common factors before considering its poles. Assume every remaining pole still comes from these nonzero Xi zeros. The [zero-division transfer](../../3-formalized/theta/theta-euler-zero-division-seed-transfer.md) constructs a real even source `u` with Fourier transform `F(z)r(z²)` and a physical-half-line causal representation

```text
u(x)=c k(x)+∫₀∞ K(s)k(x+s)ds,                 x≥0,       (1)
```

where `k` is the literal completed theta source, `c` is the constant part of `r`, and the real exponential polynomial `K` is the inverse Laplace transform of `r(-q²)-c`. Then:

1. `K` takes **both signs arbitrarily far out** on the positive half-line. Its signed Gaussian-rate density after cofinal prime deletion is

   ```text
   dν_r(λ) = 2π K(s)e^(5s/2)ds,
   λ=πe^(2s), s>0.                                             (2)
   ```

   In particular, the rate density has both signs on arbitrarily large rates.
2. For every real `ε≠0`, the perturbed source `f_ε=k+εu` fails the all-sieve complete-monotonicity condition: along **every** increasing cofinal exhaustion `S_j` of the primes, the normalized flux of `D_(S_j)f_ε` is not completely monotone for all sufficiently large `j`. A single derivative order and a single `t>1` witness failure eventually along that exhaustion.
3. If the reduced rational function has a pole associated with an off-line zero `α=γ+iβ`, `β≠0`, its causal kernel has positive exponential type. For a single quartet, after cancellation and with maximal pole multiplicity `m`,

   ```text
   limsup_(s→∞) (1/s) log |K(s)| = |β|,
   K(s) = s^(m−1)e^(|β|s)(A cos(γs)+B sin(γs)+o(1))
   ```

   for real `A,B` not both zero, with the evident sum of frequencies when several top poles share that real part. Thus the off-line displacement is the logarithmic growth exponent of the signed rate density after subtracting its universal Jacobian weight. Critical-line zero division also changes the rate density's sign, but has exponential type zero. Sign alone does not orient zeros.

## Proof

For finite `S`, the deletion formula gives on `x≥0`

```text
D_S k(x)=Σ_(n≥1, (n,∏S)=1) n^(−1/2)h(x+log n),
b_(D_S k)(t)=2πΣ_(n≥1, (n,∏S)=1)n²e^(−πn²t),              (3)
```

where `h` is the first Gaussian atom, `b` is the normalized tail flux, and `D_S=∏_(p∈S)(I-p^(−1/2)T_(log p))`. Positive shifts commute with (1), so (1) also represents `D_Su` at every `x≥0`. Direct change of variables in the flux shows

```text
b_(T_s g)(t)=e^(5s/2)b_g(e^(2s)t).                         (4)
```

For `t>1`, (1)--(4) therefore give

```text
b_(D_S f_ε)(t)
 = (1+εc)b_(D_S k)(t)
   + ε∫₀∞ K(s)e^(5s/2)b_(D_S k)(e^(2s)t)ds.                (5)
```

The finite-prime Gaussian series in (3) is bounded by the full theta series. At `e^(2s)t≥t>1`, that series and all its `t` derivatives have a Gaussian bound in `e^(2s)t`, while `K` grows at most exponentially in `s`. Dominated convergence applies to (5) and each derivative as `S_j` exhausts the primes. Only `n=1` survives, yielding

```text
B_ε(t)=2π(1+εc)e^(−πt)
       +2πε∫₀∞K(s)e^(5s/2)e^(−πe^(2s)t)ds,   t>1.       (6)
```

After multiplying the rate measure in (2) by `e^(−t₀λ)` for any `t₀>1`, it is finite. Hence (6), shifted by `t₀`, is the Laplace transform of one finite signed measure: an atom at `π` plus the continuous density (2). Uniqueness of finite Laplace measures implies that if `B_ε` were completely monotone on `(1,∞)`, this measure would be positive. The atom cannot mask a negative part of the continuous density. It remains to show that `K` takes both signs arbitrarily late.

Let `R(q)=r(-q²)-c`. It is a nonzero proper real rational function. Its poles are `q=±iα` and conjugates after cancellation, all **nonreal** because `Re α≠0`. Let `a` be the largest real part of its poles. Partial fractions give a real exponential-polynomial inverse kernel `K` and `R(q)=∫₀∞e^(−qs)K(s)ds` for real `q>a`. Suppose `K` were nonnegative past some `s₀`. The Laplace transform of its positive tail has finite convergence abscissa exactly `a`: it converges for `q>a`; if it converged at any `q<a`, it would define a holomorphic function on `Re q>q₀` agreeing with `R` minus an entire finite-interval integral, although that domain contains a pole with real part `a`. A nonnegative measure's Laplace transform must be singular at its finite real abscissa (the power-series/moment argument of Landau's theorem). But `R` and the finite-interval correction are analytic at the real point `a`, since no pole is real. Contradiction. Apply the same argument to `-K` to rule out eventual nonpositivity. Since `K` is continuous, each sign occurs on open intervals arbitrarily far out. This proves (1)--(2): `B_ε` is not completely monotone. Some derivative sign at some `t>1` witnesses this, and derivative convergence in (5) makes the same sign fail for every sufficiently large `S_j`.

For (3), the poles `q=±i(γ+iβ)` have real parts `±β` and imaginary parts `±γ`. The inverse Laplace formula has a nonzero top term of degree `m−1` at the rightmost pair; realness combines it into the stated oscillatory form. A finite nonzero trigonometric polynomial has a positive limsup of absolute value, proving the exponential-type identity. Under `λ=πe^(2s)`, this is power growth `(λ/π)^(|β|/2)` in the density after removing `e^(5s/2)` and the change-of-variable Jacobian.

## Meaning and limit

Cofinal deletion is a **rate microscope** for the causal zero-division kernel. Physical source and seed positivity can survive an off-line zero-division perturbation, while the deleted Gaussian-rate density has unavoidable alternating signs at arbitrarily high rates. The off-line coordinate is encoded in the *growth* of that signed density, not its sign: critical-line divisions oscillate too. This explains why finite-source positivity alone is too weak and why an all-sieve Bernstein law is substantially sharper.

This theorem does not exclude a zero of the literal `F`. The constructed `f_ε` is a different source, and no law makes its all-sieve flux positive merely because `k` has that property. The open producer is a source-derived constraint on the **actual** arithmetic rate/history object strong enough to prohibit positive exponential type for a divisor response without assuming its sign. Theorem (1)--(3) supplies the observable and exact exponent, not that constraint.

## Formalization gate

- [x] Paper proof of the cofinal signed-rate limit and eventual finite-depth derivative witness.
- [x] Paper proof of arbitrarily late sign changes using the real-abscissa singularity theorem.
- [x] Paper proof of the off-line exponential-type separation.
- [x] Formalize the causal rational inverse-Laplace kernel and the signed-rate limit
      (`QuasiPolynomialLaplaceCalculus`, `ThetaZeroDivisionCausalKernel`,
      `ThetaZeroDivisionRateTomography`), the derivative witness
      (`ThetaZeroDivisionRateDerivativeWitness`) and the exponential-type separation.
