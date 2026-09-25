# Positive transfer between two theta Euler boundary currents

- **ID:** `theta-chronological-boundary-positive-transfer`
- **Stage:** 2-fully-proven (paper)
- **Type:** exact source intertwiner and zero-free Mellin transfer
- **Routes:** STC, CSB, U, EDQ; theta Euler boundary
- **Status:** `[PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** [cutoff-commutator boundary current](theta-deletion-cutoff-commutator-collapse.md), [moving-cusp reflected current](theta-prime-deletion-moving-cusp-dual-source.md), ordinary beta integral and the absolutely convergent zeta series on `Re s>1`.

## A proposed independent source, tested

The two Euler-deletion limits look different. Integer-cutoff commutation gives the Möbius Gaussian current

```text
C(y) = -2π exp(3y) ∑_(d≥1) μ(d)d² exp(-πd² exp(2y)),
ℒC(z) = -G(z)/ζ(1+z),
G(z) = π^(-(z+1)/2) Γ((z+3)/2),                 Re z>0.       (1)
```

Reflection about the moving primorial cusp gives the signed-totient current `R(u)` with

```text
ℒR(w) = ξ(w+1/2)/ζ(w-1/2),                    Re w>3/2.     (2)
```

Both transforms are absolutely convergent in the stated common half-plane after putting `w=z+3/2`. Define `D=(1-∂_y)(2-∂_y)` and the **positive forward-dilation operator**

```text
(Tf)(y) = (1/(2π)) ∑_(n≥1) n^(-2)
          ∫_0^1 f(y+log n-(1/2)log t)/sqrt(1-t) dt.     (3)
```

The integral and sum converge absolutely for every bounded `f`; its kernel has total mass `ζ(2)/π`. The new exact physical-source identity is

```text
exp(3y/2) R(y) = -T(DC)(y)                 for every y∈ℝ.  (4)
```

In particular, the reflected signed-totient current is obtained from the cutoff Möbius Gaussian current by **two fixed derivatives and one positive forward-dilation average**. The two constructions do not supply independent reciprocal-zeta resonances.

## Proof of the identity

The Gaussian bound in (1), with any fixed number of logarithmic derivatives, shows `C`, `C'` and `C''` are bounded on the full line and decay rapidly as `y→+∞`. For `y≤0`, substitute `v=d exp(y)` and compare each absolutely summed derivative with `exp(3y)∑ d² P(d²exp(2y)) exp(-πd²exp(2y))`; the corresponding Gaussian Riemann sums are uniformly bounded. Hence `DC` is bounded, so (3) defines a continuous function. Its positive-shift kernel makes it rapidly decreasing at `+∞` and bounded at `-∞`. Therefore its bilateral Laplace transform is absolutely defined for `Re z>0`. Equation (2) supplies the same property for `exp(3y/2)R(y)`.

Integration by parts gives `ℒ(DC)(z)=(z+1)(z+2)ℒC(z)`. For `Re z>0`, Tonelli applied to the absolute values in (3) gives

```text
ℒ(Tf)(z) = A(z)ℒf(z),
A(z) = (1/(2π)) ζ(z+2) ∫_0^1 t^(z/2)/sqrt(1-t) dt
     = (1/(2sqrt(π))) ζ(z+2)
       Γ((z+2)/2)/Γ((z+3)/2).                           (5)
```

The first equality follows from the shift `a=log n-(1/2)log t`: its Mellin factor is `exp(-za)=n^(-z)t^(z/2)`. The second is Euler's beta integral. The completed-zeta formula gives

```text
ξ(z+2) = (1/2)(z+1)(z+2) π^(-(z+2)/2)
         Γ((z+2)/2) ζ(z+2)
       = A(z)(z+1)(z+2)G(z).                            (6)
```

Combining (1), (2), (5), and (6) yields

```text
ℒ(exp(3·/2)R)(z)
 = ξ(z+2)/ζ(1+z)
 = -A(z)(z+1)(z+2)ℒC(z)
 = ℒ(-TDC)(z).                                            (7)
```

Fix any real `σ>0`. Fourier uniqueness for the integrable functions obtained after multiplication by `exp(σy)` proves equality almost everywhere. Both sides are continuous, giving (4) pointwise.

## What this does and does not decide

The transfer multiplier

```text
H(z):=A(z)(z+1)(z+2)=ξ(z+2)/G(z)                       (8)
```

is holomorphic and zero-free throughout `Re z>-1`: `ζ(z+2)` is zero-free by its Euler product there, gamma has no zero, and `z+1`, `z+2` do not vanish in that open half-plane. Thus meromorphic continuation of (7) carries each hypothetical off-line pole of `1/ζ(1+z)` between the two currents with unchanged location and order. The positive kernel in (3) offers a source-level comparison, but `D` has no positivity-preserving sign, and the already proved cusp sign changes of both currents rule out a one-sign consequence. Equation (4) therefore identifies **one boundary resonance in two source frames**, rather than a new orientation law.

There is also a precise comparison with the corpus's [one-sided causal Möbius–theta tail](causal-mobius-theta-boundary-criterion.md). Write `B(t)` for that tail, `ℒ_tB(w)=∫_1^∞B(t)t^(-w-1)dt`, `K(w)=∫_0^∞e^(wu)k(u)du`, and `E(w)` for its analytic correction. Its already proved half-line identity is

```text
ℒ_t B(w) = K(w)(1/ζ(w+1/2)-1)-E(w),     1/2<Re w<1.
```

Putting `z=w-1/2` and using (1) gives the **three-frame resonance identity**

```text
ℒ_t B(w) = -[K(w)/G(w-1/2)] ℒC(w-1/2)-K(w)-E(w).     (9)
```

Meromorphically continue (9) to a hypothetical right-half zeta zero, where `0<Re w<1/2`. Its causal numerator `K(w)` is nonzero there: `K(w)+K(-w)=ξ(w+1/2)=0`, while source monotonicity gives `Re(w K(-w))>0`. Thus the analytic correction in (9) cannot hide an off-line pole. The cutoff current, moving-cusp reflected current, and causal tail are three source frames of the **same reciprocal-zeta resonance**. The causal frame remains useful because its subpower source bound is an exact RH criterion, not because it contributes an independent pole.

This falsifies the conjecture that two Euler boundary limits provide independent arithmetic votes for zero exclusion. The surviving problem is an unconditional signed law for their common reciprocal-zeta mode. Positive transfer (4), exact causal relation (9), and their zero-free numerators locate that law but do not supply it. Literature novelty of (4) has not been established.
