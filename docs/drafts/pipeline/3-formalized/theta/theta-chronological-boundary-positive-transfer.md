# Positive transfer and singular deconvolution of theta Euler boundary currents

- **ID:** `theta-chronological-boundary-positive-transfer`
- **Stage:** 3-formalized
- **Type:** exact source intertwiner, coefficient-faithful deconvolution, and zero-free Mellin transfer
- **Routes:** STC, CSB, U, EDQ; theta Euler boundary
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`
- **Lean:** `GaloisForLFunctions.RHTower.ThetaChronologicalCutoffCurrent`, `ThetaChronologicalPositiveTransfer`, `ThetaChronologicalCausalJumps`, `ThetaChronologicalSingularDeconvolution`, `ThetaChronologicalPacketResolution`; certificate [theta-chronological-boundary-positive-transfer-formalized.md](theta-chronological-boundary-positive-transfer-formalized.md).
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

There is also a precise comparison with the corpus's [one-sided causal Möbius–theta tail](../../2-fully-proven/theta/causal-mobius-theta-boundary-criterion.md). Write `B(t)` for that tail, `ℒ_tB(w)=∫_1^∞B(t)t^(-w-1)dt`, `K(w)=∫_0^∞e^(wu)k(u)du`, and `E(w)` for its analytic correction. Its already proved half-line identity is

```text
ℒ_t B(w) = K(w)(1/ζ(w+1/2)-1)-E(w),     1/2<Re w<1.
```

Putting `z=w-1/2` and using (1) gives the **three-frame resonance identity**

```text
ℒ_t B(w) = -[K(w)/G(w-1/2)] ℒC(w-1/2)-K(w)-E(w).     (9)
```

Meromorphically continue (9) to a hypothetical right-half zeta zero, where `0<Re w<1/2`. Its causal numerator `K(w)` is nonzero there: `K(w)+K(-w)=ξ(w+1/2)=0`, while source monotonicity gives `Re(w K(-w))>0`. Thus the analytic correction in (9) cannot hide an off-line pole. The cutoff current, moving-cusp reflected current, and causal tail are three source frames of the **same reciprocal-zeta resonance**. The causal frame remains useful because its subpower source bound is an exact RH criterion, not because it contributes an independent pole.

## The causal frame retains arithmetic jump data

The pole correspondence does **not** identify the physical sources. Write `b(x)=B(exp x)`. The positive-ray bounds for the completed theta source `k` give an absolutely and uniformly convergent series for the terms with `n` above any fixed compact interval of `t>0`. Only the term indexed by an integer `m` changes membership in `n>t` as `t` crosses `m`. Thus `b` is right-continuous and has the exact jump

```text
b(log m+)-b(log m-) = -k(0) μ(m)/sqrt(m),       m≥1.       (10)
```

Since `k(0)>0`, the jump is nonzero precisely when `m` is squarefree, and its signed size recovers the literal coefficient:

```text
μ(m) = -sqrt(m) [b(log m+)-b(log m-)]/k(0).            (11)
```

For `0<t<1`, every positive integer belongs to the causal tail. The absolutely convergent full Möbius inversion of the completed theta source therefore gives the exterior initial value

```text
B(t) = h(-log t),                                     (12)
```

where `h` is the Gaussian seed. Thus the causal frame starts with an explicit seed and crosses integer times with a coefficient-faithful signed impulse train. In distributional log time, the singular part of `db/dx` is

```text
-k(0) ∑_(m≥1) μ(m)/sqrt(m) · δ_(log m).               (13)
```

This proves a **regular-transport obstruction**. The current `C` in (1) and all its fixed derivatives are bounded and continuous. For any fixed polynomial `P` and finite complex Borel measure `ν`, the function

```text
y ↦ ∫ P(∂)C(y+a) dν(a)
```

is continuous by dominated convergence. It cannot equal `b(y)`, because (10) is nonzero at `y=0` and at every squarefree crossing. In particular, the positive finite-measure transfer `T` of (4), even with fixed finite-order derivatives, cannot construct the causal source. Regular transfer does not expose the coefficient-faithful crossing record.

## The missing record is recoverable by a singular inverse

The regular obstruction does not mean that `C` has lost arithmetic information. Define the one-atom Gaussian current

```text
φ(y)=-2π exp(3y) exp(-π exp(2y)).
```

Equation (1) has the exact arithmetic convolution form

```text
C(y)=∑_(n≥1) μ(n)/n · φ(y+log n).                        (14)
```

Fix `σ>0`, put `C_σ(y)=exp(σy)C(y)` and `φ_σ(y)=exp(σy)φ(y)`, and form the finite signed measure on log time

```text
ν_σ=∑_(n≥1) μ(n)/n^(1+σ) · δ_(-log n).                  (15)
```

With `(ν*f)(y)=∫f(y-a)dν(a)`, equation (14) becomes

```text
C_σ=ν_σ*φ_σ  in L¹(ℝ).                                 (16)
```

The Mellin/Fourier transform of `φ_σ` is `-G(σ+it)`, nonzero for every real `t` because the gamma function has no zeros. Fourier uniqueness of finite measures therefore makes convolution by `φ_σ` **injective**: `C_σ` determines `ν_σ`, and its atom at `-log n` recovers `μ(n)=n^(1+σ)ν_σ({-log n})`. The causal tail is then recovered without a spectral zero premise by the exact singular readout

```text
B(t)=∫_(a<−log t) exp(-(σ+1/2)a)
           k(-a-log t) dν_σ(a),     t>0.              (17)
```

Each atom in (17) is exactly the corresponding term in the defining causal sum. Its absolute convergence follows from the positive-ray Gaussian bound for `k`.

This inverse is necessarily unbounded in ordinary source norms. For integers `n→∞`, the arithmetic log sites `-log n` and `-log(n+1)` approach each other. The measures `λ_n=δ_(-log n)-δ_(-log(n+1))` have total variation `2`, whereas

```text
‖λ_n*φ_σ‖_(L¹)
 = ‖φ_σ(·+log n)-φ_σ(·+log(n+1))‖_(L¹) → 0       (18)
```

by continuity of translations in `L¹`. Thus no bounded linear inverse exists even on finite measures supported at arithmetic log sites. The same ratio tends to zero after scaling the two atoms by the usual `n^(-1-σ)` coefficient weights. At the critical weight the actual measure also leaves finite total variation:

```text
‖ν_σ‖_(TV)=∑_(n≥1) μ(n)²/n^(1+σ)
          =ζ(1+σ)/ζ(2+2σ),
lim_(σ↓0) σ‖ν_σ‖_(TV)=1/ζ(2).                         (19)
```

The Euler product for squarefree integers proves (19) for `σ>0`, and the simple pole of zeta at `1` gives the limit. Equations (16)–(19) give a concrete source-faithful **singular transport** from the smooth boundary current to the discrete causal source. They change the interpretation of the hard step: arithmetic coefficients are present in `C`, but recovering them at critical weight amplifies arbitrarily close log sites and incurs divergent total variation. A successful orientation law must exploit the literal signed coefficients before this singular limit; regular positivity of the smoothed current cannot provide it.

This falsifies the conjecture that two Euler boundary limits provide independent arithmetic votes for zero exclusion. The positive survivor is the explicit singular coefficient recovery (16)–(17), alongside the regular positive transfer (4). Neither controls signed jump correlations or proves RH. Literature novelty of these cross-frame identities has not been established.

## Literal opposite-sign packets defeat compact regular observers

The instability in (18) used two artificial signs at adjacent integer sites. It persists for **actual** Möbius signs. Let `q` run through odd primes, put `m=2q`, and let `p=p(q)` be the least prime strictly greater than `m`. Then `μ(m)=+1` and `μ(p)=-1`. The prime number theorem implies `p/m→1`: for every fixed `ε>0`, the interval `(m,(1+ε)m)` contains a prime for all sufficiently large `m`. Write `δ_q=log(p/m)→0` and, for fixed `σ>0`, form the literal two-atom submeasure of (15)

```text
λ_(q,σ)=m^(-1-σ) δ_(-log m) - p^(-1-σ) δ_(-log p).     (20)
```

For every compact set `K⊂L¹(ℝ)` of regular convolution kernels,

```text
sup_(ψ∈K) ‖λ_(q,σ)*ψ‖₁ / ‖λ_(q,σ)‖_TV → 0.        (21)
```

To prove this, abbreviate the positive atom weights by `A=m^(-1-σ)` and `B=p^(-1-σ)`. Translation invariance and the triangle inequality give

```text
‖λ_(q,σ)*ψ‖₁/(A+B)
 ≤ |A-B|/(A+B) ‖ψ‖₁
   + B/(A+B) ‖ψ-ψ(·+δ_q)‖₁.                          (22)
```

The first ratio tends to zero. Translations are uniformly continuous on each compact subset of `L¹`: take a finite `ε`-net, use translation continuity at its centers, and bound the remaining terms by `2ε`. This proves (21) without an assumed smoothness bound. If instead the kernels have a uniform `W^{1,1}` bound, the sharper estimate is

```text
‖λ_(q,σ)*ψ‖₁/‖λ_(q,σ)‖_TV
 ≤ δ_q/2 · ((1+σ)‖ψ‖₁ + ‖ψ'‖₁).                      (23)
```

Indeed `|A-B|/(A+B)=tanh((1+σ)δ_q/2)≤(1+σ)δ_q/2`, `B/(A+B)≤1/2`, and the `L¹` translation bound is `δ_q‖ψ'‖₁`. Consequently, a family of kernels with `‖ψ_q‖₁≤M` that separates these packets by a fixed fraction `c>0` of their total variation must satisfy

```text
‖ψ_q'‖₁ ≥ 2c/δ_q - (1+σ)M.                         (24)
```

This is a source-faithful resolution cost, not an RH obstruction: close opposite signs can disappear under every *fixed regular* observation while their aggregate contribution to a larger window remains relevant. Thus coefficient-by-coefficient recovery through a compact family of smooth theta observations is the wrong topology for a critical cancellation proof. A successful source law must control collective signed packets directly, or use observers whose resolution escapes every compact regular family. The theorem does not exclude a global argument using the smoothed current without coefficient recovery.

Nor do these packets themselves supply a macroscopic matching: up to scale `X`, there are only `O(X/log X)` possible prime choices for `q`, versus `X/ζ(2)+o(X)` squarefree sites. Even under the half-power weight, their total weight is `O(sqrt(X)/log X)` versus order `sqrt(X)` for all squarefree sites. This proves that the local resolution obstruction is widespread across arbitrarily high scales but cannot by itself cancel the full source.

## Log

- 2026-10-04: every displayed result formalized unconditionally (five new modules, 249 declarations audited); moved to 3-formalized.
