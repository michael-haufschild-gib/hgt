# Causal-germ cancellation and the translation ideal at the theta port

- **ID:** `theta-causal-germ-translation-ideal-phase-selection`
- **Stage:** 2-fully-proven (paper theorem; Lean formalization open)
- **Type:** THEOREM (paper), exact source-class obstruction and constructive local survivor
- **Routes:** STC, CSB, U, BPC, K-RVM, MPLF, RHist
- **Statement:** A smooth half-line correction that gives the completed theta port a strict right-half-plane modulus orientation must cancel every even Taylor jet of the source at the causal cut. Finite prime-translation corrections lie in the Xi ideal and cannot do this; a boundary-subtracted prime-moment port passes the local zero test but still lacks a global source inequality.
- **Dependencies:** [Alternating half-port orientation](theta-half-line-port-alternating-orientation.md), in particular its source nonvanishing and the unconditional two-sign simple-critical-zero density; the completed theta source's smooth even Schwartz profile and exponential moments; ordinary Fourier integration by parts and translation change of variables.

## Goal and change of representation

The raw causal half-transform fails both fixed directions of Hermite–Biehler order. Exact Xi symmetrization permits an additive anti-reflected channel. The question here is whether regular prime translations or finitely many full-source moments can supply that channel. The answer is controlled first by the **germ at the causal cut** `u=0`, before any cofinal Euler limit. This is a necessary condition, not a proof that a qualifying channel exists globally.

Use the centered convention

```text
H(w)=∫₀^∞e^(wu)k(u)du,
X(w)=H(w)+H(-w)=∫_ℝe^(wu)k(u)du=XiC(-iw),
F#(w)=conj(F(-conj(w))).
```

The literal `k` is real, even, smooth, positive at zero, and has the required exponential moments. Thus `X#=X` and `H#(w)=H(-w)`. Take a real `C∞` positive-ray correction `a` whose exponential moment exists in a fixed strip around `Re w=0`. Assume, for every `n`, that `(k+a)^(n)` is integrable, tends to zero at `+∞`, and permits integration by parts on `[0,∞)` (for example, absolute continuity on compact intervals suffices). These are explicit regularity hypotheses for the following source class, not assumptions on zeros. Define

```text
Q_a(w)=∫₀^∞a(u)sinh(wu)du,
E_a(w)=H(w)+Q_a(w),             E_a+E_a#=X.          (1)
```

Write `f=k+a` on `u≥0`. At a positive simple critical zero `γ` of `XiC`,

```text
E_a(iγ)=i c_a(γ),
c_a(γ)=∫₀^∞ f(u)sin(γu)du.                         (2)
```

Indeed the real part of `H(iγ)` is `X(iγ)/2=0`, and `Q_a(iγ)` is purely imaginary. Set `D_a(w)=|E_a(w)|²-|E_a#(w)|²`. Since `E_a#=X-E_a`,

```text
D_a(w)=2 Re(E_a(w) conj(X(w)))-|X(w)|²,
∂_α D_a(α+iγ)|_(α=0)=-2 c_a(γ) XiC'(γ).         (3)
```

The derivative formula uses `∂_α X(iγ)=-i XiC'(γ)`. A negative derivative contradicts `D_a(α+iγ)>0` for all sufficiently small `α>0`.

## The all-order causal-germ theorem

**[PROVED HERE ON PAPER]** Suppose `D_a(w)>0` throughout some fixed right collar `0<Re w<δ` at every height. Then

```text
(k+a)^(2m)(0)=0       for every m≥0.                (4)
```

The same conclusion holds if strict order is asserted only for all sufficiently high critical-zero neighborhoods. For proof, suppose `m` is the least index with `f^(2m)(0)≠0`. Repeated integration by parts in (2), with the Riemann–Lebesgue lemma applied to the last integrable derivative, gives

```text
c_a(γ)=(-1)^m f^(2m)(0) γ^(-2m-1)
       +o(γ^(-2m-1))             as γ→+∞.          (5)
```

Hence `c_a(γ)` has one fixed nonzero sign at every sufficiently high positive ordinate. The corpus's unconditional two-thirds simple-critical theorem and the real crossing count, as combined in the [half-port paper](theta-half-line-port-alternating-orientation.md#exact-normal-derivative-and-alternating-sign), give arbitrarily high simple critical zeros with `XiC'(γ)>0` and with `XiC'(γ)<0`. Choose the slope with the same sign as `c_a`; (3) is then negative, contradicting strict order. Thus no first nonzero even jet exists, proving (4). If `a` is real analytic near zero, (4) says the analytic germ of `k+a` is **odd**: the correction's even germ must equal `-k` exactly.

The germ condition has an exact Fourier-scale converse under the stated all-order regularity:

```text
all f^(2m)(0)=0   iff   c_a(γ)=O_N(γ^(-N))
                           for every N as γ→+∞.     (5a)
```

For the forward implication, integrate by parts `2m` times and bound the remaining sine transform by `‖f^(2m)‖₁`; choose `2m≥N`. For the reverse implication, (5) would contradict rapid decay at the first nonzero even jet. Thus strict port orientation forces removal of **every algebraic high-frequency trace of the causal cut**, leaving a rapidly decaying phase channel on the same scale as full-source spectral moments. This is the positive boundary-scale classification exposed by the obstruction.

This condition is sharp as a *local* orientation requirement. Take `a_*(u)=-k(u)+2u k(u)`. Then `k+a_*=2u k`, whose even jets all vanish, and (1) becomes

```text
E_(a_*)(w)=X(w)/2+X'(w).
```

At every simple critical zero, (3) is `2 XiC'(γ)²>0`. This is the familiar derivative-port receiver, now forced by cancellation of the causal even germ. Its global strict order is still an RH-level statement; (4) is necessary, not sufficient.

## Finite prime translations remain in the Xi ideal

For real shifts `h_j` and real coefficients `c_j`, form the odd part of a finite translation polynomial of the literal source,

```text
j(u)=1/2 ∑_j c_j [k(u+h_j)-k(u-h_j)].
```

It is real, smooth and odd. Set `a(u)=2j(u)` on `u>0`. A change of variables in the bilateral transform gives the exact source identity

```text
Q_a(w)=∫_ℝe^(wu)j(u)du
      =-X(w)∑_j c_j sinh(h_j w).                    (6)
```

Thus `Q_a` vanishes at **every** Xi zero, on or off the critical line. At each simple critical zero `E_a(iγ)=H(iγ)` and (3) is the unchanged alternating raw-port derivative. Equation (6) covers the odd part of every finite real Euler-deletion translation polynomial, irrespective of its coefficients or prime order. Independently, `a(0)=0`, so its boundary germ already fails the first requirement `a(0)=-k(0)` in (4).

If a cofinal sequence of such corrections has a finite pointwise spectral limit at any fixed Xi zero, that limit still vanishes there. A nonzero correction at that zero therefore requires a noncommuting spectral evaluation/singular renormalization, or an operation beyond full-line translations. This does **not** rule out moving-cusp limits, because local source convergence does not make Xi spectral evaluation continuous. It tells the singular construction exactly which continuity must fail.

The ordinary log-time clock does not evade (6) merely by taking a commutator. With `(Uf)(u)=u f(u)` and `(T_hf)(u)=f(u+h)`, direct calculation gives

```text
[U,T_h]f=U T_h f-T_h U f=-h T_h f.              (7)
```

Its odd source part is again a translation polynomial and remains Xi-divisible. The noncommuting operation with a chance to change the zero trace is the **unbalanced** clock multiplication `U` together with cancellation of the even causal germ, not the clock–translation commutator by itself.

## Constructive prime-moment survivor and unresolved global gate

For one prime `p`, put `L=log p`, `r=p^(-1/2)`, and use the even source

```text
g_p(u)=k(u)-r[k(u+L)+k(u-L)]/2,
Y_p(w)=∫_ℝe^(wu)g_p(u)du
      =[1-r cosh(Lw)]X(w).                           (8)
```

The correction `a_p(u)=-k(u)+2u g_p(u)` cancels every even germ jet because `g_p` is even. Its exact port is

```text
E_p(w)=X(w)/2+Y_p'(w).                             (9)
```

At a positive simple critical zero,

```text
E_p(iγ)=-i[1-r cos(Lγ)] XiC'(γ),
∂_α D_p(α+iγ)|_(α=0)
 =2[1-r cos(Lγ)] XiC'(γ)²>0,                        (10)
```

because `0<r<1`. This is an explicit **literal prime-deleted source moment** that repairs the raw port's local alternating-sign failure without choosing any zero or phase. It remains a receiver: at a hypothetical off-axis zero of `X`, (9) gives `E_p#=-E_p`, so strict interior modulus order fails there. Proving strict order globally from the source would itself resolve RH. The finite prime factor in (8) supplies a positive local coefficient, not that missing global inequality.

Two further conjecture tests delimit this survivor. First, `E_p` cannot have Hermite–Biehler order on the **whole** right half-plane. On positive real `w=α`, `X(α)>0` and `X'(α)>0`. For sufficiently large `α`, both `A_p(α)=1-r cosh(Lα)` and `A_p'(α)=-rL sinh(Lα)` are negative, hence `Y_p'(α)=A_p'X+A_pX'<0` and `D_p(α)=2X(α)Y_p'(α)<0`. At its center the exact necessary curvature condition is

```text
X''(0)/X(0) ≥ r L²/(1-r),                         (11)
```

because `Y_p''(0)=(1-r)X''(0)-rL²X(0)` and a negative value makes `D_p(α)<0` for all small `α>0`. The left side is the positive second log-time moment of the completed theta source. As `p→∞`, the right side tends to zero, so (11) holds for every sufficiently large prime without a numerical computation. This center check is strictly weaker than the missing all-height strip inequality.

The physical strip `0<Re w<1/2` fails more decisively for every sufficiently large prime. At its wall `α=1/2`, exact algebra gives

```text
A_p(1/2)=(1-p⁻¹)/2,
A_p'(1/2)=-(log p)(1-p⁻¹)/2,
Y_p'(1/2)=(1-p⁻¹)[X'(1/2)-(log p)X(1/2)]/2.     (11a)
```

Both `X(1/2)` and `X'(1/2)` are strictly positive and finite, by the positive even theta source. Thus `Y_p'(1/2)<0` once `log p>X'(1/2)/X(1/2)`. Continuity makes `D_p(α)=2X(α)Y_p'(α)<0` for some `α<1/2`. The clock applied **after** prime deletion therefore cannot produce global strip order cofinally, even though it passes the simple-zero local test (10) and eventually the center test (11).

Second, a single prime sent to infinity loses its new channel at every fixed point of the **right half of the physical strip**. On each compact subset of `0≤Re w<1/2`,

```text
E_p(w) → X(w)/2+X'(w)         locally uniformly,       (12)
```

since `r cosh(Lw)=O(p^(Re w-1/2))` and `rL sinh(Lw)=O(log p·p^(Re w-1/2))`. At the wall `Re w=1/2`, the first factor retains the oscillatory phase `p^(i Im w)/2` and the differentiated factor can grow like `log p`; convergence is nonuniform there. Thus a **fixed off-line zero** cannot be distinguished by a regular one-prime cofinal limit: its prime moment tends to the already known derivative receiver. Any arithmetic gain must use collective prime correlations, a singular boundary layer, or a source operation beyond these finite translations.

## Operator-order reinterpretation: remove the wall shear

The wall failure in (11a) comes entirely from differentiating the Euler multiplier. Let `G_p=I-r(T_L+T_(-L))/2` be symmetric prime deletion and `U f(u)=u f(u)` the log-time clock. The failed moment uses `U G_p k`, with transform `(A_p X)'=A_p X'+A_p'X`. Reversing the order to `G_p U k` gives `A_p X'`. Their difference is the Xi-divisible commutator term `A_p'X`: it vanishes at every Xi zero, so the two moments have the **same local zero-crossing orientation**, but it creates the negative `log p` wall shear away from zeros. This is an exact operator-order distinction, not a choice of phase from spectral data.

After the same forced causal-germ subtraction, the reversed-order port is

```text
E_p^cov(w)=X(w)/2+A_p(w)X'(w),
E_p^cov+(E_p^cov)#=X.                                (13)
```

The second identity uses `A_p#=A_p` and `(X')#=-X'`. At every simple critical zero its normal derivative is still the positive expression (10). Unlike (9), it also passes the **entire positive real radius** of the physical strip: `A_p(α)>0` for `0≤α≤1/2`, since

```text
r cosh(L/2)=(1+p⁻¹)/2<1,
D_p^cov(α)=2X(α)A_p(α)X'(α)>0       (0<α≤1/2).       (14)
```

The remaining complex gate is exact. At any `w` with `X(w)≠0`,

```text
D_p^cov(w)=2|X(w)|² Re[A_p(w) X'(w)/X(w)].          (15)
```

Thus a source proof of strict strip order would need both nonvanishing of `X` there and positivity of the real part in (15); the former is already RH. The Euler multiplier stays quantitatively in the right half-plane throughout the closed physical strip: `|1-A_p(α+iβ)|≤r cosh(Lα)≤(1+p⁻¹)/2<1`. Yet two right-half-plane factors can have a product with negative real part. A sufficient, currently unproved source condition is the **phase-aperture inequality**

```text
Re[X'/X](w) > r cosh(L Re w)|X'/X(w)|.              (16)
```

It is strictly stronger than the real-part positivity implied by a hypothetical RH product representation. At the strip wall its aperture is approximately `π/3`; toward the center it widens as `p` grows. This identifies the exact geometric burden added by deletion: a sector bound for the logarithmic theta transform, not another local crossing sign.

On the critical boundary, writing `x(γ)=XiC(γ)`, direct differentiation of (13) gives the exact normal derivative

```text
(1/2) ∂_α D_p^cov(α+iγ)|_(α=0)
 = [1-r cos(Lγ)] [x'(γ)²-x(γ)x''(γ)]
   -rL sin(Lγ)x(γ)x'(γ).                            (17)
```

The first bracket is the first Laguerre margin. The second is a signed prime phase coupling and is not controlled by the source positivity used above. No global phase order or RH conclusion follows. The [ordered prime–modular theta commutator](theta-prime-modular-commutator-crossing.md) is outside the translation-polynomial class of (6), but its present real one-crossing law has not established this complex phase order. External novelty of the combined causal-germ, translation-ideal, and operator-order results is not audited. Lean formalization remains open.
