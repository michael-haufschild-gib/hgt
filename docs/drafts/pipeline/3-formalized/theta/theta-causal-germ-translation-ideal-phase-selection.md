# Causal-germ cancellation and the translation ideal at the theta port

- **ID:** `theta-causal-germ-translation-ideal-phase-selection`
- **Stage:** 3-formalized (paper theorems formalized unconditionally in Lean; see `theta-causal-germ-translation-ideal-phase-selection-formalized.md`).
- **Status:** [PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]
- **Type:** THEOREM (paper), exact source-class obstruction and cofinal prime-port no-go
- **Routes:** STC, CSB, U, BPC, K-RVM, MPLF, RHist
- **Statement:** A smooth half-line correction that gives the completed theta port a strict right-half-plane modulus orientation must cancel every even Taylor jet of the source at the causal cut. Odd parts of finite full-line prime translations lie in the Xi ideal and cannot do this. At every sufficiently large prime, **every real clock/deletion commutator coefficient** fails strip-wide order; the failure persists for log-narrow positive packets and for **all positive two-scale packets with sublinear logarithmic spread**. The obstruction is an unconditional complex phase aperture forced by the proved Xi zero-radius bound.
- **Dependencies:** [Alternating half-port orientation](../../3-formalized/theta/theta-half-line-port-alternating-orientation.md), in particular its source nonvanishing and unconditional two-sign simple-critical-zero density; completed theta source's smooth even Schwartz profile and exponential moments; [multiplicity-exact Xi reciprocal-square resolvent](../../../../../formal/GaloisForLFunctions/RHTower/XiRelativeResolventTrace.lean), [source zero-radius theorem](../../../../../formal/GaloisForLFunctions/RHTower/XiReciprocalSquareSecondMomentRadius.lean), critical-strip/exterior zero-freeness, and existence of Xi zeros; ordinary Fourier integration by parts and translation change of variables.

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

Hence `c_a(γ)` has one fixed nonzero sign at every sufficiently high positive ordinate. The corpus's unconditional two-thirds simple-critical theorem and the real crossing count, as combined in the [half-port paper](../../3-formalized/theta/theta-half-line-port-alternating-orientation.md#exact-normal-derivative-and-alternating-sign), give arbitrarily high simple critical zeros with `XiC'(γ)>0` and with `XiC'(γ)<0`. Choose the slope with the same sign as `c_a`; (3) is then negative, contradicting strict order. Thus no first nonzero even jet exists, proving (4). If `a` is real analytic near zero, (4) says the analytic germ of `k+a` is **odd**: the correction's even germ must equal `-k` exactly.

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

## Odd full-line prime translations remain in the Xi ideal

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

The first bracket is the first Laguerre margin. The second is a signed prime phase coupling and is not controlled by the source positivity used above.

## The source-radius phase obstruction kills cofinal one-prime order

**[PROVED HERE ON PAPER]** The reversed-order port (13) has a point with `D_p^cov<0` in the open physical strip `0<Re w<1/2` for **every sufficiently large prime**. This is unconditional and uses no RH case split.

The [exact Xi reciprocal-square resolvent identity](../../../../../formal/GaloisForLFunctions/RHTower/XiRelativeResolventTrace.lean) already pairs the centered canonical product under functional-equation reflection. Let `ζ_q=xiSpectralPoint q=γ_q+iδ_q` run over Xi divisor copies, with multiplicity. For every `w` with `X(w)=xi(1/2+w)≠0`, its absolutely convergent form is

```text
z(w):=X'(w)/X(w)
    =w ∑_(q:XiZeroCopy) 1/(w²+ζ_q²).                 (18)
```

The [source second-moment radius theorem](../../../../../formal/GaloisForLFunctions/RHTower/XiReciprocalSquareSecondMomentRadius.lean) proves `γ_q²>599/4` for **every** Xi zero; critical-strip containment gives `|δ_q|<1/2`. Both are unconditional, and the gap uses no zero computation. At `w₀=1/2+2i`, write `ζ_q=γ+iδ` and

```text
C=γ²-δ²-15/4,       D=2+2γδ,
w₀/(w₀²+ζ_q²)=(1/2+2i)/(C+iD),
Re[w₀/(w₀²+ζ_q²)]=(C/2+2D)/(C²+D²),
Im[w₀/(w₀²+ζ_q²)]=(2C-D/2)/(C²+D²).               (19)
```

Here `C>γ²-4`, `2-|γ|<D<2+|γ|`, and `|γ|>12`. Consequently

```text
C/2+2D > (|γ|-2)²/2 >0,
8[Im numerator-(11/4)·Re numerator]
 =5C-48D >5γ²-48|γ|-116>0.                  (19a)
```

The last polynomial is positive for every `|γ|>12`. Thus **each** absolutely summable term in (18) lies in the same strict cone `Im>(11/4)Re>0`; no RH pairing or case split is needed. At least one Xi zero exists, so summing gives `z₀=z(w₀)` with `Im z₀>(11/4) Re z₀>0`. Consequently `Re z₀<|z₀|/2` (indeed `Re z₀/|z₀|<4/√137<1/2`). The wall point is nonzero unconditionally because `X(w₀)=xi(1+2i)≠0` by the proved zero-free line `Re s=1`.

Choose a phase `θ_*` so that `e^(iθ_*)z₀=|z₀|`. For each large prime put `L=log p`; choose a real `β_p` with `Lβ_p≡θ_* (mod 2π)` and `|β_p-2|≤π/L`. Then `β_p→2`, while the **exact** wall symbol is

```text
A_p(1/2+iβ_p)=1-[e^(iθ_*)+p⁻¹e^(-iθ_*)]/2.       (20)
```

By this unconditional nonvanishing and continuity,

```text
Re[A_p(1/2+iβ_p) z(1/2+iβ_p)]
  → Re z₀-|z₀|/2 <0.                             (21)
```

Equation (15) makes `D_p^cov<0` at these wall points for all sufficiently large primes, and continuity moves each negative point slightly into `0<Re w<1/2`. The exact positive survivor is a **phase-aperture classification**: for any cofinal wall multiplier of the form `1-c e^(iLβ)+o(1)` with a remainder locally uniform near `β=2` and a freely sweeping phase, strip-wide order forces `Re z(w₀)≥c|z(w₀)|`. At `w₀` the source radius makes that impossible for every `c≥4/√137`; the prime deletion coefficient is `c=1/2`.

The obstruction is stable under **every real clock-order gauge, with no size restriction**. For any `μ_p∈ℝ`, form the exact anti-reflected port

```text
E_(p,μ)(w)=X(w)/2+A_p(w)X'(w)
                 +μ_p A_p'(w)X(w)/L.               (22)
```

The cases `μ_p=0` and `μ_p=L` are respectively deletion-after-clock (13) and clock-after-deletion (9); all real interpolations and arbitrarily large real coefficients are included. At a simple Xi zero the added term vanishes, so local zero orientation remains (10). At the wall, for `θ=Lβ`,

```text
[E_(p,μ)-X/2]/X
 =z(w)-e^(iθ)[z(w)+μ_p]/2
       -p⁻¹e^(-iθ)[z(w)-μ_p]/2.                     (23)
```

For each `p`, choose `θ_p` with `e^(iθ_p)(z₀+μ_p)=|z₀+μ_p|` and choose `β_p→2` with `Lβ_p≡θ_p (mod 2π)` and `|β_p-2|≤π/L`. Put `m_p=|z₀+μ_p|` and `ε_p=|z(1/2+iβ_p)-z₀|`. The imaginary part of `z₀+μ_p` is always `Im z₀`, so `m_p≥Im z₀>2 Re z₀`. Moreover `ε_p→0` **uniformly in the chosen real coefficient**, because every `β_p` lies within `π/L` of 2. The reverse triangle inequality and `|μ_p|≤m_p+|z₀|` bound the real part of (23) by

```text
Re z₀ - (1-p⁻¹)m_p/2
       +3ε_p/2 + (|z(1/2+iβ_p)|+|z₀|)/(2p)
 ≤Re z₀-(1-p⁻¹)Im z₀/2+o(1)<0.                  (24)
```

It remains negative at a nearby point in the open physical strip. The bound is uniform in `μ_p`: **one prime threshold works for every real gauge coefficient at once**. The imaginary source phase is the part no real commutator coefficient can cancel.

## Log-narrow collective packets inherit the obstruction

**[PROVED HERE ON PAPER]** Replacing one prime by any positive, normalized packet of primes whose logarithmic width tends to zero still fails strip-wide order, uniformly over **all** real commutator gauges. More generally, let finite weights `v_(R,j)≥0` sum to one, let `L_(R,j)=log p_(R,j)`, and suppose a reference `L_R→∞` satisfies

```text
δ_R:=max_j |L_(R,j)-L_R|→0.                         (25)
```

The primes need not be distinct. Define the even real source symbol and its gauge port by

```text
A_R(w)=1-∑_j v_(R,j) p_(R,j)^(-1/2) cosh(L_(R,j)w),
E_(R,μ)(w)=X(w)/2+A_R(w)X'(w)
                         +μ_R A_R'(w)X(w)/L_R,      μ_R∈ℝ. (26)
```

For `w=1/2+iβ` with `|β-2|≤π/L_R`, the positive-frequency packet satisfies, uniformly over that interval,

```text
∑_j v_(R,j)e^(i(L_(R,j)-L_R)β)=1+o(1),
∑_j v_(R,j)(L_(R,j)/L_R)e^(i(L_(R,j)-L_R)β)=1+o(1). (27)
```

Indeed `|e^(it)-1|≤|t|`, `β` stays bounded, and (25) controls both phase error and scale ratio. The corresponding negative-frequency sums, each weighted by `p_(R,j)^(-1)`, are `o(1)` because `min_j p_(R,j)→∞`. Consequently the wall expression `[E_(R,μ)-X/2]/X` differs from

```text
z(1/2+iβ)-e^(iL_Rβ)[z(1/2+iβ)+μ_R]/2           (28)
```

by at most `η_R(1+|μ_R|)` with `η_R→0`, uniformly in the displayed `β` interval. Choose its phase so that `e^(iL_Rβ_R)(z₀+μ_R)=|z₀+μ_R|` and `|β_R-2|≤π/L_R`. Since `|μ_R|≤|z₀+μ_R|+|z₀|` and `|z₀+μ_R|≥Im z₀>2 Re z₀`, the error is small **relative to the same modulus that creates the negative margin**. Thus `Re[(E_(R,μ)-X/2)/X]<0` at `1/2+iβ_R` for every sufficiently large `R`, uniformly over `μ_R∈ℝ`; continuity moves the negative point into the open physical strip.

This rules out neighboring-prime aggregation as a repair of the scalar port. A surviving collective construction must break at least one exact feature of (25)–(26): positive normalized weights in a log-narrow packet, scalar multiplication of the same Xi clock channel, or a real commutator gauge. In particular, any attempt based on positive packets must retain nonvanishing **logarithmic scale spread** rather than relying on the number of nearby primes.

The same proof gives a quantitative **coherence threshold** for packets wider than (25). Retain (26), but require only `δ_R/L_R→0`, and set

```text
B_R(β)=∑_j v_(R,j)e^(i(L_(R,j)-L_R)β),
a₀=Re z₀>0,       b₀=Im z₀>(11/4)a₀.              (29)
```

The phase steering still works because `|B_R(β_R)-B_R(2)|≤πδ_R/L_R→0` whenever `|β_R-2|≤π/L_R`; the corresponding derivative-weighted packet differs from `B_R` by at most `δ_R/L_R`. Both errors are small **relative to** `|z₀+μ_R|` for arbitrary real `μ_R`, and the reverse-frequency packet is `o(1)` relative to it. If `|B_R(2)|≥c>2a₀/b₀` along any unbounded subsequence, choose the nearby phase so that `e^(iL_Rβ_R)B_R(2)(z₀+μ_R)` is positive real. For some `η_R→0` independent of `μ_R`, the wall defect divided by `2|X|²` is at most

```text
a₀-(c/2-η_R)|z₀+μ_R|+η_R
 ≤a₀-(c/2-η_R)b₀+η_R<0.                         (30)
```

Absorbing the packet error into `c/2` makes the negative margin uniform even when `|μ_R|→∞`. Therefore any cofinal packet sequence with strict strip order must obey

```text
limsup_(R→∞)|B_R(2)| ≤ 2a₀/b₀ < 8/11.             (31)
```

Choose `L_R` as midpoint of smallest and largest packet log scales, and write `Δ_R=max_j L_(R,j)-min_j L_(R,j)=2δ_R`. For `Δ_R<π`, every phase `2(L_(R,j)-L_R)` lies in `[-Δ_R,Δ_R]`; positivity of the weights gives `|B_R(2)|≥Re B_R(2)≥cos Δ_R`. If `Δ_R≥π`, the following bound is automatic. Thus (31) forces the sharper necessary lower spread

```text
liminf_(R→∞) Δ_R ≥ arccos(2a₀/b₀)
                      > arccos(8/11).              (32)
```

This is a source-derived, strictly positive lower bound on collective logarithmic dispersion, independent of packet size and of every real clock gauge. Equivalently, successful positive packets cannot have `max_j p_(R,j)/min_j p_(R,j)→1`. It is necessary, not sufficient: suppressing one low-frequency characteristic value does not prove RH or global phase order.

## Three-harmonic obstruction for every positive two-scale packet

The minimum-width way to suppress `|B_R(2)|` is a balanced pair of extreme scales. This follows directly from the geometry above: for `0≤Δ<π/2`, `|B_R(2)|≥cos Δ`, and equality holds exactly when all weight sits at the two endpoint logs with equal weights (apart from the degenerate `Δ=0` case). Thus increasing the number of primes cannot improve the single-height coherence bound at fixed log width. The balanced two-scale candidate is the sharp test of that bound, but cancellation at height `2` merely moves its phase to harmonics.

**[PROVED HERE ON PAPER]** Let a packet in (26) contain exactly two primes `p_(R,-),p_(R,+)`, with arbitrary normalized positive weights, midpoint log scale `L_R=(log p_(R,-)+log p_(R,+))/2→∞`, and log separation `Δ_R=log p_(R,+)-log p_(R,-)=o(L_R)`. For every sufficiently large `R` and **every** `μ_R∈ℝ`, its scalar port has a negative modulus defect somewhere in the open physical strip. There is no restriction on whether `Δ_R` tends to zero, a finite positive number, or infinity sublinearly.

The source-radius argument used at height `2` also supplies strict cones at heights `4` and `6`. For `h∈{2,4,6}`, put `w_h=1/2+ih`, `z_h=X'(w_h)/X(w_h)`, `t=|γ|>61/5`, and for each Xi zero copy set

```text
C_h=γ²-δ²+1/4-h² > t²-h²,
D_h=h+2γδ,                 h-t<D_h<h+t.
```

The real numerator of `w_h/(C_h+iD_h)` is `C_h/2+hD_h>(t-h)²/2>0`. Its imaginary numerator minus `k_h` times its real numerator is

```text
(h-k_h/2)C_h-(1/2+k_h h)D_h
 > (h-k_h/2)(t²-h²)-(1/2+k_h h)(h+t),             (33)
```

where `(k_2,k_4,k_6)=(11/4,15/4,4)`. The three right sides are respectively

```text
(5/8)t²-6t-29/2,
(17/8)t²-(31/2)t-96,
4t²-(49/2)t-291.                                    (34)
```

Each is strictly positive at `t=61/5` and strictly increasing thereafter. The zero-radius theorem gives `t²>599/4>(61/5)²`; summing the absolutely convergent reciprocal-square series and using existence of Xi zeros therefore yields

```text
0<Re z₂,    Im z₂>(11/4)Re z₂,
0<Re z₄,    Im z₄>(15/4)Re z₄,
0<Re z₆,    Im z₆>4 Re z₆.                            (35)
```

All three `X(w_h)=xi(1+ih)` are nonzero unconditionally on `Re s=1`. In particular the corresponding phase-aperture thresholds satisfy

```text
2 Re z₂/Im z₂ < 8/11,
2 Re z₄/Im z₄ < 8/15,
2 Re z₆/Im z₆ < 1/2.                                (36)
```

Write the two weights as `v,1-v`. At the three wall heights the packet characteristic function obeys

```text
B_R(2n)=v e^(-inΔ_R)+(1-v)e^(inΔ_R),
|B_R(2n)|²=cos²(nΔ_R)+(1-2v)²sin²(nΔ_R)
          ≥cos²(nΔ_R),                 n=1,2,3.    (37)
```

For every real `θ`, at least one of

```text
|cos θ|≥8/11,   |cos 2θ|≥8/15,   |cos 3θ|≥1/2       (38)
```

holds. Indeed, if `x=|cos θ|<8/11` and `|2x²-1|<8/15`, then `x²>7/30` and `x>12/25`. Also `cos 3θ` has modulus `x(3-4x²)`: if `x≤3/5`, this exceeds `(12/25)(39/25)>1/2`; if `x>3/5`, it exceeds `(3/5)(107/121)>1/2`. The identities include every value of the separation `Δ_R`, so the packet cannot hide its coherent phase at all three source-controlled heights.

Choose the height from (38) for each `R`. Equation (37) and the **strict** cone (36) put its characteristic amplitude above the negative-defect threshold, with a fixed margin drawn from the minimum of the three positive differences `c_h Im z_h/2-Re z_h`, where `(c₂,c₄,c₆)=(8/11,8/15,1/2)`. The phase-steering proof of (30) applies at this height: `Δ_R/L_R→0` makes both the characteristic-function change over the steering interval and the derivative-weight error `o(1)`; both errors stay small relative to `|z_h+μ_R|≥Im z_h` for **arbitrarily large real** `μ_R`. The reverse-frequency packet tends to zero because both primes tend to infinity. Hence the wall defect is negative uniformly in the gauge; continuity gives an interior negative point.

The result is a three-harmonic **rank obstruction**, rather than another single-height estimate: every positive packet supported on at most two comparable logarithmic prime scales recurs at one of three fixed spectral probes. An eligible scalar packet must use at least three independently placed log scales, a width comparable to its center, or an operation outside this positive scalar class. Those alternatives remain conjectural as RH producers.

A first three-scale repair also fails on the next harmonic. Ideal equal log offsets `-π/4,0,π/4` with equal weights give `B(2n)=[1+2cos(nπ/2)]/3`: the amplitudes at heights `2,4,6` are all `1/3`, so the coarse three-harmonic inequality (38) no longer forces a failure there. This does **not** establish positive defect at those heights; (36) gives upper, not lower, bounds on the exact failure thresholds. At height `8`, however, `B(8)=1`. The same termwise argument has `k₈=2`; the right side of (33) is `7t²-(33/2)t-580>0` for `t>61/5`. Hence `Im z₈>2 Re z₈>0`, while `|B(8)|=1`, so this symmetric three-scale packet again has a negative strip defect cofinally. The prime number theorem lets actual prime log scales approximate these three ideal offsets as their center tends to infinity; the strict negative margin survives that approximation. This failed repair shows why a finite list of low harmonics is only a test of a packet design, not a global phase solution.

There is an exact **finite-rank phase law** behind this recurrence. For any probability weights `v_j≥0` on at most `m` unit phases `u_j`, set `b_n=∑_j v_j u_j^n`, with `b₀=1` and `b_(-n)=conj b_n`. Then

```text
max_(1≤n≤m)|b_n| ≥ 1/m.                             (39)
```

Indeed the `(m+1)×(m+1)` Toeplitz matrix `T_(a,b)=b_(a-b)`, indexed by `0≤a,b≤m`, is the Gram matrix of the `m+1` monomials evaluated at at most `m` weighted phases. Its rank is at most `m`, so choose a nonzero vector `c` in its kernel and an index `a` with maximal `|c_a|`. The `a`-th row gives

```text
|c_a| ≤ ∑_(b≠a)|b_(a-b)| |c_b|
      ≤ m·max_(1≤n≤m)|b_n|·|c_a|,
```

proving (39). It is sharp: take equal weights on any `m` of the `(m+1)`-st roots of unity. Then `b_n=-u_*^n/m` for `1≤n≤m`, where `u_*` is the omitted root, while `|b_(m+1)|=1`. At packet wall heights `2,4,…,2m`, the phases are `u_j=e^(2i(L_j-L_R))`, so (39) is an exact rank/coherence constraint on any finite positive Euler packet, independent of prime sizes and real gauges. The three-scale test above is the `m=3` sharp configuration rotated to phases `-i,1,i`; its compulsory full recurrence at the fourth harmonic is precisely where the source cone defeats it. For larger `m`, (39) alone cannot force failure: the available Xi aperture at the selected harmonic must also be narrower than `1/m`. This states the missing joint source–arithmetic inequality without pretending that Toeplitz rank by itself proves RH.

The two operator orderings fail the same complex phase test despite identical favorable local zero orientation; clock-after-deletion also has the separate real wall shear (11a). A viable producer must change the wall phase geometry rather than merely differentiate, translate, reorder, or positively average **one or two comparable** Euler-deletion scales with a real commutator coefficient. Broad-scale packets of rank at least three, a modular commutator, and singular cofinal operations remain outside this no-go. The [ordered prime–modular theta commutator](../../3-formalized/theta/theta-prime-modular-commutator-crossing.md) is outside the translation-polynomial class of (6), but its present real one-crossing law has not established this complex phase order. External novelty of the combined causal-germ, translation-ideal, and phase-aperture results is not audited. Every numbered statement (1)–(39) is formalized in Lean; see the certificate.
