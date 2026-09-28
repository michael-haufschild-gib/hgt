# Alternating orientation of the literal theta half-line port

- **ID:** `theta-half-line-port-alternating-orientation`
- **Stage:** 3-formalized. Lean: `GaloisForLFunctions.RHTower.ThetaHalfLinePortOrientation`, `ThetaHalfLinePortCrossings`, `ThetaHalfLinePortGauge` (+ `CausalThetaHalfLaplace`, `SourceZeroHedenmalmMidpointTwoJet`, HTGeometry `RealZeroCrossingCount`), see `theta-half-line-port-alternating-orientation-formalized.md`
- **Type:** source-specific half-transform theorem, exact finite-type gauge rigidity, and additive-port nondegeneracy gate
- **Routes:** STC, CSB, U, BPC, K-RVM, MPLF
- **Status:** `[PROVED HERE ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`
- **Dependencies:** The positive, even, strictly decreasing positive-ray completed theta source and all its exponential moments; the closed Lean [two-thirds simple-critical-zero theorem](../../../../formal/GaloisForLFunctions/RHTower/Zeta23SimpleCriticalDensity.lean); the literal Hedenmalm [two-ended Volterra source](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmTwoEndedVolterraDefect.lean) and [source ODE](../../../../formal/GaloisForLFunctions/RHTower/HedenmalmThetaEigenODE.lean).

## Conjecture tested

The completed theta source `k` has two half-line transforms. A tempting source-side orientation law is that the forward port has strictly larger modulus than its reflected partner throughout the open right half-plane. At a zero of their sum, equal moduli are automatic, so such a strict law would exclude off-line zeros. The theorem below disproves **both fixed directions** of that proposed modulus order for the literal source, arbitrarily close to the critical boundary and at arbitrarily high ordinates. This does not rule out a sign-changing, genuinely arithmetic comparison.

## Half-transform and central nonvanishing

Use the centered real-variable convention

```text
H(w) = ∫₀^∞ exp(wu) k(u) du,
X(γ) = ∫ℝ exp(iγu) k(u) du = H(iγ)+H(-iγ) = XiC(γ).
```

The source has every exponential moment, so `H` is entire and can be differentiated under the integral on compact complex sets. Put `ν(u)=-k'(u)≥0`. Strict decrease of `k` on `(0,∞)` makes `ν` nonzero on a set of positive measure in every positive interval, and `∫₀^∞ν(u)du=k(0)`. Integration by parts gives, for `Re w≥0`,

```text
w H(-w) = ∫₀^∞ (1-exp(-wu)) ν(u) du,
Re(w H(-w))
  = ∫₀^∞ [1-exp(-Re(w)u) cos(Im(w)u)] ν(u) du > 0
                                                   when w≠0.  (1)
```

For `Re w>0`, the integrand is strictly positive wherever `ν` has positive mass. On the imaginary boundary `w=iγ`, `γ≠0`, it equals `(1-cos γu)ν(u)` and is strictly positive on a subinterval. At `w=0`, `H(0)>0` directly. Consequently `H(-w)` is zero-free on the **closed** right half-plane. If `H(w)+H(-w)=0` anywhere in the plane, then both `H(w)` and `H(-w)` are nonzero: use the preceding result for `Re w≥0`, and apply it to `-w` when `Re w<0`. In particular, the half-theta port does not vanish at any centered Xi zero, including critical-line zeros.

This sharpens the off-line noncancellation used by the [causal Möbius–theta criterion](../../2-fully-proven/theta/causal-mobius-theta-boundary-criterion.md): the boundary case `Re w=0` has the same strict source nonvanishing, not merely the open right half-plane. The broader no-spatial-node fact for actual zero modes is already proved in [`SelbergThetaSourcePhase.mode_ne_zero`](../../../../formal/GaloisForLFunctions/RHTower/SelbergThetaSourcePhase.lean); the new content below is the normal-derivative sign split and its finite-type-gauge consequence.

## Exact normal derivative and alternating sign

For `α≥0` and real `γ`, define the proposed one-port imbalance

```text
D(α,γ) = |H(α+iγ)|² - |H(-α-iγ)|².               (2)
```

Reality of `k` gives `D(0,γ)=0`. Let `γ>0` be a **simple critical zero**, so `X(γ)=0` and `X'(γ)≠0`. At that ordinate,

```text
H(iγ)=i b(γ),
b(γ)=∫₀^∞ k(u) sin(γu)du
    = (1/γ)∫₀^∞(1-cos(γu))ν(u)du > 0.          (3)
```

Differentiate (2) in `α` at zero. Since `H(-iγ)=conj(H(iγ))` and `H'(-iγ)=conj(H'(iγ))`,

```text
∂_α D(0,γ)
 = 4 Re(H'(iγ) conj(H(iγ)))
 = 4 b(γ) Im H'(iγ)
 = -2 b(γ) X'(γ).                                (4)
```

The last equality follows from `X'(γ)=iH'(iγ)-iH'(-iγ)=-2 Im H'(iγ)`. Thus the imbalance immediately to the right of the critical boundary has the **opposite** sign to the crossing direction of the literal real Xi function. This formula retains the source's positive half-ray sine response `b(γ)` rather than replacing it by a generic zero-count argument.

There are infinitely many simple critical zeros with `X'(γ)>0` and infinitely many with `X'(γ)<0`. In fact each direction has lower asymptotic density at least `5/18` relative to the total positive-height Xi zero count with multiplicity. Here is the counting proof. Let `N(T)` count all positive-height Xi zeros with multiplicity, `S(T)` count simple critical zeros, and `U(T),V(T)` count the simple critical up- and down-crossings, respectively, so `U+V=S`. Let `A(T)` count non-simple odd-multiplicity critical crossings. A real continuous function's up- and down-crossings alternate, ignoring its even-multiplicity touches; hence

```text
|U(T)-V(T)| ≤ A(T)+1 ≤ [N(T)-S(T)]/3 + 1.       (5)
```

Each non-simple odd crossing consumes multiplicity at least three in `N-S`; off-line and even-multiplicity zeros only strengthen the bound. Therefore

```text
min(U(T),V(T))
 ≥ [4S(T)-N(T)]/6 - 1/2.                       (6)
```

The corpus's unconditional theorem `two_thirds_simpleCritical_epsilon` gives `S(T)≥(2/3-o(1))N(T)`, and its Riemann–von Mangoldt census gives `N(T)→∞`. Dividing (6) by `N(T)` proves

```text
liminf U(T)/N(T) ≥ 5/18,
liminf V(T)/N(T) ≥ 5/18.                            (7)
```

Equations (3)–(7) imply that for arbitrarily large positive `γ` and arbitrarily small `α>0`, `D(α,γ)>0`, and likewise there are such points with `D(α,γ)<0`. The two sets of witnessing critical ordinates each have the quantitative density in (7). Thus neither `D>0` nor `D<0` throughout `α>0` can be a source theorem for the literal theta half-transform. In particular, the raw half-line port is **not** a fixed-direction Hermite–Biehler/passivity certificate for Xi.

The reason is structural. The half-line sine value `b(γ)` is **positive at every positive height**, while the real Xi function crosses in both directions. A conjugate port in a fixed positive canonical-system orientation would need its boundary sign to rotate with those crossings. The first logarithmic source moment does rotate:

```text
X'(γ) = -2 ∫₀^∞ u k(u) sin(γu)du.                (7a)
```

Thus the missing source geometry cannot be only the causal split of `k`; it must retain a height-dependent moment/phase channel, as the derivative-based Xi pair in the corpus does. Formula (7a) identifies the precise source moment whose sign the raw half-port loses. It does not bound that moment or establish the required positive orientation.

### Exact symmetrization fixes every finite-type scalar gauge

There is a stronger obstruction than failure of a particular modulus order: **the only zero-free entire scalar gauge of finite exponential type that preserves the exact Xi symmetrization is the identity**. Use right-half-plane reflection `F#(w)=conj(F(-conj(w)))`. Suppose `g` is entire and nowhere zero, `|g(w)|≤C exp(A|w|)` on the whole plane, and `E=gH` satisfies

```text
E(w)+E#(w)=H(w)+H(-w)                            (7b)
```

for all complex `w`. Then `g≡1`.

For completeness, a zero-free entire function of finite exponential type is `g(w)=exp(a w+b)` with constants `a,b∈ℂ`. One proof takes an entire logarithm `g=exp h`; `Re h(w)≤A|w|+O(1)`, and the Borel–Carathéodory estimate followed by Cauchy's estimate makes every derivative of `h` of order at least two vanish, so `h` is affine. At every positive simple critical zero `γ`, equation (7b) says `E(iγ)` is purely imaginary. By (3), `H(iγ)=i b(γ)` with `b(γ)>0`, hence `g(iγ)` is real. If `Re a≠0`, the real-valued phase condition is

```text
sin((Re a)γ + Im b)=0,                           (7c)
```

which holds at only `O(1+T)` positive heights through `T`. The corpus's two-thirds theorem and the Riemann–von Mangoldt census give `≫T log T` distinct simple critical heights, so `Re a=0`. Then (7c) at one such height forces `sin(Im b)=0`; consequently `g(iγ)` is real with **constant sign at every real height**.

In fact these restrictions force `g#=g` on the whole plane: with `a=iδ`, `δ∈ℝ`, and `Im b∈πℤ`, one has `conj(g(-conj w))=g(w)`. Since `H#(w)=H(-w)`, equation (7b) now reads

```text
g(w)[H(w)+H(-w)] = H(w)+H(-w).                     (7d)
```

The bracket is not identically zero because its value at `w=0` is `2∫₀^∞k(u)du>0`. Thus `g=1` on a neighborhood of zero and hence everywhere by the identity theorem. This proof needs no Hermite–Biehler assumption. In particular the alternating-sign obstruction (4) survives every such exact scalar gauge, because there is no nontrivial gauge to test. A prospective correction must leave this scalar class, introduce zeros/singularities, or change the port additively through an anti-reflected source moment. This is a complexity constraint, not an existence claim for such a correction.

### Additive ports need a nondegeneracy gate

Write `X(w)=H(w)+H(-w)`, so `X#=X`. Every entire port with exact symmetrization is of the form `E=H+Q` with `Q#=-Q`. This affine freedom is large enough to manufacture a circular receiver: set

```text
E₀(w) = (1/2+w)X(w),       E₀#(w) = (1/2-w)X(w).
|E₀(w)|²-|E₀#(w)|² = 2 Re(w) |X(w)|².             (7e)
```

The right-hand side is positive at every point of the open right half-plane **except precisely the off-axis Xi zeros one is trying to exclude**. Also `E₀` vanishes at every critical Xi zero, so the alternating boundary-sign law imposes no condition on this port. Equation (7e) proves that exact symmetrization and a positive-looking modulus identity do not by themselves supply an RH argument. A useful additive correction must prove its interior nonvanishing from the literal source independently of `X(w)≠0`, and must retain a nonzero boundary trace at simple critical zeros if it invokes the alternating-sign test.

The first source-moment correction `E₁=X/2+λ X'` (`λ>0`, derivative in `w`) does have the required alternating nonzero trace at every *simple* critical zero: `E₁(iγ)=-iλ X_γ'(γ)`, so its normal modulus derivative there is `2λ X_γ'(γ)²>0`. This passes the local sign test that the raw port fails. Yet at any off-axis Xi zero, `E₁#=-E₁`, hence the two moduli are equal; a global strict-order proof for `E₁` would itself be an RH proof. The corpus already studies this derivative port. The new separation here is between its genuinely repaired **local** orientation and its still-unproved **global** source inequality.

## Positive survivor: midpoint node exclusion and local two-jet test

Let `u_z(x)=hedenmalmCausalVolterra z x` in the corpus convention. Directly from its definition and the evenness of `k`,

```text
u_z(0) = -i H(-iz).                                    (8)
```

At any Xi zero `z`, equation (1) and `H(iz)+H(-iz)=XiC(z)=0` show `u_z(0)≠0`. The causal source ODE is already proved in Lean:

```text
u_z'(x) = -iz u_z(x) - i k(x).                          (9)
```

For a zero copy, Schwarz reflection supplies the conjugate spectral copy. Comparing the two actual causal flows **only at the midpoint and its first derivative** now gives the exact local classifier

```text
u_z(0)=u_conj(z)(0) and u_z'(0)=u_conj(z)'(0)
       iff z=conj(z).                                 (10)
```

Indeed equality of the values and (9) gives `(z-conj(z))u_z(0)=0`; the midpoint nonvanishing makes `z=conj(z)`. The converse is immediate. This reduces the corpus's all-`x` [source-orientation receiver](../../../../formal/GaloisForLFunctions/RHTower/SourceZeroHedenmalmOrientationRigidity.lean) to two local jets, while making explicit the nonzero source amplitude that prevents a false degenerate solution. The exact classifier (10) is now proved in [Lean](../../../../formal/GaloisForLFunctions/RHTower/SourceZeroHedenmalmMidpointTwoJet.lean) and its module-only OLean audit passed. It is still a **receiver**, not a source proof of either equality in (10).

## Boundary of the result

The failed fixed-sign conjecture was mathematically substantive: if true, it would forbid every zero with `Re w>0` because `H(w)+H(-w)=0` forces equal moduli. Its failure shows that any **nondegenerate** surviving one-port architecture must carry a height-dependent orientation, even at actual simple critical zeros. The positive survivor is the strict central half-transform nonvanishing, exact normal-derivative law (4), quantitative crossing split (7), **uniqueness** of the finite-type scalar gauge under exact symmetrization (7b)–(7d), the additive-port nondegeneracy gate (7e), and local two-jet classifier (10). None controls the collective Möbius covariance or excludes an off-line zero. External literature novelty of this combined result has not been established. All of (1)–(10) are formalized in Lean (see the certificate).

## Log
- 2026-09-28 — all results formalized unconditionally: closed half-plane positivity and nonvanishing (1), sine response `b(γ) > 0` (3), normal derivative law (4), crossing alternation and counts `U + V = S`, `|U − V| ≤ A + 1`, `S + 3A ≤ N` (5), the split (6), densities `≥ 5/18 − ε` (7) via the corpus two-thirds theorem, both-sign imbalance witnesses, first moment law (7a), exp-affine form of zero-free finite-type gauges and gauge rigidity (7b)–(7d), additive-port gate (7e) and the moment port `E₁`, midpoint amplitude (8) with the corpus ODE (9) and two-jet classifier (10); moved to 3-formalized.
