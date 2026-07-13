# Prime--polar moving-tent divisor tomography

- **ID:** `prime-polar-moving-tent-divisor-tomography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / unconditional CCM source--divisor incidence
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent theories:** Euler logarithmic derivative, parameter-holomorphic Riemann sums, and the
  finite-aperture polar boundary term
- **Statement:** One fixed moving logarithmic tent of the von Mangoldt function, corrected by an
  elementary polar sequence, has an ordinary Dirichlet series whose multiplicity-weighted pole
  divisor in `Re s>1` is exactly the shifted right off-critical zeta divisor.

> **Strengthened theorem.**  This result is now subsumed by
> `bounded-variation-prime-window-divisor-tomography.md`: smoothing is unnecessary, every compactly
> supported bounded-variation window obeys an exact Mellin-censorship law, one sharp interval gives
> the RH holomorphy criterion, and two incommensurable sharp widths recover the complete nontrivial
> divisor.  The present card remains the rectangular-autocorrelation specialization needed for the
> direct comparison with the original CCM observable.

## 1. The arithmetic sequence

Fix `L>0` and define the centered tent

```text
tau_L(x)=(L-|x-L|)_+.                                      (1)
```

It is continuous, supported on `[0,2L]`, and piecewise affine.  For `N>=1`, put

```text
T_L(N)
 =sum_(k>=1) Lambda(k)/sqrt(k)*tau_L(log(N/k)).            (2)
```

The sum is finite because its support condition is

```text
N*exp(-2L)<=k<=N.                                         (3)
```

Let

```text
c=exp(-L/2),
alpha=1-c,
beta=c^(-1)-1,                                            (4)
```

and define the elementary polar sequence

```text
P_L(N)
 =8*alpha^2*N^(1/2)+16*alpha*beta+8*beta^2*N^(-1/2).      (5)
```

Equivalently,

```text
P_L(N)
 =32*(sinh(log(N)/4)-sinh(log(N)/4-L/2))^2.               (6)
```

The prime--polar coefficient is

```text
p_L(N)=P_L(N)-2*T_L(N).                                   (7)
```

Every term in `(7)` is defined from the prime source and elementary real functions.  There is no
zero sum, zero enumeration, or limiting prime cutoff.

## 2. Tent Mellin factor

For `s in C`, define

```text
I_L(s)=integral_0^infinity tau_L(log u)u^(-s)du.           (8)
```

The integrand is supported on `[1,exp(2L)]`, so `I_L` is entire.  With `w=s-1` and `u=exp x`,

```text
I_L(s)=integral_0^(2L) tau_L(x)exp(-w*x)dx.                (9)
```

The tent is the additive convolution of two copies of `1_[0,L]`.  Fubini therefore gives

```text
I_L(s)
 =(integral_0^L exp(-w*x)dx)^2
 =((1-exp(-L*w))/w)^2,                                    (10)
```

with removable value `L^2` at `w=0`.  In the notation of the rectangular window,

```text
I_L(s)=A_L(s-1)^2.                                        (11)
```

Consequently

```text
I_L(3/2)=4*(1-exp(-L/2))^2=4*alpha^2,                     (12)
```

and `I_L(rho+1/2)=A_L(rho-1/2)^2`.

## 3. Uniform Riemann-sum lemma

For `s in C`, set

```text
g_s(u)=tau_L(log u)u^(-s)                                 (13)
```

on `u>0`, extended by zero outside `[1,exp(2L)]`.  Let `K` be a compact subset of `C`.  The family
`g_s`, `s in K`, is uniformly Lipschitz.  Indeed, away from the three breakpoints its derivative is

```text
g_s'(u)=u^(-s-1)*(epsilon(u)-s*tau_L(log u)),              (14)
```

where `epsilon(u)` is `1` on `(1,exp L)` and `-1` on `(exp L,exp(2L))`.  On the fixed compact
support, `(14)` is uniformly bounded for `s in K`.  Continuity and vanishing at the two support
endpoints extend the same Lipschitz bound across the breakpoints.

Partition the positive line into cells `((n-1)/k,n/k]`.  Comparison with the right endpoint in
each cell gives, uniformly for `s in K`,

```text
|1/k*sum_(n>=1)g_s(n/k)-integral_0^infinity g_s(u)du|
 <=C_(K,L)/k.                                             (15)
```

Only at most `k*exp(2L)+1` cells meet the support, and each cell contributes at most the common
Lipschitz constant times `1/k^2`; this proves `(15)`.

Define

```text
E_(k,L)(s)
 =sum_(N>=1)tau_L(log(N/k))*N^(-s)-k^(1-s)*I_L(s).         (16)
```

The first sum in `(16)` is finite.  Multiplying `(15)` by `|k^(1-s)|` yields

```text
|E_(k,L)(s)|<=C_(K,L)*k^(-Re s),       s in K.            (17)
```

Each `E_(k,L)` is entire.  If `K` is compactly contained in `Re s>1/2` and
`sigma_K=min_(s in K)Re s`, then

```text
sum_k Lambda(k)/sqrt(k)*sup_(s in K)|E_(k,L)(s)|
 <=C_(K,L)sum_k Lambda(k)k^(-sigma_K-1/2)<infinity.        (18)
```

The last series is the absolutely convergent Euler logarithmic derivative at
`sigma_K+1/2>1`.  Hence

```text
H_L(s)=sum_(k>=1)Lambda(k)/sqrt(k)*E_(k,L)(s)              (19)
```

is holomorphic on `Re s>1/2` by locally uniform convergence.

## 4. Meromorphic continuation of the moving-tent series

For `Re s>3/2`, the double series is absolutely convergent: the inner sum in `(2)` has
`O_L(N)` terms of total size `O_L(sqrt(N)log N)`.  Interchanging the sums and inserting `(16)`
gives

```text
sum_(N>=1)T_L(N)N^(-s)
 =sum_(k>=1)Lambda(k)/sqrt(k)
   *(k^(1-s)I_L(s)+E_(k,L)(s))

 =I_L(s)*sum_(k>=1)Lambda(k)k^(-(s-1/2))+H_L(s)

 =I_L(s)*(-zeta'(s-1/2)/zeta(s-1/2))+H_L(s).             (20)
```

Equation `(20)` supplies a meromorphic continuation to `Re s>1/2`.  Its only poles there are the
shifted zeros and pole of zeta; the error `H_L` is holomorphic.

The polar sequence has the exact Dirichlet series

```text
sum_(N>=1)P_L(N)N^(-s)
 =8*alpha^2*zeta(s-1/2)
  +16*alpha*beta*zeta(s)
  +8*beta^2*zeta(s+1/2).                                  (21)
```

Combining `(20)` and `(21)`, define

```text
Pcal_L(s)
 =8*alpha^2*zeta(s-1/2)
  +16*alpha*beta*zeta(s)
  +8*beta^2*zeta(s+1/2)
  -2*I_L(s)*(-zeta'(s-1/2)/zeta(s-1/2))
  -2*H_L(s).                                               (22)
```

On `Re s>3/2`, `(22)` is the ordinary Dirichlet series of `p_L`.  It is meromorphic on
`Re s>1`.

## 5. Exact polar cancellation

At `s=3/2`, the function `-zeta'/zeta(s-1/2)` has residue `1`, while
`zeta(s-1/2)` also has residue `1`.  By `(12)`, the two possible residues in `(22)` are

```text
+8*alpha^2,
-2*I_L(3/2)=-8*alpha^2.                                  (23)
```

They cancel.  Both singularities are simple, so `(22)` is holomorphic at `s=3/2`.  The poles of
`zeta(s)` and `zeta(s+1/2)` lie on or to the left of the boundary `Re s=1` and do not enter the
open half-plane.

Thus every pole of `Pcal_L` in `Re s>1` comes from a zeta zero `rho` with `Re rho>1/2`, at

```text
s=rho+1/2.                                                 (24)
```

If `rho` has analytic multiplicity `m(rho)`, then `-zeta'/zeta` has residue `-m(rho)`.  Therefore

```text
Res_(s=rho+1/2)Pcal_L(s)
 =2*m(rho)*I_L(rho+1/2)
 =2*m(rho)*A_L(rho-1/2)^2.                                (25)
```

Since `L>0` and `Re(rho-1/2)>0`, the rectangular half-plane nonvanishing law gives

```text
A_L(rho-1/2)!=0.                                          (26)
```

Hence no pole in `(24)` can cancel.

## Main theorem `[PROVED]`

For every `L>0`, the ordinary Dirichlet series

```text
sum_(N>=1)p_L(N)N^(-s)                                    (27)
```

has the canonical continuation `(22)` to `Re s>1`.  Its simple poles are exactly the shifted
right off-critical zeta zeros `(24)`.  The residue `(25)` recovers their exact analytic
multiplicity.  Functional-equation and Schwarz symmetry recover the full off-critical divisor.
In particular,

```text
RH iff Pcal_L is holomorphic on Re s>1.                    (28)
```

No positivity hypothesis or zero data occurs in the coefficient sequence.

## Fixed dyadic corollary `[PROVED]`

Take `L=(1/2)log 2`.  Then `(3)` becomes

```text
N/2<=k<=N.                                                 (29)
```

Therefore one fixed dyadic moving von Mangoldt tent, together with the elementary polar sequence
`(5)`, has a multiplicity-exact pole divisor equal to the complete off-critical zeta divisor.

## Holomorphic source--divisor quotient `[PROVED]`

Let `Mcal_L` be the cutoff-free continuation of the full rectangular Weil sequence constructed in
`fixed-window-logarithmic-weil-tomography`.  Its poles and residues in `Re s>1` are exactly
`(24)`--`(25)`.  Thus

```text
Pcal_L-Mcal_L is holomorphic on Re s>1.                    (30)
```

The prime--polar moving-tent series and the divisor-defined Weil series represent the same
multiplicity-weighted meromorphic class modulo holomorphic functions.  This is an unconditional
source--divisor incidence theorem; it does not identify their individual coefficients.

## Positive CCM law

The successful source carrier is forced to have the following form:

```text
cofinal moving prime window
  + exact elementary polar renormalization
  + locally uniform discretization control
  = multiplicity-exact divisor pole class.                 (31)
```

The polar term is not decorative: it cancels the zeta-pole charge at `s=3/2` exactly.  The
Riemann-sum error is holomorphic and therefore cannot alter the divisor.  Every new prime enters
through the moving interval `(3)`; the carrier pays cofinally for the arithmetic source without a
finite-prime limit theorem or a target-fed determinant.

## Parent-theory and significance attack

1. The Mellin transform of a tent and the identity `sum Lambda(n)n^(-z)=-zeta'(z)/zeta(z)` are
   classical.
2. Parameter-holomorphic Riemann-sum errors are standard analytic-number-theory technology.
3. The candidate new content is the exact ordinary integer Dirichlet compression of one fixed
   moving prime window, the polar cancellation at `s=3/2`, multiplicity-exact off-critical pole
   tomography, and the holomorphic source--divisor quotient `(30)`.
4. This conjunction must be checked against Riesz-mean explicit formulas, prime short-interval
   Mellin transforms, Beurling generalized-prime transforms, Voros superzeta functions, and the
   current Connes--Consani--Moscovici/Suzuki literature before promotion.
5. The theorem does not prove the coefficients are bounded below.  The RH-bearing source theorem
   remains a cofinal lower floor or an equivalent zero-free statement for `(27)`.

## Lean program

1. Formalize `tau_L`, its support, and the finite moving prime sum.
2. Prove the convolution/Mellin identity `(10)` using the existing
   `rectangularWindowAmplitude`.
3. Prove the uniform cellwise Riemann-sum estimate `(15)` for the concrete tent family.
4. Build the locally uniformly summable error series `(19)` on `Re s>1/2`.
5. Prove the initial double-series equality `(20)`.
6. Define `(22)`, prove the cancellation `(23)`, and compute `(25)` using actual zeta
   multiplicity.
7. Prove the exact pole-support and RH-holomorphy equivalences.
8. Prove the holomorphic quotient `(30)` against the existing full observable continuation.

No abstract meromorphic-continuation hypothesis, `Prop` interface, project axiom, `sorry`, or
target-defined source is permitted.

Formalization audit (needs-audit pass): this card is subsumed by
`bounded-variation-prime-window-divisor-tomography.md` (smoothing, the squared Mellin multiplier, and
the three-term polar sequence are unnecessary), and its continuation machinery `(20)`--`(22)` is the
same as that card's. The shared analytic building block — entireness of the tent/rectangle Mellin
factor `I_L(s)=A_L(s-1)^2` — is now available through
`RHTower.rectangularWindowAmplitude_differentiable` (axiom-clean). The remaining continuation, polar
cancellation `(23)`, and residue `(25)` are the open ANT chain tracked on the subsuming card; no
separate file is added here.

Update: the **convolution/Mellin identity `(10)` itself** (Lean program step 2), not merely
entireness, is now formalized axiom-clean in `formal/GaloisForLFunctions/RHTower/TentMellinFactor.lean`:

- `boxLaplace_eq` / `boxLaplace_zero` — the box factor `A_L(w) = ∫₀ᴸ e^{-wx}dx = (1-e^{-wL})/w`,
  with removable value `L` at `w = 0`;
- `tentLaplace_eq_boxLaplace_sq` — the exact identity `∫₀²ᴸ τ_L(x) e^{-wx}dx = A_L(w)²` for the tent
  window `τ_L` (`= x` on `[0,L]`, `2L-x` on `[L,2L]`), i.e. `I_L(s) = A_L(s-1)²`, proved by splitting
  at `L` and computing the two pieces;
- `integral_id_mul_cexp` — the primitive `∫ₐᵇ x e^{cx}dx = [(cx-1)e^{cx}/c²]ₐᵇ`, a reusable
  mathlib-missing lemma the split needs.

This closes step 2 of the Lean program (the tent Mellin factor `(10)`); the open chain remains the
uniform Riemann-sum estimate `(15)`, the summable error series `(19)`, and the polar
cancellation/residue `(23)`--`(25)` on the subsuming card.

## Gates

- [x] complete paper proof
- [x] exact source coefficient with finite support at each index
- [x] compact-uniform discretization bound
- [x] zeta-pole/polar cancellation
- [x] multiplicity-exact residue computation
- [x] dyadic one-window corollary
- [x] holomorphic source--divisor quotient
- [ ] unconditional Lean formalization
- [ ] primary-literature novelty audit
- [ ] independent proof audit
- [ ] standalone paper integration
