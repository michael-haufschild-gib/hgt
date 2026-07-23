# CCM first-clock Landau completeness law

- **ID:** `ccm-first-clock-landau-completeness-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / universal CCM source theorem
- **Scientific status:** `[CONJECTURE] [PAPER PROOF IN PROGRESS] [NOVELTY AUDIT OPEN]`
- **Parents:**
  - `ccm-singular-loewner-central-slab-order-law.md`
  - `cofinal-two-edge-weil-completeness-landau-oscillation.md`
  - Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the
    truncated Weil quadratic form*, arXiv:2607.02828
- **Intended formal modules:**
  - `GaloisForLFunctions.RHTower.CCMFirstClockZeroDictionary`
  - `GaloisForLFunctions.RHTower.CCMFirstClockLandauCompleteness`
  - `GaloisForLFunctions.RHTower.CCMFirstClockVolterraReflection`

## Exact conjecture

For `L>0`, put

```text
a=L/2,                     xi_L=2*pi/L,
B_1(L)=ccmPublishedSourceSineCoefficient(a,xi_L).
```

Thus `xi_L` is the first positive physical CCM clock frequency. The proposed law is

```text
RH
  <-> B_1(L)>=0 for every sufficiently large L
  <-> B_1 is bounded below on one tail.                         (C1)
```

The stronger false-RH conclusion is

```text
not RH -> liminf_(L->infinity) B_1(L)=-infinity.                (C2)
```

This is a single actual published-source coordinate, not an arbitrary Weil test, a finite-rank
surrogate, or a determinant-convergence hypothesis.

## Exact zero dictionary

Polarizing the finite Guinand--Weil dictionary between the central clock and mode `n` gives,
with `t_n=2*pi*n/L`,

```text
b_n(L)
 = (t_n/pi) sum_(z in Z_Xi^*) (1-cos(L*z))/(z^2-t_n^2),        (D)
```

where `Z_Xi^*` is the multiplicity-exact centered Xi divisor. At `n=1`,

```text
B_1(L)
 = (2/L) sum_(z in Z_Xi^*)
     (1-cos(L*z))/(z^2-(2*pi/L)^2).                            (D1)
```

The apparent poles at `z=+-2*pi/L` are removable. The sum is absolutely convergent for each
`L`; the unconditional central height gap keeps every Xi divisor point away from the displayed
denominator once `2*pi/L<=4`.

## RH direction

Under RH every centered divisor point `z` is real. For `L>=pi/2`, the central height gap gives
`|z|>4>=2*pi/L`, hence

```text
(1-cos(L*z))/(z^2-(2*pi/L)^2)>=0.
```

Every summand in `(D1)` is nonnegative, proving the forward direction of `(C1)`.

## False-RH Landau mechanism

Write a right off-line centered zero as `z=gamma-i*delta`, with `delta>0`. Its conjugate-paired
contribution to `(D1)` contains

```text
Re ((1-cos(L*z))/(z^2-(2*pi/L)^2)).
```

The `cos(L*z)` term has size `exp(delta*L)` and oscillates with phase `gamma*L`; its coefficient
never vanishes because `|gamma|>4` while `2*pi/L<=4`. Let

```text
delta_* = sup {delta : gamma-i*delta is a centered Xi zero, delta>0}.
```

If RH is false, `0<delta_*<=1/2`. The Laplace transform in `L` has abscissa `delta_*`.
Expanding uniformly past any fixed positive aperture,

```text
1/(z^2-(2*pi/L)^2)
 = 1/z^2 + sum_(k>=1) (2*pi)^(2k)/(L^(2k)*z^(2k+2)).           (E)
```

The `k=0` term has genuine simple singularities at `s=+-i*z`. Every `k>=1` term is an iterated
Laplace primitive: at `s=+-i*z` it is strictly weaker than a simple pole, so it cannot cancel the
`k=0` residue. The full transform is holomorphic near the real point `s=delta_*`: centered Xi
zeros have ordinates bounded away from zero, and poles with unbounded ordinate leave every fixed
neighborhood.

If `B_1` were eventually bounded below, adding a constant on a tail would give a nonnegative
Laplace carrier with the same finite abscissa. Landau's boundary theorem would force a
singularity at the real point `delta_*`, contradicting the preceding holomorphy. This proves
`(C2)` provided the uniform continuation and noncancellation assertions in `(E)` are closed.

## First-clock Volterra law `[PROVED ON PAPER]`

The moving denominator is not an independent analytic object. Put `c=2*pi` and

```text
S_z(t)=(1-cos(t*z))/z^2.
```

Then for every `L>0` and every complex `z` (with removable values understood by
continuation),

```text
(1-cos(L*z))/(z^2-(c/L)^2)
 = S_z(L) + integral_0^L (c/L)*sin(c*t/L)*S_z(t) dt.           (V)
```

For `z!=0` and `z^2!=(c/L)^2`, product-to-sum and `c=2*pi` give

```text
integral_0^L sin(c*t/L)*cos(z*t) dt
 = (c/L)*(1-cos(L*z))/((c/L)^2-z^2).
```

The integral of `sin(c*t/L)` on `[0,L]` is zero. Therefore the integral term in `(V)`
is

```text
((c/L)^2/z^2)*(1-cos(L*z))/(z^2-(c/L)^2).
```

Adding `S_z(L)` proves `(V)` by one field identity. Both sides are entire in `z`, so the
excluded removable points follow by continuity.

Equivalently, with

```text
H(x)=(1-cos x)/(x^2-c^2),
```

one has the exact compact-kernel representation

```text
H(x)=-(1/(2*c))*integral_(-1)^1 sin(c*|u|)*exp(i*x*u) du.      (K)
```

Evenness reduces the integral to twice `[0,1]`, and product-to-sum gives
`2*c*(1-cos x)/(c^2-x^2)`. Thus the first clock is one fixed compact kernel under
dilation:

```text
B_1(L)=2*L*sum_z H(L*z).                                      (K1)
```

Formula `(V)` identifies it as a universal signed Volterra filter of the already formalized
multiplicity-exact Xi screw divisor. Formula `(K)` removes the apparent moving-denominator
problem from the Landau transform.

## Continuous Landau transform after the Volterra reduction

For `Re(s)>1/2`, termwise Laplace transformation of `(K1)` gives

```text
Lap(B_1)(s)
 =-(1/(2*pi))*sum_z integral_(-1)^1
     sin(2*pi*|u|)/(s-i*z*u)^2 du.                            (L)
```

The zero-counting bound and the double zero of `1-cos x` at `x=0` give a summable
`O(log(2+|z|)/|z|^2)` majorant for transformed terms. The only intrinsic branch points of
one continued summand are endpoints `s=+-i*z`; crossings of the open segment are removable
by local contour deformation. At `s=i*z`, integration by parts on `u in [0,1]` exhibits
nonzero logarithmic coefficient `(2*pi)/(i*z)^2`. Equal divisor copies and the
`z <-> -z` copy add this coefficient; they do not cancel.

Consequently every off-line zero with transverse coordinate `delta>0` gives a genuine branch
point with real part `delta`. Formula `(L)` is holomorphic on a neighborhood of real point
`delta_*`: centered Xi zeros have nonzero ordinate, endpoint branch points therefore miss the
positive real axis, and unbounded ordinates leave each bounded neighborhood. If Laplace
abscissa were less than `delta_*`, a zero with transverse coordinate above that abscissa would
put a genuine branch point inside the Laplace half-plane, impossible. Hence abscissa is exactly
`delta_*`. Landau's boundary theorem then gives `(C2)` from eventual lower boundedness.

Remaining paper audit: state local contour-deformation and transformed zero-sum majorant as
standalone lemmas with all quantifiers. No new number-theoretic estimate is required.

## Literal published-source connector `[PROVED ON PAPER]`

Put

```text
C_T(h)=rectangularTwoEdgeAutocorrelation(T/2,T/2,h)=(T-h)_+
W(T)=xiWeilPolarization(central rectangle at T)=2*S(T).
```

Both equalities are now unconditional Lean theorems.  For `xi*L=2*pi`, the exact source-side
Volterra identity is

```text
sin(xi*h)
 = -xi*C_L(h)-xi^2*integral_(t=h)^L sin(xi*t) C_t(h) dt       (S1)
```

on `0<=h<=L`.  Apply the complete sharp rectangular Guinand--Weil identity

```text
W(t)=-2*Prime(t)+Arch(t)                                     (S2)
```

first at `t=L` with weight `xi/2`, then over `0<t<L` with weight
`xi^2*sin(xi*t)/2`.  The three source components reduce as follows.

### Prime atoms

For every `k`, central autocorrelation gives `C_t(log k)=(t-log k)_+`.  Finite Fubini and `(S1)`
give

```text
-xi*Prime(L)-xi^2*integral_0^L sin(xi*t) Prime(t) dt
 = sum_(2<=k<=exp L) Lambda(k)/sqrt(k) * sin(xi*log k).        (S3)
```

This is exactly the positive atomic term in
`-criticalMellinStieltjesPairing(L/2,sin(xi*·))`.

### Even polar square

For the central even profile, the autocorrelation identity and hyperbolic addition give

```text
P(t)^2=2*integral_0^t C_t(h) cosh(h/2) dh.                    (S4)
```

Fubini and `(S1)` therefore give

```text
xi*P(L)^2+xi^2*integral_0^L sin(xi*t) P(t)^2 dt
 = -2*integral_0^L sin(xi*h) cosh(h/2) dh,                    (S5)
```

the continuous part of `-criticalMellinStieltjesPairing`.

### Gamma cancellation kernel

The exact central Gamma kernel is

```text
K_t(s)=
 [exp(-s)*C_t(0)-exp(-s/4)*C_t(s/2)]/(1-exp(-s)).
```

At lag zero, `(S1)` reads

```text
xi*C_L(0)+xi^2*integral_0^L sin(xi*t) C_t(0) dt=-sin(0)=0.    (S6)
```

Hence both the apparently singular `C_t(0)` part of `K_t` and the
`-(EulerGamma+log pi) C_t(0)` boundary charge cancel in the weighted family before either is
split into divergent pieces.  The remaining term is

```text
integral_0^infinity
  exp(-s/4)/(2*(1-exp(-s))) * sin(xi*s/2) ds
 = integral_0^L sin(xi*h) *
     exp(-h/2)/(1-exp(-2h)) dh,                               (S7)
```

after `s=2h`; support kills `h>L`.  Since

```text
exp(-h/2)/(1-exp(-2h))=ccmPublishedArchimedeanDensity(h),
```

this is exactly the published archimedean sine term.

Combining `(S2)`--`(S7)` gives the literal source dictionary

```text
pi*ccmPublishedSourceSineCoefficient(L/2,xi)
 = xi*S(L)+xi^2*integral_0^L sin(xi*t) S(t) dt.               (S8)
```

The divisor Volterra law `(V)` then gives, for `xi=2*pi/L`,

```text
ccmPublishedSourceSineCoefficient(L/2,2*pi/L)
 = (2/L)*ccmFirstClockXiRationalDivisor(L).                   (D1')
```

Thus formula `(D1)` is dependency-closed on paper without importing Groskin's finite dictionary
as an axiom.  Its proof uses only already formalized sharp rectangular source formula plus the
new universal autocorrelation/Volterra synthesis.

## Hostile audit

## Branch-free Volterra--Landau bypass `[PAPER PROOF: CORE MECHANISM CLOSED]`

The earlier rightmost-zero/branchpoint program is unnecessary.  Write

```text
S(L)=xiScrewDivisor(L),
Q(L)=ccmFirstClockXiRationalDivisor(L),
k(x)=2*pi*sin(2*pi*x).
```

The exact first-clock law, after `t=Lx`, is

```text
Q(L)=S(L)+integral_0^1 k(x) S(Lx) dx.                        (VL)
```

Both `S` and `Q` are real-valued unconditionally.  Suppose the literal published first-clock
source is eventually bounded below.  By `(D1')`, some real `C,T` then satisfy

```text
Q(L)+C*L >= 0  for L>=T.                                    (LB)
```

This nonnegative tail carrier is the input to continuous Landau.

### Universal positive-axis cone

For every centered Xi divisor copy `q`,

```text
4 < |Re z_q|,       |Im z_q| < 1/2.
```

Consequently neither dilation segment

```text
{+i*z_q*u: 0<=u<=1}, {-i*z_q*u: 0<=u<=1}
```

meets

```text
C = {s: Re s>0 and |Im s|<=8 Re s}.                         (CONE)
```

Indeed a putative intersection gives `|Im s|>4u` from the height gap, while the strip gives
`8 Re s<4u`; this contradicts `|Im s|<=8 Re s`.  Every closed disk centered at a positive real
`r` with radius `r/2` lies in `C`.  Thus these disks form a geometric analytic-continuation
chain reaching arbitrarily close to zero.

### First-clock continuation without branches

The compact first-clock representation gives the atom continuation

```text
A_q(s)=-(1/(2*pi))*integral_0^1 sin(2*pi*u) *
       ((s-i*z_q*u)^(-3)+(s+i*z_q*u)^(-3)) du.               (AC)
```

For `Re s>1/2`, Fubini and

```text
integral_0^infinity L^2 exp(-aL) dL = 2/a^3
```

identify `A_q` with the Laplace transform of the `q`-th first-clock atom.  The cone law removes
every denominator in `(AC)`.  Two integrations by parts in `u`, retaining the cancellation
`sin(2*pi*u)=0` at both endpoints, give a locally uniform `O_K(|z_q|^-2)` majorant on each
compact `K subset C`.  Reciprocal-square divisor summability therefore makes

```text
A(s)=sum_q A_q(s)
```

holomorphic throughout `C` and equal to the Laplace transform of `Q` on `Re s>1/2`.

### Landau propagation

Apply continuous Landau to the nonnegative tail measure with density `Q(L)+C*L`.  Its initial
Laplace transform and the continuation `A(s)+C/s^2` have the same germ.  The half-radius disks
inside `(CONE)` propagate exponential integrability by a factor `1/2` at each step.  Hence

```text
for every eps>0:
integral_T^infinity exp(-eps*L)*|Q(L)| dL < infinity.         (Q∞)
```

No maximal off-line ordinate, branch cut, contour deformation, or zero enumeration occurs.

### Universal dilation--Volterra reflection law

Let

```text
E_a(F)=integral_0^infinity exp(-aL)|F(L)| dL.
```

Choose `r<1` sufficiently close to one that

```text
kappa(r)=integral_r^1 |k(x)|/x dx < 1.                       (KAPPA)
```

For truncated `E_a`, `(VL)`, Tonelli, and `u=Lx` give

```text
E_a(S) <= E_a(Q)
          + integral_0^r |k(x)|/x E_(a/x)(S) dx
          + kappa(r) E_a(S).
```

Thus `E_(a/r)(S)<infinity` and `E_a(Q)<infinity` imply `E_a(S)<infinity`.  The unconditional
strip bound supplies one seed `E_beta(S)<infinity` for every `beta>1/2`; iteration at
`a=r^n beta`, combined with `(Q∞)`, yields

```text
for every eps>0: E_eps(S)<infinity.                          (S∞)
```

This reflection principle is universal: any dilation--Volterra filter whose kernel has tail
Mellin `L1` norm below one reflects a complete family of positive exponential moments.

### Pole contradiction

On `Re s>1/2`, the screw transform is

```text
integral_0^infinity exp(-sL)S(L)dL
 = sum_q 1/(s*(s^2+z_q^2))
 = i/s^2 * logDeriv XiC(i*s).                               (P)
```

By `(S∞)`, the left side is holomorphic on all `Re s>0`.  Therefore `(P)` extends the Xi
logarithmic derivative holomorphically to the upper half-plane.  The identity theorem extends
`XiC'=A*XiC` from `Im z>1/2` to `Im z>0`.  A nonzero analytic solution of this first-order
equation cannot vanish: comparing the lowest nonzero Taylor order at a hypothetical zero gives
order `m-1` on the left and at least `m` on the right.  Hence Xi has no upper-half-plane zero;
conjugation gives no lower-half-plane zero, which is RH.

The branch-free converse for pointwise first-clock source nonnegativity is now formalized.
Normal convergence of `(AC)`, tail-measure Landau iteration, and weighted-`L1` dilation
reflection are closed in Lean.  The obsolete rightmost-zero contour audit is no longer a
dependency.

1. **Moving denominator.** Resolved algebraically by `(V)` and analytically by fixed compact
   kernel `(K)`. Remaining work is formal local continuation of `(L)`, not an estimate on the
   moving denominator.
2. **Unattained transverse supremum.** No rightmost off-line zero may be assumed. The proof must
   use the real Landau boundary, not dominant-term asymptotics.
3. **No discrete aliasing shortcut.** Sampling `L` on a fixed arithmetic progression folds
   unbounded zero ordinates modulo `2*pi` and may create a positive-real accumulation. The proof
   stays in the continuous aperture.
4. **No hidden RH.** Termwise positivity is used only in the `RH ->` direction. The converse
   must use the genuine off-line divisor poles and unconditional low-height gap.
5. **Source connector required.** Formula `(D)` must be proved for the literal
   `ccmPublishedSourceSineCoefficient`, not only for an abstract zero-side polarization.

## Formal first-clock completeness theorem `[PROVED IN LEAN]`

Define the literal source assertion

```text
CCMFirstClockPublishedSourceNonnegative :=
  for every L>=pi/2,
    ccmPublishedSourceSineCoefficient(L/2,2*pi/L)>=0.
```

Lean now proves, without RH or an auxiliary analytic hypothesis,

```text
CCMFirstClockPublishedSourceNonnegative <-> RiemannHypothesis.       (FC)
```

The hard implication is not a wrapper around a prior RH criterion.  Its dependency chain is:

```text
literal source sign
 -> positive first-clock tail measure
 -> Landau half-radius continuation iterated to every positive moment of Q
 -> exact dilation Volterra reflection with ratio 15/16
 -> every positive exponential moment of the complete Xi screw
 -> the existing screw/logarithmic-derivative pole endpoint
 -> RH.
```

The Mellin tail of the fixed dilation kernel is bounded in Lean by

```text
integral_(15/16)^1 |2*pi*sin(2*pi*x)|/x dx <= 2/15 < 1,
```

so truncation absorption is strict and no integrability at the target exponent is assumed.
An unconditional reciprocal-square divisor envelope supplies the initial screw moment for every
abscissa above `1/2`; iteration reaches every positive abscissa.

This closes the source-to-RH direction.  It does **not** prove the source sign.  Equation `(FC)`
shows that the remaining arithmetic statement is RH itself in one literal CCM coordinate:
prove the explicit von-Mangoldt--Gamma first-clock functional nonnegative for every
`L>=pi/2`, or produce one negative value and disprove RH.

## Significance

If proved, `(C1)` upgrades C30 from a necessary sign under hypothetical CCM determinant
convergence to an exact source-only RH equivalence:

```text
first published CCM clock edge eventually ordered <-> RH.
```

Combined with `eventually_ccmPublishedSourceSineCoefficient_nonneg_of_XiC_convergence`, it says
that the surviving active-even CCM determinant route cannot converge in any false-RH world for
the explicit arithmetic reason already visible in its first moving clock edge.

## Gates

- [x] corpus collision audit
- [x] external 2025--2026 CCM / finite-dictionary audit
- [x] exact candidate formula derived
- [x] RH-side termwise sign proof
- [x] exact first-clock Volterra law `(V)`
- [x] fixed compact-kernel representation `(K)`
- [x] literal first-clock source dictionary `(D1')` dependency-closed on paper
- [x] literal first-clock source dictionary `(D1')` formalized unconditionally in Lean
- [x] rightmost-zero/contour route removed by branch-free positive-axis cone
- [x] universal dilation--Volterra reflection dependency-closed on paper
- [x] rational screw-pole dictionary formalized unconditionally in Lean
- [x] first-clock continuation normal convergence dependency-closed in Lean
- [x] tail-measure Landau iteration and weighted-`L1` reflection formalized
- [ ] false-RH cofinal unboundedness `(C2)` proved
- [x] pointwise first-clock completeness theorem `(FC)` formalized
- [x] direct Lean checks and axiom audit
- [ ] final targeted module build
- [ ] unconditional published-source sign, RH, disproof, or scoped CCM death theorem

## Log

- 2026-07-23 -- Created after C29--C30 audit. Rejected unconditional source positivity: one
  off-line quartet contributes an exponentially oscillating term. Identified first physical
  clock mode as the minimal source coordinate that may retain the full transverse divisor.
- 2026-07-23 -- Proved exact Volterra law `(V)` and compact-kernel law `(K)`. This removes
  moving denominator as separate frontier and reduces converse to continuous Landau continuation
  of one fixed sign-changing aperture kernel.
- 2026-07-23 -- Proved literal source connector `(S8)` on paper.  Key cancellation: synthesized
  sine has zero lag-zero value, so Gamma `C_t(0)` singular carrier and boundary charge cancel
  before splitting; Gamma remainder is exactly published archimedean density.  Added unconditional
  Lean theorems for fixed-kernel dilation, central triangle autocorrelation, physical
  sine/autocorrelation synthesis, height-gap noncollision, absolute first-clock divisor
  summability, complete Xi Volterra sum--integral exchange, and RH-side first-clock positivity in
  `CCMFirstClockVolterra.lean`.
- 2026-07-23 -- Closed the literal source connector in Lean.  The dependency chain now includes
  unconditional prime-atom transport, global Gamma cancellation and Fubini, the `s=2h` density
  transport, polar-square synthesis, the central Guinand--Weil real formula, and the exact theorem
  `ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor`.  Its direct corollary
  `ccmPublishedSourceSineCoefficient_firstClock_nonneg_of_rh` is the source-side forward implication.
  This prevents future sessions from re-deriving `(S1)`--`(S8)`.  Remaining open core is only the
  false-RH continuous Landau implication.
- 2026-07-23 -- Removed the rightmost-zero/branchpoint dependency.  The source-pure Xi height gap
  creates a universal positive-axis cone disjoint from every dilated divisor segment.  Inside it,
  the compact first-clock kernel has the branch-free cubic continuation `(AC)`.  Continuous
  Landau plus the new universal dilation--Volterra weighted-`L1` reflection forces all positive
  exponential moments of the Xi screw; its rational Laplace transform then forbids every
  upper-half-plane Xi zero.  Lean now proves both cone orientations, the half-radius disk chain,
  unconditional reality of the complete first-clock divisor, the one-atom screw Laplace law, and
  the exact multiplicity-complete logarithmic-derivative pole dictionary in
  `CCMFirstClockLandauCompleteness.lean`.  Remaining formal core is `(AC)` normal convergence,
  Landau iteration, and weighted-`L1` reflection.
- 2026-07-23 -- Closed the entire branch-free pointwise converse in Lean.  New modules prove
  normal convergence of the cubic first-clock continuation, exact positive-tail Landau descent
  through all dyadic abscissas, the dilation Volterra law, strict Mellin-tail contraction at
  ratio `15/16`, truncation absorption, exhaustion, and reflection from first-clock moments to
  screw moments.  `CCMFirstClockVolterraReflection.lean` proves
  `ccmFirstClockPublishedSourceNonnegative_iff_rh`.  Direct Lean check passes; capstone axiom
  audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  Remaining open core is no
  longer analytic transfer: it is exactly the literal published von-Mangoldt--Gamma source sign.
