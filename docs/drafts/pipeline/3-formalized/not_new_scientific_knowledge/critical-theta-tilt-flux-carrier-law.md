# Critical theta tilt flux is the exact Euler--archimedean Hilbert--Polya carrier

- **ID:** `critical-theta-tilt-flux-carrier-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / DIRECT HILBERT--POLYA SOURCE LAW / BRIDGE
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Statement:** The Xi Bezoutian quadratic form is the first variation at the critical point of a
  concrete one-sided theta-correlation norm under exponential tilt.  For finite-prime theta
  sources, that variation splits exactly into an archimedean seed response minus the complete
  von Mangoldt prime-power shift response.  Hence a successful direct Hilbert--Polya construction
  must carry a nonnegative cofinal tilt flux, or equivalently a source-defined contraction, on a
  state space which separately retains the growing arithmetic complement.

## 1. One-sided theta correlation

Let `k:R->(0,infinity)` be even and superexponentially decreasing with all derivatives.  Put

```text
X(w)=integral_R k(x)exp(w x)dx.                            (1)
```

For a finite exponential packet

```text
Phi(x)=sum_(j=1)^d c_j exp(w_j x),
Re w_j>0,                                                  (2)
```

and real `a` near zero, define

```text
(W_a Phi)(s)
 =integral_R exp(a(x+s))k(x+s)Phi(x)dx,
s>=0,                                                      (3)

J_Phi(a)=||W_a Phi||_(L2(R_+))^2.                         (4)
```

All integrals are absolutely convergent.  After the change of variable `y=x+s`, one has the exact
formula

```text
(W_a Phi)(s)
 =sum_j c_j X(w_j+a)exp(-w_j s).                           (5)
```

Thus `a` is not an evolution parameter for `k`; it is the transverse exponential weight of one
fixed completed source.

## 2. Critical first-variation theorem `[PROVED HERE]`

Let

```text
B_X(w,v)
 =(X'(w)conjugate(X(v))+X(w)conjugate(X'(v)))
   /(w+conjugate(v))                                      (6)
```

with its removable extension.  Then

```text
J_Phi'(0)
 =sum_(j,l) c_j conjugate(c_l) B_X(w_j,w_l).               (7)
```

### Proof

Equation `(5)` and `Re(w_j+conjugate(w_l))>0` give

```text
J_Phi(a)
 =sum_(j,l) c_j conjugate(c_l)
    X(w_j+a)conjugate(X(w_l+a))
    /(w_j+conjugate(w_l)).                                (8)
```

Differentiate the finite sum at `a=0`.  The product rule gives precisely `(7)`.

There is an equivalent source-space formula.  Put

```text
(W Phi)(s)=integral_R k(x+s)Phi(x)dx,
(M Phi)(s)=integral_R (x+s)k(x+s)Phi(x)dx.                (9)
```

Differentiation of `(3)` gives

```text
partial_a W_a Phi at a=0=M Phi,
J_Phi'(0)=2 Re <M Phi,W Phi>_(L2(R_+)).                   (10)
```

The double-integral kernel of `(10)` is exactly the positive-entry theta tail kernel in
`theta-tail-first-moment-bezoutian-law.md`:

```text
H_k(x,t)
 =integral_0^infinity
    (x+t+2s)k(x+s)k(t+s)ds.                              (11)
```

Pointwise nonnegativity of `H_k` does not imply nonnegativity of `(7)`; the latter is complete
correlation positivity.

## 3. Riemann specialization and exact RH boundary

Take the correctly normalized logarithmic Riemann theta source, so that

```text
X(w)=xi(1/2+w).                                           (12)
```

The critical Xi Bezoutian theorem gives

```text
RH
 <-> J_Phi'(0)>=0
     for every Phi in span{exp(w x):Re w>1/2}.            (13)
```

Thus RH is a positive transverse-flux statement:

> Every finite correlation packet of the completed theta source must gain, rather than lose,
> one-sided correlation energy when tilted infinitesimally toward the Euler half-plane.

This is stronger than pointwise positivity of `k` or `H_k`.  It is also cofinal: no fixed compact
node set or finite correlation order suffices.

## 4. Exact contraction coordinate

For `c>0`, set

```text
V_(+,c)=M+cW,
V_(-,c)=M-cW.                                             (14)
```

Then

```text
J_Phi'(0)
 =1/(2c)(||V_(+,c)Phi||_2^2-||V_(-,c)Phi||_2^2).          (15)
```

Consequently `(13)` is equivalent to the existence, on the relevant closures, of a contraction
`C_c` with

```text
C_c V_(+,c)Phi=V_(-,c)Phi.                               (16)
```

On a single exponential, equations `(5)` and `(9)` give

```text
W exp(w x)=X(w)exp(-w s),
M exp(w x)=X'(w)exp(-w s).                               (17)
```

Hence the spectral transfer function of `(16)` is

```text
Theta_c(w)
 =(X'(w)-cX(w))/(X'(w)+cX(w))
 =(L(w)-c)/(L(w)+c),
L=X'/X.                                                   (18)
```

This attack is decisive: declaring `(18)` contractive is exactly the Cayley form of the
Caratheodory/Herglotz criterion and therefore exactly RH.  A valid proof must construct `(16)` from
the Euler--theta incidence before using `(18)`; it may not assume the desired multiplier bound.

### Reflection--continuation realization `[PROVED HERE]`

Let

```text
(R Phi)(x)=Phi(-x).                                       (18a)
```

For a finite exponential packet, the functions `W Phi`, `M Phi`, and `V_(+,c)Phi` extend from
`s>=0` to entire exponential sums in `s`.  Evenness of `k` and the change of variable `x |-> -x`
give, for real `s`,

```text
(W Phi)(-s)=(W R Phi)(s),
(M Phi)(-s)=-(M R Phi)(s).                               (18b)
```

Consequently

```text
(V_(-,c)Phi)(s)=-(V_(+,c)R Phi)(-s),
s>=0.                                                     (18c)
```

Thus the contraction `(16)` is exactly a cross-boundary reflection--continuation operator.  It
takes the positive-half trace of `V_(+,c)Phi`, analytically continues the reflected source packet
to the negative half-line, reflects it back, and changes sign.  On each exponential mode this is
the multiplier `(18)`.

The positive carrier obligation can therefore be stated without Herglotz vocabulary:

> The completed Euler--theta incidence must make reflected analytic continuation across `s=0`
> bounded and contractive on the source-selected `V_(+,c)` range.

Ordinary analytic continuation is violently unbounded between half-line `L2` spaces.  Hence the
source-selected range and its growing prime module are load-bearing; a finite Gamma boundary or an
unpointed regular germ cannot supply this carrier.

## 5. Finite-prime resolvent splitting `[PROVED HERE]`

Let

```text
b(x)=exp(x/2)h(exp x),
(tau_ell f)(x)=f(x+ell),                                  (19)

R_N(sigma)
 =product_(p<=N)(I-p^(-sigma)tau_(log p))^(-1),
k_N=R_N(1/2)b.                                            (20)
```

For `b_a(x)=exp(a x)b(x)`, translation gives

```text
exp(a x)tau_(log n)b(x)
 =n^(-a)tau_(log n)b_a(x).                               (21)
```

Expanding the commuting Neumann series in `(20)` therefore proves the exact tilted-source
factorization

```text
exp(a x)k_N(x)=R_N(1/2+a)b_a(x).                          (22)
```

Define the finite von Mangoldt shift generator

```text
Q_N(sigma)
 =-partial_sigma R_N(sigma) R_N(sigma)^(-1)

 =sum_(q=p^r, p<=N)
    Lambda(q)q^(-sigma)tau_(log q).                       (23)
```

Differentiating `(22)` at `a=0` gives

```text
x k_N
 =R_N(1/2)(x b)-Q_N(1/2)k_N.                             (24)
```

For a source `f`, write

```text
(W_f Phi)(s)=integral_R f(x+s)Phi(x)dx.                   (25)
```

The finite-prime critical flux consequently has the exact decomposition

```text
J_(N,Phi)'(0)
 =2 Re <W_(R_N(1/2)(x b))Phi,W_(k_N)Phi>
  -2 Re <W_(Q_N(1/2)k_N)Phi,W_(k_N)Phi>.                 (26)
```

The first line is the one finite-degree archimedean response.  The second is the entire finite
von Mangoldt prime-power response on the faithful rank-`pi(N)` translation module.  Gamma phases,
polynomial jets, and Stokes corrections cannot replace the second term.

## 6. Positive carrier theorem for a successful implementation

Let

```text
V_N=span_Q{log p:p<=N},
A_N=V_N/(V_N intersection D),                             (27)
```

where `D` is the finite differential-state frequency carrier.  The arbitrary-scale Gamma theorem
gives the exhaustive archimedean dichotomy

```text
R_G=0  -> exponential--rational and DA,
R_G!=0 -> scaled alien charge and HT,                     (28)
```

with no third DA state from incommensurable scales.  In either branch, every bounded-complexity
cofinal implementation must carry

```text
dim_Q A_N>=pi(N)-dim_Q D.                                 (29)
```

Combining `(13)`, `(26)`, and `(29)` yields the positive direct Hilbert--Polya resource law:

> A successful construction must realize the prime response in `(26)` on the growing quotient
> `A_N`, transport that quotient through the pointed theta screen, and prove that the resulting
> critical flux is nonnegative on every cofinal exponential packet.  Equivalently, it must build
> the contraction `(16)` from the source incidence.

The pointed cusp screen already supplies the carrier and locally uniform divisor transfer.  The
remaining theorem is precisely the cofinal flux inequality, or a weaker quantitative version which
forces sub-log-square reflected energy on every approximant zero fibre.

## 6A. Corpus-grounded completion of the carrier specification

The existing RHTower corpus removes three apparent construction problems and sharpens the one that
remains.

First, `XiRelativeResolventFlux.lean` already proves, without a prime ordering or zero enumeration,
that the continued von Mangoldt--archimedean source trace is exactly the centered Xi relative
resolvent away from its natural poles:

```text
continuedPrimeArchSourceRelativeTrace
  = xiRelativeResolventTrace.                             (30)
```

Thus the missing theorem is not analytic continuation of the source trace.  The terminal Route A
audit proves that extracting trace-Hankel positivity from `(30)` by a compact-open germ, a finite
corona expression, or divisor reconstruction is either blind or RH-equivalent.

Second, `SeamKreinStructure.lean` proves that the reflected one-particle prime diagonal is unbounded.
No bounded conjugation internal to that prime space can implement `s |-> 1-s`.  It also proves that
the full reciprocity graph is Lagrangian for the signed doubled Green form.  Therefore the positive
operator promised by `(16)` must have the following shape:

> The successful Hilbert--Polya carrier is a larger doubled Krein seam whose nonzero content comes
> from an arithmetic domain, closure, or boundary defect.  It cannot be an internal bounded prime
> reflection or the quotient of the full reciprocity graph alone.

Third, `../../3-formalized/not_new_scientific_knowledge/relative-contraction-compression-exhaustion.md` proves that cofinal finite compressions do
determine a completed contraction after the bounded self-adjoint operator, or the correct closed
semibounded form, has been source-constructed.  The companion one-sided-bound theorem shows that
upper compression inequalities alone do not construct that completion.  Consequently a viable
finite-section implementation must carry a common closed source domain and a two-sided completion
law before applying compression exhaustion.

There is also a second exact positive endpoint already present in the corpus.  For the shifted
completed quotient

```text
Theta_omega(z)
 =Xi(1/2-omega-i z)/Xi(1/2+omega-i z),                   (31)
```

let `T_omega` and `L_omega` be its causal Toeplitz and anti-causal Hardy columns.  Boundary
unimodularity gives

```text
I-T_omega^*T_omega=L_omega^*L_omega.                     (32)
```

For a finite right-half divisor, the corpus proves the first-order source curvature

```text
C_E
 =lim_(omega->0+) omega^(-2)(I-T_omega^*T_omega)
 =D^*D>=0,                                                (33)
```

and identifies its boundary corner with the global Cauchy energy

```text
C_E(0,0)
 =integral_0^infinity |ell_1(t)|^2 dt,

ell_1(t)
 =2 sum_j m_j exp(-(a_j+i gamma_j)t).                    (34)
```

The exact Cauchy Gram expansion has strictly positive ordered-pair contributions and gives

```text
C_E(0,0)>=2 sum_j m_j^2/a_j.                             (35)
```

Every right-half zeta displacement satisfies `0<a_j<1/2`; hence one off-line zero forces
`C_E(0,0)>4`.  Therefore the entirely source-side estimate

```text
C_E(0,0)<=4                                               (36)
```

implies RH and requires no ordinate localization.  Construction and positivity of `(33)` do not
prove `(36)`: a self-dual quartet satisfies the generic FE, unimodularity, cocycle, and Toeplitz
contractivity laws while making the corner arbitrarily large.  The bound must use the exact
all-prime magnitudes and the archimedean cancellation at the compressed boundary.

The corpus identifies the exact arithmetic variable on which such a bound must act.  Put

```text
c_omega(n)
 =n^omega product_(p|n)(1-p^(-2omega)),

A_omega(X)=sum_(n<=X)c_omega(n),

E_omega(X)
 =A_omega(X)
  -X^(1+omega)/((1+omega)zeta(1+2omega)).                (37)
```

Suzuki's completed integrated tail has the source identity

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x])
    g_omega^(1)(t/x)dE_omega(t).                         (38)
```

The positive average term in `A_omega` contributes exactly zero because the archimedean kernel has
the matching vanishing moment.  Moreover

```text
E_omega(X)
 =sum_(d<=X) mu(d)d^(-omega)R_omega(X/d)
  -X^(1+omega)/(1+omega)
    sum_(d>X)mu(d)d^(-1-2omega),                         (39)

R_omega(Y)
 =sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).
```

Each term in `(39)` is only `O_omega(X^(1-omega))` under absolute values.  Therefore the positive
source theorem required by `(36)` is a coupled cancellation law for the transformed pair in `(39)`.
It must retain the floor discrepancy and compensating Mobius tail together through the
archimedean kernel.  This is the concrete all-prime/archimedean incidence absent from the
self-dual-quartet fake and from every finite Gamma carrier.

Equations `(16)` and `(36)` are therefore two compatible faces of the same positive carrier
obligation.  The first asks for a contractive reflected trace on the doubled source domain.  The
second asks for an absolute boundary regularity budget on its infinitesimal Hardy defect.  A direct
Hilbert--Polya proof may close either face, but it must construct the common source domain and retain
the growing prime complement `(27)`.

## 7. Attacks and exact boundary

1. **Not ordinary norm convexity.** Although `J_Phi(a)>=0`, the derivative of a positive norm square
   at one point can have either sign.  Equation `(13)` is not implied by positivity of `J_Phi`.
2. **Not pointwise theta positivity.** Positive even superexponential kernels can have off-real
   Fourier zeros.  Entrywise positivity of `(11)` does not make it a positive operator.
3. **Not a Gamma-state escape.** The dichotomy `(28)` leaves no additional finite DA carrier at
   incommensurable scales; the growing quotient `(27)` remains arithmetic.
4. **Not a scalar Euler-product modulus argument.** Prime-factor modulus changes have phase-dependent
   signs.  The full rank-`pi(N)` response in `(26)` must be retained before taking the positive cone.
5. **Not a flow proof.** The tilt is differentiated at one fixed source.  No semigroup trajectory or
   terminal state is used to define the object.
6. **Not AF charge conservation.** Every factor in `R_N` is an invertible zero-charge bulk unit.
   The pointed screen creates finite-stage divisor charge, so AF no-nucleation does not determine
   its horizontal polarization.  The screen must carry the reflection--continuation law `(18c)`.
7. **Lean gate.** Formalizing `(13)` with the right side assumed would only rename RH.  Lean work is
   justified when the source construction proves `(16)` or the zero-fibre energy estimate without
   an RH-equivalent positivity hypothesis.

## 8. Parent and novelty audit

The first-variation identity is finite-dimensional differentiation after the bilateral Laplace
transform.  The contraction coordinate is Douglas factorization and the Cayley transform.  The
finite-prime split is differentiation of a commuting Euler resolvent.  These are useful exact
coordinates, but each reduces to standard parent theory and the result is classified `[BRIDGE]`.

The closest current source-side formulation found in the July 2026 literature is the finite-core
Volterra/Schur program for the Riemann phase kernel.  It likewise leaves a quotient-to-original
positivity lift and the final RH bridge open.  Nothing in that work supplies the sign in `(13)`.

## Lean formalization — IN PROGRESS

Module `RHTower/ThetaTiltFluxCarrier`.  Sections 1--4 of this card are fully Lean-proved,
unconditionally; every capstone below audits to `propext, Classical.choice, Quot.sound`.

| Card | Lean |
|---|---|
| the source kernel `k` (even, positive, superexponentially decaying) | `RHTower.ThetaSource` |
| `(1)` `X(w) = ∫ k(x) e^{wx} dx` | `RHTower.bilateralLaplace`, `RHTower.ThetaSource.integrable_mul_exp` |
| `X` is entire with `X'(w) = ∫ x k(x) e^{wx} dx` | `RHTower.hasDerivAt_bilateralLaplace`, `RHTower.differentiable_bilateralLaplace`, `RHTower.deriv_bilateralLaplace` |
| `X` is Schwarz real and even; `X'` is odd | `RHTower.bilateralLaplace_conj`, `RHTower.bilateralLaplaceDeriv_conj`, `RHTower.bilateralLaplace_neg`, `RHTower.bilateralLaplaceDeriv_neg` |
| `(2)` the finite exponential packet | `RHTower.expPacketFn` |
| `(3)` `W_a Φ`, `(4)` `J_Φ(a)` | `RHTower.tiltWindow`, `RHTower.tiltCorrelation` |
| `(5)` `(W_a Φ)(s) = ∑_j c_j X(w_j + a) e^{-w_j s}` | `RHTower.tiltWindow_eq` |
| `(8)` the closed Cauchy form of `J_Φ(a)` | `RHTower.tiltCorrelationForm`, `RHTower.tiltCorrelation_eq` |
| `(6)` the source Bezoutian `B_X` | `RHTower.sourceBezoutian` |
| `(7)` `J_Φ'(0) = ∑_{j,l} c_j conj(c_l) B_X(w_j,w_l)` | `RHTower.hasDerivAt_tiltCorrelationForm`, `RHTower.hasDerivAt_tiltCorrelation` |
| `(9)`, `(17)` `W Φ`, `M Φ` and their exponential forms | `RHTower.sourceWindow`, `RHTower.sourceMoment`, `RHTower.tiltWindow_zero`, `RHTower.sourceMoment_eq_integral` |
| `(10)` `J_Φ'(0) = 2 Re ⟨MΦ, WΦ⟩` | `RHTower.momentWindowPairing`, `RHTower.sourceBezoutianSum_eq_pairing` |
| the half-line Cauchy Gram of finite exponential sums | `RHTower.expSum`, `RHTower.integral_expSum_mul_conj`, `RHTower.integral_norm_sq_eq_expSum` |
| `(14)` `V_{±,c} = M ± c W` | `RHTower.contractionPlus`, `RHTower.contractionMinus` |
| `(15)` `J_Φ'(0) = (2c)^{-1}(‖V_+Φ‖² − ‖V_-Φ‖²)` | `RHTower.contraction_energy_difference`, `RHTower.sourceBezoutianSum_eq_contraction_difference` |
| `(18)` the Cayley multiplier `Θ_c = (L−c)/(L+c)` | `RHTower.contraction_multiplier` |
| `(18a)`–`(18c)` the reflection--continuation law | `RHTower.sourceWindow_neg`, `RHTower.sourceMoment_neg`, `RHTower.contractionMinus_eq_reflected` |
| `(12)` `X = ξ(1/2 + ·)` gives the centred Xi Bezoutian | `RHTower.sourceBezoutian_eq_xiCentBezoutian` |
| `(13)` RH ⟺ nonnegative critical tilt flux | `RHTower.riemannHypothesis_iff_sourceBezoutian_nonneg`, `RHTower.riemannHypothesis_iff_tiltFlux_nonneg` |

Supporting: `RHTower.sourceBezoutian_conj_symm`, `RHTower.sourceBezoutianSum_conj`,
`RHTower.sourceBezoutianSum_im` (the flux is real), `RHTower.dotProduct_mulVec_bezoutian`.

### Remaining: section 5, equations `(19)`–`(26)`

The finite-prime Euler resolvent split.  Programme:

- **S1.**  A packet class `b` with `‖b y‖ ≤ C_M exp(-(M y))` for every `M` (equivalently: bounded,
  and superexponentially decaying at `+∞`), plus the one-sided lower-tail bound
  `‖b y‖ ≤ C exp(y/2)` needed to move the linear weight `y` across the shift sums.
- **S2.**  The `N`-smooth monoid `S_N` and the resolvent `R_N(σ) f (x) = ∑'_{n ∈ S_N} n^{-σ} f(x + log n)`,
  with summability from S1 (`n^{-σ}‖f(x+log n)‖ ≤ C_M e^{-Mx} n^{-σ-M}`).
- **S3.**  `(21)` `e^{ax} τ_{log n} b = n^{-a} τ_{log n} b_a`, a pointwise identity.
- **S4.**  `(22)` `e^{ax} k_N = R_N(1/2+a) b_a`, termwise from S3.
- **S5.**  `(23)` the von Mangoldt shift generator `Q_N(σ)` and `(24)`
  `x k_N = R_N(1/2)(y ↦ y b(y)) − Q_N(1/2) k_N`, which is `log n = ∑_{d ∣ n} Λ(d)` transported
  through the shift sums (Fubini on the smooth double sum).
- **S6.**  `(25)`–`(26)` the exact flux decomposition, by applying `(10)` to the source `k_N`.

`(28)`–`(29)` (section 6) are imports of the arbitrary-scale Gamma card, not theorems of this card.
The three open gates below are the Riemann hypothesis and are not claimed.

## Lean status (historical)

The repository already formalizes the decisive downstream implication

```text
locally uniform Xi approximants
 + uniform sub-log-square prime energy on their zero fibres
 -> RiemannHypothesis
```

in `RHTower.riemannHypothesis_of_XiC_locally_uniform_primeEnergy_approximants`.  The analytic
two-variable Bezoutian, Volterra correlation operators, and source contraction `(16)` are not in
the Lean tree.  No wrapper is added while their decisive sign remains open.

## Gates

- [x] theta tilt correlation defined
- [x] Xi Bezoutian identified with its critical first variation
- [x] RH equivalence proved from the existing complete Bezoutian detector
- [x] exact Volterra contraction coordinate computed
- [x] contraction identified with reflected cross-boundary analytic continuation
- [x] finite-prime Euler--archimedean flux split proved
- [x] arbitrary-scale Gamma complement law incorporated
- [x] circular Cayley-multiplier proof rejected
- [ ] construct the source-defined contraction
- [ ] prove the sub-log-square zero-fibre energy estimate
- [ ] invoke and verify the existing Lean RH transfer theorem

## 2026-08-23 Stage 2 -> 3 formalization audit

- [x] `ThetaTiltFluxCarrier.lean` formalizes equations `(1)`--`(18c)`: tilt correlation,
  critical first variation, Xi Bezoutian specialization, contraction coordinate, and exact
  reflection--continuation laws.
- [x] `ThetaCuspFinitePrimeFluxSplit.lean` formalizes equations `(19)`--`(24)`, including the
  smooth-monoid resolvent, the complete von Mangoldt generator, and exact pointwise
  archimedean-minus-prime-power source split.
- [x] `ThetaCuspFinitePrimeFluxWindow.lean` proves bilateral Laplace integrability of the actual
  finite-prime source, its first moment, its archimedean response, and its complete generator for
  every positive-half-plane frequency.  No convergence premise is exposed by the capstones.
- [x] `RHTower.finitePrimeThetaCuspPacketWindow_eq_halfLineExpSum` is equation `(25)` for the
  concrete integral window and a closed positive-frequency packet type.
- [x] All four concrete windows satisfy `MemLp ... 2 (volume.restrict (Ioi 0))`; the source-window
  norm has the exact finite Cauchy Gram formula.
- [x] `RHTower.finitePrimeThetaCuspPacketCriticalFlux_eq_arch_sub_generator` is equation `(26)` in
  the genuine half-line `L²` pairing, with the complete generator term retained.
- [x] Direct `lake env lean` and targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeFluxWindow` passed.  No umbrella build
  was run.
- [x] `#print axioms` for all 42 new theorems reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- [x] New leaf is wired into `GaloisForLFunctions.RHTower`.

No Lean proof obligation remains for the theorem claimed by this card.  The three unchecked RH
programme gates are explicitly unclaimed downstream research obligations and are not premises of
any formalized result above.
