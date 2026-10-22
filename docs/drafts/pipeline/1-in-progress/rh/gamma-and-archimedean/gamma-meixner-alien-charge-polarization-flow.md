# Gamma--Meixner alien-charge polarization flow

- **ID:** `gamma-meixner-alien-charge-polarization-flow`
- **Stage:** 1-in-progress
- **Type:** `[GENERAL HT POLARIZATION LAW] [SOURCE-SPECIFIC EULER ENDPOINT]`
- **Scientific status:** `[PROVED ON PAPER] [LEAN CROSS LAW + ALGEBRA CORE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md`;
  - `complex-slope-gamma-alien-charge-classification.md`;
  - `../../../3-formalized/gamma-reflection-charge-conjugation-doubling.md`;
  - `../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`.

## 1. Problem

The finite Euler identity supplies nonreal Gamma slopes

```text
lambda_p = i log(p)/(2 pi),
```

but its two reciprocal-Gamma halves have zero total alien charge. Selecting one half after reading
a divisor would be target-fed and inadmissible. The missing question is whether an existing
positive source selects the two orientations before any Xi divisor is inserted.

The Gamma--Meixner convolution semigroup does. Its time-`theta` density is

```text
rho_theta(x)
 = c_theta Gamma(theta/4+i x/2) Gamma(theta/4-i x/2),    theta>0.       (1)
```

The two factors in `(1)` are distinguished by their upper/lower half-plane pole sets. One fixed
density is still phase-blind: `exp(h)A_+` and `exp(-h)A_-` preserve its product. The full
convolution-shape family contains strictly more information. Its derivative in `theta` recovers the
spectral logarithmic derivative of the pole-oriented quotient, up to exactly a linear exponential
gauge. Thus phase selection comes from source deformation, not from a divisor and not from an
unsupported uniqueness claim.

## 2. Shape--spectral phase recovery

This mechanism does not depend on Gamma. For any nonvanishing differentiable meromorphic carrier
`H`, define

```text
M_H(a,s)=H(a+lambda s)H(a-lambda s),
P_H(a,s)=H(a+lambda s)/H(a-lambda s).
```

Writing `LD` for the branch-free logarithmic derivative gives the exact cross system

```text
LD_s P_H(a,s)=lambda LD_a M_H(a,s),                      (2a)
LD_s M_H(a,s)=lambda LD_a P_H(a,s).                      (2b)
```

Both equations follow by the chain rule. Their general calculus content is the
Cauchy--Riemann relation between modulus and argument, so `(2a)--(2b)` alone are not claimed as
new mathematics. Their source consequence is load-bearing: a fixed symmetric intensity loses
phase, while its full shape jet recovers the chiral logarithmic derivative without choosing a
logarithm.

For a normalized density

```text
rho(a,s)=c(a)M_H(a,s),
```

the exact law is

```text
lambda LD_a rho(a,s)
 =LD_s P_H(a,s)+lambda LD c(a).                          (2c)
```

The last term is independent of `s`; after integration it is precisely an
`exp(alpha(a)s+beta(a))` gauge. Hence the probability normalization changes no alien charge.
This replaces the earlier appeal to minimal-order Hadamard uniqueness: the source family itself
recovers the phase modulo the exact DA zero-charge ambiguity that the HT classifier ignores.

At the actual time-one point `a=1/4`, `lambda=i/2`, the completed chiral quotient is

```text
Gamma_R(1/2+it)/Gamma_R(1/2-it)
 =zetaChi(1/2+it)^(-1)
 =gammaHardyPhase(t)^(-2).                               (2d)
```

The raw quotient `Gamma(1/4+it/2)/Gamma(1/4-it/2)` differs from `(2d)` only by
`pi^(it)`. Thus `(2a)` is exactly the Meixner-shape origin of the corpus's branch-free Hardy phase
velocity. After prime dilation and meromorphic continuation to `a=0`, the same law recovers the
time-zero Euler chiral quotient away from its pole lattice.

### 2.1 Finite plaquette and Euler normal-shift weld

The cross system has an exact finite form.  Away from the displayed denominators,

```text
M_H(a,s-h)/M_H(a,s+h)
 =P_H(a-lambda h,s)/P_H(a+lambda h,s).                  (2e)
```

This is a branch-free rectangular plaquette identity, not an infinitesimal approximation.
Equations `(2a)--(2b)` are its two tangent laws.

For an exponential ray of rate `r`, put

```text
lambda_r=i r/(2 pi),
E_r(s)=1-exp(-rs),
q_r(s)=rs exp(rs/2)/(4 pi^2).                           (2f)
```

Euler reflection and `sin(ix)=i sinh(x)` give the exact endpoint weld

```text
q_r(s) E_r(s) M_Gamma(0,s)=1.                           (2g)
```

Applying `(2e)` to `(2g)` at `s-h` and `s+h` yields

```text
E_r(s+h)/E_r(s-h)
 =q_r(s-h)/q_r(s+h)
   P_Gamma(-lambda_r h,s)/P_Gamma(lambda_r h,s).        (2h)
```

This is the source-side arithmetic coupling missing from phase recovery alone.  At
`r=log p`, the left side is one local factor of the actual normal source deformation

```text
C(h,s)=zeta(s-h)/zeta(s+h).
```

For every finite prime set, multiplying `(2h)` therefore gives an exact Gamma-chiral
factorization of the finite Suzuki normal connection.  Differentiating at `h=0` gives the local
von Mangoldt current

```text
log(p)/(p^s-1)
 =-1/s-log(p)/2
  -lambda_p LD_a P_Gamma(0,s).                          (2i)
```

Thus the same first transverse Gamma-shape jet which recovers the HT phase velocity also
recovers the genuine Euler logarithmic current, after its explicit DA counterterm.  The two
differential axes are not identified: `s` remains the Xi spectral coordinate, `h` is the
independent normal Suzuki shift, and `a=lambda_p h` is the exact local Gamma shape.

Equation `(2i)` exposes a strict cofinal constraint.  The counterterms and raw chiral derivatives
do not have separate all-prime limits.  Only their locally paired combination, equal to the Euler
current in `Re s>1`, is completion-stable.  Separating them before prime completion is rejected.

### 2.2 General HT consequence: transverse-derivation collapse

The publication-ready Gamma spectrum--clock theorem proves that, on a reflection-collapse slice,
the chiral phase slope is HT over the entire field generated by all fixed-slice intensities and
all their `s`-derivatives.  Equations `(2a)` and `(2i)` add the complementary positive statement:
that same phase slope lies in the first derivative of the positive shape family in the transverse
`a` direction, and the first chiral shape derivative contains the Euler current.

Hence infinite ordinary-differential state complexity can collapse after adjoining one
source-native transverse derivation.  This does not contradict the HT theorem and does not
silently change derivations: it identifies the missing normal coordinate.  Generic
parameterized differential algebra and the plaquette algebra are parent mathematics.  Candidate
novelty is the exact Gamma--Meixner/Hardy/Euler realization in which a positive convolution shape
supplies the transverse derivation and `(2h)--(2i)` recover the actual arithmetic normal source.

## 3. Exact complex-charge flow

Fix `lambda in C*`, a real parameter `a`, and a nonzero integer lattice label `k`. Define

```text
M_(a,lambda)(s)
 = Gamma(a+lambda s) Gamma(a-lambda s),                 (2)

P_(a,lambda)(s)
 = Gamma(a+lambda s) / Gamma(a-lambda s).               (3)
```

For the complex scaled Gamma charge at `t=k lambda`, direct evaluation gives

```text
R_M(k lambda)
 = lambda[exp(-2 pi i k a)-exp(2 pi i k a)]
 = -2 i lambda sin(2 pi k a),                           (4)

R_P(k lambda)
 = lambda[exp(-2 pi i k a)+exp(2 pi i k a)]
 =  2 lambda cos(2 pi k a).                             (5)
```

For real `a`, equations `(4)--(5)` give the conserved polarization norm

```text
|R_M(k lambda)|^2+|R_P(k lambda)|^2=4|lambda|^2.         (6)
```

The coordinate-free charge divides by the unavoidable affine scale:

```text
Rhat_M=R_M/(2 lambda)=-i sin(2 pi k a),
Rhat_P=R_P/(2 lambda)=   cos(2 pi k a),                  (6a)

|Rhat_M|^2+|Rhat_P|^2=1.                                (6b)
```

Consequently every finite source amplitude packet `w_j` has an exact isometric split

```text
sum_j |w_j Rhat_M,j|^2+|w_j Rhat_P,j|^2
 =sum_j |w_j|^2.                                        (6c)
```

This normalization is load-bearing for the all-prime problem. Raw alien charge has size
`|lambda_p|` and would insert a spurious extra `(log p)^2` into the source norm. The normalized
charge is the unit orientation label carried by the corpus's source half-form; the source
amplitude, not the affine coordinate choice, supplies the Hilbert weight.

At Gamma--Meixner time `theta`, put `a=theta/4`. Then

```text
R_M(k lambda)=-2 i lambda sin(pi k theta/2),
R_P(k lambda)= 2 lambda cos(pi k theta/2).               (7)
```

Thus convolution time rotates a fixed alien-charge magnitude between the symmetric density and
the chiral spectral factor. This is an exact charge law; no asymptotic Gamma expansion or
numerical experiment enters it.

## 4. Singular Euler endpoint

At `theta=0`, equivalently `a=0`,

```text
M_(0,lambda)(s)=Gamma(lambda s)Gamma(-lambda s)
                       =-pi/[lambda s sin(pi lambda s)], (8)
R_M=0,                                                   (9)

P_(0,lambda)(s)=Gamma(lambda s)/Gamma(-lambda s),
R_P(k lambda)=2 lambda !=0.                              (10)
```

In normalized form the endpoint is exactly `(Rhat_M,Rhat_P)=(0,1)`: the complete finite source
norm is transferred into the chiral sector.

Equation `(8)` makes the symmetric endpoint differentially algebraic. Equation `(10)` and the
complex-slope classifier make its pole-oriented phase hypertranscendental. For every
`0<theta<2`, the first symmetric charge in `(7)` is nonzero, so the interior density is
hypertranscendental; hypertranscendence collapses only at the singular convolution endpoint while
the chiral charge survives.

For a prime `p`, scale the Meixner spectral coordinate by

```text
x=(log p/pi)s,
lambda=lambda_p=i log(p)/(2 pi).
```

Then the two pole-oriented factors in `(1)` become

```text
Gamma(theta/4+lambda_p s),
Gamma(theta/4-lambda_p s),                              (11)
```

and converge meromorphically away from poles to `Gamma(lambda_p s)` and
`Gamma(-lambda_p s)`. Recurrence gives

```text
Gamma(1-lambda_p s)=(-lambda_p s)Gamma(-lambda_p s).     (12)
```

Combining `(8)`, `(12)`, and Euler reflection recovers `1-p^(-s)` from the inverse symmetric
endpoint by a nonzero rational/exponential gauge. The chiral quotient is therefore selected
before any Xi divisor is read: approach the positive Gamma--Meixner semigroup endpoint and retain
the upper/lower pole orientation.

## 5. Hypertranscendence consequence

The source transition is

```text
theta>0:
  symmetric Meixner density HT, chiral factor HT;

theta=0:
  symmetric Euler intensity DA, chiral Euler phase HT.   (13)
```

This explains the finite Euler charge cancellation without discarding the positive survivor.
Charge is not destroyed; at the singular endpoint it is completely transferred to the
pole-oriented phase.

The result is stronger than the generic statement that modulus loses phase. The source supplies:

1. an explicit positive convolution semigroup;
2. a canonical meromorphic pole polarization;
3. an exact complex alien-charge transport law;
4. the local Euler factor as its singular endpoint.

## 6. Hostile controls

1. **Characteristic-only control.** The real characteristic
   `cosh(t)^(-theta/2)` and every Jacobi Gram built only from it are invariant under arbitrary
   unimodular changes of spectral factor. They do not select `(3)`. The full differentiable
   shape family in `(2a)--(2c)`, not one time slice, is load-bearing.
2. **Spectral-factor uniqueness control.** Pole orientation alone is insufficient because
   opposite entire exponential gauges preserve one product. Equation `(2c)` recovers the chiral
   logarithmic derivative from normalized source data up to a spectral constant, hence exactly an
   `exp(alpha s+beta)` DA zero-charge gauge. No stronger uniqueness is asserted.
3. **Endpoint regularity.** The density normalization `c_theta` is singular as `theta->0`.
   Claims concern meromorphic Gamma factors and charge, not weak convergence of probability
   measures to a time-zero density.
4. **DA-limit control.** Differential algebraicity is not closed under arbitrary locally uniform
   limits. The content is the exact source family and its explicit endpoint, not a general
   closure theorem.
5. **Finite Euler control.** The unpolarized endpoint remains charge-zero. The theorem does not
   manufacture a defect from a finite Euler product; it canonically identifies the phase sector
   discarded by that product.
6. **Generic-calculus control.** Equations `(2a)--(2b)` are Cauchy--Riemann/chain-rule identities.
   Equation `(2e)` is the corresponding elementary cross-ratio identity. Novelty can only lie in
   their Meixner--Hardy--Euler composition and in a new arithmetic incidence theorem.
7. **Cofinal-pairing control.** Equation `(2h)` is exact prime-by-prime, but its explicit gauge and
   raw chiral factors diverge separately under all-prime completion. Only the paired Euler factor
   is admissible. Treating either raw factor as a cofinal invariant is rejected.
8. **RH control.** No zero location enters `(1)--(13)`. A remaining theorem must couple this
   source-selected chiral sector to the FE/Schwarz relative seam of an actual Xi fibre.

## 7. RH frontier changed

The prior source-weld alternative was

```text
chiral polarization or genuinely cofinal limit.
```

Equations `(1)--(12)` show these are not separate guesses. The canonical chiral polarization is
created by a genuinely cofinal Gamma--Meixner boundary:

```text
positive convolution roots
 -> pole-oriented spectral factors
 -> singular time-zero Euler endpoint
 -> DA intensity plus persistent HT phase charge.        (14)
```

The shape cross law and `(2d)` construct the previously missing phase-sensitive source map at the
archimedean end. Equations `(2h)--(2i)` then identify its prime-scaled normal shape derivative
with the actual Euler current before continuation. They do not show that the locally paired
normal weld survives the completed Xi graph or obeys the four-unit boundary estimate. The
remaining open core is therefore:

`[RH OPEN CORE: PAIRED CHIRAL NORMAL WELD / XI GRAPH DIVISIBILITY]`

Continue the locally paired identity `(2h)`—without splitting its divergent gauge/chiral
components—through the Gamma/Sonin conservative completion. On the corpus's charged
multiplication graph, prove that the completed Fisher numerator is divisible by the paired normal
overlap and that the quotient Ward curvature is at most four. Equations `(2a)--(2i)` remove phase
retrieval and finite-Euler current selection from this obligation, but do not prove graph
divisibility, cofinal convergence, or the RH-bearing estimate.

### 7.1 Imaginary shape is exactly the Shale--Dickman selector, not zero incidence

`[PAPER-PROVED BRIDGE / NO-GO]` Equations `(6a)` analytically continue in the shape coordinate.
For `a=x+iy` and real lattice label `k`,

```text
|Rhat_M(a)|^2+|Rhat_P(a)|^2=cosh(4 pi k y),
Rhat_P(a)^2-Rhat_M(a)^2=1.                               (15)
```

In particular, for the Euler slope `lambda_p=i log(p)/(2 pi)`, horizontal displacement
`h=Re(rho)-1/2`, and `a=lambda_p h`,

```text
Rhat_M=sinh(h log p),
Rhat_P=cosh(h log p),
|Rhat_M|^2+|Rhat_P|^2-1=2 sinh(h log p)^2.               (16)
```

Writing `tau(rho)=1-conjugate(rho)`, the reflected prime-clock displacement is therefore

```text
|p^(-rho)-p^(-tau(rho))|^2
 =4 sinh(h log p)^2/p
 =(2/p)(|Rhat_M|^2+|Rhat_P|^2-1).                        (17)
```

Thus imaginary Gamma shape converts the compact charge rotation into the exact Lorentz boost
already present in the reflected rational-Hurwitz block. It introduces no new horizontal
selector: its Euclidean charge inflation is prime-by-prime the formalized Shale defect.

There is also an exact finite-aperture collision with the proved symmetric Dickman boundary
cumulant. If

```text
E_N(h)=sum_(p<=N)|p^(-rho)-p^(-tau(rho))|^2,
K_N^bdry(z)=2 sum_(p<=N)[cosh(z log p/log N)-1]/p,
```

then

```text
E_N(h)=K_N^bdry(2h log N).                               (18)
```

Consequently, in the critical window `h=c/(2 log N)`,

```text
E_N(h)=K_N^bdry(c)
  -> 2 integral_0^1 [cosh(cu)-1]du/u.                   (19)
```

The corpus already proves that exponentiating this symmetric Dickman cumulant gives a zero-free
infinitely divisible boundary field and that the zeta divisor survives only in an escaping
nonperturbative monodromy sector.

Equations `(15)--(19)` kill the inference

```text
positive Meixner shape + Xi(rho)=0 -> h=0.
```

The positive source constructs the exact defect whose vanishing is equivalent to the critical
line, but `Xi(rho)=0` does not make the defect finite or zero. Any successful continuation of this
route must prove, from the paired completed source graph, that a zero fibre carries a nonzero
positive-metric intertwiner or a uniform source incidence bound. Assuming such an intertwiner,
contractivity, or all-positive-shape integrability merely restates the Shale/Landau RH consumer.
No Lean wrapper is warranted for `(15)--(19)` unless a source-to-zero incidence theorem is first
proved.

### 7.2 Four-unit graph-divisibility continuation is closed

`[CORPUS CLOSURE / ROUTE RETIRED]` The graph-divisibility obligation stated above is no longer a
live RH core.  The later critical-clock universality theorem proves that the four-unit
Fisher/Ward package factors through the simple-pole Mellin clock law.  Explicit positive Euler
sources with that same clock law and exact functional equation can carry strict-right zeros.
Hence no completion which uses only this class-invariant budget can force the Xi divisor bound.
The closure and its unconditional Lean certificates are recorded in
`docs/handover/connes.md` and `ccm-critical-clock-divisor-blindness.md`.

The source feature discarded by that budget is **entire completion**: cancellation of the real
polar channels between the prime and archimedean sides, equivalently the Poisson/theta relation.
Accordingly, `(2a)--(2i)` survive as a general HT transverse-derivation theorem, but their next RH
use must retain the entire Poisson seam.  Re-entering the four-unit, Gauss--Codazzi, or generic
contractive graph lane is rejected.

The corrected open research question is:

```text
Can the source-native transverse shape derivative be continued through the
entire Poisson/theta seam in a way that yields a one-sided orientation law
for the divisor-normal phase, rather than a critical-clock norm budget?
```

Any acceptable theorem must fail for the positive Euler/FE off-line counterexamples in the
handover and must use the cancellation that makes the completed Xi function entire.

## 8. Novelty boundary

Known separately:

- Ramanujan's Gamma Fourier transform and the Gamma--Meixner convolution semigroup;
- the Cauchy--Riemann modulus/argument derivative relation underlying `(2a)--(2b)`;
- the elementary rectangular cross-ratio law `(2e)`;
- the classical Gamma expression for the Hardy/Riemann--Siegel phase;
- Euler reflection and recurrence;
- Gamma intensity/phase differential-algebraic separation;
- real-slope reflected alien charge and the corpus's abstract charge doubling;
- the finite Euler reciprocal-Gamma identity.

Internal and external exact-phrase searches found no prior statement combining the normalized
shape-recovery law `(2c)`, the Hardy identification `(2d)`, the Euler normal-shift weld
`(2h)--(2i)`, the charge-flow equations `(4)--(7)`, and the Meixner-to-Euler pole-polarized
endpoint `(11)--(14)`. Each ingredient is elementary or classical. Search absence does not
establish priority, and significance depends on closing the Xi graph-divisibility core rather
than merely publishing the composition.

## 9. Lean status

`[LEAN-PROVED GENERAL CROSS LAW + ALGEBRAIC CORE]`

```text
formal/GaloisForLFunctions/HTGeometry/SymmetricChiralShapeLogDeriv.lean
formal/GaloisForLFunctions/HTGeometry/GammaMeixnerAlienChargePolarization.lean
formal/GaloisForLFunctions/RHTower/GammaMeixnerHardyPhaseWeld.lean
formal/GaloisForLFunctions/RHTower/GammaEulerNormalChiralWeld.lean
```

prove unconditionally:

1. both general branch-free cross laws `(2a)--(2b)`;
2. normalized-source recovery modulo the scalar gauge `(2c)`;
3. exact finite plaquette law `(2e)`;
4. exact Euler--Gamma endpoint and normal-shift welds `(2g)--(2h)`;
5. exact time-one inverse-zetaChi and inverse-Hardy-square laws `(2d)`;
6. exact exponential and sine/cosine formulas `(4)--(5)`;
7. raw and normalized norm conservation `(6)--(6b)`;
8. the finite weighted isometry `(6c)`;
9. the pure chiral time-zero endpoint `(0,1)`;
10. nonzero symmetric charge throughout `0<theta<2`.

The charge module contains no analytic Gamma function or hidden hypertranscendence premise. The
cross-law module proves the analytic Gamma specialization away from its poles. The Euler-normal
module proves `(2g)--(2h)` for an arbitrary complex exponential rate, which specializes to
`rate=log p`. The exact raw `pi^(it)` gauge, all-prime cofinal continuation, and analytic DA/HT
classifier remain paper-level parents of the source interpretation.

## Gates

- [x] exact source family identified
- [x] pole polarization defined before divisor insertion
- [x] intensity and phase charges computed on paper
- [x] singular Euler endpoint derived
- [x] phase-blind characteristic control stated
- [x] RH overclaim excluded
- [x] unconditional Lean algebraic charge-flow theorem
- [x] unconditional Lean normalized finite-source isometry
- [x] unconditional Lean general shape--spectral cross law
- [x] unconditional Lean normalized-density gauge law
- [x] unconditional Lean time-one inverse-Hardy-phase weld
- [x] unconditional Lean finite plaquette law
- [x] unconditional Lean exponential-ray Euler endpoint gauge
- [x] unconditional Lean Euler normal-shift / Gamma shape-shift weld
- [ ] independent hostile proof audit
- [ ] full primary-literature priority audit
- [x] paired four-unit graph-divisibility continuation retired by critical-clock universality
- [ ] entirety-sensitive transverse shape/Poisson-seam orientation theorem
