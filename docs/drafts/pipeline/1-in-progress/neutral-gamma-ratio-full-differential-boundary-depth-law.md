# A neutral Gamma-ratio differential field is carried by a two-stage boundary

- **ID:** `neutral-gamma-ratio-full-differential-boundary-depth-law`
- **Stage:** 1-in-progress / exact analytic compatibility lemma open
- **Type:** CONJECTURAL THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOVELTY UNVERIFIED]`
- **Statement:** For `theta>0`, every finite coefficient tuple in the full differential field of
  `G_theta(s)=Gamma(s+i theta)/Gamma(s)` should acquire a finite positive boundary carrier: first a
  phase--jet--Stokes tuple over `C(s,e^(2 pi i s))`, then one constant projective point. Conditional
  on the fixed-direction resurgent principalization lemma isolated below, differential-algebraic
  dependence over this Gamma field forces a finite rational frequency carrier. A prime packet then
  forces either differential-state complexity of size at least `pi(N)/2` or an arithmetic quotient
  carrier of complementary rank.

## 1. Setup

Fix `theta>0` and put

```text
G(s)=Gamma(s+i theta)/Gamma(s),
Psi=G'/G,
L=C(s)<Psi>,
K_theta=C(s)<G>=L(G).                                      (1)
```

The equality in `(1)` follows from the Bell-polynomial identities for derivatives of `G` and the
inverse logarithmic-derivative identities. The orbit-charge theorem gives:

```text
G, Psi, and their formal upper-sector expansions are HT over C(s),
G is transcendental over L.                                (2)
```

The last assertion follows from the scaling automorphisms `G^(j)|->c G^(j)`, which fix `Psi` and
therefore fix `L`.

Let

```text
x=1/s,
u=s^(i theta),
q=exp(2 pi i s).                                           (3)
```

The variables have distinct boundary roles: `x` measures algebraic height, `u` is the compact
logarithmic phase, and `q` is the upper Stokes scale.

## 2. Candidate quasianalytic Gamma chart

`[SEARCH; CLASSICAL]` Write

```text
Gamma(s)=sqrt(2 pi) s^(s-1/2) exp(-s) lambda(s).            (4)
```

Sauzin proves that `lambda` and its reciprocal are resurgent, stable under multiplication and
nonlinear substitution, with Borel singularities exactly over `2 pi i Z`. Across the upper and
lower Stokes directions the wall-crossing factors are rational in `exp(+-2 pi i s)`; explicitly,
the lateral Gamma sums differ by factors `1-exp(2 pi i s)` or its reciprocal.

The formal target is a fixed-upper-direction generalized-multisummable quasianalytic algebra
`M_theta` in the boundary variables, with asymptotic map

```text
T:M_theta -> C[[x,v,q]]_gen,  v=u-A.                       (5)
```

The required chart would contain the ratio and its differential field in the form

```text
G=u U(x,q),  U(0,0)!=0,                                   (6)
Psi and every derivative of Psi belong to Frac M_theta.   (7)
```

`[SEARCH]` Rolin--Servi--Speissegger construct fixed-direction generalized-multisummable algebras,
prove quasianalyticity, and prove closure under the relevant regular and singular blow-up charts.
`[SEARCH]` Bierstone--Milman prove principalization in suitable quasianalytic Denjoy--Carleman
classes. Sauzin supplies the resurgent Gamma input and its cyclic Stokes lattice.

`[OPEN CORE]` The cited statements have not yet been assembled into an exact theorem saying that the
complex upper-sector Gamma differential field lies in one such algebra and that the
Bierstone--Milman principalization functor preserves its fixed-direction sums and translated-arc
limits. This is a mathematical compatibility theorem, not a bibliographic formality.

Conditional on that chart theorem, a finite nonzero tuple in `K_theta`, after one common denominator
and one common monomial in `x,q,u`, determines a nonzero coefficient ideal

```text
I=(F_1,...,F_r) subset R=C[[x,v,q]],                       (8)
```

whose entries are fixed-direction generalized-multisummable germs. This is the **coefficient ideal
at boundary phase `A`**.

## 3. Fixed-direction Gamma principalization lemma

`[OPEN CORE]` Let `I` be as in `(8)`. There should be a finite sequence of admissible blow-ups along
smooth quasianalytic centers

```text
pi:Y->Spec R                                                (9)
```

such that

```text
I O_Y=h J,                                                  (10)
```

where `h` is one local exceptional monomial and the residual ideal `J` is the unit ideal, with the
following three properties:

1. the lifted germs remain in the same fixed-direction generalized-multisummable category;
2. asymptotic expansion, blow-up pullback, and fixed-direction summation commute;
3. every translated Gamma arc has, after a subsequence, a compact-open limiting lift on which the
   residual tuple is nonzero.

These properties make the meromorphic projective map

```text
[F_1:...:F_r]:Spec R -->> P^(r-1)                          (11)
```

extend to an actual upper-sector morphism on `Y` and make its exceptional fibers genuine functional
boundary carriers.

### Proof

Formal Hironaka principalization proves `(9)`--`(10)` for the ideal generated by the asymptotic
series in the regular complete local ring `C[[x,v,q]]`. It does not prove properties 1--3. In
particular, ordinary formal principalization neither commutes automatically with Borel--Laplace
summation nor supplies compact-open convergence of lifted translation arcs. The positive missing
theorem is therefore a **summation-stable resolution functor for Gamma coefficient ideals**. The
quasianalytic resolution and blow-up-closure results cited in Section 2 are the candidate parent
mechanism, but their exact complex fixed-direction hypotheses must be verified.

## 4. Translation arcs lift to phase--jet--Stokes carriers

Let `S_n->+infinity` be arbitrary. After a subsequence,

```text
(iS_n)^(i theta)->A,  |A|=exp(-pi theta/2).                (12)
```

For local variable `z`, the translated asymptotic coordinates are

```text
x_n(z)=1/(z+iS_n),
v_n(z)=(z+iS_n)^(i theta)-A,
q_n(z)=exp(2 pi i(z+iS_n))
      =exp(-2 pi S_n) exp(2 pi i z).                       (13)
```

`[CONJECTURE; REDUCED TO SECTION 3]` For every finite nonzero tuple `(a_1,...,a_r)` in `K_theta`,
there are a subsequence and nonzero meromorphic functional normalizations `c_n(z)` such that

```text
c_n(z)(a_1(z+iS_n),...,a_r(z+iS_n))
 ->(H_1(z),...,H_r(z))                                     (14)
```

locally uniformly in the spherical sense away from the limiting poles, where the limit vector is
nonzero and

```text
H_j in C(z,exp(2 pi i z)).                                 (15)
```

### Conditional proof

Assume the fixed-direction Gamma principalization lemma. Its property 3 lifts the arcs `(13)` and
gives a limiting point of the resolved coefficient ideal. Division by the common exceptional factor
`h` leaves a residual tuple with at least one nonzero limiting component. Pullback along `(13)` gives
the functional normalizations `c_n` and the projective convergence `(14)`.

It remains to identify the limit field. This follows inductively through the finite blow-up chain.
The initial translated coordinates have locally uniform leading jets generated by

```text
1,
z,
exp(2 pi i z).                                             (16)
```

Indeed, `x_n(z)/x_n(0)->1`; the phase-height blow-up theorem gives every nontrivial limit of `v_n`
relative to `x_n` as an affine function of `z`; and `q_n(z)/q_n(0)=exp(2 pi i z)` exactly. A
coordinate blow-up chart replaces coordinates by ratios and products of earlier coordinates. To
deduce `(15)`, the resolution in Section 3 must be chosen so that every center and residual unit has
a translated boundary value rational in the generators `(16)`. This **rational terminal-field
property** is part of the open core; arbitrary quasianalytic centers could otherwise leave a larger
terminal field.

The positive target is an exhaustiveness law: every cancellation is carried by a compact phase
divisor, a polynomial jet divisor, or a cyclic Stokes divisor, and their finite exceptional
composites.

## 5. The terminal field has one-point recession

Put

```text
E=C(z,Q),  Q=exp(2 pi i z).                                (17)
```

`[PROVED HERE]` Every finite nonzero tuple in `E` has a one-point upper functional-projective
boundary.

### Proof

Clear one common denominator and write each component as a finite Laurent polynomial in `Q` with
polynomial coefficients in `z`. Under `z|->z+iT`,

```text
Q(z+iT)=exp(-2 pi T)Q(z).                                  (18)
```

Choose the least `Q`-power occurring in the whole tuple; exponential separation makes every higher
power negligible after division by that common power. Among the surviving polynomial
coefficients, choose the greatest degree in `z`; division by `(iT)` to that degree leaves a nonzero
constant vector. This is the required one-point boundary.

Conditional on Sections 3--4, `K_theta` has the boundary-carrier chain

```text
K_theta -> C(z,exp(2 pi i z)) -> C                         (19)
```

of length at most two.

## 6. Recurrent finite-carrier law

Let `f` be holomorphic and vertically Bohr uniformly almost periodic on a vertical strip.

`[CONJECTURE; REDUCED TO SECTION 3 AND THE COMPANION FREQUENCY THEOREM]`

```text
f DA over K_theta -> f has a finite rational Bohr carrier. (20)
```

The same conclusion holds for every continuous translation-equivariant observable of the divisor
of a nonzero `f`.

### Conditional proof

Choose a nonzero ADE for `f` with a finite coefficient tuple in `K_theta`. Choose positive return
times `S_n->infinity` for `f` and every derivative occurring in the equation. Apply `(14)`.
Translation and local uniform convergence give a nontrivial limiting ADE for `f` with coefficients
in `E`.

Choose a second sequence of simultaneous return times for `f` and its derivatives and apply the
one-point recession of Section 5 to that finite `E`-coefficient tuple. The second limiting relation
is a nontrivial autonomous ADE for `f`. The autonomous implicit-ADE frequency theorem gives finite
Bohr rank and the divisor-observable conclusion.

Thus differential-algebraic dependence over `K_theta` positively equips `f` with a finite-dimensional
rational frequency carrier. Infinite rational Bohr rank is the contrapositive consequence, not the
primary formulation.

## 7. Arithmetic carrier-completion law

Assume the open core and let the final autonomous relation have minimal order `n`. Let `m` be the
size of a finite regular-sample atlas for its hull. The implicit-ADE frequency theorem gives a
differential-state carrier `D` with

```text
rank_Q D<=2m(n+1).                                         (21)
```

If the realization is required to contain the independent prime packet, put

```text
V_N=span_Q{log p:p<=N prime}.                              (22)
```

Unique factorization gives `dim_Q V_N=pi(N)`. Let `D` denote the rational frequency subspace carried
by the differential-state atlas and put

```text
A_N=V_N/(V_N intersection D).                              (23)
```

`A_N` is the **arithmetic complement carrier**. Rank additivity gives the positive conservation law

```text
dim_Q A_N>=pi(N)-2m(n+1).                                  (24)
```

Thus every realization of the prime packet comes equipped with two explicit resources:

```text
pi(N)=dim_Q(V_N intersection D)+dim_Q A_N.                 (25)
```

A Gamma-only realization has `A_N=0`, and therefore its differential order and regular-state atlas
are forced to satisfy

```text
m(n+1)>=pi(N)/2.                                           (26)
```

A bounded-complexity realization is instead forced to instantiate `A_N` in an operator,
coefficient, determinant, test space, or divisor module. Polynomial jets and Stokes strata supply
boundary depth; the quotient `A_N` supplies terminal compact character rank.

## 8. Positive carrier requirements for RH architectures

1. **Connes / Hilbert--Polya / de Branges.** The spectral operator, determinant, or canonical system
   must realize the quotient carrier `A_N`; alternatively its differential-state atlas must grow at
   the rate `(26)`.
2. **Nyman--Beurling / Weil positivity.** The cofinal test spaces must contain an arithmetic
   covariance module whose rank supplies `A_N`. Gamma jets supply the local boundary resolution,
   while this module supplies the independent Euler directions.
3. **Li-type criteria.** The coefficient hierarchy must preserve an Euler-character module whose
   cutoff rank supplies `A_N`; the neutral completion supplies the phase--jet--Stokes carrier.
4. **Finite-prime approximants.** Through cutoff `N`, the implementation must distribute `pi(N)`
   compact prime directions between the differential-state carrier and `A_N`, including through the
   `1/log N` crossover.

These are positive implementation requirements. They classify the carrier a successful realization
must exhibit; they do not reject any RH-equivalent criterion by name.

## 9. Carrier-completeness tests and extensions

1. **Polynomial jets.** The exact Gamma-ratio counterexample makes the affine jet an exceptional
   coordinate of the `(x,v)` blow-up; every higher polynomial multiplicity supplies a higher jet
   coordinate.
2. **Stokes data.** The coordinate `q` and Sauzin's wall-crossing formulas place the upper Gamma
   Stokes carrier on the cyclic `2 pi i Z` lattice.
3. **Analytic realization.** A proof must supply the summation-stable resolution functor in Section
   3, so that a nonzero resolved formal tuple produces a nonzero functional boundary tuple.
4. **Pole carrier.** Spherical projective convergence and common-denominator clearing provide the
   compactification needed for moving poles.
5. **Several neutral orbit pairs.** The carrier must contain one compact coordinate `u_c` for each
   rationally independent imaginary orbit exponent.
6. **Incommensurable scales.** The carrier must contain the full generated Stokes lattice and its
   associated multi-exponential chart.
7. **Negative slopes.** Reflection forces explicit trigonometric carrier coordinates and enlarges
   the terminal rational exponential field.
8. **Depth versus degree.** Individual elements realize jets of every degree; finite boundary depth
   asserts finite resolution for each finite coefficient ideal, not a uniform jet-degree bound.

## 10. Parent and novelty audit

`[NOVELTY UNVERIFIED]`

- Gamma resurgence, the `2 pi i Z` Borel lattice, and the exact Stokes wall-crossing factors are
  classical; Sauzin gives explicit modern formulas.
- Formal principalization and elimination of projective indeterminacies are classical
  Hironaka--Kollar theory. They do not by themselves establish the open analytic compatibility
  lemma.
- Bierstone--Milman supply principalization in suitable quasianalytic classes, while
  Rolin--Servi--Speissegger supply quasianalytic fixed-direction generalized-multisummable algebras
  closed under blow-up charts. Verifying that the complex Gamma chart satisfies one common theorem
  is the open core.
- The relative/autonomous almost-periodic frequency theorem is supplied by the companion pipeline
  work.
- Preliminary searches did not locate the boundary-carrier chain or the arithmetic complement law
  specialized to a full Gamma differential field.
- Scientific novelty cannot be assessed until Section 3 is proved. If the required compatibility is
  an immediate corollary of one parent theorem, the result is a bridge rather than new science.

Primary adjacent sources:

- D. Sauzin, *Variations on the Resurgence of the Gamma Function*, arXiv:2112.15226. In particular,
  the Borel singularities lie over `2 pi i Z`, resurgence is stable under nonlinear operations, and
  the Stokes jumps are rational in `exp(+-2 pi i s)`.
- J. Kollar, *Lectures on Resolution of Singularities*, especially principalization and elimination
  of indeterminacies.
- E. Bierstone, P. Milman, *Resolution of singularities in Denjoy--Carleman classes*, Selecta Math.
  10 (2004), 1--28; arXiv:math/0108204.
- J.-P. Rolin, T. Servi, P. Speissegger, *Multisummability for generalized power series*, Canad. J.
  Math. 76 (2024), 458--494.
- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503.

## 11. Lean status

The tree contains unconditional Gamma/digamma vertical boundary lemmas and algebraic
projective-Gamma jet relations. Stage 3 requires the complete positive carrier theorem, including a
resurgent Borel--Laplace algebra, a formal/analytic quasianalyticity interface, principalization of
analytic ideals, blow-up lifting, and Bohr hull frequency theory. The present card therefore remains
in stage 1.

## Gates

- [x] exact three-coordinate boundary chart identified
- [x] exact summation-stable principalization lemma isolated
- [ ] complex fixed-direction Gamma chart placed in one quasianalytic blow-up-closed category
- [ ] summation-stable coefficient-ideal principalization proved
- [ ] rational terminal-field property proved for the chosen centers
- [ ] phase--jet--Stokes limit field identified unconditionally
- [x] terminal one-point recession proved
- [x] arithmetic complement law proved conditionally from the boundary and frequency theorems
- [ ] recurrent finite-carrier law proved unconditionally
- [ ] full parent-literature and priority audit
- [ ] complete unconditional Lean formalization
