# Multiplicative Positivity Geometry (MPG)

Namespace `GaloisForLFunctions.MultiplicativePositivityGeometry`; umbrella `MultiplicativePositivityGeometry.lean`.

**Question.** The only forcing mechanism in the corpus is multiplicative: positivity of the Euler
log-coefficients $\Lambda(n)\ge0$, coupled across the harmonics of a height, forces $\zeta(1+it)\ne0$, and with
growth input the classical zero-free regions. What is the complete content of that positivity — everything it
permits, everything it forces, and exactly what it can certify in the strip?

**Basic object:** the **boundary divisor** $D(u)=$ (pole order) − (zero order) at $1+iu$, a function on the discrete
group $(\mathbb R,+)$. **Basic theorem:** for nonnegative log-coefficients $D$ is an even positive-definite function.
De la Vallée Poussin, Mertens and Fejér inequalities are Gram forms of this one function.

**Status.** On the boundary the theory is complete (classification + realization). In the interior it is closed
for positive certificates with constant growth input: the best case is strictly below any fixed strip. The missing
input for RH lies outside multiplicative positivity — in the growth input or an interior object.

---

## 1. Place in the research

Two exhaustion facts: single-channel quadratic positivity certifies only blindness (maximal blind ideal,
ArithmeticCastelnuovoSeveri); coefficient positivity forces, but only on $\Re s=1$ (VK with growth input). MPG is the
theory of the second.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Maximality theorem (quadratic side); harmonic coupling, Fejér barrier $a_1<2a_0$ |
| `HTGeometry` | `cosinePolynomial`, universal purchase cap, Bohr means; Riemann theta relation characterizes $\mathbb Z$ |
| `RHTower` | dlVP calibration input; classical dlVP, Littlewood, VK regions; over-regular Beurling systems |
| ArithmeticOrientationGeometry/Theory | Orientation = positive definiteness of orbit correlation (quadratic counterpart); golden datum passes multiplicative positivity |
| BVI, THIM, SRT, AOT width functor | Their receivers are width statements; MPG's growth law says which widths positivity can reach |

---

## 2. Why

**The boundary is a limit of positive-definite functions.** For $\sigma=1+x$, $u\mapsto\Re(-\zeta'/\zeta)(\sigma+iu)=\sum\Lambda(n)n^{-\sigma}\cos(u\log n)$
is positive definite; multiply by $x$, let $x\downarrow0$: pole order at 1 minus zero orders on the line. Positive
definiteness survives pointwise limits.

**Positive-definite integer functions are rigid.** With $D(0)=1$ and integer values, $D\in\{-1,0,1\}$; a three-point
Gram form makes the nonvanishing set a subgroup and $D$ a $\pm1$ character on it. A boundary zero is a $-1$ of a
character, so $D(2u)=1$: every boundary zero forces a pole at twice its height. $\zeta$ has none, so $\zeta(1+it)\ne0$.

**In the interior there is no limit.** Zeros in the strip enter only through continuation and growth bounds; the
method reduces to one inequality between pole weight, zero weight and growth.

---

## 3. Objects and language

| Object | Definition | Lean |
|---|---|---|
| Positive-definite function | $\sum c_ic_j\varphi(x_i-x_j)\ge0$ on an additive group | `IsPosDef`, `IsEvenPosDef` |
| Cosine trace | $\sum w_i\cos(\lambda_iu)$, $w_i\ge0$ | `cosineTrace` |
| Boundary datum / divisor | damped weights $w(x)$ with $x\cdot\text{trace}\to D$ | `IsBoundaryDivisor`, `zetaBoundaryDivisor` |
| Nonvanishing subgroup | $\{D\ne0\}$ for integer $D$, $D(0)=1$ | `nonvanishingSubgroup` |
| Profile | $m\mapsto D(mt_0)$, PD sequence on $\mathbb Z$ | `profileCoeff` |
| Twist | weights times $P(t_0\lambda_i)$, $P\ge0$ cosine polynomial | `twistedWeight` |
| Certificate, purchase ratio | nonnegative cosine/almost-periodic polynomial; $a_1/a_0$ | `cosinePolynomial` |
| Exclusion | $A/\delta+G<B/(\delta+\eta)$: pole $A$, zero $B$ at distance $\eta$, growth $G$ | `exclusion_iff` |
| Joint divisor | families over finite abelian $G$, on $G\times\mathbb R$ | `IsJointBoundaryDivisor` |

**Four boundary invariants:** (N) nonnegative weights; (Z) integer divisor; (S) simple pole $D(0)=1$; (I) pole
isolation, $D\le0$ off 0. Keep separate: test-space positivity (Weil, Hodge) vs height-space positivity (MPG); one Gram
form vs all; boundary (limit, exact) vs interior (continuation + growth); certificate vs input.

---

## 4. Mechanisms

1. **Two-point Gram** $|\varphi(h)|\le\varphi(0)$: zero order ≤ pole order.
2. **Three-point translation** + integrality ⇒ subgroup-and-character structure.
3. **Fejér progression vector** on $0,h,\dots,(N-1)h$.
4. **Closure** of PD functions under limits (from $\sigma>1$ to the line).
5. **Discreteness / Baire.** Locally finite divisors have cyclic nonvanishing subgroups; boundary divisors are
   pointwise limits of continuous functions, so cannot be $\pm1$ on a dense subgroup and 0 on its translate.
6. **Twisting = convolution of divisors** (product-to-sum on characters).
7. **Dual quadrature** on roots of $z^{K+2}=-1$ (extremal Fejér certificates).
8. **Geometric-mean damping** $\delta^*=\sqrt{A\eta/G}$ turns exclusion into AM–GM.
9. **Følner Gram forms** (polynomially growing sets) see every zero with weight $\approx|F_N|$; Bohr means along
   non-resonant progressions.
10. **Rankin–Selberg Bessel**: the square of a signed datum bounds the $\ell^2$-norm of its divisor.
11. **Decay-exponent law**: growth rates of $\log|Z|$ replace boundary limits.

---

## 5. Pillar theorems

1. **Boundary positivity** (`IsBoundaryDivisor.isEvenPosDef`).
2. **Simple-pole rigidity and trichotomy**: zero at $u$ forces pole at $2u$; locally finite simple-pole integer
   divisors are $1_{\{0\}}$, $1_{c\mathbb Z}$ or the alternating character (plus constant 1 in general)
   (`boundary_zero_forces_double_pole`, `boundary_trichotomy`, `boundary_tetrachotomy`).
3. **Total zero mass** $\le D(0)/2$ without off-origin poles, sharp; abelian version (`total_zero_mass_le`, `total_offOrigin_mass_le`).
4. **$\zeta$ on the line from positive definiteness alone** (`riemannZeta_boundary_ne_zero_of_posDef`).
5. **Completeness and minimality**: (N),(Z),(S),(I) force $D=\delta_0$; dropping any one admits a realized boundary zero
   (`boundary_forcing_law`, `isolation_necessary`, `simplicity_necessary`, `integrality_necessary`, `nonnegativity_necessary`).
6. **Interior invisibility**: $\zeta(s)\Phi(s+\kappa)$ satisfies all four invariants and vanishes in the strip (`interior_zero_invisible`).
7. **Exact Fejér barrier** $a_1\le2\cos(\pi/(K+2))a_0$, attained; any finite multi-frequency certificate has $a(\gamma)\le2a(0)$
   (`cosinePolynomial_first_le_fejer`, `multiFrequency_purchase_le_two`).
8. **Growth-to-forcing law**: exclusion ⇔ $\sqrt A+\sqrt{G\eta}<\sqrt B$; certified width exactly $(\sqrt B-\sqrt A)^2/G$; universal cap
   $(3-2\sqrt2)/(2L)$; dlVP is the instance $(3,4,\tfrac52\log\gamma+C)$ with no better region from it
   (`exclusion_iff`, `multiFrequency_width_cap`, `dlvp_input_consistent`).
9. **Bochner realization**: a locally finite $D$ is a boundary divisor iff even PD; realized by one Dirichlet series
   $\sum\Lambda(n)g(\log n)n^{-s}$ and by an integral Euler product $\prod_p(1-p^{-s})^{-m(p)}$; summable configurations
   (dense supports included), families, and one prime progression realize the whole summable cone
   (`locallyFinite_boundary_divisor_iff`, `arithmetic_bochner`, `integral_bochner`, `summable_real_integral`, `progression_realizes`).
10. **Rankin–Selberg forcing**: simple poles of $f$ and $f\otimes f$ force $D_f=\delta_0$ (`rankinSelberg_forcing`).
11. **Families and the Siegel exception**: on $G\times\mathbb R$ the only unforced configuration is $\delta_0-\delta_{(h,0)}$ with
    $2h=0$; order-two fibres have purchase ratio 1, so a real zero at any $\beta<1$ is unexcluded
    (`joint_boundary_classification`, `unpaired_real_zero_unexcluded`).
12. **Decay and Beurling thresholds**: $\sum\alpha_z\le k/2$ for decay exponents; count error $O(t/\log^\gamma t)$ with $\gamma>3/2$
    leaves no boundary zero (`decay_mass_law`, `beurling_zero_count`).
13. **Positivity margin**: weights $\ge-\varepsilon\Lambda$; a simple pole forces $\delta_0$ iff $\varepsilon<1$ (`simple_pole_margin_threshold`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| One harmonic inequality is the whole positivity | It is one Gram form; PD is all of them |
| More channels buy more | Any finite multi-frequency certificate has $a(\gamma)\le2a(0)$ |
| Higher degree approaches the cap | $2\cos(\pi/(K+2))<2$ at every degree |
| Boundary completeness reaches the interior | Boundary data cannot see interior zeros |
| Positive definiteness alone forces vanishing | Needs integrality (half zeros otherwise) |
| (Z) is integrality of prime data | It is meromorphy at the boundary; integral Euler products realize everything PD |
| Twisted products are Beurling systems | Prime weights not integral; they calibrate positivity |
| A better constant is a better method | The constant is fixed by $(A,B,G)$; only better input helps |
| Function-field positivity proves Hasse | The golden datum has nonnegative counts and fails RH |
| Multiplicative positivity excludes Siegel zeros | Order-two fibres have purchase ratio 1 |

---

## 7. Open problems

1. **Interior positivity.** Which positive-definite structure survives continuation into $\tfrac12<\sigma<1$? It cannot
   be a boundary datum.
2. **Interior invariants.** Without the functional equation the answer is no (over-regular Beurling systems; $\zeta(s)/\zeta(s+1-\beta)$
   keeps all four invariants); with Riemann's theta relation and integral masses only $\zeta$ remains, so the question
   becomes RH itself.
3. **$\sigma$-dependent growth.** State the VK step on a $\delta$-range (it would give VK with optimal constant and barrier);
   inputs with genuinely $\delta$-dependent $G(\delta)$.
4. **Full range of the boundary map** beyond local finiteness (a cone closed under summable sums containing dense supports;
   PD alone is not enough — $1_{\mathbb Q}$ is PD and not a divisor).
5. **Integral realization** of non-locally-finite configurations.

## 8. Tools to build

A positive-definite object attached to the strip; VK and Littlewood inputs as range-limited inequalities; a law for
$\delta$-dependent growth.

## 9. Contribution standard

Unconditional, with $\zeta$ inputs limited to $\Lambda\ge0$, the residue, the Euler factorization and named growth bounds;
states a classification, realization, exact constant or sharp barrier (not a new RH equivalent); selective (distinguishes
$\zeta$ from a realized countermodel, or proves none of its class can); keeps boundary/interior, forced/imported,
certificate/input separate; records the positive survivor of every no-go.
