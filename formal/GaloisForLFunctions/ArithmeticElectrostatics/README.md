# Arithmetic Electrostatics of the Zero Divisor (AES)

Namespace `GaloisForLFunctions.ArithmeticElectrostatics`; umbrella `ArithmeticElectrostatics.lean`.

**Question.** The nontrivial zeros are the charges of one logarithmic potential $U=\log|\xi|$. Arithmetic computes four
quantities of it: its Laplacian (the collided form $D$), its regularized gradient at the charges (the field $E$, read off
$\Lambda\star\Lambda$), its renormalized self-interaction at the diagonal (torsion log-discriminants; the double pole of $(\zeta'/\zeta)^2$), and its
reflection pairing (Weil's form $W$). RH says the configuration is in **transverse equilibrium**: no zero feels a field
across the critical line. Equilibrium is computed; its *stability* is the sign. Which inequality between the computed
quantities makes it stable, which renormalization of the diagonal joins positivity and equivariance, and which of these
inequalities are provably out of reach?

Two charge carriers and a dictionary between them:
- the **zero divisor** $Z=\sum m_\rho\delta_\rho$ with reflection $\rho\mapsto1-\rho$ (explicit formula) and conjugation $\rho\mapsto\bar\rho$ (potential theory);
- the **characteristic circle** $\mathbb R/\mathbb Z$: torsion orbits $O_n$ as charges, $-\log|z-w|$ as Green function, power maps $z\mapsto z^t$ as
  Hecke correspondences, the arithmetic point $z=1$ as distinguished fibre.

> The explicit formula is the equilibrium equation; it does not supply stability. On the circle both equilibrium and
> stability are theorems, and the torsion realizes them.

---

## 1. Place in the research

What is missing has a precise shape: an inequality turning the computed positive form or field into a bound, or a
renormalization keeping a positive equivariant family positive at the diagonal. Over $\mathbb F_q$ both come from a polarization
(Riemann–Roch, Frobenius similitude, $\Delta^2=2-2g$). AES states and tests the joining inequality — a **Hodge index theorem
with adjunction** — and reduces it to its sharp form. AES supplies the atomic stability law, gauge invisibility of the prime
form, and mean values at zero ordinates to the proposed harmonic analysis at the spacing scale.

| Programme | Takes / adds |
|---|---|
| ArithmeticPolarization | $W,D,\Delta$, log-Sobolev equivalence, $\sigma_\gamma$ / $D$ as Riesz energy of $\log|\xi|$; affine-blindness of electrostatics |
| ConjugateDiagonalGeometry | $\xi$ current, theta readings / field and transverse energy of the same current |
| ArithmeticCorrespondencePositivity | Quadratic terminals, source field, $L(\Lambda\star\Lambda)=(\zeta'/\zeta)^2$ / virial laws, field threshold, renormalized square |
| ArithmeticEffectivityTheory | Torsion orbits, $I(m,n)$, Hecke law, Abel energies / self-intersections, adjunction, counterterm rates, Fekete |
| `RHTower` (transverse chain) | Transverse force, marginality, maximum principle, attainment dichotomy, Selberg's identity / whole-divisor energy, window selection |
| ArithmeticIntersectionTheory | Local different of torsion orbits / bridge $\varphi\star\Lambda=\varphi\cdot$tame different |
| BiarithmeticGaugeGeometry, ArithmeticCorrelationGeometry | Gauge torus, twins / gauge charge of the renormalized source |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Scaling surface, Hodge index / electrostatic reading of adjunction |
| RenormalizedArithmeticPotentialTheory | Sharp two-sided atomic counterterm $\log N+O(1)$ |

---

## 2. Why

**Two involutions.** The explicit formula sees reflection (pairing $W$, equivariant, positivity = RH); potential theory sees
conjugation (Riesz measure = zero divisor, pairing $D$, positive, equivariance = RH). They agree iff $\bar\rho=1-\rho$ at every zero.

**Stieltjes without an ODE.** Zeros of classical orthogonal polynomials are equilibria in an external field via their ODE; $\xi$
has none, so equilibrium is not variational. What holds on every configuration are **virial laws**: work = energy. The
transverse virial turns the field into a nonnegative Dirichlet energy of the real parts on the complete graph of zeros.

**Quantization.** An off-line zero and its partner share their ordinate; the horizontal segment contributes exactly
$m_\rho m_{\rho^*}$ at every depth. Energy is 0 or $\ge1$ quantum; detection is a quantized lower bound; the missing input is an upper
bound of definite size.

**One diagonal, three appearances.** $\Delta\cdot\Delta=2-2g$, torsion self-energy $\log1/(1-r)$, double pole $m^2/(s-\rho)^2$ of $(\zeta'/\zeta)^2$. In both
arithmetic instances the self-term is renormalized by the **degree** $\log n$ of $T_n$: on the zero side $(\zeta'/\zeta)'=\sum\Lambda(n)\log n\,n^{-s}$
turns the square into Selberg's nonnegative $\Lambda_2=\mu\star\log^2$; on the circle the self-intersection per point of $O_n$ is $\log n$ minus
local terms, growing by $\log p$ along towers: arithmetic adjunction.

**Stability on the base.** The circle's discrete log-energy is bounded below (Fekete–Hadamard) and the torsion attains it.
The torsion pairing is positive before renormalization and Hecke equivariant after; the obstruction is a self-energy
diverging logarithmically in the order, carried by the arithmetic point.

---

## 3. Objects and language

| Electrostatics | Zero divisor | Circle | Lean |
|---|---|---|---|
| charges | zeros, $m_\rho$ | torsion orbits $O_n$ | `XiZeroCopy`, `XiDivisorSupport`, `primitiveRoots` |
| field at a charge | $E(\rho)=\sum_{q\ne\rho}m_q/(\rho-q)$ | — | `fieldAt`, `xiTransverseField`, `transverseForce` |
| transverse energy | $\tfrac12\sum m_\rho m_q(\Re\rho-\Re q)^2/|\rho-q|^2$ | — | `transverseEnergy`, `divisorTransverseEnergy`, `xiCopyTransverseEnergy` |
| work; window energy | $\sum m_\rho(\Re\rho-\tfrac12)\Re E(\rho)$; $\sum_{|\gamma-T|\le H}$ | — | `transverseWork`, `windowEnergy` |
| self-energy | double pole $m^2$ → $m(m-1)$ in $\zeta''/\zeta$ | $\log1/(1-r)$ → $I(n,n)=\log|\operatorname{disc}\Phi_n|$ | `selfTerm_and_residue_of_analyticOrderAt`, `orbitIntersection` |
| renormalized source | $\Lambda_2=\mu\star\log^2$ | $\varphi\star\Lambda$ | `selbergSource`, `localCorrection` |
| renormalized pairing | — | $\sum y_my_nI(m,n)$ vs $\kappa\sum\varphi(n)y_n^2$ | `torsionPairing`, `RenormalizesAt` |
| distinguished fibre | critical line | arithmetic point $z=1$ | `primitiveRoots_one` |
| atomic tests | bumps of width $w$ at $\log n$, $n\le N$ | — | `atomicTest`, `atomicWeilForm`, `atomicWidth` |

**Words.** *Equilibrium* (vanishing transverse field); *stability* (positivity of the energy whose gradient is the field);
*virial law*; *quantum*; *gap* (reflection-closed energy never in $(0,1)$, windows never in $(0,2)$); *self-term*, *regularized*,
*renormalized*, *counterterm*, *Hecke compatible*; *adjunction*; *cover formula*.

---

## 4. Mechanisms

**Finite configurations.**
1. **Virial laws**: Newton's third law; Stieltjes' virial (a count); transverse virial = transverse energy for every centre;
   transverse + vertical = $\tfrac12((\sum m)^2-\sum m^2)$.
2. **Equilibrium is the critical line** on reflection-closed configurations; nonpositive work ⇔ critical; deepest charge feels an
   outward field.

**The divisor.**
3. **Energy of the divisor**: $=0$ ⇔ RH ⇔ $<1$; finite ⇔ finitely many off-line zeros; $\#$off-line $\le2\cdot$energy.
4. **Global arithmetic work**: rationally damped, tapered work of the Laurent residues of $(\zeta'/\zeta)^2$ converges and exhausts the
   multiplicity-weighted transverse energy — work = energy as an arithmetic limit; the missing upper bound is the sign problem.
5. **Window selection**: window energy counts off-line zeros; energy $<2$ ⇒ critical.
6. **Energy of a zero is logarithmic**: $1\le E(\rho)\le16(C+\log(|\gamma|+4))$ off the line (Lorentzian zero mass). The field has no unconditional bound.
7. **Hecke defect = moment of inertia**: $4L^2M_f\le E_f(L)\le8(\cosh L-1)M_f$.

**The field.**
8. **The field is computed**: residue of $(F'/F)^2$ and of $F''/F$ at a zero of order $m$ is $2mR(\rho)$, $R$ the regular part = field of the other zeros.
9. **Field threshold**: RH ⇔ field $\le1$ at every right zero ⇔ field $<\sqrt{2c\log\gamma}$ (terminal reserve $1/(2\delta)+c\delta\log\gamma$).
10. **External field is a prime sum** for $\Re s>1$; **anti-alignment** at a zero ordinate:
    $\sum\Lambda(n)n^{-\sigma}\cos(\gamma\log n)\le\Re(\text{arch}'/\text{arch})(\sigma+i\gamma)-m/(\sigma-\beta)$.
11. **Large values at zero ordinates** (Sobolev on unit cells + local zero ceiling + mean value): alignment of prime polynomials of
    length $X$ to $(1-\eta)\log T$ happens at a vanishing proportion of zeros for $\log X=o(\sqrt{\log T})$; higher moments ($F^k$, mass $\le k!(\sum|c_p|^2)^k$)
    give a power saving $T^{1-1/C+o(1)}$.

**Renormalization of the diagonal.**
12. **Zero side**: $F''/F=(F'/F)^2+(F'/F)'$; $\Lambda_2=\Lambda\log+\Lambda\star\Lambda\ge0$, $L(\Lambda_2)=\zeta''/\zeta$.
13. **Circle**: $I(n,n)=\varphi(n)\log n-(\varphi\star\Lambda)(n)$; additive on coprime orders; cover formula; per point the different of $\mathbb Q(\zeta_n)$.
14. **Counterterm rate**: minimal constant counterterm on orders $\le N$ lies in $[\tfrac12\log(N/2),4\log N+O(1)]$; the atomic Weil prime form has the
    same logarithmic rate (sharp two-sided $\log N+O(1)$ with the pole vector) — forced by the atom at the arithmetic point.
15. **Stability law at atomic resolution**: below the spacing $\delta_N$ atoms are orthogonal, Lévy self-energy $\ge e^{-1/2}\log(\delta_N/2w)$ per unit mass,
    prime sum = $(\int g^2)\times$atomic form; so $M=\text{arch}-\text{prime}\ge0$ for widths $w\le$ `atomicWidth N` $=N^{-O(1)}$ (sharp: $\delta_NN^{-e^{1/2}}$). With the pole
    $\Re W=M+2C^2-2S^2$: $\Re W+2S^2\ge0$ (rank-one counterterm), $\Re W\ge0$ on nonnegative atomic tests.

**The base and the arithmetic point.**
16. **Power maps are similitudes** of the PSD Abel energy $T_r(A,B)=\gcd\log1/(1-r^{\rm lcm})$; adjunction = shift of self-energy under rescaled cutoff.
17. **Torsion is the stable equilibrium**: $\sum_{i\ne j}\log|z_i-z_j|\le N\log N$, attained by roots of unity.
18. **The arithmetic point carries the divergence**: $I(1,n)=\Lambda(n)$; any counterterm has $c(1)\ge\sum\Lambda^2/(c\varphi)$.

**Gauge.**
19. Reflection-commuting affine maps preserve transverse energy (archimedean twists invisible).
20. Twin sources $\omega\Lambda_2$; nonnegativity forces $\omega(p)=1$; coefficient margin $2\log^2p$ at the first flipped prime.
21. **Gauge invisible at atomic resolution**: $P_\omega=\operatorname{diag}(\omega)P\operatorname{diag}(\omega)$; the stability law holds for every sign twin; the difference is
    archimedean polarization across the charge; on nonnegative tests the twin *wins* by $2\Lambda(p)/\sqrt p$ per unit mass.

---

## 5. Pillar theorems

1. **Virial laws; equilibrium = critical line; quantum gap** (`sum_mul_re_fieldAt_eq_transverseEnergy`, `critical_iff_equilibrium`,
   `critical_iff_transverseEnergy_lt_one`).
2. **Energy of the divisor** (`riemannHypothesis_iff_divisorTransverseEnergy_lt_one`, `divisorTransverseEnergy_lt_top_iff`).
3. **Global source-work exhaustion** (`xiDampedSourceWork_tendsto_energy`).
4. **Window selection** (`riemannHypothesis_iff_windowEnergy_lt_two`).
5. **Defect = moment of inertia** (`tendsto_heckeDefect_div_sq`).
6. **Field threshold** (`riemannHypothesis_iff_forall_transverseField_le_one`, `exists_riemannHypothesis_iff_transverseField_lt_sqrt_log`).
7. **Anti-alignment and large values at zero ordinates** (`re_LSeries_vonMangoldt_le_at_zero_ordinate`, `exists_card_aligned_le`,
   `exists_card_aligned_power_saving`).
8. **Renormalized square and torsion adjunction** (`selbergSource_nonneg`, `LSeries_selbergSource`, `orbitIntersection_self_eq`,
   `orbitIntersection_self_prime_pow_succ`).
9. **Logarithmic counterterm; arithmetic point** (`torsionCounterterm_rate`, `log_two_mul_le_sq_of_atomicWeilForm_le`, `le_counterterm_one`).
10. **Similitudes and Fekete stability on the base** (`fullTorsionEnergy_mul`, `sum_sum_log_norm_sub_le`).
11. **Stability at atomic resolution, with pole and sharp counterterm** (`markovEnergy_atomicTest_nonneg`, `markovEnergy_atomicTest_nonneg_sharp`,
    `re_W_add_sinh_sq_nonneg`, `re_W_atomicTest_nonneg_of_nonneg`).
12. **Gauge invisibility at atomic resolution** (`twistedWeilPrimeKernel_eq`, `twinMarkovEnergy_atomicTest_nonneg`, `twinMarkov_sub_markov_atomicTest`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Equilibrium can be derived variationally | Stieltjes needs a linear ODE; $\xi$ has none |
| Marginality is an inequality awaiting proof | RH-equivalent: attained case RH, non-attained is escape |
| A positive field at the deepest zero excludes it | It detects; exclusion needs an upper bound $\max(1,\sqrt{2c\log\gamma})$ |
| Transverse energy decays as zeros approach the line | Quantized: a full unit per pair at every depth |
| Removing the diagonal keeps positivity | Needs a counterterm $\Theta(\log N)$ |
| A bounded counterterm suffices on most orbits | The arithmetic point forces divergence |
| $\Lambda_2\ge0$ is positivity beyond isotropy | Coefficient positivity; the field enters only via residues |
| Field and energy are equally hard | Energy is $O(\log\gamma)$ per zero unconditionally; field unbounded |
| Archimedean self-energy cannot pay the prime form | It pays it below a power of the spacing; not at the spacing |
| A coefficient gauge margin gives a form margin | On atoms the gauge is a diagonal of signs: zero spectral margin |
| On nonnegative tests $\zeta$ beats its twins | It loses by $2\Lambda(p)/\sqrt p$ per unit mass |
| The pole term is a nonnegative correction | Signature $(1,1)$; $-2S^2$ is the rank-one counterterm |
| Energy controls the potential at a point | Log energy does not bound pointwise potentials (Franel–Landau) |

---

## 7. Open problems

1. **The field law**: an arithmetic upper bound for the transverse field at right zeros below $\max(1,\sqrt{2c\log\gamma})$, or unit-window energy
   below 2 (RH-strength); partial forms: finite total energy (finite off-line index), window energies below the zero count.
2. **Stability law at the spacing** $w\asymp1/N$: the Lévy gain is bounded there and the prime counterterm is not, so positivity must come
   from cancellation in the prime form; does a bounded-rank counterterm survive?
3. **Matched renormalization**: torsion counterterm vs zero-side $\Lambda\log$ through the explicit formula for $\zeta''/\zeta$.
4. **Electrostatics of twins** at the level of forms: overlapping atoms, near-coincidences $m/n\approx k$ where the Lévy gain fails.
5. **Attainment**: exclude infinite transverse energy, or an energy criterion for attainment of the depth supremum.
6. **Alignment against depth (forcing law)**: every zero of depth $\delta$ makes a short prime detector reach $V(\delta)$ at its ordinate; with the
   power-saving count this would be a zero-density estimate $T^{1-1/C+o(1)}$ for deep zeros. The terminal reserve lies below the
   background $\tfrac12\log\gamma$; forcing needs a reserve $(\tfrac12+c'\delta)\log\gamma$ reaching $\Re s>1$.

## 8. Tools to build

A field upper bound at right zeros; positivity at the spacing scale from prime cancellation; a calculus of overlapping atoms
and non-ratio lags; a forcing law at zero ordinates.

## 9. Contribution standard

Unconditional; state the carrier (divisor or circle), the involution (reflection or conjugation), whether a quantity is
computed, bounded or posited, detected or excluded; state counterterm size and Hecke compatibility; report gauge behaviour
(archimedean twist vs sign gauge) and the battery; record the positive survivor of every no-go.
