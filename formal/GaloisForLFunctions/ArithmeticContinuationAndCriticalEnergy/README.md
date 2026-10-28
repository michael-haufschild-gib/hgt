# Arithmetic Continuation and Critical Energy (ACCE)

**One question.** A critical energy of an exact arithmetic source is finite at one end of a
parameter range (half damping, a finite cutoff, a bounded aperture); RH says it stays finite as the
parameter runs to the critical end. Which arithmetic identities prevent the energy from escaping
on the way, and what exactly must be estimated to use them?

ACCE is a theory of **transport in a parameter**. Where the incidence, lag and aperture faces ask
for a sign at a fixed parameter, ACCE asks for the derivative: how much energy the family loses
per unit of parameter, read through a scale, and what pays that loss. Objects carry two indices —
a continuous parameter and an observation horizon — and the only currency is a bound **uniform
in the horizon**.

Namespace `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`; umbrella
`ArithmeticContinuationAndCriticalEnergy.lean`.

---

## 1. Place in the research

Model: the exact damped Möbius divisor source in the pronic norm. Half damping is admitted;
admission at dampings accumulating at 0 is RH; the accumulation threshold is exactly the width
$\Theta-\tfrac12$. Pillars: exact work identities, linear/Osgood transport, signed averaged budgets
= admission, the dilation calculus of integer prefixes, and the exact aperture shell-flux law.
These locate the missing source estimate; they do not supply it. Partial results score in the
width unit: a budget on $(a_0,c]$ is the strip $\Theta\le\tfrac12+a_0$.

| Programme | Connection |
|---|---|
| arithmetic-positivity-theory | Fixes source and complete energy |
| BiScaleUncertainty | Blind models; recovery vs stable estimates |
| TransHorizonIncidenceMechanics | Owns the finite-horizon receiver and damping admission |
| BezoutValuationIncidence | Markov derivative, divisor identities, pronic geometry, damping chain |
| ArithmeticCriticalityTheory | Aperture path $\mu(A)$ and its doubly exponential ceiling |
| SquareRootThreshold | Damping threshold = width; partial transport = strip |
| ArithmeticIncidencePositivity | Local window certificates; signed prime–polar decomposition |
| ArithmeticCompensationTheory | Coupled flux–forcing budgets; positive-part failure; adapted energies; floor-loss laws |
| ArithmeticDefectRigidity | Forcing–cofactor cancellation in the same receiver; uses exact pronic dilation blocks |
| ArithmeticOrientationTheory | Cofinal admission = damping unit; damping preserves residue-mode signs (magnitude is the issue) |
| Others (SSIC, ACS, SAEI) | Observation sign-preservation; effectivity; signed incidence kernel |

Routes: RW uses the compensated width floor, aperture transport, shell flux and rate equalities;
PM uses the classification of obstructing terms, complementary-sector propagation and
signed-observation stability.

---

## 2. Why

Three proved obstructions shape the choice: receiver changes are not arithmetic bounds; bounded
apertures cannot decide arbitrary configurations; below half damping no sign-blind datum controls
the receiver. With
$c_\varepsilon(d)=\mu(d)d^{-\varepsilon}$, $A_\varepsilon(n)=\sum_{d\le n}c_\varepsilon(d)\lfloor n/d\rfloor-n\Re(1/\zeta(1+\varepsilon))$,
$E_T(\varepsilon)=\sum_{n\le T}A_\varepsilon(n)^2/(n(n+1))$: admitted at $\varepsilon\ge\tfrac12$; RH = admission
accumulating at 0. RH is not an inequality at one damping; it is whether finite energy **survives
transport** to zero damping. Transport needs a bound on the rate of loss on compact intervals away
from the critical end, starts from a known finite state, and needs only the energy-*increasing*
part of the derivative backwards. Cutoff removal and aperture growth are continuations in the same
sense.

---

## 3. Objects and language

**Energy families** $E:\mathbb R\to\mathbb N\to\mathbb R$ (module `CriticalEnergyFamilies.lean`): `Admits E ε`
($\exists B\forall T$ — the quantifier order is the content); `CofinallyAdmits`; `UniformlyAdmitsOn`.
Horizon monotone ⇒ admission along any cofinal (e.g. dyadic) horizons or on Cesàro means suffices.

**Critical energy of record** `dampedMobiusEnergy` (= `pmPowerDampedDivisorDiscreteEnergy`):
`mem_receiverDampings_iff_admits`, `riemannHypothesis_iff_cofinallyAdmits`; strictly positive.

**Signed work** $W_T(\varepsilon)=\sum_{n\le T}A_\varepsilon(n)E_\varepsilon(n)/(n(n+1))$, $E_\varepsilon=\partial_\varepsilon A_\varepsilon$
(`signedDampingWork`) — one signed number, not a norm.

**Tangent autocorrelation** $K_T(\eta,\varepsilon)=\sum E_\eta(n)E_\varepsilon(n)/(n(n+1))$; second tangent
$F_\varepsilon$ = centred prefix of $\sum_{d\mid k}\mu(d)(\log d)^2d^{-\varepsilon}$.

**Budgets.** Pointwise linear: $-E_T'\le\beta'(1+E_T)$ with $\beta$ horizon-free
(`LinearContinuation`); Osgood with coercive scale $\Psi$ (`OsgoodContinuation`); **averaged**:
horizon-free bound on $\int r_T$, $r_T=-\partial_\varepsilon\log(1+E_T)$ (`AveragedContinuation`) — the
bottom of the hierarchy and the target.

**Dilation coordinates.** $(D^fv)(n)=\sum_{j\le n}f(j)v(\lfloor n/j\rfloor)$, $D^f\circ D^g=D^{f*g}$ exactly;
damped prime row $\Lambda_\varepsilon$, unit row $\zeta_\varepsilon$; quotient incidence kernel $\kappa_\varepsilon(n,m)$.

**Prime-pair/level coordinates.** Pronic summation of prefix pairings = Nyman–Beurling
$1/\max(j,k)$ kernel = single scale sum.

**Vocabulary.** Admission (finite named norm + quantifiers); continuation (propagation with a stated
bound); compensation (bound on a combined signed expression); observation (map + indistinguishability
class); stability (quantitative, in the receiver norm); selectivity (proved reason it fails for a model).

---

## 4. Mechanisms

1. **Master inequality.** $0\le\psi E_T'+\beta'$ ⇒ $\Psi\circ E_T+\beta$ nondecreasing
   (`scaledEnergy_add_budget_le`). Grönwall form $1+E_T(a)\le(1+E_T(c))e^{\beta(c)-\beta(a)}$; Osgood via
   coercivity; superlinear scale $\log(1+\log(1+u))$ allows an extra log loss.
2. **Exact derivative, two faces.** $\partial_\varepsilon E_T=2W_T$ = Markov boundary flux − jump energy −
   forcing; $\int_a^c2W_T=E_T(c)-E_T(a)$. With admitted right end, admission at $a$ ⇔ horizon-free bound
   on $\int_a^c-2W_T$.
3. **Averaged = admission; pointwise strictly stronger.** `averagedContinuation_iff_admits`; cofinal
   averaged budgets ⇔ RH; a family admitted everywhere may have no pointwise budget (spike witness);
   positive-part budgets fail even for bounded horizon-monotone families (ACT-comp); adapted energies
   $H_T\asymp1+E_T$ with signed budgets ⇔ admission.
4. **Tangent-norm subsumption** by Cauchy–Schwarz; averaged tangent norm suffices.
5. **Endpoint and partial deliverable.** Admitted above $\Theta-\tfrac12$ (cleared Mellin law); eight
   continuation forms equivalent (`signedAveragedContinuation_tfae`), all unconditional on
   $(\Theta-\tfrac12,\infty)$ and on the VK band; threshold infimum exactly $\Theta-\tfrac12$.
6. **One admitted damping translates zeros** $\rho\mapsto\rho-\varepsilon$ with multiplicity (cleared Mellin
   identity + $|M(s)|\le C(2(\Re s-\tfrac12))^{-1/2}$); width read only by accumulation.
7. **Both ends paid; escape is an interior bump.** $E_T(\varepsilon)\to\sum1/(n(n+1))\le1$ as $\varepsilon\downarrow0$;
   RH ⇔ no interior bump; one forbidden order of work sign change suffices; global nonnegative work
   is false ($W_1\to-\tfrac12$). The bump lives at $n\gtrsim2^{1/\varepsilon}$.
8. **The sign is an angle.** $W_T=\langle A_\delta,E_\varepsilon\rangle+\int_\delta^\varepsilon K_T$; obstruction = off-diagonal
   anti-correlation; relative tangent stability ⇒ RH; second-tangent control; hierarchy is strict;
   $\iint_{[a,c]^2}K_T=\|A_c-A_a\|_T^2\ge0$ and its horizon-uniform bound ⇔ admission.
9. **Convexity** ⇔ $-\|E_\varepsilon\|^2\le\langle A_\varepsilon,F_\varepsilon\rangle$; $F_\varepsilon$ is the source dilated by
   $\Lambda*\Lambda-\Lambda\log$.
10. **Prime-pair/polar/level coordinates.** Polar terms grow linearly in $T$, so prime-pair cancellation
    must hold to **relative precision $1/T$**; admission ⇔ $C/(T+1)$ cancellation
    (`admits_iff_relative_precision_inv_T_primePair`), unconditional above $\Theta-\tfrac12$ and on VK.
11. **Dilation picture.** Tangent = source dilated by prime powers; work = numerical range of the prime
    dilation at the literal source + polar pairing = correlation with its own window means; Möbius
    content in one dilation. Quotient kernel indefinite (zero diagonal); pronic contraction $j^{-1/2}$ ⇒
    scale sum finite exactly above ½; positive core $Q_\varepsilon(1)\ge0$ whose zero-anchored integral is a
    prime harmonic series ($\log\log T$ debt) while on $[\eta,\varepsilon]$ it is $\le\log\zeta(1+\eta)-\log\zeta(1+\varepsilon)$.
12. **Self-improving identity** $E_T=\langle A,\rho_\varepsilon\rangle-\langle A,D^{\zeta_\varepsilon,\ge2}A\rangle$ with $0\le\rho_\varepsilon\le n$;
    $\|\rho_\varepsilon\|^2=m_0^2E^{\text{maj}}$ (diverges $\le\tfrac12$); single-damping four-way equivalence
    (`singleDamping_admission_tfae`) incl. block energy.
13. **Dilation graph and block energy.** $2Q=M-J$ (edge mass − jump energy); Hardy inequality
    $\|v\|^2\le\frac q{(\sqrt q-1)^2}\sum(v(n)-v(\lfloor n/q\rfloor))^2/(n(n+1))$ ⇒ one-step block energy ⇔ admission.
    Exact pronic dilation blocks $Q_{p(N+1)-1}(D_pu,D_pv)=Q_N(u,v)/p$.
14. **Zero anchor.** Admission at $\varepsilon$ ⇔ bound on $\int_\eta^\varepsilon2W_T$ uniform in $T$ and $\eta$.
15. **Selectivity.** Majorant row $d^{-\varepsilon}$ never admitted $\le\tfrac12$: size-blind arguments are refuted.
16. **Aperture mirror.** Relative-decay transport $\mu(c)\ge\mu(a)e^{-(\beta c-\beta a)}$; fixed positive margins
    impossible (doubly exponential ceiling); vanishing relative steps with strict positivity at every
    stage ⇒ RH; four-way equivalence along unbounded sequences; ceiling-renormalized Lyapunov
    monotonicity; graded negative-floor steps ⇒ `CompensatedWidthFloor σ`.
17. **Aperture shell flux.** $\mu(a)-\mu(b)$ = relaxation energy of the extended old ground state
    $\ge0$; **strictly decreasing** (translation invariance + finite-dimensional BS eigenspaces); RH ⇔
    $\mu>0$ at every aperture, else unique contact. Freezing primes at $\lfloor e^{2a}\rfloor$: drop =
    geometric relaxation + signed new-prime correlation, localized to boundary collars.
    **Threshold ladder** $A_{j+1}=\frac12\log(j+2)$: every step is pure frozen relaxation
    (`riemannHypothesis_iff_sum_frozen_relaxation_le`); collar-defect dominance bounds the shell; every
    frozen-prime family collapses ($\le-\alpha e^c$): unfreezing the shell is indispensable.
18. **Rates.** $Q_a=E_+-E_-$ on the smooth core; `CompensatedWidthFloor σ` ⇔ $\mu\ge-Ce^{2\sigma A}$;
    unconditional `CompensatedWidthFloor (1/2)`; **polar and full $L^2$ ground-energy rates are equal
    unconditionally**; RH ⇔ ground-energy rate 0; in the CCM archimedean **form-domain** normalisation
    the form, polar-form and Birman–Schwinger norm rates **equal the width unconditionally**
    (log weight absorbs the divisor packet density); physical-$L^2$ $E_-$ bounded iff off-line zeros do
    not cluster.
19. **Cutoff is free** given admission (shells telescope into the critical energy).
20. **Iterated compensation.** Affine envelopes need contraction $\theta<1$; sector compensation is only
    leading-order exact; cutoff transitions contract for free; the bounded source term is admission again.
21. **Five faces of the obstruction** (deviation−core, jump−edge mass−polar, Markov, window mean,
    Möbius-factored); on compact positive intervals admission ⇔ bound on any one
    (`obstructingTerms_positive_interval_tfae`). **Stable signed observation** $O_q(v)=v-v(\lfloor\cdot/q\rfloor)$:
    complete, pronic-stable, selective against majorant and parity twin.
22. **Paid vs unpaid.** Scalar first moment uniformly paid; renormalisation neutral; residual has a
    linear cusp from a critical zero — positive work escapes every fixed horizon.
23. **Function-field calibration.** Over $\mathbb F_q[T]$ the centred prefix is exactly constant.
24. **Short/long modulus split.** For every cutoff $D$ the centred divisor prefix is a short sawtooth
    (moduli $\le D$) plus the integral of an integrable **long-modulus Möbius quadrature function**
    whose integer samples count hyperbola incidences, with the harmonic tail kept signed. At $D=\sqrt n$
    the short head has bounded pronic energy for every $\varepsilon\in(0,1)$ (exponent $(1-\varepsilon)/2$):
    **the whole obligation is the long-modulus quadrature.** Incomplete dilation fibres cost at most
    $CD/p$ in the mixed pronic pairing, uniformly in the horizon.

---

## 5. Pillar theorems

1. **Master inequality and transport** (`scaledEnergy_add_budget_le`, `Admits.of_osgoodContinuation`).
2. **Exact derivative** (`hasDerivAt_dampedMobiusEnergy`, `two_mul_signedDampingWork_eq_markov`).
3. **Averaged budget = admission; pointwise strictly stronger** (`averagedContinuation_iff_admits`,
   `riemannHypothesis_iff_cofinal_averagedDampingContinuation`, `exists_admits_everywhere_not_linearContinuation`).
4. **Threshold = width** (`sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half`, `signedAveragedContinuation_tfae`).
5. **Both ends paid; escape is an interior bump** (`tendsto_dampedMobiusEnergy_nhdsGT_zero`, `riemannHypothesis_of_no_interior_bump`).
6. **Relative-precision prime-pair cancellation** (`admits_iff_relative_precision_inv_T_primePair`).
7. **Self-improving identity and block energy** (`singleDamping_admission_tfae`, `admits_majorantEnergy_iff_half_lt`).
8. **Aperture shell flow** (`strictAnti_ccmRestrictedWeilGroundEnergy`, `riemannHypothesis_iff_sum_frozen_relaxation_le`,
   `not_exists_subtrivial_exp_floor_frozenFamily`).
9. **Rate equalities** (`groundEnergyRate_eq_polarGroundEnergyRate`, `formGroundEnergyRate_eq_zetaZeroWidth`,
   `compensatedWidthFloor_half`).
10. **Obstruction faces and stable observation** (`obstructingTerms_positive_interval_tfae`,
    `dilationStepObservation_two_sided_stability`).
11. **Short/long split** (`pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature`, `sum_pmShortModulusSawtooth_sqrt_pronic_le`).

---

## 6. Traps

- **Horizon-dependent budgets transport nothing** (`escapeEnergy`: exact linear identity with
  coefficient $2\log(T+1)$, admitted nowhere below ½).
- **Pointwise budgets are not implied by RH**; the averaged form is equivalent.
- **Tangent norm is strictly harder** (rotating rows: zero work, large tangent).
- **No positivity of the dilation kernel**; use the actual source with its polar correction.
- **Absolute dilation estimates stop at ½** ($\sum j^{-(\varepsilon+1/2)}$).
- **Size-blind arguments are refuted** (majorant row).
- **Deviation terms cannot be bounded in absolute value** in the zero-anchored joint limit.
- **Ratio smallness is not a bound**; **sector energies may not be added** (cross terms carry $m^2$ vs $m$).
- **A scale without coercivity says nothing.**
- **No fixed positive aperture margin**; demand strict positivity at each stage or a graded negative floor.
- **Recovery is not control** (but $O_q$ is both).
- **Compactness on $c_0$ is not a pronic bound.**
- **Integer prefix ≠ real-centred extension** (fractional-part correction, pole tail).
- **Leading-order prime asymptotics cannot settle the sign** (relative precision $1/T$ needed).
- **Frozen-prime operators have no sub-trivial floor**; the shell must be unfrozen.
- **Form-domain rate equality is not the $L^2$ rate equality**; physical $L^2$ needs non-clustering.

---

## 7. Open problems

1. **Transport below one half.** A horizon-free bound on any of the eight continuation forms on a
   fixed $[a,\tfrac12]$, $a<\tfrac12$ (a zero-free strip), then cofinally (RH).
2. **The signed deviation** on a fixed positive interval (any of the four faces), with its sign —
   absolute estimates are refuted by the majorant, sign-blind ones by the parity twin.
3. **Tangent anti-correlation** below ½ beyond the double-integral identity, controlling accumulated
   cross terms of a partition.
4. **Relative-precision prime-pair cancellation** at a fixed damping below ½: which prime-pair
   information, at which height?
5. **A contraction for sector compensation** for the actual Möbius row below ½.
6. **Long-modulus quadrature.** Bound the pronic energy of the long-modulus Möbius quadrature at
   one fixed $\varepsilon<\tfrac12$ (the square-root head is already paid).
7. **Quantitative prime-shell control.** Bound the signed new-prime correlation along ground states to
   exclude contact or give a graded floor (respecting the doubly exponential ceiling); the threshold
   ladder reduces RH to summed frozen relaxation.
8. **$L^2$ rate equality.** Polar = full is proved; form-domain rates = width is proved; whether the
   physical-$L^2$ rate equals the width without a non-clustering input.
9. **Selectivity against sign-reading models** (shifted pair, Beurling with off-line zero, Liouville twist).
10. **Function-field defect.** Quantify the deviation of the number-field centred prefix from a constant
   at a fixed damping.

---

## 8. Tools to build

A horizon-free signed-deviation bound below ½; a long-modulus quadrature estimate; a source-derived
prime-shell bound; a contraction for sector compensation.

---

## 9. Principles

1. Exact source before closure; no source selected from the zeros.
2. Keep signs until their cancellation is paid.
3. Uniformity is part of the theorem ($\forall\varepsilon\,\exists C_\varepsilon\,\forall T$).
4. State the demand at the bottom of its hierarchy (averaged).
5. Recovery ≠ control; preserve the required norm ($H^1\ne L^2$; $c_0\ne$ pronic).
6. Test selectivity against majorant, parity twin, shifted pairs, coherent blocks.
7. Pay both ends of a limit (origin, infinity, fractional parts, polar constraints).
8. Endpoint success ≠ bridge success; a failed continuation must yield a sharp survivor.
