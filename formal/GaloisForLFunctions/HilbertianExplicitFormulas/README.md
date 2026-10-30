# Hilbertian Explicit Formulas (HEF)

Namespace `GaloisForLFunctions.HilbertianExplicitFormulas`; umbrella `HilbertianExplicitFormulas.lean`.

**Question.** Weil's explicit formula evaluates zero sums $\sum_\rho m_\rho\,h(\rho)$ with a *holomorphic* weight
$h$. Its quadratic form pairs a transform at a zero with the transform at the line-reflected zero
$\rho^*=1-\bar\rho$. The Hilbert norm $\sum_\rho m_\rho|F(\rho)|^2$ evaluates a transform and its conjugate at the
*same* zero. RH is the statement that the two agree. Which zero sums can arithmetic evaluate, which
same-point sums lie beyond every explicit formula and by how much, and what would an arithmetic
identity for a same-point sum have to look like, at a precision where a quantum decides?

HEF is the theory of **same-point zero sums**: their explicit-formula image, their quantized carriers,
their calibration over $\mathbb F_q$ and their selectivity battery. Every statement is unconditional; RH
appears only inside equivalences.

---

## 1. Place in the research

The corpus has two quadratic functionals on one zero divisor and an exact identity between them:

$$S(F)=\sum_\rho m_\rho|F(z_\rho)|^2,\qquad W(F)=\sum_\rho m_\rho F(z_\rho)\overline{F(\bar z_\rho)},\qquad
S(F)=W(F)+\tfrac12\sum_\rho m_\rho|F(z_\rho)-F(\bar z_\rho)|^2,$$

in spectral coordinates $z_\rho=-i(\rho-\tfrac12)$, where line reflection is $z\mapsto\bar z$. The explicit
formula computes $W$; nothing computes $S$ from primes. HEF asks for the missing side and states
precisely what stands in the way.

| Programme | Interface |
|---|---|
| ArithmeticPolarization (APol) | The two forms $\Re W=D-\Delta$; RH = coincidence = Hecke invariance of $D$. HEF proves that no explicit formula reaches past $W$ and studies quantized carriers of $\Delta$ |
| ConjugateDiagonalGeometry (CDG) | $D$ computed in the limit from theta-prefix source currents; depth moments. HEF supplies the explicit-image theorem and the quantum side |
| ArithmeticElectrostatics (AES) | $\log\lvert\xi\rvert$ potential, Laplacian = collided form. HEF's harmonic/subharmonic split of zero weights is its linear shadow |
| RHTower horizontal collision (HC) | Collision charge $O(T)\in2\mathbb N$, RH ⇔ $O<2$; two-prime Cesàro carrier; holomorphic pencil growth dichotomy; resolvent line-reflection defect. HEF generalizes the carrier laws and calibrates them |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | Weil's form as a Krein form, its index. HEF is the comparison of that Krein form with the Hilbert norm on the same carrier |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Curve data, Frobenius reflection defect, golden datum, Rosati = orbit Hodge index. HEF uses them for the $\mathbb F_q$ calibration |
| CACT, CAF, RAPT ($\Sigma_1$) | Conductor floors, residuals, reserves of the complete Weil matrix. HEF does not replace them; it addresses the coalescence wall, not the overlap wall |
| `HTGeometry` coalescence modules | Pairwise-first coalescence law, exchange no-go, even-reader jet loss: the design constraints of §6 |

---

## 2. Why

**Two forms, one divisor.** Every arithmetic identity for the zeros of $\zeta$ comes from the argument
principle applied to $\xi'/\xi$ times a holomorphic weight. Its output is a linear statistic
$\sum_\rho m_\rho h(\rho)$ with $h$ holomorphic. Weil's quadratic form is such a statistic, with $h=F\cdot F^\#$
where $F^\#(z)=\overline{F(\bar z)}$. The Hilbert norm $S$ needs the non-holomorphic weight $|F|^2$. On the
critical line the two weights coincide; off it they differ by $|F(z)-F(\bar z)|^2$.

**The explicit image is rigid.** A holomorphic weight is determined by its values on the real line.
Hence any explicit formula that is correct for critical configurations *is* the Weil form, and its
same-point error at an off-line pair is exactly the line-reflection defect (§4.1). No explicit formula
reaches past Weil's form: the same-point problem is not a problem of finding a better test function.

**Mean squares are same-point sums.** Parseval converts a linear statistic into a quadratic one:
$\frac1N\sum_n|\sum_\rho m_\rho c(\rho)^n|^2$ tends to a sum over coincidence classes of the clock values. When
the clock is a pure phase this is a same-point sum, and its excess over the diagonal is an integer:
the collision charge $O=\sum_\rho m_\rho(H_\rho-m_\rho)\in2\mathbb N$, a **quantum**. RH is $O<2$. When the clock is
holomorphic — the only kind an explicit formula produces — every off-line pair contributes one
exponentially growing mode, and the excess is $0$ or $\infty$ (§4.4). The quantum lives only on the
same-point side.

**Why a quantum matters.** Positivity criteria are statements at zero margin. A quantized carrier turns
RH into an $O(1)$ statement with margin $2$, and the census of critical zeros into an $N$-normalized
statement: $N_0\ge N-O$, so $O\le N/4$ gives $75\%$. A same-point identity whose error is quantized would
attack both. HEF builds the theory such an identity must live in.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Reflection configuration | finite multiset $Z\subset\mathbb C$ with positive multiplicities, closed under $s\mapsto 1-\bar s$ and $s\mapsto\bar s$ | `ReflectionConfiguration`, `IsCritical`, `total`, `lineMass` |
| Spectral point | $z_\rho=-i(\rho-\tfrac12)$; critical ⇔ $z_\rho\in\mathbb R$; depth $\delta_\rho=\Re\rho-\tfrac12=-\Im z_\rho$ | `RHTower.xiSpectralPoint` |
| Same-point form $S$ | $\sum m_\rho\lvert F(z_\rho)\rvert^2$; Hilbert norm of the evaluation vector | `RHTower.xiWeilEvaluationLp` |
| Weil form $W$ | $\sum m_\rho F(z_\rho)\overline{F(\bar z_\rho)}$; Krein form $\Re\langle Jv,v\rangle$ | `RHTower.xiWeilPolarization`, `xiWeilHilbertQuadratic` |
| Line-reflection defect $\Delta$ | $\tfrac12\sum m_\rho\lvert F(z_\rho)-F(\bar z_\rho)\rvert^2=S-W$ | `RHTower.norm_sq_xiResolvent_reflectionDefect` |
| Explicit statistic | $\sum m_\rho h(z_\rho)$ with $h$ entire; Weil weight $F\cdot F^\#$ | `explicitStatistic`, `weilWeight`, `samePointForm`, `lineReflectionDefect` |
| Clock | function $c$ of the zero; *holomorphic* $c_\lambda(s)=e^{\lambda(s-1/2)}$; *ordinate* (same-point) $c_\lambda(s)c_\lambda(1-\bar s)=e^{2i\lambda\Im s}$; *modulus* $\lvert c_\lambda(s)\rvert^2=e^{2\lambda(\Re s-1/2)}$ | `holomorphicClock`, `ordinateClock` |
| Pencil, Cesàro excess | $P(n)=\sum m_\rho c(\rho)^n$; $\frac1N\sum_{n<N}\lvert P(n)\rvert^2-\sum m_\rho^2$ | `cesaroMeanSquare`, `CesaroBounded`, `aliasCharge`, `NonResonant` |
| Collision charge | $O=\sum_\rho m_\rho(H_\rho-m_\rho)$, $H_\rho$ = multiplicity at the ordinate of $\rho$ | `ReflectionConfiguration.collisionCharge`; for $\xi$: `RHTower.xiHorizontalCollisionCharge` |
| Quantum | least positive value of a carrier's excess on configurations with an off-line zero | — |
| Curve datum | normalized Frobenius eigenvalues $\beta_i$ with conjugation and functional-equation symmetry; ordinate $\beta/\lvert\beta\rvert$ | `ArithmeticCastelnuovoSeveri.CurveDatum`, `curveOrdinate`, `curveCollisionCharge` |
| Resolvent norms | $S(s)=\sum m_\rho\lvert s-\rho\rvert^{-2}$, $E(s)=\sum m_\rho\Re\frac1{s-\rho}$, defect $D(s)$, depth moments $M_{2k}$ | `samePointResolvent`, `explicitResolvent`, `resolventDefect`, `depthMoment` |
| Signed divisor | multiplicities in $\mathbb R$ | `signedSamePointForm`, `isolatingPolynomial` |

**Words.** *Same-point*: a weight evaluated at one zero through both $z$ and $\bar z$ (holomorphic ×
antiholomorphic). *Reflection-paired*: a holomorphic weight, pairing $z$ with its line reflection.
*Explicit image*: the set of zero sums an explicit formula evaluates. *Calibrated on the line*: correct
on every critical configuration. *Quantized*: integer-valued on every configuration. *Source-realizable*:
produced by an explicit formula from prime and archimedean data. *Effective*: all multiplicities
positive.

---

## 4. Mechanisms

1. **Calibration rigidity.** An entire weight $h$ with $h=|F|^2$ on $\mathbb R$ equals $F\cdot F^\#$ (identity
   theorem; `eq_weilWeight_of_calibrated`). So every line-calibrated explicit statistic is the Weil form,
   and at a pair $\{z,\bar z\}$ it misses the same-point value by exactly $|F(z)-F(\bar z)|^2$
   (`samePoint_sub_explicit_pair`). An explicit statistic correct at one off-line pair forces $F$ to be
   blind there (`blind_of_explicit_eq_samePoint`); one correct on every pair forces $F$ constant
   (`const_of_explicit_eq_samePoint_everywhere`).
2. **Polarization identity.** $S=W+\Delta$, $\Delta\ge0$, on finite configurations
   (`samePointForm_sub_explicitStatistic`, `explicitStatistic_eq_samePointForm_iff`) and on the Xi divisor
   (`norm_sq_sub_explicit_eq_half_reflectionDefect`, `explicit_eq_norm_sq_iff_lineConj_fixed`).
3. **Parseval with classes.** The Cesàro mean square of a pencil with unimodular clocks tends to the sum
   over clock classes of $m_\rho m_{\rho'}$ (`RHTower.tendsto_tsum_pencil_cesaro_norm_sq`).
4. **Dominant modes.** With positive multiplicities a clock of modulus $>1$ makes the Cesàro mean square
   unbounded; clocks of modulus $\le1$ keep it bounded (`not_cesaroBounded_of_one_lt_norm`,
   `cesaroBounded_of_norm_le_one`).
5. **Clock classification.** A holomorphic clock $e^{\lambda(s-1/2)}$ has modulus
   $e^{(\Re\lambda)\delta-(\Im\lambda)\gamma}$; the four points of a quartet realize all four sign patterns, so the
   pencil is bounded exactly when $\Re\lambda\cdot\delta_\rho=\Im\lambda\cdot\gamma_\rho=0$ at every point
   (`cesaroBounded_holomorphicClock_iff`). The ordinate clock is the holomorphic clock at $s$ times the one
   at $1-\bar s$ (`holomorphicClock_mul_lineReflect`); it is unimodular, and its mean square tends to
   $\sum m^2+O+A_t$ (`tendsto_cesaro_ordinateClock`, `classPairSum_eq`).
6. **Resolvent formula.** For $\Re s>\tfrac12$ and $s\notin Z$: $(\sigma-\tfrac12)S(s)=E(s)+D(s)$ with
   $D(s)=\sum m_\rho\,2(\sigma-\tfrac12)(\beta_\rho-\tfrac12)^2/(|s-\rho|^2|s-\rho^*|^2)$, from the pair identity
   $|s-\rho^*|^2-|s-\rho|^2=(2\sigma-1)(2\beta-1)$ (`pair_depth_resolvent`, `sub_mul_samePointResolvent_eq`). If
   every $\Re\rho\le\tfrac12+w$ then $(\sigma-\tfrac12-w)S\le E\le(\sigma-\tfrac12)S$
   (`sub_width_mul_samePointResolvent_le`, `explicitResolvent_le`). Along a vertical line
   $\int D\,dt=\pi\sum m_\rho d_\rho^2/(u^2-d_\rho^2)=\pi\sum_{k\ge1}M_{2k}u^{-2k}$
   (`integral_resolventDefect_vertical`).
7. **$\mathbb F_q$ calibration.** On a curve datum line reflection is $\beta\mapsto1/\bar\beta$, which keeps the argument
   (`curveOrdinate_reflPerm`); off-unitary eigenvalues collide with their reflections
   (`two_le_curveCollisionCharge`). The Lefschetz pencil $\sum\beta_i^n$ is the holomorphic clock
   (`lefschetzPencil_eq_powerSum`). Calibration rigidity transports to the circle through $w=e^{iz}$
   (`eq_rosatiWeight_of_circleCalibrated`).
8. **Effectivity.** The Lagrange polynomial vanishing at all other points isolates one multiplicity
   (`signedSamePointForm_isolating`).

---

## 5. Pillar theorems

1. **Calibration rigidity**: the explicit image of the same-point problem is the Weil form
   (`eq_weilWeight_of_calibrated`, `samePointForm_sub_explicitStatistic`,
   `tsum_explicit_eq_xiWeilPolarization`, `const_of_explicit_eq_samePoint_everywhere`).
2. **Clock classification**: holomorphic clocks are bounded exactly where they read nothing; for a real
   frequency, exactly below the quantum, so their excess is $0$ or $\infty$
   (`cesaroBounded_holomorphicClock_iff`, `cesaroBounded_holomorphicClock_real_iff`,
   `not_cesaroBounded_holomorphicClock_of_im_ne_zero`). The ordinate clock reads the collision charge at
   every non-resonant frequency (`tendsto_cesaro_ordinateClock_sub_diag_of_nonResonant`).
3. **Quantum law**: the collision charge is even, vanishes exactly on critical configurations and is
   $\ge2$ otherwise; $N\le N_0+O$, so $O\le cN$ gives the proportion $1-c$ (`even_collisionCharge`,
   `isCritical_tfae`, `total_le_lineMass_add_collisionCharge`, `one_sub_mul_total_le_lineMass`).
4. **Resolvent Hilbertian formula**: $(\sigma-\tfrac12)S=E+D$, $D\ge0$, $D=0$ ⇔ critical; width sandwich;
   depth-moment series (`sub_mul_samePointResolvent_eq`, `resolventDefect_eq_zero_iff`,
   `explicitResolvent_eq_iff`, `integral_resolventDefect_vertical`).
5. **$\mathbb F_q$ calibration**: unitary ⇔ charge $=0$ ⇔ charge $<2$ ⇔ bounded Lefschetz pencil; the charge is
   even; the golden datum has charge exactly $2$; every circle-calibrated explicit formula is the Rosati
   pairing (`unitary_tfae`, `even_curveCollisionCharge`,
   `cesaroBounded_lefschetz_iff_curveCollisionCharge_lt_two`, `goldenDatum_curveCollisionCharge`,
   `explicit_eq_rosatiPairing`).
6. **Effectivity**: same-point positivity ⇔ effectivity; a pole makes the form indefinite
   (`signedSamePointForm_nonneg_iff`, `exists_signedSamePointForm_neg`).

| Module | Content |
|---|---|
| `TheExplicitImageIsTheWeilForm` | calibration rigidity; finite and Xi polarization identities |
| `TheSamePointQuantumOfAReflectionConfiguration` | reflection configurations, collision charge, quantum law, census |
| `HolomorphicClocksCarryNoQuantum` | dominant modes, clock classification, ordinate Parseval |
| `TheResolventHilbertianExplicitFormula` | resolvent formula, sandwich, vertical integral, depth moments |
| `TheFiniteFieldCalibration` | circle rigidity, curve collision charge, Lefschetz pencil, golden datum |
| `SamePointPositivityIsEffectivity` | signed divisors |

---

## 6. Principles

From the corpus no-gos on collision observables:

1. Orientation is carried from the source, never reconstructed downstream (`PairwiseFirstCoalescenceLaw`).
2. Exchange symmetry is broken by data beyond an unlabelled pair (`XiHorizontalCollisionExchangeOrientationNoGo`).
3. Collision weights are linear in multiplicity (`XiHeatCassiniWoldOrbitChargeLowerSemicontinuousCollisionNoGo`).
4. No even reader at an anti-phase collision (`evenReader_firstJet_zero`).
5. Bounds are stated at the quantum: absolute for RH, $N$-normalized for the census.

From HEF itself:

6. A holomorphic weight is decided on the line; its off-line value is never new information.
7. Same-point information enters only through a non-holomorphic operation: a mean square, a modulus,
   a Laplacian, a conjugation of the divisor.
8. Identities first, sign last; calibrate over $\mathbb F_q$; test on the battery.

---

## 7. Traps

| Trap | Truth |
|---|---|
| A better test function makes the explicit formula compute $S$ | Line calibration pins every holomorphic weight to $F F^\#$ |
| An explicit formula correct at one off-line pair is progress | It forces the test to be blind to that pair |
| Mean squares of explicit formulas are same-point sums | Only with unimodular clocks; holomorphic clocks weight by $e^{2n\lambda\delta}$ and diverge off the line |
| A holomorphic clock with complex frequency avoids growth | Conjugation symmetry supplies the mirrored ordinate; $\Im\lambda\ne0$ grows already on critical configurations |
| Normalized bounds $O=o(N)$ give RH | They give censuses; RH needs the absolute bound $<2$ |
| A positive same-point form is a Hilbert structure for every L-function | Signed divisors (twins with poles) make it indefinite |
| Computing $S$ (CDG source currents) bounds $\Delta$ | It computes the collided side only; the comparison is the problem |

---

## 8. Questions

1. **Explicit image.** Which zero sums does an explicit formula evaluate, and what is the exact error of
   the best explicit approximation to a same-point sum? *Answer:* a line-calibrated explicit formula is
   the Weil form, and its error is the line-reflection defect, pair by pair (pillar 1).
2. **Quantized carriers.** Which clocks give integer-valued excesses, and which are source-realizable?
   *Answer for exponential clocks:* holomorphic clocks have excess $0$ or $\infty$; the ordinate clock has
   excess $O+A_t$, integer-valued, equal to $O$ at non-resonant frequencies, and it is antiholomorphic in
   one factor (pillar 2).
3. **First same-point identity.** For one nontrivial carrier, the same-point sum as the reflection-paired
   sum plus a source term. *Answer for the resolvent carrier on finite configurations:*
   $(\sigma-\tfrac12)S=E+D$ with $D$ a weighted second depth moment (pillar 4). For the zeta divisor
   $E=\Re\,\xi'/\xi$ (`RHTower.re_logDeriv_xi_eq_tsum`), a prime sum for $\sigma>1$. Open: the identity on the full
   divisor, and $D$ as a prime-side quantity.
4. **Census constant.** An $N$-normalized bound $O\le cN$ with $c<1/4$. Open; pillar 3 is the reduction.
5. **$\mathbb F_q$.** Every pillar has its curve form; there Weil's theorem makes the charge $0$, the golden
   datum is the extremal fake at charge $2$ (pillar 5).
6. **Selectivity.** Critical configurations pass every pillar; configurations with an off-line point fail
   with charge $\ge2$ and positive defect; signed divisors fail effectivity; the golden datum fails at
   exactly the quantum.

---

## 9. Tools to develop

- Calibration rigidity for entire weights, on finite configurations, on the Xi divisor and on curve data.
- A clock calculus: modulus, ordinate and holomorphic clocks; dominant-mode lower bounds; Parseval with
  classes.
- Quantum laws for finite reflection configurations: parity, critical vanishing, census inequality.
- The resolvent Hilbertian formula and its depth-moment expansion.
- An $\mathbb F_q$ calibration layer on `CurveDatum`: collision charge, Lefschetz pencil, golden datum.
- Battery models: planted quartets, signed divisors, golden datum.

---

## 10. Open research topics

1. **A non-holomorphic producer.** An arithmetic identity for one same-point sum whose error is
   quantized: Laplacian (Riesz) formulas, two-variable kernels, conjugation of the divisor.
2. **Prime-side bounds for the defect at $L\asymp\log T$** (CDG's open question) in quantized form.
3. **Census through same-point carriers**: $O(T)\le cN(T)$ with $c<1/4$.
4. **Source-realizable unimodular clocks.** Products $c(\rho)c(\rho^*)$ are unimodular but antiholomorphic;
   is there any source-realizable family whose mean square reads the collision charge with finite loss?
5. **Depth moments from resolvent data**: the resolvent formula on the full Xi divisor (summability of
   $S$, symmetrization of the tsum), and which part of the vertical resolvent defect is arithmetic.

---

## 11. Success criteria and contribution standard

**Success.** An arithmetic same-point identity on one nontrivial carrier with a quantized error, or a
theorem that no producer of a stated class can supply one; in either case reducing over $\mathbb F_q$ to
Weil's theorem and failing on the battery for a stated reason.

A contribution:

1. is unconditional, with every input discharged in Lean;
2. says which side it lives on: explicit (holomorphic), same-point, or the comparison;
3. states its precision: absolute (at the quantum) or $N$-normalized;
4. reports what it gives on the battery (critical configurations, planted quartets, signed divisors,
   golden datum) and over $\mathbb F_q$;
5. respects the principles of §6, or proves that the principle fails for its carrier;
6. records the positive survivor of every negative result.

A reformulation of RH as another equality of two forms is not a contribution.
