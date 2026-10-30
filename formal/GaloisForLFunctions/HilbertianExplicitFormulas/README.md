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
| Reflection configuration | finite multiset $Z\subset\mathbb C$ with positive multiplicities, closed under $s\mapsto 1-\bar s$ (and $s\mapsto\bar s$) | — |
| Spectral point | $z_\rho=-i(\rho-\tfrac12)$; critical ⇔ $z_\rho\in\mathbb R$; depth $\delta_\rho=\Re\rho-\tfrac12=-\Im z_\rho$ | `RHTower.xiSpectralPoint` |
| Same-point form $S$ | $\sum m_\rho\lvert F(z_\rho)\rvert^2$; Hilbert norm of the evaluation vector | `RHTower.xiWeilEvaluationLp` |
| Weil form $W$ | $\sum m_\rho F(z_\rho)\overline{F(\bar z_\rho)}$; Krein form $\Re\langle Jv,v\rangle$ | `RHTower.xiWeilPolarization`, `xiWeilHilbertQuadratic` |
| Line-reflection defect $\Delta$ | $\tfrac12\sum m_\rho\lvert F(z_\rho)-F(\bar z_\rho)\rvert^2=S-W$ | `RHTower.norm_sq_xiResolvent_reflectionDefect` |
| Explicit statistic | $\sum m_\rho h(z_\rho)$ with $h$ entire | — |
| Clock | function $c$ of the zero; *holomorphic* $c_\lambda(s)=e^{\lambda(s-1/2)}$; *ordinate* (same-point) $c_\lambda(s)c_\lambda(1-\bar s)=e^{2i\lambda\Im s}$; *modulus* $\lvert c_\lambda(s)\rvert^2=e^{2\lambda(\Re s-1/2)}$ | `RHTower.burnolPrimeCharacter` |
| Pencil, Cesàro excess | $P(n)=\sum m_\rho c(\rho)^n$; $\frac1N\sum_{n<N}\lvert P(n)\rvert^2-\sum m_\rho^2$ | `RHTower.finiteExponentialPencil` |
| Collision charge | $O=\sum_\rho m_\rho(H_\rho-m_\rho)$, $H_\rho$ = multiplicity at the ordinate of $\rho$ | `RHTower.xiHorizontalCollisionCharge` |
| Quantum | least positive value of a carrier's excess on configurations with an off-line zero | — |
| Curve datum | normalized Frobenius eigenvalues $\beta_i$ with conjugation and functional-equation symmetry | `ArithmeticCastelnuovoSeveri.CurveDatum` |

**Words.** *Same-point*: a weight evaluated at one zero through both $z$ and $\bar z$ (holomorphic ×
antiholomorphic). *Reflection-paired*: a holomorphic weight, pairing $z$ with its line reflection.
*Explicit image*: the set of zero sums an explicit formula evaluates. *Calibrated on the line*: correct
on every critical configuration. *Quantized*: integer-valued on every configuration. *Source-realizable*:
produced by an explicit formula from prime and archimedean data. *Effective*: all multiplicities
positive.

---

## 4. Mechanisms

1. **Calibration rigidity.** An entire weight $h$ with $h=|F|^2$ on $\mathbb R$ equals $F\cdot F^\#$ (identity
   theorem). So every line-calibrated explicit statistic is the Weil form, and at a pair $\{z,\bar z\}$ it
   misses the same-point value by $|F(z)-F(\bar z)|^2$. An explicit statistic correct at one off-line pair
   forces $F$ to be blind there; one correct on every configuration forces $F$ constant.
2. **Polarization identity.** $S=W+\Delta$, $\Delta\ge0$, pairwise and summed; RH ⇔ $\Delta\equiv0$.
3. **Parseval.** The Cesàro mean square of a pencil with unimodular clocks tends to the sum over clock
   classes of the squared class multiplicity.
4. **Dominant modes.** With positive multiplicities, the top-modulus modes of a pencil cannot cancel in
   mean square; a pencil whose maximal clock modulus exceeds $1$ has unbounded Cesàro mean square.
5. **Clock classification.** A holomorphic clock $e^{\lambda(s-1/2)}$ has modulus
   $e^{(\Re\lambda)\delta-(\Im\lambda)\gamma}$; on a reflection-and-conjugation-closed configuration the four points of a
   quartet realize all four signs, so the pencil is bounded only if $\Re\lambda\cdot\delta_\rho=\Im\lambda\cdot\gamma_\rho=0$ for every
   zero. The ordinate clock is unimodular; its excess is the collision charge plus aliasing.
6. **Resolvent formula.** For $\Re s>\tfrac12$:
   $(\sigma-\tfrac12)\sum m_\rho|s-\rho|^{-2}=\sum m_\rho\Re\frac1{s-\rho}+\sum m_\rho(\beta_\rho-\tfrac12)|s-\rho|^{-2}$, and the last term is a
   nonnegative pair sum vanishing exactly on critical configurations. Its vertical integral is a
   generating function of the even depth moments.
7. **$\mathbb F_q$ calibration.** On a curve datum the Frobenius line reflection is $\beta\mapsto1/\bar\beta$, which keeps
   the argument; off-unitary eigenvalues collide with their reflections, so the charge is $0$ or $\ge2$,
   and the golden datum realizes $2$. The Lefschetz pencil is the holomorphic clock; it is bounded
   exactly on unitary data.
8. **Effectivity.** The same-point form of a signed divisor is indefinite as soon as one multiplicity is
   negative. Hilbertian identities need effective divisors; twins with poles fail them.

---

## 5. Pillar theorems

1. **Calibration rigidity**: the explicit image of the same-point problem is the Weil form.
2. **Clock classification**: no holomorphic exponential clock carries a finite quantum on reflection
   configurations; the ordinate clock carries the collision charge.
3. **Quantum law**: on effective reflection configurations the collision charge is even, vanishes
   exactly on critical configurations, and is $\ge2$ otherwise; $N-N_0\le O$.
4. **Resolvent Hilbertian formula** with a nonnegative, exactly critical-vanishing defect.
5. **$\mathbb F_q$ calibration**: unitary ⇔ charge $<2$ ⇔ bounded Lefschetz pencil; golden datum has charge $2$;
   the unique line-calibrated explicit formula is Weil's.
6. **Effectivity**: same-point positivity ⇔ effectivity of the divisor.

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
   the best explicit approximation to a same-point sum? (Answered by calibration rigidity.)
2. **Quantized carriers.** Which clocks give integer-valued excesses on all configurations, and which of
   them are source-realizable? (Holomorphic exponential clocks: none.)
3. **First same-point identity.** For one nontrivial carrier, an identity expressing the same-point sum as
   the reflection-paired sum plus a source term.
4. **Census constant.** An $N$-normalized bound on that source term with constant $<1/4$.
5. **$\mathbb F_q$.** Does every HEF statement reduce to Weil's theorem over $\mathbb F_q$, with the golden datum as
   the extremal fake?
6. **Selectivity.** Which statements fail on Beurling systems with off-line zeros, on signed twins and on
   the golden datum, and for which stated reason?

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
5. **Depth moments from resolvent data**: which part of the vertical resolvent defect is arithmetic.

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
