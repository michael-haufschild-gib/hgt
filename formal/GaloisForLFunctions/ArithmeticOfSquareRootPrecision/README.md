# Arithmetic of Square-Root Precision (ASRP)

Namespace `GaloisForLFunctions.ArithmeticOfSquareRootPrecision`; umbrella `ArithmeticOfSquareRootPrecision.lean`.

**Question.** The corpus has reduced RH to one count, $\psi(x)-x=O(\sqrt x\log^2x)$, and has shown
that no estimate stable under relative error $o(1)$ can produce it. Which statements about the
prime-side source can carry information at square-root precision at all? Which identities and
integers over $\mathbb Z$ carry it, how much of it can integrality extract, and where exactly is it
lost in the classical methods?

ASRP is the arithmetic of **precision**. Basic object: a *weight* $a:\mathbb N\to\mathbb R$ (a
prime-side source; $\Lambda$ is the arithmetic one) with partial sums $A(x)=\sum_{n\le x}a(n)$.
Basic invariant: the **precision class** of a statement, the set of perturbations of the weight it
survives. Basic integer: the **horizon period** $d_N=\operatorname{lcm}(1,\dots,N)$, whose log-order
is $\psi(N)$. Everything is unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

Every route in the corpus ends at the same wall: a deciding input must be **parity-breaking**
(fail for the Liouville twin $\lambda\Lambda$), **square-root precise** (fail for
$\Lambda+\varepsilon n^{-\eta}$, $\eta<\tfrac12$), and of **unbounded aperture** (not determined by a
finite window). The programmes that met this wall stated it as a principle or a test battery. ASRP
makes it a theory: precision classes, the battery as a classification, and the integrality face of
the count. It sits one level below the index theory of the Weil kernel, where signs come from
integers.

| Programme | Interface |
|---|---|
| ArithmeticEffectivityTheory | Log-torsion $\psi(N)=\log\lvert\mathbb Z/d_N\rvert$, Nair's floor (`log_inv_integral_le_psi`); ASRP proves the floor is attained and computes its exact precision |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | The global law is the one-sided count (`global_law_count`); precision and parity principles; Stepanov compressions. ASRP supplies the precision calculus those principles presuppose, and proves that *each* half of the count is RH |
| SelectiveMultiscaleArithmeticPositivity | Precision rigidity of tower positivity (`not_towerPositive_and_perturbed`); ASRP proves the count-level analogue with the sharp threshold |
| ArithmeticCorrelationGeometry, BiarithmeticGaugeGeometry | The gauge torus; ASRP computes the count's stabilizer in the sign-gauge group |
| ArithmeticCorrespondencePositivity | "On nonnegative tests $\zeta$ is the worst twin"; its count-level form is the monotonicity of the lower half |
| SquareRootThreshold | The zero width $\Theta$; ASRP identifies it with the precision exponent and with the integrality exponent |
| ArithmeticCastelnuovoSeveri, ArithmeticLorentzianGeometry | Curve data, golden datum, one-sided power-sum bounds (`norm_le_of_re_sum_pow_le`); ASRP's calibration of precision exponents |
| ConjugateDiagonalGeometry, RenormalizedArithmeticPotentialTheory, ArithmeticIntersectionTheory | The Hecke defect, the covariant regulator, torsion orbits: targets whose precision class is open (§9) |
| `RHTower` | Von Koch, the exponent law $\Theta=$ order of $\psi(x)-x$ (`chebyshevPsi_sub_exponent_law`), Littlewood, PNT, Guth–Maynard short intervals |
| `HTGeometry` | Real zeros of exponential polynomials (`card_lt_of_expPoly_eq_zero`) |

---

## 2. Why

**Over $\mathbb F_q$ the sign is a count, and the count is an integer.** For a curve,
$N_m=q^m+1-q^{m/2}\sum_i\beta_i^m$ counts a finite set; Weil is $|N_m-q^m-1|\le2g\,q^{m/2}$; Stepanov
proves the one-sided half by integrality, with an auxiliary polynomial whose coefficients contain
$x^q$, invisible to differentiation and equal to $x$ on $\mathbb F_q$.

**Over $\mathbb Z$ the integers are log-orders.** $\psi(N)=\log d_N$ exactly, and integrality gives
$d_{n+1}\int_0^1P\in\mathbb Z$ for $P\in\mathbb Z[x]$ of degree $\le n$. The classical extraction
(Chebyshev, Nair) reaches linear precision only. The question the review of 29 October calls central
is whether integrality over $\mathbb Z$ reaches any precision beyond linear.

**Why precision is the right invariant.** Three facts organise everything, and each is a theorem
here.

1. The count has a precision class: it survives exactly the perturbations with partial sums
   $O(\sqrt x\log^2x)$. Every implication into the count must respect that class.
2. The classical theorems (PNT, Guth–Maynard, every error law weaker than square root) hold for
   $\Lambda+\varepsilon n^{-\eta}$ with $0<\eta<\tfrac12$, which never satisfies the count. None can decide.
3. Identities have precision class $\{0\}$: the Chebyshev identity $\sum_d\Lambda(d)\lfloor n/d\rfloor=\log n!$
   determines $\Lambda$, and the integrality floor $\min^+\int_0^1P=1/d_{n+1}$ is attained. Precision is
   not missing from the arithmetic of $\mathbb Z$. It is lost when estimates are extracted from
   identities, and the loss is located: Möbius inversion, and the analytic ceiling of auxiliaries.

---

## 3. Objects and language

| Over $\mathbb F_q$ | ASRP object | Over $\mathbb Z$ | Lean |
|---|---|---|---|
| point count $N_m$ | weight, partial sum | $a:\mathbb N\to\mathbb R$, $A(x)=\sum_{n\le x}a(n)$ | `partialSum` |
| $\lvert N_m-q^m-1\rvert\le Cq^{m/2}$ | the count and its halves | $A(x)-x=O(\sqrt x\log^2x)$ | `Count`, `UpperCount`, `LowerCount` |
| error $O(q^{m\theta})$ | precision class | $\{\delta:\sum_{n\le x}\delta(n)=O(\varphi)\}$ | `PrecisionClass`, `sqrtClass` |
| $\tfrac12+\max\log\lvert\beta\rvert/\log q$ | precision exponent | order of $A(x)-x$ | `precisionExponent`, `CountAtPrecision` |
| fake data (golden) | battery move | $\lambda\Lambda$, $c\Lambda$, $\Lambda+\varepsilon n^{-\eta}$, flips | `liouvilleWeight`, `powerWeight`, `towerWeight`, `signGauge` |
| $x^q-x$ | horizon period | $d_N=\operatorname{lcm}(1..N)$, $\log d_N=\psi(N)$ | `Nat.lcmUpto` |
| Stepanov auxiliary | Nair functional | $P\mapsto\int_0^1P=D_P(1)$ | `nairIntegral` |
| integrality of $N_m$ | integrality lattice | $\{\int_0^1P\}=d_{n+1}^{-1}\mathbb Z$ | `nairLattice_eq` |
| — | Siegel / Liouville halves | small positive integrals exist / all are large | `SiegelHalf`, `LiouvilleHalf` |
| auxiliary in $\mathbb F_q[x]$ | integer Dirichlet polynomial | $D(s)=\sum_{n\le N}a_nn^{-s}$, $a_n\in\mathbb Z$ | `intDirichlet` |
| Möbius on $\mathbb F_q[T]$ | Chebyshev transform, inversion | $T_a(n)=\sum_da(d)\lfloor n/d\rfloor$, $I_x$ | `chebyshevTransform`, `inversionOp` |

**Words.**
*Precision class* of a statement $S$ at a weight $a$: the perturbations $\delta$ with $S(a+\delta)$.
*Square-root class* $\mathcal Q$: perturbations with partial sums $O(\sqrt x\log^2x)$.
*Visible move*: one outside $\mathcal Q$; no weight satisfies the count both before and after it.
*Invisible move*: one inside $\mathcal Q$.
*Precision-faithful*: fails for $a+\varepsilon n^{-\eta}$, every $0\le\eta<\tfrac12$.
*Parity-breaking*: fails for the Liouville twin.
*Aperture-unbounded*: not determined by a finite window of the weight.
*Precision exponent* $\theta(a)$: the infimum of $\theta$ with $A(x)-x=O(x^\theta)$.
*Siegel half* at scale $\varphi$: auxiliaries with $0<\int_0^1P\le e^{-(n+1)+C\varphi(n+1)}$ exist.
*Liouville half*: every positive $\int_0^1P$ is $\ge e^{-(n+1)-C\varphi(n+1)}$.
*Ceiling*: the analytic bound used to certify a small positive integral.
*Sign gauge* of a prime set $F$: $\Lambda$ with sign $(-1)^k$ at $p^k$, $p\in F$.
*Flipped mass* $\theta_F(x)=\sum_{p\le x,\,p\in F}\log p$.
*Reciprocal torsion*: a horizon value $e^{A(n)}=1/r_n$ with $r_n\in\mathbb N$.

---

## 4. Mechanisms

1. **The stabilizer law.** If $a$ satisfies the count, $a+\delta$ does iff $\delta\in\mathcal Q$. The
   precision class of the count is the square-root class.
2. **The power threshold.** For $\varepsilon\ne0$, $\eta\ge0$: $\varepsilon n^{-\eta}\in\mathcal Q$ iff
   $\eta\ge\tfrac12$, from $\tfrac12x^{1-\eta}\le\sum_{n\le x}n^{-\eta}\le2\sqrt x$ $(\eta\ge\tfrac12)$.
   Precision rigidity of the count is sharp at $\tfrac12$, inclusive.
3. **Each half of the count is RH.** A one-sided square-root bound on $\psi(x)-x$, either sign,
   forces $\Theta\le\tfrac12$: by Landau both signs of $\psi(x)-x$ reach $x^b$ for every $b<\Theta$.
4. **Precision exponent = zero width.** $\theta(\Lambda)=\Theta$; RH iff $\theta(\Lambda)=\tfrac12$. Every
   weight has $\theta\ge0$ (a step function stays $\tfrac14$ from $x$), and the count gives $\theta\le\tfrac12$.
5. **The battery as a classification.** Visible, unconditionally: every Liouville mixture
   $(1-t)\Lambda+t\lambda\Lambda$, $t\ne0$ (partial sums $(1-2t)\psi+O(\sqrt x)$); $c\Lambda$, $c\ne1$
   (PNT); cofinite flips; $\Lambda+\varepsilon n^{-\eta}$, $\eta<\tfrac12$ (Littlewood: the count would make
   $\psi(x)-x$ eventually one-signed). Invisible: finite modifications, rescaled Euler factors (a prime
   tower carries $\le\log x$), $\varepsilon n^{-\eta}$ with $\eta\ge\tfrac12$.
6. **The lower half is monotone; the gauge stabilizer.** $a\le b$ and the lower half for $a$ give it
   for $b$. So for $a\le\Lambda$: the count for $a$ is RH and $\Lambda-a\in\mathcal Q$. For a sign
   gauge: the count is RH and $\theta_F=O(\sqrt x\log^2x)$. The count's stabilizer in the sign-gauge
   group is the set of square-root sparse flip sets.
7. **The deciding-input theorem.** Every property implying the count is parity-breaking,
   precision-faithful, aperture-unbounded, with stabilizer in $\mathcal Q$. Stable under the twist, or
   finitely determined, or stable under one visible move, it holds for no weight.
8. **Producers are precision-blind.** $\Lambda+\varepsilon n^{-\eta}$, $0<\eta<\tfrac12$, satisfies PNT and
   the Guth–Maynard law $\psi(x+x^\alpha)-\psi(x)\sim x^\alpha$ for every $\alpha\in(17/30,1)$, and fails the
   count. An error law $O(E)$ with $x^{1/2+\kappa}=O(E)$ is inherited by a weight failing the count.
9. **The integrality lattice.** $\{\int_0^1P:P\in\mathbb Z[x],\deg P\le n\}=d_{n+1}^{-1}\mathbb Z$, by Bézout
   over the horizon ($u/a+v/b=1/\operatorname{lcm}(a,b)$, iterated). The least positive Nair integral is
   $1/d_{n+1}$, and $\psi(n+1)=\max_P\log(1/\int_0^1P)$.
10. **The integrality exponent is the zero width.** The Siegel half and the Liouville half are the
    lower and upper halves of the count at the same scale. Both hold at $x^\theta$, $\theta>\Theta$, and
    both fail at every $\theta<\Theta$. Square-root integrality in either half is RH; a zero-free strip
    $\Theta<1$ is integrality at a fixed precision $\theta<1$.
11. **Integer Dirichlet polynomials at arithmetic points.** $\int_0^1P=D_P(1)$, the value at the pole.
    $d_N^m D(m)\in\mathbb Z$, so a nonzero $D(m)$ is $\ge d_N^{-m}=e^{-m\psi(N)}$, and this is attained (the
    values form $d_N^{-m}\mathbb Z$). $D(-k)\in\mathbb Z$. A nonzero $D$ has fewer real zeros than nonzero
    coefficients, hence $|D(-k)|\ge1$ at some $k<N$. Siegel's lemma gives $D\ne0$ of length $N$ vanishing at
    $0,-1,\dots,-(M-1)$ with height $\le(N^M)^{M/(N-M)}$, $M<N$.
12. **Parity in integrality.** $\sum_{m\le n}\lambda\Lambda(m)=2\psi(\lfloor\sqrt n\rfloor)-\psi(n)$, so
    $e^{A_\lambda(n)}=1/r_n$ with $r_n=d_n/d_{\lfloor\sqrt n\rfloor}^2\in\mathbb N$: the twin's horizon value is a
    reciprocal group order.
13. **Where precision is lost.** $T_\Lambda(n)=\log n!$ exactly; $0<\log n!-(n\log n-n)\le1+\tfrac12\log n$;
    every nonzero nonnegative perturbation moves $T$ linearly; $A(n)=\sum_{k\le n}\mu(k)T_a(\lfloor n/k\rfloor)$,
    so $\psi(n)=\sum_k\mu(k)\log\lfloor n/k\rfloor!$; the inversion operator sends some $E$ with
    $|E(y)|\le y^\theta$ to $\ge\pi(x)$, and no bound $Cx^{\theta'}$, $\theta'<1$, survives it.
14. **Calibration over $\mathbb F_q$.** The count at precision $\theta$ holds iff every
    $\|\beta_i\|\le q^{\theta-1/2}$, already from its lower half; the precision exponent is
    $\tfrac12+\max_i\log\|\beta_i\|/\log q\ge\tfrac12$, with equality iff unitary. Odd hyperelliptic data
    have exponent $\tfrac12$ (Stepanov). The golden datum has $N_k/5^k\to1$ and exponent $\tfrac12+\log\varphi/\log5$.

---

## 5. Pillar theorems

1. **Stabilizer law and power threshold** (`count_add_iff_mem_sqrtClass`,
   `smul_powerWeight_mem_sqrtClass_iff`, `not_count_and_count_add_smul_powerWeight`).
2. **Each half is RH; exponent = zero width** (`upperCount_vonMangoldt_iff`,
   `lowerCount_vonMangoldt_iff`, `precisionExponent_vonMangoldt`,
   `riemannHypothesis_iff_precisionExponent`).
3. **The battery classification** (`battery_classification`,
   `count_vonMangoldt_add_smul_powerWeight_iff`).
4. **The gauge stabilizer** (`count_iff_of_le_vonMangoldt`, `count_signGauge_iff`).
5. **The deciding-input theorem** (`deciding_input_necessary_properties`, `not_of_stable_visible`).
6. **Producers are precision-blind** (`producers_are_precision_blind`, `errorLaw_cannot_decide`).
7. **The integrality lattice** (`nairLattice_eq`, `isLeast_positive_nairIntegral`,
   `isGreatest_log_inv_nairIntegral`).
8. **The integrality exponent** (`siegelExponent_eq_zeroReSup`, `liouvilleExponent_eq_zeroReSup`,
   `riemannHypothesis_iff_siegelHalf_sqrtScale`, `riemannHypothesis_iff_liouvilleHalf_sqrtScale`,
   `zeroReSup_lt_one_iff_siegelHalf`).
9. **The transcendence toolkit on integer Dirichlet polynomials**
   (`exists_intDirichlet_eq_one_div_lcmUpto_pow`, `card_lt_of_intDirichlet_eq_zero`,
   `exists_one_le_abs_intDirichlet_neg`, `exists_intDirichlet_vanishing_on_trivial_lattice`).
10. **The twin's reciprocal torsion** (`partialSum_liouvilleWeight_eq`, `exp_partialSum_liouvilleWeight`).
11. **The Chebyshev ledger** (`psi_eq_sum_moebius_log_factorial`, `eq_of_chebyshevTransform_eq`,
    `log_factorial_sub_bounds`, `not_inversion_bounded`).
12. **Curve precision exponents** (`countAtPrecision_iff`, `precisionExponent_eq`,
    `precisionExponent_eq_half_iff`, `golden_countAtPrecision_iff`, `golden_tendsto_pointCount_div`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| A sharper constant in a relative-error theorem approaches RH | Its precision class contains every $\varepsilon n^{-\eta}$, $\eta>0$; constants do not measure distance to the count |
| The count selects $\Lambda$ | Modulo $\mathcal Q$ only: finite flips, Euler-factor deletions and square-root sparse sign gauges pass |
| One-sided counts are weaker | Each half alone is RH |
| Integrality reaches only linear precision | The floor is exact and the Siegel half at precision $\theta$ is $\Theta\le\theta$; what is linear is the *ceiling* used to certify auxiliaries |
| Nair's method loses at the integrality step | $\min^+\int_0^1P=1/d_{n+1}$ exactly |
| Identities are soft | They have precision class $\{0\}$; they lose precision under inversion |
| A small error in $\log\lfloor x\rfloor!$ gives a small error in $\psi$ | Inversion turns $y^\theta$ errors into $\pi(x)$-size errors |
| Perturbations with $\eta\ge\tfrac12$ are a defect of the method | They are invisible to the count itself |
| The golden datum violates integrality | It has integral counts and $N_k/5^k\to1$; its precision exponent is $\tfrac12+\log\varphi/\log5$ |
| Integer Dirichlet polynomials certify zeros by integrality | Integrality speaks at $s\in\mathbb Z$ (pole side sharp, trivial lattice integral), not at nontrivial zeros |
| The Liouville twin is an integrality-preserving move | Its horizon value is a reciprocal group order |

---

## 7. Questions the programme answers

1. **Which statements can decide the count?** Only parity-breaking, precision-faithful,
   aperture-unbounded statements whose stabilizer lies in $\mathcal Q$ (mechanism 7). *Answered.*
2. **Which battery moves does the count see?** The classification of mechanisms 5–6, including the
   sign-gauge stabilizer. *Answered.*
3. **What is the precision of the classical producers?** PNT, Guth–Maynard and every error law
   weaker than square root are inherited by $\Lambda+\varepsilon n^{-\eta}$: none decides. *Answered.*
4. **How much precision does integrality over $\mathbb Z$ reach?** Exactly $\Theta$, in each half;
   square-root integrality is RH; a fixed strip is integrality at a fixed precision. *Answered.*
5. **Where is precision lost in Chebyshev–Nair?** Not at the floor (exact) nor in the identity
   (precision $\log n$), but in the inversion (unbounded at every precision) and in the ceiling.
   *Answered for floor, identity and inversion; the ceiling is open problem 1.*
6. **How does integrality see parity?** Through reciprocal torsion. *Answered.*
7. **What is precision over $\mathbb F_q$?** The exponent formula, one half suffices, unitarity is
   square-root precision, golden is the relative-error twin. *Answered.*
8. **Where can integer auxiliary Dirichlet polynomials speak?** At $s\in\mathbb Z$, sharply on the
   pole side; fewer than $N$ real zeros; Siegel existence up to $N-1$ trivial conditions. *Answered;
   off-line vanishing is open problem 2.*

---

## 8. Tools

Built: precision classes and the count; each half of the count for $\Lambda$; the precision exponent;
the battery classification and the gauge stabilizer; the deciding-input theorem; precision-blindness
of producers; the integrality lattice and exponent; the transcendence toolkit on integer Dirichlet
polynomials; the twin's reciprocal torsion; the Chebyshev ledger; curve precision exponents.

To build:

| Tool | Purpose | Test |
|---|---|---|
| A precision-preserving ceiling | Certify Siegel auxiliaries using cancellation in $\int_0^1P$, not $\int\lvert P\rvert$ | Must fail for the golden datum and for $\lambda\Lambda$ |
| Inversion with arithmetic input | Bound $\sum\mu(k)E(x/k)$ for the Stirling error at precision $\theta<1$ | Equivalent strength to a strip; must use $\mu$ |
| Precision of the index | Precision class of finite index on two towers (HKT) | Lindelöf test |
| Precision of the Hecke defect | Which perturbations move $E_f(c\log T)$ at order $N(T)$ (CDG) | Census |
| Successor precision | Precision class of laws using the exact integer count $\lfloor x\rfloor$ | Over-regular Beurling systems must fail |

---

## 9. Open research topics

1. **The constructive limit of integrality (integer Chebyshev problem).** The floor is exact and the
   exponent is $\Theta$; determine the precision reachable by auxiliaries certified through
   $\sup_{[0,1]}\lvert P\rvert$ or $\int_0^1\lvert P\rvert$ (expected: linear with constant $<1$, since the
   integer Chebyshev constant of $[0,1]$ exceeds $e^{-1}$), and design a ceiling that keeps sign
   cancellation. A ceiling that reaches precision $\theta<1$ proves a zero-free strip.
2. **Off-line vanishing.** A source of integer Dirichlet polynomials vanishing at one character of
   every off-line pair (HKT's arithmetic Stepanov problem). Integrality speaks only at $s\in\mathbb Z$;
   which precision class must such a source have?
3. **Precision of positivity.** Classify the precision classes of the corpus's positivity theorems
   (apertures, atomic tests, the separated regime). Every twin-blind theorem has the twin in its class.
4. **Inversion with arithmetic input.** How much cancellation of $\mu$ against the specific Stirling
   error is needed at each precision $\theta$; the inversion is unbounded on size classes.
5. **The successor as a precision source.** Over-regular Beurling systems have integer counts at
   square-root precision and prime counts without it; isolate the identity of $\mathbb Z$ (the exact
   count $\lfloor x\rfloor$, precision $0$) that excludes them.
6. **Gauge geometry of the stabilizer.** The stabilizer of the count in the full gauge torus
   $(\mathbb R/\mathbb Z)^{\text{primes}}$, beyond sign gauges; its relation to Haar-generic square-root
   cancellation (ACG).
7. **Precision classes of index, defect and regulator.** The finite-index stratum, the Hecke defect at
   logarithmic translation, the covariant regulator on the characteristic circle.

---

## 10. Success criteria and what a contribution is

**Success.** A producer: one unconditional inequality about $\zeta$ whose precision class lies in
$\mathcal Q$, which fails the battery, and which lands in a stratum above [open]. The first target is a
fixed zero-free strip, which by the integrality exponent is a ceiling for Siegel auxiliaries at a
fixed precision $\theta<1$; then the count. Intermediate success: a no-go of a new kind (a stated
class of ceilings or inversions cannot pass a stated precision) with its positive survivor.

**A contribution**
- states its precision class (which perturbations of the weight it survives) and its parity behaviour;
- says what it gives for the battery: $\lambda\Lambda$, $c\Lambda$, finite and cofinite flips, sign
  gauges, $\Lambda+\varepsilon n^{-\eta}$, the golden datum, over-regular Beurling systems;
- separates identity, floor, ceiling and inversion, and names the step where precision is kept or lost;
- calibrates over $\mathbb F_q$ (Weil by counting, golden datum by precision exponent);
- is unconditional, and records the positive survivor of every no-go.

**Principles.** Precision is a class, not a constant. Identities are exact; precision is lost in
extraction. A statement that survives a visible move cannot decide. Each half of the count is the
whole count. Integrality is exact at the floor; the ceiling is the problem. Calibrate over
$\mathbb F_q$.
