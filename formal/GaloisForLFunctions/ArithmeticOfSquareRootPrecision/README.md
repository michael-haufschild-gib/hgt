# Arithmetic of Square-Root Precision (ASRP)

Namespace `GaloisForLFunctions.ArithmeticOfSquareRootPrecision`; umbrella `ArithmeticOfSquareRootPrecision.lean`.

**Question.** The corpus has reduced RH to one count: $\psi(x)-x\le C\sqrt x\log^2x$, and has shown
that no estimate stable under relative error $o(1)$ can produce it. Which arithmetic statements
can carry information at square-root precision at all, which identities and integers over
$\mathbb Z$ carry it, how much of it can integrality extract, and where exactly is it lost in the
classical methods?

ASRP is the arithmetic of **precision**. Basic object: a *weight* $a:\mathbb N\to\mathbb R$ (a
prime-side source, $\Lambda$ being the arithmetic one) and its partial sums $A(x)=\sum_{n\le x}a(n)$.
Basic invariant: the **precision class** of a statement, the set of perturbations of the weight
it survives. Basic integer: the **horizon period** $d_N=\operatorname{lcm}(1,\dots,N)$, whose
log-order is $\psi(N)$. Everything is unconditional; RH appears only inside equivalences.

---

## 1. Place in the research

Every route in the corpus ends at the same wall: the deciding input must be **parity-breaking**
(fail for the Liouville twin $\lambda\Lambda$), **square-root precise** (fail for
$\Lambda+\varepsilon n^{-\eta}$, $\eta<\tfrac12$) and of **unbounded aperture** (not determined by a
finite window). The programmes that met this wall stated it as a principle or as a test battery.
ASRP makes it a theory: precision classes, the battery as a classification theorem, and the
integrality face of the count. It sits one level below the index theory of the Weil kernel, where
signs come from integers.

| Programme | Interface |
|---|---|
| ArithmeticEffectivityTheory | Log-torsion $\psi(N)=\log\lvert\mathbb Z/d_N\rvert$ (`logTorsion_eq_psi`), Nair's integrality floor (`log_inv_integral_le_psi`, `nair_psi_ge`); ASRP proves the floor is attained and computes its exact precision |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | The global law is the one-sided count (`global_law_count`); precision and parity principles; Stepanov compressions and the annihilation law. ASRP supplies the precision calculus those principles presuppose |
| SelectiveMultiscaleArithmeticPositivity | Precision rigidity on towers (`not_towerPositive_and_perturbed`): tower positivity is precision-faithful. ASRP proves the same for the count and classifies which moves each statement sees |
| ArithmeticCorrelationGeometry | The gauge torus; square-root cancellation at Haar-almost every gauge point. Gauge points are weights; their visibility is a precision question |
| SquareRootThreshold | Zero visibility and the square-root threshold $X\asymp T$; the zero width $\Theta$ |
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Curve data, the golden datum, Lefschetz growth = width. ASRP's calibration: precision exponents of curve data |
| ArithmeticIntersectionTheory, RenormalizedArithmeticPotentialTheory | Torsion orbits with integer intersection numbers; the covariant regulator problem |
| ConjugateDiagonalGeometry | The Hecke defect $E_f(L)$ as displacement currency; its precision class is an ASRP question |
| MultiplicativePositivityGeometry | The only producer of zero-free regions (positivity + growth) and its exact width law |
| `RHTower` | Von Koch (`riemannHypothesis_iff_chebyshevPsi_sub_isBigO`), the exponent law $\Theta=$ order of $\psi(x)-x$ (`chebyshevPsi_sub_exponent_law`), PNT, Guth–Maynard short intervals |
| `HTGeometry` | Real zeros of exponential polynomials (`card_lt_of_expPoly_eq_zero`) |

---

## 2. Why

**Over $\mathbb F_q$ the sign is a count, and the count is an integer.** For a curve,
$N_m=q^m+1-\sum_i\alpha_i^m$ is the number of points of a finite set; Weil's theorem is
$|N_m-q^m-1|\le2g\,q^{m/2}$; Stepanov proves the one-sided half by integrality (an auxiliary
polynomial with $x^q=x$ in its coefficients vanishes to high order at every rational point). The
precision $q^{m/2}$ is reached because the coefficient ring has elements invisible to
differentiation.

**Over $\mathbb Z$ the integers are log-orders.** $\psi(N)=\log d_N$ exactly; integrality gives
$d_{n+1}\int_0^1P\in\mathbb Z$ for $P\in\mathbb Z[x]$ of degree $\le n$, hence Chebyshev–Nair bounds
at *linear* precision. The open question of the whole programme (AET open problem 4; review 2910,
question 3) is whether integrality over $\mathbb Z$ can reach any precision beyond linear.

**Why precision is the right invariant.** Three facts organise everything:

1. The count is a statement with a *precision class*: it survives exactly the perturbations whose
   partial sums are $O(\sqrt x\log^2x)$. Every implication into the count must respect that class.
2. The classical theorems (PNT, Vinogradov–Korobov, Guth–Maynard, Chebyshev, Nair) have precision
   classes that contain $\varepsilon n^{-\eta}$ for every $\eta>0$; therefore none can decide.
3. Identities (the Chebyshev identity $\sum_d\Lambda(d)\lfloor x/d\rfloor=\log\lfloor x\rfloor!$, the
   Euler product, $\psi(N)=\log d_N$) have precision class $\{0\}$. Precision is not missing from the
   arithmetic of $\mathbb Z$; it is lost when estimates are extracted from identities.

ASRP studies where it is lost, and what it would take to keep it.

---

## 3. Objects and language

| Over $\mathbb F_q$ | ASRP object | Over $\mathbb Z$ | Lean |
|---|---|---|---|
| point count $N_m$ | weight, partial sum | $a:\mathbb N\to\mathbb R$, $A(x)=\sum_{n\le x}a(n)$ | `partialSum` |
| $\lvert N_m-q^m-1\rvert\le Cq^{m/2}$ | the count | $A(x)-x=O(\sqrt x\log^2x)$ | `Count`, `UpperCount`, `LowerCount` |
| error of size $q^{m\theta}$ | precision class | $\{\delta:\sum_{n\le x}\delta(n)=O(\varphi)\}$ | `PrecisionClass`, `sqrtClass` |
| $\max\log\lvert\alpha\rvert/\log q$ | precision exponent | order of $A(x)-x$ | `precisionExponent` |
| fake data (golden) | battery move | $\lambda\Lambda$, $c\Lambda$, $\Lambda+\varepsilon n^{-\eta}$, flips | `liouvilleWeight`, `powerWeight` |
| $x^q-x$, Frobenius-flat coefficients | horizon period | $d_N=\operatorname{lcm}(1..N)$, $\log d_N=\psi(N)$ | `Nat.lcmUpto` |
| Stepanov auxiliary | Nair functional | $P\mapsto\int_0^1P=D_P(1)$ | `nairIntegral` |
| integrality of $N_m$ | integrality lattice | $\{\int_0^1P\}=d_{n+1}^{-1}\mathbb Z$ | `nairLattice` |
| — | Siegel / Liouville halves | small positive integrals exist / all are large | `SiegelHalf`, `LiouvilleHalf` |
| auxiliary in $\mathbb F_q[x]$ | integer Dirichlet polynomial | $D(s)=\sum_{n\le N}a_nn^{-s}$, $a_n\in\mathbb Z$ | `intDirichlet` |
| $\#C(\mathbb F_q)\in\mathbb Z$ | Liouville inequality | $D(k)\in d_N^{-k}\mathbb Z$, $D(-k)\in\mathbb Z$ | — |
| Möbius on $\mathbb F_q[T]$ | Chebyshev transform | $T_a(x)=\sum_da(d)\lfloor x/d\rfloor$ | `chebyshevTransform` |

**Words.**
*Precision class* of a statement $S$ at a weight $a$: the perturbations $\delta$ with $S(a+\delta)$.
*Square-root class* $\mathcal Q$: perturbations with partial sums $O(\sqrt x\log^2x)$.
*Visible* move: one outside $\mathcal Q$; the count cannot hold before and after it.
*Precision-faithful*: fails for $a+\varepsilon n^{-\eta}$, every $\eta<\tfrac12$.
*Parity-breaking*: fails for the Liouville twin.
*Aperture-unbounded*: not determined by any finite window of the weight.
*Precision exponent* $\theta(a)$: the infimum of $\theta$ with $A(x)-x=O(x^\theta)$; $\theta(\Lambda)=\Theta$.
*Integrality exponent*: the precision at which the minimal positive Nair integral equals $e^{-n}$.
*Siegel half*: existence of auxiliaries with small positive integral (a lower bound for $\psi$).
*Liouville half*: every positive integral is large (an upper bound for $\psi$).
*Ceiling*: the analytic bound used to make a Siegel auxiliary small.
*Reciprocal torsion*: the twin's horizon value $e^{A(n)}=1/r_n$ with $r_n\in\mathbb N$.

---

## 4. Mechanisms

1. **The stabilizer law.** If $a$ satisfies the count, then $a+\delta$ does iff $\delta\in\mathcal Q$. The
   precision class of the count is exactly the square-root class.
2. **The power threshold.** $\varepsilon n^{-\eta}\in\mathcal Q$ iff $\eta\ge\tfrac12$ ($\varepsilon\ne0$):
   precision rigidity of the count is sharp at $\tfrac12$ inclusive.
3. **The battery as a classification.** Visible: the Liouville twin, every scaling $c\Lambda$ with
   $c\ne1$, quadratic mixtures, cofinite flips, $\varepsilon n^{-\eta}$ with $\eta<\tfrac12$. Invisible:
   every finite modification, every finite set of Euler-factor deletions or prime-tower flips,
   $\varepsilon n^{-\eta}$ with $\eta\ge\tfrac12$. The count does not select $\Lambda$; it selects its
   class modulo $\mathcal Q$.
4. **The deciding-input theorem.** Every property of weights that implies the count is
   parity-breaking, precision-faithful, aperture-unbounded, and has stabilizer inside $\mathcal Q$. A
   property stable under one visible move and implying the count holds for no weight.
5. **Producers are precision-blind.** PNT, short-interval asymptotics with relative error $o(1)$ at
   any length (Guth–Maynard's theorem itself), and every error-term law weaker than $x^{1-\eta}$ hold
   for $\Lambda+\varepsilon n^{-\eta}$ whenever they hold for $\Lambda$.
6. **Precision exponent = zero width.** $\theta(\Lambda)=\Theta=\sup\operatorname{Re}\rho$; for a one-signed
   perturbation the exponent of its partial sums is the abscissa of its Dirichlet series.
7. **The integrality lattice.** $\{\int_0^1P:P\in\mathbb Z[x],\deg P\le n\}=d_{n+1}^{-1}\mathbb Z$ (Bézout over
   the horizon). The minimal positive Nair integral is $1/d_{n+1}$: the integrality floor is
   attained, and $\psi(n+1)=\log(1/\min^+\!\int_0^1P)$.
8. **The integrality exponent is the zero width.** The Siegel half and the Liouville half each hold
   at precision $\theta>\Theta$ and fail at every $\theta<\Theta$. RH ⇔ square-root precise Nair
   auxiliaries exist ⇔ every positive Nair integral is $\ge e^{-n-O(\sqrt n\log^2n)}$. A fixed
   zero-free strip is exactly integrality at a fixed precision $<1$.
9. **Integer Dirichlet polynomials at arithmetic points.** $\int_0^1P=D_P(1)$ is the value at the pole
   of an integer Dirichlet polynomial; $\{D(k)\}=d_N^{-k}\mathbb Z$ for $k\ge1$ (sharp Liouville
   inequality), $D(-k)\in\mathbb Z$, a nonzero $D$ of length $N$ is $\ge1$ in modulus at one of
   $s=0,-1,\dots,-(N-1)$, has fewer than $N$ real zeros, and Siegel's lemma supplies small $D$ with
   prescribed integer vanishing conditions. Integrality speaks at the pole and at the trivial-zero
   lattice, and at precision $\Theta$.
10. **Parity in integrality.** The Liouville twin's horizon value is $1/r_n$ with
    $r_n=\prod_{p\le n,\ \lfloor\log_pn\rfloor\text{ odd}}p$: parity turns torsion into reciprocal torsion,
    and $\log r_n\ge\theta(n)-\theta(\sqrt n)$.
11. **Where precision is lost.** The Chebyshev transform of $\Lambda$ is $\log\lfloor x\rfloor!$, known at
    precision $\log x$ (Stirling), and every nonzero one-signed perturbation is visible in it at
    linear scale. The count is its Möbius inversion, and inversion is unbounded at every precision:
    errors of size $y^\theta$ invert to errors $\gg x/\log x$. All loss is in the inversion; integrality
    loses nothing at the floor.
12. **Calibration over $\mathbb F_q$.** The precision exponent of a curve datum is
    $\tfrac12+\max_i\log|\beta_i|/\log q$; the square-root count holds iff the datum is unitary;
    relative-error counts $N_m\sim q^m$ hold on the golden datum, whose exponent is
    $\tfrac12+\log\varphi/\log5$.

---

## 5. Pillar theorems

1. **Stabilizer law and power threshold** (`count_add_iff_mem_sqrtClass`, `powerWeight_mem_sqrtClass_iff`).
2. **The battery classification** (`not_count_liouvilleWeight`, `not_count_smul_vonMangoldt`,
   `count_add_iff_of_finite_support`, `battery_classification`).
3. **The deciding-input theorem** (`deciding_input_necessary_properties`).
4. **Producers are precision-blind** (`guthMaynard_perturbed`, `pnt_perturbed`).
5. **Precision exponent = zero width** (`precisionExponent_vonMangoldt`).
6. **The integrality lattice** (`nairLattice_eq`, `minPositiveNairIntegral_eq`).
7. **The integrality exponent** (`siegelHalf_iff`, `liouvilleHalf_iff`,
   `riemannHypothesis_iff_sqrt_siegelHalf`, `riemannHypothesis_iff_sqrt_liouvilleHalf`).
8. **Liouville inequality at the pole** (`intDirichlet_values_eq`).
9. **Reciprocal torsion of the twin** (`exp_partialSum_liouvilleWeight`).
10. **Inversion amplification** (`exists_inversion_amplification`).
11. **Curve precision exponents** (`curve_count_iff_unitary`, `golden_relative_count`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| A sharper constant in a relative-error theorem approaches RH | Its precision class contains every $\varepsilon n^{-\eta}$; distance to the count is not measured by constants |
| The count selects $\Lambda$ | It selects $\Lambda$ modulo $\mathcal Q$: finite flips and Euler-factor deletions pass |
| One-sided counts are weaker | Each half alone is RH-equivalent; one-sidedness is not a precision loss |
| Integrality reaches only linear precision | The integrality floor is exact; the Siegel half at precision $\theta$ is the strip $\Theta\le\theta$. What is linear is the *ceiling* used to certify auxiliaries |
| Nair's method loses at the integrality step | $\min^+\int_0^1P=1/d_{n+1}$ exactly |
| Identities are soft | Identities have precision class $\{0\}$; they lose precision only under inversion |
| A small error in $\log\lfloor x\rfloor!$ gives a small error in $\psi$ | Möbius inversion turns $y^\theta$ errors into $x/\log x$ errors |
| Perturbations above $\eta=\tfrac12$ are a defect of the method | They are invisible to the count itself |
| Golden data violate integrality | They have integral counts, relative-error counts and every soft structure; their precision exponent is above $\tfrac12$ |
| Integer Dirichlet polynomials certify zeros by integrality | Integrality speaks at $s\in\mathbb Z$ (pole, trivial lattice), never at a nontrivial zero |

---

## 7. Questions the programme answers

1. **Which statements can decide the count?** Only parity-breaking, precision-faithful,
   aperture-unbounded statements whose stabilizer lies in $\mathcal Q$.
2. **Which battery moves does the count see?** The classification of mechanism 3.
3. **What is the precision of the classical producers?** At least $1-\eta$ for every $\eta>0$ in the
   sense of mechanism 5: none decides.
4. **How much precision does integrality over $\mathbb Z$ reach?** Exactly $\Theta$, in each half
   separately; square-root precise integrality is RH.
5. **Where is precision lost in Chebyshev–Nair?** Not at the floor (exact) and not in the identity
   (precision $\log x$), but in the inversion (unbounded at every precision) and in the ceiling.
6. **How does integrality see parity?** Through reciprocal torsion.
7. **What is precision over $\mathbb F_q$?** The precision exponent of the datum; square-root
   precision is unitarity; the golden datum is the relative-error twin.
8. **Where can integer auxiliary Dirichlet polynomials speak?** At $s\in\mathbb Z$ with sharp
   Liouville inequality, on the real axis with fewer than $N$ zeros, with Siegel-lemma existence.

---

## 8. Tools

Built: precision classes and the count; the battery classification; the deciding-input theorem;
the precision-blindness of producers; the exponent law in precision language; the integrality
lattice and the integrality exponent; integer Dirichlet polynomials at arithmetic points; the
twin's reciprocal torsion; the inversion amplification lemma; curve precision exponents.

To build:

| Tool | Purpose | Test |
|---|---|---|
| A precision-preserving ceiling | Certify Siegel auxiliaries using cancellation in $\int_0^1P$, not $\int\lvert P\rvert$ | Must fail on the golden datum and for $\lambda\Lambda$ |
| Precision of the index | Precision class of finite index on two towers (HKT) | Lindelöf test |
| Precision of the Hecke defect | Which perturbations change $E_f(c\log T)$ at order $N(T)$ (CDG) | Census |
| Successor precision | The precision class of $\gcd(n,n+1)=1$-laws | Beurling systems must fail |

---

## 9. Open research topics

1. **The constructive limit of integrality (integer Chebyshev problem).** The floor is exact;
   determine the precision reachable by auxiliaries certified through $\int_0^1\lvert P\rvert$ or
   $\sup\lvert P\rvert$ (expected: linear with constant $<1$, Gorshkov–Montgomery), and design a
   ceiling that keeps sign cancellation.
2. **Off-line vanishing.** A source of integer Dirichlet polynomials vanishing at one character of
   every off-line pair (the arithmetic Stepanov problem of HKT) in precision language: which
   precision class must such a source have?
3. **Precision of positivity.** Classify the precision classes of the corpus's positivity theorems
   (apertures, atomic tests, separated regime); every twin-blind theorem has the twin in its class.
4. **Inversion with arithmetic input.** Quantify how much cancellation in $\sum\mu(k)E(x/k)$ for the
   specific Stirling error is needed for each precision $\theta$.
5. **The successor as a precision source.** Over-regular Beurling systems have integer counts at
   square-root precision and prime counts without it; locate the identity of $\mathbb Z$ (exact
   integer count $\lfloor x\rfloor$) that excludes them.
6. **One-prime certification in height.** Explicit primes certifying all right zeros of height
   $\le T$ (Diophantine separation of $\log p$).
7. **Precision classes of index and defect.** The finite index stratum, the Hecke defect at
   logarithmic translation, the covariant regulator.

---

## 10. Success criteria and what a contribution is

**Success.** A producer: one unconditional inequality about $\zeta$ whose precision class lies in
$\mathcal Q$, which fails the battery, and which lands in a stratum above [open] — first a fixed
zero-free strip (integrality at precision $<1$), then the count. Intermediate success: a no-go of a
new kind (a stated class of ceilings cannot pass a stated precision) with its positive survivor.

**A contribution**
- states its precision class (which perturbations of the weight it survives) and its parity
  behaviour;
- says what it gives for the battery: $\lambda\Lambda$, $c\Lambda$, flips (finite and cofinite),
  $\Lambda+\varepsilon n^{-\eta}$, the golden datum, over-regular Beurling systems;
- separates identity, floor, ceiling and inversion, and names the step where precision is kept or lost;
- calibrates over $\mathbb F_q$ (Weil by counting, golden datum by precision exponent);
- is unconditional, and records the positive survivor of every no-go.

**Principles.** Precision is a class, not a constant. Identities are exact; precision is lost in
extraction. A statement that survives a visible move cannot decide. Integrality is exact at the
floor; the ceiling is the problem. Calibrate over $\mathbb F_q$.
