# Arithmetic Gauge Theory of the ring ℤ (AGT)

Namespace `GaloisForLFunctions.ArithmeticGaugeTheory`; umbrella `ArithmeticGaugeTheory.lean`.

**Question.** The integers carry two structures, addition and multiplication. Each has a dual: the
circle of additive characters, and the gauge torus `G` of unimodular completely multiplicative
functions. The prime source `Λ` is one point of `G`, the trivial point `0`, and Haar-almost every
other point already satisfies every square-root law that RH asks of `0`. The question is what makes
`0` typical, and where the two structures meet so that a proof could see the difference between `0`
and its twins. Over `𝔽_q` they meet in Frobenius, a ring endomorphism that is additive and
multiplicative at once. `ℤ` has no such endomorphism.

AGT studies the ring `ℤ` through this pair of duals. Its basic object is a **gauge point**
`x ∈ G`, the twist `χ_x`, and a coefficient system read through it. Its basic dichotomy is between
**gauge-invariant** statistics, which are constant on gauge orbits, and **gauge-charged** statistics,
which have mean zero on them. Everything is unconditional; RH appears only inside equivalences and as
the statement that the point `0` is typical modulo its pole.

---

## 1. Place in the research

The corpus has established two facts that define this programme.

- **Selectivity has two sources.**
  - Weil positivity is pointwise-closed, and every twist of `Λ` is a pointwise limit of vertical
    shifts. So a selective statement must use the shift-fixed terms (the pole and the Gamma factor)
    or the non-ratio lags.
  - Non-ratio lags carry gauge charge, i.e. additive structure.
  - Multiplicative data cannot select, because the whole gauge orbit shares them.
- **The first source has a limited reach.**
  - The pole pays the complete Weil form at bounded overlap, and rejects the Liouville twin and the
    prime flip `ω₁₁` there.
  - Past touching, additive successor shells enter the form, and every nonpolar reference energy
    loses `log c`.
  - At the RH-complete overlap, the remaining input is gauge charge at the single point `0`.

AGT is the programme for the second source. ACG built the gauge torus and its orthogonality. AGT
asks what the additive structure of `ℤ` contributes at the one point that is additively invariant.

| Programme | Interface |
|---|---|
| ArithmeticCorrelationGeometry (ACG) | Gauge torus `GaugeTorus`, Haar measure `gaugeHaar`, twists `twist`, orthogonality, successor charge, finite gauge subgroups. AGT builds on these objects. |
| ArithmeticKreinLangerTheory (AKLT) | Twin-blindness of pointwise-closed statements; the parity twin lives only in the Bohr closure; the producer ledger; Stepanov's order over `𝔽_q`. |
| ArithmeticOfSquareRootPrecision (ASRP) | Precision classes; the count's stabilizer is the square-root class; deciding-input theorem. |
| SpacingScaleHarmonicAnalysis (SSHA) | Diamagnetic inequality; the gauge enters through non-ratio lags; length–height coordinates. |
| TransMetzlerWeilPositivity (TM), CACT, RAPT | Complete positivity at bounded overlap; successor-shell thresholds; nonpolar losses; Ramanujan coordinates. |
| HeckeKreinToeplitz (HKT), EAHT | Index of the Weil kernel; global law; heights and carriers. |
| ArithmeticOrientationGeometry (AOG) | Orientation of the scaling correspondence; AGT supplies the additive side that AOG's "Bézout-selective orientation" asks for. |
| ArithmeticCastelnuovoSeveri (ACS) | Census and coalescent surplus; the scaling surface. |

---

## 2. Why

**One point among many.**

- Twisting `Λ` by a gauge point `x` gives `Λχ_x`.
- For Haar-almost every `x`, the twisted partial sums cancel to the square root and carry no pole.
- At `x = 0` they carry the pole (the prime number theorem), and RH says the pole is the only
  atypicality.
- The exceptional set of the Möbius half-power law is comeager and null, and `0` lies in its
  closure.

So RH is not a statement about an ensemble. It is the typicality of one specific point, in the way
Roth's theorem is the typicality of algebraic numbers.

**What distinguishes the point `0`.** It is the only gauge point that is compatible with addition:

- `χ₀(n+1) = χ₀(n)`;
- `Λ * 1 = log` collapses every divisor fibre to an archimedean absolute value;
- the pole is the trace of that collapse.

Every other gauge point sees addition only as noise (gauge charge). A proof must therefore use
addition at `0`, at square-root precision.

**Why a new field.** Over `𝔽_q`, Frobenius couples the two structures, and Weil's theorem follows in
Stepanov's order:

1. an auxiliary vanishes with multiplicity `√q` on the rational points, because `x^q = x`;
2. a count follows;
3. positivity follows from the count.

Over `ℤ` there is no ring endomorphism to supply the multiplicity, and the parity twin is not
geometric. AGT has to find what replaces Frobenius. It also has to prove what cannot replace it.

---

## 3. Objects and language

| Object | Meaning | Lean |
|---|---|---|
| Gauge torus `G`, Haar measure | Unimodular completely multiplicative functions | `ArithmeticCorrelationGeometry.GaugeTorus`, `gaugeHaar`, `twist` |
| Trivial point `0` | The prime source itself | `twist 0 = 1` |
| Special point | A gauge point with additive structure (periodic, eventually constant) | this programme |
| Liouville point (twin tail) | Agrees with `0` on finitely many primes, then follows the Liouville sign | ACG |
| Approximate ring endomorphism | Multiplicative map with bounded additive defect | this programme |
| Divisor fibre `F_x(ℓ) = Σ_{k∣ℓ} Λ(k)χ_x(k)` | The prime source read on one product | this programme |
| Successor shell `n = km + j` | Additive pairs entering the Weil form at overlap `≈ |j|` | CACT; this programme |
| Gauge charge | Mean zero over `G` | ACG |
| Gauge exponent of a point | Precision exponent of a twisted coefficient system | this programme |
| Producer, ledger | Integer auxiliary; `Σ m_p log p ≤ log A` | AKLT |

**Words.**

- *Gauge-invariant*: constant on gauge orbits. *Gauge-charged*: gauge mean zero. *Boundary*:
  shift-fixed and archimedean (pole, Gamma, escaped dilation mass).
- *Typical*: satisfies every Haar-almost-sure law. *Special*: carries additive structure.
  *Coherent*: a gauge-charged statistic whose value at `0` exceeds its gauge root-mean-square.
- *Shell*, *repayment*, *marginal positivity*, *multiplicity beyond divisibility*, *Frobenius
  substitute*.

---

## 4. Mechanisms

1. **Gauge calculus.** Orthogonality of twists turns every statistic into a gauge-invariant part
   (products that coincide) and a gauge-charged part (everything else). Multiplicative arguments
   prove the invariant part, and therefore prove almost-sure statements.
2. **Special-point rigidity.** Additive structure on a gauge point is rigid: compatibility with
   addition forces the trivial point. This is the mechanism that singles out `0` and explains why
   the Dirichlet characters, which have additive structure, are not unimodular.
3. **The Frobenius gap.** A multiplicative self-map of `ℕ` that respects addition up to a bounded
   defect is either the identity or a gauge point bounded by one. No growing multiplicity comes from
   self-maps of `ℤ`; a Frobenius substitute must live on a larger object.
4. **Coherent collapse.** At `0` the divisor fibre is `log ℓ`, while its gauge mean is `0` and its
   gauge root-mean-square is `(Σ_{k∣ℓ} Λ(k)²)^{1/2}`. The ratio measures how strongly `0` is atypical
   on that fibre; the pole is the sum of these coherent fibres.
5. **Shells as successor correlations.** The non-ratio part of the prime form on atomic families is a
   sum of successor correlations of the convolved source `Λ * x` against `x`. This identifies the
   gauge-charged part of the Weil form with the additive statistics of ACG.
6. **Bounded multiplicity of classical producers.** Factorial-ratio auxiliaries have multiplicity
   bounded by the number of factorials above the square root, so they cannot grow multiplicity the way
   Stepanov's auxiliary does.

---

## 5. Pillar theorems

To be filled with the Lean statements as they are proved:

1. Uniqueness of the additively invariant gauge point.
2. Classification of approximate ring endomorphisms of `ℕ`, and the Frobenius gap.
3. The divisor collapse selects `0`; its gauge mean, variance and coherence.
4. Shells are successor correlations of the convolved source.
5. Bounded multiplicity of factorial-ratio producers.
6. The gauge exponent: Haar-almost-sure value, twin tails, the trivial point.

---

## 6. Traps

| Trap | Truth |
|---|---|
| A multiplicative argument proves something about `0` | It proves the same statement for Haar-almost every twist, and decides nothing about `0`. |
| Dirichlet characters are special gauge points | Unimodular periodic points are trivial; characters are special only because they vanish at their conductor. |
| An approximate Frobenius exists on `ℤ` | Bounded-defect endomorphisms are the identity or bounded gauge points. |
| The pole is the only atypicality one must handle | It is the only atypicality RH allows; others would be off-line zeros. |
| A positive mixed Gram of an affine orbit carries arithmetic | It is positive for every source. |
| Coherence at `0` is a sign | It is a size statement; signs need the boundary. |
| Typical in measure means typical in category | The exceptional set is comeager. |

---

## 7. Questions the programme aims to answer

1. What replaces `x^q = x` over `ℤ`? At which points should an auxiliary vanish, and in what sense
   finer than divisibility?
2. Is there a structure on which the Liouville twist acts geometrically? Its only possible home is the
   Bohr closure of the vertical shifts.
3. What is the positive form of the affine Weil kernel, and is its boundary the pole?
4. Which gauge-charged statistics have values at `0` determined by structure (`Λ * 1 = log`, the
   singular series), and which are pure discrepancy?
5. What is the gauge exponent of a point, and is it `Θ` at `0`?
6. What replaces Riemann–Roch as an index ceiling?
7. Why is positivity marginal at the limit, and which exact identity carries the zero margin?

---

## 8. Tools to develop

| Tool | Purpose | Test |
|---|---|---|
| Gauge calculus | Split any statistic into invariant and charged parts | Recover ACG's orthogonality and successor charge |
| Special-point theory | Characterize gauge points with additive structure | The trivial point is the unique additively invariant point |
| Endomorphism theory | Classify multiplicative maps compatible with addition | Identity and gauge points only; contrast with Frobenius over `𝔽_q` |
| Shell calculus | Exact shells of the Weil form as successor correlations | Gauge mean zero; pole-vector collapse to `log` |
| Producer theory | Multiplicity of integer auxiliaries | Factorial ratios bounded; Stepanov unbounded over `𝔽_q` |
| Gauge exponents | Typicality of points | Almost-sure value; twin tails at `1`; `0` at `Θ` |

---

## 9. Open research topics

- A Frobenius substitute on a larger object (Bohr compactification, Witt vectors, an adelic affine
  group) with a fixed budget.
- Repayment of the nonpolar `−log c` losses by successor shells.
- An index ceiling from ring structure.
- A typicality theorem for special points, in the style of Roth and Siegel.
- Gauge charge at `0` beyond the major arcs.

---

## 10. Success criteria and what a contribution must be

**Success.** One of the following:

- a statement about gauge charge at the point `0` that is false for Haar-random points;
- a Frobenius substitute with growing multiplicity;
- a positivity theorem in which additive structure pays;
- a proof that no input of a stated class can do any of these, with its positive survivor.

**A contribution:**

1. is unconditional;
2. says what it gives at `0`, at Haar-random points, at twin tails and at the Liouville twin;
3. separates gauge-invariant from gauge-charged content;
4. states its analogue over `𝔽_q`;
5. records the positive survivor of every no-go.

**Battery.**

- the Liouville twin and all prime flips;
- twin tails;
- Haar-random gauge points;
- Dirichlet gauge points;
- vertical shifts;
- `Λ + ε n^{−η}`;
- over-regular Beurling systems;
- the golden curve datum.

**Principles.**

- Identities first, sign last.
- Work at one point.
- Calibrate over `𝔽_q`.
- Selectivity is a theorem.
- A reformulation is not a reduction.
