# Signed Successor Arithmetic (`GaloisForLFunctions.SignedSuccessorArithmetic`)

**One question.** The successor `n ↦ n+1` is the one structure of `ℤ` that a Beurling system does
not have. How does it produce signed cancellation in multiplicative data, at what strength, at a
single scale, and with positivity inherited from a count rather than from analysis?

Signed Successor Arithmetic (SSA) is the quantitative theory of signed multiplicative data along
the successor. Its basic object is a completely multiplicative sign `f` read through its
**successor sign** `σ_f(n) = f(n) f(n+1)`. Its basic identity is the **dilation cocycle**
`∏_{j<m} σ_f(mn + j) = σ_f(n)`, which carries the multiplicative structure onto the successor. Its
basic theorem is the **one-third floor**: every completely multiplicative sign keeps its sign
across at least one third of the steps in logarithmic density, the constant is exact, and the
extremal signs are the conductor-three twins of the quadratic character modulo `3`.

**The open core.** Over a finite field the successor correlation of characters is a count:
`Σ_x χ(x) χ̄(x+1) = −1`, and `|Σ_x χ(x) ψ(x+1)|² = q` when `χ, ψ, χψ` are nontrivial. Signed
cancellation at the square-root scale is there the shadow of an integer. Over `ℤ` the programme has
the density scale (floors, exact identities, quantized biases) and does not have the square-root
scale. The square-root scale is what the walls of the RH frontier ask for; the density scale is
the first rung that is proved.

Everything in the programme is unconditional. No theorem rests on a hypothesis about zeros.

---

## Place in the research

The review `docs/reports/review-2410/fable.md` (§§1–3) reads the corpus's three wall families as
three projections of one missing input: a **signed, single-scale, successor-selective** estimate on
the actual Möbius or prime source at the square-root scale. Every exit the corpus has built (a
rate, a quantized index, a transport in aperture) reduces to this input. The review proposes SSA as
the field that would supply it: not a new reformulation, but a new source of positivity in which
cancellation is a count and the successor is visible in the proof.

| Programme | Interface |
|---|---|
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Sorts every conservation law of the sieve theories into Beurling-universal (Class I), sign-blind (Class II) and Bézout-selective (Class III). Its Class III laws are identities. SSA's floors are Class III laws with a constant. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Owns the successor incidence count `#{k ≤ M : d₁ ∣ k, d₂ ∣ k+1}` with its sawtooth defect in `[−1, 1]`, the least successor seed `pa = qb + 1`, the pronic Gram and the hypercube Dirichlet form. SSA imports the language of counts with defects and states its open topics in these coordinates. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Calibrates over `𝔽_q` and counts the Hodge defect as the number of right zeros. SSA calibrates over `𝔽_q` too, but on the successor side: Jacobi sums are successor correlations. |
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md), [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Orient correspondences and sources by integer-valued invariants (frustration index, orientation index). SSA supplies a different integer: the doubled-agreement count that pays the signed two-scale identity. |
| [Square-Root Threshold](../SquareRootThreshold/README.md), [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Locate every route at the square-root threshold and prove bounded readings blind. They say which scale SSA has to reach. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Owns the coalescent prime surplus, the cleanest additive test bed for a signed correlation tool. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps the Möbius signs through quadratic forms and locates frustration on prime-sum edges. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies the adversarial models (fake curves, shifted pairs, window hiding) that every SSA statement is tested against. |

**Where SSA sits.** The corpus programmes are the receiver side of the frontier: each one reads the
zero width in its own coordinates and proves that its readings are exact. SSA is the source side.
It studies the arithmetic of the signs themselves, with the successor as the structure that a
receiver statement must eventually use. Its proved theorems live at the density scale and at
finite-field scale; its research topics are the routes by which a density-scale law could be
lifted toward the square-root scale.

---

## 1. Why

### 1.1 The walls as questions

Read as questions for which tools are missing, the three wall families of the frontier say:

- **W1.** How does the additive structure of `ℤ` (the successor, Bézout) produce square-root
  cancellation in a *signed* multiplicative sum at a *single* scale? Classical tools average over a
  family (large sieve, Bombieri–Vinogradov, dispersion), are sign-blind (`ℓ²`, period forms), or
  are subpower (Vinogradov–Korobov, Matomäki–Radziwiłł–Tao).
- **W3.** Which observables of the arithmetic source both separate parity twins and carry a
  constant or an exponent? Every amplitude-derived datum is blind; every reading of finite
  resolution has width limit `1/2`.
- **W14.** Is there an arithmetic object whose count is manifest and whose identities reproduce the
  explicit formula? Every identity of Weil's proof holds on impure models; only effectivity, that
  is the sign, is missing.

### 1.2 The three words

*Signed*: the content that sign-blind laws cannot see — the Möbius and Liouville signs, parity, the
orientation of a zero. *Successor*: the structure every Bézout-selective law uses —
`gcd(n, n+1) = 1`, `pa − qb = 1`, `|log(A/B)| ≥ 1/max(A, B)`. *Arithmetic*: positivity inherited
from integers, because the corpus proves that analysis alone is Beurling-universal or sign-blind.

### 1.3 Point of view

1. The integers are the interaction of `×` (divisors, Euler products, characters) and `+1` (the
   successor). RH is a statement about this interaction at the square-root scale.
2. Positivity comes from counting. Analytic positivity (the archimedean place, a zero-free
   region) is a remainder, not a mechanism.
3. One scale and one height. Averaging over heights, characters or moduli loses selectivity.
4. Cofinality. Every statement is a law in a scale parameter.
5. Quantization. Where a deficit is integer-valued, prove rigidity rather than decay.

---

## 2. What: objects and language

### 2.1 Objects

| Object | Meaning | Lean |
|---|---|---|
| Completely multiplicative sign | `f : ℕ → ℤˣ`, `f(1) = 1`, `f(mn) = f(m) f(n)` on positive integers; a group under pointwise product, freely generated by its prime values | `CMSign`, `CMSign.ofPrimes`, `CMSign.liouville` |
| Successor sign | `σ_f(n) = f(n) f(n+1)`: `+1` when the sign is kept across `n → n+1` | `succSign` |
| Dilation cocycle | `∏_{j<m} σ(mn + j) = σ(n)` for all `m, n ≥ 1` | `IsDilationCocycle`, `IsDilationCocycleAt` |
| Reconstruction | `f(n) = ∏_{1 ≤ k < n} σ_f(k)` | `signOfSucc` |
| Agreement indicator, count | `a(n) = [f(n) = f(n+1)]`, `A(N) = Σ_{n ≤ N} a(n)` | `agree`, `agreeCount` |
| Doubled-agreement count | `E_N = #{n ≤ N : a(n) = a(2n) = 1}` — the defect of the two-scale identity | `doubleAgreeCount` |
| Successor correlation | `C(N) = Σ_{n ≤ N} f(n) f(n+1) = 2A(N) − N` | `succCorr` |
| Logarithmic masses | `L(N) = Σ_{n ≤ N} a(n)/n`, `Σ_{n ≤ N} σ_f(n)/n` | `logAgree`, `logSuccCorr` |
| Lag-`h` sign | `σ_h(n) = f(n) f(n+h)`, its agreements and logarithmic mass | `shiftSign`, `agreeAt`, `logAgreeAt` |
| Twins | the completely multiplicative sign equal to a real character off one prime `p` and to `ε` at `p`: conductor three, conductor four, prime conductor | `chi3Twin`, `chi4Twin`, `legTwin` |
| Character successor correlation | `S(χ, ψ) = Σ_{x ∈ F} χ(x) ψ(x+1)` over a finite field | `charSuccCorr` |
| Summatory function of a sign | `M(N) = Σ_{n ≤ N} f(n)` | `signSum` |
| Alternating control | `(−1)^n`, a non-multiplicative sign | `altSign` |

### 2.2 Language

**Counts with defects.** Every statement is an exact identity `count = main term + defect`, with
the defect nonnegative by construction, followed by a classification of when the defect vanishes.
The model is the two-scale identity `A(2N+1) + A(N) = a(1) + N + 2E_N`.

**Currencies.** The programme keeps four scales apart and converts between them explicitly:
natural density (a count per period), logarithmic density (a mass `Σ a(n)/n` against `log N`),
bias (the mean of `σ_f`, a rational number such as `−1/p`), and square-root size (an integer under
a square root, such as `q` in `|S|² = q`).

**Words.**

* *Floor.* A universal lower bound on the agreement density of a class of signs.
* *Twin.* A completely multiplicative sign that agrees with a character away from one prime.
* *Junction.* The two steps of a period adjacent to a multiple of the conductor, where the twin's
  free value `ε f(j)` enters.
* *Bias.* The mean successor sign; for a twin it is fixed by the conductor.
* *Balance.* Zero bias with bounded error; the conductor-four twin has `C(4J) = 0` exactly.
* *Zero defect.* `E_N = 0` for all `N`: the two-scale identity holds with equality at every scale.
* *Odd and even shifts.* Whether the shift `h` is coprime to the dilation `2`; the floor needs it.

---

## 3. How: the pillar theorems

### 3.1 The successor carries the multiplicative structure (`TheSuccessorDilationCocycle`)

1. **Dilation cocycle.** For every completely multiplicative sign, telescoping over the dilated
   block `mn, …, mn+m` gives `∏_{j<m} σ_f(mn + j) = σ_f(n)` (`dilation_cocycle`). The prime values
   cancel (`f(m)² = 1`), so every completely multiplicative sign satisfies the same constraints.
2. **Characterization.** A sign sequence is the successor sign of a completely multiplicative
   sign iff it satisfies the cocycle at every prime dilation (`exists_cmSign_iff_primeCocycle`);
   the prime cocycle implies the full cocycle (`isDilationCocycle_of_prime`), and the sign is
   recovered as `f(n) = ∏_{k<n} σ_f(k)` (`eq_signOfSucc_succSign`, `CMSign.eq_of_succSign`).
   Completely multiplicative signs are exactly the cocycles of the successor.
3. **Group structure.** Signs multiply pointwise, the successor sign is a homomorphism
   (`succSign_mul`), and every sign is `ofPrimes` of its prime values (`CMSign.eq_ofPrimes`).
4. **Pronic law.** For multiplicative (not necessarily completely multiplicative) functions,
   `g(n) g(n+1) = g(n(n+1))` (`pronic_law`): successor correlations are sums over pronic numbers.

### 3.2 The one-third floor (`TheOneThirdSuccessorFloor`)

5. **Per-step doubling count.** The cocycle at `m = 2` is `σ(2n) σ(2n+1) = σ(n)`, equivalently
   `a(2n) + a(2n+1) + a(n) = 1 + 2 a(n) a(2n)` (`agree_doubling`): a flip at `n` forces exactly one
   agreement among `2n, 2n+1`; an agreement at `n` forces the two steps to agree with each other.
6. **Exact two-scale identity.** `A(2N+1) + A(N) = a(1) + N + 2E_N` (`two_scale_identity`), and in
   signed form `C(2N+1) − σ(1) + C(N) = 4E_N − N` (`signed_two_scale_identity`). The defect is four
   times a count.
7. **Natural-density law.** `A(2N+1) + A(N) ≥ N` (`two_scale_floor`): at one of the scales `N`,
   `2N+1` the agreement density is at least one third (`one_third_at_one_of_two_scales`), hence at
   arbitrarily large scales (`frequently_one_third`).
8. **The logarithmic floor.** For every completely multiplicative sign and every `M ≥ 1`,
   `Σ_{n ≤ M, f(n) = f(n+1)} 1/n ≥ (1/3) log M − 1` (`one_third_log_floor`), equivalently
   `Σ_{n ≤ M} f(n) f(n+1)/n ≥ −(1/3) log M − 3` (`neg_third_log_floor`). The constants are absolute.

### 3.3 The floor is attained at conductor three (`TheFloorIsAttainedAtConductorThree`)

9. **Exact count.** The twins `f = χ₃` off `3`, `f(3) = ε`, keep their sign exactly once per period:
   `A(3J+1) = J`, `A(3J+2) = J + [ε f(J+1) = −1]`, `A(3J+3) = J + 1`
   (`agreeCount_chi3Twin_three_mul_add_one`, `…_add_two`, `…_add_three`), so
   `N ≤ 3A(N) + 2` and `3A(N) ≤ N + 1` (`agreeCount_chi3Twin_bounds`).
10. **Zero defect.** No `n` has `a(n) = a(2n) = 1` (`doubleAgreeCount_chi3Twin`); the signed
    two-scale identity holds with equality at every scale,
    `C(2N+1) + C(N) = −1 − N` (`signed_two_scale_identity_chi3Twin`).
11. **Sharpness.** The twins have logarithmic agreement mass `≤ (1/3) log M + 1`
    (`logAgree_chi3Twin_le`); with item 8 this is `one_third_floor_sharp`: the floor constant is
    exactly `1/3`.
12. **The extremal and Liouville.** The twin with `ε = −1` agrees with `λ` at `2, 3, 5` and first
    differs at `7` (`chi3Twin_neg_one_vs_liouville`). Complete multiplicativity and the prime values
    below `7` cannot move the successor floor of `λ` above `1/3`.

### 3.4 Square-root cancellation is a count: calibration over `𝔽_q` (`SquareRootCancellationIsACount`)

13. **The successor correlation is a Jacobi sum.** `S(χ, ψ) = χ(−1) J(χ, ψ)`
    (`charSuccCorr_eq_jacobiSum`).
14. **Perfect cancellation.** `S(χ, χ⁻¹) = −1` for nontrivial `χ` (`charSuccCorr_inv`); for the
    quadratic character `Σ_x χ(x) χ(x+1) = −1` (`quadraticChar_succCorr`), equivalently the exact
    agreement count `2·#{x : χ(x) χ(x+1) = 1} + 3 = q` (`two_mul_card_quadratic_succ_agree_add_three`).
15. **Square root as an integer.** For complex characters with `χ, ψ, χψ` nontrivial,
    `|S(χ, ψ)|² = q` (`norm_sq_charSuccCorr`).

### 3.5 The successor bias is quantized by the conductor (`TheSuccessorBiasIsQuantizedByTheConductor`)

16. **Exact identity of a Legendre twin.** For an odd prime `p` and the twin `f = χ_p` off `p`,
    `f(p) = ε`, each period contributes `−1` from its interior steps (item 14) and
    `(1 + χ(−1)) ε f(j+1)` from its junction, so
    `C(pJ) = −J + (1 + χ(−1)) ε M(J)` (`succCorr_legTwin`, `block_succCorr_legTwin`).
17. **Exact law for `p ≡ 3 (mod 4)`.** The junction cancels: `C(pJ) = −J`
    (`succCorr_legTwin_of_three_mod_four`).
18. **Quantized bias.** The summatory function is self-similar, `M(pJ) = ε M(J)`
    (`signSum_legTwin_prime_mul`), so `|M(N)| ≤ p(log_p N + 1)` (`abs_signSum_legTwin_le`) and
    `|C(pJ) + J| ≤ 2p(log_p J + 1)` (`abs_succCorr_legTwin_add_le`): the mean successor sign of the
    prime-conductor twin is `−1/p`. The one-third floor is its value at `p = 3`.

### 3.6 The floor reads the parity of the shift (`TheFloorReadsTheParityOfTheShift`)

19. **Lag-`h` cocycle.** `∏_{j<m} σ_h(mn + jh) = σ_h(n)` (`shift_dilation_cocycle`), with the same
    per-step doubling count (`agreeAt_doubling`).
20. **Odd shifts keep the floor.** For odd `h` the positions `2n` and `2n+h` are disjoint and fill
    `[1, 2N+h]`, and `Σ_{n ≤ M, f(n) = f(n+h)} 1/n ≥ (1/3) log M − (h+1)` (`odd_shift_log_floor`).
21. **Even shifts break it.** The conductor-four twins disagree at every odd position for `h = 2`
    (`agreeAt_chi4Twin_two_odd`), are perfectly balanced along the successor, `C(4J) = 0`
    (`succCorr_chi4Twin_four_mul`), and have lag-two mass `≤ (1/4) log M + 1`
    (`chi4Twin_lag_two_log_le`). Lag two at even positions is lag one at half the position for every
    sign (`agreeAt_two_two_mul`), so every sign has lag-two mass `≥ (1/6) log M − 1`
    (`lag_two_log_floor`). The lag-two floor lies in `[1/6, 1/4]` (`lag_two_bracket`).
22. **The alternating control.** `(−1)^n` flips at every step (`alternating_succSign`,
    `alternating_logAgree`) and violates the cocycle (`alternating_not_cocycle`): the floor is a
    property of `×` and `+1` together.

---

## 4. Mechanisms

* **Telescoping along a dilated block.** `f(mn) f(m(n+1)) = σ_f(n)`, written as a product of
  successor signs over the block. Every SSA identity begins here.
* **Doubling count.** At `m = 2` the cocycle becomes a statement about three bits; summed over `n`
  it is an exact identity whose defect is a count.
* **Interleaving.** A floor needs the dilated positions to tile the range without overlap: `2n` and
  `2n+h` are disjoint exactly when `h` is odd, that is when `2a − hb = 1` is solvable. This is
  where Bézout enters the proof.
* **Junction bookkeeping.** For a twin of conductor `p`, the interior of each period is a finite-field
  sum, computed exactly; the two steps adjacent to `p(j+1)` carry the twin's free value and
  contribute a term proportional to the twin's own summatory function.
* **Self-similarity.** `M(pJ) = ε M(J)` turns the junction term into a logarithmic error.
* **Jacobi sums.** A successor correlation of characters is a Jacobi sum; its modulus squared is
  the cardinality of the field.

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| The floor is a form of Chowla's conjecture | It is a universal density-scale lower bound over all completely multiplicative signs, and it is attained: the extremal signs are pretentious (conductor-three twins). Chowla for `λ` says the bias of `λ` is `0`; the floor says no sign has bias below `−1/3`. |
| The cocycle constrains the prime values | The prime values cancel out of it (`f(m)² = 1`). The cocycle characterizes complete multiplicativity, not a particular sign; the values live in initial segments of `σ_f`. |
| Any shift gives the same floor | Odd shifts do; even shifts do not. The conductor-four twin has lag-two density `1/4 < 1/3`. |
| A bias of `−1/p` is a failure of cancellation | It is the main term of a pretentious sign, quantized by the conductor. Over the field `𝔽_p` the same periods cancel perfectly (`−1` per period). |
| Finite-field square-root cancellation transfers to `ℤ` | The calibration is about complete periods of characters. Along `ℤ`, periodic data acquire junctions, and twins carry a nonzero bias. Square-root size over `ℤ` is the open core. |
| A density-scale law reaches the receivers | The corpus's receivers read the zero width at rate `1/2` and need square-root-scale signed estimates. A density law with an absolute constant does not produce a zero-free region. |
| An exact identity with a count defect is a bound | It is an identity. Its value is that the defect is nonnegative by construction and that its vanishing is classifiable (zero defect at conductor three). |
| `ℤˣ`-valued powers behave like monoid powers in Lean | `(u : ℤˣ) ^ (k : ℕ)` elaborates through `Int.instUnitsPow`, which `pow_add` and `pow_one` do not match syntactically. Use term-mode `pow_add ε _ _` with `exact`, or parity definitions. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **How do `×` and `+1` interact on signs?** Through the dilation cocycle, which characterizes
   complete multiplicativity, is generated by the primes, and does not contain the prime values
   (§3.1).
2. **Does the successor force positivity on multiplicative signs, unconditionally, and how much?**
   Yes, at density scale: the one-third floor, with an exact identity whose defect is a count, the
   exact constant `1/3`, and extremals at conductor three with zero defect (§§3.2–3.3).
3. **Is successor bias quantized?** For prime-conductor twins the mean successor sign is `−1/p`,
   exactly for `p ≡ 3 (mod 4)` and with a logarithmic error in general; over `𝔽_q` the successor
   correlation is `−1` for an inverse pair and has modulus `√q` otherwise (§§3.4–3.5).
4. **Which structure of `ℤ` does a successor law use?** The Bézout relation between the dilation and
   the shift (odd shifts keep the floor, even shifts lose it) together with multiplicativity (the
   alternating sign has no floor) (§3.6).
5. **What does square-root cancellation look like when it is a count?** Over `𝔽_q`: `|S|² = q`, a
   Jacobi-sum identity. Over `ℤ`: open; it is wall W1.
6. **Can a successor law see `λ` beyond its pretentious neighbour?** Not with the cocycle and the
   prime values below `7`; beyond that, open (§7).

### 6.2 Tools

Built and reusable:

- *The successor sign calculus*: completely multiplicative signs as a group, prime-value
  constructors, successor and lag-`h` signs, telescoping along dilated blocks and progressions,
  the cocycle characterization and reconstruction.
- *Counts with defects*: agreement and doubled-agreement counts, the exact two-scale identity, the
  splitting of `[1, 2N+1]` into pairs, the interleaving inequality for odd shifts.
- *Logarithmic floors*: harmonic comparison lemmas, the one-third floor, the odd-shift floor, the
  lag-two floor.
- *Twin constructions*: conductor three, conductor four and prime-conductor twins with their exact
  successor patterns and junctions.
- *Finite-field calibration*: successor correlations as Jacobi sums, perfect cancellation, the
  consecutive-residue count, the square-root identity.
- *Periodic bookkeeping*: block sums over periods, the Legendre symbol on `ℕ` with periodicity, the
  self-similar summatory function and its logarithmic bound.

To build:

- *Spectral form of dilation Gram matrices*: the Mellin representation of the dilation profile, so
  that hypercube forms become integrals of partial Euler products against a spectral weight (§7,
  topic 3).
- *Prime windows*: lower bounds for `Σ_{x < p ≤ λx} p^{−σ}` from the corpus's prime number theorem
  with error (`RHTower.Sieve.chebyshevTheta_sub_id_isBigO`, `PNTPlus.chebyshev_asymptotic`).
- *Kloosterman calibration*: second moments of Kloosterman sums as exact counts.

---

## 7. Open research topics

1. **Break the conductor-three floor for `λ`.** The extremal twin agrees with `λ` below `7`. A
   successor law that uses `λ(p) = −1` at infinitely many primes `p ≡ 1 (mod 3)` must separate `λ`
   from every conductor-three twin. Target: `Σ_{n ≤ M, λ(n) = λ(n+1)} 1/n ≥ (1/3 + c) log M − C` for
   some `c > 0`, with a proof that names the successor input.
2. **The square-root scale over `ℤ` (W1).** A signed successor estimate for `λ` or `μ` with a power
   saving at one scale. Its first output in receiver coordinates must be a zero-free strip, and the
   statement must say which one.
3. **The hypercube Dirichlet form (fable §3.8, topic 3; BVI §7.5).** The form
   `Σ_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁d₂)^{−1/2−ε} Φ_r(d₁/d₂)` is `‖Σ_{d ∣ P} μ(d) d^{−1/2−ε} D_{1/d} v‖²` for
   the normalized dilations `D`. In the Mellin coordinate it is
   `∫ w(τ) ∏_{p ∣ P} |1 − p^{−σ+iτ}|² dτ` with `σ = 1/2 + ε` and `w = |v̂|² ≥ 0`. For `σ < 1` the
   partial Euler product over a window of primes `x < p ≤ λx` grows like
   `exp(c x^{1−σ}/log x)` on the heights where the phases `p^{iτ}` align, and the prime number
   theorem makes the alignment coherent across the window: the coherence is the pole of `ζ` at `1`,
   not its zeros. The topic is to prove that the form is unbounded in `P` for every `0 < ε < 1/2`,
   unconditionally, and to identify the size-truncated replacement that carries the successor
   input.
4. **Classify the zero-defect signs.** Which completely multiplicative signs satisfy
   `a(n) = 1 ⇒ a(2n) = 0` for all `n`? The conductor-three twins do. The branch with `f(2) = 1` is
   forced through `f(3) = f(5) = f(7) = −1`, `f(11) = f(13) = 1`, `f(19) = 1`, and does not match a
   character of small conductor.
5. **Lag floors.** The lag-two floor lies in `[1/6, 1/4]`. Determine it, and determine the floor for
   odd shifts divisible by `3`, where the conductor-three twin agrees at two thirds of the steps.
6. **The complex floor.** For completely multiplicative `f` with values on the unit circle and
   `σ_f(n) = f̄(n) f(n+1)`, the binary cocycle gives a floor `−1/2` for the logarithmic mean of
   `Re σ_f`; the configuration that would attain it is inconsistent with complete
   multiplicativity at `9`. The true floor lies in `[−1/2, −1/3]`.
7. **From `λ` to `μ`.** `μ = λ · μ²`, and the squarefree restriction breaks the cocycle
   (`μ(2n) = 0` for even `n`). Find the successor calculus of squarefree-supported signs.
8. **The index exit (fable §2.3 C, topic 6).** The doubled-agreement count `E_N` is a count that pays
   a signed identity and vanishes exactly at the extremals. An arithmetic count that pays the Hodge
   defect of the scaling surface in the same way would force the defect to zero. Find the
   counterpart.
9. **Kloosterman reciprocity (topic 2).** Calibrate the balanced cross-scale Gram over `𝔽_p`: the
   Kloosterman form is the successor correlation of additive and multiplicative characters.
10. **Witt structure (topic 10).** Decide whether Frobenius and Verschiebung on ghost coordinates
    supply a successor law, or whether they are Beurling-universal.

---

## 8. Success criteria and contributions

**The programme succeeds** when it proves a signed successor estimate at the square-root scale for
an arithmetic source over `ℤ` whose first output in receiver coordinates is a stated zero-free
strip, or when it proves that a stated class of successor laws cannot reach that scale, with the
strongest positive survivor recorded.

**A contribution must**

* be an unconditional Lean theorem in this folder, wired into the umbrella;
* be exact where the mathematics is exact: an identity with a signed defect, not an inequality with
  an absorbed constant;
* use the successor visibly, and say where (a block, a junction, an interleaving, a solution of
  `pa − qb = h`);
* state what it gives for the control group: the alternating sign, the twins of small conductor,
  the parity twin `f ≡ 1`, and, where it applies, Beurling systems and finite-field models;
* name its scale (density, logarithmic, bias, square root) and convert explicitly between scales;
* record the positive survivor of every no-go.

---

## 9. Principles

1. **Selectivity.** A statement that holds verbatim for a Beurling system, a parity twin or the
   alternating sign cannot close the frontier. Test before proving.
2. **Successor.** The additive input must be visible in the proof.
3. **Integrality.** Positivity is inherited from a count; analytic positivity is a remainder.
4. **Single scale.** No averaging over heights, characters or moduli in the statement.
5. **Cofinality.** Every result is a law in a scale parameter.
6. **Quantization.** Where a deficit is integer-valued, prove rigidity rather than decay.
7. **Exactness.** Identity before asymptotics; keep boundary terms and signed defects.
8. **Calibrate over `𝔽_q`.** State the finite-field form of every law first.
9. **Search the corpus first**: `scripts/formal_tools.py research "<query>"`.

---

## Source entry points

| Module | Content |
|---|---|
| `TheSuccessorDilationCocycle` | completely multiplicative signs, Liouville, prime-value construction; successor signs, telescoping, the dilation cocycle, characterization by prime cocycles, reconstruction; pronic law |
| `TheOneThirdSuccessorFloor` | agreement and doubled-agreement counts, the per-step doubling count, the exact two-scale identity in counting and signed form, natural-density and logarithmic one-third floors |
| `TheFloorIsAttainedAtConductorThree` | conductor-three twins, exact agreement counts, zero doubling defect, sharpness of `1/3`, comparison with `λ` |
| `SquareRootCancellationIsACount` | successor correlations of characters as Jacobi sums, perfect cancellation, the consecutive-residue count, `|S|² = q` |
| `TheSuccessorBiasIsQuantizedByTheConductor` | Legendre symbol on `ℕ`, prime-conductor twins, block sums, the exact identity `C(pJ) = −J + (1 + χ(−1)) ε M(J)`, `p ≡ 3 (mod 4)`, self-similar summatory functions, bias `−1/p` |
| `TheFloorReadsTheParityOfTheShift` | lag-`h` signs and cocycle, the odd-shift floor, conductor-four twins with perfect balance, the lag-two bracket `[1/6, 1/4]`, the alternating control |
