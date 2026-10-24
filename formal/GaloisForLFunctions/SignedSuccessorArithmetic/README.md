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
the density scale (floors, exact identities, quantized biases and deficits) and does not have the
square-root scale. The square-root scale is what the walls of the RH frontier ask for; the density
scale is the first rung that is proved.

**A correction to the frontier.** The hypercube Dirichlet form of Bézout–Valuation Incidence, whose
uniform bound for `0 < ε ≤ 1/2` was listed as an open entry point of the successor input, is
unbounded for every `−1/2 ≤ ε < 1/2`, unconditionally (§3.7). Its threshold is the abscissa of
absolute convergence of the Euler product, set by the pole of `ζ` and not by its zeros.

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
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Owns the successor incidence count with its sawtooth defect, the least successor seed, the pronic Gram and the hypercube Dirichlet form. SSA settles the hypercube form below half damping (§3.7) and calibrates the balanced cross-scale Gram over `𝔽_q` (§3.8). |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Calibrates over `𝔽_q` and counts the Hodge defect as the number of right zeros. SSA calibrates over `𝔽_q` too, but on the successor side: Jacobi and Kloosterman sums are successor correlations. |
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md), [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Orient correspondences and sources by integer-valued invariants. SSA supplies a different integer: the doubled-agreement count, which pays the signed two-scale identity and quantizes its deficit (§3.10). |
| [Square-Root Threshold](../SquareRootThreshold/README.md), [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Locate every route at the square-root threshold and prove bounded readings blind. They say which scale SSA has to reach. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Owns the coalescent prime surplus, the cleanest additive test bed for a signed correlation tool. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Keeps the Möbius signs through quadratic forms and locates frustration on prime-sum edges. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies the adversarial models (fake curves, shifted pairs, window hiding) that every SSA statement is tested against. |

`RHTower` supplies the prime number theorem with error term (`RHTower.Sieve.chebyshevTheta_sub_id_isBigO`,
and `chebyshev_asymptotic` in `PNTPlus/Consequences`), the Sonin space with its dilation group, and
the Ramanujan step vectors. `HTGeometry` supplies the half-line Mellin unitary
(`HTGeometry.halfLineMellinUnitary`) under which dilations become modulations.

**Where SSA sits.** The corpus programmes are the receiver side of the frontier: each one reads the
zero width in its own coordinates and proves that its readings are exact. SSA is the source side.
It studies the arithmetic of the signs themselves, with the successor as the structure that a
receiver statement must eventually use. Its proved theorems live at the density scale and at
finite-field scale; it also tests proposed entry points of the successor input against the
structure of the primes, and the hypercube form fails that test for a reason unrelated to zeros.

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
| Doubled-agreement count | `E_N = #{n ≤ N : a(n) = a(2n) = 1}`, the defect of the two-scale identity | `doubleAgreeCount` |
| Successor correlation | `C(N) = Σ_{n ≤ N} f(n) f(n+1) = 2A(N) − N` | `succCorr` |
| Two-scale deficit | `D_N = C(2N+1) − σ(1) + C(N) + N = 4E_N` | `twoScaleDeficit` |
| Zero defect | `E_N = 0` for all `N` | `ZeroDefect` |
| Logarithmic masses | `L(N) = Σ_{n ≤ N} a(n)/n`, `Σ_{n ≤ N} σ_f(n)/n` | `logAgree`, `logSuccCorr` |
| Lag-`h` sign | `σ_h(n) = f(n) f(n+h)`, its agreements and logarithmic mass | `shiftSign`, `agreeAt`, `logAgreeAt` |
| Unimodular sign | completely multiplicative `f : ℕ → ℂ`, `|f| = 1`, with phase `σ(n) = f̄(n) f(n+1)` | `CMUnit`, `unitSuccPhase`, `logUnitCorr` |
| Twins | the completely multiplicative sign equal to a real character off one prime `p` and to `ε` at `p`: conductor three, conductor four, prime conductor | `chi3Twin`, `chi4Twin`, `legTwin` |
| Character successor correlation | `S(χ, ψ) = Σ_{x ∈ F} χ(x) ψ(x+1)` over a finite field | `charSuccCorr` |
| Kloosterman sum | `K(a, b) = Σ_{x ≠ 0} ψ(ax + b x⁻¹)` | `kloosterman` |
| Summatory function of a sign | `M(N) = Σ_{n ≤ N} f(n)` | `signSum` |
| Squared Euler factor and product | `|1 − p^{−σ} e^{iτ log p}|²` and its product over a finite set of primes | `eulerFactorSq`, `eulerProductSq` |
| Prime window | the primes in `(x, λx]` | `primeWindow` |
| Spectral weight of the step vector | `W(ξ) = |𝓜(v|₊)(ξ)|²` for the Ramanujan step vector `v` | `stepSpectralWeight` |
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
* *Aligned window.* A window of primes `(x, λx]` and a short interval of heights on which every
  phase `τ log p` stays near `π` modulo `2π`.
* *Pole-driven divergence.* Growth of a partial Euler product forced by the coherent distribution of
  the primes (the prime number theorem), present whatever the zeros of `ζ` are.

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
4. **Pronic law.** For multiplicative functions, `g(n) g(n+1) = g(n(n+1))` (`pronic_law`):
   successor correlations are sums over pronic numbers.

### 3.2 The one-third floor (`TheOneThirdSuccessorFloor`)

5. **Per-step doubling count.** The cocycle at `m = 2` is `σ(2n) σ(2n+1) = σ(n)`, equivalently
   `a(2n) + a(2n+1) + a(n) = 1 + 2 a(n) a(2n)` (`agree_doubling`): a flip at `n` forces exactly one
   agreement among `2n, 2n+1`; an agreement at `n` forces the two steps to agree with each other.
6. **Exact two-scale identity.** `A(2N+1) + A(N) = a(1) + N + 2E_N` (`two_scale_identity`), and in
   signed form `C(2N+1) − σ(1) + C(N) = 4E_N − N` (`signed_two_scale_identity`).
7. **Natural-density law.** `A(2N+1) + A(N) ≥ N` (`two_scale_floor`): at one of the scales `N`,
   `2N+1` the agreement density is at least one third (`one_third_at_one_of_two_scales`), hence at
   arbitrarily large scales (`frequently_one_third`).
8. **The logarithmic floor.** For every completely multiplicative sign and every `M ≥ 1`,
   `Σ_{n ≤ M, f(n) = f(n+1)} 1/n ≥ (1/3) log M − 1` (`one_third_log_floor`), equivalently
   `Σ_{n ≤ M} f(n) f(n+1)/n ≥ −(1/3) log M − 3` (`neg_third_log_floor`). The constants are absolute.

### 3.3 The floor is attained at conductor three (`TheFloorIsAttainedAtConductorThree`)

9. **Exact count.** The twins `f = χ₃` off `3`, `f(3) = ε`, keep their sign exactly once per period:
   `A(3J+1) = J`, `A(3J+2) = J + [ε f(J+1) = −1]`, `A(3J+3) = J + 1`
   (`agreeCount_chi3Twin_three_mul_add_one`, `…_add_two`, `…_add_three`).
10. **Zero defect.** No `n` has `a(n) = a(2n) = 1` (`doubleAgreeCount_chi3Twin`); the signed
    two-scale identity holds with equality at every scale,
    `C(2N+1) + C(N) = −1 − N` (`signed_two_scale_identity_chi3Twin`).
11. **Sharpness.** The twins have logarithmic agreement mass `≤ (1/3) log M + 1`
    (`logAgree_chi3Twin_le`); with item 8 this is `one_third_floor_sharp`.
12. **The extremal and Liouville.** The twin with `ε = −1` agrees with `λ` at `2, 3, 5` and first
    differs at `7` (`chi3Twin_neg_one_vs_liouville`).

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
18. **Quantized bias.** `M(pJ) = ε M(J)` (`signSum_legTwin_prime_mul`), so
    `|M(N)| ≤ p(log_p N + 1)` (`abs_signSum_legTwin_le`) and `|C(pJ) + J| ≤ 2p(log_p J + 1)`
    (`abs_succCorr_legTwin_add_le`): the mean successor sign of the prime-conductor twin is `−1/p`.

### 3.6 The floor reads the parity of the shift (`TheFloorReadsTheParityOfTheShift`)

19. **Lag-`h` cocycle.** `∏_{j<m} σ_h(mn + jh) = σ_h(n)` (`shift_dilation_cocycle`), with the same
    per-step doubling count (`agreeAt_doubling`).
20. **Odd shifts keep the floor.** `Σ_{n ≤ M, f(n) = f(n+h)} 1/n ≥ (1/3) log M − (h+1)` for odd `h`
    (`odd_shift_log_floor`): the positions `2n` and `2n+h` are disjoint and fill `[1, 2N+h]`.
21. **Even shifts break it.** The conductor-four twins disagree at every odd position for `h = 2`
    (`agreeAt_chi4Twin_two_odd`), are perfectly balanced along the successor, `C(4J) = 0`
    (`succCorr_chi4Twin_four_mul`), and have lag-two mass `≤ (1/4) log M + 1`
    (`chi4Twin_lag_two_log_le`); every sign has lag-two mass `≥ (1/6) log M − 1`
    (`lag_two_log_floor`). The lag-two floor lies in `[1/6, 1/4]` (`lag_two_bracket`).
22. **The alternating control.** `(−1)^n` flips at every step (`alternating_succSign`,
    `alternating_logAgree`) and violates the cocycle (`alternating_not_cocycle`).

### 3.7 The hypercube Dirichlet form is unbounded below half damping (`PartialEulerProductsDivergeInTheStrip`, `TheSpectralHypercubeFormIsUnbounded`, `TheHypercubeDirichletFormIsUnbounded`)

Bézout–Valuation Incidence defines
`Q_ε(P) = Σ_{d₁, d₂ ∣ P} μ(d₁) μ(d₂) (d₁ d₂)^{−1/2−ε} Φ_r(d₁/d₂)` with `Φ_r(c) = Re⟨v, D_c v⟩` for the
Ramanujan step vector `v`, proves it nonnegative, and bounds it uniformly in squarefree `P` for
`ε > 1/2`.

23. **Aligned prime windows.** For `0 ≤ σ < 1`, a height `τ₀ > 0` and `x` large, the primes in
    `(x, λx]` with `λ = exp(1/(10(τ₀+1)))` all have `cos(τ log p) ≤ −1/2` on a ball of radius
    `ρ = 1/(10 log λx)` around an aligned height `(2πj + π)/log x` within `40πρ` of `τ₀`
    (`cos_le_of_aligned`, `eventually_aligned`). The prime number theorem puts
    `θ(λx) − θ(x) ≥ (λ − 1)x/2` in the window (`eventually_theta_window_ge`), so
    `ρ ∏_p |1 − p^{−σ+iτ}|² ≥ M` on that ball (`exists_aligned_window`).
24. **The spectral hypercube form diverges.** For every integrable `w ≥ 0` with
    `∫_{(0,∞)} w > 0`, `∫ w(τ) ∏_{p ∈ S} |1 − p^{−σ+iτ}|² dτ` is unbounded over finite sets of primes
    (`spectralHypercube_unbounded_of_integrable`); no regularity of `w` is used, by the Lebesgue
    differentiation theorem along non-centred balls.
25. **Spectral form of the profile.** `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ` with `W = |𝓜(v|₊)|²` and
    `∫ W = Φ_r(1) > 0` (`dilationProfile_eq_integral`, `integral_stepSpectralWeight_pos`).
26. **Divisor expansion.** For `P = ∏_{p ∈ S} p`,
    `Σ_{d₁,d₂ ∣ P} μ(d₁)μ(d₂)(d₁d₂)^{−σ} cos(θ log(d₁/d₂)) = ∏_{p ∈ S} |1 − p^{−σ}e^{iθ log p}|²`
    (`hypercube_cos_sum_eq_eulerProductSq`), hence
    `Q_ε(P) = ∫ W(ξ) ∏_{p ∈ S} |1 − p^{−1/2−ε+2πiξ}|² dξ` (`hypercubeDilationDirichletForm_eq_integral`).
27. **The hypercube Dirichlet form is unbounded.** For `−1/2 ≤ ε < 1/2` and every `r > 1`,
    `sup_P Q_ε(P) = ∞` over squarefree `P` (`hypercubeDilationDirichletForm_unbounded`). With the
    bound for `ε > 1/2` the threshold is the abscissa of absolute convergence. The divergence is
    driven by the prime number theorem, that is by the pole of `ζ`, not by its zeros.

### 3.8 The Kloosterman second moment is a count (`TheKloostermanSecondMomentIsACount`)

28. **Square root on average, exactly.** `Σ_{a ∈ F} |K(a, b)|² = q(q − 1)` for a primitive additive
    character (`sum_normSq_kloosterman`); `K(0, b) = −1` for `b ≠ 0` (`kloosterman_zero_left`), so
    `Σ_{a ≠ 0} |K(a, b)|² = q² − q − 1` (`sum_normSq_kloosterman_ne_zero`). The pointwise bound `2√q`
    is Weil's theorem; the mean square is orthogonality in `a`, which keeps only the diagonal.

### 3.9 The complex successor floor (`TheComplexSuccessorFloor`)

29. **Two unit vectors.** `(Re u + Re v)² ≤ 2(1 + Re(uv))` for `|u| = |v| = 1` (`sq_re_add_re_le`),
    so the cocycle `σ(2n)σ(2n+1) = σ(n)` (`unitSuccPhase_two_mul_mul`) forces
    `Re σ(2n) + Re σ(2n+1) ≥ −√(2(1 + Re σ(n)))` (`re_two_mul_add_re_ge`).
30. **The complex floor.** For a completely multiplicative `f` of modulus one,
    `Σ_{n ≤ M} Re(f̄(n) f(n+1))/n ≥ −(1/2) log M − 3` (`complex_log_floor`), by Cauchy–Schwarz on the
    logarithmic sum (`sum_sqrt_le`). Signs are unimodular functions (`CMSign.toCMUnit`), and the
    conductor-three twins have `≤ −(1/3) log M + 2`, so the complex floor lies in `[−1/2, −1/3]`
    (`complex_floor_bracket`).
31. **Catalan's pair.** The value `−1/2` would need `f` with values in the cube roots of unity and
    distinct consecutive values. That fails by `9 = 8 + 1`: distinctness up to `4` forces `f(3) = 1`,
    so `f(9) = f(3)² = 1 = f(2)³ = f(8)` (`no_cubeRoot_successor_coloring`).

### 3.10 The two-scale deficit is quantized (`TheTwoScaleDeficitIsQuantized`)

32. **Quantization.** `D_N = 4E_N` (`twoScaleDeficit_eq`); `D_N < 4` iff there is no doubled
    agreement up to `N` (`twoScaleDeficit_lt_four_iff`).
33. **Zero defect is equality.** A sign has zero defect iff `C(2N+1) − σ(1) + C(N) = −N` at every
    scale (`zeroDefect_iff`); the conductor-three twins have it (`zeroDefect_chi3Twin`).
34. **Zero defect forces the floor.** A zero-defect sign has `Σ_{n ≤ M} a(n)/n ≤ (1/3) log M + 2`
    (`logAgree_le_of_zeroDefect`): zero-defect signs are extremal for the one-third floor.
35. **A second branch.** Zero defect with `f(2) = 1` forces `f(3) = f(5) = f(7) = −1` and
    `f(11) = f(13) = 1` (`zeroDefect_of_two_eq_one`), a pattern no conductor-three twin has.

---

## 4. Mechanisms

* **Telescoping along a dilated block.** `f(mn) f(m(n+1)) = σ_f(n)`, written as a product of
  successor signs over the block. Every SSA identity begins here.
* **Doubling count.** At `m = 2` the cocycle becomes a statement about three bits; summed over `n`
  it is an exact identity whose defect is a count.
* **Interleaving.** A floor needs the dilated positions to tile the range without overlap: `2n` and
  `2n+h` are disjoint exactly when `h` is odd, that is when `2a − hb = 1` is solvable.
* **Junction bookkeeping.** For a twin of conductor `p`, the interior of each period is a
  finite-field sum, computed exactly; the two steps adjacent to `p(j+1)` carry the twin's free value.
* **Self-similarity.** `M(pJ) = ε M(J)` turns the junction term into a logarithmic error.
* **Jacobi and Kloosterman sums.** Successor correlations of characters are Jacobi sums; the
  second moment of Kloosterman sums is orthogonality.
* **Cauchy–Schwarz on the logarithmic sum.** It converts the pointwise complex bound into a floor.
* **Phase alignment on prime windows.** On `(x, λx]` the phases `τ log p` move together; the prime
  number theorem fills the window, and the product of factors `≥ 1 + p^{−σ}` grows like
  `exp(c x^{1−σ}/log x)` on an interval of heights of length `≍ 1/log x`.
* **Spectral transport.** The half-line Mellin unitary turns dilations into modulations, so a
  dilation Gram form is an integral of `|Dirichlet polynomial|²` against a spectral weight.

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| The floor is a form of Chowla's conjecture | It is a universal density-scale lower bound over all completely multiplicative signs, and it is attained by pretentious signs. Chowla for `λ` says the bias of `λ` is `0`; the floor says no sign has bias below `−1/3`. |
| The cocycle constrains the prime values | The prime values cancel out of it. The cocycle characterizes complete multiplicativity, not a particular sign. |
| Any shift gives the same floor | Odd shifts do; even shifts do not. The conductor-four twin has lag-two density `1/4 < 1/3`. |
| A bias of `−1/p` is a failure of cancellation | It is the main term of a pretentious sign, quantized by the conductor. Over `𝔽_p` the same periods cancel perfectly. |
| Finite-field square-root cancellation transfers to `ℤ` | The calibration is about complete periods of characters. Along `ℤ`, periodic data acquire junctions, and twins carry a nonzero bias. |
| A density-scale law reaches the receivers | The receivers read the zero width at rate `1/2` and need square-root-scale signed estimates. A density law with an absolute constant does not produce a zero-free region. |
| Cross-depth cancellation of the hypercube form is a quasi-RH statement | It is false for every `ε < 1/2`, unconditionally. A Dirichlet polynomial truncated by prime support is a partial Euler product, which diverges in `1/2 < σ < 1` because of the pole. Only size truncation can carry information about zeros. |
| Divergence of partial Euler products needs a smooth spectral weight | Any integrable weight with positive mass on one side works; Lebesgue differentiation along the shrinking aligned intervals replaces continuity. |
| The complex floor equals the real floor | The cocycle argument gives `−1/2` for unimodular signs; the real floor is `−1/3`; the true complex floor is not known. |
| `ℤˣ`-valued powers behave like monoid powers in Lean | `(u : ℤˣ) ^ (k : ℕ)` elaborates through `Int.instUnitsPow`, which `pow_add` does not match syntactically. Use term-mode `pow_add ε _ _` with `exact`, or parity definitions. |
| `open RHTower` inside the package namespace opens the corpus root namespace | Inside `GaloisForLFunctions` it resolves to `GaloisForLFunctions.RHTower`. Use `open _root_.RHTower`. |

---

## 6. Questions the programme answers and the tools it builds

### 6.1 Questions

1. **How do `×` and `+1` interact on signs?** Through the dilation cocycle, which characterizes
   complete multiplicativity, is generated by the primes, and does not contain the prime values
   (§3.1).
2. **Does the successor force positivity on multiplicative signs, unconditionally, and how much?**
   Yes, at density scale: the one-third floor, with an exact identity whose defect is a count, the
   exact constant `1/3`, and extremals at conductor three with zero defect (§§3.2–3.3, 3.10).
3. **Is successor bias quantized?** For prime-conductor twins the mean successor sign is `−1/p`;
   over `𝔽_q` the successor correlation is `−1` for an inverse pair and has modulus `√q` otherwise;
   the two-scale deficit is four times a count (§§3.4, 3.5, 3.10).
4. **Which structure of `ℤ` does a successor law use?** The Bézout relation between the dilation and
   the shift, together with multiplicativity (§3.6).
5. **What does square-root cancellation look like when it is a count?** Over `𝔽_q`: `|S|² = q` for
   Jacobi sums and `Σ_a |K(a, b)|² = q(q − 1)` for Kloosterman sums. Over `ℤ`: open; it is wall W1.
6. **Is cross-depth cancellation of the hypercube form an entry point of the successor input?** No.
   The form is unbounded for every `−1/2 ≤ ε < 1/2`, for a reason that does not involve the zeros
   (§3.7). The entry point has to be a size-truncated form.
7. **Do the floors survive complex values?** Yes with constant `−1/2`; the exact complex constant is
   open in `[−1/2, −1/3]`, and the configuration that would reach `−1/2` dies at Catalan's pair
   (§3.9).
8. **Can a successor law see `λ` beyond its pretentious neighbour?** Not with the cocycle and the
   prime values below `7`; beyond that, open (§7).

### 6.2 Tools

Built and reusable:

- *The successor sign calculus*: completely multiplicative signs as a group, prime-value
  constructors, successor and lag-`h` signs, telescoping along dilated blocks and progressions,
  the cocycle characterization and reconstruction; unimodular signs and their phases.
- *Counts with defects*: agreement and doubled-agreement counts, the exact two-scale identity and
  its quantized deficit, the splitting of `[1, 2N+1]` into pairs, the interleaving inequality.
- *Logarithmic floors*: harmonic comparison lemmas, the one-third, odd-shift, lag-two and complex
  floors.
- *Twin constructions*: conductor three, conductor four and prime-conductor twins with their exact
  successor patterns and junctions.
- *Finite-field calibration*: successor correlations as Jacobi sums, the consecutive-residue count,
  `|S|² = q`, the Kloosterman second moment.
- *Periodic bookkeeping*: block sums over periods, the Legendre symbol on `ℕ`, self-similar
  summatory functions.
- *Prime windows and alignment*: the prime number theorem in multiplicative windows, aligned
  heights, lower bounds for squared partial Euler products, and their divergence against any
  integrable spectral weight.
- *Spectral form of dilation Gram matrices*: the Ramanujan step vector on the half line, its
  spectral weight, and the identity `Φ_r(c) = ∫ W(ξ) cos(2πξ log c) dξ`; the divisor expansion of
  hypercube forms into partial Euler products.

To build:

- *Size-truncated forms*: the spectral identity for `Σ_{d₁, d₂ ≤ D} μ(d₁)μ(d₂)(d₁d₂)^{−σ} Φ_r(d₁/d₂)`
  as `∫ W |Σ_{d ≤ D} μ(d) d^{−σ−2πiξ}|²`, and its relation to `1/ζ` on vertical lines.
- *Balanced Kloosterman forms*: from the second moment to the cross-scale Gram of BVI §3.13.

---

## 7. Open research topics

1. **Break the conductor-three floor for `λ`.** The extremal twin agrees with `λ` below `7`. Target:
   `Σ_{n ≤ M, λ(n) = λ(n+1)} 1/n ≥ (1/3 + c) log M − C` for some `c > 0`, with a proof that names the
   successor input and uses `λ(p) = −1` at infinitely many primes `p ≡ 1 (mod 3)`.
2. **The square-root scale over `ℤ` (W1).** A signed successor estimate for `λ` or `μ` with a power
   saving at one scale. Its first output in receiver coordinates must be a zero-free strip, and the
   statement must say which one.
3. **Size-truncated hypercube forms.** The prime-supported form is settled (§3.7). Its borderline
   `ε = 1/2` (where the Euler product sits on the line of absolute convergence) is open, and so is
   the size-truncated form above: its uniform boundedness for `1/2 < σ < 1` is where the zeros of
   `ζ` enter, and its first rung is a zero-free strip.
4. **Classify the zero-defect signs.** Zero-defect signs attain the floor (item 34). The
   conductor-three twins are zero-defect; the `f(2) = 1` branch is forced at the first primes
   (item 35). Is it realized by an infinite sign, and is it a twin of a character of larger
   conductor?
5. **Lag floors.** The lag-two floor lies in `[1/6, 1/4]`. Determine it, and determine the floor for
   odd shifts divisible by `3`, where the conductor-three twin agrees at two thirds of the steps.
6. **The complex floor.** Determine the constant in `[−1/2, −1/3]`.
7. **From `λ` to `μ`.** `μ = λ · μ²`, and the squarefree restriction breaks the cocycle
   (`μ(2n) = 0` for even `n`). Find the successor calculus of squarefree-supported signs.
8. **The index exit (fable §2.3 C).** The doubled-agreement count is a count that pays a signed
   identity, quantizes its deficit, and vanishes exactly at the extremals. An arithmetic count that
   pays the Hodge defect of the scaling surface in the same way would force the defect to zero.
9. **Kloosterman reciprocity (fable topic 2).** Carry the exact second moment to the balanced
   cross-scale Gram, where the Kloosterman fractions `k q̄/p` appear with cosecant weights.
10. **Witt structure (fable topic 10).** Decide whether Frobenius and Verschiebung on ghost
    coordinates supply a successor law, or whether they are Beurling-universal.

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
* when it tests an entry point of the successor input, say whether the test is decided by the zeros
  or by the pole;
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
8. **Pole before zeros.** Before reading a divergence as a statement about zeros, check whether the
   pole already forces it.
9. **Calibrate over `𝔽_q`.** State the finite-field form of every law first.
10. **Search the corpus first**: `scripts/formal_tools.py research "<query>"`.

---

## Source entry points

| Module | Content |
|---|---|
| `TheSuccessorDilationCocycle` | completely multiplicative signs, Liouville, prime-value construction; successor signs, telescoping, the dilation cocycle, characterization by prime cocycles, reconstruction; pronic law |
| `TheOneThirdSuccessorFloor` | agreement and doubled-agreement counts, the per-step doubling count, the exact two-scale identity, natural-density and logarithmic one-third floors |
| `TheFloorIsAttainedAtConductorThree` | conductor-three twins, exact agreement counts, zero doubling defect, sharpness of `1/3`, comparison with `λ` |
| `SquareRootCancellationIsACount` | successor correlations of characters as Jacobi sums, perfect cancellation, the consecutive-residue count, `|S|² = q` |
| `TheSuccessorBiasIsQuantizedByTheConductor` | Legendre symbol on `ℕ`, prime-conductor twins, block sums, `C(pJ) = −J + (1 + χ(−1)) ε M(J)`, `p ≡ 3 (mod 4)`, self-similar summatory functions, bias `−1/p` |
| `TheFloorReadsTheParityOfTheShift` | lag-`h` signs and cocycle, the odd-shift floor, conductor-four twins with perfect balance, the lag-two bracket `[1/6, 1/4]`, the alternating control |
| `PartialEulerProductsDivergeInTheStrip` | squared Euler factors, prime windows from `θ ~ id`, phase alignment, aligned windows, divergence against continuous weights |
| `TheSpectralHypercubeFormIsUnbounded` | aligned heights and radii, eventual alignment, divergence against every integrable weight with positive mass |
| `TheHypercubeDirichletFormIsUnbounded` | the step vector on the half line, the spectral form of the dilation profile, the twisted power and the divisor expansion, `Q_ε(P)` as a spectral integral, unboundedness for `−1/2 ≤ ε < 1/2` |
| `TheKloostermanSecondMomentIsACount` | Kloosterman sums, conjugation of additive characters, the exact second moment, `K(0, b) = −1` |
| `TheComplexSuccessorFloor` | unimodular signs, the unit-vector inequality, Cauchy–Schwarz on logarithmic sums, the complex floor `−1/2`, Catalan's pair |
| `TheTwoScaleDeficitIsQuantized` | the two-scale deficit, its quantization, zero defect and equality, zero defect forces the floor, the `f(2) = 1` branch |
