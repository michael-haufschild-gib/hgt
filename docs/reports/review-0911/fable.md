# Consolidated review — big picture, obstacles, questions, programmes

**Sources.** [Frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [unification ledger](route-unification-ledger.md), [route obstacles](route-obstacles.md), [walls ledger](walls-ledger.md), [obstacles summary](obstacles-summary.md), the pipeline cards under `docs/drafts/pipeline/`, and the Lean corpus through `scripts/formal_tools.py research`. Corpus checkpoint `97ebb59233` with its working tree.

**Evidence.** `[L]` Lean, integrated, as recorded in the ledgers. `[L*]` Lean statement and proof read for this report. `[S]` Lean source present, audit pending. `[P]` paper proof on a pipeline card, taken as correct. `[D]` deduction made in this report, not a Lean theorem. `[C]` published mathematics, not in the corpus. `[A]` assessment.

**Where the review-0911 ledgers and the corpus differ.**

| Ledger row | Corpus |
|---|---|
| Σ146, A64: `log²T` criterion not assembled | `riemannHypothesis_iff_prime_logSquare_windows`, with absolute, width and quasi-RH forms `[L*]` |
| Γ189, A69: full-degree carrier is a stub | `TheFullAdelicDegreeConfiguration`, `ThePrimeAdjacencyOnTheAdelicCarrier` `[L]` |
| B85, B86, B142: the family step is open | fixed-part theorem `[P]`, `ArithmeticWeightTheory/TheZeroMotiveIsTheFixedPartOfEveryArithmeticFamily` `[S]` |
| B125: no halving pairs is a condition | void: `riemannHypothesis_iff_sharp_rate_and_no_shimura_obstruction` `[L*]` |
| Π103: no saving for long Möbius mean values past the height | `averagedMeanSquare_moebius_of_tendsto`: Matomäki–Radziwiłł for `μ` at every length `h→∞`, `h≤√x`, in fibre form `[L*]` |
| Π144: no `p`-derivation in the corpus | `SignFreePurityMechanisms/TheFermatQuotientIsTheDerivativeAtAPrime` `[L]`; `δ_p` on the ghost ring `[P]` |

---

## 1. The big picture

### 1.1 One object

The 38 live formulations and 9 candidates are readings of one quantity. For the cubic spline `B` let `c_B(u)=Re S(u)` be its orbit correlation under Weil's form; then `c_B(log d)=A(d)−P(d)`, where `P(d)` is the smoothed von Mangoldt count in the multiplicative window of `d` and `A(d)` its archimedean-plus-pole prediction `[L]`. Both have size `√d`; only the difference matters. Write `c_p=c_B(log p)`.

| Statement | Reading |
|---|---|
| `c_p≥−K` at every prime | Weil positivity of the two-bump test `B+τ_{log p}B` (U-Σ) |
| `P(p)≤A(p)+K` at every prime | a crude prime count; Stepanov's bound for the smoothed Frobenius graph of degree `p` (U-Π) |
| the class `Γ_1+Γ_p` carries an `ℕ`-count with Tate limit `2c_B(0)+2c_p` | the count half of a Born rule (U-Γ) |
| `\|c_p\|≤K` at every prime | the same decision with no sign: absolute convergence, continuation, Laplace rate theorem |
| distinct zeros of `ξ` have distinct ordinates | separation by the height (`RHTower/OrdinateInjectivity`) |

Each line is equivalent to RH `[L]`. The object is local in scale and its growth exponent is the width `[L*]` (`SurfaceOfSpecZ/ScaleLocality/PrimeLogSquareWindows`):

- for every `α≥0`: all zeros have `Re ρ≤½+α` ⇔ `∃K`, for arbitrarily late `T`, every prime with `|log p−T|≤C log²(T+2)` has `2c_p≥−Kp^α` ⇔ the same with `|2c_p|≤Kp^α`;
- `α=0` is RH; some `α<½` is quasi-RH (`quasiRH_iff_prime_logSquare_power_windows`);
- if RH fails, every sufficiently late window of that radius contains a prime violating any prescribed `K` (`eventually_prime_logSquare_window_negative`).

In the original variable the window is `[x·e^{−C(log log x)²}, x·e^{C(log log x)²}]`, along any sequence `x→∞`. Radius `32 log(T+2)`, that is `[x(log x)^{−32}, x(log x)^{32}]`, has its kernel, its leakage estimate and the filter for the actual zeros of ζ in Lean (`QuartetLogMoments`, `PositiveKernelLeakage`, `PositiveKernelConvolution` `[L]`; `ZetaQuartetFilter`, `KernelLogarithmicTrace` `[S]`); the criterion on those windows is not assembled. If the off-line ordinates are `δ`-separated, windows of fixed ratio `e^{80/δ+1}` decide from either side, and the length is sharp up to the constant `[L]`. Unconditionally `|P(n)−A(n)|≤C√n·exp(−(log n)^{3/5}/(10⁸ log log n))` `[L]`.

**Law and point** `[D]`. Outside the Vinogradov–Korobov region and the verified heights, every unconditional theorem of the corpus about the zeros is a statement in law: the density exponent `30/13`, primes in almost all intervals of length `x^θ`, `θ>2/15`, the census `0.6725`, the Matomäki–Radziwiłł mean square, the form factors below the diagonal `[L*]`. Purity is a statement about every zero. A proof must convert law into a pointwise statement, and four conversions are known:

| Conversion | Where it proves a Riemann hypothesis | Over ℤ |
|---|---|---|
| sign of a form (Hodge index, Maass–Selberg, Landau) | Weil for curves; the Lagarias–Suzuki line law `[L*]` | the routes of U-Σ; no producer |
| integrality gap with a cheap source of vanishing | Stepanov–Bombieri; transcendence | the product formula is an identity; vanishing costs its own count `[L]` |
| exact recurrence in height | curves (periodic zeros) | the dark range: only primes `≲ log t` are prescribable at height `t` `[L]` |
| separation by an invariant of the symmetry | Carlitz–Goss `[C]` | a receiver: the ordinate separates ⇔ RH `[L]` |

The three route families are the first three conversions. No test is compact on both sides of the explicit formula: a compact prime side leaves infinitely many zero modes and only a sign decides; a localized zero side lets a crude bound decide but needs square-root precision of a prime count; the third family is the involution `ρ↦1−ρ̄` and the vertical position of the zeros.

### 1.2 The second coordinate: three atoms, two worlds

With `Θ=sup Re ρ` and `Θ∞=inf{σ: finitely many zeros right of σ}`:

- **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL.
- RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; no two of B13, Landing, DH fail together `[L]`.
- `Θ<1 ∨ AAL`; `Θ<1 ⇔ Θ∞<1`; `¬(Θ<1) ⇔ Θ=Θ∞=1 ∧ AAL` `[L*]` (`ZeroConfigurationGeometry/AbscissaLaws/QuasiRHIsATailLaw`).

A failure of RH lies in exactly one of two worlds `[D from L*]`.

| World | Description | What is proved inside it |
|---|---|---|
| ¬AAL: a finite isolated top layer at `β*<1` over a remainder at `Re s≤β*−η` | rigid: finite oscillation of `ψ`, a finite wave | `Θ<1`; `M(x)=O(x^β)`, `β<1`; heavy returns of the primes `≤y` need `log t≥c·y^{1−β}` with `β<Θ` `[S]`; prime filters recover each top residue at every damping speed `[S]` |
| AAL ∧ ¬ZAL: the top `Θ=Θ∞>½` is approached by infinitely many zeros | a tail law | nothing beyond the receivers |

The curve proof needs neither coordinate: finite rank makes ZAL automatic and periodicity of the zeros in height makes AAL automatic `[L]`.

### 1.3 Hard obstacles that are solved

| Obstacle | What is a theorem | Anchor |
|---|---|---|
| "Many routes" | one inequality per prime; route classes by source identity | SOSZ, CDGeo `[L]` |
| Attainment and global data in the decision step | decisive samples of density zero; `√T` and `log²T` windows; width, absolute and quasi-RH forms on windows; fixed-ratio windows under ordinate separation; counts needed on one sequence of windows | SOSZ ScaleLocality `[L*]` |
| A decision step without positivity | two-sided gap iteration; RH ⇔ ordinate injectivity ⇔ bounded absolute traces at the primes; the absolute log-square criterion by complex deletion filters, with no positive averaging | `TwoSidedGapIteration`, `OrdinateInjectivity` `[L]`; `SignedPrimeLogSquareWindows`, `TheHeightSeparatesTheZerosIffThePrimeTracesAreBounded` `[S]` |
| Structure of the exceptional coordinate | three atoms, strict dial, landing in eleven forms, DH classified on models, two-scale law, quasi-RH as a tail law | ZCG AbscissaLaws, ELT `[L]` |
| The finite-layer world | rigid description of ¬AAL; a filter that reads each top residue for every contraction `h→0`; with boundary rotation the fixed Gamma loss `π/4` is absent and every damping speed `a>0` reads | ELT, `BoundaryDampingReadsTheDivisor` `[L]` |
| Critical compactness of the atomic matrix | `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; Γ-liminf; charged compactness | AHD, CACT `[L]` |
| Subcritical positivity | complete matrix PD for exponent `<1/8` and one critical multiple | CACT `[L/K]` |
| The window chain | precontact canonical system, `L′=q−sinh 2L`, restoring bound, RH ⇔ `Ψ` locally bounded | CSTW, AIF `[L]` |
| Identification of ζ | Hamburger: a Dirichlet series with ζ's FE is a multiple of ζ `[L*]`; FE with `L¹` or `L²` defect ⇒ rational primes; degree-one Selberg class; count distance `o(log n)` | HTGeometry, EFT, SEL, SPAL `[L/K]` |
| Exact Frobenius over ℤ | orbit preservers are (Laurent) Adams maps; integrality acts only on the torsion; exact Stepanov count = Chebyshev; a zero-derivative endomorphism of `ℤ[X]` is an evaluation; simultaneous inseparability at the primes of `S` costs the primorial of `S`; order `m` at every prime of `S` costs exactly `m·θ(S)` | ALST `[L]`; `SignFreePurityMechanisms` `[L]` |
| The family step of Deligne's argument | the zero motive of ζ is the fixed part of every arithmetic family (§5.2) | AWT `[P/S]` |
| The square of Spec ℤ over `𝔽₁` in Λ-geometry | `Spec W(ℤ)`: the union of the Frobenius graphs glued along the primes; `#(ℤ/J(1,n))=e^{Λ(n)}`; contact orders give the prime part of Weil's off-diagonal exactly; it is a curve and has no diagonal | `agz-absolute-geometry-of-spec-z` `[P]`; `TheGhostRingOfTheArithmeticSquare`, `TheFrobeniusGraphsMeetInThePrimes` `[S]` |
| Returns of the prime orbit | depth law (Baker), breadth to the VK height, collective counts beyond the depth floor | TTPO, CDGeo `[L]` |
| The off-diagonal of Weil's kernel | pole − `ℍ³` Green function at `s=½` − tree Green functions at the Ramanujan point; Gram coupling; discrete adelic carrier with commuting prime operators; the product of local critical profiles on the rational torus orbit has a height finite part | SOSZ, HAT `[L]` |
| A geometric normalization of the full Weil functional | on compactly supported `C²` autocorrelations Weil's functional is the limit of energies built from the truncated Maass–Selberg diagonals of the modular Eisenstein series at cusp height one, with one scalar archimedean counterterm and the two boundary poles | `tendsto_renormalizedTower`, `tendsto_geometricWeilEnergy` `[S]` |
| The horizon | one cuspidal cavity function sees every resonance; reflection Krein form has one negative square per off-line zero; for one Hecke eigenform RH ⇔ sharp energy rate ∧ no simultaneous Shimura zero at `ρ/4+¼` | AHMH `[L*]` |
| Deligne's other steps over ℤ | Künneth for the zero motive, exact tensor weights, generic purity and big monodromy of the gauge family, jump at ζ | AWT `[L]` |
| Prime distribution in law | Guth–Maynard large values; `N(σ,T)≪T^{(30/13)(1−σ)+ε}`; primes in almost all intervals `(x,x+x^θ]`, `θ>2/15`; asymptotics at length `x^{17/30+ε}`; Matomäki–Radziwiłł for `μ` at every length | `GuthMaynardCorollariesUnconditional`, `RHTower/Sieve` `[L*]` |
| Census | simple critical zeros `≥(0.67250071−ε)N(T)`; `4/5` of the ordinates critical; `3/4` of the zeros within `4/log T` of the line; `(HD(1)−ε)N(T)` critical zeros of `ξ′` | Zeta23, IGP, RHTower `[L*]` |
| Finite verification | RH through height 67, `PF₂₀₀`, Li `n≤314`, theta rank 14 | VHR, TCS `[L]` |
| Purity proved for an infinite-rank object built from ζ | `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` has no non-real zero off the line, `Y>1` (Maass–Selberg) | `lagariasSuzuki_ne_zero` `[L*]` |
| Scope of failed mechanisms | 42 dead mechanisms and the scoped obstructions, each with its survivor | killed-routes |

### 1.4 What stands between the corpus and a proof

**(a) No producer for the minimal face.** Every unconditional pointwise saving in the corpus is the Vinogradov–Korobov saving. The theorems beyond it are in law (§1.1). On the width axis every interior value is a zero-free strip; there is no rung between VK and quasi-RH. The heat axis is the width axis: `H_t` is real-rooted for `t≥w²/2`, and an off-line zero of depth `δ` at height `γ≥e^{1600}` gives `Λ_{dBN}≥δ²/(200 log γ)` `[L*]`.

**(b) The three atoms.** ZAL is at least quasi-RH. B13 contains the exclusion of one off-line quartet. Landing is undecided for ζ; it fails with the FE alone and with the Euler product alone `[L]`.

**(c) Three structural gaps** `[L/D]`.

1. *The dark range.* Dirichlet polynomials longer than the height; primes past the Kronecker scale. The only unconditional theorem inside it is in law (Matomäki–Radziwiłł).
2. *The diagonal and the second dimension.* Weil's form has no counterterm-free positive presentation of its diagonal. As a quadratic functional on packets it has a geometric normalization with one scalar counterterm `[S]`; as a bilinear pairing of degree points with a self-intersection it has none: the Λ-square carries the prime part of every off-diagonal intersection number and has no normal direction to the diagonal `[P]`, and atoms need a genus of order `N log N`, which is archimedean `[L]`.
3. *The two-scale FE–Euler input.* An inequality the explicit formula does not imply. The exceptional-current receiver is complete; the gap left is `a(1−Re ρ)/2`, the distance from the top layer to absolute convergence `[L/S]`.

**(d) Rigidity, read as an obstacle** `[D]`. ζ has no moduli.

1. Hamburger: a Dirichlet series with the functional equation of ζ is a multiple of ζ `[L*]`. The Euler product is not needed for the identification.
2. FE-defect isolation: among countable Beurling systems an FE with integrable defect forces the rational primes `[L]`.
3. Degree one and conductor one is ζ `[L/K]`.
4. Summable Euler deformations keep the zeros; deformations that move zeros are analytically disconnected from ζ `[L]`.

Consequences.

- *No calibration with both structures.* The fakes of the corpus each drop one structure. Inside the class with Euler product and FE the calibration set is: the non-tempered pair `ζ(s−a)ζ(s+a)` (FE, Euler product, nonnegative coefficients, zeros on `Re s=½±a`; Ramanujan fails) `[L*]`, and two scenarios that are not excluded: an exceptional real zero of a quadratic `L`-function, an exceptional Laplace eigenvalue `[C]`.
- *ζ is the fixed part.* In every family of twists or covers the zeros of ζ are the part common to all members; the family controls the variable part only (§5.2) `[P/S]`.
- *No Frobenius for a window.* One power map is a Frobenius at one prime only (`isFrobeniusAt_iff`), and on every ring with Frobenius lifts the cost of vanishing is the product formula, with equality `[S/P]`.
- *The trivial fibre is the homogeneous case.* Amplified moments beat the trivial bound at every nontrivial torsion fibre and not at `0`, because the phases align there `[S]`. The same point is where Diophantine tools are homogeneous: the corpus has the effective Baker bound for homogeneous forms in prime logarithms and only the qualitative inhomogeneous theorem `[L]`.

**(e) Sharpness in the coefficient size** `[L*]`. Any argument that tolerates a loss `p^ε` in the size of the coefficients, or that uses only Euler positivity and the FE, is refuted by the non-tempered pair, whose prime coefficients are `p^a+p^{−a}`. A proof must use the exact normalization: pole at distance exactly `½` from the centre, one Gamma factor.

**(f) Every transported mechanism has its exact price** `[D]`.

| Mechanism | Price over ℤ | Evidence |
|---|---|---|
| moments of a family, with amplifier | the trivial bound `(Σa_n)^{2k}` at the fibre of ζ | `[L]`, `[S]` |
| positivity of product coefficients | one-way: base to product | `[S]` |
| Frobenius lifts and high-order vanishing | `m·θ(S)`, the count to be bounded | `[L]`, `[P]` |
| carries against `𝔽_q[T]` | a fixed positive proportion of the window count | `[P]` |
| integrality of auxiliaries | Chebyshev; exact on the torsion only | `[L]` |
| finite-layer filters | the gap `a(1−Re ρ)/2` | `[L]`, `[S]` |
| window positivity at aperture `a` | verification to `windowHeight(a)` | `[L]` |
| the de Bruijn–Newman time | the width squared | `[L*]` |

---

## 2. Opportunities

Ranked by what they would change. None closes a wall named in §1.4.

| # | Opportunity | What it gives | Status |
|---|---|---|---|
| 1 | **Logarithmic windows** (B140) | the minimal face on `[x(log x)^{−32}, x(log x)^{32}]` along one sequence of `x`; with `O(e^{δT})` exceptional primes per window, `δ<1`, as a conjecture on a card | positive quartet kernel with moments `≤C·exp((s+6)log(s+6))`, leakage `≤AC·exp(DB−T)` at radius `8 log(T+2)` `[L]`; filter and trace floor for the zeros of ζ `[S]`; quartet excursion and prime transfer open |
| 2 | **One object for the diagonal** (§5.3) | the first object on which Riemann–Roch and ampleness can be posed without Weil's form | finite part of the coupled orbit `[L]`; its density constant is built from Weil's two archimedean constants (§11.6) `[D]`; the packet functional from the scattering tower `[S]`; the comparison of the two and torus invariance open |
| 3 | **Seventy per cent from a bounded form factor** (§4.2) | `70%` from `F≤4` on `(1,10/9)`; an exact covariance equivalent at every proportion | exchange rate and density calibration `[L*]`; no source bound |
| 4 | **Higher Gram moments for the census** (§4.4) | a route to `70%` without prime pairs `Λ(n)Λ(n+h)` | triple and four-level form factors for `α+β<1` `[L*]`; model `16/21` `[L*]`; wider frequencies open |
| 5 | **The finite-layer receiver at polynomial damping** | a prime cutoff polynomial in the height, where Vinogradov-type estimates apply | conjecture on a card; the gap `a(1−Re ρ)/2` is unchanged by it `[A]` |
| 6 | **The archimedean fibre and a second dimension for the arithmetic square** (§9.4 D, E) | what Λ-geometry lacks, as constructions with kill conditions | not started |
| 7 | **Unassembled corollaries** | graded recurrence against the Guth–Maynard density (§11.6); effective Baker in three logarithms for the upper side at `pᵃqᵇ`; two-prime local criterion (A65); dominant-ordinate divergence (A67); finite-stratum laws on the cosine and shifted Jensen families (A50) | `[D]`, `[C]` |
| 8 | **Shimura nonvanishing for one eigenform** | the single-eigenform receiver with no side condition | `[L*]` reduction; the nonvanishing at `ρ/4+¼`, real part in `(3/8,½)`, is open |

Two observations.

- **A contradiction search for AAL may assume a zero-free strip.** In the ¬AAL world `Θ<1`, Mertens has a power saving and heavy returns cost `log t≳y^{1−β}` `[S]`. These do not produce a contradiction: the finite-layer identities stay consistent `[L]`.
- **Contraction-induced smallness cannot contradict a top layer.** For `dκ≥a(1−σ)/2` the raw prime filter tends to zero while the normalized filter tends to the nonzero divisor constant `[L]`. An upper bound that contradicts the layer has to beat the trivial bound for a filtered prime sum of length `e^{at/2}` at height `t` by the power `1−Re ρ`; that is the exclusion it is meant to prove `[A]`.

---

## 3. Quasi-RH: is there a clear path?

**No.**

What the corpus establishes.

- Quasi-RH is a tail law: `Θ<1 ⇔ Θ∞<1`; its failure forces `Θ=Θ∞=1` and AAL `[L*]`.
- Quasi-RH is a one-sided power saving on sparse windows: `Θ<1` ⇔ for some `α<½` and `K`, arbitrarily late log-square windows have `2c_p≥−Kp^α` at every prime `[L*]`.
- Every interior value of every width parameter is a zero-free strip: Möbius or Liouville power saving, a polynomial stencil rate `K^{−a}`, a horocycle or Farey or cavity exponent past `½`, a growth exponent `p^a`, `a<½`, of either side at the primes, a tensor-moment slope, a heavy-return exponent, the de Bruijn–Newman time `[L]`.
- All unconditional pointwise savings are VK `[L]`. The density theorems are in law: `N(σ,T)≪T^{(30/13)(1−σ)+ε}` bounds the number of zeros right of `σ` and excludes none `[L*]`.

Why this is not a path.

1. The only mechanism known for a zero-free region is Euler positivity at the pole combined with growth bounds; its limit is VK, and Lindelöf-strength growth does not imply a strip `[C]`. The pretentious form of the same argument (repulsion of `n^{it}` from `−1`) reaches the same region `[C]`.
2. Beurling systems with integer-like counting can have zeros approaching `Re s=1` `[C]`; the Euler product and regular counting do not give a strip. Return bounds are statements about the labels `log p` and are shared by `ζ(s−h)` `[L]`.
3. A failure of quasi-RH is an AAL world with zeros approaching the 1-line on a set of heights of density zero; statements in law do not see it `[L/D]`.
4. On the width axis there is no intermediate rung: improving `exp(−(log)^{3/5})` is "past VK", a named problem.
5. A producer that improves on VK uniformly in the target point of the prime torus also removes the exceptional zero of a real character `[D]`. It must be specific to the trivial fibre or contain the Landau–Siegel problem.

A proof of quasi-RH would have to be a new mechanism, not an assembly. The corpus identifies where it must act: a pointwise statement at the primes of one sequence of log-square windows, using the coefficient size.

---

## 4. Seventy per cent of the zeros on the line

### 4.1 Status

- `simple_critical_proportion_ge_67250071` `[L*]`: simple critical zeros are at least `(0.67250071−ε)N(T)`. The constant is `HD(1)+10⁻⁸`, `HD(1)=3/2−cot(1/√2)/√2`: the explicit-formula Gram certificate at bandwidth `λ=1` in the `Zeta23` package, plus the disjoint-pair pinching slack of IncommensurableGaborPinching.
- `four_fifths_critical_ordinates` `[L*]`: `4/5` of the distinct ordinates are critical.
- `three_quarters_within_four_div_log` `[L*]`: `3/4` of the zeros lie within `4/log T` of the line.
- `eventually_deriv_xi_criticalLine_count_ge` `[L*]`: at least `(HD(1)−ε)N(T)−1` distinct critical zeros of `ξ′`.
- `xi_five_runs_positive_proportion` `[L*]`: runs of five consecutive simple critical ordinates have lower density `3HD(1)−2−11π/2000>0`.
- Near-line alternatives `[L*]`: for every `A>0` and `θ∈{7/10, 3/4, 4/5}`, either `N₀≥θN` or at least `(1+HD(1)−2θ−1/A−ε)N` simple off-line zeros lie within `A/log T` of the line. A failure of `70%` needs more than a quarter of all zeros to be simple, off the line and at depth `O(1/log T)`.
- Positivity together with sub-threshold data cannot reach `3/4` (`PositivityCannotReachTheThreeQuarterThreshold`) `[L]`.

### 4.2 Four exact receivers

**(i) Bounded form factor.** In the rank–trace certificate with sharp taper at bandwidth `λ`, the certified proportion is `2−c(λ)`, `c(λ)=1/λ+(2/λ²)∫₀^λ(λ−α)F(α)dα`. If `F≤B` on `(1,λ)` the best proportion over all `λ` is `H*(B)=(2B−1)/(3B−2)`, attained at `λ*=(3B−2)/(3(B−1))` (`certValue_le_opt`, `certValue_at_opt`) `[L*]`.

| `B` | `H*(B)` | `λ*` |
|---|---|---|
| any finite `B` | `2/3+1/(3(3B−2))` | |
| `4` | `7/10` | `10/9` |
| `2` | `3/4` | `4/3` |
| `1` (random-matrix value) | `1` | `∞` |

So `70%` follows from `F≤4` on `(1,10/9)` `[D from L*]`. The obstruction beyond bandwidth one is boundedness of `F` just above `1`, not its value. At fixed `λ=4/3` the proportion is `7/8−B/16`.

**(ii) Prime-side certificates** `[L]`.

- `(29/36−32πε₁−ε)N − coalescentSurplus ≤ N₀*` at `λ=4/3`;
- `(Hcos(λ)+δ_λ−ε)N − S_λ ≤ N₀^{simple}` for `0<λ≤2`, with coefficients `3/4+79/1250` at `4/3` and `5/6+43/3750` at `2`;
- `FrobeniusFourThirds`: `tr G̃²≤(5/4+ε)(aL)²·Tℓ₁/2π` gives `3/4` simple and on the line; the random-matrix value of the left side is `19/16` `[L*]`.

| Target | Budget for the surplus per `N(T,2T)` |
|---|---|
| beat `2/3` | `<5/36` |
| beat `HD(1)` | `≤577/4500` |
| `70%` | `≤19/180` (boxcar, `λ=4/3`); `≤0.113` (cosine, `4/3`); `≤0.145` (cosine, `2`) `[D]` |
| `75%` | `≤1/18` |
| Hardy–Littlewood value | `−1/144` |

**(iii) Source covariance.** The height-cell source covariance of the critical-feature census equals `4π` times the off-line multiplicity up to `o(N)`: for every `a`, the ceiling `(4π(1−a)+o(1))N` holds ⇔ the critical-line density is at least `a` (`criticalFeaturePhaseCovariance_four_pi_complement_upper_iff_criticalLine_lower`) `[L*]`. The proved ceiling is `4π/3` (`criticalFeaturePhaseCovariance_fourPiThirds_upper`, from the two-thirds theorem) `[L*]`; the census constant gives `4π·0.32749929` `[D]`. `70%` ⇔ ceiling `6π/5`; `75%` ⇔ ceiling `π`.

**(iv) Local count.** If every window `(S−1,S+1]` holds at most `M` off-line zeros, then `N₀/N→1` (`tendsto_N0_div_N_of_offLineLocallyBounded`) `[L*]`; the same holds when the bound fails on a set of centres of measure `o(T)` (`tendsto_N0_div_N_of_almostOffLineLocallyBounded`) `[L]`. The full local count is a multiplicity statement and does not follow from RH with counting inputs `[L]`.

### 4.3 What blocks them

The surplus is a sum over odd primes at even shifts `p, p+2r` with `|log(n/m)|≤T^{−1+η}`, `n≈T^λ`, against a signed kernel `[L]`. The model part (singular series) is evaluated and gives a negative Ward–Mertens term `[L]`. The discrepancy from the model is a prime-pair correlation in shifts up to `X^{1−1/λ}`: `X^{1/4}` at `λ=4/3`, `X^{1/10}` at `λ=10/9`.

1. Unsigned bounds diverge (`sum_Icc_abs_cosTransform_ge_inner_lobe`); an unsigned additive sieve would need a constant `≤8/9` `[L]`. An upper-bound sieve for prime pairs, which loses a constant factor, is therefore not enough `[D]`.
2. The main terms cancel: the diagonal contributes `α` to `F(α)` and the prime pairs must contribute `≈1−α`. What is needed is the variance of primes in intervals of length `X^{1−1/λ}` to within a constant factor `[D]`. Asymptotics for almost all shifts with a saving `log^{−A}` per shift do not reach it.
3. A bound `F≤4` on average over `(1,10/9)` is not among the known consequences of RH `[C/A]`.

### 4.4 A second route `[A]`

The certificate uses the first two moments of the on-line Gram matrix. The corpus has the next moments unconditionally in the range `α+β<1`: the triple form factor vanishes (`tendsto_tripleFormFactor`) and the four-level form factor factorizes (`tendsto_fourLevelFormFactor`) `[L*]`; with sine-kernel moments `(1,4/3,2,13/4)` the model certificate is `16/21` `[L*]`; the blind spot is exact through third order `[L]`.

Its prime side is a mean value of a product of two prime polynomials, hence a shifted convolution of `Λ∗Λ`. This has bilinear structure, which `Λ(n)Λ(n+h)` lacks. Twisted second moments with coefficients of length `T^θ`, `θ<17/33`, are published `[C]`; their use for a fourth Gram moment is a theorem to be proved, not a consequence. The model value is not a ζ-proportion.

**Verdict: no clear path.** Every receiver is exact, and each waits for one estimate: a bounded pair-correlation form factor just above `1`, which is a binary additive problem at a precision not available even conditionally.

---

## 5. The one big question

### 5.1 Questions not to pose

| Question | State |
|---|---|
| B131 Deuring–Heilbronn question | settled: DH is off the RH path; classical repulsion calibrated; no Siegel regime |
| B132 almost all primes | settled: No; power-thin exceptions keep the criterion |
| B136 decisive samples with large gaps | settled: they exist |
| B138 landing | resolved in the sense posed: three-atom factorization; fails for the FE alone and for the Euler product alone |
| B139 scale-local sampling; A64 | settled: `√T` and `log²T` windows; width, absolute and quasi-RH forms |
| (FP) the fixed part of a family; B85, B86, B142 | settled: Yes (§5.2) |
| (S1) a Frobenius shadow over ℤ | settled: it exists one prime at a time and its cost is the count (§6) |
| (S2) a separation shadow | settled as a receiver (§6) |
| B125, halving pairs | settled: the condition is void; open: the Shimura condition |
| the square of Spec ℤ in Λ-geometry | settled: `Spec W(ℤ)`, a curve (§9) |
| a sign-free proof of the local criterion (A66) | settled: complex deletion filters `[S]` |
| a geometric normalization of Weil's functional on packets | settled on the modular surface: the scattering tower `[S]` |
| B140 logarithmic windows | open; kernel, filter and leakage in Lean, criterion in assembly |
| B141 DH for ζ | open; off the RH path |
| B133 the diagonal | open; §5.3 |

### 5.2 (FP): the zero motive of ζ is the fixed part of every arithmetic family

> **(FP)** Let `(𝔉,ν)` be a family of Euler products whose even moments of window traces are computed by orthogonality: the gauge torus, the characters modulo `q≤Q`, the vertical line, Hecke eigenforms under the Weyl law and their Rankin–Selberg squares, number fields under a counting measure, summable Euler deformations, and their mixtures. For every `k` the `2k`-th moment identity controls the variable traces only: the centred trace of ζ enters with `ν`-mass tending to zero or as an exact common factor, and no inequality derived from the family bounds `|c_p|` below the trivial bound.

The following fixed-part laws are proved (`awt-fixed-part-theorem-for-arithmetic-families`); Lean: `AmplifiedMonodromyBreaksOnlyOffTheTrivialFibre`, `ProductPositivityCouplingIsOneWay`, `TheZeroMotiveIsTheFixedPartOfEveryArithmeticFamily` `[S]`. They do not establish (FP)'s universal clause about every derived inequality. In particular, the Euler-weight countermodel does not retain an FE.

1. *Coherence at the trivial fibre.* For every finite measure `ν` on the gauge torus, every continuous amplifier `A` and nonnegative weights, `ν{0}·|A(0)|²(Σa_n)^{2k}≤∫|A|²|S_x|^{2k}dν`, with no orthogonality hypothesis; centring by the pole changes the moment only by the atom at `0`. Away from `0` amplification wins: on `{2,3}` an orthonormal four-point measure and a prime-supported amplifier give the moment `2<4` at a torsion fibre.
2. *One-way coupling.* Positivity of the coefficients of `ζ·L^{var}` passes from the base to the product and not back. The symmetric shift preserves every product positivity and moves the base width by `a`; doubling the Euler factors on a sparse set of primes keeps the pole, the residue and all positivity couplings and changes the prime window by `≥c·p^{θ−½}` at infinitely many primes. So no bound `|c_p|≤Kp^a`, `a<½`, follows from variable-family data and product positivity.
3. *Mixtures and the tensor criterion.* In each of the five family classes ζ has mass tending to zero or is an exact common summand; a common summand `c` is unconstrained by the moments of the variable part, since the pushforward by `c+V` is a probability measure for every `c`. With the trace of ζ retained, sublinear growth of the tensor moments of a cover family is equivalent to RH.

Consequences.

- These identities and product-positivity laws provide support for the tensor and family branch. A universal exclusion of family producers remains unproved.
- Producing the base-trace bound remains open after these obstructions; the cover-family tensor criterion still retains exactly that input.
- For nonzero integer values, order `m` at every prime of `S` costs `m·θ(S)` (§6). Transferring this statement from evaluated δ-jets requires compatibility of the integer point with Frobenius.

### 5.3 The question: is Weil's diagonal the finite part of one glued object?

**What exists.**

- *Finite places.* In the arithmetic square the graphs `Γ_m`, `Γ_n` meet in `Spec ℤ/J(m,n)`, and `gcd(m,n)·log#(ℤ/J(m/g,n/g))` is the prime part of `frobeniusIntersection m n` `[P]`. The square is a curve: the conormal module of the diagonal is torsion and there is no self-intersection `[P]`.
- *Archimedean place.* The other part of the off-diagonal is `min/(1−(min/max)²)`: one cusp and the jets of the trivial zeros, the Lefschetz trace of the dilation of `ℝ` at its fixed point `[L]`. No metric on `O(1)` over `ℙ¹_ℤ` carries it `[L]`.
- *The carrier.* `X=Γ\(ℍ³×Π′_p PGL₂(ℚ_p)/PGL₂(ℤ_p))`, `Γ=J⁻¹SL₂(ℚ)J`, retains every degree point; the prime operators `A_p` commute, preserve nonnegative functions and satisfy `A_p1=p+1` `[L]`.
- *A finite part.* On a reduced rational displacement `a/b<1` the product of the critical archimedean profile and the normalized critical tree factors is `b^{−2}/(1−(a/b)⁴)`. The height-damped orbit sum converges exactly for positive damping. After subtracting the collision row and the density row `c₀φ(b)/b²`, `c₀=log 2/4+π/8`, the rows are absolutely summable (`tendsto_orbit_finitePart`) `[L]`.
- *A first match* `[D]`. With `γ₀=gammaHardyPhaseRate(0)=(ψ(¼)−log π)/2`, the constant of the Gamma factor at the centre, `4c₀=−2γ₀−(log 4π+γ)`. The right side consists of the two constants of Weil's archimedean diagonal. Proof: `regularMean_eq`, `digamma_quarter` and the definition of `gammaHardyPhaseRate` `[L*]`.
- *The packet functional on the modular surface* `[S]`. With `A(u)=Λ(1+2u)`, `B(u)=Λ(2u)` and `P(u)` the truncated Maass–Selberg pairing at cusp height one, `D(u)=(A²−B²)/(4uAB)−P/(2AB)` equals `Λ′/Λ(2u)−Λ′/Λ(1+2u)` (`geometricDiagonal_eq`). The tower `Σ_{n<N}D((s+n)/2)` with the scalar counterterm `½log((Re s+N)/2)−½log π` and the two boundary poles tends to `ξ′/ξ(s)` for `Re s>1` (`tendsto_renormalizedTower`), and its pairing with a compactly supported `C²` autocorrelation tends to the full Weil functional (`tendsto_geometricWeilEnergy`). The diagonal is defined by the truncated Eisenstein integral and its cusp coefficients, not by the zeros. It is a quadratic functional on packets in the absolute chamber; it is not a Green operator on the carrier and carries no sign.
- *The defects of the scalar and Gram couplings.* Both dampings leave the discriminant; atoms need a renormalization of order `N log N` `[L]`.

**Precise form.** Prove or refute:

> **(G)** There is a normalization of the coupled orbit sum on `X`, invariant under the rational torus and determined by the Laplacian of `ℍ³` and the operators `A_p` alone, whose finite part is Weil's form as a bilinear pairing of the degree points: the off-diagonal with prime part the contact orders of the arithmetic square and archimedean part the jets, and the diagonal equal on packets to the Robin-normalized diagonal of the scattering tower, with no further counterterm.

A refutation is an obstruction theorem: every torus-invariant finite part of products of local critical kernels differs from the tower's diagonal by a term of the size of the discriminant. The three presentations exist separately: contacts in the arithmetic square, a finite part on the carrier, a packet functional on the modular surface. (G) asks whether they are one object.

*Why this question.*

- It is the one structural gap of §1.4 (c) that is an identity and not an inequality.
- After (FP) and (S1) both doors, the sign and the count, need a two-dimensional object with a diagonal. Ampleness and Riemann–Roch (question 4 of §9.5) cannot be posed before the diagonal exists as geometry.
- It is implied by nothing about the zeros and implies nothing about them.

*What either answer gives.*

| Answer | Effect |
|---|---|
| (G) holds | Weil's form is the renormalized Green energy of one operator on one space; the classes `Γ_n` have a self-intersection defined without `c_B`, so ampleness and a Riemann–Roch count can be posed on them; the sign becomes a statement about that operator at its critical point |
| (G) fails | the product of local critical kernels is a different object; construction C of §9.4 is closed in this form; the diagonal is an analytic counterterm with no geometric origin on the carrier |

*Tests.* T1 method. T2 an identity or an explicit defect. T3 the table. T4 no finite rung. T5 calibrated on a curve over `𝔽_q`, where the same recipe on the product of the trees of the places must return `Γ_n²=n(2−2g)`; it must not close on the integer-norm one-off, which has no archimedean fibre, and must return a different diagonal on the non-tempered pair. T6 not refuted; the scalar and Gram forms are refuted. T7 moves B133 and B88. T8 not a named problem; the first step is to compare the density constant `c₀` and the tower's scalar counterterm through the identity above; the named obstacle is torus invariance of the height subtraction.

*Limit.* It produces the object, not the sign.

### 5.4 Runner-ups

| Question | Why second |
|---|---|
| B140 logarithmic windows | in assembly; a criterion, not a producer |
| (S3) of §6: transfer from homogeneous breadth to one window | one of its two links is past VK |
| Ampleness (question 4 of §9.5) | needs the object of (G) first |
| B104 polar orthogonality of a half-line ground state | confined to the critical curve |
| B141 DH for ζ | off the RH path |
| Shimura nonvanishing at `ρ/4+¼` | sharpens one receiver |

---

## 6. The one big question without positivity and without spectral theory

"Spectral" and "positivity" are read as in §2.6 of the obstacles summary. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, analytic continuation, power sums, integrality, Diophantine approximation and transcendence, recurrence, Jensen and Rouché.

**The frontier under this constraint.** The receiver side is complete, local and proved inside the constraint: width `≤α` ⇔ `|c_p|≤Kp^α` at the primes of arbitrarily late log-square windows, by complex deletion filters of bounded total variation and polynomials in a translation, with no positive averaging (`zeta_re_le_iff_abs_prime_logSquare_power_windows_signed`) `[S]`; RH ⇔ the ordinate is injective on the zeros `[L]`. The producer side is capped by theorems.

| Sign-free producer | Reach | Evidence |
|---|---|---|
| integrality of auxiliaries | Chebyshev; exact on the torsion | `[L]` |
| Frobenius lifts | one prime at a time; `m·θ(S)` for a set `S` | `[L]`, `[P]` |
| exponential sums | VK | `[L]` |
| recurrence | the Kronecker scale `p≲log t` | `[L]` |
| transcendence | depth of two logarithms; breadth to the VK height for heavy subsets | `[L]` |
| separation | none: a receiver | `[L]` |

**The two sign-free proofs of a Riemann hypothesis and their shadows over ℤ.**

1. *Stepanov–Bombieri for curves.* Its input is the Frobenius as a ring endomorphism with zero derivative, which makes high-order vanishing at all rational points cheap. The golden datum at `q=5` has positive integral counts, an FE and an Euler product, and is impure `[L/K]`.
2. *The Carlitz–Goss zeta function of `𝔽_q[T]`* `[C]`. The Newton polygon has distinct slopes, so the roots have distinct valuations, and the Galois group, which preserves the valuation, fixes each root: purity by separation.

- **(S1) Endomorphism.** *Is there a commutative ring with commuting endomorphisms `F_n`, `F_mF_n=F_{mn}`, whose fixed-point counts are the point counts `N(n)=Λ(n)+1+1/(n²−1)` of Spec ℤ, on which vanishing to order `m` at the fixed points of the degrees of one window costs less than `m` times the window's Chebyshev count?*
  **Answer: no.** A literal count does not exist: `N(n)∈(1,2)` off the prime powers (`not_exists_card_eq_specPointCount`). The count is logarithmic: `Λ(n)=log Φ_n(1)`, and modulo `p` the primitive `p^k`-torsion collapses onto the fixed point `1` (`cyclotomic_prime_pow_zmod`). The Frobenius exists one prime at a time: `x↦xⁿ` is additive in characteristic `q` exactly when `n` is a power of `q` (`isFrobeniusAt_iff`), so `Λ(n)` is the number of primes at which `x↦xⁿ` is a Frobenius, counted with weight `log q` (`vonMangoldt_eq_finsum_log_isFrobeniusAt`); it fixes the fibre `𝔽_p` pointwise exactly when `p−1∣n−1`, at no more than `d(n−1)` primes (`forall_pow_eq_self_iff`, `ncard_fixed_fibres_le`). Stepanov's identity holds modulo `n` to all orders (`C_dvd_iterate_derivative_mul_expand_sub`). It is not archimedean: an endomorphism of `ℤ[X]` with zero derivative is an evaluation (`exists_eq_C_eval_of_derivative_eq_zero`). A monic polynomial whose derivative vanishes modulo every prime of `S` has degree divisible by the primorial of `S`, and one that is a `p^{k_p}`-th power modulo each `p∈S` has degree divisible by `Πp^{k_p}` (`prod_dvd_natDegree_of_map_derivative_eq_zero`, `prod_pow_dvd_natDegree`); multiplicity `m` modulo every prime of `S` is reached at log-degree `θ(S)+|S|log m` (`log_prod_pow_clog_le`), but it is multiplicity modulo `p`. On ℤ the `δ_p`-order is the `p`-adic valuation, the constants of `δ_p` are `0, ±1`, and order `m` at every prime of `S` costs `log|a|≥m·θ(S)` with equality for `Πp^m` (`forall_dvd_iterate_fermatQuotient_iff`, `mul_sum_log_le_log_abs`, `log_prod_pow_eq`) `[L]`. For a general ring with Frobenius lifts, this integer cost applies after restriction; identifying it with evaluated δ-jets requires Frobenius compatibility of the ℤ-point. The exact ideal-power restriction theorem is `map_ghostComponent_ker_pow_prime_pow`. On the diagonal Stepanov's inequality "zeros × order ≤ degree" is the product formula, an identity; there is no slack to construct.
- **(S2) Separation.** *Is there a sign-free prime-side quantity that bounds the fibre multiplicity of the height map on the zeros?*
  **Answer: yes as a receiver, no as a producer.** A Galois-invariant function injective on the roots forces the roots into the base field; a real polynomial whose roots have distinct absolute values has only real roots (`SeparationForcesRationality`) `[L]`. For ζ the invariant is the ordinate: zeros at one height have real parts within `2σ` ⇔ width `≤σ` ⇔ `|c_p|≤Kp^σ` at every prime (`fibre_spread_le_iff_twoSided_primes`, `injOn_im_iff_riemannHypothesis`) `[L]`. In the ultrametric case the Newton polygon produces the injectivity from the coefficients: for a nonarchimedean absolute value, nonzero coefficients with `|a_j||a_{j+2}|<|a_{j+1}|²` give simple roots of pairwise distinct size, and over a complete ultrametric field the polynomial splits over the base field (`HasSimpleSlopes.injOn_isRoot`, `splits_of_strict_logConcave`; example `padicTheta_splits`) `[L]`. Its archimedean counterpart is a theorem with a quantitative gap: nonzero coefficients with `|a_{j+1}|²≥9|a_j||a_{j+2}|` give exactly `i+1` zeros in `|z|<3|a_i|/|a_{i+1}|` by Rouché, hence zeros of pairwise distinct absolute value, and real zeros for real coefficients; no sign of a coefficient is used (`HasCoeffGaps.injOn_norm_zeros`, `im_eq_zero_of_coeff_gaps`) `[L]`. Its price is lacunarity: of three zeros of increasing absolute value the largest exceeds nine times the smallest (`HasCoeffGaps.nine_mul_norm_lt`) `[L]`. Separation by absolute value is therefore not available for ζ: some dyadic range carries three critical ordinates, and no polynomial with such gaps vanishes at their squares (`exists_critical_ordinates_not_hasCoeffGaps`) `[L]`. Over ℤ the injectivity of the ordinate is the statement to be proved.

**A filter for sign-free producers** `[D]`. The return bounds of the corpus are uniform in the target point of the prime torus `[L]`. A sign-free producer past VK that is uniform in the target applies to the orbit `(χ(p)p^{it})` of a real character and removes its exceptional zero. So a sign-free producer either contains the Landau–Siegel problem or uses what separates ζ from quadratic `L`-functions without a sign: the pole, or conductor one. The pole alone does not decide `[S]` (§5.2, part 2). What conductor one gives is the homogeneous problem: the target is the identity of the torus, where Dirichlet's theorem and the effective Baker bound apply `[L]`.

**The question.** Under the constraint no question below quasi-RH passes all of T1–T8: every pointwise sign-free statement past VK is a named problem (§3). What can be decided is whether the one unpriced producer, breadth at the homogeneous point, would suffice.

> **(S3) Transfer.** Suppose the heavy Bohr sets of the prime orbit at the identity are empty at the heights seen by one log-square window at scale `x`: for fixed `A, η, δ`, no heavy subset of the primes `≤(log x)^A` returns to precision `δ` at a height in `[T₁, x^η]`. Does `|P(p)−A(p)|≤K` follow at the primes of that window?

*Why this question.*

- It is a conditional statement about Dirichlet polynomials, with no hypothesis on the zeros. A zero of depth `δ` and height `γ` enters the window at scale `x` once `x^δ≳γ⁴`, so the window sees heights up to a power of `x` `[D]`.
- Its hypothesis is homogeneous, so it passes the filter. Whether the hypothesis holds is a separate problem: at `(log y)^A` it is past VK `[D]`.
- Both answers are theorems of use: if the transfer holds, the positivity-free route is one Diophantine statement about the logarithms of the primes; if it fails, the short-sum barrier is a theorem and the positivity-free programme has no route through returns.

*Tests.* T1 method. T2 an implication or a countermodel. T3 above. T5 two calibrations: on `𝔽_q[T]` every prime returns at the period and the conclusion holds, so the hypothesis is at most sufficient; on the integer-norm one-off the conclusion fails for every constant `[L]`, so the transfer predicts heavy early returns of its orbit, a statement that can be checked on that model. T6 not refuted. T8 the transfer is not a named problem; its hypothesis is.

*Limit.* It speaks about large heights. A finite layer at a fixed height is invisible to it; there the gap is `a(1−Re ρ)/2` (§1.4 (f)).

---

## 7. A new field for the walls

**Infinite-rank purity theory: Weil numbers without finite rank, without moduli, in law and at a point.**

*What it is about.* Frobenius modules of infinite rank with a duality: the zero motive `M=⊕ℤ(−ρ)` on which the Frobenius at `p` acts by `p^ρ`, with the pairing `ρ↔1−ρ`, the trace `Σ_ρ n^ρ`, and the archimedean involution `ρ↦ρ̄`. In finite rank purity comes from rationality of the characteristic polynomial, Galois conjugation, Kronecker's theorem, the determinant weight, a family with monodromy, and a Frobenius with zero derivative. The field asks what replaces each when the rank is infinite and the object is rigid, and how a statement in law becomes a statement at every zero.

| Finite rank | Infinite-rank counterpart | State |
|---|---|---|
| Newton–Girard elimination | exceptional-rank window theorem, infinite Turán sums, positive and signed deletion | available `[L]`, `[S]` |
| Finitely many eigenvalues | well-foundedness of the towers (ZAL) | open |
| Conjugates share their absolute value | zero transport (AAL); eventual bounds are global | open |
| Irreducibility of the characteristic polynomial | no finite stable exceptional set (B13) | open |
| Closedness of the set of weights | landing | open |
| Integer traces ⇒ algebraic integers ⇒ Kronecker | traces in `ℤ·log p`; count-distance rigidity; FE rigidity (Hamburger) | rigidity theorems `[L]`; no purity consequence |
| Determinant weight from the pairing | the FE fixes the weight of each pair `{ρ,1−ρ}` only if the pair is irreducible | the content of RH |
| Integral lattice stable under Frobenius | none: no finitely generated lattice is stable under three prime Frobenii | no-go `[L]` |
| A family with big monodromy | the fixed part is not seen | theorem `[P/S]` |
| A Frobenius with zero derivative | the product formula is an identity | theorem `[S]` |
| The square of the curve | `Spec W(ℤ)`: prime contacts, no diagonal | theorem `[P]` |
| The diagonal and Riemann–Roch | a glued object (§5.3) | open |

*Point of view.* RH is the statement that two involutions of the zero set coincide: the algebraic one `ι: ρ↦1−ρ` and the archimedean one `c: ρ↦ρ̄` (§10). The atoms are the infinite-rank forms of finiteness, conjugacy, irreducibility and closedness. The object has a fixed part and no variable part: every tool that averages is blind to it.

*Foundational principles.*

1. Purity statements are pointwise; a theory in law is blind to them `[L/D]`.
2. Both structures are used jointly, and the coefficient size sharply (§1.4 (e)).
3. Trace-integrality replaces lattice-integrality.
4. Elimination is free; well-foundedness and conjugacy are the inputs.
5. Every transported finite-rank mechanism has an exact price (§1.4 (f)); a theorem of the field names the price before the mechanism is used.

*Criteria.* It must reprove Weil's theorem for curves in a form that does not use finite rank at the decisive step, and the Lagarias–Suzuki line law `[L*]` in a form that does not use the truncated Eisenstein series. It must fail on: the golden datum, the integer-norm one-off, the approaching Euler product, the `cosh` models, the heat family, the non-tempered pair, and zeta functions with exceptional spectral parameters `s(1−s)=λ<¼` `[L*]`, `[C]`. It must not be uniform in real characters unless it excludes exceptional zeros. It must explain why integer norms in a free abelian monoid differ from lengths in a non-abelian group.

*Research topics.* A Kronecker theorem for trace-integral infinite-rank modules with duality. A notion of irreducibility for `ξ` (no factor with an FE and a Dirichlet series; compare the relocation obstruction `[L]`). Conjugacy classes of zeros: which zeros are forced to share a depth. The purity of a fixed part: what a family proves about the object common to all its members. The glued square: finite contacts, archimedean jets, a diagonal. Weight filtrations on infinite-rank cohomology of the Meyer flow and of the orientation cover. Semicontinuity of weights along towers.

---

## 8. A new field without positivity and without spectral theory

**Unlikely intersections on the prime torus.**

*What it is about.* The Bohr hull of ζ is the infinite torus of unimodular multiplicative twists; the vertical line is the orbit `t↦(p^{it})_p` through the identity. Haar-almost every fibre is zero-free right of `½` with natural boundary `½` `[L]`. The set of fibres with a zero right of `½+δ` is an exceptional locus of measure zero, and an off-line zero of ζ at height `γ` is a point of the orbit of the identity on that locus: an unlikely intersection. The field is the Diophantine geometry of such intersections, in the sense of Manin–Mumford, André–Oort and Zilber–Pink `[C]`.

*Dictionary.*

| Diophantine geometry | Prime torus |
|---|---|
| special subvarieties | torsion cosets and subtori; the Adams maps are the only exact symmetries of the orbit `[L]` |
| the orbit is special | function fields: the orbit is a closed one-parameter subgroup, zeros are periodic, AAL is free `[L]` |
| the base point is special | ζ: the identity (homogeneous approximation); a real character: a 2-torsion point (inhomogeneous) `[D]` |
| atypical intersections lie in special subvarieties | an off-line zero forces a structured event of the orbit: a heavy return or anti-return `[L]` |
| finiteness of atypical points | landing; B13 as the statement that isolated atypical points do not exist |
| recurrence of an atypical component | AAL as zero transport; Bagchi's criterion `[L*]` |
| counting rational points on transcendental sets | return counts; the depth floor in the number of logarithms |
| functional transcendence | hypertranscendence of ζ and differential independence of its dilates `[L]` |
| equidistribution in law | Matomäki–Radziwiłł, the density exponent `30/13`, almost-every-height cancellation `[L*]` |

*Tools it would develop.* Point counting on definable sets restricted to boxes of the strip. Zero estimates for exponential polynomials in `π(y)` logarithms with constants polynomial in the number of logarithms. Effective inhomogeneous bounds in three logarithms `log(−1), log p, log q`, which the upper side at the degrees `pᵃqᵇ` needs `[C]`. Ax–Schanuel statements for the orbit map. A graded form of Bagchi's criterion: how many returns exclude which zeros (§11.6). The involution of the hull induced by the FE.

*Criteria.* No sign and no operator. It must reproduce periodicity over `𝔽_q`. It must respect the label obstruction: `ζ(s−h)` has the same orbit, so the exceptional locus must be defined with the coefficient size or with the FE `[L]`. It must respect return–form duality: bounded-height Diophantine information reaches the Kronecker scale only, and rounded orbits are function fields `[L]`. It must be homogeneous or exclude exceptional zeros (§6). It must convert law into a statement at one point of the orbit; equidistribution alone does not `[L]`.

*Questions.* In which topology is the exceptional locus closed? Is it contained in a countable union of proper analytic subsets, and which of them are invariant under an Adams map? Does a point of the orbit on the locus force a near-relation among `log p`, `p≤y`, of height polynomial in the depth? Does emptiness of the heavy Bohr sets at the identity transfer to one window ((S3) of §6)?

*Main conjecture.* For every `δ>0` the orbit of the identity meets the locus of fibres with a zero right of `½+δ` in a set that is empty or recurrent with gaps controlled by the Kronecker scale.

---

## 9. A research programme for `𝔽₁`

### 9.1 Aim

Not a definition of `𝔽₁`. The aim is a geometry in which Spec ℤ has a product with itself and one of the two proofs for curves runs: Weil's (a surface with a Hodge index) or Stepanov's (an endomorphism and an auxiliary). §1.4 (d) says why nothing less will do: ζ is rigid, so no family replaces the base. The programme is `AbsoluteGeometryOfSpecZ` (AGZ); its card is `agz-absolute-geometry-of-spec-z`.

### 9.2 What the corpus fixes

- **Points.** `N(n)=Λ(n)+1+1/(n²−1)`; `Γ_1·Γ_n=N(n)` `[L]`. `N(n)` is not a cardinality; `Λ(n)=log Φ_n(1)` is the logarithm of the order of a fixed scheme `[S]`. The third term is `Σ_{k≥1}n^{−2k}`, the contribution of the trivial zeros.
- **The square in Λ-geometry** `[P]`. If descent to `𝔽₁` is a commuting family of Frobenius lifts, `Spec ℤ×_{𝔽₁}Spec ℤ=Spec W(ℤ)`. In ghost coordinates it is the ring `𝒢` of integer sequences with `x_{pn}≡x_n (mod p^{v_p(n)+1})`; `F_k`, `V_k`, `F_kV_k=k`; unique necklace coordinates `x_n=Σ_{d|n}d·b_d`; cofree among rings with Frobenius lifts over a ℤ-point. The component `x↦x_n` is the graph `Γ_n`.
- **Contacts.** `Γ_m∩Γ_n=Spec ℤ/J(m,n)`; `J(m,mp^j)=(p^{v_p(m)+1})`; two distinct graphs meet in at most one prime; `log#(ℤ/J(1,n))=Λ(n)` (`TheFrobeniusGraphsMeetInThePrimes`) `[S]`; `gcd(m,n)·log#(ℤ/J(m/g,n/g))` is the prime part of Weil's off-diagonal `[P]`.
- **Two half-products.** The zonotope surface with `Γ_m·Γ_n=m+n` and an exact count; the torsion half-product on `ℙ¹_ℤ` `[L]`.
- **Fibres.** `ℍ³` with one geodesic and the Green function at `s=½`; Bruhat–Tits trees at the Ramanujan point; a discrete carrier `Γ\(ℍ³×Π′_p T_p)` with commuting prime operators `A_p` `[L]`.
- **Diagonal.** Not local: atoms give the discriminant; Gram coupling leaves a signed defect; a truncation at degree `N` has genus of order `N log N`, archimedean in origin `[L]`. In the Λ-square there is none `[P]`.
- **Frobenius.** The Adams operations, exact on the torsion; `δ_p(a)=(a−a^p)/p` on ℤ and `δ_p x=(F_px−x^p)/p` on `𝒢`; the constants are the Teichmüller points `[S]`, `[P]`.
- **Cohomology.** Infinite rank; the explicit formula is the Lefschetz trace of the Meyer flow `[L]`.
- **Counts.** `Q` is not integer-valued; a count must be a limit, and a logarithm of a cardinality `[L]`.

### 9.3 Criteria

| # | Criterion | Test from the corpus | Reading on the Λ-square `[P]` |
|---|---|---|---|
| C1 | reproduces Weil and Stepanov for curves | count law of every hyperelliptic curve `[L]` | point counts of a curve are an effective element of `𝒢`; the three facts of Stepanov's count are located |
| C2 | counts alone are not enough | the golden datum must fail `[L/K]` | effectivity in `𝒢` does not imply purity |
| C3 | uses the FE | the integer-norm one-off and the approaching Euler product must fail `[L]` | absent: `W(ℤ)` is built from the finite primes |
| C4 | uses the Euler product | `cosh` models and the heat family must fail `[L]` | present: the graphs meet exactly in the primes |
| C5 | sees the tempered edge | the non-tempered pair must fail `[L*]` | absent: contact orders do not see the normalization `p^{1/2}` |
| C6 | distinguishes ℤ from geodesic flows | zeta functions with exceptional spectral parameters must fail `[L*]`, `[C]` | undecided |
| C7 | infinite rank, no stable lattice | lattice no-go `[L]` | `𝒢≅Πℤ` |
| C8 | the diagonal is Weil's, not the discriminant | locked dampings `[L]` | no diagonal |
| C9 | positivity, if used, is derived | λ-ring effectivity reduces to the Hodge index and does not prove it `[L]` | none used |
| C10 | the archimedean place is a fibre | `ℍ³` at `Δ=½`; the pole as the spherical piece `[L]` | absent |

### 9.4 Constructions

**A. Frobenius lifts (the Stepanov side).** Deliverables: the square in Λ-geometry; the Adams ring as a δ-ring; Stepanov–Bombieri with δ-multiplicity; the answer to (S1). Kill condition: δ-multiplicity at all primes of a window costs at least the Chebyshev count. **State: the ideal-power restriction theorem is exact; the whole-class claim for evaluated δ-jets needs Frobenius compatibility of the integer point.** Teichmüller elements show that arbitrary integer points do not preserve δ-order. Positive survivor: the square exists, is cofree, and carries the prime part of every intersection number exactly.

**B. Carries (transport of purity).** `ℤ_p` is `𝔽_p[[T]]` with addition deformed by the Witt carry polynomials; RH holds on the undeformed side. Deliverables: the carry cocycle as deformation parameter; a comparison of the prime count in a window with the exact count of irreducible polynomials; a statement of what a global tilt would be. Kill condition: the comparison error is of the size of the count. **State: met** `[P]`: `Σ_{k≤N}Λ(k)⌊q{N/k}⌋+Σ_{N<k≤qN}Λ(k)⌊qN/k⌋=log((qN)!/(N!)^q)`, and the carry term is a fixed positive proportion of the window count. Positive survivor: Teichmüller, digit and floor carries are one cocycle; the necklace coordinates of `[q]` count the irreducible polynomials over `𝔽_q`. The global tilt is undefined.

**C. The surface (the Weil side).** Continue from the adelic carrier: a global Green resolvent built from the `A_p` and the hyperbolic Laplacian, its Robin mass, and the two half-products as two projections of one object. Deliverables: the off-diagonal identity on the carrier; the diagonal as a global finite part; Riemann–Roch with the FE as duality. Kill condition: every global finite part differs from Weil's diagonal by a term of the size of the discriminant. **State: open.** The finite part of the product orbit exists `[L]`; its density constant matches Weil's archimedean constants `[D]`; on the modular surface the packet functional is the limit of Robin-normalized Maass–Selberg diagonals `[S]`; the question is (G) of §5.3.

**D. The archimedean fibre of the square.** The Λ-square lacks the cusp, the jets, the pole and the Gamma factor. The jets are the Lefschetz trace of the dilation of `ℝ` on even germs at its fixed point `[L]`. Deliverables: a ring or space with commuting maps `F_n` whose Lefschetz numbers are `1+1/(n²−1)`; its gluing to `𝒢` along the degree points; the FE as the duality exchanging the two. Kill condition: every gluing compatible with `F_kV_k=k` makes the archimedean intersection numbers depend on `mn` and not on `m/n` (the failure of toric metrics `[L]`).

**E. A second dimension.** The Λ-square is a curve. Stepanov's count and Riemann–Roch both need spaces of sections of bidegree `(a,b)` of rank of order `ab`. Candidates: the toric surface `𝔾_m²` with the power-map graphs, which has the pole plane and an exact count `[L]`, enlarged by torsion sections; geometries in which the square of ℤ does not collapse and is not a union of graphs `[C]`. Deliverables: a lattice of sections with a rank count; restriction to `Γ_n` multiplying the second degree by `n`; the product formula on each graph. Kill condition: on every such lattice the restriction to `Γ_n` has no forced zeros beyond `Γ_1∩Γ_n`, so the count returns the product formula.

### 9.5 Questions the programme must answer

| # | Question | Answer | State |
|---|---|---|---|
| 1 | Which endomorphisms have `N(n)` fixed points, and on what? | the Witt Frobenius `F_n` on the arithmetic square; its fixed scheme on the diagonal is `Spec ℤ/e^{Λ(n)}`; the terms `1` and `1/(n²−1)` are archimedean and are not in `W(ℤ)` | `[P]` |
| 2 | What is the multiplicity of a function at a prime over `𝔽₁`? | the order of the `p`-derivation, which on ℤ is `v_p`; between graphs the contact order `1+v_p(m)` of `Γ_m` and `Γ_{mp^j}` | `[P]`, `[S]` |
| 3 | Why is the diagonal not local? | in the Λ-square it is one component of a curve; its conormal module is torsion, of order `lcm(1,…,N)` after truncation | `[P]` |
| 4 | What is ampleness, and why would Riemann–Roch imply the Hodge index without assuming it? | — | open |
| 5 | Where do the Gamma factor and the pole enter as geometry? | not through a Λ-structure; they are the complement of `W(ℤ)` in Weil's form | half `[P]` |
| 6 | Why do monoids with integer norms that are not ℤ fail? | the Λ-structure sees the set of norms, not their multiplicities; the dividing line is additive, the count `⌊x⌋` | `[P]`, `[L]` |
| 7 | What is the normal direction to the diagonal? | — | open; construction E |
| 8 | Which duality exchanges the finite contacts and the archimedean jets? | — | open; construction D |
| 9 | Is Weil's diagonal a finite part of the glued object? | — | open; (G) of §5.3 |

### 9.6 Order of work

1. C1–C6 as a test suite on existing fakes, with the reading of each criterion on every construction that reaches it.
2. Construction C up to the torus-invariant finite part and its comparison with Weil's diagonal.
3. Construction D up to the gluing along the degree points.
4. Construction E up to a rank count for one bidegree.
5. Constructions A and B: Lean for the theorems of the card; no further search for a producer.

---

## 10. A research programme for a Galois theory of the zeros

### 10.1 The dictionary

For a curve of genus `g` over `𝔽_q` the Frobenius eigenvalues are the roots of a polynomial in `ℤ[T]`. Two involutions act on them: `ι: α↦q/α`, algebraic and commuting with the Galois group, and complex conjugation `c`. RH is `c=ι`. The Galois group lies in the hyperoctahedral group `(ℤ/2)^g⋊S_g`, the centralizer of `ι`; generically it is the whole group, and `c` is its central element `[C]`.

For ζ: `ι: ρ↦1−ρ`, `c: ρ↦ρ̄`.

> **RH ⇔ `c=ι` on the zero set ⇔ complex conjugation is central in the group of all permutations of the zeros commuting with `ι`** `[D]`.

The atoms translate: B13 is irreducibility (no finite exceptional set stable under the group), AAL is the statement that conjugate zeros share their depth, ZAL is well-foundedness. The fibre form is a theorem: RH ⇔ `ιc`, which preserves the height, acts trivially ⇔ the ordinate is injective on the zeros (`OrdinateInjectivity`) `[L]`; the horizontal spread of the fibres of the height map is twice the zero width (`fibre_spread_le_iff_zetaZeroWidth_le`) `[S]`. The mechanism is in Lean: an invariant function injective on the roots fixes every root (`fixed_of_injOn`, `mem_range_algebraMap_of_injOn`) `[S]`.

### 10.2 What an "algebraic equation" can mean

| Candidate | Roots and group | What the corpus has |
|---|---|---|
| Jensen polynomials of Ξ | roots of `J_d` over the field of Taylor coefficients; `c` has cycle type given by the non-real root count | `N_d` nondecreasing, `sup_d N_d` = off-line multiplicity, `N_d≤300√(d log d)`, inner roots real `[L]` |
| Local Weierstrass polynomials | `ξ=P_R·unit` on a rectangle `R`; coefficients are power sums `Σ_{ρ∈R}ρ^k`, contour integrals of `ξ′/ξ` | explicit contour and mass bounds `[L]` |
| Monodromy in a real family | zeros as functions of a parameter (heat time, cosine depth, Hurwitz shift); the group generated by the branch points | collision criterion; finitely many non-real zeros of `H_t`, `t>0`; only `τ=0` has a Dirichlet series `[L]` |
| The torus of the zero motive | character group = the additive group generated by the zeros; relations among ordinates | parity of ordinate relations and annihilator mass `[L]`; lattice no-go `[L]` |
| Differential Galois theory | relations among ζ and its derivatives | none exist: hypertranscendence, differential independence of algebraic dilates `[L]` |
| Adams∘FE dynamics | the maps `s↦ms` and `s↦1−s`; orbits of zeros | half-descent `s↦1−s/2`: every failure of RH has a right zero `ρ` with `ζ(ρ/2)≠0`; a halving pair forces `Θ≥2/3` `[L*]` |

### 10.3 Criteria

1. Over `𝔽_q` it reproduces the hyperoctahedral group and the centrality of `c`.
2. A large group does not imply purity: the golden datum has full monodromy and is impure `[L]`. The theory must locate `c`, not measure the group.
3. Integrality must enter as trace-integrality; Kronecker's theorem and finite certificates of integral purity are the finite-rank models, and the certificate length grows with `q` `[L]`.
4. It must be pointwise: generic zeros are indistinguishable, so any invariant definable over the ground field that holds at one zero of an orbit holds on the orbit. The first zeros are on the line `[L]`. The programme succeeds if "on the line" is such an invariant and the group is transitive.
5. It contains the separation proof of the Carlitz–Goss case `[C]` as a special case. Separation by absolute value is excluded for ζ; the separating invariant has to be the ordinate or a function of it (§6).

### 10.4 Questions

1. **Ground field.** Over which field `K⊂ℝ` generated by prime-side data are the power sums of the zeros in a rectangle defined, and is the Galois group of the local Weierstrass polynomial over `K` the full hyperoctahedral group?
2. **Location of `c`.** Is there a generating set of the group whose elements commute with `c` for a structural reason (monodromy along loops in a family defined over ℝ is conjugated by `c` to the monodromy of the conjugate loop)?
3. **Irreducibility.** Is `ξ` irreducible in the class of entire functions with an FE whose quotient keeps a Dirichlet series? The relocation obstruction (moving one quartet destroys the Dirichlet series on `Re s>1`) `[L]` and Hamburger's theorem `[L*]` are the theorems of this type.
4. **Separation.** The ordinate separates iff RH. Which prime-side computation proves injectivity of the ordinate on one rectangle without locating the zeros? Verification by counting sign changes is such a computation at finite height `[L]`; the question is its form uniform in the height.
5. **Stability under limits.** Do the Galois groups of `J_d` stabilize, and does the cycle type of `c` converge in a sense stronger than `N_d→` off-line multiplicity?

### 10.5 Tools to develop

Galois theory of local Weierstrass polynomials with coefficients given by contour integrals; a theory of conjugacy for zeros of Dirichlet series with an FE; monodromy of the zero set in real-analytic families and its interaction with `c`; trace-integral Kronecker theorems; Newton polygons and their archimedean substitutes (the Laguerre and Turán layers); the Adams∘FE correspondence on the strip.

### 10.6 Limit

In finite rank the centrality of `c` is a consequence of purity, not its proof. The programme has content only if question 2 or question 4 has an answer that does not pass through the sign.

---

## 11. Missed opportunities

### 11.1 Halving chains terminate

A theorem `[L*]` (`ArithmeticHolographyOfTheModularHorizon/HalvingDescentAndShimuraZeros`).

- If RH fails, some zero has `½<Re ρ<1` and `ζ(ρ/2)≠0` (`exists_right_zero_not_halved`).
- Any halving pair forces `Θ≥2/3` (`two_thirds_le_abscissa_of_halving_pair`).
- For a nonzero Hecke cusp eigenform `u` with nonzero first coefficient: RH ⇔ the energy of `u` has rate `O(y^{3/4−ε})` for every `ε` ∧ no nonhalving right zero `ρ` of ζ is a zero of the Shimura integral of `u` at `ρ/4+¼`.

Open: the nonvanishing, at points with real part in `(3/8,½)`. For a fixed `ρ` a first moment over the eigenforms would give one `u` that does not vanish there `[A]`; a statement for one `u` at all `ρ` is of a different kind.

### 11.2 The family step through twists and covers

The precise results of §5.2 `[L*]` give positive survivors: amplification strictly beats the trivial bound at nontrivial torsion fibres; positivity couples base to product in one direction; with the trace of ζ retained, sublinear tensor growth of a cover family is equivalent to RH. The Lean statement does not quantify over every arithmetic family or every inequality derived from one. Its Euler-weight countermodel does not retain an FE. The universal closure inside the FE class remains unproved.

### 11.3 Calibrations

- **Exceptional spectral parameters.** An eigenvalue `0<λ<¼` gives two real parameters in `(0,1)`, off the centre and exchanged by `s↦1−s` (`selbergSmallEigenvalue_offCritical`) `[L*]`; the complementary-series model is in `SelbergExceptionalSphericalModel` `[L*]`. Missing: a compact surface with its geodesic Euler product and the identity `s(1−s)=λ` for the zeros of its zeta function `[C]`. Its use: B13 is false in the non-commutative class, so any B13 argument must use the absence of real zeros in the strip, integer norms, or order one.
- **The Lagarias–Suzuki line law** `[L*]`. For `Y≥1`, `Λ(2s)Y^s+Λ(2s−1)Y^(1−s)` has no non-real zero off the line; at most one real exceptional zero lies to its right. The audited parity proof uses a Schur quotient and index one. Both obstacle ledgers now include this sign calibration.
- **Exceptional characters.** The two sides of a Dirichlet `L`-function are in the corpus: the upper side at the primes is GRH including real zeros; a real top masks the shallower zeros on the lower side `[L]`. The filter of §6 follows `[D]`.

### 11.4 Published mathematics and the corpus

| Result | State |
|---|---|
| Multiplicative functions in short intervals | in the corpus for `μ`, every `h→∞`, `h≤√x`, as a mean square over the fibres `[x/a,(x+h√x)/a]`, `a≈√x` `[L*]`. Not in the corpus: integer starting points for general bounded multiplicative functions; averaged correlations `Σ_{h≤H}|Σ_nλ(n)λ(n+h)|=o(HX)` `[C]`. The saving is in law and is a power of `log`; it does not touch an atom or the width axis `[A]` |
| Large values and zero density | in the corpus: Guth–Maynard `[L*]` |
| The Carlitz–Goss Riemann hypothesis | `[C]`; its mechanism is in Lean (`SeparationForcesRationality`) `[S]`; the statement for `𝔽_q[T]` is not |
| Twisted second moments past length `T^{1/2}` | `[C]`; needed in §4.4 |
| Stepanov's method for Heilbronn sums and Fermat quotients | `[C]`; a power saving, not square-root, at one prime in mixed characteristic; the fibres of the first carry polynomial of §9 |
| Effective lower bounds for linear forms in three logarithms | `[L*]` for the principal logs of `−1,p,q`: `ArithmeticOfSquareRootPrecision.exists_minusOne_primeLog_separation`. The affine real form `m+a log p+b log q` remains `[C]` |

### 11.5 Routes without a mechanism

| Group | Reason | Recommendation `[A]` |
|---|---|---|
| Scheduled sums: FU, CFC, RP | one-sided history floors; exact criteria; no source estimate beyond fixed horizons | keep the criteria; no further work without an estimate |
| Source completions: SEC, CDC, PCS; candidates APF, EWJ, RFHM, WBF | a source plus one condition at each actual zero; the condition is RH zero by zero | freeze |
| TH rank by rank | each rank is a finite rung from verified height; all ranks reduce to the adaptive head | stop at rank 14; work only on the head near critical zeros |
| The fourteen window routes | one form; positivity at aperture `a` gives a near-line zero-free statement to height `e^{a/K}` and follows from verification to `windowHeight(a)` `[L]` | treat as one route with one open step (the stage step) |
| Family and tensor branch | §5.2 | support |
| Frobenius lifts and carries | B: the carry error has the size of the count; A: ideal-power restriction gives the exact contacts; unrestricted descent of evaluated δ-jets is false `[L*]`, `DeltaOrderDoesNotDescendAtEveryIntegerPoint` | the exact Frobenius-compatibility law replaces the overbroad δ-order claim; retain both positive survivors |
| Exceptional-current upper bounds | §2, second observation | close unless an inequality using the FE is named |

### 11.6 Small assemblies

| Item | Statement | State |
|---|---|---|
| Width and absolute forms of the log-square criterion | `zeta_re_le_iff_prime_logSquare_power_windows`, `zeta_re_le_iff_abs_prime_logSquare_power_windows`, `riemannHypothesis_iff_abs_prime_logSquare_windows` | `[L*]` |
| Quasi-RH on windows; `qRH ∨ AAL`; tail law | `quasiRH_iff_prime_logSquare_power_windows`, `quasiRH_or_asymptoticAbscissaLaw`, `quasiRH_iff_zetaAsymptoticAbscissa_lt_one` | `[L*]` |
| The ¬AAL world | `asymptoticAbscissaLaw_or_mertens_power_saving`, `asymptoticAbscissaLaw_or_stronger_heavy_return_power_bound` | `[L*]` |
| Census alternatives at `70%`, `75%`, `80%` | `seventy_percent_…`, `three_quarters_…`, `four_fifths_or_simple_offLine_near_line` | `[L*]` |
| Signed deletion on log-square windows | the absolute criterion with complex three-point filters, no positive averaging: `riemannHypothesis_iff_abs_prime_logSquare_windows_signed` | `[L*]` |
| Logarithmic windows | radius `32 log(T+2)`; width, absolute, quasi-RH and Stepanov forms | `[L*]`, `ScaleLocality/PrimeLogarithmicWindows` |
| **Density row of the coupled orbit** | `4·regularMean=−2γ₀−(log 4π+γ)`, `γ₀=gammaHardyPhaseRate(0)` | `[L*]`, `ArchimedeanConstantBridge.four_mul_regularMean_eq` |
| **Census baseline in covariance form** | ceiling `4π(1−0.67250071)` for the source covariance, strictly below `4π/3` | `[L*]`, `Census/SourceCovarianceBaseline` |
| **Exchange-rate rows** | `H*(4)=7/10` at `λ*=10/9`: `70%` from `F≤4` on `(1,10/9)`; the Frobenius constant for `70%` at `λ=4/3` is `13/10` | `[L*]`, `TransThresholdPairCorrelation/SeventyPercentExchangeRates`; the actual bound `F≤4` remains open |
| **Graded recurrence** | For `1/2≤σ≤5/6`, `c>(30/13)(1−σ)`, `T^c` one-separated self-returns in `[0,T]` for every sufficiently small disc exclude a zero with `Re ρ>σ`; one return at arbitrarily large height is AAL `[L]` | `[L*]`, `Recurrence/GradedSelfRecurrence`, using the actual Guth–Maynard bound |
| **Upper side at the degrees `pᵃqᵇ`** | the cubic construction needs an effective bound for the affine real form `2c+a log p+b log q`; replacing its constant term by `log(−1)=iπ` changes the form | `[C]` affine input; assembly open |
| Two-prime local criterion | A65: lower bounds on two-prime difference lags in arbitrarily late `r√T` windows ⇔ RH, every fixed `r>0` | `[L*]`, `ScaleLocality/TwoPrimeLocalWindows` |
| Dominant-ordinate divergence | A67: one ordinate's grouped Gamma mass exceeds the other ordinates' mass; the corrected current's norm tends to infinity at every supercritical speed | `[L*]`, `ExceptionalLayerTheory/ADominantOrdinateForcesCurrentDivergence`; multiplicities included |
| Finite-stratum laws on the cosine and shifted Jensen families | A50 | `[L*]`: the shifted Jensen law implies RH; under the cosine law, RH ⇔ ZAL. The cosine law alone still needs finiteness near zero |

---

## 12. Answers in one line each

1. **Big picture.** One inequality per prime on sparse log-square windows, and three atoms; solved: the reductions, the locality, the sign-free decision and its local form, the model classifications, rigidity, the named fixed-part moment laws, the Frobenius shadow, the square of Spec ℤ in Λ-geometry, a geometric normalization of Weil's functional on packets; standing: a pointwise producer past VK, the atoms, the dark range, the diagonal as a self-intersection and a second dimension, the two-scale input.
2. **Opportunities.** Logarithmic windows are formalized. Open: one object for the diagonal; `70%` from a bounded form factor; higher Gram moments; the archimedean fibre and a second dimension of the square.
3. **Quasi-RH.** No clear path; it is the tail law `Θ∞<1`, a one-sided power saving on sparse windows, and has no rung below it.
4. **Seventy per cent.** No clear path; `67.25%` is proved; `70%` is equivalent to a covariance ceiling `6π/5` and follows from `F≤4` on `(1,10/9)`; the missing estimate is a signed prime-pair bound.
5. **One question.** Are the contacts of the arithmetic square, the finite part on the adelic carrier and the packet functional of the scattering tower one object, with Weil's diagonal as its finite part?
6. **Without positivity.** Both shadows are priced; no question below quasi-RH passes every test; the one to decide is whether homogeneous breadth at the heights of one window transfers to the bound at its primes.
7. **New field.** Infinite-rank purity theory, in law and at a point.
8. **New field without positivity.** Unlikely intersections on the prime torus, at the homogeneous point.
9. **`𝔽₁`.** The Λ-square exists and is a curve; the carry obstruction and ideal-power contact law are proved; unrestricted descent of δ-order fails. Open: the surface, the archimedean fibre, a second dimension, ampleness.
10. **Galois theory.** RH ⇔ complex conjugation is central ⇔ the ordinate is injective; locate `c` or prove injectivity without locating the zeros.
11. **Missed.** Small assemblies and the Lagarias–Suzuki calibration are audited; the compact-surface calibration, published analytic inputs and affine two-prime upper bound remain. The cosine criterion still needs its tail input; broad family and δ-order closures require the scope corrections in §11.
