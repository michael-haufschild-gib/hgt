# Arithmetic Criticality Theory (ACT)

Umbrella `ArithmeticCriticalityTheory.lean` (88 modules, flat folder). Namespace
`GaloisForLFunctions.ArithmeticCriticalityTheory`. Inputs: `RHTower` (Doob tests `phiDoob`, Weil–Markov–pole
split, odd/half-line RH criteria, CCM/Suzuki restricted Weil ground energy, PNT `psiSum`, γ bounds),
`ArithmeticIncidencePositivity` (odd window folds, shifted-pair zero form, atom-vs-pole classification),
`arithmetic-positivity-theory` (`Ẑ` = real Weil functional, `Re W_ζ` split), `SquareRootThreshold` (height
windows), `HTGeometry` (Hadamard quotient `smoothCoordinateQuotient`), `BiScaleUncertainty` (power nodes).

## 1. Motivation

RH is the sign of one quadratic jump form. With Riemann's kernel `Φ` and `F = Φv`:

`RH ⇔ Q(Φv) = E_arch(v) + E_prime(v) − ∫Φ cosh(x/2) v² ≥ 0` for every odd `v ∈ C²_c`,

jump energies `∫dm(t)∫Φ(x)Φ(x+t)(v(x) − v(x+t))²`, jump measure `dm = ω(t)dt + Σ Λ(n)n^{−1/2}δ_{log n}`.
For a finite Z-type jump form, nonnegativity ⇔ a positive supersolution exists (Allegretto–Piepenbrink,
proved here: `nonneg_iff_exists_pos_supersolution`). ACT transports ground-state and criticality theory
(Pinchover trichotomy) to this arithmetic operator and asks four questions: does a positive supersolution
exist; if not, what carries positivity; how critical is the form; where can positivity be proved outright.

Answers: no positive supersolution exists (two-moment law); positivity lives in a gauge-free zero form whose
only non-Z-type part is the prime anti-diagonal; the form is critical in every direction (no Hardy weight,
no rate slack, no variance slack); positivity is provable on windows up to aperture `3/10`.

## 2. Objects

Kernel and densities.
- `Φ = riemannKernelReal`: even, positive, strictly decreasing on `[0,∞)`, `Φ(u) ≤ Ce^{9|u|/2}e^{−πe^{2|u|}}`,
  `∫Φcosh(x/2) = 1/2`, Mellin transform `ξ`.
- Archimedean rate `ω(t) = e^{−t/2}/(1 − e^{−2t}) = 1/(4sinh(t/2)) + 1/(4cosh(t/2))` (`archLevyDensity`),
  strictly decreasing, infinite mass (only differences converge). Diagonal density `ν = e^{−2u}/(1 − e^{−2u})`,
  killing `N(a) = ∫_a^∞ν = −½log(1 − e^{−2a})`. Sharp: `½ + u/4 − u²/48 − u³/32 ≤ uω ≤ … + u⁴/1152 + u⁵/256`
  on `(0,1]`.
- Weil jump density `κ = ω − 2cosh(t/2)` (`weilJumpDensity`): strictly decreasing; `> 0` iff
  `t < log ρ ≈ 0.2812` (plastic number `ρ³ = ρ + 1`).

Operators.
- Two-sided generator `𝓛_D` (Dirichlet) and folded generator `𝓛_N` (Neumann, = `𝓛_D` of `ω(|·|)`) on odd
  gauges; `𝓛_N = 𝓛_D − 2Φ·C` (reflected collar mass `C`).
- Pole-free Weil operator `𝒲M = Σ Λn^{−1/2}(M(x+log n) + M(x−log n)) − ∫_0^∞[2νM(x) − ω(M(x+u) + M(x−u))]
  + (γ + log π)M`. Harmonic identity `𝒲Φ = cosh(x/2)`. Source of any gauge `ω = M/Φ`:
  `𝓛_Dω − Φcosh(x/2)ω = −Φ·𝒲M`.

Gauges (`M = Φω`).

| Gauge | `M` | Source `/Φ` |
|---|---|---|
| constant | `Φ` | `−cosh(x/2)` |
| translate `τ_b` | `Φ(·−b)` | `−cosh((x−b)/2)` |
| shifted ground state `ω_a` | `m_a = Φ(·−a) − Φ(·+a)` (odd, > 0 on `(0,∞)`) | `2sinh(a/2)sinh(x/2)` |
| span / smeared | `Σc_j m_{a_j}`, `∫ν(c)m_c dc` | `σ sinh(x/2)` |
| theta convolution | `Φ∗φ` | `−(A_φcosh(x/2) − B_φsinh(x/2))` |
| window gauge | `q·plateau`, `q = 1 − cy² + dy⁴`, radius `R`, `2R < log 2` | `−𝒲M`, purely archimedean |

Harmonic gauges (zero source) = translate/convolution combinations with `A = B = 0` (`σ = 0` on the odd
span): infinite-dimensional, none positive on the half line.

Energies of `v = ωu` (shifted ground states).
- Same-side `S_a`, reflected sum, reflected difference `D_a` (collar `0 < x < t`: jumps crossing the origin);
  ground remainder `R_N = 2S + reflected sum ≥ 0`; collar mass `C_a`; fold excess weight `W_a ≤ C_a`.
- Half-line measure `μ_a = m_a sinh(x/2)`, mass `sinh(a/2)/2`; profile moment `∫u dμ_a`; profile
  variance `V_a = 4sinh(a/2)∫(u − ū)²dμ_a`; cross term `X_a`.
- Signed jump energy `J_M(u) = ∫dm∫M(x)M(x+t)(u(x) − u(x+t))²` (conductance negative across nodes of `M`);
  variance energy `∫∫μμ(u(x) − u(y))²`.

Forms.

| Form | Definition | RH content |
|---|---|---|
| Markov `Q` | jump energy − `∫Φcosh·v²` | `≥ 0` on odd; `Q(Φu_L) → −1/2` on even |
| zero form `Z` | `Q − 2(∫F sinh(x/2))²` | `≥ 0` on odd; kills odd theta span |
| full zero form `Ẑ` | `Q − 2(∫F sinh)² + 2(∫F cosh)² = Q + 2(∫Fe^{x/2})(∫Fe^{−x/2})` = Weil form | `≥ 0` on all real tests; kills whole theta span |
| Lorentz form | `(B² − A²)/2` on translates | explicit formula with every zero erased |
| pole-free variation | `2S_a − D_a + V_a = Z(m_a u)` | gauge invariant |
| ground energy `μ(A)` | inf Rayleigh quotient of `Ẑ` on `(−A,A)` (CCM restricted); `μ₀` pole-vanishing | `μ ≥ 0 ∀A ⇔ μ(A) → 0` |
| shifted pair `Ẑ_a` | zero form of `Λ(s−a)Λ(s+a)` | not positive on any window |

## 3. Language

- **Test vs Doob coordinates**: `F = Φv` vs profile `u = v/ω`, `M = Φω`. Mixing them is the first error.
- **Supersolution / subsolution**: `𝓛ω ≥ / ≤ Φcosh(x/2)ω`. **Z-type**: nonpositive off-diagonal
  (`|v|` does not raise energy). **Defect** = source minus collar.
- **Super-/sub-/critical**: negative value / nonnegative without Hardy weight / Hardy weight `W ≥ 0, ≠ 0`
  with `Q ≥ ∫WF²`. **Null sequence**: plateau truncation `ωu_L` of a pole-free gauge, energy `O(e^{−8L})`.
- **Radical**: directions `Q` cannot see (harmonic theta span). **Pole moments** `A = 2∫F cosh`, `B = 2∫F sinh`.
- **Two moments**: jump-measure moment `∫M dm` (origin) and half-line cosh moment `∫_0^∞M cosh(r/2)`
  (infinity).
- **Collar ratio** `R(a) = lim C_a/(sinh(a/2)sinh(x/2)) = 2 + 2∫_0^∞e^{−r/2}m_a/sinh(a/2) > 2`.
- **Visibility threshold**: `ω_a` sees an extra jump of length `ℓ` at infinity iff `e^{−2a} + e^{−2ℓ} < 1`.
- **Aperture / contact aperture**: half-width `A` of the test window; first `A` with `μ(A) ≤ 0`.
- **Even fold**: even profiles pair jump `s` at `x` with its reflection `s + 2x`; **folded conductance**
  `κ(s) + κ(s+2x)`; **fold cost** `G` = its negative part, paid by the potential. **Hub**: a set `Z` whose
  pairs carry a Poincaré constant. **Anchors**: tangents of `−½log(1 − s)` at `1 − (3/4)^k(15/16)^j`.
- **Light cone**: odd-coordinate antisymmetric kernel `κ(s) − κ(s+2x)`.

## 4. Mechanisms

1. **Ground-state representations.** Pointwise `(ω_xu_x − ω_yu_y)² = ω_xω_y(u_x − u_y)² + (ω_x − ω_y)(ω_xu_x² −
   ω_yu_y²)`. Folded: `Q(Φ(ωu)) = R_N + 2∫_{x>0}u²ω(𝓛_Nω − Φcosh ω)` (remainder ≥ 0 for `ω ≥ 0` on half
   line). General gauge, any parity: `Q(Φ(ωu)) = J_M(u) + ∫u²M·g`; harmonic gauges give pure signed Dirichlet
   forms. All from the weak form `Q(Φz) = ∫z(𝓛_Dz − Φcosh z)` (summation by parts) + Leibniz rule.
2. **Exact sources from the harmonic identity.** `𝒲Φ = cosh(x/2)` (theta functional equation) gives every
   source above with archimedean diagonals cancelling; no estimates.
3. **Two-moment obstruction.** Folded source `/Φ → −2∫M dm` as `x → 0⁺`; `/(Φe^{x/2}) → −2∫_0^∞M cosh(r/2)`
   as `x → ∞` (two-sided, odd `M`: `→ 2∫_0^∞M sinh`). At infinity the generator sees a profile only through
   its moments at the poles `e^{±r/2}`. Nonneg profiles make both moments positive ⇒ strict subsolution at
   both ends. Independent routes: prime 2 at the origin; theta harmonic identity at infinity (no PNT); prime by
   prime at `x = log p + y₀`; PNT gives exact ratios (`R(a) > 2`, cosh-moment law).
4. **Theta span is Lorentzian and radical.** Plateau laws: span `Q(Φ(ωu_L)) → 2σ²` (square of one linear
   functional); translates `→ (B² − A²)/2`, signature `(1,1)` plus infinite null space `A = B = 0`; harmonic
   gauges are a radical (`|Q(Φ(v + ωu_L)) − Q(Φv)| = O(e^{−8L})`). `Ẑ` annihilates the whole theta span.
5. **Pole subtraction.** Source `4sinh(a/2)∫u²dμ_a = 8(∫u dμ_a)² + V_a`; `Q = (2S − D + V_a) + 8·moment²`;
   `Z(m_au) = 2S − D + V_a` for every shift (gauge invariance); in any odd gauge `Z = J_M + V_μ`, variance
   conductances `2sinh(x/2)sinh(y/2)` positive across the origin where jump conductances are negative.
6. **Single-shift completeness.** `F = m_a·(F/m_a)` (Hadamard quotient, `m_a` vanishes only at 0) realises
   every odd test vanishing near 0 at every shift ⇒ each frontier inequality at one shift is RH.
7. **Criticality by null sequences.** Pole-free pairs `sinh(n/2)m_1 − sinh(1/2)m_n` separate points ⇒ no
   Hardy weight (odd sector and primitive hyperplane `∫F cosh = 0`); `Q(Φv) < εJ_ℓ(v)` for every jump length
   ⇒ every prime rate `Λ(n)n^{−1/2}` is least admissible; `Z < εV_μ` in every smeared gauge; capacity ratio
   `S(Φv)²/(2Q) → 1`; `μ(A) → 0` with Gaussian ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`.
8. **Archimedean Z-type; light cone.** Reflected jump at `(s+2x, x)` = same-side jump `J_s(x)`, so
   `D_arch = 2∫∫ω(s+2x)J_s ≤ 2S_arch` (`ω` decreasing). With `2cosh((s+2x)/2) − 2cosh(s/2) =
   4sinh(x/2)sinh((x+s)/2)`: arch surplus `+ V_a = 2∫∫(κ(s) − κ(s+2x))J_s > 0`, no threshold. Hence
   `Z(Φ(ω_au)) = positive light-cone energy + 2S_prime − 2Σ_nΛ(n)n^{−1/2}∫_0^{log n/2}(reflected jump)`:
   every failure of RH sits on prime anti-diagonals `x + y = log n`.
9. **Window gauges.** For `2R < log 2` no prime shift lands back: `Ẑ(Mu) = ∫κ·I_M + ∫u²M(−𝒲M +
   2∫M(y)cosh((x−y)/2))` (`I_M` gauge jump profile). The pole enters as a positive mass, `−𝒲M` as killing
   `N(a) + N(b)` minus `γ + log π` plus regional curvature gains. Stages: flat plateau; pole as conductance;
   curved `q = 1 − cy²`; parity split `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`; even fold (free up to `log ρ`); quartic
   `q`; fold cost past `log ρ` (one-point, then two-point using the gain `κ(s) + κ(s+2x) ≥ 2f(m) + 36x²`);
   sharp Lévy moments. Odd sector from `ArithmeticIncidencePositivity` folds. Each certificate is a 1-D
   polynomial inequality on anchored pieces.
10. **Transfer.** `Ẑ` is translation invariant; `Re W_ζ(g,g) = Ẑ(Re g) + Ẑ(Im g)`; Rayleigh/GLB gives `μ(A)`
    floors; window floor `w(A) = −log 2A − (3/2)A − (γ + log π) − 4A³` = Suzuki main term.
11. **Selectivity.** `Ẑ_a(F) = 2Ẑ(F) + 4∫(cosh(at) − 1)(2cosh(t/2) − ω)A_F` on short windows. Even
    extension `G_a + G_a(−·)`, `G_a = e^{−ay}H`, turns the negative off-diagonal coupling into diagonal:
    `Ẑ_a < 0` on some even test in `[−r,r]` for every `r` and large `a`.
12. **PNT asymptotics.** Abel summation with `ψ`: reflected prime mass `e^{−x/2}P_M → ∫_0^∞e^{r/2}M`, direct
    mass `→ ∫_0^∞e^{−r/2}M`; `e^{r/2} = 2sinh(r/2) + e^{−r/2}` splits twice-the-source from the other-pole excess.
13. **Pole-dominated positivity.** Wide plateaus `Q ≥ sinh²(a/2)`; far-apart bumps with `∫g e^{u/2} ≠ 0`
    (log-window PNT); mean-corrected profiles converge to the pole-free form. Hard core: mean-zero profiles.
14. **Shift averaging.** `∫_0^∞m_a(x)m_a(y)da = G(x−y) − G(x+y)`, `G = Φ∗Φ`; averaged source
    `2∫u²sinh²(x/2)`; Bessel `8∫moment² ≤ 2∫u²sinh²`.

## 5. Pillar theorems

1. Folded sufficiency `riemannHypothesis_of_foldedSupersolution`; two-sided exact source
   `twoSidedGenerator_shiftedGroundState_sub_potential`.
2. Two-moment no-go: `exists_origin_and_infinity_windows_foldedGenerator_lt_potential`,
   `tendsto_foldedSource_div`, `tendsto_shiftedCollarMass_div_source`.
3. Theta span: `exists_abs_markovEnergy_translatePlateau_sub_le` (Lorentz law),
   `abs_markovEnergy_add_harmonicPlateau_sub_le` (radical).
4. Gauge-free forms: `poleFreeForm_eq_zeroForm`, `riemannHypothesis_iff_forall_odd_zeroForm_nonneg`,
   `riemannHypothesis_iff_forall_fullZeroForm_nonneg`, `riemannHypothesis_iff_forall_nonneg_cone`,
   `zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`, `markovEnergy_phiDoob_mul_eq_signedJump_add_source`.
5. Single-shift completeness `riemannHypothesis_iff_forall_poleFreeVariationInequality`.
6. Criticality: `riemannHypothesis_iff_nonneg_and_no_hardyWeight`, `riemannHypothesis_iff_isLeast_primeRate`,
   `exists_zeroForm_lt_mul_varianceEnergy`, `riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`,
   `ccmRestrictedWeilGroundEnergy_gaussian_of_riemannHypothesis`.
7. Light cone: `archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy`,
   `zeroForm_shiftedGroundState_eq_antisymmetric_weilJumpDensity_add_prime`.
8. Unconditional windows: `fullZeroForm_ge_of_support_le_threeTenths`, `windowFloor_eq_suzukiMainTerm`,
   `foldBoundary_window_selective`.

Window floors (all unconditional, `Ẑ(F) ≥ c∫F²` for `supp F ⊆ [−A, A]`, hence `μ(A) ≥ c`):

| `A` | `c` | gauge |
|---|---|---|
| `< e^{−2}/2` | `3/40` | flat plateau |
| `21/200` | `1/30` | pole as conductance |
| `29/200` | `1/125` | past plastic density |
| `39/200` | `1/50` | quadratic `1 − 15y²` |
| `6/25`, `13/50` | `1/250` | even fold, quadratic / quartic |
| `7/25` | `1/500` | quartic at fold boundary |
| `29/100` | `1/1000` | one-point fold cost |
| `3/10` | `1/5000` | sharp moments + two-point fold cost |

Mean-zero (both pole moments 0) even profiles: margin `1/10` on `[−1/3, 1/3]`, `1/20` on `[−7/20, 7/20]`
(prime 2 inside).

## 6. Tools

Developed.
- Generator calculus: weak form, Leibniz commutator, bilinear summation by parts, polarisation, collar Fubini.
- Exact source equations for translate, shifted, span, convolution, and arbitrary profile gauges.
- Plateau families `u_L` (Lipschitz constant independent of `L`), plateau localisation `O(e^{−8L})`.
- Asymptotic machines: reflected/direct prime mass via Abel summation; origin jump-moment law; log-window PNT.
- Null-sequence constructors (pole-free pairs, harmonic even pairs + `ε_L` correction, Hadamard quotients).
- Window toolkit: killing bracket, sharp Lévy moments `P_k − E_k ≤ m_k ≤ P_k − E_k + E⁺_k`, quartic profile
  potential, even-fold identity `∫κI = 2∫∫(κ(s) + κ(s+2x))J_s`, fold-cost lemmas, hub Poincaré
  (`hub_energy_ge`), Schur step `A(t − c)² + Bt² ≥ c²AB/(A + B)`, anchored piecewise certification.
- CCM transfer: `Ẑ ↔ Re W_ζ ↔ μ(A)`; window floor `w(A)`.

To build.
- A signed gauge with global control of its nodal remainder (opposite-moment profiles are positive at both ends
  but have signed conductances).
- Coercive norm for `Z` on (tests)/(theta span).
- Prime anti-diagonal vs same-side comparison inequality.
- Even-sector certificate across `½log 2` (a prime shift lands back in the window).
- Hub/Schur certificates past `3/10` (the hub lemma is proved; only `k = 0` is used so far).
- Quantitative Harnack across growing prime shifts.

## 7. Open questions

1. **Prime anti-diagonal inequality.** RH ⇔ `Σ_nΛ(n)n^{−1/2}∫_0^{log n/2}R_{log n} ≤ light-cone energy +
   S_prime` for even profiles at one shift. Which prime-side structure pays anti-diagonal atoms? Criticality
   says no slack exists.
2. **Quotient coercivity.** Is there a norm `N` with `Z ≥ N` on odd tests modulo the theta span? (No Hardy
   weight exists, so `N` must vanish on null sequences.)
3. **Even windows past `½log 2`.** Odd and mean-zero sectors cross `½log 2`; the even sector with nonzero
   pole moments stops at `3/10`. Does the hub/Schur step carry the even fold further, and where does the first
   prime atom enter?
4. **Contact aperture.** Locate (or bound below) the first `A` with `μ(A) ≤ 0`; currently `> 3/10`.
5. **Monotone cone.** The weight criterion `W_a ≤ 2sinh(a/2)sinh(x/2)` is false for large `a`; which
   weaker statement uses same-side terms away from the origin?
6. **Selectivity classes.** Which features of `ζ` (beyond those shared with `ζ(s−a)ζ(s+a)`) does window
   positivity use? Separate theta-equation identities from universal gauge algebra.
7. **Signed gauges.** Profiles with `M'(0)∫M dm < 0` and cosh moment of opposite tail sign have positive
   quadratic potential at both ends; can the middle and the signed remainder be controlled?
8. **Atom vs pole.** Which moduli are atom-dominated in collars (`2,3,4,5,7` proved; `6` is polar-only)?

## 8. Traps

| Trap | Correct statement |
|---|---|
| Positive even supersolution on `ℝ` | Impossible: `Q(Φu_L) → −1/2` (constant profile is the negative direction) |
| `𝓛_D`-supersolution certifies | Its remainder is indefinite; only `𝓛_N` has `R_N ≥ 0` — and `ω_a` is an exact strict `𝓛_D`-supersolution, useless alone |
| Some positive folded supersolution exists | None: every nonneg decaying profile fails at origin and infinity |
| Superpositions / convolutions fix it | Span, signed combinations, smeared and convolution gauges all fail (same pole moment) |
| Weight criterion `W_a ≤ 2sinh sinh` | False for all large shifts (`exists_not_weightCriterion`) |
| Shift carries information | Shift is a gauge; single-shift statements are RH |
| Frontier "variation inequalities" are progress | `D ≤ 2S + V_a`, cone, capacity, light-cone, prime forms are all equivalent to RH |
| Source = pole term | Source = pole term + variance; zeros live in mean-zero profiles |
| Plateau/bump positivity says something about zeros | Pole-dominated; theta span erases zeros |
| A Hardy weight, smaller rate, or less variance | All critical: no slack anywhere |
| Shift averaging weakens the target usefully | Single shifts are already complete; averaging only reweights |
| `J_M` positive in a positive gauge | Negative somewhere in every smeared gauge |
| Plastic threshold `log ρ` bounds positivity | It bounds only the free even fold; `κ(s) − κ(s+2x) > 0` everywhere in odd coordinates; windows pass it |
| Window positivity follows from Euler product + functional equation | Selective: `ζ(s−a)ζ(s+a)` shares both and has negative even tests at every radius |
| Window certificates touch the primes | All-profile windows (`≤ 3/10 < ½log 2`) are purely archimedean; only the pole-vanishing sector (`[−7/20, 7/20]`, via `RHTower`) contains prime 2 |
| `μ(A)` has margin at large aperture | `μ(A) → 0` doubly exponentially under RH; `→ −∞` otherwise |
| Total jump rate finite | `∫ω = ∞`; only differences converge |
| `FoldedAdmissible` is harmless | It is a hypothesis of the folded criterion; discharged only for `ω_a` |
| Docstrings of `…_threeTenths` say `29/100` | Statements are `3/10` |

## 9. Context

- Reverse dependencies: `SquareRootThreshold` (8 modules), `ArithmeticIncidencePositivity` (7),
  `ArithmeticContinuationAndCriticalEnergy` (3), `ArithmeticCastelnuovoSeveri` (3),
  `TransHorizonIncidenceMechanics`, `ArithmeticOrientationTheory`, `arithmetic-positivity-theory` (2 each),
  `TransThresholdPairCorrelation`, `SignChangingScrewGauge`, `CriticalArithmeticCorrelationTheory`,
  `BiScaleUncertainty`, `ArithmeticLorentzianGeometry`, `ArithmeticCompensationTheory`, `MainTheorems`.
- ACT owns the gauge theory of the Weil form in Doob coordinates and the aperture function `μ(A)`.
  `ArithmeticIncidencePositivity` supplies the odd-sector folds and pays reflected prime conductances;
  `SquareRootThreshold` turns ACT's window positivity into height-window statements; `arithmetic-positivity-
  theory` identifies `Ẑ` with the Weil functional; `TransHorizonIncidenceMechanics` uses the same odd theta
  gauges (`oddProfile = m_a/(2sinh(a/2))`).
- Bridge results to `BiScaleUncertainty` (atom vs polar collar mass, power nodes) are cross-programme facts,
  not RH progress.

## 10. Big picture

ACT asked whether RH has a positive ground state, the way nonnegative Schrödinger operators do. It does not:
the arithmetic operator reads any positive profile only through two moments, and both have the wrong sign.
What remains after removing the poles is a single gauge-free form that is exactly critical — no direction has
slack, and the obstructing directions are precisely the theta-span combinations with zeros erased. Inside that
form the archimedean place is harmless and strictly positive at every scale; all difficulty sits on the prime
anti-diagonals, where reflected jumps cross the origin. Positivity can be proved, unconditionally and with
explicit constants, on windows up to `3/10`, and these certificates are genuinely selective: an `L`-function
with the same Euler product and functional equation but off-line zeros fails on every window. Yet they live
below the first prime, where the form is purely archimedean. The lesson for the RH programme: reformulations
are cheap and all equivalent; gauges, shifts, superpositions and averages only move bookkeeping; the live
content is a prime-side inequality between anti-diagonal and same-side atoms, which no window certificate has
yet reached.
