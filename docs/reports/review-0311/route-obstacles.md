# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates, and the programmes and support lines that feed them
(ADT, AHD, CWS, WTZ, DZG, ATD, CACT, CAF, RIT, the prime-blind line PBAP), read against the Lean
corpus at `4c804b1979` with the working tree. For every route: what is established, how its open
obligation reads on the window tower, the obstacles that are **(A) just work** and the obstacles that
are **(B) open mathematics**. Just work: known mathematics, finite or certified computation,
effectivization, composing proved statements, integrating unfinished modules. Open mathematics: a
statement nobody knows how to prove.

Evidence: `[L]` Lean in the corpus; `[W]` Lean in the uncommitted working tree; `[P]` paper proof or
plan; `[N]` numerical only; `[D]` derived here from Lean statements, not formalized.
Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies a zero-free half-plane and Lindelöf;
**sub** strictly weaker or of unknown strength; **indep.** not implied by RH and not known to imply it;
**method** a missing tool, not a statement; **identity** an exact identity, true or false independently
of the zeros.

Window lengths `A` (window `[−A, 0]`); RW, LST, ACS and SP use the half-width `a = A/2`. Wall labels
Σ/Π/Γ refer to `walls-ledger.md`; classes C1–C18 to `route-unification-ledger.md`. Programme codes follow
the frontier-map source locator; ATD = ArchimedeanTateDomination, DZG = DimensionZeroGeometryOfSpecZ,
WTZ = WindowTowerOfSpecZ, PBAP = the prime-blind modules of RHTower.

## 0. The window picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ `Q(H) ≥ 0` on every window test of every length; a window of length `A` reads `Λ(n)` only for `n ≤ e^A` | CWS `TheWindowDatum` [L] | every positivity route is a statement about windows |
| Window algebra = Dirichlet ring truncated at `⌊e^A⌋`; `ρ_A(Λ) = [M, log Z]`; `ζ ≡ exp(Λ/log)` on every window; `ζ ≡ exp Σ_a ψ^a(P)/a` (plethystic exponential of the prime folds) | WTZ `TheWindowDirichletAlgebra`, `TheTateFamilyIsAnExponentialOfPointCounts`, `TheWindowZetaIsAPlethysticExponential` [L] | the arithmetic of a window is a finite local λ-ring; the prime powers of a window are the primes of the windows `A/2, A/3, …` |
| Hilbert function of the tower = Landau's `π_k(N)`; socle spanned by `(N/2, N]`, dimension `⌈N/2⌉`; Gorenstein iff `N ≤ 2` | WTZ `TheHilbertFunctionOfTheTower` [L] | no one-generator (Serre-type) duality past `log 3` |
| `Q = Ω(0)τ_H(0) − 2τ′_H(0) + J_∞ + pole`, `τ_H(k) = ⟨ρ_A(J_k)H,H⟩`, `J_k ≡ exp(ℓ·(n^k − 1))`, `J_k = Σ_j k^jΛ_j/j!` | WTZ `weilQuad_eq_tateJet`, `TheJetsOfTheTateFamily` [L] | Weil's form is the 1-jet at dimension zero of point counts of `𝔸^k∖0` |
| Dimension zero is classified: bare domination ⇔ `Q ≥ 0`; no Gamma–pole family dominates uniformly; any domination horizon on Riemann's kernel `≤ C·exp(−exp(A−2))`; pole weights pinch to `1/ζ(1+k)` and fail | DZG `TheDominationQuestionIsFirstOrder`, ATD `archimedean_tate_domination_complete_solution` [L] | positive dimension supplies no positivity of its own |
| Tate operators are positive only below a horizon `k*(A)`: exact `log₂(1+2√2)` at the first prime stage, exact `1.19966…` at the second, `≳ 0.13e^{−A/2}` in general, negative somewhere in every fixed `k > 0` along the tower | WTZ `TheTateHorizonAtTheFirstPrime`, `TheSecondStagePathIsAttained`, `TheTatePositivityHorizon`, `NoTatePositivityIsUniform` [L] | counts in positive dimension are themselves not uniformly positive |
| Rational lattice: every finite `S ⊂ ℚ_{>0}` of spread `< A` is realized by bumps; the window arithmetic form on `S` is the Hecke operator of `ℤ[ℚ^×_{>0}]`; folds count multiplicative pairs | WTZ `TheRationalLatticeOfAWindow`, `TheFoldsCountMultiplicativePairs` [L] | window horizons are thresholds of finite weighted rational Hecke graphs |
| Barta and Picone criteria: a balanced weight bounds `Σ 2a_n|c_n(H)| ≤ ‖H‖²`; Picone weights bound the Lévy energy below by a potential; together `Q ≥ (Ω_Γ − κ)‖H‖² + ∫VH² + pole` | WTZ `TheWindowBartaCriterion`, `TheGroundStateTransformOfAWindow` [L] | ground-state (Allegretto–Piepenbrink) certificates exist; they are sign-blind in the folds |
| Stage transfer `Q = Q_N − 2w_{N+1}c_H(log(N+1))`, the correlation living on the left collar; ground-state identity `Q = Q_N − wE_φ + w∫φ(u)φ(u+ℓ)(H/φ(u) − H/φ(u+ℓ))²` for every weight `φ > 0` | DZG `TheGroundStateRepresentationOfAStage` [L] | each new fold is one collar-to-collar term; its exact form keeps a jump-difference square |
| Frozen forms are indefinite: a real C² test on `[−21/20, 0]` has `Q₁ < 0 < Q`; on the unit window the frozen odd form satisfies `Q₁ + 20M² ≥ ‖F‖²/125` (one negative direction, the cubic moment) | WTZ `TheFirstFoldPaysANegativeFrozenDirection` [L], `TheCubicMomentPaysTheFrozenOddComplement` [L/W] | the new fold is a positive source, not a cost; every cost-only payment fails at the first prime |
| All real C² tests positive through total length `181/250·(1+6·10⁻⁷)`, floor `1/8000`; odd tests on `[−0.347, 0.347]` floor `1/100`; odd prime-free window by count `h¹ ≥ ‖f‖²/2000` | SP, AIP `AnExplicitLargerApertureRetainsAWeilFloor`, `OddWindowPastFirstPrime`; LST [L] | the unconditional base ends near `0.7243`, inside the first prime stage `[log 2, log 3)` |
| Zero modes of a nonnegative window are its radical, translation stable, and at a first critical length nonvanishing on both collars | DZG `ZeroModesOfAWindowAreItsRadical` [L] | an edge is born at full length and lives where the newest folds act |
| No Frobenius inside a window: `Q`-similitudes of the window algebra are scalars; reflection centralizer scalar | DZG `HeckeSimilitudesOfAWindowAreScalars`, WTZ `TheReflectionCentralizerOfTheWindowAlgebra` [L] | a Frobenius must change the window (translations `T_p − Id`, dilations, Adams lifts); positivity must be Rosati-type |
| Complete tilted-spline matrix positive definite for every `α < 1/8`, uniformly `1 ≤ c ≤ (log N)^α` | CACT `TheCompleteWeilMatrixIsPositiveDefiniteBelowTheEighthRoot` [L] | the subcritical regime is closed; the critical curve `c⁸ ≍ K log N` remains |
| At the critical curve: every mean-zero periodic twist, every real frequency `u` and every primitive character contributes a positive count (Hurwitz forms, `L(s,ψ̄²)` corrections); twisted directions add no negative square; only untwisted windows carry Weil's form | AHD (25 modules) [L/W] | the complete family is Weil's form on untwisted windows plus positive counts |
| Weil cone `{Λ}` or empty; prime-blind positivity ⇔ RH; node-critical; finite-level Farkas; zero-side identity | RHTower PBAP modules [L] | selection is automatic after positivity; positivity is zero-side positivity on blind tests |
| One cyclotomic mode carries the zero exponent: every eventually positive band, the first band included, has energy abscissa `2Θ` | CAF `FirstCyclotomicBandAbscissa` [L] | precision is one Fourier coefficient of the Chebyshev error |

## 1. Shared obstacle blocks

### S1. Complete Weil family at the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW-atomic, SC, CHMD (index), FEL, MSC. Class C1.

Established:
- [L] Subcritical regime closed: `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for every `α < 1/8`,
  `1 ≤ c ≤ (log N)^α`, floor `κ/(2c⁷)`; block split `y + u₀ + u₁ + w` along
  `V_{⌊L^{α+1/4}⌋} ⊂ V_{⌊exp√L⌋} ⊂ V_{⌊N^θ⌋}`, Schur coupling paid row by row.
- [L] Receivers: window criterion; horizon criterion (RH ⇔ eventual sign at every `2K(log N)^{1/8}`);
  Beurling schedule `2L(log L)²`; unit-bump receiver at every positive-power rate.
- [L] Critical-curve decomposition: untwisted windows `κQ(H) + (βJ/K)‖H‖²_{−(β+1)}`; Ramanujan
  windows `(Σ_m a_m²J_{β+1}(m))βJ/K`, diagonal in the Ramanujan basis; prime windows
  `(p^{β+1} − 1)βJ/K = J(1)φ(p)#ℙ⁷(𝔽_p)` (tilted spline); every mean-zero periodic twist: spectral
  Dirichlet series `2M^sΣ_j|χ̂(j)|²j^{−s}`, coercive; real frequencies `cos(2πnα)`:
  `½(ζ(β+1,u) + ζ(β+1,1−u))`, `u = {α}`; primitive characters: count `± q^{s−1}‖L(s,ψ̄²)‖`, opposite
  parities orthogonal, same parity coupled through `L(s,ψ̄₁ψ₂)`; trigonometric twists graded by
  frequency [W].
- [L/W] Polarization inheritance (mechanism B) on the twisted sector, on short windows (`≤ 3/5`), on
  the cosh hyperplane below `log 2 + 1/50` (window index `≤ 1` there), and on every window length below
  one fixed positive multiple. For `β>0`, the exponential weighted floor
  `Q(H) ≥ −C(β+1)∫e^{−(β+1)y}H²` has `C` independent of aperture; each fixed family inherits
  positivity (`OneCriticalMultiplePaysEveryWindow`). Twisted directions carry no negative square.
- [L] Bulk: zeros of height `≤ N^θ` (every `θ < 1`) enter only through the pole, as
  `(c/log N)κy₁²(2 + γ − log 4π)` (twice the first Li coefficient); pole-free packets are blind.
- [L] Pencil index = number of jump multiples below `K`; window index exhausts the right zeros;
  separated packets under Nyquist conditions are resolved; nonpositive directions localize in a finite
  conductor sector at every fixed overlap.
- [D] Under ¬RH the edge of the complete family has exponent exactly `1/8`: positivity holds below
  `(log N)^{1/8−ε}` [L], and the edge lies below `2(log N)^{1/8+ε}` infinitely often (EHT [L]).

Research status: below the critical curve the problem is solved. At the critical curve every direction
is a positive count except Weil's form on untwisted windows; the open content is the sign of that form
on windows of growing length and the uniformity of the decomposition in growing conductors.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons: eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion | — |
| A2 | General profiles past `θ = 1/1080` and past the super-log-log clocks; transfer of the eighth-root block-reserve scheme to other profiles | — |
| A3 | Fixed finite twist families: finish the frequency grading [W]; joint families of Ramanujan, character and frequency twists with untwisted windows; characters of different moduli; tables of the `L`-value corrections | — |
| A4 | Phase diagram: equality case at a critical multiple `K*(H)`; finite-`N` sign at jump thresholds | — |
| A9 | Window index as a counting function of the length; location of the jump multiples (conditional calculus) | — |
| B1 | Weil's sign on windows of every length (all equivalent forms, `walls-ledger.md` Σ1) | RH; fixed length sub |
| B4 | Growing-conductor decomposition at the critical curve: uniformity in the conductor, mixed and bulk–horizon cross terms on the full space; conductors `√N < m ≤ N` need an Elliott–Halberstam-type input | sub |
| B5 — solved [W] | One positive range of critical multiples works on every window, for `β>0`; WTZ `weilQuad_ge_neg_exponentialMass`, AHD `tilted_exists_positive_multiple_inheriting_all_windows`. Finite-`N` convergence remains family by family | sub |
| B6 | Full-space positivity of general profiles past `log log N` | sub |
| B7 | Exact sum of squares on one two-prime lattice; any identity on the `{∞,2}` window is aperture-specific (that family turns negative at half-width `0.5574`) [N] | RH |

### S2. The window tower and the stage step
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT; programmes CWS, WTZ, DZG. Classes C1, C4, C15.

Established [L]: window datum and locality; truncated Dirichlet algebra, small extensions, Hilbert
function, socle, plethystic Adams recursion; stage transfer and its ground-state identity; exit charge
pays every entrance pointwise; composite stages free; end profile `V_A = Ω_Γ + φ(−u) + φ(A+u)`, windows
`≤ 1/7` positive by the exit charge; sharp floor `Q ≥ −(deg K_A + 2sinh(A/2) − A)‖H‖²`; fold capacity
criterion; Barta and Picone ground-state criteria; rational Hecke-graph reading; exact Tate horizons at
the first two prime stages and the second-stage path bound `α² + β ≤ 1` (attained); first-prime
obstruction to finite-square identities; frozen negative direction at the first fold; frozen odd form on
the unit window negative only along one cubic moment; zero modes are the radical and touch both
collars; all-test floor to `≈ 0.7243`; odd floor on `[−0.347, 0.347]`; odd supersolution criterion
(a folded generator dominating the potential, `𝓛_Nω ≥ Φcosh(x/2)ω`, makes every admissible odd Markov
energy nonnegative, and RH follows when every odd test factors through `ω`); nonnegative combinations of
shifted ground states fail the folded test near the origin and at infinity (ACT).

Research status: the stage step is exact and local: for `A = log(N+1) + ε` the new fold couples only the
left collar `[−A, −A+ε]` to the right collar `[−ε, 0]`. If the frozen form is positive definite on the
interior (an earlier stage), Weil positivity on `W_A` is the two-collar inequality
`S^N_ε − w_{N+1}(J + J*) ⪰ 0` on `L²(collar) ⊕ L²(collar)`, `S^N_ε` the Schur complement of the frozen
form onto the collars and `J` translation by `log(N+1)` [D]. The frozen form is indefinite at the first
prime stage [L], so the frozen collar coupling must contain the new fold: the new fold is a positive
source. Every payment that treats the fold as a cost (exit charge, collar loan, the weighted transfer
criterion `wE_φ ≤ Q_N`, Barta weights on `|c_n|`) cannot certify the frozen-negative tests [L/D].

| | Obstacle | Strength |
|---|---|---|
| A5 | Certified first prime stage from `0.7243` to `log 3` (odd margin `1.5×10⁻⁵`, even `5.6×10⁻⁸` at half-width `½log 3` [N]) and second-stage certificates on the exact path graph (Lehmann–Goerisch with a Lévy comparison operator). Finite; not scalable | — |
| A6 | Odd unit window: pay the single cubic-moment direction of the frozen odd form by the signed fold at `log 2` (a rank-one Schur problem on a fixed window) | — |
| A7 | Rational Hecke graphs, Perron vectors and exact Tate horizons of stages 3, 4, 5, 7, … | — |
| A8 | The two-collar Schur complement `S^1_ε` of the prime-free datum (first prime stage) in closed form | — |
| A29 | Atomic-lattice bound `λ_max ≤ ½log N` with an explicit Mertens error | — |
| B2 | Exact stage step: at every prime-power stage the two-collar inequality, with the new fold entering through its signed correlation | RH as induction; each stage sub |
| B3 | Window criticality: a positive supersolution (Agmon ground state) of the folded arithmetic jump process at every length, passing each stage by a collar correction; on the odd sector with sinh capacity `≤ 1` | RH; fixed length sub |
| B41 | Two-collar recursion: a closed causal evolution of the frozen collar form in the window length (Krein/Gelfand–Levitan type), the prime powers entering as impulses `Λ(n)/√n` at `A = log n` | identity |
| B14 | Growth law of window negativity: exponent between `Θ − ½` (two-bump tests) and `½` (floor) | `< ½` ≥qRH; subexponential RH |

### S3. Dimension zero and the Tate family
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD. Class C13.

Established [L]: Tate jet and signed-count forms of `Q`; exponential and plethystic forms; flow equation
`∂_kJ_k = DJ_k + J_k * Λ` and jet tower generated by `M` and `ρ_A(Λ)`; sign change at `k = 0`
(`(−1)^{ω(n)}J_k > 0` for `k < 0`, order of vanishing `ω(n)`); the wall `k ↦ −k` is Dirichlet
inversion (`μ` on squarefree integers); centred family is an odd exponential; symmetric Tate twist =
shifted pair `Λ(s−k)Λ(s+k)`, tilting archimedean and prime jumps by the same `cosh(kt)`; imaginary twist
unitary and positivity preserving; short windows stay positive for `|k| ≤ 1/200`; archimedean Tate
family `Γ_ℝ(s−k)/Γ_ℝ(s)` is a cocycle, finite in even dimension; completed centred family unimodular on
the critical line; bare domination ⇔ Weil sign, with explicit prime-blind canonical family; null tests
force the Selberg second jet `∂²A ≥ 2⟨ρ_A(Λ₂)H,H⟩`; Tate positivity does not descend (`ζ(s)ζ(s−ε)`);
archimedean domination: no uniform horizon for Gamma–pole families, horizon `≤ C·exp(−exp(A−2))` on
Riemann's kernel, shifted-pole weights pinched to `1/ζ(1+k)` and refuted; domination holds on
`[0, 0.7243]` for `0 ≤ k ≤ 1/160000`.

Research status: classified. Positive dimension carries no positivity that reaches `k = 0`; the
dimension-zero derivative is Weil's form itself. What survives: the only admissible pole weight is the
Euler-product weight `1/ζ(1+k)` (domination in positive dimension is forced to be arithmetic); null
tests carry Selberg's `Λ₂`; positivity lives on the line `Re k = 0` of complex Tate dimension.

| | Obstacle | Strength |
|---|---|---|
| — | none beyond B1: positivity surviving the derivative at dimension zero is equivalent to Weil's sign | — |

### S4. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant. Class C12.

Established [L]: Kähler package (HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus); stars with depth law;
gcd stratification, graded/top Möbius pair; disconnected links; nerve `χ̃ = −M(N)`, Redheffer
`det = M(N)`; no semilocal positive carrier; cyclic Hodge defect on a two-prime orbit; zero modes are
the radical.

| | Obstacle | Strength |
|---|---|---|
| A21 | Björner wedge decomposition of the squarefree complex | — |
| A22 | Quantitative depth law, star horizons, gcd-strata tables | — |
| B8 | Hard Lefschetz on the positive locus: no zero mode at any length | RH |
| B9 | Payment of the top coprime stratum | RH |
| B15 | Cross-tower spectral gap through the archimedean channel | method; uniform RH |
| B31 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |

### S5. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS. Classes C1, C3.

Established [L]: finite index = PD minus finitely many squares; finite index ⇒ Lindelöf; RH ⇔ index
zero; window index finite, monotone, exhausting; pencil index counts jump multiples; `{0, ∞}` laws for
tensor squares, regular extensions, mixing and Hecke-supported carriers; index `≤ R + A` on `R` coarse
cells; growing Euler heads unbounded; index-one dichotomy (PD plus one hyperbolic pair, or a positive
unitary-character hyperplane).

| | Obstacle | Strength |
|---|---|---|
| B10 | Arithmetic index ceiling uniform in resolution | ≥qRH (`K_ζ`); RH (`K_ζ ⊠ K_ζ`) |
| B11 | Zero–one law `κ(K_ζ) ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF. Classes C3, C11.

Established [L]: window integer = Wiener–Hopf index, index `0` ⇔ outer Szegő factorization; pair
resolvent = Laplace transform of `|𝒵(t)|²`, abscissa = twice the maximal depth; eight-way near-line
density equivalence (log-mean, mollified log-mean, linear-mollifier outer law, horizontal moment,
critical-scale clustering, Hecke readings); almost-all log-stage certificates ⇔ log-free unit-window
occupancy; occupancy and horizontal moment incomparable on generic density data; Planck windows
zero-free beyond `A/log V` outside `O(e^{−rA}/A)`; double-log stage with `O_c(V/log log V)` exceptions;
port decomposition, right-edge flux never cancelled by its functional-equation image, Cauchy caps
cancel down to `σ_m = 1 − 1/(116log(m+5))`; polynomial stage ⇔ RH, fixed degree `k` ⇔
`|β − ½| ≤ C/|γ|^k`; heat counts `κ(φ_c^{(t)}) − 1 = N(t)/2`, floors `133/200`, `2/3 + ε`.

| | Obstacle | Strength |
|---|---|---|
| A26 | WD composition: computable stopping prefix, flow threshold from sub-Weyl profiles, `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf | — |
| B16 | Inner caps `[½, σ_m]`: cancel the right-port flux at every polynomial stage | RH; fixed degree ≥qRH |
| B17 | `100%` critical-scale clustering (≡ log-mean `o(1)` ≡ Hecke `o(log U)` ≡ horizontal moment `o(T)`) | sub |
| B18 | Log-free unit-window occupancy `D_win`; log-free multiplicity density `D_zero` | sub |
| B19 | Hecke defect pointwise `O(1)` / one dyadic constant | ≥qRH / RH |
| B20 | Distributional input beyond counts and moments (a rate in a Selberg-type limit law) | method |

### S7. Counts, producers and precision
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census. Classes C7, C13.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_εlog²x`;
individual producers have slope `> 1`; integer-Chebyshev ceiling; Redheffer `det = M(N)`, `Ω±(√N)`;
Künneth RR, window `h¹` = primitive Künneth `h¹ = ½Q`; pole-plane Abel completion and logarithmic RR;
count classification (bidegree, fixed rank, definite, Siegel excluded); first-prime count identity
refuted; census `0.67250071`, positivity-only certificates cannot reach `3/4`; every eventually positive
cyclotomic band, the first band included, has energy abscissa `2Θ`; Baire-generic Möbius gauge exponent
`1` (Haar-null level set), Haar-a.e. `½`; cluster-product detector: every zero with depth `≥ 1/a` and
height `≤ exp(a/(10⁵A₀ log a)) − 306` is seen by a smooth test supported in `[−(a+1), a+1]`.

| | Obstacle | Strength |
|---|---|---|
| A20 | Logarithmic two-point Chowla (Tao) | — |
| A23 | Census: `S_cos(λ)` for `λ ≤ 1`; odd stabilizer taper transport; stabilizer at `β = 2` | — |
| A24 | Voronoi summation; Zwegers' indefinite theta series | — |
| A25 | Künneth primitive `h¹` at small degree; mixed-jet recovery for `≥ 3` primes; explicit main-term producer | — |
| A27 | Explicit cluster-detector constant `A₀`; combination of the cluster horizon with the window index | — |
| B21 | Count-valued primitive `h¹` as an inequality (naive height at bounded distance; `ℕ`-count height on one generic two-prime orbit) | RH; fixed length sub |
| B22 | Genus upper law `g ≤ (2 + η)e^A` | indep. |
| B23 | Logarithmic Serre duality of the split surface, primitive part | sub |
| B24 | `ε`-uniform producer; square-root source input; half-power Redheffer determinant | sub; RH |
| B25 | First cyclotomic mode: Chebyshev first-band energy `O(N^{1+ε})` (a power saving `O(N^{2−η})` is a zero-free strip) | RH (power saving ≥qRH) |
| B26 | Signed prime-pair information beyond bandwidth one | sub |
| B27 | First Epstein real zero on the boost line `0 < |u| ≤ 1` | sub |

### S8. Carriers, coupling, selection and the prime-blind cone
Routes: SC, ACS, HF; Γ-candidates; support line PBAP. Classes C2, C8, C16.

Established [L]: coupling calculus; bounded dense two-prime coupling ⇔ RH, coupling rate = zero width;
Gaussian-damped cone: rate `σ` ⇔ width `≤ σ`, bounded `ℕ²` coupling ⇔ RH; undamped cone: bounded
coupling ⇒ RH or unattained width; finite stratum: bounded single-lattice coupling ⇒ RH; RvM-count
exact-spline countermodels for undamped density; carrier classification; two free primes carry the
full affine index; prime-set flips separated at every density; complete degeneration selects `Λ`;
Weil cone `{Λ}`; prime-blind positivity: RH ⇔ PBAP ⇔ pole-free PBAP on the primitive hyperplane ⇔
archimedean symbol `≥ 0` on blind combinations of pole mass zero ⇔ moment region above `q = −p`;
node-critical (every prime power needed, composites free; one prime plus the archimedean place
suffices on the even sector after blindness at all other nodes); finite-level Farkas duality; zero-side
identity on blind tests; PBAP solved on nonnegative tests (reduction to `(0, log 2)`) and on separated
narrow-bump cones; pole floor `P(c) ≥ −(4mass + 6M)`; finite-level cones local, convex, an interval of
`λ(2)` at the first prime level.

| | Obstacle | Strength |
|---|---|---|
| A10 | Function-field calibration: horizon layer and second order for curves with twists; higher-genus fakes; `𝔽₃` elliptic loop chain | — |
| A12 | Prime-side identity for the Gaussian-damped two-prime coupling (heat-smoothed explicit formula on the cone) | — |
| A28 | Finite-level Weil cones: compute `C_A` (first prime level: the `λ(2)`-interval; levels `log 4`, `log 6` by the Farkas lemma) and the widths of `C_A` around `Λ` | — |
| B28 | Bounded Gaussian-damped cone coupling from the prime side; bounded dense two-prime coupling; exclusion of an unattained width on the undamped cone | RH |
| B29 | Finite-sieve Hodge positivity → global inter-tower form | RH |
| B30 | Reflection positivity: Rosati positivity of the window algebra / naive height at bounded distance / Hecke similitude with positive form | RH |
| B32 | Zero-independent selection at the trivial gauge point | RH |
| B33 | Euler-product FE twins; unimodular gauges with `S_N/H_N → 1` | sub |
| B40 | Prime-blind positivity on signed blind combinations with dense cancellation | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C. Classes C9, C14.

Established [L]: regularized Gauss–Mayer operator, Euler product over modular geodesics, faithful
divisor; resonance ⇔ `ζ(2s) = 0` (five forms); `Z_PM` = Hardy's `Z`; Lewis period space `H_LP`,
`I_s† = I_{1/2−s̄}`, `I_s` bounded iff `Re s = ¼`, head branch bounded iff `Re s ≤ ¼`, Riemann–Mayer pair
bounded iff `Re s = ¼`; `D_s ≤ 0`, `= 0` iff `Re s = ¼`; Krein–Lax–Phillips space with `2κ₋` = polar
defect, Krein positivity ⇔ RH; Farey–Lewis three-term operator with `M_sM_s† = μ_s > 1`; Eisenstein
period: `D_s < 0` iff `Re s ≠ ¼` at resonant and nonresonant points; finite dyadic cusp energy ⇔
resonance; `U_LP` intertwines `I_s` with the window multiplier, defect of a window lift = window
Frobenius defect, fold functionals = dilation integrals of the lift; source Hecke eigenvalues
`1 + p·p^{−2s}` (`p = 2, 3`) from Barnes cones without spectral assumption; `T_p − Id` realizes
`√p H(· + log p)` into the window `A + log p`, scaling complete Weil energy by `p`; complete Weil energy
= limit of twice the real Krein squares of finite core sums with twisted reflection; every
positive-length window prescribes arbitrary finite resonance coordinates, so finite projections keep
every negative PM direction (compensated by the omitted tail); no real-linear isometry intertwines
Serre duality with the Krein reflection; boundary-subtracted cores carry a nonzero Hecke correction at
every upper resonance; finite Hecke words keep finite cusp energy at every aperture; congruence poles
persist; cutoff Grams, Hecke residual gaps and height laws retain the rate.

| | Obstacle | Strength |
|---|---|---|
| A13 | Classical identifications: Selberg-zeta normalization, scattering constant term into `Re(2s) < 1`, Lax–Phillips for `PSL₂(ℤ)\ℍ`, Lewis–Zagier separation of cusp-form events, `+1` Mayer eigenspace classification, Garland loop-group identification of the rational Weyl sum | — |
| A14 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| A15 | Barnes-cone Hecke relations and Mellin bridges `T_p − Id` for every prime `p` | — |
| B34 | Arithmetic `D_s ≥ 0` on finite-cusp-energy resonances (Krein positivity); a separated scattering gap | RH; gap ≥qRH |
| B35 | A statistic of resonant states selecting the decay rate | method |
| B36 | Hecke-equivariant completion: an exact (not limit) identification of complete Weil window energy with the Krein form, carrying conjugation, the exponential twist and the boundary correction | identity |
| B37 | Infinite physical-core synthesis retaining the outgoing boundary charge | sub |
| B39 | Source-faithful realization: a tower of unbounded rank | RH |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A16 | Theta Hankel rank-8 strictness; ranks 9–10 | TH | — |
| A17 | Hausdorff shifts, Jensen degree horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF | — |
| A18 | Nine atom-dominated collar moduli | ACT | — |
| A19 | Mixed Schur debit; first-prime, coarse and polar costs on fixed cells | AIP, CHMD | — |
| A11 | Integration of unfinished modules: LI Cayley ladder, SZ first-variation transfer, HKT compressions, AKLT fine towers, ALG Lorentzian/conformal modules, AGT coherence, ACP density transfer | LI, SZ, HF, ACS, SC, MC | — |
| B12 | All-rank / all-degree signs; Laguerre–Pólya property of `ξ(½ + z)` | TH, LA, HCF, PA, GTA; ART | RH |
| B13 | Lower bounds for scheduled prime energies | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B38 | Pre-divisor forcing | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 2. Programmes

### ADT and AHD — degenerations
Thesis: the complete Weil family is a degenerating family along the resolution axis.

Established [L]: first order = Jordan count `#ℙ⁷(ℤ/m)` over every finite ring; monodromy eventually
idempotent; Redheffer gluing; graded/top Möbius pair; complete degeneration selects `Λ`; second order
for every regular profile; pencil index = jump multiples; every periodic twist, frequency and character
at the critical curve; Frobenius-angle dictionary: over a pure curve the family is a sum of squares at
every resolution with Hurwitz weights of the angles, its rescaled limit is the Hurwitz form of the
angles, and over `ℤ` a twist frequency `u` contributes exactly the Hurwitz form an angle `u` contributes
over `𝔽_q`; pure curves degenerate completely, the golden fake has exponential monodromy and a fixed
hyperbolic plane at every width; bulk blind below the resolution height, reading only the archimedean
genus at the pole; polarization inherited on twisted sectors, short windows, the cosh hyperplane and
below the uniform multiple.

Research status: the degeneration reads the zeros only statistically (through counts and Hurwitz
constants); every graded piece except the untwisted (trivial-angle) direction is positive; the sign
problem sits at the trivial angle `u = 0`, where the Hurwitz form is singular (`u^{−(β+1)}`) and Weil's
form lives.

| | Obstacle | Strength |
|---|---|---|
| A3, A4, A9, A10 | Fixed finite twist families; phase diagram; window index vs length; `𝔽_q` twists | — |
| B4 | Growing-conductor decomposition | sub |
| B5 — solved [W] | Aperture-independent weighted floor; one positive range of critical multiples on all windows | sub |
| B1 | Weil's sign on untwisted windows of every length | RH |

### CWS, WTZ, DZG, ATD — the window tower and dimension zero
Thesis: a window is a module over a finite local λ-ring; the tower is a chain of small extensions;
Weil's form is produced stage by stage.

Established: S2 and S3 in full.

Research status: algebra, dimension zero and the payment of entrances are settled. The open core is the
exact signed stage step on the two collars (B2), equivalently window criticality (B3).

| | Obstacle | Strength |
|---|---|---|
| A5–A8, A29 | Certified first and second stages; odd unit window; Hecke-graph horizons; first two-collar complement; atomic Mertens bound | — |
| B2, B3, B41 | Exact stage step; window criticality; two-collar recursion | RH; RH; identity |
| B30 | Rosati-type positivity of the window reflection | RH |

### CACT and CAF — complete forms
Established [L]: complete tilted-spline positivity below `1/8`; exponent ladder `1/59 → 1/16 → 1/9 → 1/8`;
every fixed overlap positive; logarithmic profile to `ε₀L(log L)²`; growing-conductor shell, harmonic
and upward-row bounds; cyclotomic coercivity; first cyclotomic mode carries `2Θ`.

| | Obstacle | Strength |
|---|---|---|
| A1, A2 | Constants; general profiles | — |
| B4, B6 | Critical-curve uniformity; general profiles past `log log N` | sub |
| B25 | First-mode energy at square-root precision | RH |

### PBAP — the prime-blind line (support, no route)
Established: S8 (prime-blind part) in full.

Research status: RH is a statement without primes and without zeros (archimedean symbol on blind
combinations), and it is node-critical and convex-dual at every finite level; on blind tests it is
zero-side positivity. Solved on nonnegative and separated-bump cones; open on signed blind combinations.

| | Obstacle | Strength |
|---|---|---|
| A28 | Finite-level cones and their widths | — |
| B40 | Signed blind combinations | RH |

## 3. Live routes

Per route: path; established; A (just work); B (open). Shared items refer to Section 1.

### WL — Weil lag / prime lag
Path: prime error → square-root bound or subexponential critical energy → RH.
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope;
Chebyshev–Stirling split; Landau-window cost `(2log2 − ε)mn`; Adams threshold `2^{qr}`; `{2,3}` stencil
`ψ ≤ 23x/20`; multivariate parity producers at the main term; one cyclotomic mode carries `2Θ`.
- A: A25. B: B24, B25; joint Möbius-moment/Mertens/sawtooth payment at square-root precision (RH).

### RW — restricted Weil ground energy
Path: `μ(a) ≥ 0` at every aperture → RH.
Established: attained strictly decreasing minima; all-test floor through total length `≈ 0.7243`;
exact `{∞,2}` trace through `½log 3`; finite-prime zero crossing by `2log(|S|+2) + 11`; ceiling
`μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; stage transfer and ground-state identity; frozen negative
direction at the first fold; pointwise folded-Markov and fold-only count identities fail.
- A: A5, A6, A8. B: B1, B2, B3; depth-weighted all-window mass bound (≥qRH).

### FU, CFC, RP — scheduled prime histories
Established: exact receivers (completed Abel moment; first-clock tail; linear history floor);
cofinal unboundedness under ¬RH; sublinear floors impossible (RP); phase-natural transport is identity
(CFC).
- A: none. B: B13 for each.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A17. B: B12.

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`, Baire-generic `1`; RH ⇔ trivial point
typical; every eventually positive cyclotomic band, the first included, retains `2Θ`; Redheffer
`det R_N = M(N)` = nerve Euler characteristic, `Ω±(√N)`; finite-clock leaf squares paid.
- A: A20, A21. B: B24, B25; head/leaf signed cancellation (RH); B32.

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; Φ-Doob identities; restricted current signs.
Window reading: the odd/Markov sector of window capacity.
- A: none. B: B3 (odd sector), B1.

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; slice floor `133/200`; right-half depth
moment `o(V)`; PF₃₇ at the centre; inverse-log heat ladder.
- A: A17, A26. B: B12; uniform tail narrowing (≥qRH); exceptional heights (sub).

### TG — topological sub-unit gate
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
window integer decided by the window energy.
- A: none. B: B16; B8.

### HF — Hodge / Hecke / complete cells
Established: S1, S2, S3, S4 in full; the degeneration dictionary; band poles = Hodge defect; Frobenius at
infinity ⇔ RH; correspondence algebra; RR branch of S7; no finite-rank realization.
Research status: positivity below the critical curve is a theorem; at the critical curve every
direction except untwisted windows is a positive count; the window algebra has no internal Frobenius.
- A: A1–A4, A9, A10, A21, A22, A25. B: B1, B4, B6, B7, B8, B9, B10, B21, B23, B30, B31, B39.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; Markov form and sinh capacity; Haar pieces with uniform
finite index except the first-prime coarse layer; all-detail prime–pole cancellation
`O(exp(−√log Y/92160000))`; normalized prime matrix approaches one separable pole channel.
Research status: the `√Y` normalization gives no unnormalized vanishing error and no index ceiling.
- A: A19. B: B10; B3; joint non-arithmetic Gamma graph + signed diagonal + poles (sub).

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; strict rank-three reflected blocks; all-rank signed-center
positivity ⇔ RH; native tails = Gram-square mass minus signed local flux.
- A: A16. B: B12; rank-uniform signed flux payment (RH).

### RN — renewal
Established: compact cone-positive renewal operator with exact determinant and resonances.
- A: none. B: directed mixed prime + Gamma `≥` pole (RH); B39.

### WD — Ward / collision / window energy
Established: S6 in full.
Research status: the analytic block is one density statement in eight forms; almost-all certificates
⇔ log-free occupancy, unconditional one logarithm short; inner caps are the zero-free-region problem.
- A: A11 (WD modules marked unfinished), A26. B: B16, B17, B18, B19, B20; B10 (tower branch).

### LI — paired Li / prime–Gamma balances
Established: guarded history-zero set finite, RH ⇔ empty; Cayley–Li primitive-sign receiver.
- A: A11. B: B13 (outside budget at every guarded zero).

### SZ — Suzuki screw / shifted-kernel limits
Established: exact lower-bound receiver; finite reflected-current/light-cone Gram identities; Krein–Schur
block congruences of the screw function; first-variation transfer.
Window reading: the screw function is Weil's kernel; the Krein–Schur machinery is the natural carrier of
the two-collar recursion (B41).
- A: A11. B: B13; B41 (shared with S2).

### PM — Gauss–Mayer physical realization
Established: S9 in full.
Research status: PM has a faithful divisor, Hardy's `Z`, the reflection as a Hilbert adjoint, a Krein
space whose negative index is the polar defect, source Hecke operators with Barnes-cone eigenvalues,
Mellin bridges into longer windows, and complete Weil energy as a limit of Krein squares of finite core
sums. The linear identification of window Serre duality with the Krein reflection is impossible; finite
core projections retain every negative direction. Every positivity PM has is contractive (blind) or
Krein (RH).
- A: A13, A14, A15. B: B34, B35, B36, B37, B39, B31; escape (sub / ≥qRH).

### JAS, CTF, PBM, RB — one-sided count
Established: JAS positivity at growing logarithmic budget; CTF completion identities and Euler completion
error `≤ 1/(n+1)`; PBM convergence at every `σ > ½` ⇔ RH; RB colossally abundant reduction.
- A: none. B: B24.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: two-grid criterion; one grid aliases. A: A17. B: B12.
- XN: Newton-disc criterion; nonnegative Laplacian of the margin. B: covering with nonnegative margin (RH).
- BAG: disc recurrence ⇔ RH; weak ladders collapse. B: B32.
- EWU: weight rigidity; attained aperture-antitone blind minima; even prime-blind node criticality. A: A5.
  B: B1 (even sector).
- GTA: transverse-charge criterion; positive charge and finite-prefix convergence. B: B12.
- OWU: odd floors (`[−0.347, 0.347]` with floor `1/100`; prime-free window by count); logarithmic jump
  gap `log 2 + 7/5`; frozen odd form on the unit window negative only along one cubic moment; Liouville
  twist separation. A: A5, A6. B: B1 (odd sector), B3.

### SRT, ACT, AIP — complete atomic matrix
- SRT: S1 in full; horizon criterion; pencil index counts jump multiples; cluster-product detector at
  one-logarithm aperture. A: A1, A3, A4, A9, A27. B: B1, B4, B10.
- ACT: collar thresholds pay every modulus outside nine; single-shift receiver; criticality theory
  (odd supersolution criterion, shifted ground states; combinations of shifted ground states fail near
  origin windows). A: A18. B: B1, B3.
- AIP: complete form = jump + incidence − shell + boundary; prime-successor edges pay nonconstant packet
  mass; three-band complement reserves; the eighth-root Schur synthesis closed; odd floor past the first
  prime. A: A1, A19. B: B1, B4, B6.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count; finite divisor; genus `≥ (2−η)e^A` plus
multiplicity excess; LST counts; Abel completion and pole-plane RR; primitive `h¹ = Q/2`; odd prime-free
count; windowed Tate law; two-prime `ℕ`-count criterion; FE, Epstein and golden fakes; first-prime
count identity refuted; Tate counts soft; socle non-principal for `N ≥ 3`; Hecke similitudes scalar.
Research status: flooring a nonnegative form assumes its sign; finite-square identities fail; positive
dimension descends nothing; the producer would be an independent count-valued inequality.
- A: A10, A23, A24, A25. B: B21, B22 (indep.), B23, B26, B27, B30, B1, B7, B31.

### SC — Stokes/Witt–Krein / archimedean successor
Path: glued index `κ(φ_c) < 3` → RH; or bounded Gaussian-damped two-prime coupling → RH.
Established: `κ(φ_c) = κ + 1` at every place; carrier classification; two-prime lattices carry the full
affine index; coupling ≡ kernel; damped cone ⇔ RH; undamped cone ⇒ RH or unattained width; finite
stratum closed; every finite rational Gram is a compression limit on the Beurling schedule.
- A: A10, A12. B: B1, B7, B10, B28, B29, B8.

## 4. Candidates

| Candidate | Established | A | B |
|---|---|---|---|
| APF | Fredholm index; cycle-trace reconstruction | — | zero-independent divisor exhaustion (B38) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B38) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B38) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (B38) |
| EGC | pole-safe contour; complete copy correction | — | outer expanding-contour sign (B13) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B38) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B13) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (B38) |
| IRK | rotation-algebra trace / winding | — | arithmetic projective lift with integral count (B21-type) |
| MSC | Möbius–Sonin; strict-right divisor preservation | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation (B38) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port (B39) |
| RFHM | support grade | — | symmetry-breaking law (B38) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B38) |
| W1C | finite Lee–Yang/Ising receiver; PM's faithful divisor and Krein realization | A13 | positive arithmetic Hilbert realization with self-adjoint generator (B34, B39) |
| WBF | genealogy Gram | — | any arithmetic coupling (B38) |

Support lines (not routes): ADT, AHD, CWS, WTZ, DZG, ATD (Section 2); PBAP (S8); ART (centred
approximation; survivor lands in B12); the classical-formalization programme (Lax–Phillips, Voronoi,
Zwegers, Björner, logarithmic Chowla).

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, window sign / exact two-collar stage step / window criticality | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC, CHMD, TT, SZ; MSC, FEL; ADT/AHD/CWS/WTZ/DZG |
| Σ, critical-curve uniformity (growing conductors and families) | HF, SRT, AIP, SC; CACT, AHD |
| Σ, Hodge–Lefschetz / zero modes / top coprime stratum | HF, ACS-Hodge, TG |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA; ART |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization (tower of unbounded rank) | RN, PTR, W1C |
| Π, inner caps, near-line density, mollified log-mean | WD, TG, LA (heat), SC-heat, census |
| Π, count-valued primitive `h¹` | ACS-effectivity, HF-RR, IRK |
| Π, one-point precision (one-sided count, first cyclotomic mode, Redheffer, damped coupling) | WL, MC, PBM, RB, JAS, CTF, SC |
| Π, conjugate diagonal | WD (Hecke defect), census |
| Γ, reflection positivity (window Rosati form; Lewis co-isometry defect; Mayer Krein form) | PM, HF, ACS, CWS, W1C |
| Γ, prime-blind positivity on signed blind combinations | PBAP |
| Γ, trivial gauge point / pre-divisor forcing | BAG, XN, MC; APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
