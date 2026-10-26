# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-26, corpus `19b8caad1` with the working tree of that day, including the uncommitted modules `HeckeInvarianceOfTheCollidedPolarizationIsRH`, `RamanujanTorsionStabilizersAndMonomialCollapse` and `MasterBiarithmeticGaugeGeometryTheorem`. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](hard-obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; the record is `logs/review-2610/working-log-v3.md`. Nothing was compiled. Labels: `[L]` integrated according to the frontier map, `[S]` working or unintegrated source, `[P]` paper proof, `[R]` assessment or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, classical ranges of known estimates. IDs `W1`–`W13`, defined in the [summary](hard-obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](hard-obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

Notation: `Δ = sup_ρ |Re ρ − 1/2|`, `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ`, `ρ* = 1 − ρ̄` is its reflection; `{ρ, ρ*}` is a reflection pair, off-line when `Re ρ ≠ 1/2`; `δ = Re ρ − 1/2` is its depth. `β_ρ = p^{ρ−1/2}` is the Hecke symbol of `ρ` at `p`. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`. `W` is Weil's form, `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**, `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**. `T_L` is translation by `L` (the Hecke action of the dilation `e^L`). `σ_γ(s) = 1 + 2iγ − s` is the **elliptic localizer** at ordinate `γ`.

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space

The corpus identifies two quadratic forms on real compact `C²` tests, each with one half of what a polarization needs (PL `TheOscillatoryCapacity`, `HeckeInvarianceOfTheCollidedPolarizationIsRH`):

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH | yes, for every zero configuration: `W(T_L f, T_L g) = W(f, g)` (`W_translate_translate`) [S] | the explicit formula (primes, Gamma, poles) |
| Collided form `D` | yes, unconditionally (`collidedForm_nonneg`) | iff RH: `D(T_L f) = Σ m_ρ e^{2δ_ρ L} \|f̂(ρ)\|²` (`collidedForm_translate`, `riemannHypothesis_iff_collided_hecke_invariant`) [S] | nothing known |

- **Capacity identity** [L]. `Re W(f, f) = D(f) − Δ(f)` for every configuration and every test with square-summable transforms (`re_W_eq_collided_sub_defect`); for `ζ` it holds for every compact `C²` test, and RH holds iff `W = D` on every real test (`riemannHypothesis_iff_W_eq_collided`). `Δ` charges every off-line pair `m|f̂(ρ) − f̂(ρ*)|²`, whatever its depth: it is a depth-uniform capacity for intrinsic charge.
- **Hecke defect of `D`** [S]. `D(T_L f) + D(T_{−L} f) − 2D(f) = Σ_ρ m_ρ (2cosh(2δ_ρ L) − 2)|f̂(ρ)|² ≥ 0` (`collidedForm_second_difference`): the second difference of the positive form counts off-line charge with hyperbolic weight.
- **Why `D` is not computed** [L]. `D` is not of the form `Σ_ρ H(ρ)` with `H` holomorphic: it pairs `ρ` with its conjugate `ρ̄`. The explicit formula computes holomorphic sums, i.e. the reflection pairing `ρ ↔ 1 − ρ` that `W` uses. A one-variable meromorphic carrier of the conjugate collision does not exist (`zeta_global_collision_not_analytic`, §1.9).

Reading [R]: over `𝔽_q` the Rosati trace is both positive and equivariant. Over `ℤ` positivity and equivariance sit on two different forms, and RH is the statement that they are the same form. Complex conjugation `s ↦ s̄` (the Frobenius at infinity) defines `D`; the functional equation `s ↦ 1 − s` defines `W`; their composite is the Rosati reflection `s ↦ 1 − s̄`.

### 1.2 Local type, elliptic localizers and resonance

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, of signature `(1, 1)` (ACP P4, P5, P13).

| Type | Action on the fibre | Correspondences | What positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost `diag(β, β̄⁻¹)`, `\|β\| ≠ 1` | Hecke operators, the archimedean flow, every gauge twist, exactly at off-line pairs | `u v̄ = 0`: isotropy |
| Elliptic | rotation or the swap `(u, v) ↦ (v, u)` | Hecke operators on the line; a resonant symmetric Hecke operator; `σ_γ` | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the additive successor | nothing |

- **Multiplicative symmetry is hyperbolic exactly off the line** [L] (`norm_heckeSymbol_eq_one_iff`); separating isometries are boosts (`separating_isometry_is_boost`); the successor is unipotent (`succShift_vonMangoldt_eq`).
- **Elliptic localization is resonance** [L] (`EllipticLocalizationIsResonance`). The symmetric dilation by `a > 1` has a real symbol at `ρ = σ + iγ`, `σ ≠ 1/2`, iff `γ log a ∈ πℤ`. One non-resonant scale plus local positivity forces the fibre to vanish (`eq_zero_of_nonresonant_scale`); a carrier closed under all archimedean scales is blind at every non-real off-line point (`eq_zero_of_archimedean_closed`); if every closure scale is resonant the fibre `z = 1` survives (`resonant_survivor`). The resonant group `exp((π/γ)ℤ)` contains at most one prime and depends on the unknown `γ`: within correspondence-closed carriers, elliptic localization needs a non-multiplicative operation.
- **The elliptic localizers** [L] (`TheEllipticLocalizers`). Affine maps commuting with `s ↦ 1 − s̄` are `s ↦ 1/2 + a(s − 1/2) + iκ`, `a` real; the stabilizer of an off-line pair is `{id, σ_γ}` (`affine_mem_pair_iff`), and `σ_γ = τ_γ ∘ (s ↦ 1 − s) ∘ τ_{−γ}` is the functional equation conjugated by the archimedean flow (`sigma_eq_tau_comp_fe_comp_tau`). On `σ_γ`-even fibres the local form is `+2|G(ρ)|²`, on odd fibres `−2|G(ρ)|²`. Dihedral dilemma: positivity on the span of a vector, its boost and their swaps forces the vector to vanish (`eq_zero_of_boost_swap_nonneg`); a positive carrier stable under one Hecke operator and under `σ_γ` is blind at every off-line pair of ordinate `γ` (`hecke_swap_blind`). The twisted symmetric symbol `p^{s−1/2} + p^{2iγ}p^{1/2−s}` acts on pairs of ordinate `γ` by a scalar.
- **Sectors are twists** [L] (`TwistedSectorsCollideQuartets`). `σ_γ`-symmetric tests are the twists `e^{−iγu} r` of even tests; Weil's form on twisted tests is Weil's form of the shifted configuration `Z − iγ` (`W_twist`), which collides the quartet at ordinate `γ` into the real pair `{1/2 ± δ}` (`shift_quartet`). Summand at a point of ordinate `γ`: `+m|tr f|²` on the even sector, `−m|tr f|²` on the odd sector.

### 1.3 The price of elliptic localization and the forcing gap

- **Gauge charge** [L]. The twisted explicit formula has shifted poles, phased prime weights `Λ(n) n^{−1/2}(n^{−iγ}k(log n) + n^{iγ}k(−log n))` and a shifted digamma density (`twisted_explicit_formula`); for every `γ ≠ 0` some `n ∈ {2^k, 3^k}` has `Λ(n) > 0` and `cos(γ log n) < 0` (`exists_vonMangoldt_pos_cos_neg`): every off-axis elliptic localizer is gauge charged.
- **Conductor horizon** [L]. For every `ε > 0` there is `C` with `Re W_ζ(e^{−iγu}f) ≥ 0` for every `C²` test of aperture `a` once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)` and two tail conditions hold (`elliptic_sector_nonneg_below_conductor_horizon`). The bound uses only `|Λ|`: below the horizon twisted positivity is source-blind. Beyond it, no eventual-in-height positivity holds for all tests: coefficient `2` is optimal for the prime symbol and no power saving is eventual (`not_exists_eventually_atTop_PX_ge_of_lt_two`, `not_exists_eventually_atTop_endpointPair_power_saving`), because Kronecker peaks of the prime phases recur syndetically.
- **The forcing half** [L] (`TheForcingHalfOfEllipticLocalization`). The single-height detector `sinh(δu)(a² − u²)₊^{5/2}`, twisted to the ordinate `γ₀` of a candidate zero, is `σ_{γ₀}`-odd. If local zero counts are `≤ A₀ log(|t| + 3)`, Weil's form is nonnegative on that one test, and the depth signal `sinh(δ(a − 2w))⁴` beats the background (`hbig`), then an off-line zero `1/2 + δ + iγ₀` has an off-line companion within ordinate distance `R` (`odd_sector_nonneg_forces_offLine_companion`). The even sector cannot force (`even_sector_summand_nonneg`).
- **The forcing gap** [R]. With `w = ca`, `c < 1/4`, and `R ≥ e^a`, `hbig` reads `e^{2δa(1−4c)} ≳ A₀ a⁵ log γ₀`, i.e. `e^a ≳ (log γ₀)^{1/(2δ(1−4c))}`. The conductor horizon supplies the positivity hypothesis only for `e^a ≲ (log γ₀)/(4 + ε)`. For every depth `δ < 1/2` the two ranges are disjoint; they meet only as `δ → 1/2`. The forcing half therefore needs one sign — `W ≥ 0` on one odd-sector test at the candidate's own ordinate — at apertures between the conductor horizon and the zero-spacing scale `a ≍ log γ₀`. The Kronecker-peak obstructions concern all tests at aligned heights, not this test at this height.

### 1.4 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, `F F′ = q` | exact (AOG) | no: hold on the golden datum `1 − 5X + 5X²` |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs (`normGraph_square`); Tate's limit law turns a bounded-error square law into an exact one (`tateLimit_parallelogram`) | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free: similitude law (`normGraph_degree_act`); the Frobenius is always a similitude of ratio one (`frob_star_mul_frob`) | no |
| L4 Kernel counts | `#ker ≥ 0`; exterior counts | determinant counts pair conjugates, nonnegative without real eigenvalues (`counts_do_not_force_purity`); coupled counts are modulus squares for every datum (`couple_detDeg_eq_normSq`); exterior counts force unitarity over `𝔽_q` (`unitary_of_exteriorDetDeg_nonneg`) | collided positivity only |
| L5 Rosati positivity | polarization | `⇔` orbit Hodge index `⇔` RH; similitude + anisotropic eigenvector `⇒` unit modulus (`normSq_eq_of_similitude`); Rosati form `≥ 0` iff unitary (`rosatiForm_nonneg_iff_unitary`) | missing |
| L5′ Counting origin of L5 | Riemann–Roch on `C × C` | a section count with RR and Bézout `⇔` Hodge index (`hodgeIndex_iff_exists_sectionCount`); an effectivity function `⇔` Hodge index (`hodgeIndex_tfae`); a naive height at bounded distance `⇔` Rosati positivity (`orbitHodgeIndex_iff_exists_naiveHeight`) | each is RH over `ℤ` |
| L6 Base | fixed tensor loss (Deligne) | fixed tensor loss `⇔` RH (`riemannHypothesis_iff_fixed_tensor_loss`); twists are rate neutral (`twisted_growth_iff`) | missing |

The polarization law isolates what is missing: the involution and the similitude are free; positivity of the trace is the whole content, and it fails exactly where eigenvectors become isotropic (`rosatiForm_single`).

### 1.5 Counting is the sign

ArithmeticEffectivityTheory (AE) and ACP turn Weil's counting argument into exact receivers over `ℤ`:

- **Section counts** [L] (`ASectionCountIsTheSign`). On every polar surface `h⁰ ≡ 1` satisfies Riemann–Roch and `h⁰ ≡ 0` satisfies Bézout; making `x` and `−x` effective at `x² > 0` violates Bézout. A count with both axioms exists iff the Hodge index holds; over `ℤ` iff RH (`riemannHypothesis_iff_exists_sectionCount`), over `𝔽_q` iff purity on every window.
- **The effectivity calculus** [L] (`TheEffectivityCalculus`). With `χ(x) = ½ x·(x − κ) + χ₀`, the Riemann inequality `χ(x) ≤ h(x) + h(κ − x)` plus subquadratic growth in degree zero forces the Hodge index (`ampleHodgeIndex_of_riemannInequality`); conversely `½ max(0, χ)` works under the Hodge index. A degree-zero class is abundant iff `x² > 0`; the least growth rate along `x` is `max(0, ½x²)`. On the scaling surface an effectivity function exists iff RH, and an off-line zero is an abundant class (`riemannHypothesis_iff_no_abundant_class`). `ℙ¹ × ℙ¹` over `𝔽_q` satisfies every law with a genuine `h⁰` (`hyperbolicPlane_hodgeIndex`).
- **The base does not extend** [L] (`TheBaseDoesNotExtend`). The Riemann inequality forces Hilbert–Samuel growth `n²`; the theta `h⁰` of the degree satisfies linear RR on every surface and the quadratic Riemann inequality on none (`thetaEffectivity_not_riemannInequality`).
- **Tate's limit law** [L] (`TatesLimitLaw`). A degree-two homogeneous `q` is nonnegative iff some function bounded below lies at bounded distance from it (`exists_naiveHeight_iff_nonneg`). Rosati positivity at a cycle holds on real correspondences iff on integral ones iff the integral Rosati form has a naive height; RH iff every cycle's has one (`riemannHypothesis_iff_forall_exists_naiveHeight`). In genus one the kernel order is its own naive height (Hasse); the golden datum has none.
- **The theta surface** [L] (`TheThetaSurface`). `h⁰(a, d) = log Σ_n e^{−π(n+a)² e^{−2d}}` satisfies `h⁰(a, d) − h⁰∨(a, −d) = d` for every characteristic `a`. `log ϑ(J, t) = πJ²/t + O_t(1)` is a nonnegative naive height whose Tate limit is positive definite: a polarization from counting. It is soft: translating the lattice changes only the bounded part, so the quadratic term is the same on every fibre (`hasSum_shifted_thetaChar`), and the fibre at `a = 0` (whose Mellin transform is `Λ(s)`) is not selected.
- **The diagonal collapse** [L] (`TheDiagonalCollapse`). The lattice `ℤ(n, m)` of a Hecke graph has lattice zeta `n^{−s₁}m^{−s₂}ζ(s₁ + s₂)`; `ℤ²` gives `ζ(s₁)ζ(s₂)`. On the reflection plane the diagonal variable lies on `Re = 1` and the product is `|ξ(s)|²`: lattice counts on the square give boundary or determinant positivity, never Rosati positivity. A count with quadratic RR needs rank growing with the class.
- **One-sided counts** [L] (`TheStepanovCountIsTheSign`, `TheStepanovMethodOverZ`). RH iff `ψ(x) − x ≤ C√x log²x` eventually (Bombieri's one-sided principle over `ℤ`). An auxiliary `1 − T_p^N` kills only critical symbols; a `K`-term polynomial auxiliary vanishes to order `< K` at every nonzero symbol. Integrality gives `lcm(1,…,n+1)∫₀¹P ∈ ℤ` and Nair's `ψ(2m+1) ≥ m log 4`; the square-root sign is the integer Chebyshev problem. Reading [R]: the integer Chebyshev constant of `[0, 1]` exceeds `1/e`, so univariate integer polynomials on `[0, 1]` classically stop below the prime number theorem (Gorshkov, Montgomery).
- **Horizon torsion** [L] (`TheHorizonTorsion`). `log |ℤ/lcm(1,…,N)ℤ| = ψ(N)`; `log n = log|ℤ/nℤ|` is the product formula, the only integrality inequality of the base; the box class `√N·A` has `χ = N`; RH iff `ψ(N) = N + O(√N log²N)`: two computations of one Euler characteristic agree at square-root precision.
- **Five currencies** [S] (`riemannHypothesis_effectivity_tfae`). An effectivity function, the absence of abundant classes, naive heights for integral Rosati forms, fixed tensor loss, and horizon torsion at `√N` precision are one statement. The golden datum satisfies the multiplicative base axioms (Beurling counts, integral zeta, functional equation) and has no effectivity (`goldenDatum_multiplicative_axioms_not_effective`).
- **Finite-level coupling of `+` and `×`** [L] (`TheTorsionCharacteristics`). `|τ(χ, ψ)|² = |F|` by orthogonality and `|root number| = 1`: at each finite level the coupling is exact and square-root sized by counting; the walls ask for it at the arithmetic point uniformly in the level.

### 1.6 Lefschetz theory at one prime: the local–global split

For a test `g`, `c_m = W(T_{p^m} g, g)`.

- One test serves every prime: `c_m^{(p)} = O(R^m)` iff `R ≥ p^Δ`; RH iff `|c_m^{(p)}| ≤ c_0^{(p)}` at any single prime.
- At one prime, width `≤ θ` iff every test has `ε Re c_m = O(p^{θm})` for a fixed sign; RH iff the upper (or the lower) one-sided Weil inequality holds; tests in `[−η, η]` suffice for every `η > 0`; RH iff `W(g − T_{p^m} g) ≥ 0` for `g` in `[−η, η]`, and each window is positive for `η ≤ 3/10`; one fixed shift `v` decides RH (`zeta_riemannHypothesis_iff_oneShift`).

Hodge index splits into a **local part** (short cycles), which holds, and a **Lefschetz part**, which is all of RH. In the language of §1.1 the Lefschetz part is the positivity of the equivariant form `W` on Hecke translates.

### 1.7 The first rung of every cancellation receiver is quasi-RH

The weakest nontrivial statement of each graded receiver is a fixed strip `Θ < 1`: WL lag or deficit at fixed rate, PBM convergence, the JAS level-one budget, balanced and centred-prime bands, every Vaughan power improvement, RW and ACS floors, admission at fixed damping, power growth of the damped receiver energy (`riemannZeta_sub_eq_zero_of_energy_growth`), one-sided Lefschetz bounds at one prime. Unconditional arithmetic stops at Vinogradov–Korobov. Escape is now located exactly: at damping `ε` the receiver escapes iff zeros lie right of `1/2 + ε`, up to a countable set of dampings, and RH iff it admits at every `ε > 0` (`riemannHypothesis_iff_forall_admits`) [L].

### 1.8 The gauge principle

The gauge torus `(ℝ/ℤ)^{primes}` acts by unimodular completely multiplicative twists.

- **Orbits, not points** [L]. Multiplicative data determine a source up to its gauge orbit; for `μ` the half-power law holds Haar-a.e., fails at the Liouville twin and at `0` is RH; the prime source is typical at `0` except for its pole; successor, pair and surplus statistics have gauge mean zero.
- **Finite lattice blindness** [S] (`PrimeGaugeTorusAndVacuumIntertwiners`). Every diagonal + ratio-shift + product-crossing lattice form on `[1, X]` is unitarily equivalent under a real sign gauge to the Euler form (`realSign_latticeForm_eq`); positivity is identical at the Euler and Liouville vacua (`nonneg_realSign_latticeForm_iff`).
- **The successor connection** [S]. `A_ω(n) = conj χ_ω(n) χ_ω(n+1)` is flat on `[1, N]` iff `ω(p) = 1` for every `p ≤ N + 1` (`succConn_flat_iff_primes_eq_one`); on `2 → 3 → 4`, `A₂A₃ = ω(2)` and `A₂²A₃ = ω(3)` (`catalan_holonomy_two`, `catalan_holonomy_three`); the Liouville vacuum has `A₃ = −1`. Additive structure reads the prime phases from three consecutive integers.
- **The first gauge charge is a twist** [L] (`TheFirstGaugeChargeIsATwist`). On kernels vanishing at `±log n`, `n ≥ 3`, `W_λ(f) = W_ζ(e^{−iγ₂u}f) + Δ_arch(f) + Δ_pole(f)` with `γ₂ = π/log 2` (`liouville_window_eq_zeta_twisted`): separating `ζ` from its twin there compares `ζ` with itself at two heights. No ordinate flips the atoms at `2` and `3` together (`not_twist_flips_two_and_three`): the second gauge charge is not archimedean.
- **The edge** [L] (`TheFirstGaugeChargedWindowOffTheEdge`). On the odd window `[−181/500, 181/500]` the atom satisfies `|a(F)| ≤ 2∫_E F²` on the edge strips `E = {log 2 − A ≤ |x| ≤ A}` of width `≈ 0.031`; `W_λ(F) ≥ ∫F²/1000 − 2√2 log 2 ∫_E F²`; the twin is positive whenever the edge mass is at most `1/1961` of the total.
- **Catalan repulsion** [S] (`QuantitativeCatalanDiophantineRepulsion`). `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50` for every `γ`; a twist `ε`-approximating the Liouville vacuum on `{2, 3}` needs `|γ| ≥ log(1/(50ε))`.
- **Monomial collapse and torsion rotation** [S] (`RamanujanTorsionStabilizersAndMonomialCollapse`). Separable `ℤ²` theta weights factor under monomial dilations, which fix the zero torsion point and the axes. Dyadic multiplication permutes `(ℤ/q)ˣ` without fixed points for odd `q ≥ 3`; the Ramanujan sum `c_q` is invariant under every coprime dilation, has mean zero and Parseval energy `qφ(q)`; the contrast `Δ_{q₁,q₂} = φ(q₂)c_{q₁} − φ(q₁)c_{q₂}` vanishes at `0` and separates divisibility branches.
- **Worst twin; amplification** [L]. On nonnegative tests `Re W_Λ ≤ Re W_w` for every `w ≤ Λ`. Gauge moments, family averages, products and relative powers lose at least linearly; twists are rate neutral.

Consequence: a `ζ`-specific sign must use gauge-charged structure — the archimedean place and pole, additive structure (the successor connection), the boundary of finite presentations, or the signs of prime-power atoms; beyond the first prime this charge is not archimedean.

### 1.9 Invariants, pole order and one-variable positive systems

- **Degree-one rigidity** [L]. Coefficient positivity, Riemann's FE, the simple pole and finite order determine `ζ`, stably; `CompletedPositiveSystem 1 d = ℝ^× · ζ` (`completedPositiveSystem_one_iff`). Relaxation models (pole order 2 or 3, strip poles, no FE, no positivity, the Siegel datum) admit off-line zeros. Pole order pays exactly for inserted zeros (`WeilIndexConservation`); pole order one is rigid; `4 ord_{1/2}Λ + 8Σ ord_x Λ + 5d < 9κ`.
- **Contraction calculus** [L]. Real off-critical pairs contract to `1/2` at `Δκ = 0`. A positive polar sum with a non-real rightmost residue has a real residue at least as large on that line, twice as large for one ordinate (`real_anchor_of_posDef_polarSum`); the pure quartet ratio is never positive. Planting a weight-two real anchor costs `Δκ ≥ 2` among zero-planting multipliers (`two_le_pole_cost_of_doubleRealAnchor_polarSum`); any completed positive system carrying a quartet with a double real anchor has `κ ≥ 3` (`three_le_pole_of_anchored_quartet`), from the Hadamard bound `16M + 144M/(9+4γ²) + 4 ord_{1/2}Λ + 72 ord_{1/2+iγ}Λ/(9+4γ²) + 5d < 9κ`. Direct pole-paid contraction costs `Δκ = 1` for `a ≤ 1/4`, `Δκ = 2` for `a < 1/2`.
- **Collision** [L]. `F_γ = F²F(s+iγ)F(s−iγ)` lifts `CompletedPositiveSystem κ d` to `HeightCoupledSystem (2κ) κ d γ`; quartets at ordinate `γ` contract at no marginal pole cost; the budget is the classical Hadamard count at `2 + iγ`. Boundary-twist factors absorb the shifted poles at central cost `κ₀ + 2κ_γ`, minimal (`HeightCoupledSystem.absorbShiftedPoles`); degree-`K` Fejér coupling lowers the central coefficient to `9(K+1)/(2K) → 9/2` (`FejerCoupledSystem`). Every height-coupled completion vanishes to even order on the real axis (`heightCoupled_order_even`), so a coupling anchors and never counts. No harmonic lift removes the whole lifted deepest divisor (`not_removes_lifted_divisor`, the Fejér barrier). The global conjugate collision `{2 Re ρ − 1/2}` has no analytic carrier (`zeta_global_collision_not_analytic`).
- **The coupled class is not rigid** [S] (`ChiralDeformationAndNonRigidityOfHeightCoupledSystems`). At every critical zero ordinate `γ`, `W_β(s) = ((s − 1/2)² + β²)/(s − 1/2)²` is Bochner positive and gives a member of `HeightCoupledSystem 2 1 1 γ` not proportional to `ζ_γ`, with central order lowered by two (`not_coupledRigid_of_xi_critical_zero`); by Hardy, rigidity fails at unbounded ordinates. The inverse, inward collapse, is not Bochner positive (`not_isEvenPosDef_inwardCollapseMultiplier`): positivity is chiral. Survivor: the **central vanishing ceiling** `ord_{1/2}Λ ≤ ord_{1/2}Λ_γ` for every member; a contracted off-line quartet raises the central order by four, so the ceiling at `γ` excludes off-line zeros at `γ` and the ceiling at every `γ ≠ 0` implies RH (`riemannHypothesis_of_forall_centralVanishingCeiling`). The converse is not proved. Rational surgery by `W_β` or a quartet contraction leaves the class of `O(2^{−σ})` Dirichlet-lattice decay (`criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice`).
- **Reading [R].** At an ordinate with `ξ(1/2 ± iγ) ≠ 0`, `ord_{1/2}Λ_γ = 0`, so the ceiling at `γ` is the central nonvanishing of every member of the coupled class.
- **Boundary and collars** [L]. Boundary forcing with each invariant necessary, capacity `⌊k/2⌋`, realization by one residue class; completed systems have `⌊κ/2⌋` collars of width `≍ 1/(d log T)`; interior multiplicative gain only from growth input (`a₁ ≤ 2cos(π/(K+2))a₀`).

### 1.10 Positivity: pointwise, averaged, at zero ordinates, without localization

- Exact form `Q(F) = (γ₀−2)‖F‖² + Lévy(F) + 4·horizonEnergy(F) + 2∫incoming·G²(C_F)`; floor-rate sets `[Δ, ∞)`.
- Windows: full `‖f‖²/5000` through `3/10`; odd `‖f‖²/1000` through `181/500`; primitive through `(log 2 + 1/50)/2`.
- Non-localizing positivity: `realTestsAt a`, `a ≤ 3/10`, is coercive, sees both points of every pair, and holds for every prime weight.
- Short-window averages on `Γ^{99/100} ≤ H ≤ Γ/8`; pointwise floor `Q_γ(F₀) ≥ −4(A+1)²e^A N(F₀)²Φ(γ)`; positivity for nonnegative tests at all but `CH/η` zero ordinates.
- Aperture flow: `μ(A)` strictly decreasing, RH iff `μ(A) > 0` for all `A`; Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`.
- Rates: `Δ ≤ polarRate = groundRate ≤ 1/2`; form-norm rates equal `Δ`.

### 1.11 Realization: blind, half-blind and isotropic carriers

The maximal sharp-stable positive Meyer ideal is the off-line-blind ideal (whole source iff RH); coupled point-stable carriers are isotropic; the left-blind ideal is positive, not blind; synthesis by critical jets and the Poisson boundary. Every invariant carrier sees each off-line pair through a boost, and boost-invariant positivity is isotropy. Every unconditional positivity theorem in the corpus is one of: positivity on a blind, half-blind or isotropic carrier; averaged positivity; non-localizing positivity; positivity on nonnegative tests; positivity of a collided form (kernel counts, coupled counts, escape forms, `D`); twisted positivity below the conductor horizon.

### 1.12 Positive Poisson pairs and the successor

Prime-side positivity is unconditional, spectral positivity is RH. Positive self-dual measures with a gap are Dirac combs; integer positive-definite functions are sign characters; the two-prime receiver is a Bochner problem on `T²`. Affine positivity on `Aff(ℚ)` is induced from the dilations; Weil's extensions are a box over the critical zeros; the successor sees continuous archimedean spectra, never atoms. The successor defect is small in the strip: `|D_Λ(s)| ≤ (4/(η(1+η−σ)) + 2/(η(σ−η)))(|s|+1)^{1−σ+η}` (`norm_succShiftDefect_vonMangoldt_le_rpow`) and on the real axis `D_Λ(σ) ≥ σ 2^{−1−σ}|ζ′/ζ(1+σ)|` (`le_re_succShiftDefect_vonMangoldt`) [L].

### 1.13 Cofactor modules and escape

- **Structure** [L]. Cyclic critical-Wiener modules; record minima with `K_pp ≥ p^{2ε−2}`; singleton-or-continuum kernel families; the cofactor Gram is a translation Gram of one profile with Laplace form `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s`; rank-one and nonresonant finite-rank escape rows are translated zeros.
- **Escape states** [L]. For finite, power-row and absolutely summable dominant configurations (Bohr uniqueness, `InfiniteDominantConfigurationsAreComplete`) every escape state is a phase kernel of rank the number of dominant zeros. A dominant split `v = Σ Re(c_k n^{z_k}) + r` with subdominant `r` yields such a limit, and in critical normalization it tends to `0` under dilation: zero gauge spectrum (`exists_tendsto_normGram_of_dominant_split`, `tendsto_escapeKernel_shift_zero`).
- **Escape forms are collided forms** [L] (`EscapeKernelsAreCollidedForms`). The Cauchy denominators `2x + i(y_k − y_l)` are exterior points `ext(z_k, z̄_l) − 1/2`; escape forms are Pick forms of the conjugate exterior divisor, automatically positive. They pair each dominant zero with the conjugates of the dominant zeros, never with its reflection: escape classifies, it does not exclude.
- **Abel escape states** [S] (`TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol`). With the Abel weight `e^{−2cu}` the Gram is the cosine transform of `|G(c + iy)|²` (Wiener–Khinchin); dilation acts by the scalar `p^{−2c}`; a simple pole on the abscissa line carries the atom `π|r|²δ_{y₀}`; the finite-height part of an Abel escape state is determined by the poles on the abscissa line with no contour shift; otherwise the mass escapes to infinite height.
- **Criterion** [L]. RH iff every actual escape state at every `0 < ε < 1/2` has positive gauge mass.

### 1.14 Heat, divisor geometry, Vaughan calibration and payment domains

Local divisor geometry is complete at model level (Hermite barrier, optimal first heat, universal reflectors), every positive heat repairs high heads, residual region of bounded height and small heat; Vaughan admission at and above half damping, rank-two Gram at half damping, below half the signed long-modulus quadrature; the AIP linear diagonal reserve cancels on the polar-neutral hyperplane (`fullArchCrossingForm_polarNeutral_eq`) [S] and the log-cell shift correlation is a divisibility spine plus a Euclidean remainder bounded by a biarithmetic Sobolev energy uniformly in the multiplier (`euclideanCellRemainder_sq_le`) [S]; payment domains nonclosed, controlled by the graph norm.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit, critical-energy and cross-work receivers read `Δ` exactly; RH ⇔ `E` bounded; high zeros contribute `O(1)`. Counting forms: RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually (one-sided); RH ⇔ `ψ(N) = N + O(√N log²N)` (horizon torsion); Nair's floor `ψ(2m+1) ≥ m log 4` from integrality. Filtered deficit `Γ^{−1/2}` on frequency averages.
**(a)** W2–W4; W6; W7(i).
**(b)** B1.1 (bounded `E`; equivalently the one-sided count). B2.1 (fixed rate). B1.4 (averages to the actual head). B3.30 (auxiliaries beyond univariate integer polynomials).
**Walls:** 1.0, 1.1, 1.15, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; on the prime-threshold ladder RH ⇔ cumulative relaxation `≤ μ(3/10)`; ground rate = polar rate; local part of Hodge index holds.
**(a)** W2/W5; W7(ii); W4.
**(b)** B1.3 (sign at every aperture; the Lefschetz part). B3.6. B3.1. B1.4.
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent; terminal primes realize graph sources; the isolated critical prime channel is negative on narrow windows, positive (`≥ log 2/(8π⁴)`) on dyadic and wider windows [S]; bounded graph norm with vanishing diagonal is not compactness.
**(a)** W2–W4.
**(b)** B1.1 (complete history).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K+2)` on the matched-quantile history is RH-equivalent; hyperbola, centroid, square-debt identities and low-LCM payment proved.
**(a)** W2–W4.
**(b)** B1.1 (full history with high-LCM pairs, moving core, singular transport).
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers RH-equivalent; each fixed Hausdorff order positive beyond its threshold; order-24 sign closed by certificates.
**(a)** W2/W5.
**(b)** B1.5; B3.12.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; one-sided `O(√x)` forces RH with simple zeros. Balanced and centred-prime bands ⇔ `Θ < 1`; the Vaughan picture of §1.14; on the gauge orbit the half-power law holds a.e., fails at the Liouville twin, and at `0` is RH; finite multiplicative lattice forms cannot separate `μ` from `λ` [S].
**(a)** W3/W4.
**(b)** B2.1; B1.1 (typicality of the gauge point `0`); B2.6; B3.24.
**Walls:** 1.0, 1.1, 1.12, 1.18, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2`; RH ⇔ the bound at every `t ∈ (0, 1/2)`; one-sided `D_t(N) ≤ C` is RH-equivalent.
**(a)** W2, W4.
**(b)** B1.3 (signed nonlocal covariance).
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** RH ⇔ all-height head coefficient positivity at fixed `R² ≥ 1/2`; every positive heat repairs high heads; reality beyond `2π exp((27/40+ε)/t)`.
**(a)** W7(iii); W2/W5.
**(b)** B1.5; B2.9; B3.9.
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace = winding; an integral nonnegative residual below one vanishes; neither sign nor the sub-unit bound is derived.
**(a)** W2, W4.
**(b)** B1.6.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** Prime-blind and odd receivers; finite `D` even, RH ⇔ `D < 2`; the one-prime Lefschetz receivers (§1.6); correspondence surface with free square law and budget. Counting forms (§1.5): section count with RR and Bézout ⇔ RH; effectivity function ⇔ RH; naive heights for integral Rosati forms ⇔ RH; RI with paired growth `≤ rn²` arbitrarily late forces `x² ≤ 2r`. Two-form picture (§1.1): `Re W = D − Δ`; RH ⇔ `W = D`; RH ⇔ `D` Hecke invariant [S].
**(a)** W2, W4; W7(xii).
**(b)** B1.3; B1.7 (`D < 2`); B1.9 (an arithmetic naive height or effectivity function); B1.11 (equivariance of `D`) [S]; B2.2; B3.10; B3.33; B3.35.
**Walls:** 1.3, 1.4, 1.17, 3.13, 14.2, 14.4, 14.18, 14.21.

### CHMD — Causal hyperbolic–modular duality
**Status.** Odd energy nonnegative iff no odd bound state above `1/2`; fixed-aperture completion, sharp cuts, domain preservation and nodal convergence proved.
**(a)** W3/W4.
**(b)** B1.3 (nodal / reflected-prime inequality).
**Walls:** 1.3, 3.3, 3.4.

### TH — Theta moment positivity
**Status.** All-rank strict positivity on the orthant at small time; fixed-rank coercivity; rank-`N` tests blind above height `O(N√log N)`.
**(a)** W2/W5.
**(b)** B1.5; B3.12.
**Walls:** 1.6, 3.11.

### RN — Theta renewal and singular comparison
**Status.** Compact cone-positive renewal operator realizes the denominator through `det₂`; cone positivity does not confine resonances.
**(a)** W2, W4.
**(b)** B1.6 (boundary-current orientation).
**Walls:** 1.2, 14.1, 14.3.

### WD — Ward orientation and horizontal collision
**Status.** The nonnegative global cap vanishes iff RH; collision masses even, matching the index bridge; Hermite barrier, optimal heat and large-height repair proved.
**(a)** W7(iii); W2.
**(b)** B1.6; B1.5.
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate; off-line rates `≤ 1/431`, `β < 1/300`; currency is reciprocal depth.
**(a)** W2/W5.
**(b)** B1.7.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint limits; RH ⇔ nonnegative first variation on RH-complete tent families.
**(a)** W3/W4.
**(b)** B1.3.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal admission and Haar approximation RH-equivalent; RH ⇔ admission at every damping, escape filling `(0, Θ − 1/2)` up to a countable set; cofactor structure of §1.13; escape forms are collided Cauchy forms; Abel escape states read the symbol's boundary poles [S]; RH ⇔ positive gauge mass of every escape state; the centered divisor prefix = bounded short sawtooth + long-modulus quadrature.
**(a)** W3/W4; W7(viii) (upper direction of the energy-rate law); W12.
**(b)** B1.2; B3.2 (residue summability and infinite-height mass); B3.3; B3.11; B3.16.
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** Positive level-one budget ⇔ half-plane bound `< 1/2`; half-power endpoint is RH; Gamma–theta source admitted at all finite supports.
**(a)** W2–W4.
**(b)** B2.1; B1.1.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Chronological tail and Báez–Duarte approximation
**Status.** Residual = `(1 − readout)² + centeredEnergy`; RH ⇔ both small; floor `κ/log N` exact.
**(a)** W2/W5.
**(b)** B1.2; B3.3.
**Walls:** 1.8, 1.10, 3.12.

### HCF — Gaussian heat trace / critical feature variance
**Status.** All-degree positivity of the two literal grids (`log 2`, `log 3`) on their polar hyperplanes is RH-equivalent; one grid aliases.
**(a)** W2/W5.
**(b)** B1.5.
**Walls:** 1.6, 3.4, 3.11.

### XN — Xi Newton invariant discs
**Status.** Line-centred Newton discs covering every zero ⇔ RH; the interior margin is subharmonic.
**(a)** W2.
**(b)** B1.5.
**Walls:** 1.2, 3.2, 14.3.

### BAG — Deterministic zeta self-return
**Status.** Strong, local and cutoff-uniform positive-mass recurrence each RH-equivalent; recurrence exactly at non-zeros.
**(a)** W3/W4.
**(b)** B1.7.
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; high-window positivity; full-cone source selection; finite-level existence ⇔ RH.
**(a)** W2–W5.
**(b)** B1.3.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay RH-equivalent; an off-line zero forces a late positive charge floor.
**(a)** W2.
**(b)** B1.5.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity RH-equivalent; light-cone variation positive; odd `181/500` window is the first certificate reading a prime. Its Liouville twin is a height twist of `ζ` there (`γ₂ = π/log 2`) and is positive on every test with edge mass `≤ 1/1961`; the second gauge charge is not archimedean; Catalan repulsion `e^{−|γ|}/50` [S].
**(a)** W2–W5; W8.
**(b)** B1.3; B3.26.
**Walls:** 1.3, 1.18, 3.4.

### PBM — Regularized prime/log-ζ abscissa
**Status.** Half-plane bound at `α` ⇔ convergence on `Re s > 1/2 + α`; RH is `α = 0`.
**(a)** W4.
**(b)** B2.1; B1.1.
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas divisor-sum criterion
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need growing lcm cores.
**(a)** W2.
**(b)** B1.7.
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH; smooth detector at aperture `Cδ^{−2}(4+|γ|)²`; single-height phase-selective law; eventual all-height saving refuted (Kronecker peaks); one-prime Lefschetz receivers. The detector, twisted to its ordinate, is the odd sector of the elliptic localizer; twisted positivity is a theorem below the conductor horizon; the forcing half turns one odd-sector sign into an off-line companion; the forcing gap separates the two by a power of `log γ` [R].
**(a)** W3/W4; W6; W7(x).
**(b)** B1.4; B1.1; B1.3; B1.9; B3.20; B3.32.
**Walls:** 1.17, 3.1, 3.2, 3.14, 3.19.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation to `Ke^r e^{−c√r}`; Schur payment to a finite head; exact shared-budget descent. The apparent linear diagonal reserve cancels against off-diagonal polar terms on the polar-neutral hyperplane, leaving `−Σ n³q_n²/(n⁴−1)` [S]; the log-cell correlation splits into a divisibility spine and a uniformly bounded Euclidean remainder [S].
**(a)** W2/W5.
**(b)** B1.3; B3.8.
**Walls:** 1.3, 3.4.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Exact source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; non-localizing positivity; Lefschetz receivers; Weil's layers over `ℤ` (§1.4).
- Counting (§1.5): section count ⇔ Hodge ⇔ RH; effectivity calculus; base `h⁰` does not extend; Tate heights; theta surface soft; diagonal collapse.
- One-variable systems (§1.9): κ = 1 class `ℝ^× · ζ`; contraction calculus closed (anchored quartet ⇒ `κ ≥ 3`); collision calculus closed (Fejér barrier, even real orders, global collision non-analytic); coupled class not rigid; central vanishing ceiling ⇒ RH [S].
- Two forms (§1.1): `W = D − Δ`; `D` positive, Hecke invariant iff RH [S].
**(a)** W1; W7(xi), W7(xii); W11; W12.
**(b)** B1.6; B1.8; B1.9; B1.11; B1.12; B3.18; B3.28; B3.33; B3.34; B3.35; B2.5.
**Walls:** 1.3, 1.15, 1.16, 1.17, 3.8, 3.14, 3.18, 14.4, 14.8, 14.10–14.22.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6. Ten theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- a carrier closed under multiplicative correspondences acts hyperbolically at every off-line pair; elliptic localization inside correspondence-closed carriers is resonance, at most one prime; the only reflection-compatible affine localizer is `σ_γ`, whose even sector cannot force;
- positivity on nonnegative tests is shared by every dominated twin;
- finite multiplicative certificates are capped by growth input; completed and coupled systems reach the boundary, the `1/log T` collar and the classical local count;
- a mechanism must separate `ζ` from the relaxation models at pole order two and from the `W_β`-deformed members of the coupled class;
- a mechanism built from multiplicative data proves its conclusion for the whole gauge orbit; finite multiplicative lattice forms are blind to real sign gauges;
- kernel, coupled and escape-form positivity are collided (conjugate pairing) and see no sign;
- a section count with RR and Bézout, an effectivity function, a naive height, a one-sided count and a fixed tensor loss are each the sign: a candidate whose output is one of them has not reduced the problem;
- a counting polarization that is the same on every fibre (theta surface) is not selective;
- every positive one-variable construction removes a complex quartet only against a real anchor (κ ≥ 3 if the anchor is planted) and collides conjugate zeros only ordinate by ordinate.

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; Fredholm trace receiver exact. | W1–W3 | Annihilation of the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support. | W1, W2 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W1, W2 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; dyadic descent universality. | W2, W3 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation. | W2–W4 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W1, W2 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = sum over off-line zeros of `log\|ρ/(1−ρ)\|`, zero on critical zeros. | W2 | Cofinal contrast equality (B1.7); the contrast is a depth capacity like `Δ`. |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W1, W2 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W1, W2 | Source lift with integral count (B1.6); an integral count is the sign (B1.9). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source. | W2, W3 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained. | W2 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; Ξ-limit ⇔ RH; prime-log stacks cannot converge to Ξ. | W2 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Energy probabilities erase grade. | W2 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0. | W2, W3 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W1, W2 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centred real compact-uniform convergence suffices. | W2, W4 | Arithmetic couplings with a centred limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W2 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic, with exact depth laws; they detect, they do not force. FEL's contrast and PL's `Δ` are both nonnegative depth capacities vanishing exactly on critical zeros; neither has the arithmetic upper bound that would force it to zero.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; bands ⇔ `Θ < 1`; half-damping transition; every power improvement ⇔ a fixed strip. | W4 | B2.1; B1.2 |
| **ADR / AOT** cofactor modules | §1.13; record minima, contraction calculus, eigencharacter moduli, translated-zero escape rows, two-factor pole trace. | — | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates, long moduli | §1.10; long-modulus decomposition. | W7(ii) | B3.6, B3.1; B1.2 |
| **ACS / Meyer** | §1.6, §1.10, §1.11. | — | B1.6, B1.8 |
| **ACP** correspondence positivity | §1.1–§1.5, §1.9, §1.13: normalized graphs, budget, determinant vs Rosati, local types, elliptic resonance, section counts, Stepanov count, successor defect, first gauge window, contraction and collision calculus with minimum anchor cost, escape alternative, completeness criterion, Abel escape [S]. | W8, W9, W11 | B3.2, B3.26, B3.28, B3.30; B1.9 |
| **PL** arithmetic polarization | §1.1–§1.4, §1.9: polarization law, elliptic localizers, twisted sectors, price of localization, conductor horizon, forcing half, Fejér barrier, collision law, first charge a twist, diagonal collapse, rate neutrality, oscillatory capacity, coupling parity, escape forms collided; Hecke invariance of `D` ⇔ RH [S]. | W7(x), W7(xii) | B1.11, B3.32, B3.33 |
| **AE** arithmetic effectivity | §1.5: effectivity calculus, base does not extend, Tate's limit law, Stepanov over `ℤ`, theta surface, horizon torsion, `ℙ¹ × ℙ¹` calibration, Gauss sums; five currencies TFAE and golden countermodel [S]. | W12 | B1.9, B3.30, B3.35 |
| **BGG** biarithmetic gauge geometry [S] | §1.8, §1.9, §1.14: gauge torus and finite lattice blindness, successor holonomy, Catalan repulsion, coupled non-rigidity, chirality and central ceiling, lattice-decay separation, polar-neutral collapse, log-cell subdivision, Ramanujan torsion and monomial collapse. | W7(xi), W12 | B1.12, B3.26, B3.34 |
| **APD** positive duality | §1.12 and the invariant half of §1.9. | — | B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, regularity, families and Siegel exception; interior capped. | W10 | — (complete below RH strength) |
| **SBWF** strip Bochner–Weil forcing | Completed-system collars; κ = 1 class; `5d < 9κ`; base of the contraction calculus. | — | B3.18 |
| **ACG** correlation geometry | §1.8: gauge invariance, a.e. square-root law, comeager-null exceptions, prime pole, gauge charge of pair statistics, archimedean-line threshold, loss law, escape spectral measures, gauge-mass criterion. | W9 | B1.2, B3.24 |
| **AKT** Künneth theory | Product receivers see depth only through total length; Künneth positivity = point-count positivity. | W9 | — |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; base theta `h⁰`. | W4 | B3.10; B2.2 |
| **ALDG** local divisor heat | §1.14. | W7(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering, observation | Endpoints; high-zero tail; filtered deficit; closed-cycle recovery. | W6, W7(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3`, lag-2 `1/4` floors exact; zero-defect signs. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure. | — | B3.3 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36−ε)N − surplus`; surplus is gauge charge. | — | B2.5, B2.7, B3.24 |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density; Heath–Brown; KKL; dlVP, Littlewood, VK. | W6, W10 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - Whether a section count on the correspondence surface is weaker than the sign: no; with RR and Bézout it is the Hodge index, with either alone it is empty.
  - Whether elliptic localization exists inside correspondence-closed carriers: exactly at resonant scales of the unknown ordinate, at most one prime; the only reflection-compatible affine localizer is `σ_γ`.
  - Whether the coupled class `HeightCoupledSystem 2 1 1 γ` is rigid: no, at every critical-zero ordinate [S].
  - Whether an arithmetic Stepanov count is weaker than the sign: its natural output, a one-sided square-root count, is RH; one-prime Hecke auxiliaries kill only critical symbols.
  - The contraction calculus: minimum anchored cost `κ ≥ 3`; planting cost `Δκ ≥ 2`; boundary-twist absorption cost; Fejér barrier for coupled contraction; even real orders of coupled completions; non-analyticity of the global collision.
  - Whether the theta `h⁰` extends to the surface by the degree: no.
  - Whether multiplicative lattice forms see the Liouville vacuum: no (unitary equivalence) [S].
  - The first gauge charge: a height twist; separation only on edge-concentrated tests; the second charge is not archimedean.
  - Escape: located exactly (alternative), classified for dominant configurations, and its forms are collided Cauchy forms.
  - Further settled items: theorem of the square and budget free; positivity beyond isotropy only without localization; kernel counts blind to complex quartets; base at receiver level; successor coupling empty; κ = 1 class; Lefschetz receivers at one prime; family averages lose linearly; twists rate neutral; invariant completeness in degree one; absolute pole-order budget false; interior multiplicative forcing beyond growth input excluded; synthesis of the blind ideal; averaged positivity at `Γ^{99/100}`; summation-scope "defects" never existed.
- **Excluded mechanisms** (in addition to those of the [killed-routes catalogue](../rh-killed-routes.md)):
  - two-sided scalar rigidity of the coupled class as an exclusion mechanism;
  - inward collapse of critical pairs as a positive deformation;
  - section counts, effectivity functions, naive heights, one-sided counts or tensor bases offered as weaker inputs than the sign;
  - lattice counts on the square of `Spec ℤ` (rank one or Künneth) as Rosati positivity;
  - the theta-surface polarization as a selective positivity;
  - collided positivity (determinants, coupled counts, escape Cauchy forms, `D`) as Rosati positivity;
  - twisted positivity below the conductor horizon as a selective sign;
  - correspondence-closed elliptic carriers beyond resonance;
  - finite multiplicative lattice positivity as a selector of the Euler vacuum;
  - the AIP linear diagonal reserve as a free reserve.
- **Substitutions that do not hold.** Collided for Rosati; positive for equivariant; equivariant for positive; resonance for localization; twist for gauge charge beyond the first prime; soft polarization for selective polarization; section count for sign reduction; coupled class for the class of `ζ`; one-sided ceiling for two-sided rigidity; classification of escape for its exclusion; orthant for signed positivity; cone positivity for self-adjoint confinement; finite for all ranks; local payments for one budget; finite-aperture for global index; averages for selected heights; nonnegative tests for the full cone; algebraic for bounded inverses; zero-indexed objects for pre-divisor constructions; imported for forced regions; boundary capacity for interior depth; isotropy for blindness; the gauge orbit for the gauge point; product positivity for correspondence positivity; determinants for Rosati traces; a free budget for its sufficiency; global positivity for fibre information without localization.
