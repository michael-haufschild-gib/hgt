# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-27, corpus `0bd3153ba` (clean tree). Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; findings are recorded in `logs/review-2710-refresh-research-log.md`. Nothing was compiled. Labels: `[L]` integrated source, `[S]` working or unintegrated source (marked so in the frontier map, or in the umbrella-free `SelectivePositivityAndThresholdLaws`), `[P]` paper proof, `[R]` reading or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, classical ranges of known estimates. IDs `W1`–`W19`, defined in the [summary](obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

**Notation.** `Δ = sup_ρ |Re ρ − 1/2|` (the zero width), `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ`, `ρ* = 1 − ρ̄` is its reflection; `δ = Re ρ − 1/2` its depth. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`. `W` is Weil's form; `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**; `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**; `T_L` translation by `L` (the Hecke action of the dilation `e^L`); `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` the **Hecke defect** of `D`. `σ_γ(s) = 1 + 2iγ − s` is the elliptic localizer at ordinate `γ`. `ζ_γ(s) = ζ(s)²ζ(s + iγ)ζ(s − iγ)` is the height-coupled carrier, `Λ_γ` its completion, `HeightCoupledSystem 2 1 1 γ` its class. `ν_N` is the torsion measure (roots of unity of order `≤ N`). For a zero `p` of multiplicity `m`, `E(p) = Σ_{q ≠ p} m_q/(p − q)` is the **field** of the other zeros at `p` (regularized as in Lean); `Re E(p)` is its **transverse field**.

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space, and how far each is computed

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH; finitely many negative directions at every aperture [L] | yes, for every zero configuration [L] | the explicit formula (primes, Gamma, poles) |
| Collided form `D` | yes; faithful; at each aperture equivalent to the logarithmic Sobolev norm [L] | iff RH; a Hecke translation is a similitude of `D` iff RH [L] | the current `Δ log|ξ|` and polynomially many integer theta values, without zero indexing [L] |

- **Capacity identity** [L]. `Re W = D − Δ` on every compact `C²` test; RH iff `W = D` iff `D` is Hecke invariant iff some `T_L` (`L ≠ 0`) is a similitude of `D` (`riemannHypothesis_iff_W_eq_collided`, `riemannHypothesis_iff_collided_hecke_invariant`, `hecke_similitude_iff`).
- **`D` is the logarithmic Sobolev norm** [L] (`collidedForm_equiv_logSobolev`). For every aperture `A` there are `0 < c ≤ C` with `c ∫|f̂(σ)|² log(|σ| + 4) dσ ≤ D(f) ≤ C ∫|f̂(σ)|² log(|σ| + 4) dσ` on `C²` tests supported in `[−A, A]`: the norm of `L²` weighted by the zero density. `D(f) = 0` only for `f = 0`; `D ≥ ‖f‖²/5000` on `[−3/10, 3/10]`; the zeros with multiplicity are a sampling set for every Paley–Wiener space. Gårding: `Re W ≥ 2π‖f‖² − K ∫_{−T₀}^{T₀}|f̂|²`; every orthonormal family on which `W` is negative has fewer than `2AT₀K/π` members (`card_negative_orthonormal_le`). Local Weyl law: `(1 − η)‖f‖² log|γ| ≤ D(e^{−iγu}f) ≤ K_f log|γ|`.
- **`D` is computed** [L] (ConjugateDiagonalGeometry). The distributional Laplacian of `log|ξ|` evaluates compact test squares; a canonical exhaustion recovers `D` and every depth moment `Σ m_ρ |f̂(ρ)|² k(L, δ_ρ)^j`, `k(L, d) = 2cosh(2dL) − 2`. Integer theta prefixes of polynomial size (cutoff `(K + 4)(n + 1)^{20}`) recover the `4^j`-normalized moments for `a + j|L| ≤ 2 log(n + 1)`, `|τ| ≤ n/2`, with error `size(f)²(B/(n + 1)² + (640/n)(C + log(n + 4)))` (`exists_polynomialThetaSource_aperture_logarithmic_bound`). A two-radius reading detects zeros locally: a zero of `ξ` within `r_n = 1/(16(n + 1)^6)` of a centre `c` (`0 ≤ Re c ≤ 1`, `|Im c| ≤ n/2`) forces the reading above `1/2`, and a reading above `1/2` forces a zero within `2r_n` (`polynomialThetaLocalReading_uniform_zero_detector`). The readings use continuous integrals, not finite quadrature; uniform finite-theta amplitude bounds on vertical strips are in place (`ThetaCuspStripAmplitudeBounds`).
- **Depth geometry of `D`** [L]. `L ↦ D(T_L f)` is the Laplace transform of the depth measure; `(1/L) log D(T_L f) → 2a_f`. `E_f(L) ≤ k(L, 1/2) D(f)` (`heckeDefect_le_strip`) and `E(L)² ≤ D·(E(2L) − 4E(L))`, with equality at `L ≠ 0` iff all seen zeros share one absolute depth (`TwoScaleDepthRigidity`); `k(2L, d) = 4k(L, d) + k(L, d)²`.
- **Reading [R].** Since `W` is equivariant and `Re W = D − Δ`, `E_D(L) = E_Δ(L)`. Over `𝔽_q`, `D` is the Hermitian trace and `W` the Rosati trace on `H¹`; purity is their coincidence (`re_rosatiForm_eq_collided_sub_defect`, `collided_frob_invariant_iff_unitary` [L]). What computes `D` is answered; what bounds `E_f(L)` above by something that vanishes is not.

### 1.2 Local type, elliptic localizers and the forcing gap

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, signature `(1, 1)`.

| Type | Action on the fibre | Correspondences | What positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost `diag(β, β̄⁻¹)`, `\|β\| ≠ 1` | Hecke operators, archimedean flow, gauge twists, exactly at off-line pairs | isotropy |
| Elliptic | rotation or swap | Hecke operators on the line; resonant symmetric dilations; `σ_γ` | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the additive successor | nothing |

- **Resonance** [L]. A symmetric dilation by `a > 1` is elliptic at an off-line point of ordinate `γ` iff `γ log a ∈ πℤ`.
- **Elliptic localizers** [L]. The stabilizer of an off-line pair among reflection-compatible affine maps is `{id, σ_γ}`; even sector `+2|G(ρ)|²` (cannot force), odd sector `−2|G(ρ)|²`. Hecke + `σ_γ` stability is blindness.
- **Symmetric squares** [L]. For a symbol `β ≠ 0`, `(β − c)(β⁻¹ − c)` is a nonnegative real for every real `c` iff `|β| = 1`; for the Hecke symbol `p^{ρ − 1/2}` this is `Re ρ = 1/2` at one prime, with no resonant exception (`symSquare_heckeSymbol_nonneg_iff`). The kernel count of a symmetric square is a square and sees nothing. The positivity Weil's argument uses is pointwise positivity of this spectrum.
- **Sparse annihilators** [L]. A `K`-term polynomial vanishes to order `< K` at every nonzero point; `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = 1/2` and `N Im ρ log p ∈ 2πℤ`. Stepanov's mechanism needs a spectrum on a lattice.
- **Conductor horizon** [L]. `Re W_ζ(e^{−iγu}f) ≥ 0` for every `C²` test of aperture `a` once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)`; source-blind there. Beyond it, no eventual-in-height positivity holds for all tests (Kronecker peaks).
- **Forcing half and gap** [L]. One sign of `W` on the twisted odd detector, a local count `≤ A log(|t| + 3)` and depth dominance force an off-line companion within ordinate distance `R`. A successful certificate needs `768A log(|γ| + 3) < e^{2δa}`; this never coexists with the conductor horizon for `0 ≤ δ ≤ 1/2` (`TheConductorForcingGap`).
- **Reading [R].** Beyond the horizon the detector's prime side is a Dirichlet polynomial of length `(log γ)^{O(1)}` evaluated at the zero's ordinate; its sign is governed by how `γ log p` aligns modulo `2π`.

### 1.3 The transverse field and the outward reserve

- **The Rankin–Selberg square sees the field** [L] (`TheRankinSelbergSquareSeesTheFieldOfTheOtherZeros`, `TheVonMangoldtSquareIsTheZetaSource`). `L(Λ ⋆ Λ, s) = (ζ′/ζ)²` on `Re s > 1`. For `F = Σ_j m_j/(s − z_j)`, `F² = Σ_j m_j²/(s − z_j)² + Σ_j 2m_j E_j/(s − z_j)`: the simple-pole coefficient at `z_j` is `2m_j` times the field of the other points. On critical configurations `Re E_j = 0` (transverse equilibrium); at the deepest off-line point, with its reflection present, `Re E_j > 0`.
- **Quadratic terminals** [L] (`EveryXiZeroHasALocalQuadraticTerminal`, `RightQuadraticTerminalsNearOffLineZeros`, `QuadraticAscentReachesALocalMaximum`, `LogarithmicWindowsAreQuadraticallySparse`). Every right-hand `ξ` zero `q` has a right-hand zero `p` within ordinate distance `C log(|γ_q| + 3)`, at least as deep, with an empty quadratic ascent cone: `δ_r² ≤ δ_p² + (γ_r − γ_p)²` for every zero `r`.
- **The outward ray** [L] (`exists_local_outward_zeta_ray`). On the ray `p + h`, `0 < h < 1/2 − a` (`a` the depth of `p`, `m` its multiplicity), `ξ` and `ζ` do not vanish and `m/h + m/(2a + h) + c·a·log(|γ_p| + 4) ≤ Re(ζ′/ζ + Γ-part)(p + h)`. Every ordinate has at least `log(|t| + 4)` zero copies at distance in `[1, H]` (`exists_xi_zero_logarithmic_band`).
- **The witness** [S] (`exists_local_outward_field_witness`). Every off-line zero has such a terminal with transverse field `≥ m/(2a) + c·a·log(|γ| + 4)`, and the simple Laurent coefficient of `(ζ′/ζ)²` at the terminal equals `2m` times the regular part `B(p)` of `ζ′/ζ`, bounded below by `m²/a + 2mca log(|γ| + 4) − 2m Re(Γ-part)`.
- **Reading [R].** The reserve is a large value, of order `a log γ`, of the regularized prime sum `−Σ Λ(n) n^{−(1/2 + a + h) − iγ_p}` near the terminal ordinate: Liouville-like alignment of `γ_p log p` for small primes. Excluding the off-line zero through it needs an arithmetic upper bound for `Re ζ′/ζ` on the outward ray below `c·a·log γ` — an interior de la Vallée Poussin inequality. It is the same Diophantine question as §1.2's reading, entered from the zero side. The witness detects; it does not exclude. Under RH, `‖ζ′/ζ(σ + iγ)‖ ≤ C log|γ|/(σ − 1/2)` (`exists_logDeriv_zeta_bound_rh`).

### 1.4 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, `FF′ = q` | exact | no: hold on the golden datum `1 − 5X + 5X²` |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs; Tate's limit makes bounded-error square laws exact | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free: similitude law | no |
| L4 Kernel counts | `#ker ≥ 0`; exterior counts | determinant and coupled counts are collided; the complex fake has every kernel count `≥ 0` and Rosati value `−2304` at `F² + 16` | collided positivity only |
| L5 Rosati positivity | polarization | `⇔` orbit Hodge index `⇔` RH; `⇔` pointwise nonnegativity of symmetric-square spectra | missing |
| L5′ Counting origin | RR on `C × C`; Stepanov count + `\|τ\|² = q` | section count, effectivity function, naive height, convex height, one-sided count, horizon torsion: each RH; Stepanov needs a lattice spectrum | each is RH |
| L6 Base | fixed tensor loss | fixed tensor loss `⇔` RH; twists rate neutral | missing |

**Calibration over `𝔽_q`** [L]. RH for odd-degree squarefree hyperelliptic curves over every finite field of odd characteristic by counting (`riemannHypothesis_oddHyperelliptic`), including the split case through degree sums and Weil's bound `|Σ_x χ(Π_{c∈S}(x − c))| ≤ (|S| − 1)√q` (`HyperellipticRiemannHypothesis`, `HyperellipticCharacterSums`); Hasse for elliptic curves. Effectivity functions and naive heights exist there unconditionally (`TheHyperellipticCalibration`); `ℙ¹ × ℙ¹` has an exact effectivity function.

**Completion law** [L]. At finite level square-root cancellation of complete sums is a count (`|τ|² = q`), and completion transports it to incomplete sums (Pólya–Vinogradov). Burgess's bound for quadratic characters on all intervals and `r ≥ 2` and the least non-residue `≤ p^{1/(4√e) + ε}` are proved (`TheBurgessBound`, `eventually_exists_nonresidue_le`). The arithmetic point (`Σ μ(n)`, `ψ(x) − x`) has no period. Over `ℤ`, integrality gives the Stepanov floor `log(1/∫₀¹ P) ≤ ψ(n + 1)` for `P ∈ ℤ[X]` with positive integral (`TheStepanovMethodOverZ`), Nair's floor.

### 1.5 Counting is the sign

- **Section counts and effectivity** [L]. A count with RR and Bézout, or an effectivity function, exists iff the Hodge index; over `ℤ` iff RH.
- **Six currencies** [L]. An effectivity function, no abundant class, a naive height for every integral Rosati form, a fixed tensor loss, horizon torsion at `√N` precision and a midpoint-convex height at bounded distance from every integral Rosati form are each RH.
- **The polar box** [L]. The box count is an effectivity function iff the Hodge index; subtracting the prime-power nodes gives `N − ψ(N)` and destroys the Riemann inequality.
- **Torsion potential** [L]. `Λ(n) = Σ_{μ primitive} log|1 − μ|`; RH iff `Σ_{n≤N} Σ_{(k,n)=1} log(2 sin(πk/n)) = N + O(√N log²N)`; `ν̂_N(1) = M(N)`; `log P_N(q) = Σ_{d≤N} M(⌊N/d⌋) log[d]_q`.
- **Large-sieve sections** [S]. Finite Jacobi–Hurwitz packets are blind on degree zero or inflate quadratically; an unsigned large-sieve majorant forces `q_P(z) ≥ |z·z|/2`; section supply beyond the large-sieve diagonal is a zero-free strip; sign-free Serre-dual box cohomology fails Riemann–Roch on the golden datum.
- **Theta surface and lattice counts** [L]. The theta surface's counting polarization is the same on every fibre; lattice counts on the square give `ζ(s₁ + s₂)` or `ζ(s₁)ζ(s₂)`.

### 1.6 Budget currencies

A **budget** is a linear log-energy of a row: `∫_0^L e^{−u} g(⌊e^u⌋)² du ≤ S L + B`.

| Row | Over `ℤ` | Over `𝔽_q` |
|---|---|---|
| Prime error `ψ(n) − n` | a budget exists **iff RH** (`riemannHypothesis_of_primeError_budget`, `primeError_budget_of_riemannHypothesis`); every budget has `S ≥ 2 + γ_E − log 4π` (the archimedean genus). **Abel–Cramér law:** RH with simple zeros iff `2c·A(c) → 2 + γ_E − log 4π` as `c ↓ 0` (`tendsto_abelSlope_of_riemannHypothesis_of_simple`, `eventually_abelSlope_lt`, `eventually_lt_abelSlope`) [L] | a budget is purity; slope `Σ_β mult(β)²`, `= 2g` iff simple spectrum [L] |
| Mertens `M(n)` | a budget forces RH, simple critical zeros and `Σ_ρ |ρζ′(ρ)|^{−2} ≤ S` [L]; the converse is not formalized | a budget is purity with simple spectrum; slope = repulsion energy; genus one: strict Hasse `a² < 4q` [L] |
| Successor shift | `D_Λ(s)/s ∈ H²(Re s > 1/2)` with `‖·‖² = 2πΣΛ(n)²/(n(n + 1))`; the shifted prime error carries the same cost [L] | — |

Reading [R]: the prime-error budget is a two-sided receiver; the Abel–Cramér law adds simplicity at the genus. The Mertens converse is classical only under RH together with a bound `J_{−1}(T) = Σ_{|γ|≤T}|ζ′(ρ)|^{−2} ≪ T` (Ng's method); summability of the residues alone is not known to suffice, because the truncation needs horizontal growth bounds for `1/ζ` between zeros.

### 1.7 Torsion intersection theory

- **`Λ` is an intersection number** [L]. `I(m, mt) = φ(m)Λ(t)` for Galois orbits of roots of unity (Hecke law); the log-energy of `μ_a` against `μ_b` is `gcd(a, b) log lcm(a, b)`.
- **Weil's prime kernel is a renormalized positive energy** [L] (`weilPrimeKernel_renormalized_torsion_energy`). For `r < 1` the torsion energy `G∘T_r` is positive semidefinite; off the diagonal it tends to `−Λ(n/m)(n/m)^{−1/2}`; on the diagonal it diverges like `−log(1 − r)` and after renormalization tends to minus the log-discriminant. Positivity is lost exactly in the divergent self-energy.
- **Reading [R].** At `r < 1` positive, at `r = 1` Hecke equivariant: the two properties a polarization needs separate only at the diagonal. The same diagonal appears in `(ζ′/ζ)²`: its double pole `m²/(s − ρ)²` is the self-term, and removing it leaves the field `2mE(ρ)` (§1.3).

### 1.8 The gauge principle

- **Orbits, not points** [L]. Multiplicative data determine a source up to its gauge orbit; for `μ` the half-power law holds Haar-a.e., fails at the Liouville twin and at `0` is RH. Gauge-charged boundaries normalize at weight `1/4`, half the archimedean weight; the Möbius boundary law at the gauge point `0` is RH (`ChargedBoundariesAreCriticalAtAQuarter`).
- **Finite lattice blindness** [L]. Every diagonal + ratio + product lattice form is unitarily equivalent under a real sign gauge to the Euler form. The successor connection is flat iff `ω(p) = 1` on `[1, N + 1]` and reconstructs `ω(2), ω(3)` on `2 → 3 → 4`.
- **First gauge charge** [L]. On windows below `log 3` the Liouville twin is `ζ` twisted to height `π/log 2` plus Gamma and pole corrections.
- **First windows separate** [S]. At `181/500` an odd smooth test has `W_ζ ≥ ‖F‖²/1000`, `W_λ = W_{flip 2} < −‖F‖²/1000`; the full-sector floor of `ζ` is `1/5000` there; a shifted pair is negative on an even test. At `23/40` an odd test has `W_ζ > ‖F‖²/25`, `W_λ < −(3/10)‖F‖²`; the full floor of `ζ` at `23/40` is not certified. The successor-square form `w(2)w(4)` is `−(log 2)²` at `λΛ` and `+8^σ(log 2)²` on every scale twist; the Catalan twist defect of the Liouville twin is `≥ e^{−2|γ|}/5000`.
- **Repulsion** [L]. `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50`; with enough primes the sum beats `exp(−|γ|^ε)`: archimedean twists approach the Liouville vacuum at most stretched-exponentially fast.
- **Worst twin; amplification** [L]. On nonnegative tests `Re W_Λ ≤ Re W_w` for `w ≤ Λ`. Moments, family averages, products and relative powers lose linearly; twists are rate neutral.

### 1.9 Positive systems: one variable, polar configurations, deformations

- **Degree-one rigidity and contraction** [L]. `CompletedPositiveSystem 1 d = ℝ^× · ζ`; pole order pays inserted zeros; a complex quartet contracts only against a real anchor; an anchored quartet forces `κ ≥ 3`; planting costs `Δκ ≥ 2`; coupled completions vanish to even real order; Fejér barrier; the global conjugate collision has no analytic carrier.
- **Positive polar configurations** [L]. One vertical section at one abscissa decides positivity (`w ≥ 0`); the leading line carries a nonnegative almost-periodic sum and is itself a positive configuration; line hierarchy; commensurable positive lines are `|Q|²` (couplings).
- **Deformation principle** [L]. Landau–Wronskian principle; Abel–Gram law (divisor jumps even positive definite, bounded by the real one); critical conservation: for finitely many moved critical zeros, `r(0) + 2Σ r(z) cos(θz) ≥ 0` and the central drop pays every created critical zero twice.
- **The coupled class** [L]. `HeightCoupledSystem 2 1 1 γ` is not rigid at any critical-zero ordinate. Positive prime-mass rigidity at `γ` iff `ξ` has no zero at ordinate `γ`; positive chirality and the positive and rational central ceilings at `γ` each iff `ξ` has no off-line zero at ordinate `γ`; RH iff any of them holds at every `γ`.
- **Arithmetic members and quantization** [L]. A central excess forces a deficit series with abscissa `≥ 1/2` and Abel residue `≥` the excess; zero residue and no central drop force `F = Kζ_γ`. Where `ξ` has no off-critical zero at ordinate `γ`, the Abel residue of the surplus of a (perturbed) positive deformation, and of an arithmetic member with zero-residue half-power deficit, equals the central drop `D = ord_{1/2}Λ_γ − ord_{1/2}Λ`, an even integer `≤ 2 ord_{1/2+iγ} ξ` (`tendsto_abel_excess_eq_centralDrop`, `tendsto_surplus_residue_eq_centralDrop`). A full-class central ceiling at `γ` transfers to entire factors `Λ = (2ξ)^k Λ_G` (`TheCentralCeilingTransfersToFactors`); the ceiling itself and an actual Rankin–Selberg member are not constructed. For `ζ^d`: `κ ≤ d` and a sub-half deficit force `F = Kζ^d`; boundary capacity `2Σ ord_{1+it}Λ ≤ κ − d`.

### 1.10 Escape

- **Location and classification** [L]. At damping `ε` the receiver escapes iff zeros lie right of `1/2 + ε` (up to countably many `ε`); RH iff admission at every damping iff every actual cofactor limit has positive gauge mass; power growth of the energy gives gauge mass zero (`gaugeMass_eq_zero_of_powerGrowth`).
- **Energy-rate law** [L]. `E_ε(T) ≤ C_κ(T + 1)^κ` for every `κ > max(0, 2Θ − 2ε − 1)`, with its lower direction.
- **Abel atoms of `ζ`** [L]. Each dominant simple zero carries an atom of mass `π‖r_ρ‖²`, `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`; capacity, endpoint and shadow laws; effective orders are visible translated-zero orders.
- **Infinite height** [L]. Non-summable residue masses, an unattained abscissa or unbounded visible orders send every compact window's share to zero. Escape classifies; it does not exclude.

### 1.11 Positivity: pointwise, averaged, statistical

- Windows: full `‖f‖²/5000` through `3/10` [L] and through `181/500` [S]; odd `‖f‖²/1000` through `181/500` [L]; primitive through `(log 2 + 1/50)/2`.
- Non-localizing positivity (`a ≤ 3/10`) holds for every prime weight.
- Short-window averages on `Γ^{99/100} ≤ H ≤ Γ/8` (Selberg's near-line density on such windows is formal, `SelbergShortWindowNearLineDensity`); pointwise floor `−4(A + 1)²e^A N²Φ(γ)`; nonnegative tests positive at all but `CH/η` zero ordinates; a positive proportion of heights in every short window is Weil-positive for all nonnegative tests of aperture `A`.
- **Census** [L] (RHTower `Zeta23*`, the two-thirds certificate imported from the `Zeta23` dependency). In `(T, 2T]`: `(2/3 − ε)N + M_off ≤ N₀ˢ` (simple critical zeros, `M_off` the off-line multiple mass); hence `M_off ≤ (1/6 + ε)N`; at least `(4/5 − ε)` of the zero ordinates carry a critical zero (`four_fifths_critical_ordinates`); at least `3/4` of the zero copies satisfy `|Re ρ − 1/2| ≤ 4/log T` (`three_quarters_within_four_div_log`); either `N₀ ≥ (3/4)N` or at least `(HD(1) − 1/2 − 1/A − ε)N` simple off-line zeros lie within `A/log T` of the line.
- Aperture flow `μ(A)` strictly decreasing; Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`; polar ground rate equals the width when off-line zeros do not cluster (locally bounded copy count or depth mass), and the form-norm rate equals it unconditionally.

### 1.12 Realization and duality

Maximal sharp-stable positive Meyer ideal = off-line-blind ideal; coupled point-stable carriers isotropic; every invariant carrier sees an off-line pair through a boost. Positive self-dual measures with a gap are Dirac combs; affine positivity on `Aff(ℚ)` is induced from dilations; Hecke states `(nd)^{−s}·1[db ∈ ℤ]` are positive definite iff `s ≥ 1/2`; Weil's extensions are a box over the critical zeros. Every nonzero `L²` wave has a visible successor; atomic spectra stay blind; singular-continuous spectra are unclassified [L].

Every unconditional positivity in the corpus is one of: invariant (blind, half-blind, isotropic), averaged or statistical, non-localizing, on nonnegative tests, collided (kernel counts, coupled counts, escape forms, `D`), twisted below the conductor horizon, a finite-window certificate, positive before a renormalization (torsion energies at `r < 1`), or a zero-side reserve (outward field) that detects without bounding.

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit, critical-energy and cross-work receivers read `Δ` exactly; RH ⇔ critical energy bounded; high zeros contribute `O(1)`. RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually ⇔ horizon torsion ⇔ the Farey sum at `√N`; Nair's floor from integrality. Budgets (§1.6): RH ⇔ a linear prime-error budget, slope `≥ 2 + γ_E − log 4π`; RH with simple zeros ⇔ the Abel slope tends to the genus; the successor shift preserves the cost. Filtered deficit `Γ^{−1/2}` on frequency averages.
**(a)** W2–W4; W6; W7(i).
**(b)** B1.1; B1.13; B2.1; B1.4; B3.30.
**Walls:** 1.0, 1.1, 1.15, 1.19, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; on the prime-threshold ladder RH ⇔ cumulative relaxation `≤ μ(3/10)`; ground rate = polar rate, equal to the width when off-line zeros do not cluster; local part of the Hodge index holds. Gårding inequality and fewer than `2AT₀K/π` negative directions at aperture `A`; full floor `1/5000` through `181/500` [S]; no positive exponential floor.
**(a)** W2/W5; W7(ii); W4.
**(b)** B1.3; B3.6; B3.1; B1.4.
**Walls:** 1.3, 1.11, 1.13, 3.2, 3.14.

### FU — CCM-FU signed prime scheduling
**Status.** Both one-sided bounds of the completed Möbius–divisor Abel moment are RH-equivalent; terminal primes realize graph sources; the isolated critical prime channel is negative on narrow windows and positive on dyadic and wider windows [S]; bounded graph norm with vanishing diagonal is not compactness.
**(a)** W2–W4.
**(b)** B1.1 (complete history).
**Walls:** 1.1, 1.6, 3.2, 3.4.

### RP — Route-P / SP-E history floor
**Status.** An eventual floor `−B(K + 2)` on the matched-quantile history is RH-equivalent; hyperbola, centroid, square-debt identities and low-LCM payment proved.
**(a)** W2–W4.
**(b)** B1.1 (full history with high-LCM pairs, moving core, singular transport).
**Walls:** 1.1, 1.8, 3.6.

### PA — Prime–archimedean source passivity
**Status.** Current, Bernstein-mismatch and signed-moment receivers RH-equivalent; each fixed Hausdorff order positive beyond its threshold.
**(a)** W2/W5.
**(b)** B1.5; B3.12.
**Walls:** 1.5, 1.6, 14.1.

### MC — Möbius cancellation at half power
**Status.** `M(x) = Ω±(√x)`; one-sided `O(√x)` forces RH with simple zeros; `ν̂_N(1) = M(N)` and RH ⇔ `M(N) = O(N^{1/2+δ})` for every `δ`. A linear Mertens budget forces RH, simple critical zeros and `Σ|ρζ′(ρ)|^{−2} ≤ S`; over `𝔽_q` a Mertens budget is purity with simple spectrum and its slope is the repulsion energy. Balanced and centred-prime bands ⇔ `Θ < 1`; gauge a.e. law; gauge-charged boundaries critical at `1/4`; finite multiplicative lattice forms blind. Escaped Möbius pairings: growing-endpoint saving `θ` ⇔ zero abscissa `≤ 1 − θ`, `θ > 1/2` impossible [S]. Pólya–Vinogradov, Burgess and the least non-residue bound proved [L]; completion needs a period, which the arithmetic point lacks.
**(a)** W3/W4; W7(xv).
**(b)** B2.1; B1.1; B1.13; B2.6; B3.24.
**Walls:** 1.0, 1.1, 1.12, 1.18, 1.19, 1.20, 3.10.

### TT — Theta tail and heat–Cassini currents
**Status.** The directed Wold receiver bounds `D_t(N) + Q_t(N)/2`; RH ⇔ the bound at every `t ∈ (0, 1/2)`; one-sided `D_t(N) ≤ C` is RH-equivalent; restricted current signs and continuum light-cone positivity.
**(a)** W2, W4.
**(b)** B1.3 (signed nonlocal covariance).
**Walls:** 1.3, 1.6, 3.4.

### LA — Line anchor
**Status.** RH ⇔ all-height head coefficient positivity at fixed `R² ≥ 1/2`; every positive heat repairs high heads; reality beyond `2π exp((27/40 + ε)/t)`.
**(a)** W7(iii); W2/W5.
**(b)** B1.5; B2.9; B3.9.
**Walls:** 1.2, 1.14, 1.6.

### TG — Topological sub-unit gate
**Status.** Anchored cubic trace = winding; an integral nonnegative residual below one vanishes; neither the residual sign nor the sub-unit bound is derived.
**(a)** W2, W4.
**(b)** B1.6.
**Walls:** 1.2, 14.3, 14.8.

### HF — Positive Hodge form on arithmetic cohomology
**Status.** Prime-blind and odd receivers; the distinct-right-zero index `D_idx` is even when finite and RH ⇔ `D_idx < 2`; one-prime Lefschetz receivers; symmetric-square spectra are the sign at one prime; correspondence surface with free square law and budget. Counting (§1.5): section count, effectivity, naive and convex heights each RH. Two forms (§1.1): `Re W = D − Δ`; RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ one-shift similitude; `D` is the logarithmic Sobolev norm at each aperture, computed with its depth moments by polynomial theta prefixes, which also detect zeros locally; `W` has finite negative index. Field (§1.3): `(ζ′/ζ)²` computes the transverse field; every off-line zero has a terminal with positive field and an outward reserve [L/S].
**(a)** W2, W4; W5; W7(xii), W7(xiv), W7(xvi); W14; W18.
**(b)** B1.3; B1.7 (`D_idx < 2`); B1.9; B1.11; B1.14; B2.2; B3.10; B3.33; B3.35; B3.37; B3.38.
**Walls:** 1.3, 1.4, 1.16, 1.17, 1.21, 3.13, 3.20, 3.22, 14.2, 14.4, 14.18, 14.21, 14.24, 14.26.

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
**Status.** The nonnegative global cap vanishes iff RH; collision masses even; Hermite barrier, optimal heat and large-height repair proved.
**(a)** W7(iii); W2.
**(b)** B1.6; B1.5.
**Walls:** 1.2, 1.14, 3.8.

### LI — Paired Li and prime–Gamma balances
**Status.** RH ⇔ subexponential lower floors at every positive rate; off-line reciprocal-depth rates `≤ 1/431`; currency is reciprocal depth.
**(a)** W2/W5.
**(b)** B1.7.
**Walls:** 1.5, 3.8.

### SZ — Suzuki screw and shifted-kernel limits
**Status.** Compact-`L²` first variation = extended Weil energy; joint limits; RH ⇔ nonnegative first variation on RH-complete tent families.
**(a)** W3/W4.
**(b)** B1.3.
**Walls:** 1.3, 3.3, 3.6.

### PM — Physical-model Haar approximation (FZZ-P)
**Status.** Cofinal admission and Haar approximation RH-equivalent; RH ⇔ admission at every damping ⇔ positive gauge mass of every escape state. Energy-rate law in both directions. Escape (§1.10): Abel atoms of `ζ` are its dominant zeros; capacity, endpoint and shadow laws; infinite-height escape when residues are non-summable, the abscissa is unattained or visible orders are unbounded. Escape forms are collided Cauchy forms; centred divisor prefix = short sawtooth + actual long-modulus quadrature, with bounded pronic energy of the square-root head [L].
**(a)** W3/W4; W12.
**(b)** B1.2; B3.2; B3.3; B3.11; B3.16.
**Walls:** 1.8–1.10, 3.7, 3.12, 3.15.

### JAS — Joint ancestry
**Status.** Positive level-one budget ⇔ half-plane bound `< 1/2`; half-power endpoint is RH; Gamma–theta source admitted at all finite supports; unconditional positivity reaches a growing logarithmic prime budget.
**(a)** W2–W4.
**(b)** B2.1; B1.1.
**Walls:** 1.0, 1.1, 3.4.

### CTF — Chronological tail and Báez–Duarte approximation
**Status.** Residual = `(1 − readout)² + centred energy`; RH ⇔ both small; floor `κ/log N` exact.
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
**Status.** Strong, local and cutoff-uniform positive-mass recurrence each RH-equivalent; recurrence exactly at non-zeros; sharp threshold on zero-free discs.
**(a)** W3/W4.
**(b)** B1.7.
**Walls:** 1.2, 3.2.

### EWU — Even pole-weight uniqueness
**Status.** Blind minima attained and antitone, nonnegative at every aperture ⇔ RH; high-window positivity; full-cone source selection; finite-level existence ⇔ RH; full/even floor `1/5000` through `181/500` [S], shared by every weight with `w(2) = log 2`.
**(a)** W2–W5.
**(b)** B1.3.
**Walls:** 1.3, 1.4, 3.3.

### GTA — Transverse Schur charge
**Status.** Uniform quartic Schur decay RH-equivalent; an off-line zero forces a late positive charge floor.
**(a)** W2.
**(b)** B1.5.
**Walls:** 1.6, 3.2.

### OWU — Odd Weil-weight uniqueness
**Status.** Odd positivity RH-equivalent; light-cone variation positive; odd `181/500` window is the first certificate reading a prime; the Liouville twin there is a height twist of `ζ` plus corrections, separated by an odd witness [S]; at `23/40`, where the `{2,3}`-flip is not a height twist, a witness has `W_ζ > ‖F‖²/25`, `W_λ < −(3/10)‖F‖²` [S]. Multi-prime repulsion. The companion-forcing certificate and the conductor horizon have no common aperture at any height [L]; the outward-field reserve is a second zero-side detector at the same ordinates (§1.3).
**(a)** W2–W5; W13; W15; W17.
**(b)** B1.3; B3.26; B3.32; B3.36; B3.38.
**Walls:** 1.3, 1.18, 1.21, 3.4, 3.19.

### PBM — Regularized prime/log-ζ abscissa
**Status.** Half-plane bound at `α` ⇔ convergence on `Re s > 1/2 + α`; RH is `α = 0`; raw positive series diverge at every `Re s < 1`.
**(a)** W4.
**(b)** B2.1; B1.1.
**Walls:** 1.0, 1.1.

### RB — Robin/Nicolas divisor-sum criterion
**Status.** Eventual Robin ⇔ Robin on colossally abundant numbers; counterexamples need growing lcm cores and small moving valuation defects.
**(a)** W2.
**(b)** B1.7.
**Walls:** 1.1, 1.6.

### SRT — Prime-side one-parameter lag localization
**Status.** One fixed-width late-lag family decides RH; smooth detector at aperture `Cδ^{−2}(4 + |γ|)²`; single-height phase-selective law; eventual all-height saving refuted (Kronecker peaks); one-prime and two-prime Lefschetz receivers are the strip. The detector twisted to its ordinate is the odd sector of `σ_γ`; conductor-horizon positivity; forcing half; the forcing gap is a theorem at every height.
**(a)** W3/W4; W6; W7(ii); W15; W18.
**(b)** B1.4; B1.1; B1.3; B1.9; B3.20; B3.32; B3.36; B3.38.
**Walls:** 1.17, 1.21, 3.1, 3.2, 3.14, 3.19.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation to `Ke^r e^{−c√r}`; Schur payment to a finite head; exact shared-budget descent; joint signed `2, 3` payment at `r = 23/40` with `1/62` margin. The linear diagonal reserve cancels on the polar-neutral hyperplane; log-cell correlations = divisibility spine + bounded Euclidean remainder. The full-form `181/500` separation shows finite-lattice gauge conjugacy does not extend to the complete form [S]. Raw continuum prime towers have negative edge energy of order `e^A` [S]; the pole-neutralized full form is not covered.
**(a)** W2/W5.
**(b)** B1.3; B3.8.
**Walls:** 1.3, 3.4, 3.21.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; non-localizing positivity; Lefschetz receivers at one and two primes; Weil's layers (§1.4); faithful degree needs RH + simple zeros.
- Counting (§1.5): six currencies; polar box node twist destroys RI; Jacobi–Hurwitz dichotomy [S].
- One-variable systems and deformations (§1.9): κ = 1 class `ℝ^× · ζ`; contraction and collision calculus closed; polar-configuration cone classified; coupled class not rigid; per-ordinate equivalences of positive rigidity, positive chirality and rational/positive central ceilings; critical transfer and conservation; strong multiplicity one below the square-root deficit; quantization of the surplus residue as an even central drop `≤ 2 ord ξ`; transfer of an assumed ceiling to entire factors; `ζ^d` rigidity and boundary capacity.
- Two forms (§1.1) and the field (§1.3): `W = D − Δ`; `D` positive, faithful, computed, the log-Sobolev norm; Hecke invariant iff RH; `Λ ⋆ Λ` computes the transverse field.
- Census (§1.11): `3/4` of the zero copies within `4/log T`; `4/5` of the ordinates critical.
**(a)** W1; W7(xi), W7(xii), W7(xvi), W7(xvii); W11; W12; W19.
**(b)** B1.6; B1.8; B1.9; B1.11; B1.12; B1.14; B3.18; B3.28; B3.33; B3.34; B3.35; B3.37; B2.5.
**Walls:** 1.3, 1.15, 1.16, 1.17, 1.21, 3.8, 3.14, 3.18, 14.4, 14.8, 14.10–14.26.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6. Thirteen theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- multiplicative correspondences act hyperbolically at every off-line pair; elliptic localization in correspondence-closed carriers is resonance; the only reflection-compatible affine localizer is `σ_γ`, whose even sector cannot force and whose odd-sector certificate is separated from the conductor horizon at every height;
- positivity on nonnegative tests is shared by every dominated twin;
- finite multiplicative certificates are capped by growth input; completed and coupled systems reach the boundary, the `1/log T` collar and the classical local count;
- a mechanism must separate `ζ` from the relaxation models, from `W_β`-deformed members of the coupled class, and from the Liouville and `{2,3}`-flipped twins (which unconditional positivity of `ζ` already separates at `181/500` and `23/40` [S]);
- a mechanism built from multiplicative data proves its conclusion for the whole gauge orbit;
- kernel, coupled and escape-form positivity and `D` are collided and see no sign; `D` is computed, positive, faithful and the log-Sobolev norm, and its equivariance is RH;
- a section count, effectivity function, naive or convex height, one-sided count, fixed tensor loss or horizon torsion is the sign; Stepanov auxiliaries need a lattice spectrum;
- a counting polarization that is the same on every fibre is not selective; a large-sieve majorant inflates quadratically;
- positive one-variable constructions remove a complex quartet only against a real anchor and collide conjugates only ordinate by ordinate;
- positive deformations keep the off-line divisor; at zero-free ordinates the surplus residue is an even central drop bounded by `2 ord ξ`; changing the central order of an arithmetic member costs a square-root prime deficit;
- positivity of torsion energies is lost exactly in the diagonal renormalization that produces Weil's prime kernel;
- zero-side reserves (the outward field, local zero detectors) detect an off-line zero; they supply no upper bound that excludes it.

| Candidate | Present construction / exact boundary | (a) | (b) |
|---|---|---|---|
| **APF** adelic/Fourier | Countable Fourier data reconstruct the cycle off a null set; Fredholm trace receiver exact. | W1–W3 | Annihilation of the reconstructed off-line component (B1.6). |
| **BSH** framed-mate curvature | Curvature detects line support; finite cutoffs trace-blind. | W1, W2 | Pre-divisor section with curvature sign (B1.6). |
| **CDC** constitutive dagger | Calibrated confluence ⇔ `Re s = 1/2`. | W1, W2 | A descending source potential (B1.6). |
| **DR** dyadic roots | Local cusp roots; finite monodromy; capped atlas. | W2, W3 | Global compatible roots, i.e. the regularized abscissa (B2.1/B1.1). |
| **EGC** Euler/Gamma contour | Fixed-line correction; enclosed-pole cancellation; centred exterior decay. | W2–W4 | Outer expanding-contour sign (B1.6). |
| **EWJ** Euler–Wold jets | Exact finite jets; compact-character locus. | W1, W2 | Norm exhaustion into a receiver (B1.6). |
| **FEL** free-energy contrast | BSY integral = sum over off-line zeros of `log\|ρ/(1−ρ)\|`, zero on critical zeros. | W2 | Cofinal contrast equality (B1.7); the contrast is a depth capacity like `Δ`. |
| **HJ** pre-divisor reflection | Residual = SEC charge = two-grid HCF sign. | W1, W2 | Global stabilization weld (B1.6). |
| **IRK** inverse rotation kernel | Completed relation invertible off the line, no left inverse on it. | W1, W2 | Source lift with integral count (B1.6); an integral count is the sign (B1.9). |
| **MSC** squarefree Hilbert source | Divisor-preserving `L²` source; critical logarithmic discrepancy in `L²`. | W2, W3 | Positive Sonin/Weil landing (B1.6). |
| **PCS** chronological carrier | Shift defect retained; strong finite-prime convergence with norm gap. | W2 | Wall annihilation with forward mode (B1.6). |
| **PTR** photonic ports | Finite lossless stacks real-rooted; Ξ-limit ⇔ RH; prime-log stacks cannot converge to Ξ. | W2 | Prime-faithful nonlocal port (B1.6). |
| **RFHM** survival information | Full finite-support admission; energy probabilities erase grade. | W2 | Phase-sensitive invariant with a source law (B1.6). |
| **SC** scattering completion | Wall recovery ⇔ wall vector = 0; canonical polarization wall-singular. | W2, W3 | Cross-fibre index (B1.6). |
| **SEC** time-one Fock | Fock boundedness ⇔ `Re ρ = 1/2`. | W1, W2 | Pre-divisor compactness (B1.6). |
| **W1C** Ising law convergence | Centred real compact-uniform convergence suffices. | W2, W4 | Arithmetic couplings with a centred limit (B1.6). |
| **WBF** genealogy Gram | Completion ⇔ square-summable coefficients. | W2 | Arithmetic certificate stream (B1.6). |
| **PW-B** two-response action | Action indexed by `XiZeroCopy`. | W2 | Pre-divisor reformulation; zero-damping landing (B1.6, B1.2). |

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic, with exact depth laws; they detect, they do not force. FEL's contrast and the defect `Δ` are nonnegative depth capacities vanishing exactly on critical zeros; neither has an arithmetic upper bound. ConjugateDiagonalGeometry computes zero-indexed depth functionals from `ξ` and polynomially many theta values, and detects zeros locally; the outward field computes a positive reserve at a terminal. Both remove the circularity of zero-indexed definitions, not the missing bound.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; bands ⇔ `Θ < 1`; half-damping transition; every power improvement ⇔ a fixed strip. | W4 | B2.1; B1.2 |
| **ADR / AOT** cofactor modules | Record minima, contraction calculus, eigencharacter moduli, translated-zero escape rows, Mellin residues pin power-like solutions to translated zeros, two-factor pole trace, tied exponents of twisted one-prime laws. | — | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates, long moduli | §1.11; long-modulus decomposition, integrable producer, integer sampling and bounded square-root head energy. | W7(ii) | B3.6, B3.1; B1.2 |
| **ACS / Meyer** | §1.4, §1.11, §1.12; Lefschetz sequences grow at the zero width; blindness of a fixed tower needs a separating folded spectrum. | — | B1.6, B1.8 |
| **ACP** correspondence positivity | Normalized graphs, budget, local types, resonance, section and Stepanov counts, symmetric-square spectra, sparse annihilators, contraction and collision calculus, escape alternative and criterion, Abel atoms, budget currencies in both directions for the prime error, successor defect in `H²` (§1.6, §1.10). | W7(xv), W9, W11 | B1.13, B3.2, B3.26, B3.28, B3.30; B1.9 |
| **OF** outward field / `Λ ⋆ Λ` localization (ACP) | §1.3: quadratic terminals, outward ray with reserve [L]; terminal field and witness [S]; the Rankin–Selberg square computes the field; logarithmic zero bands. | W12, W18 | B1.14, B3.28, B3.36, B3.38 |
| **PL** arithmetic polarization | Polarization law, elliptic localizers, twisted sectors, conductor horizon, forcing half, collision law, rate neutrality, oscillatory capacity; `D` faithful, coercive, the log-Sobolev norm, a polarization with similitudes iff RH; Gårding; finite negative index; local Weyl law; depth profile; polar-configuration cone; selectivity battery. | W5, W7(xii), W7(xiv) | B1.11, B3.32, B3.33 |
| **CDG** conjugate-diagonal geometry | §1.1: `ξ` current, finite and polynomial theta metrics, local zero detector, depth distribution, two-scale variance law, conductor–forcing gap, fixed-strip source cutoff. | W14 | B3.33, B3.36 |
| **AE** arithmetic effectivity | §1.4–§1.7: effectivity calculus, Tate, naive heights are traces, convex heights, polar box, torsion potential and intersections, renormalized torsion energy, completion law, Burgess and least non-residue, Stepanov method over `ℤ`, hyperelliptic calibration. | W16 | B1.9, B3.30, B3.35, B3.37 |
| **BGG** biarithmetic gauge geometry | §1.8, §1.9: gauge torus, successor holonomy, Catalan and multi-prime repulsion; deformation principle, Abel–Gram law, coupled-class equivalences, strong multiplicity one, square-root deficit law, critical conservation, quantization of the surplus, ceiling transfer to factors, `ζ^d` boundary capacity, polar-neutral collapse, Ramanujan torsion. | W7(xi), W12 | B1.12, B3.26, B3.34 |
| **SP** selective positivity and thresholds [S] | §1.5, §1.8: `181/500` full floor and twin separation, `23/40` two-prime separation, continuum tower obstruction, escaped Möbius pairing law, parity-lobe obstruction, Serre-dual box cohomology, Jacobi–Hurwitz heights. | W5, W12, W13, W17 | B3.8, B3.26, B3.35 |
| **APD** positive duality | §1.12; Hecke states positive definite iff `s ≥ 1/2`; Kakutani wall; Bost–Connes temperature = Hecke exponent. | — | B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, decay-exponent mass law, Beurling threshold, families, Siegel exception; interior capped. | W10 | — (complete below RH strength) |
| **SBWF** strip Bochner–Weil forcing | Completed-system collars; κ = 1 class; `5d < 9κ`; positive-definite sections are completely monotone. | — | B3.18 |
| **ACG** correlation geometry | Gauge invariance, a.e. laws, comeager-null exceptions, prime pole, archimedean-line threshold, charged boundaries at `1/4`, finite gauge subgroups, loss law, gauge-mass criterion. | W9 | B1.2, B3.24 |
| **AKT** Künneth theory | Product receivers see depth only through total length; Künneth positivity = point-count positivity. | W9 | — |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; base theta `h⁰`. | W4 | B3.10; B2.2 |
| **ALDG** local divisor heat | Hermite barrier, optimal heat, residual region model complete. | W7(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering, observation | Endpoints; high-zero tail; filtered deficit; closed-cycle recovery. | W6, W7(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3`, lag-2 `1/4` floors exact. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure. | — | B3.3 |
| **TTPC** coalescent pairs and census | `N₀* ≥ (29/36 − ε)N − surplus`; parity-blind dispersion cannot give `β < 5/36` at `λ = 4/3` [S]; census of §1.11 [L]. | W19 | B2.5, B2.7, B3.24 |
| **HTG** tools | Fejér–Riesz; Bochner uniqueness for Laplace weights; lattice Fourier vanishing ⇒ absolute continuity; planar log-square bounds; quadratic ascent; logarithmic windows quadratically sparse. | — | — |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density on windows `≥ U^{99/100}`; Heath-Brown; KKL; dlVP, Littlewood, VK; smoothed Landau formula over all zeros; Cramér mean square under RH; the two-thirds certificate (`Zeta23`). | W6, W10, W15 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - What computes `D`: the current `Δ log|ξ|` and polynomially many integer theta values, with multiplicities, without zero indexing; the same readings detect zeros locally.
  - Whether `D` is a norm, and which: faithful, coercive, and at each aperture equivalent to the logarithmic Sobolev norm.
  - Whether `W` can have infinitely many negative directions at one aperture: no; fewer than `2AT₀K/π`.
  - The forcing gap: the existing companion certificate and the conductor horizon are disjoint at every height.
  - Whether an off-line zero leaves an arithmetic trace at its own height: yes, a terminal with positive transverse field and an outward reserve `≥ c·a·log γ`; detection only.
  - Whether the prime-error budget is weaker than RH: no, it is equivalent; with the Abel slope at the genus it is RH with simple zeros.
  - The edge problem at `181/500` and the first non-archimedean twin at `23/40`: both twins fail on explicit witnesses on which `ζ` is positive [S].
  - The energy-rate law at the zero abscissa, both directions; escape when residues are non-summable, the abscissa unattained or orders unbounded: infinite height.
  - Positive and rational deformations of the coupled carrier: rigid exactly at zero-free ordinates; their central ceilings and positive chirality are RH ordinate by ordinate; the surplus residue is an even central drop.
  - Budget currencies over `𝔽_q`; whether Weil's prime kernel is a limit of positive forms (yes, after a divergent diagonal renormalization); whether kernel counts supply naive heights (no, complex fake).
  - What fraction of the zeros the unconditional statistics already place near the line: `3/4` of the copies within `4/log T`, `4/5` of the ordinates on it.
  - Earlier settled items: section counts, effectivity, naive heights, one-sided counts are the sign; elliptic localization in correspondence-closed carriers is resonance; coupled-class two-sided rigidity fails at critical-zero ordinates; contraction and collision calculus; theta `h⁰` does not extend; multiplicative lattice forms are blind; the first gauge charge is a height twist; theorem of the square and budget free; positivity beyond isotropy only without localization; κ = 1 class; Lefschetz receivers at one and two primes; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false; summation-scope "defects" never existed.
- **Excluded mechanisms** (in addition to the [killed-routes catalogue](../rh-killed-routes.md)):
  - collided coercivity, sampling, log-Sobolev equivalence or finite negative index offered as Weil's sign;
  - the computed `D` (current, theta or local readings) offered as a bound on its own Hecke defect;
  - the companion-forcing certificate spliced with the conductor horizon;
  - the outward-field witness or a local zero detector offered as exclusion;
  - positive or rational deformations of `ζ_γ`, or the surplus quantization, offered as forcing;
  - budget currencies, convex heights or Farey sums offered as inputs weaker than the sign;
  - large-sieve or Cauchy–Schwarz majorants offered as Riemann–Roch sections;
  - torsion-energy positivity at `r < 1` offered as Weil positivity;
  - raw continuum prime towers as sub-half exponential floors;
  - completion offered as a mechanism at the arithmetic point; sparse annihilators offered as Stepanov auxiliaries over `ℤ`;
  - zero statistics (census, short-window averages, almost-every-ordinate positivity) offered as exclusion of an individual zero.
- **Substitutions that do not hold.** Computed for bounded; detected for excluded; collided for Rosati; positive for equivariant; equivariant for positive; norm for sign; sampling for positivity; finite index for zero index; resonance for localization; twist for gauge charge beyond the first prime; soft polarization for selective polarization; positive deformation for arbitrary member; rational ceiling for full ceiling; one-sided ceiling for two-sided rigidity; classification of escape for its exclusion; budget for sign; regularized limit for limit of positivity; finite-level count for the arithmetic point; finite window separation for all-aperture selection; averages and proportions for individual zeros; nonnegative tests for the full cone; zero-indexed objects for pre-divisor constructions; reserve for contradiction.
