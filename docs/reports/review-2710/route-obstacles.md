# Hard mathematical obstacles: routes, candidates and supporting programmes

Status: 2026-10-27, corpus `80f251476` with the working tree of that day. Scope: the 31 live routes, 17 standalone candidates, PW-B and the supporting programmes that change their prospects. Companions: [summary, next questions and new-field assessment](obstacles-summary.md), [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md).

## Evidence and classification

**Sources.** Route inventory: the [frontier map](../rh-current-frontier-map.md) and the [killed-routes catalogue](../rh-killed-routes.md). Statuses were researched with `scripts/formal_tools.py research` and by reading module docstrings and theorem statements in `formal/`; the record is `logs/review-2710-research-log.md`. Nothing was compiled. Labels: `[L]` integrated source, `[S]` working or unintegrated source (modified or untracked in the working tree, or marked so in the frontier map), `[P]` paper proof, `[R]` reading or model calculation of this review, not a theorem.

**Obstacle classes.**

- **(a) Just work.** Known mathematics suffices: finite certificates, certified computations, premise checks, transport of proved estimates, corollary assembly, classical ranges of known estimates. IDs `W1`–`W17`, defined in the [summary](obstacles-summary.md#1-just-work). A just-work item may have an unknown outcome; what is known is the method.
- **(b) Open mathematics.** No known solution. Three tiers, defined in the [summary](obstacles-summary.md#2-open-mathematical-obstacles):
  - `B1.*`: RH-strength closing statements, each equivalent to RH or stronger;
  - `B2.*`: classical open problems weaker than RH;
  - `B3.*`: open problems isolated by this research, not known to be RH-equivalent.

**Notation.** `Δ = sup_ρ |Re ρ − 1/2|` (the zero width), `Θ = 1/2 + Δ`. A receiver bounded at rate `σ < 1/2` gives `Δ ≤ σ` (quasi-RH); RH is rate zero. `κ` is the pole order at `s = 1`, `d` the archimedean degree. For a zero `ρ`, `ρ* = 1 − ρ̄` is its reflection; `δ = Re ρ − 1/2` its depth. `f̂(s) = ∫ f(u) e^{(s−1/2)u} du`. `W` is Weil's form; `D(f) = Σ_ρ m_ρ |f̂(ρ)|²` the **collided form**; `Δ(f) = Σ_ρ (m_ρ/2)|f̂(ρ) − f̂(ρ*)|²` the **off-line defect**; `T_L` translation by `L` (the Hecke action of the dilation `e^L`); `E_f(L) = D(T_L f) + D(T_{−L} f) − 2D(f)` the **Hecke defect** of `D`. `σ_γ(s) = 1 + 2iγ − s` is the elliptic localizer at ordinate `γ`. `ζ_γ(s) = ζ(s)²ζ(s + iγ)ζ(s − iγ)` is the height-coupled carrier, `Λ_γ` its completion, and `HeightCoupledSystem 2 1 1 γ` its class. `ν_N` is the torsion measure (roots of unity of order `≤ N`).

## 1. Facts that fix the present frontier

### 1.1 Two forms on the test space, and how far each is computed

| Form | Positive? | Hecke equivariant? | Computed by |
|---|---|---|---|
| Weil's form `W` | iff RH; finitely many negative directions at every aperture [L] | yes, for every zero configuration [L] | the explicit formula (primes, Gamma, poles) |
| Collided form `D` | yes; faithful; coercive at every aperture [L] | iff RH; a Hecke translation is a similitude of `D` iff RH [L] | the current `Δ log|ξ|` and finite integer theta prefixes, without zero indexing [L] |

- **Capacity identity** [L]. `Re W = D − Δ` on every compact `C²` test; RH iff `W = D` iff `D` is Hecke invariant iff some `T_L` (`L ≠ 0`) is a similitude of `D` (`riemannHypothesis_iff_W_eq_collided`, `riemannHypothesis_iff_collided_hecke_invariant`, `hecke_similitude_iff`).
- **`D` is a norm** [L]. `D(f) = 0` only for `f = 0` (`collidedForm_eq_zero_iff`); `D ≥ ‖f‖²/5000` on `[−3/10, 3/10]`; for every aperture `A` there is `c_A > 0` with `c_A ‖f‖² ≤ D(f)` (`exists_collidedForm_coercive`, non-effective): the zeros with multiplicity are a sampling set for every Paley–Wiener space. The Gårding inequality `Re W ≥ 2π‖f‖² − K ∫_{−T₀}^{T₀}|f̂|²` holds for `W` and hence for `D`. Upper bound `D ≤ C ∫|f̂|² log(|σ| + 4)` per aperture [S] (`collidedForm_le_log`); the matching lower bound is not declared. Local Weyl law: `(1 − η)‖f‖² log|γ| ≤ D(e^{−iγu}f) ≤ K_f log|γ|` as `|γ| → ∞` [L].
- **`D` is computed** [L] (ConjugateDiagonalGeometry). The distributional Laplacian of `log|ξ|` evaluates compact nonholomorphic test squares; a canonical smooth exhaustion recovers `D` and every depth-kernel moment `Σ m_ρ |f̂(ρ)|² k(L, δ_ρ)^j`, `k(L, d) = 2cosh(2dL) − 2`, for the actual divisor (`XiSourceCurrent`). Finite integer theta prefixes recover the same moments uniformly for `sourceTestSize f ≤ 1`, support radius `a`, `|τ| ≤ n/2`, `a + j|L| ≤ 2 log(n + 1)`, with error `B exp(−n⁴ + 68n² + 66) + O(reference tail)` after normalization by `4^j` (`exists_finiteThetaSource_aperture_error_bound`); the readings still use continuous integrals, not finite quadrature. The computation evaluates the Hecke defect; it does not bound it.
- **Depth geometry of `D`** [L]. `L ↦ D(T_L f)` is the two-sided Laplace transform of the depth measure `Σ m_ρ|f̂(ρ)|² δ_{2δ_ρ}`, and `(1/L) log D(T_L f) → 2a_f`, `a_f` the largest depth the test sees (`tendsto_log_depthProfile_div`). Two scales determine the depth dispersion: `D(E(2L) − 4E(L)) − E(L)² ≥ 0`, with equality at `L ≠ 0` iff all seen zeros have one absolute depth (`TwoScaleDepthRigidity`).
- **Reading [R].** Since `W` is equivariant and `Re W = D − Δ`, the Hecke defect of `D` equals the Hecke defect of `Δ`: `E_D(L) = E_Δ(L)`. Over `𝔽_q`, `D` is the Hermitian trace and `W` the Rosati trace on `H¹`; purity is their coincidence (`re_rosatiForm_eq_collided_sub_defect`, `collided_frob_invariant_iff_unitary` [L]).

Reading [R]: what computes `D` is answered — the zero divisor's Riesz measure, read through `ξ` and theta sums. What remains is an inequality: no computation so far bounds `E_f(L)` above by anything that vanishes.

### 1.2 Local type, elliptic localizers and the forcing gap

At an off-line pair the local form is `2 Re(u v̄)` in `(f̂(ρ), f̂(ρ*))`, signature `(1, 1)`.

| Type | Action on the fibre | Correspondences | What positivity of a cyclic span forces |
|---|---|---|---|
| Hyperbolic | boost `diag(β, β̄⁻¹)`, `\|β\| ≠ 1` | Hecke operators, archimedean flow, gauge twists, exactly at off-line pairs | isotropy |
| Elliptic | rotation or swap | Hecke operators on the line; resonant symmetric dilations; `σ_γ` | only `Re(u v̄) ≥ 0` |
| Unipotent | identity on polar parts | the additive successor | nothing |

- **Resonance** [L]. A symmetric dilation by `a > 1` is elliptic at an off-line point of ordinate `γ` iff `γ log a ∈ πℤ`; within correspondence-closed carriers elliptic localization is resonance, at most one prime.
- **Elliptic localizers** [L]. The stabilizer of an off-line pair among reflection-compatible affine maps is `{id, σ_γ}`; `σ_γ` is the functional equation conjugated by the flow. Even sector `+2|G(ρ)|²` (cannot force), odd sector `−2|G(ρ)|²`. Dihedral dilemma: Hecke + `σ_γ` stability is blindness.
- **Conductor horizon** [L]. Twisted positivity `Re W_ζ(e^{−iγu}f) ≥ 0` for every `C²` test of aperture `a` once `C + (4 + ε)e^a + 2 ≤ log(1 + |γ|/8)` (with tail conditions); source-blind there. Beyond it, no eventual-in-height positivity holds for all tests (Kronecker peaks).
- **Forcing half** [L]. One sign of `W` on the twisted odd detector at the ordinate of a candidate zero, a local count `≤ A log(|t| + 3)` and depth dominance force an off-line companion within ordinate distance `R`.
- **The forcing gap is a theorem** [L] (`TheConductorForcingGap`). The detector's squared signal is at most `N² e^{2δa}/2`; a successful certificate needs `768 A log(|γ| + 3) < e^{2δa}`; this cannot coexist with the conductor horizon for `0 ≤ δ ≤ 1/2`, at every height, with no asymptotic threshold.
- **Reading [R].** The conductor `log γ` of the gap is the local Weyl law of `D`: any test at height `γ` pays the local zero density. Beyond the horizon the twisted detector's prime side is a Dirichlet polynomial of length `e^{2a} = (log γ)^{O(1)}` evaluated at the zero's ordinate; its sign is governed by how well `γ log p` (`p ≤ e^{2a}`) aligns modulo `2π`, the same Diophantine quantity that the multi-prime repulsion law of §1.7 bounds near the Liouville vacuum.

### 1.3 Weil's argument over `ℤ`, layer by layer

| Layer | Over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, `FF′ = q` | exact | no: hold on the golden datum `1 − 5X + 5X²` |
| L2 Theorem of the square | graph map quadratic | free for normalized graphs; Tate's limit makes bounded-error square laws exact | no |
| L3 Budget | `δ(Δ, Δ) = 2g` | free: similitude law; Frobenius always a similitude of ratio one | no |
| L4 Kernel counts | `#ker ≥ 0`; exterior counts | determinant and coupled counts are collided (modulus squares); the complex fake has every kernel count `≥ 0` and integral Rosati value `−2304` at `F² + 16` (`complexFake_kernelCounts_nonneg_no_naiveHeight`) | collided positivity only |
| L5 Rosati positivity | polarization | `⇔` orbit Hodge index `⇔` RH; similitude + anisotropic eigenvector `⇒` unit modulus | missing |
| L5′ Counting origin | RR on `C × C`; Stepanov count + `\|τ\|² = q` | section count, effectivity function, naive height, convex height, one-sided count, horizon torsion: each RH; naive heights are traces, not kernel orders | each is RH |
| L6 Base | fixed tensor loss | fixed tensor loss `⇔` RH; twists rate neutral | missing |

**Calibration over `𝔽_q`** [L]. RH for every odd-degree squarefree hyperelliptic curve over every finite field of odd characteristic is proved by counting: Stepanov's auxiliary-section count, the Gauss-sum modulus and descent from the splitting field (`riemannHypothesis_oddHyperelliptic`); Hasse for elliptic curves follows. On these curves every Frobenius window has an effectivity function and the integral Rosati form has a naive height, unconditionally (`TheHyperellipticCalibration`). Over `𝔽_q` the sign is carried by two cardinalities.

**Completion law** [L]. At each finite level, square-root cancellation of complete sums is a count (`|τ|² = q`), and completion transports it to incomplete sums with a logarithmic loss (Pólya–Vinogradov, `norm_sum_range_le_polyaVinogradov`). Burgess's moment, energy and inequality are proved at finite level [S]. The arithmetic point (`Σ μ(n)`, `ψ(x) − x`) has no period: no finite group computes its sums.

### 1.4 Counting is the sign

- **Section counts and effectivity** [L]. A count with RR and Bézout, or an effectivity function (Riemann inequality, subquadratic degree-zero growth), exists iff the Hodge index; over `ℤ` iff RH. An off-line zero is an abundant class.
- **Six currencies** [L/S]. An effectivity function, no abundant class, a naive height for every integral Rosati form, a fixed tensor loss, horizon torsion at `√N` precision (`riemannHypothesis_effectivity_tfae`) and a midpoint-convex height at bounded distance from every integral Rosati form (`riemannHypothesis_iff_forall_exists_convexHeight`) are each RH. Log-counts of nonnegative weights are convex for free on every datum: convexity, like nonnegativity of cardinalities, is soft.
- **The polar box** [L]. The box class `√N·A` has `χ = N`; its count is an effectivity function iff the Hodge index; subtracting the prime-power node conditions gives `N − ψ(N)` and destroys the Riemann inequality on every polar surface (`not_riemannInequality_nodeBoxCount`).
- **Torsion potential** [L]. `Λ(n) = Σ_{μ primitive} log|1 − μ|` (product formula in `ℚ(ζ_n)`); `ψ(N) = Σ_{n ≤ N} Σ_{(k,n)=1} log(2 sin(πk/n))`; RH iff this Farey sum is `N + O(√N log²N)` (`riemannHypothesis_iff_fareySum`). The first Fourier coefficient of the torsion measure is `M(N)`; RH iff `ν̂_N(1) = O(N^{1/2+δ})` for every `δ > 0`. `log P_N(q) = Σ_{d ≤ N} M(⌊N/d⌋) log[d]_q` (q-deformation of the horizon period).
- **Large-sieve sections** [S] (SelectivePositivity). Every finite packet of shifted Jacobi–Hurwitz theta log-heights is a Tate quadratic plus `O(1)`; either it is blind on the degree-zero hyperplane or it inflates quadratically along some degree-zero cycle; an unsigned large-sieve majorant forces inflation `q_P(z) ≥ |z·z|/2`. Asymptotic Riemann inequality plus subquadratic growth still forces the Hodge index; short-cycle subquadratic heights exist at `r ≤ (log 2 + 1/50)/2`; RH iff one exists globally. Sign-free Serre-dual box cohomology reproduces `max(0, χ)` on unitary curves and fails Riemann–Roch on the golden datum; section supply beyond the large-sieve diagonal is a zero-free strip.
- **Theta surface and lattice counts** [L]. The theta surface has a counting polarization `πJ²/t`, the same on every fibre; lattice counts on the square give `ζ(s₁ + s₂)` or `ζ(s₁)ζ(s₂)` (boundary or determinant positivity).

### 1.5 Budget currencies

A **budget** is a linear log-energy of a row: `∫_0^L e^{−u} g(⌊e^u⌋)² du ≤ S L + B`.

| Row | Over `ℤ` | Over `𝔽_q` |
|---|---|---|
| Prime error `ψ(n) − n` | a budget forces RH and `S ≥ 2 + γ_E − log 4π` (the archimedean genus `Σ 1/(ρ(1 − ρ))`); unconditionally the log-slope is `≥ Σ_{Re ρ = 1/2} m_ρ²/|ρ|²` on every finite set; an Abel slope tending to the genus forces RH and simple zeros [L] | a budget is purity; slope `Σ_β mult(β)² ≥ 2g`, equality iff simple spectrum [L] |
| Mertens `M(n)` | a budget forces RH, simple critical zeros and `Σ_ρ ‖1/(ρζ′(ρ))‖² ≤ S` [L] | a budget is purity with simple spectrum; slope = repulsion energy `Σ_i Π_{j≠i}|β_i − β_j|^{−2}`; genus one: strict Hasse `a² < 4q` [L] |
| Successor shift | `D_Λ(s)/s ∈ H²(Re s > 1/2)` with `‖·‖² = 2π Σ Λ(n)²/(n(n+1))`; the shifted prime error carries the same cost [L] | — |

Reading [R]: Cramér's constant `Σ m_ρ²/|ρ|²` is the arithmetic form of Weil's budget `2g`: the spectrum counted with squared multiplicities. The converse directions (RH ⇒ prime-error budget, Cramér; RH + simple + residue summability ⇒ Mertens budget) are classical or conditional and are not formalized; RH-conditional partial fractions of the symbol exist [S].

### 1.6 Torsion intersection theory

- **`Λ` is an intersection number** [L]. The archimedean intersection of the Galois orbits of primitive `m`-th and `n`-th roots of unity is `I(m, n) = φ(n)Λ(m/n)` if `n | m` (Apostol's resultant); `I(m, mt) = φ(m)Λ(t)`, the same for every `m` (Hecke law). The log-energy of `μ_a` against `μ_b` is `gcd(a, b) log lcm(a, b)`.
- **Weil's prime kernel is a renormalized positive energy** [L] (`weilPrimeKernel_renormalized_torsion_energy`). For `r < 1` the torsion energy `T_r(m, n) = Σ_k (r^k/k) c_m(k) c_n(k)` is a positive semidefinite Gram matrix of Ramanujan sums; its Schur product with the positive gcd twist `G(m, n) = gcd/φ(gcd)` stays positive; off the diagonal `G T_r/√(mn) → −Λ(n/m)(n/m)^{−1/2}`; on the diagonal it diverges like `−log(1 − r)` and after renormalization tends to minus the log-discriminant per point. The discrete prime form plus the log-discriminant diagonal is minus the renormalized limit of positive torsion energies: positivity is lost exactly in the divergent self-energy.
- **Reading [R].** At `r < 1` the torsion energy is positive; at `r = 1` it is Hecke equivariant (the intersection law) and computes the prime kernel. The two properties a polarization needs sit on one family and separate only at the diagonal — the analogue of the self-intersection of the diagonal in Weil's proof and of Arakelov's regularized adjunction.

### 1.7 The gauge principle

- **Orbits, not points** [L]. Multiplicative data determine a source up to its gauge orbit; for `μ` the half-power law holds Haar-a.e., fails at the Liouville twin and at `0` is RH; the prime source is typical at `0` except for its pole.
- **Finite lattice blindness** [L]. Every diagonal + ratio-shift + product-crossing lattice form is unitarily equivalent under a real sign gauge to the Euler form. The successor connection `conj χ_ω(n) χ_ω(n + 1)` is flat iff `ω(p) = 1` for `p ≤ N + 1` and reconstructs `ω(2), ω(3)` on `2 → 3 → 4`.
- **First gauge charge** [L]. On windows below `log 3` the Liouville twin is `ζ` twisted to height `π/log 2` plus Gamma and pole corrections; the twin is positive on odd tests with edge mass `≤ 1/1961` of the total.
- **The first windows separate** [S] (SelectivePositivity). At radius `181/500` an odd smooth test has `W_ζ ≥ ‖F‖²/1000` and `W_λ = W_{flip 2} < −‖F‖²/1000`; the full-sector floor of `ζ` is `1/5000` through `181/500`; a shifted pair `ζ(s − a)ζ(s + a)` is negative on an even test there. At radius `23/40` (atoms `2` and `3` read; the `{2,3}`-flip is not a height twist) an odd smooth test has `W_ζ > ‖F‖²/25` and `W_λ < −(3/10)‖F‖²`; the Liouville ground eigenvalue at `23/40` is `< −3/10`. An archimedean-free separator: the successor-square form `w(2)w(4)` is `−(log 2)²` at `λΛ` and `+8^σ(log 2)²` on every scale twist.
- **Repulsion** [L]. `(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50`; for `N` primes `Σ_j(1 + cos(γ log p_j)) ≥ γ² e^{−2τL}/(32Nτ²)`, `τ = (N(|γ|L/π + 1))^{1/(N−1)}` (Siegel's lemma); with enough primes the sum exceeds `exp(−|γ|^ε)` for large `|γ|` (`exists_primes_repulsion_ge_exp_neg_rpow`): an archimedean twist approaches the Liouville vacuum at most stretched-exponentially fast.
- **Worst twin; amplification** [L]. On nonnegative tests `Re W_Λ ≤ Re W_w` for `w ≤ Λ`. Gauge moments, family averages, products and relative powers lose linearly; twists are rate neutral.

### 1.8 Positive systems: one variable, polar configurations, deformations

- **Degree-one rigidity and contraction** [L]. `CompletedPositiveSystem 1 d = ℝ^× · ζ`; pole order pays inserted zeros; real off-line pairs contract at `Δκ = 0`; a complex quartet contracts only against a real anchor of twice the weight, and an anchored quartet forces `κ ≥ 3`; planting costs `Δκ ≥ 2`. Coupled completions vanish to even real order; no harmonic lift empties the deepest line (Fejér barrier); the global conjugate collision has no analytic carrier.
- **The positive cone of polar configurations** [L] (PL). Positivity of one vertical section at one abscissa is equivalent to nonnegativity of the scale weight `w(t) = Σ c(z)e^{Re z·t}cos(Im z·t)` and propagates to every section. The leading line carries a nonnegative almost-periodic sum (Bohr return); each lower line is nonnegative wherever all higher lines vanish (line hierarchy law). On a commensurable line positive configurations are Hermitian squares `|Q|²` (couplings, even collision): odd collision needs incommensurable ordinates on the leading line.
- **Deformation principle** [L] (BGG). If `Λ₀′/Λ₀ − Λ′/Λ = 𝓛ν + E` with `ν ≥ 0` on a real ray, the divisors agree right of the abscissa of `ν`, and a positive abscissa is a real zero of `Λ₀` (Landau–Wronskian). Divisor jumps across a line are Abel limits of `(σ − x₀)𝓛ν` and form an even positive-definite function (Abel–Gram); every jump is bounded by the real one.
- **The coupled class** [L]. `HeightCoupledSystem 2 1 1 γ` is not rigid at any critical-zero ordinate (outward splitting `W_β` is Bochner positive; inward collapse is not). Positive prime-mass deformations of `ζ_γ` keep every off-line zero and never raise the central order when `ξ` has no off-line zero at ordinate `γ`; then `|ord_{1/2+it}Λ_γ − ord_{1/2+it}Λ| ≤` central drop (critical transfer law), and at constant central order the deformation is trivial. Exact per-ordinate equivalences: positive prime-mass rigidity at `γ` iff `ξ` has no zero at ordinate `γ` (`positiveCoupledRigid_iff`); positive chirality at `γ`, the positive central ceiling and the rational central ceiling at `γ` each iff `ξ` has no off-line zero at ordinate `γ`; RH iff any of them holds at every `γ`. The full-class ceiling at `γ` implies the absence of off-line zeros at `γ`; its converse and full-class two-sided rigidity at zero-free ordinates are not proved.
- **Arithmetic members** [L]. For a member with `−F′/F = Σ b(n)n^{−s}`, `b ≥ 0`, and deficit `d = (b_γ − b)⁺`, `b_γ(n) = Λ(n)(2 + 2cos(γ log n))`: a central excess forces the deficit series to have abscissa `≥ 1/2` and `liminf_{σ↓1/2}(σ − 1/2)D(σ) ≥` excess; zero Abel residue of the deficit and no central drop force `F = Kζ_γ` (strong multiplicity one below the square-root deficit). For deformations of `ζ^d` in `CompletedPositiveSystem κ d`: `κ ≤ d` and a sub-half deficit force `κ = d`, `F = Kζ^d`, with no hypothesis on zeros; boundary capacity `2Σ_{t∈Z} ord_{1+it}Λ ≤ κ − d`. Critical conservation: the central drop pays every created critical zero twice [S].

### 1.9 Escape

- **Location and classification** [L]. At damping `ε` the receiver escapes iff zeros lie right of `1/2 + ε` (up to countably many `ε`); RH iff admission at every damping iff every escape state has positive gauge mass. Escape states of dominant configurations are phase kernels; their forms are collided Cauchy forms.
- **Energy-rate law** [L]. `E_ε(T) ≤ C_κ(T + 1)^κ` for every `κ > max(0, 2Θ − 2ε − 1)`, and an uncancelled zero forces growth beyond `κ < 2θ`.
- **Abel atoms of `ζ`** [L]. With the Abel weight, each dominant simple zero carries an atom of mass `π‖r_ρ‖²`, `r_ρ = ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))`; effective orders are visible translated-zero orders. Capacity law: the escape rate dominates the residue mass. Endpoint law: at the zero abscissa, `E_ε(T) ≤ C(T + 1)^{2θ}` forces `C ≥ Σ‖r_ρ‖²/(2θ)`. Shadow law: at `ε = Re ρ − 1/2` the boundary receiver's log-slope is at least `Σ‖ζ(1/2 + i Im ρ)/(ζ′(ρ)(1/2 + i Im ρ))‖²`.
- **Infinite height** [L]. If the residue masses are not summable, if the abscissa is not attained, or if the visible orders are unbounded, every compact window's share tends to zero: the mass escapes to infinite height. Escape classifies; it does not exclude.

### 1.10 Positivity: pointwise, averaged, at zero ordinates, without localization

- Windows: full `‖f‖²/5000` through `3/10` [L] and through `181/500` [S]; odd `‖f‖²/1000` through `181/500` [L]; primitive through `(log 2 + 1/50)/2`. Below `log 2/2` every weight is read blindly; at `181/500` only atom `2`.
- Non-localizing positivity (`a ≤ 3/10`) holds for every prime weight.
- Short-window averages on `Γ^{99/100} ≤ H ≤ Γ/8`; pointwise floor `−4(A + 1)²e^A N²Φ(γ)`; nonnegative tests positive at all but `CH/η` zero ordinates.
- Aperture flow `μ(A)` strictly decreasing; Gaussian ceiling `μ(A) ≤ K exp(11A/2 − πe^{2(A−2)})`; finite negative index at every aperture.

### 1.11 Realization and duality

Maximal sharp-stable positive Meyer ideal = off-line-blind ideal; coupled point-stable carriers isotropic; every invariant carrier sees an off-line pair through a boost. Positive self-dual measures with a gap are Dirac combs; affine positivity on `Aff(ℚ)` is induced from dilations; Weil's extensions are a box over the critical zeros. Every nonzero `L²` wave has a visible successor, every density with nonzero absolutely continuous part a visible affine extension; atomic spectra stay blind; singular-continuous spectra are unclassified [L].

Every unconditional positivity in the corpus is one of: invariant (blind, half-blind, isotropic), averaged, non-localizing, on nonnegative tests, collided (kernel counts, coupled counts, escape forms, `D`), twisted below the conductor horizon, a finite-window certificate, or positive before a renormalization (torsion energies at `r < 1`).

## 2. The 31 routes

Each entry gives the status, the (a) and (b) obstacles, and the walls ([walls ledger](walls-ledger.md)).

### WL — Weil lag function
**Status.** Spline, lag, deficit, critical-energy and cross-work receivers read `Δ` exactly; RH ⇔ critical energy bounded; high zeros contribute `O(1)`. Counting forms: RH ⇔ `ψ(x) − x ≤ C√x log²x` eventually; RH ⇔ horizon torsion `ψ(N) = N + O(√N log²N)` ⇔ the Farey sum of `log(2 sin πk/n)`; Nair's floor from integrality. Budgets (§1.5): a linear prime-error budget forces RH with slope `≥ 2 + γ_E − log 4π`; an Abel slope at the genus forces RH with simple zeros; the successor shift preserves the cost. Filtered deficit `Γ^{−1/2}` on frequency averages.
**(a)** W2–W4; W6; W7(i), W7(xv).
**(b)** B1.1; B1.13; B2.1; B1.4; B3.30.
**Walls:** 1.0, 1.1, 1.15, 1.19, 3.14.

### RW — Restricted Weil ground energy
**Status.** RH ⇔ `μ(A) > 0` for all `A`; the flow never stalls; on the prime-threshold ladder RH ⇔ cumulative relaxation `≤ μ(3/10)`; ground rate = polar rate; local part of the Hodge index holds. Gårding inequality and finite negative index at every aperture; full floor `1/5000` through `181/500` [S]; no positive exponential floor.
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
**Status.** `M(x) = Ω±(√x)`; one-sided `O(√x)` forces RH with simple zeros; `ν̂_N(1) = M(N)` and RH ⇔ `M(N) = O(N^{1/2+δ})` for every `δ`. A linear Mertens budget forces RH, simple critical zeros and `Σ‖1/(ρζ′(ρ))‖² ≤ S`; over `𝔽_q` a Mertens budget is purity with simple spectrum and its slope is the repulsion energy (strict Hasse in genus one). Balanced and centred-prime bands ⇔ `Θ < 1`; gauge a.e. law; finite multiplicative lattice forms blind. Escaped Möbius pairings: growing-endpoint power saving `θ` ⇔ zero abscissa `≤ 1 − θ`, `θ > 1/2` impossible, unrestricted multiplier uniformity false [S]. Pólya–Vinogradov by completion [L]; Burgess moment, energy and inequality [S]; completion needs a period, which the arithmetic point lacks.
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
**Status.** Prime-blind and odd receivers; the distinct-right-zero index `D_idx` is even when finite and RH ⇔ `D_idx < 2`; one-prime Lefschetz receivers; correspondence surface with free square law and budget. Counting (§1.4): section count, effectivity, naive heights (traces, not kernel orders), convex heights each RH. Two forms (§1.1): `Re W = D − Δ`; RH ⇔ `W = D` ⇔ `D` Hecke invariant ⇔ one-shift similitude; `D` faithful, coercive at every aperture, log-Sobolev upper bound [S], local Weyl law; `D` and its Hecke defect computed by the `ξ` current and finite theta prefixes; `W` has finite negative index.
**(a)** W2, W4; W5; W7(xii)–(xiv); W14.
**(b)** B1.3; B1.7 (`D_idx < 2`); B1.9; B1.11; B2.2; B3.10; B3.33; B3.35; B3.37.
**Walls:** 1.3, 1.4, 1.16, 1.17, 3.13, 3.20, 14.2, 14.4, 14.18, 14.21, 14.24.

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
**Status.** Cofinal admission and Haar approximation RH-equivalent; RH ⇔ admission at every damping ⇔ positive gauge mass of every escape state. Energy-rate law in both directions [L]. Escape (§1.9): Abel atoms of `ζ` are its dominant zeros; capacity, endpoint and shadow laws; effective orders; infinite-height escape when residues are non-summable, the abscissa is unattained or visible orders are unbounded. Cofactor modules; escape forms are collided Cauchy forms; centred divisor prefix = sawtooth + long-modulus quadrature.
**(a)** W3/W4; W12.
**(b)** B1.2; B3.2 (exclusion of infinite-height escape; exterior tightness); B3.3; B3.11; B3.16.
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
**Status.** Odd positivity RH-equivalent; light-cone variation positive; odd `181/500` window is the first certificate reading a prime; the Liouville twin there is a height twist of `ζ` plus corrections. The twin is separated [S]: an odd smooth witness has `W_ζ ≥ ‖F‖²/1000`, `W_λ = W_{flip 2} < −‖F‖²/1000`. At `23/40`, where the `{2,3}`-flip is not a height twist, a witness has `W_ζ > ‖F‖²/25`, `W_λ < −(3/10)‖F‖²` [S]. Multi-prime repulsion (§1.7). The companion-forcing certificate and the conductor horizon have no common aperture at any height [L].
**(a)** W2–W5; W17.
**(b)** B1.3; B3.26; B3.32; B3.36.
**Walls:** 1.3, 1.18, 3.4, 3.19.

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
**Status.** One fixed-width late-lag family decides RH; smooth detector at aperture `Cδ^{−2}(4 + |γ|)²`; single-height phase-selective law; eventual all-height saving refuted (Kronecker peaks); one-prime Lefschetz receivers. The detector twisted to its ordinate is the odd sector of `σ_γ`; conductor-horizon positivity; forcing half; the forcing gap is a theorem at every height: a certificate needs `e^{2δa} > 768A log(|γ| + 3)`.
**(a)** W3/W4; W6; W7(ii).
**(b)** B1.4; B1.1; B1.3; B1.9; B3.20; B3.32; B3.36.
**Walls:** 1.17, 3.1, 3.2, 3.14, 3.19.

### ACT — Arithmetic criticality / single-shift variation
**Status.** One fixed shift against all even compact profiles decides RH; light-cone kernel positive; sub-unit collar paid for `log d ≤ a − R`.
**(a)** W3/W4.
**(b)** B1.3.
**Walls:** 1.3, 3.1, 3.4.

### AIP — Arithmetic incidence positivity
**Status.** Allocation for all tests ⇔ RH; universal-constant allocation to `Ke^r e^{−c√r}`; Schur payment to a finite head; exact shared-budget descent; joint signed `2, 3` payment at `r = 23/40` with retained `1/62` mass margin. The linear diagonal reserve cancels against off-diagonal polar terms on the polar-neutral hyperplane; log-cell correlations = divisibility spine + bounded Euclidean remainder. Full-form `181/500` Λ/Liouville separation shows finite-lattice gauge conjugacy does not extend to the complete form [S]. Raw continuum prime towers have negative edge energy of order `e^A`, excluding sub-half exponential `H¹` floors [S]; the pole-neutralized full form is not covered.
**(a)** W2/W5.
**(b)** B1.3; B3.8.
**Walls:** 1.3, 3.4, 3.21.

### ACS — Arithmetic Castelnuovo–Severi effectivity
**Status.**
- Source RR; Meyer RR + Bézout; maximal blind ideal; isotropy; non-localizing positivity; Lefschetz receivers; Weil's layers (§1.3); faithful degree needs RH + simple zeros.
- Counting (§1.4): six currencies; polar box node twist destroys RI; Jacobi–Hurwitz dichotomy [S].
- One-variable systems and deformations (§1.8): κ = 1 class `ℝ^× · ζ`; contraction and collision calculus closed; polar-configuration cone classified; coupled class not rigid; per-ordinate equivalences of positive rigidity, positive chirality and rational/positive central ceilings; critical transfer law; strong multiplicity one below the square-root deficit; central excess ⇒ square-root deficit with residue `≥` excess; `ζ^d` rigidity and boundary capacity; critical conservation [S].
- Two forms (§1.1): `W = D − Δ`; `D` positive, faithful, coercive, computed; Hecke invariant iff RH.
**(a)** W1; W7(xi), W7(xii); W11; W12.
**(b)** B1.6; B1.8; B1.9; B1.11; B1.12; B3.18; B3.28; B3.33; B3.34; B3.35; B3.37; B2.5.
**Walls:** 1.3, 1.15, 1.16, 1.17, 3.8, 3.14, 3.18, 14.4, 14.8, 14.10–14.25.

## 3. The 17 candidates and PW-B

A candidate lacks an independent source construction or landing. Each faces B1.6. Twelve theorems constrain every candidate:

- single-channel sharp-stable positivity certifies only blindness; coupled point-stable positivity only isotropy; non-localizing positivity holds for every prime weight;
- multiplicative correspondences act hyperbolically at every off-line pair; elliptic localization in correspondence-closed carriers is resonance; the only reflection-compatible affine localizer is `σ_γ`, whose even sector cannot force and whose odd-sector certificate is separated from the conductor horizon at every height;
- positivity on nonnegative tests is shared by every dominated twin;
- finite multiplicative certificates are capped by growth input; completed and coupled systems reach the boundary, the `1/log T` collar and the classical local count;
- a mechanism must separate `ζ` from the relaxation models, from `W_β`-deformed members of the coupled class, and from the Liouville and `{2,3}`-flipped twins (which unconditional positivity of `ζ` already separates at `181/500` and `23/40` [S]);
- a mechanism built from multiplicative data proves its conclusion for the whole gauge orbit;
- kernel, coupled and escape-form positivity and `D` are collided and see no sign; `D` is computed, positive and faithful, and its equivariance is RH;
- a section count, effectivity function, naive or convex height, one-sided count, fixed tensor loss or horizon torsion is the sign;
- a counting polarization that is the same on every fibre is not selective; a large-sieve majorant inflates quadratically;
- positive one-variable constructions remove a complex quartet only against a real anchor (`κ ≥ 3` if planted) and collide conjugates only ordinate by ordinate;
- positive deformations keep the off-line divisor and cannot raise the central order at an ordinate without off-line zeros; changing the central order of an arithmetic member costs a square-root prime deficit;
- positivity of torsion energies is lost exactly in the diagonal renormalization that produces Weil's prime kernel.

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

The zero-indexed diagnostics of HJ, SEC, CDC, BSH, IRK and W1C read whether a zero's Hecke symbol is elliptic, with exact depth laws; they detect, they do not force. FEL's contrast and PL's `Δ` are both nonnegative depth capacities vanishing exactly on critical zeros; neither has an arithmetic upper bound. ConjugateDiagonalGeometry shows that zero-indexed depth functionals of this kind can be computed from `ξ` without zero indexing; that removes the circularity of the definition, not the missing bound.

## 4. Supporting programmes

| Programme | Established | (a) | (b) |
|---|---|---|---|
| **BVI** rows and Vaughan | Minor arcs; all-modulus `Q^{−δ/32}`; bands ⇔ `Θ < 1`; half-damping transition; every power improvement ⇔ a fixed strip. | W4 | B2.1; B1.2 |
| **ADR / AOT** cofactor modules | Record minima, contraction calculus, eigencharacter moduli, translated-zero escape rows, two-factor pole trace. | — | B3.2, B3.3, B3.16 |
| **ACCE** aperture flow, rates, long moduli | §1.10; long-modulus decomposition. | W7(ii) | B3.6, B3.1; B1.2 |
| **ACS / Meyer** | §1.3, §1.10, §1.11. | — | B1.6, B1.8 |
| **ACP** correspondence positivity | Normalized graphs, budget, local types, resonance, section and Stepanov counts, contraction and collision calculus, escape alternative and criterion; Abel escape atoms, capacity, endpoint, shadow and infinite-height laws; budget currencies over `ℤ` and `𝔽_q`; successor defect in `H²` (§1.5, §1.9). | W7(xv), W9, W11 | B1.13, B3.2, B3.26, B3.28, B3.30; B1.9 |
| **PL** arithmetic polarization | Polarization law, elliptic localizers, twisted sectors, conductor horizon, forcing half, collision law, rate neutrality, oscillatory capacity; `D` faithful, coercive, a polarization with similitudes iff RH; Gårding; finite negative index; local Weyl law; depth profile; polar-configuration cone; selectivity battery; log-Sobolev upper bound [S]. | W5, W7(xii)–(xiv) | B1.11, B3.32, B3.33 |
| **CDG** conjugate-diagonal geometry | §1.1: `ξ` current, finite theta metrics, depth distribution, two-scale variance law, conductor–forcing gap; fixed-strip source cutoff [S]. | W14 | B3.33, B3.36 |
| **AE** arithmetic effectivity | §1.3–§1.6: effectivity calculus, Tate, naive heights are traces, convex heights, polar box, torsion potential and intersections, renormalized torsion energy, completion law, hyperelliptic calibration; Burgess [S]. | W12 | B1.9, B3.30, B3.35, B3.37 |
| **BGG** biarithmetic gauge geometry | §1.7, §1.8: gauge torus, successor holonomy, Catalan and multi-prime repulsion; deformation principle, Abel–Gram law, coupled-class equivalences, strong multiplicity one, square-root deficit law, `ζ^d` boundary capacity, polar-neutral collapse, Ramanujan torsion; critical conservation [S]. | W7(xi), W12 | B1.12, B3.26, B3.34 |
| **SP** selective positivity and thresholds [S] | §1.4, §1.7: `181/500` full floor and twin separation, `23/40` two-prime separation, continuum tower obstruction, escaped Möbius pairing law, parity-lobe obstruction, Serre-dual box cohomology, Jacobi–Hurwitz heights. | W5, W12, W17 | B3.8, B3.26, B3.35 |
| **APD** positive duality | §1.11. | — | B1.6 |
| **MPG** multiplicative positivity | Boundary forcing, capacity, regularity, families, Siegel exception; interior capped. | W10 | — (complete below RH strength) |
| **SBWF** strip Bochner–Weil forcing | Completed-system collars; κ = 1 class; `5d < 9κ`. | — | B3.18 |
| **ACG** correlation geometry | Gauge invariance, a.e. laws, comeager-null exceptions, prime pole, archimedean-line threshold, loss law, gauge-mass criterion. | W9 | B1.2, B3.24 |
| **AKT** Künneth theory | Product receivers see depth only through total length; Künneth positivity = point-count positivity. | W9 | — |
| **AOG** orientation, index, theta `h⁰` | Generic orbit; scale-stable families; index exit; base theta `h⁰`. | W4 | B3.10; B2.2 |
| **ALDG** local divisor heat | Hermite barrier, optimal heat, residual region model complete. | W7(iii) | B3.9; B1.5 |
| **APT** full cone, selectivity, phases | Source selection; phase-selective single height; finite-level existence. | W4 | B1.4, B3.20 |
| **BiScale** lag, packet, filtering, observation | Endpoints; high-zero tail; filtered deficit; closed-cycle recovery. | W6, W7(i) | B1.4, B2.4 |
| **SAEI** shared budgets, damping | Frustration law; half-damping chain bounded, not Hilbert–Schmidt. | W2 | B3.8, B3.11 |
| **SSA** signed successor | Odd-shift `1/3`, lag-2 `1/4` floors exact. | — | B3.13, B2.6 |
| **THIM** damping and Dini laws | Dini thresholds; integer local exponents below half. | — | B3.11 |
| **Biarithmetic** carriers | Affine quotient; torsion; golden calibration; payment-domain nonclosure. | — | B3.3 |
| **TTPC** coalescent pairs | `N₀* ≥ (29/36 − ε)N − surplus`; parity-blind dispersion cannot give `β < 5/36` at `λ = 4/3` [S]. | — | B2.5, B2.7, B3.24 |
| **HTG** tools | Fejér–Riesz; Bochner uniqueness for Laplace weights; lattice Fourier vanishing ⇒ absolute continuity; planar log-square bounds; quadratic ascent [S]. | — | — |
| **Analytic inputs** | Guth–Maynard; 30/13 density; Selberg near-line density; Heath-Brown; KKL; dlVP, Littlewood, VK; Cramér mean square under RH. | W6, W10 | B2.4, B2.8, B2.10 |

## 5. Not open tasks

These are complete results or excluded shortcuts. They must not reappear as open obstacles.

- **Settled questions.**
  - What computes `D`: the current `Δ log|ξ|` and finite theta prefixes, with multiplicities, without zero indexing.
  - Whether `D` is a norm: faithful, coercive at every aperture; the zeros are a sampling set.
  - Whether `W` can have infinitely many negative directions at one aperture: no.
  - The forcing gap: the existing companion certificate and the conductor horizon are disjoint at every height.
  - The edge problem at `181/500` and the first non-archimedean twin at `23/40`: both twins fail on explicit witnesses on which `ζ` is positive [S].
  - The energy-rate law at the zero abscissa, both directions.
  - Escape when residues are non-summable, the abscissa unattained or orders unbounded: infinite height.
  - Positive and rational deformations of the coupled carrier: rigid exactly at zero-free ordinates; their central ceilings and positive chirality are RH ordinate by ordinate.
  - Whether a central excess of an arithmetic member is cheap: it costs a square-root prime deficit with residue at least the excess.
  - Budget currencies over `𝔽_q`: prime-error slope counts the spectrum with squared multiplicity; Mertens slope is the repulsion energy; genus one: strict Hasse.
  - Whether Weil's prime kernel is a limit of positive forms: yes, after a divergent diagonal renormalization, where positivity is lost.
  - Whether kernel counts supply naive heights: no (complex fake).
  - Earlier settled items: section counts, effectivity, naive heights, one-sided counts are the sign; elliptic localization in correspondence-closed carriers is resonance; coupled-class two-sided rigidity fails at critical-zero ordinates; contraction and collision calculus; theta `h⁰` does not extend; multiplicative lattice forms are blind; the first gauge charge is a height twist; escape location and dominant classification; theorem of the square and budget free; positivity beyond isotropy only without localization; κ = 1 class; Lefschetz receivers at one prime; linear loss; twists rate neutral; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false; summation-scope "defects" never existed.
- **Excluded mechanisms** (in addition to the [killed-routes catalogue](../rh-killed-routes.md)):
  - collided coercivity, sampling or finite negative index offered as Weil's sign;
  - the computed `D` (current or theta readings) offered as a bound on its own Hecke defect;
  - the companion-forcing certificate spliced with the conductor horizon;
  - positive or rational deformations of `ζ_γ` offered as forcing (they detect zero-free ordinates);
  - budget currencies, convex heights or Farey sums offered as inputs weaker than the sign;
  - large-sieve or Cauchy–Schwarz majorants offered as Riemann–Roch sections;
  - torsion-energy positivity at `r < 1` offered as Weil positivity;
  - raw continuum prime towers as sub-half exponential floors;
  - completion offered as a mechanism at the arithmetic point.
- **Substitutions that do not hold.** Computed for bounded; collided for Rosati; positive for equivariant; equivariant for positive; norm for sign; sampling for positivity; finite index for zero index; resonance for localization; twist for gauge charge beyond the first prime; soft polarization for selective polarization; positive deformation for arbitrary member; rational ceiling for full ceiling; one-sided ceiling for two-sided rigidity; classification of escape for its exclusion; budget for sign; regularized limit for limit of positivity; finite-level count for the arithmetic point; finite window separation for all-aperture selection; averages for selected heights; nonnegative tests for the full cone; zero-indexed objects for pre-divisor constructions.
