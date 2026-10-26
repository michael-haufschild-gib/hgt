# Arithmetic Correspondence Positivity (ACP)

**One question.** Over `𝔽_q` one structure — the intersection theory of correspondences on
`C × C` — supplies the sign of the explicit formula (Rosati positivity, the Hodge index), its
budget (`2g`), the base and the tensor powers. Over `ℤ` the corpus has the pairing, the Lefschetz
receivers and the exhaustion of every substitute it has tried. What is the positivity theory of
**arithmetic correspondences** — dilations (gauge invariant), affine maps and additive relations
(gauge charged), the archimedean flow — and which layers of Weil's argument exist for them, which
are free, which are provably absent, and what would a sign specific to `ζ` have to look like?

ACP is the join of [Arithmetic Positive Duality](../ArithmeticPositiveDuality/README.md) (rigidity
and capacity of positive Poisson pairs, with its exhaustion map of forcing mechanisms) and
[Arithmetic Correlation Geometry](../ArithmeticCorrelationGeometry/README.md) (the gauge torus and
its charged and invariant statistics) with the object neither of them has: **a ring of
correspondences with graphs, degrees, a Rosati involution and a budget**. Its basic object is a
*correspondence surface*: a polar surface on which a ring with involution acts by similitudes. Its
basic invariant is the **Rosati trace** `τ_x(ξ) = δ(ξ·x, x)` of a cycle `x`. Its basic measurement
is the **local type** of a correspondence at a reflection pair `{ρ, ρ* = 1 − ρ̄}` of the spectrum:
hyperbolic, elliptic or unipotent.

Namespace `GaloisForLFunctions.ArithmeticCorrespondencePositivity`; umbrella
`ArithmeticCorrespondencePositivity.lean`. Everything is unconditional; RH appears only inside
equivalences.

---

## 1. Place in the research

The B-tier obstacles of the frontier (B1.3, B1.6, B1.9, B3.17, B3.22, B3.23) are one obstacle in
several currencies: *a positivity of gauge-charged correspondences with a fixed budget*. The
corpus has mapped every forcing mechanism it knows, each with a sharp limit:

| Mechanism | Sharp limit | Owner |
|---|---|---|
| Quadratic positivity on carriers | blind, half-blind or isotropic fibres at off-line pairs | ACS, APD |
| Multiplicative positivity | boundary and capacity `⌊k/2⌋`; interior only from growth input | MPG, SBWF |
| Linear rigidity | determines `ζ` (theta, Beurling, `κ = 1`), never sees zeros | APD |
| Pole order | pays inserted zeros exactly, intrinsic zeros not at all | RHTower, SBWF |
| Multiplicative data | gauge orbits only; the actual source is one point | ACG |
| Amplification over `ℤ` | loses linearly (gauge Jensen; product receivers; family averages, P23) | ACG, AKT, ACP |
| Averaging over heights | selects windows, not zeros | ACS, ACG |
| Affine positivity on `Aff(ℚ)` | induced from the dilations; integer successors see only Kronecker-null spectra | APD |
| Weil's receiver over `ℤ` | complete: one prime, one test, `|c_m| ≤ c_0` ⇔ RH | ACS, AOG |

Over `𝔽_q` the missing input is supplied by correspondences. ACP asks for the arithmetic analogue
of each layer of Weil's argument separately, so that a negative answer names exactly the layer
that is missing, and it explains the common shape of the limits above by the local geometry of a
reflection pair.

| Programme | Interface |
|---|---|
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Scaling data, the correspondence algebra `G →₀ ℝ`, Rosati, Hecke graphs, orientation, rates, the spline orbit. ACP's correspondence surfaces are AOG's scaling data with graphs, degrees and budgets added. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Polar surfaces, the scaling surface, curve data, the golden datum, genus-one graph classes and Hasse, the no-go for Hecke scales, the maximal blind ideal, the window theorems. |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Positive-definite functions on `ℚ_{>0}` and `Aff(ℚ)`, coupled isotropy, the left-blind ideal, Hecke and Bost–Connes states, the Kronecker split, archimedean–successor coupling. ACP reads its states as Rosati traces and its isotropy laws as consequences of hyperbolicity. |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | Gauge torus, gauge charge, near-incidences as successor correlations, boundaries, loss laws, the `𝔽_q` fixed-budget law. |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md), [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md) | Boundary forcing, Fejér barrier, completed positive systems, collar capacity. |
| [ArithmeticKunnethTheory](../ArithmeticKunnethTheory/README.md) | Künneth positivity is point-count positivity; product receivers see depth only through total length. |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Cofactor modules, escape states, translated-zero eigenstates. |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Zero width, the aperture-`3/10` certificate for every prime weight, the Liouville twist. |
| HTGeometry, RHTower | Characteristic-zero Stepanov; the full Weil functional affine in the prime weights; Dirichlet first differences. |

---

## 2. Why

**Weil's proof in layers.** Over `𝔽_q`, for the Frobenius `F` of a curve of genus `g`:

| Layer | Content over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz, adjunction, Rosati adjoint, `F F′ = q` | exact (AOG) | no: hold on the golden datum |
| L2 Graphs | the graph map `End → NS` is quadratic (theorem of the square) | exact for normalized graphs (P1) | no: holds on the golden datum |
| L3 Budget | `δ(Δ, Δ) = 2g`, unchanged along the Frobenius orbit | `δ(x, x)` for every test, unchanged along every Hecke orbit (P2) | no: the golden datum has budget `2` |
| L4 Kernel counts | `deg P(F) = #ker = Π P(α_i) ≥ 0` (`H¹`); exterior `det_{Λ^k}(c ∓ Λ^k F) ≥ 0` (`1 ≤ k ≤ |ι|/2`, `c > (√q)^k`, P17, `CurveDatum.exterior` in P25); `deg(f f′)` is a square | affine maps of `ℤ` have genus zero (P9); archimedean midpoint contractions contract real pairs at `Δκ = 0` (P17), single-system complex quartets obey the Post–Widder real-anchor law (`Δκ ≥ 1` without a real anchor) and functor-independent Hadamard pole floor (`κ ≥ 3` for a weight-`2` anchored quartet, `16M + 5d < 9κ`, P31), and height-coupled / Fejér-coupled systems eliminate the marginal pole tax (`Δκ = 0`) across `0 < a < 1/2` with normalized central pole cost `9(K+1)/(2K) κ ↘ (9/2)κ` against matching Fejér–Egerváry–Szász (`c₀ ≥ 1/cos(π/(K+2))`) and `Θ(d log(3+|γ|))` Gamma lower bounds (P25, P31) | `H¹` only real off-line pairs (P3); exterior `Λ^k H¹` forces unitarity in every genus (P17, P25) |
| L4′ Spectrum of `f f′` | eigenvalues `P(α_i)P(q/α_i) ≥ 0` | the critical line itself, at one prime (P10) | yes: it is purity |
| L5 Rosati positivity | `Tr(ξ ξ′) ≥ 0` from a polarization | equivalent to RH | yes |
| L6 Base | even tensor powers over a base, fixed loss (Deligne) | a fixed loss is RH (P8) | — |

The first three layers are identities and transfer to `ℤ` intact; the golden datum
`1 − 5X + 5X²` satisfies them and violates Hasse–Weil. The budget of Weil's inequality is not
what `ℤ` lacks: it is fixed for free by the similitude law. What `ℤ` lacks is its **sufficiency**,
which on every span `{x, T x}` is the positivity of the two normalized graphs of `1 ± T`.

**Two kinds of effectivity.** The degree of an endomorphism is the size of its kernel,
`Π_i P(α_i)`: a determinant, pairing each eigenvalue with its complex conjugate. The Rosati trace
`Σ_i P(α_i) P(q/α_i)` pairs each eigenvalue with its **reflection**. In genus one the two coincide
(Hasse). From genus two on they separate: the complex fake (`q = 16`, roots `±8i, ±2i` of
`X⁴ + 68X² + 256`) has nonnegative point counts at every level and a nonnegative kernel count for
every ring element, and violates Hasse–Weil. The off-line candidates of `ζ` are non-real, so a
kernel-count effectivity on `H¹` would be blind to all of them. Exterior powers repair this over
`𝔽_q`: kernel counts on `Λ^k H¹` collide a complex quartet into a real off-line eigenvalue and force
unitarity in every genus (P17).

**Local types.** The Rosati trace of a cycle splits over the reflection pairs of its spectrum. At an
off-line pair the local form `2 Re(u v̄)` in the coordinates `(ĝ(ρ), ĝ(ρ*))` has signature `(1, 1)`.
Correspondences act on such a fibre in three ways:

| Type | Action on the fibre | Correspondences | What positivity forces |
|---|---|---|---|
| **Hyperbolic** | boost `diag(β, β̄⁻¹)`, `|β| ≠ 1` | Hecke operators, archimedean flow, all gauge twists — exactly off the line | isotropy / half-blindness of every invariant positive subspace |
| **Elliptic** | rotation, or the reflection swap `(u, v) ↦ (v, u)` | Hecke operators on the line; the symmetric Hecke operator at a resonant prime; the functional equation | a sign or phase condition only: positive non-isotropic fibres survive |
| **Unipotent** | identity on the polar part | the additive successor | nothing |

This is the common origin of blindness, half-blindness and isotropy: **multiplicative symmetry is
hyperbolic exactly at off-line zeros**. On real even tests the fibre is `z = ĝ(ρ) ∈ ℂ` with form
`2 Re(z²)`, and the symmetric Hecke operator at `p` acts by `w = p^{ρ−½} + p^{½−ρ}`, real iff
`γ log p ∈ πℤ`; a non-real point resonates at no more than one prime, so two primes force
blindness.

**What counting can and cannot see.** The kernel count of a symmetric square `f f′` is a square,
the kernel count of `f` pairs conjugates, and only the spectrum of `f f′` — each eigenvalue
`(α − c)(q/α − c)` separately — is the sign: it is nonnegative for every `c` iff the datum is pure
(P10). Positivity in Weil's argument is pointwise on the spectrum of symmetric squares, the spectral
form of the positivity of the Rosati involution. The gauge-charged correspondences of `ℤ`, the
affine maps, have at most one periodic point and meet each other at most once (P9): they have genus
zero, and their arithmetic enters only through counts weighted by a source.

**Localization and source.** Positivity constrains a fibre only where the carrier localizes.
Bounded-aperture carriers are Weil-positive with full fibres at every pair of points — positivity
beyond isotropy — but they do not localize, and the same positivity holds for every prime weight:
it is source-blind. On nonnegative tests the form is antitone in the source, so `ζ` is the worst
member of its sign orbit there and positivity is an upper-bound statement. A sign specific to `ζ`
must localize, must have a non-hyperbolic local symmetry at off-line pairs, and must live on
autocorrelations that change sign at prime-power logarithms.

**Escape.** The only handle on the rate wall that is not a rate is the escape alternative of the
damped Möbius receiver: its normalized cofactor Grams either converge with bounded energy or escape.
On the log scale a dilation is a translation, so a cofactor Gram is the translation Gram of one
profile, whose Laplace transform is `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s` (P18, P19). A
translated zero `ρ − ε` contributes the exponential `e^{(ρ−ε−½)u}`, and the escape states of the
zeros of maximal depth are phase kernels: positive semidefinite, of rank the number of those zeros,
generated by the characters `j^{−(ρ−ε)}`, with the horizon acting on the phases and dilation acting
as the archimedean flow (P20–P22, P24, P26, P27). Escape completeness is therefore not a positivity
question but an energy split of the profile with symbol `G`.

---

## 3. Objects and language

| Weil over `𝔽_q` | ACP object | Over `ℤ` | Lean |
|---|---|---|---|
| `C × C`, `NS` | correspondence surface: polar surface with a ring acting by similitudes | scaling surface with the Hecke algebra of `ℝ_{>0}` | `ScalingDatum` (AOG), `scalingSurface` (ACS) |
| `End(J)`, `ℤ[F]` | correspondence ring `G →₀ ℝ`, Rosati `ξ′(g) = ξ(−g)` | Hecke algebra | `Correspondence`, `rosati` (AOG) |
| graph `Γ_f` | normalized graph `N(y) = y + (1 − y·V)H + β(y)V` | normalized Hecke graph | `normGraph`, `graphDegree` |
| `deg f` | `deg N(y) = δ(y, y)/2` | half the Weil form | `normGraph_degree` |
| `2g` | budget `δ(x, x)` | Weil norm of a test | `CurveDatum.diagonal_defect` |
| `#ker P(F)` | determinant degree `Π P(α_i)` | — | `detDeg` |
| `Tr(P(F) P(F)′)` | Rosati degree `Σ P(α_i) P(q/α_i)` | Weil form on a Hecke orbit | `rosatiDeg`, `traceAt` |
| `α ↦ q/α` | reflection pair, local form `2 Re(u v̄)` | `ρ ↦ 1 − ρ̄` | `localForm` |
| Frobenius eigenvalue | symbol `p^{s − ½}`; symmetric symbol `p^{s−½} + p^{½−s}` | Hecke operator, symmetric Hecke operator | `heckeSymbol`, `symHeckeSymbol`, `symHecke` |
| — | successor defect `D_a(s)` | `Σ a_{n+1}((n+1)^{−s} − (n+2)^{−s})` | `succShiftDefect` |
| fake curves | golden datum (real pair), complex fake (complex quartets) | — | `goldenDatum`, `complexFake` |
| — | sign twins, Liouville twin, flipped twins | dominated prime weights | `liouvilleTwin`, `flipTwin` |
| — | tensor-power bounds and their loss | `|c(t)|^k ≤ C e^{Lt}` | `splineCorr` |
| — | log profile and translation Gram of a row | `g(u) = e^{−u/2} v(⌊e^u⌋)`; `⟨D_j v, D_k v⟩` | `logProfile` (ADR), `pronicPairing_rowDilate_eq_translationGram` |
| — | dominant configuration, phase kernel, Cauchy form | `Σ c_k e^{(x+iy_k)u}`; `K_θ`; `Σ v_k v̄_l/(2x + i(y_k − y_l))` | `domProfile`, `escapeKernel`, `cauchyDensity`, `domSeries`, `escapeKernelSeries` |
| — | power row of a translated zero | `Re(c n^{ρ−ε})` | `powerRow`, `powerProfile` |

**Words.** *Correspondence surface*: polar surface with a ring acting by similitudes that preserve
the fibre plane. *Normalized graph*: the isotropic class of unit vertical degree in `y + ⟨H, V⟩`.
*Budget*: the self-defect of a cycle. *Sufficiency*: Weil's inequality on every span `{x, ξ·x}`.
*Determinant* / *Rosati degree*: the two quadratic-type invariants of a ring element, pairing
conjugates / reflections. *Local form*: the Rosati trace on the fibre of a reflection pair.
*Hyperbolic*, *elliptic*, *unipotent*: the local types above. *Resonant prime* (for a point `ρ`):
`γ log p ∈ πℤ`. *Localizing carrier*: one that can isolate the contribution of one reflection pair.
*Atoms* of a test `k`: `Re(k(log n) + k(−log n))`. *Dominated source*: a prime weight `w ≤ Λ`.
*Loss* of an amplification: the exponent `L_k` in `|c|^k ≤ C_k e^{L_k t}`. *Escape state*: a limit
of normalized cofactor Grams. *Dominant configuration*: a profile `Σ c_k e^{(x+iy_k)u}` of
exponentials on one line `x > 0`. *Phase kernel*: the escape kernel `K_θ` of a configuration at
unimodular phases `θ`. *Escape rank*: the rank of an escape state on the dilations.
*Subdominant remainder*: a part of a row whose pronic energy is negligible against the row's.

---

## 4. Mechanisms

**Owned by sibling programmes.** Rosati positivity is the orbit Hodge index (AOG); eventual
Hasse–Weil is Hasse–Weil (AOG); coupled isotropy (APD); Hasse in genus one (ACS); gauge projection
and gauge Jensen (ACG); Künneth collapse (AKT); the window certificate for every prime weight
(SquareRootThreshold).

**ACP mechanisms.**

1. **Normalization of graphs.** Every class has a unique normalized graph modulo fibres; its degree
   is half the defect, its polarization the defect pairing, and the graph map is quadratic. On a
   scaling datum the degree form of the ring at a cycle is half the Rosati trace form.
2. **Similitude law.** Hecke graphs multiply degrees by `e^{s(g)}`; normalized correspondences keep
   them. The degrees of `N(x ± ψ_g x)` are `c_x(0) ± c_x(g)`.
3. **Determinant versus trace.** Conjugation pairs the factors of the determinant into `|·|²`
   when no eigenvalue is real; the Rosati degree is the Toeplitz form of the power sums.
4. **Boost lemma.** If `|β| ≠ 1`, the map `(a, b) ↦ (a + bβ, a + bβ̄⁻¹)` is onto `ℂ²`, so positivity of
   `2 Re(u v̄)` on a cyclic span forces `u v̄ = 0`; if `|β| = 1` it forces only `Re(u v̄) ≥ 0`.
5. **Lagrange localization.** On a finite spectrum a separating symbol interpolates any values,
   isolating one reflection pair.
6. **Resonance arithmetic.** `Im(p^{ρ−½} + p^{½−ρ}) = 2 sinh((σ − ½) log p) sin(γ log p)`; `p^a ≠ q^b`
   for distinct primes.
7. **Unit step.** `‖x^{−s} − (x + 1)^{−s}‖ ≤ ‖s‖ x^{−Re s − 1}`: the successor shift of a source is a
   holomorphic perturbation on `Re s > 0`.
8. **Affine source.** `W_w − W_λ = Σ (λ − w) n^{−1/2}(k(log n) + k(−log n))`: on nonnegative atoms the
   form is antitone in the source.
9. **Root extraction.** `|c|^k ≤ C e^{Lt}` gives width `≤ L/k`.
10. **Dilation is translation.** On the cell `[log n, log(n+1))` both dilates of a row are constant
    and `∫ e^{−u} = 1/(n(n+1))`: the pronic measure is Lebesgue measure on the log scale.
11. **Cauchy positivity.** `1/(2x + iω) = ∫_0^∞ e^{−(2x+iω)t} dt`, so the escape form is
    `∫_0^∞ e^{−2xt}|Σ v_k e^{−iy_kt}|² dt`; distinct frequencies are separated by Artin's lemma
    (finitely many) or by Bohr means (summable).
12. **Horizon averaging.** `|∫_0^T e^{iωL} dL| ≤ 2/|ω|` kills the cross terms of escape kernels at
    the scale of the inverse spacing.
13. **Floor error.** `|⌊e^u⌋^z − e^{zu}| ≤ 4|z| e^{(Re z − 1)u}`: a power row and its exponential
    profile differ by a subdominant amount.

---

## 5. Pillar theorems

**Foundations from sibling programmes.**

| Foundation | Statement | Lean |
|---|---|---|
| F1 Rosati = orbit Hodge index (AOG) | `τ_x(ξ ⋆ ξ′) ≥ 0` for all `ξ` ⇔ the defect is nonnegative on the orbit of `x` | `rosatiPositive_iff_orbitHodgeIndex` |
| F2 Scaling Hodge index = RH (ACS, AOG) | the scaling surface satisfies the Hodge index iff RH | `scalingSurface_hodgeIndex_iff` |
| F3 Hasse in genus one (ACS) | unitarity ⇔ `deg(m − nF) ≥ 0` on `ℤ²` ⇔ `t² ≤ 4q` | `genusOne_hasse_tfae` |
| F4 Hecke scales are numerically free (ACS) | `a ↦ T_a x` satisfies no parallelogram law | `heckeCorrespondence_no_square_relation` |
| F5 Coupled isotropy (APD) | positivity on point-stable coupled carriers forces `K_ρ`-isotropy | `coupled_isotropy`, `positive_ideal_halfBlind` |
| F6 Fixed budget over `𝔽_q` (ACG) | bounded power sums force unitarity | `unitary_of_bounded_powerSum` |
| F7 Eventual budgets are sharp (AOG) | eventual Hasse–Weil with any constant is Hasse–Weil | `hasseWeilAt_of_eventually_bounded` |
| F8 Spline rate law (AOG) | `|c(t)| = O(e^{σt})` ⇔ zero width `≤ σ` | `zeta_splineOrbit_rate_iff_zetaZeroWidth_le` |
| F9 Window certificate (SquareRootThreshold) | aperture `3/10` positivity for every prime weight | `re_weilFullFunctional_ge_of_aperture_le_threeTenths` |
| F10 Finite-rank escape rows (ADR) | rows obeying finite-rank dilation laws at `2` and `3` are sums of translated-zero powers plus finite energy | `exists_finiteRank_zeroPower_decomposition` |
| F11 Escape states on the gauge torus (ACG) | every cofactor limit has a spectral measure on the gauge torus; power-type energy growth leaves it zero | `exists_actualCofactorLimit_spectralMeasure`, `gaugeMass_eq_zero_of_powerGrowth` |
| F12 Energy growth cancels zeros (ACG) | receiver energy `O(T^κ)` forces `ζ(ρ − ε) = 0` at every zero with `Re ρ > (1 + κ)/2 + ε` | `riemannZeta_sub_eq_zero_of_energy_growth` |

**ACP pillars.**

| Pillar | Statement | Lean |
|---|---|---|
| **P1 The theorem of the square is free** | On every polar surface `N(y)·V = 1`, `N(y)² = 0`, `deg N(y) = δ(y,y)/2`, `N` is quadratic and unique modulo fibres; on a scaling datum the degree of the normalized graph of `ξ·x` is `τ_x(ξ ⋆ ξ′)/2`, its positivity is the orbit Hodge index, and on two-term correspondences it is Hasse–Weil. RH ⇔ every normalized Hecke graph of every test (equivalently of the cubic spline) has nonnegative degree. The ring map obeys the theorem of the square while the scale map does not. In genus one ACS's graph classes are normalized graphs; the golden datum has the theorem of the square and a graph of degree `−1`. | `normGraph_square`, `normGraph_degree`, `eq_normGraph_of_mem`, `graphDegree_eq`, `forall_graphDegree_nonneg_iff`, `hasseWeilAt_iff_graphDegree_nonneg`, `riemannHypothesis_iff_forall_graphDegree_nonneg`, `riemannHypothesis_iff_splineCycle_graphDegree_nonneg`, `ring_square_and_scale_no_square`, `CurveDatum.graphCycle_eq_normGraph`, `goldenDatum_normGraph_degree_neg` |
| **P2 The budget is free, its sufficiency is not** | Similitude law for normalized Hecke graphs; Weil's inequality at a scale ⇔ `deg N(x ± ψ_g x) ≥ 0`; the budget of the diagonal of a curve is `2g`; sufficiency at every level ⇔ unitarity; golden (budget `2`) and complex fake (budget `4`) insufficient; RH ⇔ sufficiency of the spline budget at every scale. | `normGraph_degree_heckeGraph`, `normGraph_degree_act`, `hasseWeilAt_iff_normGraph_degree_nonneg`, `CurveDatum.diagonal_defect`, `budget_sufficient_iff_unitary`, `goldenDatum_budget_insufficient`, `complexFake_budget_insufficient`, `riemannHypothesis_iff_spline_graphs_one_add_sub_nonneg` |
| **P3 Kernel counts are blind to complex quartets** | The determinant degree is multiplicative, real, and nonnegative on every datum without real eigenvalues; the Rosati degree is the Toeplitz form of the power sums and is nonnegative on `ℝ[F]` iff the datum is unitary; golden `deg(2 − F) = −1`; the complex fake has nonnegative point counts and kernel counts, violates Hasse–Weil, and has Rosati degree `−2304` at `F² + q`; zeros of `ζ` in the strip are non-real. | `detDeg_mul`, `conj_detDeg`, `detDeg_nonneg_of_im_ne_zero`, `rosatiDeg_sum_monomials`, `rosatiDeg_nonneg_iff_unitary`, `goldenDatum_detDeg_two_sub_X`, `complexFake_eigenvalue_root`, `complexFake_pointCount_nonneg`, `complexFake_not_hasseWeil`, `complexFake_rosatiDeg_neg`, `counts_do_not_force_purity`, `zeta_strip_zero_im_ne_zero` |
| **P4 Off-line fibres are hyperbolic** | Boosts are isometries of the local form; cyclic positivity under a boost forces `u v̄ = 0`, under a rotation only `Re(u v̄) ≥ 0`; the Hecke symbol is a boost iff off the line; finite configurations: cyclic positivity under a separating symbol ⇔ half-blindness at every off-line pair; real even fibres: a non-real symbol forces `ĝ(ρ) = 0`, a real one only `Re ĝ(ρ)² ≥ 0`; resonance iff `γ log p ∈ πℤ`; a non-real point resonates at no more than one prime, a real point at every prime; two primes force blindness; the symmetric Hecke operator acts on transforms by its symbol, and the law holds for actual real even tests. | `localForm_boost`, `mul_conj_eq_zero_of_cyclic_nonneg`, `cyclic_nonneg_iff_of_norm_eq_one`, `norm_heckeSymbol_eq_one_iff`, `mul_conj_eq_zero_of_heckeCyclic_nonneg`, `halfBlind_iff_cyclicForm_nonneg`, `eq_zero_of_symCyclic_nonneg`, `symCyclic_nonneg_iff_of_im_eq_zero`, `symHeckeSymbol_im_eq_zero_iff`, `not_resonant_at_two_primes`, `eq_zero_of_two_prime_symCyclic_nonneg`, `mellinAt_reflect_of_even`, `mellinAt_symHecke`, `mellinAt_eq_zero_of_symHecke_local_nonneg` |
| **P5 The successor is unipotent** | Gauge twists and the archimedean flow keep the modulus `p^{σ−½}` of a symbol; the successor defect `D_a` is holomorphic on `Re s > 0` for every source with `Σ |a_{n+1}| n^{−σ−1} < ∞`; `Σ Λ(n)(n+1)^{−s} = −ζ′/ζ(s) − D_Λ(s)`: the shifted prime source has the poles of `−ζ′/ζ` in the strip with the same principal parts; the defect is at most `|s| Σ|a_{n+1}|(n+1)^{−σ−1}`, for the primes `|D_Λ(s)| ≤ |s| |ζ′/ζ(1 + σ)|`, sharp on the real axis up to `2^{1+σ}`: `D_Λ(σ) ≥ σ 2^{−1−σ}|ζ′/ζ(1 + σ)|`. | `norm_twisted_heckeSymbol`, `norm_archimedeanSymbol`, `differentiableOn_succShiftDefect`, `succShift_vonMangoldt_eq`, `differentiableOn_succShiftDefect_vonMangoldt`, `norm_succShiftDefect_le`, `norm_succShiftDefect_vonMangoldt_le`, `le_re_succShiftDefect_vonMangoldt` |
| **P6 Positivity beyond isotropy does not localize** | For `0 < a ≤ 3/10` the carrier `realTestsAt a` is coercively Weil-positive, sees both points of every pair, and is positive for every prime weight. | `positivity_beyond_isotropy_at_finite_aperture`, `exists_mem_realTestsAt_mellinAt_ne_zero`, `re_mellinAt_apertureProbe_pos` |
| **P7 On nonnegative tests `ζ` is the worst twin** | The full Weil functional is affine in the prime weights; on nonnegative atoms it is antitone; for `f ≥ 0` and every `w ≤ Λ` (sign twins, the Liouville twin, truncations, the prime-free weight) `Re W_Λ(f ⋆ f̃) ≤ Re W_w(f ⋆ f̃)`, so positivity there transfers to all of them; a negative atom at `n₀` makes the flipped twin strictly worse. | `weilFullFunctional_sub_eq`, `re_weilFullFunctional_le_of_le`, `re_weilTest_nonneg`, `re_weilFullFunctional_vonMangoldt_le_of_nonneg`, `liouvilleTwin_le`, `weilPositive_nonneg_transfers`, `flipTwin_lt` |
| **P8 The base is a fixed loss** | `|c(t)|^k ≤ Ce^{Lt}` gives width `≤ L/k`; bounds with linear loss `kσ` hold iff width `≤ σ`; sublinear loss gives RH; RH ⇔ one exponent bounds every tensor power of the spline correlation; the golden datum's tensor powers lose `k log φ`. | `zetaZeroWidth_le_of_tensor_bound`, `zetaZeroWidth_le_iff_linear_tensor_loss`, `riemannHypothesis_of_sublinear_tensor_loss`, `riemannHypothesis_iff_fixed_tensor_loss`, `goldenDatum_tensor_loss_ge` |
| **P9 Affine correspondences of `ℤ` have genus zero** | `(a − 1)(f^m(n) − n) = (a^m − 1)((a − 1)n + b)`; for `a ≥ 2` every iterate of `n ↦ an + b` has at most one fixed point, the same for all `m`, integral iff `(a − 1) ∣ b`; the successor has no periodic points; two distinct affine graphs meet at most once. | `affineIter_mul`, `affineIter_fixed_iff`, `fixedPoints_iter_subsingleton`, `exists_fixed_iff`, `translate_iter_ne`, `affine_graphs_meet_at_most_once` |
| **P10 The spectrum of symmetric squares is the sign** | Core lemma: `α α' = q > 0` and `(α − c)(α' − c) ≥ 0` for all real `c` force `|α|² = q`; `deg(f f′)` is a square; every eigenvalue of `(F − c)(F − c)′` is a nonnegative real iff the datum is unitary; the complex fake has `17 − 6i`, the golden datum `−1`; locally `(β − c)(β⁻¹ − c) ≥ 0` for all `c` iff `|β| = 1`, which for the Hecke symbol is `Re ρ = ½` at one prime without resonant exception. | `normSq_eq_of_symSquare_nonneg`, `prod_symSquareEig_eq_sq`, `symSquare_spectrum_nonneg_iff_unitary`, `complexFake_symSquareEig_one`, `goldenDatum_symSquareEig_two`, `symSquare_local_nonneg_iff`, `symSquare_heckeSymbol_nonneg_iff`, `riemannHypothesis_iff_symSquare_heckeSymbol_nonneg` |
| **P11 The resolution of a correspondence is its length** | `|p^{iγ} − p^{iγ'}| ≤ log p · |γ − γ'|`; a polynomial separating two critical symbols by `1` has derivative bound `C` with `1 ≤ C log p |γ − γ'|`; modulation by `cos(γu)` translates the transform, `(ĝ(s + iγ) + ĝ(s − iγ))/2`. | `norm_heckeSymbol_sub_le`, `one_le_deriv_bound_mul_length`, `mellinAt_mul_cos` |
| **P12 A budget pays a hyperbolic pair only on a finite segment** | Within a quarter period the phase turns `w e^{iγt}` to real part `≥ |w|/2`; a bounded remainder plus `2 Re(w e^{(δ+iγ)t})`, `w ≠ 0`, `δ > 0`, `γ ≠ 0`, exceeds every budget at arbitrarily large scales, before `log((|K| + |B| + 1)/|w|)/δ + π/(2|γ|)`. | `exists_abs_re_ge_half`, `exists_gt_abs_of_hyperbolic` |
| **P13 Separation is hyperbolic** | Diagonal isometries of the local form are `(au, bv)` with `a b̄ = 1`; they separate the two points iff they are boosts; antidiagonal isometries `(λv, μu)` have `λ μ̄ = 1`, square to a unimodular scalar, and fix positive lines. | `diagonal_isometry_iff`, `diagonal_isometry_separates_iff`, `antidiagonal_isometry_iff`, `antidiagonal_isometry_sq`, `localForm_swap_fixed`, `separating_isometry_is_boost` |
| **P14 Sparse annihilators need a lattice** | A nonzero polynomial with `K` monomials vanishes to order `< K` at every nonzero point; `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = ½` and `N Im ρ log p ∈ 2πℤ`; it never kills an off-line symbol. | `rootMultiplicity_lt_card_support`, `heckeSymbol_pow_eq_one_iff`, `heckeSymbol_pow_ne_one_of_re_ne` |
| **P15 The Rankin–Selberg square sees the field of the other zeros** | For a finite polar source `F = Σ m_j/(s − z_j)`, `F² = Σ m_j²/(s − z_j)² + Σ 2m_j E_j/(s − z_j)` with the field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`; on critical configurations `Re E_j = 0`; at the deepest off-line point with its reflection present `Re E_j > 0`. | `sq_sum_eq_partial_fractions`, `re_fieldAt_eq_zero_of_critical`, `re_fieldAt_pos_of_deepest` |
| **P16 The selectivity battery** | Real points resonate at every prime (symmetric Hecke positivity is blind to them); the spectral sign sees a real symbol `β ≠ ±1` through the negative value `−(β − β⁻¹)²/4` and a non-real symbol off the unit circle through a non-real value; kernel counts see real pairs and miss complex quartets (P3). | `real_point_resonant_at_every_prime`, `symSquare_neg_of_real`, `symSquare_not_real_of_nonreal` |
| **P17 Symmetric-square contractions and exterior kernel counts** | Without reading the spectrum: on any curve datum, exterior-power kernel counts `exteriorDetDeg D k (C c ∓ X)` (`1 ≤ k ≤ |ι|/2`, `c > (√q)^k`) are nonnegative on unitary data, evaluate to `−665379 < 0` on `complexFake` at `k = 2, c = 17`, and force unitarity across all genera; vertical correspondence symmetric squares `(1 + c²)φ(u) − c φ(u + h) − c φ(u − h)` preserve `IsEvenPosDef` (and both `goldenDatum` and `complexFake` have `IsEvenPosDef` vertical zeta sections on `σ > 1`, whereas `CompletedPositiveSystem 1 d` collapses to `ℝ^× · ζ`); over `ℤ`, the archimedean midpoint symmetric-square multiplier `M_β(s) = (s − ½)² / ((s − β)(s − (1 − β)))` has Laplace density `e^{−σt}(e^{βt/2} − e^{(1−β)t/2})² ≥ 0`, contracts any real off-critical pair of `CompletedPositiveSystem κ d` onto `1/2` at `Δκ = 0`, eliminates all real off-critical zeros in finitely many steps, forces `Λ(β) ≠ 0` (`β ≠ 1/2`) at `κ = 1` by self-similarity in `ℝ^× · ζ`, and its pole-paid quartet analogues contract any complex off-critical quartet onto `{1/2, 1/2 ± iγ}` at `Δκ = 1` (`a ≤ 1/4`) and `Δκ = 2` (`0 < a < 1/2`). | `exteriorDetDeg_linear_nonneg_of_unitary`, `unitary_of_exteriorDetDeg_nonneg`, `complexFake_exteriorDetDeg_two_seventeen`, `IsEvenPosDef.symSquareShift`, `symSquareShift_cos`, `isEvenPosDef_goldenDatum_verticalSection`, `isEvenPosDef_complexFake_verticalSection`, `archSymSquare_neg_eq_sq`, `isEvenPosDef_midpointSymSquare`, `CompletedPositiveSystem.contractRealPair`, `CompletedPositiveSystem.exists_real_offCritical_free`, `completedPositiveSystem_one_ne_zero_of_midpoint_contraction`, `CompletedPositiveSystem.contractComplexQuartet_of_le_quarter`, `CompletedPositiveSystem.contractComplexQuartet` |
| **P18 The cofactor Gram is a translation Gram** | With the log profile `g(u) = e^{−u/2} v(⌊e^u⌋)`, `⟨D_j v, D_k v⟩_T = (√j √k)⁻¹ ∫_0^{log(T+1)} g(u − log j) g(u − log k) du` exactly: dilation is translation, the pronic measure is Lebesgue measure on the log scale. Exponential profiles give power characters. For `v = h + r`, `|⟨D_j v, D_k v⟩ − ⟨D_j h, D_k h⟩| ≤ ‖r‖(‖v‖ + ‖h‖)`, so a remainder with `‖r‖/‖v‖ → 0` does not change escape states; Grams of finite combinations are bilinear. | `pronicPairing_rowDilate_eq_translationGram`, `translationGram_exp`, `abs_pairing_rowDilate_sub_le`, `tendsto_normGram_sub_of_subdominant`, `pronicPairing_rowDilate_sum` |
| **P19 The Laplace symbol of the cofactor** | For the prefix `A` of any coefficients, `∫_0^{log(N+1)} A(⌊e^u⌋) e^{−su} du = (Σ_{n≤N} a(n) n^{−s} − A(N)(N+1)^{−s})/s` (Abel summation on the cells); the centered damped divisor coefficients have `Σ c̃_ε(n) n^{−s} = ζ(s)/ζ(s + ε) − Re(1/ζ(1+ε)) ζ(s)`; the Laplace transform of the cofactor profile is `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s` on `Re s > 1`, whose singularities right of `½` are the translated zeros `ρ − ε` (the pole at `1` is cancelled by the centering). | `sum_prefix_diff`, `integral_prefix_exp_eq`, `divisorCoeff_eq_convolution`, `LSeries_centeredDivisorCoeff`, `tendsto_laplace_cofactorProfile` |
| **P20 The escape rank counts the dominant zeros** | For a dominant configuration `F = Σ_k c_k e^{(x + i y_k)u}` (`x > 0`, `y_k` distinct) the horizon law `e^{−2xL} ∫_0^L F(u−a)F̄(u−b) = K_{θ(L)}(a,b) − e^{−2xL} K_1(a,b)` is exact, with phase kernels `K_θ = Σ_{k,l} (c_kθ_kψ_k(a)) conj(c_lθ_lψ_l(b))/(2x + i(y_k − y_l))`; every escape state is some `K_θ`, `|θ_k| = 1`; the Cauchy form is `∫_0^∞ e^{−2xt}|Σ v_k e^{−iy_kt}|² dt`, positive for `v ≠ 0`; the null space of every `K_θ` is the annihilator of the characters `ψ_k`, which at `a = log j` are the independent power characters `j^{−(x+iy_k)}`. So every escape state has rank exactly the number of dominant zeros, for every phase. | `exp_mul_hermGram_eq`, `exists_tendsto_escapeKernel`, `cauchyForm_eq_integral`, `eq_zero_of_expSum_eq_zero`, `integral_cauchyDensity_pos`, `escapeForm_eq_cauchyForm`, `escapeForm_eq_zero_iff`, `escapeKernel_self_pos`, `transChar_log`, `linearIndependent_powChar`, `escapeForm_log_eq_zero_iff` |
| **P21 Horizon averages select the zeros** | `K_{θ(L)} = Σ D_{kl} e^{i(y_k − y_l)L}`; `|∫_0^T e^{iωL}| ≤ 2/|ω|`; the average `T⁻¹∫_0^T K_{θ(L)} dL` is within `(2/T) Σ_{k≠l} |D_{kl}|/|y_k − y_l|` of the diagonal kernel `Σ_k c_kψ_k ⊗ conj(c_kψ_k)/(2x)`, and the horizon averages of the scaled Grams tend to it. | `escapeKernel_phase`, `norm_integral_phaseExp_le`, `norm_avg_escapeKernel_sub_le`, `tendsto_avg_escapeKernel`, `tendsto_avg_gram` |
| **P22 On escape states dilation is the archimedean flow** | `ψ(a + t) = ψ(t)ψ(a)`; `K_θ(a + t, b + t) = e^{−2xt} K_{θ e^{−iyt}}(a, b)`; along the horizons `K_{θ(L)}(a + log p, b + log p) = p^{−2x} K_{θ(L − log p)}(a, b)`. | `transChar_add`, `escapeKernel_shift`, `escapeKernel_phase_shift`, `escapeKernel_phase_dilate` |
| **P23 Every family average loses linearly** | For probability weights and `z ≥ 0`, `(Σ w z)^k ≤ Σ w z^k`, so any bound `Σ w z^k ≤ B_k` has `k log(Σ w z) ≤ log B_k`; equality at `k = 2` iff `z` is constant on the support; on a curve datum flatness of `|β_i|` is unitarity; the golden datum is not flat. | `family_moment_le`, `mul_log_mean_le_log_bound`, `sq_mean_eq_mean_sq_iff`, `curveDatum_flat_iff_unitary`, `goldenDatum_not_flat` |
| **P24 The power rows of the zeros are dominant configurations** | `0 ≤ u − log⌊e^u⌋ ≤ 2e^{−u}` and `|⌊e^u⌋^z − e^{zu}| ≤ 4|z|e^{(Re z−1)u}`; on a line `Re z_k = ½ + x` the log profile of `Σ_k Re(c_k n^{z_k})` is within `K e^{(x−1)u}` of `Σ_k Re(c_k e^{(z_k−½)u})`, which is the dominant configuration with frequencies `±Im z_k`; profiles that close have scaled Grams within `M L e^{−min(2x,1)L}`; so along any horizons a subsequence of the scaled cofactor Grams of the row converges, for all dilations at once, to a phase kernel of that configuration. | `sub_log_floor_exp_le`, `norm_floor_cpow_sub_le`, `abs_logProfile_powerSum_sub_le`, `tendsto_scaled_gram_sub`, `tendsto_scaled_rowGram_sub`, `domProfile_append_eq`, `hermGram_append_eq`, `exists_tendsto_powerSum_escapeKernel` |
| **P25 Exterior and height-coupled zero-tax quartet contractions** | Post–Widder scale-weight positivity on finite conjugation-symmetric polar sums forces the **real-anchor law**: any `Δκ = 0` cancellation of a rightmost non-real pole `σ_max + iγ₁` must simultaneously cancel a real pole at `σ_max` of weight `c(σ_max) ≥ c(σ_max + iγ₁)` (`≥ 2 c(σ_max + iγ₁)` for a single ordinate), ruling out pure quartet ratios at `Δκ = 0`. Two phase-colliding couplings achieve `Δκ = 0`: (i) the functorial exterior power `CurveDatum.exterior D 2` and archimedean exterior-square divisor `exteriorTwoDivisorPoly` (`2 Λ²z_ρ(t) = z_ρ(t)² − z_ρ(2t)`) send `{1/2 ± a ± iγ}` to `realPairPoly(1/2 + 2a) · (s − 1/2)²((s − 1/2)² + 4γ²)`, contracting at `Δκ = 0` for `0 < a < 1/4`; (ii) `coupledQuartetSymSquare b a γ` attains the sharp `2 : 1` real-anchor bound with Laplace density `2e^{t/2}((e^{bt/2} − e^{−bt/2})² + cos(γt)(e^{at/2} − e^{−at/2})²) ≥ 0` across all `0 < a ≤ b < 1/2`, and lifting any `CompletedPositiveSystem κ d` to `HeightCoupledSystem (2κ) κ d γ` (`F_γ(s) = F(s)² F(s+iγ) F(s−iγ)`) collides `(±iγ) ↦ 0` onto `1/2 + a ∈ ℝ` with multiplicity `2`, contracts arbitrarily many ordinate-`γ` quartets at `Δκ₀ = 0, Δκ_γ = 0` under a fixed Hadamard–digamma budget (`8 ∑_{a ∈ A} ord_{1/2+a+iγ}(Λ) + 4 ord_{1/2}(Λ) + 4 ord_{1/2+iγ}(Λ) < 18κ + 3d log(3+|γ|) − (7/2)d`), and terminates in finitely many steps. | `posDef_polarSum_laplaceWeight_nonneg`, `real_anchor_of_posDef_polarSum`, `two_mul_le_real_anchor_of_single_ordinate`, `not_isEvenPosDef_quartetPureRatio`, `CurveDatum.exterior`, `detDeg_exterior_eq_exteriorDetDeg`, `quartetCurveDatum_exterior_two_spectrum`, `exteriorTwoScaleTrace_eq_newton`, `exteriorTwoDivisorPoly_quartet_contract`, `isEvenPosDef_coupledQuartetSymSquare`, `CompletedPositiveSystem.contractComplexQuartet_of_doubleRealAnchor`, `CompletedPositiveSystem.contractComplexQuartet_of_singleDeepRealAnchor`, `CompletedPositiveSystem.heightCouple`, `HeightCoupledSystem.contractCollidedQuartet`, `CompletedPositiveSystem.contractComplexQuartet_heightCoupled`, `HeightCoupledSystem.archimedean_budget`, `CompletedPositiveSystem.contractOrdinateQuartets_heightCoupled`, `CompletedPositiveSystem.ordinateQuartet_multiplicity_archimedean_bound`, `HeightCoupledSystem.exists_real_offCritical_free` |
| **P26 Infinite dominant configurations are complete** | For `v ∈ ℓ¹` and distinct `y_k`, an exponential series `Σ v_k e^{−iy_kt}` vanishing on `t > 0` has `v = 0` (Bohr uniqueness: means over `[0,T]` by dominated convergence of the series); the Cauchy form `Σ_{k,l} v_k v̄_l/(2x + i(y_k − y_l))` is `∫_0^∞ e^{−2xt}|S(t)|²`, positive for `v ≠ 0`; for `F = Σ_k c_k e^{(x+iy_k)u}`, `c ∈ ℓ¹`, the horizon law holds, every escape state is a phase kernel over the compact torus `(S¹)^ℕ`, and its null space is the annihilator of all the characters `ψ_k`. | `eq_zero_of_expSeries_eq_zero`, `cauchyFormSeries_eq_integral`, `integral_cauchyDensitySeries_pos`, `exp_mul_hermGram_series_eq`, `exists_tendsto_escapeKernelSeries`, `escapeFormSeries_eq_zero_iff` |
| **P27 The escape completeness criterion** | For `v = Σ_k Re(c_k n^{z_k}) + r`, `Re z_k = ½ + x`, distinct `±Im z_k`, `c ≠ 0`, `‖r‖_T/‖v‖_T → 0`: along a subsequence of any horizons the normalized cofactor Grams `⟨D_j v, D_k v⟩_T/‖v‖_T²` converge, for all `j, k`, to `K_θ(log j, log k)/(√j √k K_θ(0,0))`; phase kernels are bounded uniformly in the phase and `K_θ(a + t, b + t) → 0`, so their critical (gauge-torus) kernel vanishes. | `exists_tendsto_normGram_of_dominant_split`, `tendsto_norm_ratio_of_subdominant`, `norm_escapeKernel_le`, `tendsto_escapeKernel_shift_zero` |
| **P28 The escape alternative** | An uncancelled zero (`ζ(ρ) = 0`, `½ + ε < Re ρ < 1`, `ζ(ρ − ε) ≠ 0`) makes the energy `O(T^κ)` for no `κ < 2(Re ρ − ε) − 1`, in particular unbounded; an escaping damping has `ε ≤ Θ − ½`; the cancelling dampings form a countable set; every `ε ∈ (0, Θ − ½)` outside it escapes; RH ⇔ the receiver admits at every `ε > 0` (the receiver-boundedness form of this equivalence is THIM's `riemannHypothesis_iff_forall_pos_receiverBounded_moebius`). | `not_energy_le_rpow_of_uncancelled_zero`, `not_admits_of_uncancelled_zero`, `le_of_not_admits`, `countable_cancellingDampings`, `not_admits_of_mem_Ioo_of_not_mem`, `riemannHypothesis_iff_forall_admits` |
| **P29 A section count is the sign** | For a count `h⁰` with effective classes `{h⁰ > 0}`: Riemann–Roch (`x² > 0 ⇒ h⁰(x) > 0 ∨ h⁰(−x) > 0`) alone is satisfied by `h⁰ ≡ 1` and Bézout (effective classes meet nonnegatively) alone by `h⁰ ≡ 0`; sections at `x` and `−x` with `x² > 0` violate Bézout; both together hold for some count iff the Hodge index holds, on every polar surface; over `ℤ` this is RH, over `𝔽_q` purity, and the golden datum has no such count on some window. | `sectionRR_const`, `sectionBezout_zero`, `not_sectionBezout_of_symm`, `hodgeIndex_iff_exists_sectionCount`, `riemannHypothesis_iff_exists_sectionCount`, `forall_window_exists_sectionCount_iff_unitary`, `goldenDatum_not_forall_window_exists_sectionCount` |
| **P30 The Stepanov count is the sign** | RH iff the prime-power count obeys the one-sided bound `ψ(x) − x ≤ C √x log²x` for large `x` (Bombieri's one-sided principle over `ℤ`, from the corpus von Koch theorems); an auxiliary `1 − T_p^N` kills the symbol of `ρ` only if `Re ρ = ½` and `N Im ρ log p ∈ 2πℤ`. | `riemannHypothesis_iff_one_sided_count`, `hecke_auxiliary_kills_only_critical` |
| **P31 Intrinsic exterior obstructions, sharp minimum anchor cost, and Fejér entry-cost halving** | Local degree-`1` Adams exterior squares vanish; on isobaric shift packets `1^{⊕ m₀} ⊕ |·|^{±iγ}` (`g_{m₀}(θ) = m₀ + 2 cos θ`), `(g_{m₀}(θ)² − g_{m₀}(2θ))/2 = (m₀² − m₀ + 2)/2 + 2 m₀ cos θ` cancels `cos 2θ` (`m₀ = 0` has zero collision, `1 ≤ m₀ ≤ 4` fails nonnegativity at `π`, `m₀ ≥ 5` keeps `κ_γ = m₀ κ ≥ 5κ > 0` at ratio `≥ 11/5 > 2`), while scale-space bilinear squaring puts cross-singularities at `1 + a + iγ` (`Re > 1`). Multiplying `HeightCoupledSystem κ₀ κγ d γ` by `boundaryTwistFactor γ ^ κγ` unconditionally absorbs shifted poles (`κ_γ ↦ 0`) on the exact same `Λ` at `κ₀ + 2κ_γ` (minimal by `total_zero_mass_le`), whereas keeping `κ_γ = κ` saves `3γ²(γ²+3)κ/((4+γ²)(1+γ²)) > 0` at `s = 2` and halves P25's `18κ` pole ceiling to `(9 + 12/(4+γ²) + 6/(1+γ²))κ → 9κ`. At `κ_γ = 0, Δd = 0`, `plantDoubleRealAnchor` plants a weight-`2` real anchor at `Δκ = 2` (minimal among zero-planting polar sums), and functor-independently any `CompletedPositiveSystem κ d` with `M` weight-`2` anchored quartets obeys `16M + 144M/(9+4γ²) + 4 ord_{1/2}(Λ) + 72/(9+4γ²) ord_{1/2+iγ}(Λ) + 5d < 9κ` (`κ ≥ 3` for `M = 1, d ≥ 1`). Across degree-`K` nonnegative cosine shift multipliers with `c₁ ≥ 2`, discrete Fejér–Egerváry–Szász quadrature forces `c₀ ≥ 1/cos(π/(K+2)) > 1` with two-sided shifted-Gamma cost `∈ [d(log(3+|γ|) − 5), d(log(3+|γ|) + 1/2)]` per unit pair, while `FejerCoupledSystem K` achieves `Δκ = 0` quartet contraction at normalized central pole cost `(9(K+1)/(2K))κ ↘ (9/2)κ` (`27/4 · κ < 8κ` at `K = 2`). | `degreeOne_exteriorTwo_eq_zero`, `isobaricExteriorTwoPoly_eq`, `isobaricExteriorTwoPoly_pi_neg`, `isobaricExteriorTwoPoly_nonneg_of_five_le`, `isobaricExteriorTwoPoly_ratio_ge`, `centeredScaleCross_re_gt_one`, `isEvenPosDef_boundaryTwistFactor`, `HeightCoupledSystem.absorbShiftedPoles`, `two_mul_le_origin_of_poleCancelling_posDef`, `HeightCoupledSystem.archimedean_budget_exact`, `CompletedPositiveSystem.ordinateQuartet_multiplicity_ordinate_decay_bound`, `CompletedPositiveSystem.plantDoubleRealAnchor`, `two_le_pole_cost_of_doubleRealAnchor_polarSum`, `CompletedPositiveSystem.anchored_quartet_pole_lower_bound`, `CompletedPositiveSystem.three_le_pole_of_anchored_quartet`, `fejer_egervary_szasz_first_harmonic_le`, `cosine_multiplier_anchor_cost_lower`, `re_logDeriv_Gammaℝ_pair_two_sandwich`, `IsEvenPosDef.fejerShift`, `FejerCoupledSystem`, `CompletedPositiveSystem.fejerCouple`, `FejerCoupledSystem.contractCollidedQuartet`, `CompletedPositiveSystem.fejerOrdinateQuartet_bound`, `CompletedPositiveSystem.fejerTwo_ordinateQuartet_bound`, `tendsto_fejer_central_pole_coeff` |
| **P32 The successor defect in the strip** | `q(x+1)^{q−1} ≤ (x+1)^q − x^q` for `0 < q ≤ 1` (concave Bernoulli); `Σ_{n<M}(n+1)^{−β} ≤ M^{1−β}/(1−β)`; each defect term is at most `2Λ(n+1)(n+1)^{−σ}` and at most `|s|Λ(n+1)(n+1)^{−σ−1}`; splitting at `M ≈ |s|` with `Λ(n) ≤ n^η/η` gives, for `0 < η < σ < 1` and `Re s = σ`, `|D_Λ(s)| ≤ (4/(η(1+η−σ)) + 2/(η(σ−η)))(|s| + 1)^{1−σ+η}`: growth of exponent `1 − σ + η` in the height, not linear. | `mul_rpow_sub_one_le_rpow_sub`, `sum_range_rpow_neg_le`, `norm_succShiftTerm_le_two`, `norm_vonMangoldtC_le`, `norm_succShiftDefect_vonMangoldt_le_rpow` |
| **P33 The first gauge-charged window off the edge** | For odd `C²` tests supported in `[−181/500, 181/500]`, the atom `Re(k(log 2) + k(−log 2))` only sees the edge strips `E = {log 2 − 181/500 ≤ |x|}` (width `≈ 0.031`): `|atom| ≤ 2∫_E F²`; hence the Liouville twin (Λ(2) flipped) satisfies `W_λ(F) ≥ (1/1000)∫F² − 2√2 log 2 ∫_E F²` and is Weil-positive on every test with `1961 ∫_E F² ≤ ∫F²`. | `abs_mul_le_edge`, `abs_integral_shift_le_edge`, `abs_atom_le_edge`, `re_weilFullFunctional_liouvilleTwist_ge_sub_edge`, `re_weilFullFunctional_liouvilleTwist_nonneg_of_edge_le` |
| **P34 Elliptic localization is resonance** | At an off-line point the symmetric dilation by `a > 1` is elliptic iff `γ log a ∈ πℤ`, i.e. `a ∈ exp((π/γ)ℤ)`; one non-resonant scale makes a real even carrier blind there; carriers closed under the archimedean flow (all `a > 1`) are blind at every non-real off-line point; if every closure scale is resonant, the fibre `z = 1` survives as a positive non-isotropic fibre. | `symHeckeSymbol_im_ne_zero_iff`, `sin_mul_log_eq_zero_iff`, `eq_zero_of_nonresonant_scale`, `exists_nonresonant_scale`, `eq_zero_of_archimedean_closed`, `resonant_survivor` |

---

## 6. The questions and their answers

1. **What replaces `C × C`?** A correspondence surface: the scaling surface of `ℤ` with the Hecke
   algebra of `ℝ_{>0}` (AOG's scaling datum). It carries the Lefschetz sequences
   `c_m^{(p)} = τ_x(T_p^m)` as Rosati traces, the adjunction and Rosati identities, normalized graphs
   with their theorem of the square (P1) and a fixed budget (P2). The Hodge index on its spans is RH
   (F2, AOG). What it lacks is not a space but a sign.
2. **Is there a theorem of the square over `Spec ℤ`?** Yes: the normalized graph map of the
   correspondence ring is quadratic, unique modulo fibres, of degree half the Rosati trace (P1). No:
   for the scale map `a ↦ T_a`, which adds scales instead of ring elements (F4). Either way it
   carries no budget: the golden datum has it and a graph of degree `−1`.
3. **What is the budget?** The self-defect `δ(x, x)` of a cycle: `2g` for the diagonal of a curve,
   the Weil norm of a test over `ℤ`; constant along every orbit by the similitude law (P2), and every
   finite budget self-improves to it (F7). It is neither a section count nor a torsion order: a
   section count with Riemann–Roch and Bézout exists exactly when the sign holds (P29). Its
   sufficiency at one scale is the positivity of the graphs of `1 ± T`; at every level of a curve it
   is unitarity, and for `ζ` it is RH.
4. **Which positivity is gauge charged and not isotropic?** Isotropy is forced by hyperbolic local
   symmetry, and every multiplicative correspondence — Hecke, archimedean, twisted — is hyperbolic at
   every off-line pair (P4, P5); the only elliptic multiplicative fibres off the line are resonant,
   at one prime at most (P4). The successor is unipotent and constrains nothing (P5). Positivity beyond
   isotropy exists, at bounded aperture, but does not localize and holds for every prime weight
   (P6). On nonnegative tests positivity is an upper-bound statement shared by every dominated twin
   (P7). The answer: a `ζ`-specific positivity beyond isotropy must localize at off-line pairs, have a
   non-hyperbolic local symmetry there (reflection type), and live on sign-changing autocorrelations.
   No such carrier is known; each carrier treated here fails one of the three conditions. The
   Rankin–Selberg source `Λ ⋆ Λ`, the report's first candidate, is non-local at the polar level: its
   residue at a zero is the field of all the other zeros, which vanishes transversally when every
   zero is critical and is positive at the deepest off-line zero (P15) — a spectral quantity that
   its multiplicative structure (an external square) does not see.
5. **How are the archimedean and finite places coupled?** Positivity on `ℚ_{>0}` splits them
   (APD `kronecker_decomposition`); integer and Bost–Connes successors see only Kronecker-null
   spectra (`integer_successor_kronecker_null`); atomic archimedean spectra blind every successor
   (`successor_blind_of_atomic_archimedean`); continuous archimedean spectra are seen by the real
   successor (`successor_sees_autocorrelation`). The zeros are atoms of the archimedean spectrum, and the successor is
   unipotent on their polar fibres (P5): additive coupling reaches the continuous part and never the
   zeros. A coupling that sees zeros must act on the atoms, hyperbolically (forcing isotropy) or by
   reflection (elliptic). One structure keeps the places coupled: escape states. They are not
   functions on `ℚ_{>0}` — they carry the weight `(jk)^{−x}` of the dominant zeros and a phase — and
   on them dilation by `p` is the archimedean flow back by `log p`, scaled by `p^{−2x}` (P22). The
   coupling is exact but it is not a positivity on the multiplicative group: it lives in the weight
   and the phase that a dilation-invariant kernel does not have.
6. **What pays `ζ`'s own zeros?** Along any Hecke orbit an off-line pair contributes a hyperbolic
   term growing at the rate of its depth while critical zeros contribute rotations (P4, F8); a fixed
   budget pays an off-line pair only on a segment of length `≍ log(budget/weight)/depth` (P12), and
   Weil's inequality fails at every large `m` for the test that sees it (ACS
   `OffLineZerosAreLefschetzRatios`). At bounded aperture,
   intrinsic charge is paid by domination with capacity the archimedean horizon count (ACS
   `hodgeDefectAt_zeta_le_shannon`), and that positivity is source-blind (P6). Oscillatory payment
   has a capacity in the escape model: the rank of an escape state is the number of dominant
   translated zeros, independently of the phase (P20), so the integer that counts intrinsic charge on
   the dominant line is an escape rank, read from a positive semidefinite kernel. It counts the
   zeros of maximal depth only; a capacity uniform in the depth is what RH asserts.
7. **What are escape states?** Normalized limits of translation Grams of one log profile (P18),
   whose Laplace transform is `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s` (P19). For a dominant
   configuration they are exactly the phase kernels `K_θ` over the orbit closure of the horizon
   phases, positive semidefinite of rank the number of dominant zeros, with null space the
   annihilator of the translated-zero characters `j^{−(ρ−ε)}` (P20); their horizon averages are the
   diagonal kernel, one rank-one term per zero (P21); dilation acts on them as the archimedean flow
   (P22). Remainders of subdominant energy do not change them (P18). ADR adds the finite windows
   (translated zeros with multiplicity) and the converse at finite rank (F10); ACG reads every
   escape state as a measure on the gauge torus, zero for power-type growth (F11).
8. **What is the base?** At the level of receivers, exactly a fixed-loss bound for the tensor powers
   of one orbit correlation (P8): linear loss gives the strip and nothing more, sublinear or fixed loss
   gives RH. Multiplicative amplification loses linearly (ACG gauge Jensen), relative powers of `ζ`
   are `ζ` (ACG), and the golden datum loses `log φ` per power (P8). A base must come from a structure
   whose cost does not scale with the power. Family averages — characters mod `q`, archimedean
   windows, any finite family of twists — lose linearly too, and lose nothing only on a flat family,
   which on a curve is a pure one (P23): averaging is not a base.
9. **How does an average become a point?** Averaging over heights or along orbits averages the
   elliptic phases of critical zeros and never isolates a fibre; isolation needs hyperbolic growth
   (an off-line zero's own) or length: a correspondence of length `L` resolves heights `≍ 1/L`, and
   separating two critical zeros at distance `δ` costs a derivative `≥ 1/(Lδ)` (P11); modulation
   moves fibres instead of acting on them. At the zero spacing this is the persistence scale `1/A`
   of ACG with `A ≍ log T`. On escape states an average does become a sum of points: the horizon
   average of the escape states of a dominant configuration is the diagonal kernel
   `Σ_k (|c_k|²/2x) ψ_k ⊗ ψ̄_k`, each zero with its own mass, within `(2/T) Σ_{k≠l}|D_{kl}|/|y_k − y_l|`
   (P21) — selection at the zero-spacing scale, with a window longer than the inverse spacing.
   Selection below the zero spacing is RH-strength (B1.4).
10. **How are shared resources paid?** The Rosati trace form is one budget for the whole ring;
    frustration is its negative index, which counts the seen off-line zeros (AOG). On configurations
    the shared budget is decided by two-term spans at all scales because hyperbolic growth exposes
    every seen pair (AOG orientation theorem); on finite windows it is not (mimics).

**The report's three questions.** Q3 (a theorem of the square over `Spec ℤ`): answered by P1, with
the conclusion that it carries no budget. Q2 (positivity beyond isotropy): answered in sharp form by
P4, P5, P6 and P7 — it exists only without localization or without source; localizing
multiplicative carriers are isotropic, additive closure is unipotent. Q1 (escape completeness) has
two halves. *Escape at `ε` is exactly the presence of zeros right of `½ + ε`* (P28): an uncancelled
zero there forces escape, escape forces `ε ≤ Θ − ½`, every damping below `Θ − ½` outside a
countable set escapes, and RH holds iff no damping escapes — so under RH completeness is empty.
*The escape states are generated by translated zeros* for every dominant configuration, and for
`ζ` exactly when its profile splits. The cofactor Gram
is a translation Gram of the log profile (P18), whose Laplace symbol is `G` (P19); escape states do
not see remainders of subdominant energy (P18); the escape states of a dominant configuration are
phase kernels of rank exactly the number of its frequencies, generated by the characters
`j^{−(ρ−ε)}` for every phase (P20), and the same holds for absolutely summable configurations with
infinitely many dominant zeros (P26); the power row `Σ_k Re(c_k n^{ρ_k−ε})` of `r` dominant
translated zeros has exactly these escape states, the configuration with frequencies `±Im ρ_k`, of
rank `2r` when the `ρ_k` are distinct with `Im ρ_k > 0` (P24). With ADR's finite-rank theorem
(F10) — rows obeying finite-rank dilation laws are such sums plus finite energy — finite-rank escape
is classified: it is carried by finitely many dominant translated zeros, each seen through its pair
of characters. P27 states this in ADR's normalization: a row that splits into such a power row and
a subdominant remainder has as escape states the normalized phase kernels
`K_θ(log j, log k)/(√j √k K_θ(0,0))`, whose critical kernel vanishes — the ACP side of ACG's zero
gauge mass for power-type escape. What remains for `ζ` is the split of its cofactor profile into a
dominant configuration and a subdominant remainder: an explicit formula for the damped Möbius
prefix, i.e. a contour shift of `G(s)e^{su}` past the translated zeros, which needs growth bounds
for `1/ζ(s + ε)` on horizontal segments between zeros. That input is analytic and of the type the
explicit formula for `M(x)` needs; it is not a positivity statement, and no further correspondence
structure decides it.

**The report's mechanisms and milestones (§4.6).**

| Mechanism | Outcome in ACP |
|---|---|
| Budget law | the theorem of the square is free and the self-defect is constant along every orbit (P1, P2): the budget exists; its sufficiency is RH; a section count with Riemann–Roch and Bézout is the Hodge index, RH over `ℤ` and purity over `𝔽_q` (P29) |
| Charged positivity law | sharp no-go: localizing multiplicative carriers are hyperbolic, hence isotropic (P4, P13); the successor is unipotent (P5); non-localizing positivity is source-blind (P6); positivity on nonnegative tests is shared by every dominated twin (P7) |
| Coupling law | positivity on `ℚ_{>0}` splits the places (APD); on escape states dilation is the archimedean flow (P22) |
| Capacity law for oscillation | the escape rank is the number of dominant zeros (P20, P24); a fixed budget pays a hyperbolic pair only on a finite segment (P12) |
| Completeness law for escape | complete for dominant configurations, their power rows and summable infinite configurations (P20, P24, P26); for `ζ` reduced to the explicit-formula split of the profile with symbol `G` (P18, P19) |
| Base law | the base is a fixed loss; linear loss is the strip (P8); family averages lose linearly, flat families are pure (P23) |

| Milestone | Outcome |
|---|---|
| (1) W8 and escape completeness or a counterexample | W8 is P18 with the symbol P19; completeness for dominant configurations is P20, P24 and P26 |
| (2) positivity on `Λ ⋆ Λ` or an affine carrier, or universal isotropy | the polar residue of `Λ ⋆ Λ` is the field of the other zeros (P15); affine correspondences have genus zero (P9); isotropy is universal on localizing multiplicative carriers (P4, P13) |
| (3) a theorem of the square for an enlarged ring, or a no-go | P1: it holds for the ring, fails for scales, and carries no budget |
| (4) the loss law for the remaining amplification classes (W9) | tensor powers (P8), family averages (P23) and gauge moments (ACG) all lose linearly; zero loss is flatness, which over `𝔽_q` is purity |
| (5) the `κ = 1` class collapse (W11) | `CompletedPositiveSystem 1 d` collapses to `ℝ^× · ζ`, and midpoint contraction with `κ = 1` self-similarity excludes real off-critical zeros (P17) |
| (6) archimedean–finite coupling for continuous spectra (B3.23) | continuous archimedean spectra are seen by the real successor (APD `successor_sees_autocorrelation`); on escape states the coupling is exact (P22) |

---

## 7. Traps

| Trap | Truth |
|---|---|
| The theorem of the square is the missing algebraic precondition | It is an identity of normalized graphs and holds on the golden datum (P1) |
| Hecke scales failing the parallelogram law means no theorem of the square | Scale addition is not ring addition (F4 vs P1) |
| A fixed budget is what `ℤ` lacks | The budget is fixed by the similitude law; its sufficiency is RH (P2) |
| Counting kernels on `H¹` gives the sign | Only in genus one; the complex fake passes every `H¹` kernel count (P3); exterior-power counts force unitarity (P17) |
| Positive point counts are a weak form of Weil | The golden datum and the complex fake have them (AKT, P3) |
| Isotropy is a defect of the carriers studied so far | It is forced by any hyperbolic local symmetry, and every multiplicative correspondence is hyperbolic off the line (P4, P5) |
| An elliptic symmetry could localize at one point of a pair | Local isometries separate the two points only as boosts (P13) |
| One prime may leave an off-line zero invisible forever | It resonates at one prime at most; two primes see it (P4) |
| The successor couples the zeros to additive structure | It is unipotent on their polar fibres (P5) |
| Positivity on a carrier with full fibres excludes zeros | Only if the carrier localizes; at bounded aperture it holds for every prime weight (P6) |
| A positivity proof on nonnegative tests can be specific to `ζ` | It proves the same for every dominated twin (P7) |
| Tensor powers amplify a weak bound into RH | Only with sublinear loss; linear loss returns the strip (P8) |
| Affine (gauge-charged) correspondences carry a Lefschetz spectrum | They have genus zero: at most one periodic point, graphs meet at most once (P9) |
| Kernel counts of symmetric squares see the sign | They are squares; only the spectrum of `f f′` does (P10) |
| A long enough average isolates a zero | Only a correspondence of length `≳` the inverse spacing does (P11) |
| A non-commutative (affine) carrier adds positivity | Induced from the dilations unless the successor is prescribed (APD) |
| Rosati positivity at one cycle is weaker than RH | For the spline it is RH (P1) |
| Escape completeness needs a new positivity | It is an energy split: remainders of subdominant energy are invisible (P18), and dominant configurations are complete with rank the number of zeros (P20) |
| An escape state is a positive-definite function on `ℚ_{>0}` | It carries the weight `(jk)^{−x}` and a phase; dilation acts on it as the archimedean flow (P22) |
| Averaging over horizons blurs the zeros | It separates them: the horizon average of escape states is diagonal, one term per zero (P21) |
| Averaging a family of twists is a base | Family averages lose linearly; only flat (pure) families lose nothing (P23) |

---

## 8. Tools

Built in sibling programmes: polar surfaces, curve data, the golden datum, scaling data, the
correspondence algebra with Rosati and Hecke graphs, coupled isotropy and the left-blind ideal,
positive-definite functions on `ℚ_{>0}` and `Aff(ℚ)`, the gauge torus, escaped pairings, the
window certificates, characteristic-zero Stepanov.

The tools the report asks for (§4.5), with what ACP has built for each:

| Tool | Built | Pillars |
|---|---|---|
| Correspondence intersection theory over `ℤ` | normalized graphs, their degree calculus and the free theorem of the square; the similitude law and budgets on Weil planes; determinant, Rosati, spectral and exterior degrees of curve data; affine graphs, their periodic points and intersections | P1, P2, P3, P9, P10, P17 |
| Gauge-charged positivity | the local form with boosts, rotations and its isometries; Hecke, symmetric Hecke, twisted and archimedean symbols; the resonance law; the transform `mellinAt` of real tests; aperture probes; the successor defect; the Weil functional affine in the source, dominated and flipped twins; the Rankin–Selberg field | P4, P5, P6, P7, P13, P15, P16 |
| Loss-law calculus | root extraction and the loss of tensor powers; the family Jensen law with its flatness case | P8, P23 |
| Oscillatory capacity | the escape rank: an integer read from a positive semidefinite kernel that counts the dominant zeros phase-independently, with dominated (subdominant) payment excluded; the budget horizon of a hyperbolic pair | P12, P18, P20, P24, P26 |
| Base constructions | the base as a fixed loss; vertical sections, midpoint contractions, height-coupled zero-tax quartet contractions (`HeightCoupledSystem`), boundary-twist pole absorption (`absorbShiftedPoles`), single-system real-anchor planters (`plantDoubleRealAnchor`), and degree-`K` Fejér height-coupled systems (`FejerCoupledSystem`, halving central pole cost to `(9/2)κ`) against sharp Hadamard and Fejér–Egerváry–Szász converse floors; family averages are not a base | P8, P17, P23, P25, P31 |
| Escape-state classification | the translation-Gram form of the cofactor Gram and its Laplace symbol `G`; the subdominance law; the horizon law, phase kernels, the Cauchy form and its positivity, the null space of escape states, independence of power characters; the transfer from power rows to exponential profiles; Bohr uniqueness and the summable case; the completeness criterion in ADR's normalization | P18, P19, P20, P24, P26, P27 |
| Archimedean–finite coupling | on escape states dilation by `p` is the archimedean flow by `log p` | P22 |
| Selection lemmas at the zero spacing | the resolution of a correspondence is its length; horizon averages select the zeros within `(2/T) Σ |D_{kl}|/|y_k − y_l|` | P11, P21 |
| Arithmetic Stepanov | sparse annihilators need a lattice and never kill an off-line symbol; the Stepanov output (a one-sided prime-power count) is equivalent to RH | P14, P30 |

Each tool is built to the point where its first sharp statement holds for `ζ` or is reduced to a
named input; what lies beyond is in §9.

---

## 9. Open research topics

The report's questions are answered in §6. What remains are frontier problems; each is stated with
what ACP has proved about it.

1. **A localizing carrier with an elliptic local symmetry (B3.25).** Proved: separating local
   isometries are boosts (P13); at a non-real off-line point — the only kind `ζ` can have (P3) —
   real even carriers closed under the symmetric Hecke operators of two primes are blind, and the
   fibre is elliptic exactly when the point is resonant for the prime, `γ log p ∈ πℤ`, which happens
   for one prime at most (P4). More generally a single non-resonant symmetric dilation of any real
   scale blinds the carrier, the archimedean flow blinds it at every non-real off-line point, and
   elliptic survivors exist exactly when every closure scale lies in the resonant group
   `exp((π/γ)ℤ)` of the point (P34). So elliptic localization by correspondences is resonance.
   Open: a carrier that localizes by a non-multiplicative operation and is unconditionally positive;
   separating `ζ` from its twins on it would be a forcing input of RH strength (B1.6).
2. **The first gauge-charged window (W8).** The odd-sector positivity on `[−181/500, 181/500]` is the
   first window theorem that meets a prime (`2`). Proved: the twin with `Λ(2)` flipped can fail only
   on tests with a negative atom at `log 2` (P7), the atom is controlled by the mass in the edge
   strips of width `2·181/500 − log 2 ≈ 0.031`, and the twin is positive on every test with at most
   `1/1961` of its mass there (P33). Open: the edge-concentrated tests, where the archimedean
   penalty for concentration competes with the flipped atom.
3. **Intrinsic exterior square over `ℤ` without shifted poles (settled within shift polynomials and unshifted `CompletedPositiveSystem`s by P31; non-linear `GL(2)` / global cohomological lifts open).** P31 settles both halves of the P25 entry-cost problem across Euler/shift operations and arbitrary unshifted `CompletedPositiveSystem` outputs: (i) local degree-`1` Adams `Λ²` vanishes, isobaric shift-packet `Λ²` either kills quartet collision (`m₀ = 0`), fails positivity (`1 ≤ m₀ ≤ 4`), or retains `κ_γ ≥ 5κ > 0` at ratio `≥ 11/5 > 2` (`m₀ ≥ 5`), and scale-space bilinear squaring puts singularities at `1 + a + iγ` (`Re > 1`); (ii) twisting out shifted poles (`absorbShiftedPoles`, `κ_γ ↦ 0`) is unconditional on the same `Λ` at `κ₀ + 2κ_γ` (minimal by `total_zero_mass_le`), whereas keeping `κ_γ = κ` strictly saves `3γ²(γ²+3)κ/((4+γ²)(1+γ²)) > 0` at `s = 2` and halves P25's `18κ` ceiling to `(9 + O(1/γ²))κ`; (iii) functor-independently, any unshifted `CompletedPositiveSystem κ d` carrying `M` weight-`2` real-anchored quartets obeys `16M + 144M/(9+4γ²) + 5d < 9κ` (`κ ≥ 3` at `M = 1, d ≥ 1`, attained by `plantDoubleRealAnchor`), ruling out bounded `(κ, d)` as `M → ∞`; (iv) across degree-`K` nonnegative cosine shift multipliers with `c₁ ≥ 2`, `c₀ ≥ 1/cos(π/(K+2)) > 1` with two-sided shifted-Gamma cost `Θ(d log(3+|γ|))` per unit pair, while `FejerCoupledSystem K` halves the normalized central pole cost to `(9(K+1)/(2K))κ ↘ (9/2)κ` (`27/4 · κ < 8κ` at `K = 2`). Open beyond P31: whether genuinely higher-rank automorphic `GL(2)/GL(n)` functorial lifts (outside shift-polynomial combinations of degree-`1` `L`-functions and outside fixed-`(κ, d)` unshifted `CompletedPositiveSystem`s) or a multi-ordinate joint Hadamard–Fejér packing can eliminate an entire strip zero configuration when `M` and `K` are coupled to zero-density bounds.
4. **Sections on correspondence surfaces (B3.5).** Settled as a strength statement (P29): a section
   count with Riemann–Roch alone or Bézout alone is free and carries nothing; with both it exists
   iff the Hodge index holds — RH over `ℤ`, purity over `𝔽_q`. Every class has a normalized graph
   (P1), so the same holds on normalized graphs. A section count is therefore not an input weaker
   than the sign; what remains is to construct one with both axioms, which is RH.
5. **Arithmetic Stepanov (B3.30).** Settled as a strength statement (P30): the natural output of a
   Stepanov method over `ℤ`, a one-sided square-root bound on the prime-power count, is equivalent
   to RH, as over `𝔽_q` the one-sided point count is purity. Hecke auxiliaries kill only critical
   lattice symbols and vanish to order `< K` with `K` monomials (P14, P30), so they cannot supply
   it; an arithmetic Stepanov method needs auxiliary sections outside the Hecke algebra of a single
   prime and, if it works, proves RH.
6. **The regular part of the successor (B3.29).** Quantified: `D_Λ` is holomorphic on `Re s > 0`,
   `|D_Λ(s)| ≤ |s||ζ′/ζ(1 + σ)|`, sharp on the real axis up to `2^{1+σ}` (P5), and in the strip
   `|D_Λ(σ + it)| ≪_{σ,η} (|t| + 1)^{1−σ+η}` for every `η > 0` (P32): the size of a Dirichlet
   polynomial of length `|t|`. Open: a lower bound off the real axis, and the part of `D_Λ` that a
   positivity can read.
7. **A base from a non-multiplicative structure.** Proved: a fixed tensor loss is RH and a linear
   loss is the strip (P8); tensor powers, family averages, gauge moments and products all lose
   linearly, and zero loss is flatness, which over `𝔽_q` is purity (P8, P23, ACG, AKT). Open: a
   non-multiplicative structure with loss independent of the power; by P8 it would prove RH.
8. **The explicit-formula split of the cofactor profile (B3.2).** Proved: under RH no damping
   escapes, so completeness holds (P28); escape at `ε` is the presence of zeros right of `½ + ε` up
   to a countable set (P28); a split into a dominant configuration and a subdominant remainder gives
   completeness with rank the number of dominant zeros, for finitely many dominant zeros (P20, P24,
   P27) and for absolutely summable infinite configurations (P26). Open, off RH: the split itself,
   i.e. a contour shift of `G(s)e^{su}` past the translated zeros, which needs growth bounds for
   `1/ζ(s + ε)` between zeros. Its remaining cases are non-summable residues
   `ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))` along a line of zeros, and real parts that accumulate at their
   supremum without attaining it, where the escape states concentrate at infinite height on the
   gauge torus (ACG).

---

## 10. Success criteria and contribution standard

ACP succeeds when it produces a positivity theorem of a type the corpus does not contain — a
completeness law, a charged positivity on a localizing carrier, a budget law, a coupling law — or a
sharp no-go naming the missing layer. Its no-gos: the theorem of the square and the budget are
free (P1, P2); degree-one kernel counts are blind to complex quartets (P3); multiplicative symmetry is hyperbolic and the successor
unipotent (P4, P5); separation is hyperbolic (P13); non-localizing positivity is source-blind (P6);
positivity on nonnegative tests is shared by every dominated twin (P7); tensor powers need
sublinear loss (P8); affine maps have genus zero (P9); kernel counts of symmetric squares are squares
(P10); sparse annihilators need a lattice (P14); family averages lose linearly (P23). Its
completeness law: escape states of dominant configurations are phase kernels of rank the number of
zeros (P20).

| Criterion | Test |
|---|---|
| Selectivity | distinguishes `ζ` from the battery: `CompletedPositiveSystem 2 1` pairs and quartets, pole-order-3 and strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems, the golden datum, the complex fake, `Γ_ℝ^d` solutions, signed self-dual combinations, dominated and flipped twins |
| Gauge charge | separates the gauge point `0` from its twins; fails on the Liouville twin |
| Beyond isotropy | localizes, and its local symmetry at off-line pairs is not hyperbolic |
| Sublinear loss | a term that does not scale with its amplification |
| Joint use of invariants | positivity, FE, simple pole, strip holomorphy together |
| Non-circularity | objects constructed before their sign |
| Calibration | Weil for curves with budget `2g`; the theorem of the square in genus one; Hasse; boundary forcing; `κ = 1` rigidity; the Kronecker split |

A contribution must:

1. be an unconditional Lean theorem about a stated object of §3;
2. name the layer of Weil's argument it concerns (L1–L6);
3. state the local type of its correspondences at off-line pairs and whether its carrier localizes;
4. say whether it uses gauge-charged data, and on which atoms (sign-changing or nonnegative);
5. state what it gives on the golden datum, the complex fake, curves (must reproduce Weil) and the
   battery;
6. give identities where Weil's step is an identity, and keep identities apart from signs;
7. record the positive survivor of every no-go.

Principles: identities first, sign last; the budget is free, its sufficiency is the theorem;
determinants pair conjugates, traces pair reflections; multiplicative symmetry is hyperbolic off the
line, the successor unipotent, the reflection elliptic; positivity constrains only what it localizes;
nonnegative atoms see only the size of the source; calibrate over `𝔽_q`; a reformulation is not a
reduction.

---

## 11. Modules

| Module | Content |
|---|---|
| `TheTheoremOfTheSquareIsFree` | Normalized graphs, degree, uniqueness, the theorem of the square; degree form of the correspondence ring; RH as degree positivity; genus one and golden calibration |
| `TheBudgetIsFreeItsSufficiencyIsNot` | Similitude law; sufficiency as positivity of the graphs of `1 ± ψ`; budget `2g`; golden and complex fake; the spline budget |
| `KernelCountsAreBlindToComplexQuartets` | Determinant and Rosati degrees; Toeplitz identity; Weil in ring form; golden; the complex fake; non-real zeros of `ζ` |
| `TheLocalGeometryOfAReflectionPair` | Local form, boosts, rotations; Hecke symbol; finite orientation law; real even fibres and the resonance law; two primes; the transform of real tests and the symmetric Hecke action |
| `TheSuccessorIsInvisibleAtZeros` | Twisted and archimedean symbols; the successor defect and its holomorphy; the shifted prime source |
| `PositivityBeyondIsotropyDoesNotLocalize` | Aperture probes; full fibres; positivity beyond isotropy and its source-blindness |
| `OnNonnegativeTestsZetaIsTheWorstTwin` | The Weil functional affine in the source; antitonicity on nonnegative atoms; dominated twins; flipped twins |
| `TheBaseIsAFixedLoss` | Root extraction; linear loss is the strip; sublinear and fixed loss are RH; golden tensor loss |
| `AffineCorrespondencesOfZHaveGenusZero` | Iterates of affine maps, periodic points, the successor, intersections of affine graphs |
| `TheSpectrumOfSymmetricSquaresIsTheSign` | Core lemma; kernel count of `f f′`; spectral positivity is unitarity; calibration; the local criterion at one prime |
| `TheResolutionOfACorrespondenceIsItsLength` | Lipschitz symbols on the line; the cost of separation; modulation as spectral translation |
| `ABudgetPaysAHyperbolicPairOnlyOnAFiniteSegment` | Quarter-period phase turn; hyperbolic terms exhaust every budget; the budget horizon |
| `TheIsometriesOfAReflectionPair` | Diagonal and antidiagonal isometries of the local form; separation is hyperbolic |
| `SparseAnnihilatorsAndTheStepanovMechanism` | Sparse root multiplicity; roots of unity among Hecke symbols; no sparse annihilator of an off-line symbol |
| `TheRankinSelbergSquareSeesTheFieldOfTheOtherZeros` | Partial fractions of a squared polar source; the field at a zero; transverse equilibrium; the deepest point |
| `SymmetricSquareContractionsAndExteriorCounts` | Exterior determinant degrees on `Λ^k H¹`, unitary positivity, `complexFake` refutation (`−665379`), unitarity forcing across all genera; vertical correspondence symmetric squares and curve vertical sections; archimedean midpoint symmetric-square contraction (`Δκ = 0` on real pairs, finite-step elimination, `κ = 1` self-similarity) and pole-paid complex quartet contractions (`Δκ = 1, 2`) |
| `TheSelectivityBatteryOfCorrespondencePositivity` | Which invariant sees real off-line pairs and which sees complex quartets |
| `TheCofactorGramIsATranslationGram` | Dilation is translation of the log profile; the translation Gram identity; exponential profiles; the subdominance law; Grams of combinations |
| `TheLaplaceFormOfTheCofactorProfile` | Abel summation on the log cells; the Laplace transform at every horizon; the cofactor symbol `ζ(s)/ζ(s+ε) − Re(1/ζ(1+ε))ζ(s)`; the Laplace form `G` |
| `TheEscapeRankCountsTheDominantZeros` | Dominant configurations; the horizon law; phase kernels as escape states; the Cauchy form and its positivity; null spaces; power characters on the dilations |
| `HorizonAveragesSelectTheZeros` | Phase form of escape kernels; the spacing bound; selection by horizon averages; the Cesàro escape state |
| `OnEscapeStatesDilationIsTheArchimedeanFlow` | Translated characters; the dilation law; dilation by `p` as the archimedean flow by `log p` |
| `ThePowerRowsOfTheZerosAreDominantConfigurations` | The floor estimate; profiles of power rows; comparison of scaled Grams; the real profile as a configuration with frequencies `±Im z`; escape states of power rows |
| `InfiniteDominantConfigurationsAreComplete` | Exponential series; Bohr uniqueness; the Cauchy form of a summable configuration and its positivity; the horizon law; escape states over `(S¹)^ℕ`; the null space |
| `TheEscapeCompletenessCriterion` | Escape states of rows with a dominant split in the normalization of ADR; the vanishing critical kernel of phase kernels |
| `TheEscapeAlternative` | Uncancelled zeros force escape with a lower energy exponent; escape below the zero width; countable cancellation; the escape set; RH as the absence of escape |
| `ASectionCountIsTheSign` | Riemann–Roch and Bézout for section counts; each alone is free; together they are the Hodge index, RH over `ℤ`, purity over `𝔽_q`; golden calibration |
| `TheStepanovCountIsTheSign` | The one-sided prime-power count is RH; Hecke auxiliaries kill only critical symbols |
| `TheSuccessorDefectInTheStrip` | The concave unit step; the head of a power sum; the strip bound `|D_Λ(s)| ≪ (|s|+1)^{1−σ+η}` |
| `TheFirstGaugeChargedWindowOffTheEdge` | The atom at `2` lives on the edge strips; the Liouville twin is positive off the edge |
| `EllipticLocalizationIsResonance` | Resonant scales; one non-resonant scale is blindness; the archimedean flow is blind; resonant survivors |
| `MomentAmplificationOfAnyFamilyLosesLinearly` | Family Jensen; the loss law of family averages; flatness; calibration over `𝔽_q` |
| `ExteriorAndHeightCoupledQuartetContractions` | Post–Widder polar scale-weight positivity and the real-anchor law (`c(σ_max) ≥ c(σ_max + iγ₁)`, `≥ 2c` single-ordinate); functorial `CurveDatum.exterior` and complete quartet phase elimination on `Λ²`; archimedean `exteriorTwoDivisorPoly` (`2 Λ²z_ρ(t) = z_ρ(t)² − z_ρ(2t)`) and `Δκ = 0` contraction (`a < 1/4`); full-strip `coupledQuartetSymSquare` (`0 < a ≤ b < 1/2`, `Δκ = 0`) and `HeightCoupledSystem (2κ) κ d γ` (`F(s)² F(s+iγ) F(s−iγ)`) with zero-tax collided quartet contraction, Hadamard–digamma budget, ordinate-`γ` quartet multiplicity bound, and finite-step real-zero elimination |
| `IntrinsicExteriorAndMinimumAnchorCost` | Local degree-`1` Adams `Λ²` vanishing, isobaric shift-packet `Λ²` dichotomy (`m₀ ≥ 5`, ratio `≥ 11/5`), and scale-space cross-singularity (`Re = 1 + a > 1`); unconditional `κ_γ ↦ 0` boundary-twist absorption (`absorbShiftedPoles`), `total_zero_mass_le` origin-capacity floor, exact `s = 2` pole defect, and `(9 + 12/(4+γ²) + 6/(1+γ²))κ → 9κ` ordinate pole decay; single-system `plantDoubleRealAnchor` (`Δκ = 2`) and functor-independent Hadamard minimum pole law (`16M + 144M/(9+4γ²) + 5d < 9κ`, `κ ≥ 3`); discrete Fejér–Egerváry–Szász multiplier converse (`c₁ ≤ 2c₀ cos(π/(K+2))`), all-height two-sided shifted-Gamma sandwich, and `FejerCoupledSystem K` central pole halving (`9(K+1)/(2K) κ ↘ (9/2)κ`, `27/4 · κ < 8κ` at `K = 2`) |
