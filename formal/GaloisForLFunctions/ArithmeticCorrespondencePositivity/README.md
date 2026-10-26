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
| Amplification over `ℤ` | loses linearly (gauge Jensen; product receivers) | ACG, AKT |
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
| L4 Kernel counts | `deg P(F) = #ker = Π P(α_i) ≥ 0`; `deg(f f′)` is a square | absent; affine maps of `ℤ` have genus zero (P9) | only real off-line eigenvalues (P3) |
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
kernel-count effectivity would be blind to all of them. The sign is of trace type.

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

**Words.** *Correspondence surface*: polar surface with a ring acting by similitudes that preserve
the fibre plane. *Normalized graph*: the isotropic class of unit vertical degree in `y + ⟨H, V⟩`.
*Budget*: the self-defect of a cycle. *Sufficiency*: Weil's inequality on every span `{x, ξ·x}`.
*Determinant* / *Rosati degree*: the two quadratic-type invariants of a ring element, pairing
conjugates / reflections. *Local form*: the Rosati trace on the fibre of a reflection pair.
*Hyperbolic*, *elliptic*, *unipotent*: the local types above. *Resonant prime* (for a point `ρ`):
`γ log p ∈ πℤ`. *Localizing carrier*: one that can isolate the contribution of one reflection pair.
*Atoms* of a test `k`: `Re(k(log n) + k(−log n))`. *Dominated source*: a prime weight `w ≤ Λ`.
*Loss* of an amplification: the exponent `L_k` in `|c|^k ≤ C_k e^{L_k t}`.

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

**ACP pillars.**

| Pillar | Statement | Lean |
|---|---|---|
| **P1 The theorem of the square is free** | On every polar surface `N(y)·V = 1`, `N(y)² = 0`, `deg N(y) = δ(y,y)/2`, `N` is quadratic and unique modulo fibres; on a scaling datum the degree of the normalized graph of `ξ·x` is `τ_x(ξ ⋆ ξ′)/2`, its positivity is the orbit Hodge index, and on two-term correspondences it is Hasse–Weil. RH ⇔ every normalized Hecke graph of every test (equivalently of the cubic spline) has nonnegative degree. The ring map obeys the theorem of the square while the scale map does not. In genus one ACS's graph classes are normalized graphs; the golden datum has the theorem of the square and a graph of degree `−1`. | `normGraph_square`, `normGraph_degree`, `eq_normGraph_of_mem`, `graphDegree_eq`, `forall_graphDegree_nonneg_iff`, `hasseWeilAt_iff_graphDegree_nonneg`, `riemannHypothesis_iff_forall_graphDegree_nonneg`, `riemannHypothesis_iff_splineCycle_graphDegree_nonneg`, `ring_square_and_scale_no_square`, `CurveDatum.graphCycle_eq_normGraph`, `goldenDatum_normGraph_degree_neg` |
| **P2 The budget is free, its sufficiency is not** | Similitude law for normalized Hecke graphs; Weil's inequality at a scale ⇔ `deg N(x ± ψ_g x) ≥ 0`; the budget of the diagonal of a curve is `2g`; sufficiency at every level ⇔ unitarity; golden (budget `2`) and complex fake (budget `4`) insufficient; RH ⇔ sufficiency of the spline budget at every scale. | `normGraph_degree_heckeGraph`, `normGraph_degree_act`, `hasseWeilAt_iff_normGraph_degree_nonneg`, `CurveDatum.diagonal_defect`, `budget_sufficient_iff_unitary`, `goldenDatum_budget_insufficient`, `complexFake_budget_insufficient`, `riemannHypothesis_iff_spline_graphs_one_add_sub_nonneg` |
| **P3 Kernel counts are blind to complex quartets** | The determinant degree is multiplicative, real, and nonnegative on every datum without real eigenvalues; the Rosati degree is the Toeplitz form of the power sums and is nonnegative on `ℝ[F]` iff the datum is unitary; golden `deg(2 − F) = −1`; the complex fake has nonnegative point counts and kernel counts, violates Hasse–Weil, and has Rosati degree `−2304` at `F² + q`; zeros of `ζ` in the strip are non-real. | `detDeg_mul`, `conj_detDeg`, `detDeg_nonneg_of_im_ne_zero`, `rosatiDeg_sum_monomials`, `rosatiDeg_nonneg_iff_unitary`, `goldenDatum_detDeg_two_sub_X`, `complexFake_eigenvalue_root`, `complexFake_pointCount_nonneg`, `complexFake_not_hasseWeil`, `complexFake_rosatiDeg_neg`, `counts_do_not_force_purity`, `zeta_strip_zero_im_ne_zero` |
| **P4 Off-line fibres are hyperbolic** | Boosts are isometries of the local form; cyclic positivity under a boost forces `u v̄ = 0`, under a rotation only `Re(u v̄) ≥ 0`; the Hecke symbol is a boost iff off the line; finite configurations: cyclic positivity under a separating symbol ⇔ half-blindness at every off-line pair; real even fibres: a non-real symbol forces `ĝ(ρ) = 0`, a real one only `Re ĝ(ρ)² ≥ 0`; resonance iff `γ log p ∈ πℤ`; a non-real point resonates at no more than one prime, a real point at every prime; two primes force blindness; the symmetric Hecke operator acts on transforms by its symbol, and the law holds for actual real even tests. | `localForm_boost`, `mul_conj_eq_zero_of_cyclic_nonneg`, `cyclic_nonneg_iff_of_norm_eq_one`, `norm_heckeSymbol_eq_one_iff`, `mul_conj_eq_zero_of_heckeCyclic_nonneg`, `halfBlind_iff_cyclicForm_nonneg`, `eq_zero_of_symCyclic_nonneg`, `symCyclic_nonneg_iff_of_im_eq_zero`, `symHeckeSymbol_im_eq_zero_iff`, `not_resonant_at_two_primes`, `eq_zero_of_two_prime_symCyclic_nonneg`, `mellinAt_reflect_of_even`, `mellinAt_symHecke`, `mellinAt_eq_zero_of_symHecke_local_nonneg` |
| **P5 The successor is unipotent** | Gauge twists and the archimedean flow keep the modulus `p^{σ−½}` of a symbol; the successor defect `D_a` is holomorphic on `Re s > 0` for every source with `Σ |a_{n+1}| n^{−σ−1} < ∞`; `Σ Λ(n)(n+1)^{−s} = −ζ′/ζ(s) − D_Λ(s)`: the shifted prime source has the poles of `−ζ′/ζ` in the strip with the same principal parts. | `norm_twisted_heckeSymbol`, `norm_archimedeanSymbol`, `differentiableOn_succShiftDefect`, `succShift_vonMangoldt_eq`, `differentiableOn_succShiftDefect_vonMangoldt` |
| **P6 Positivity beyond isotropy does not localize** | For `0 < a ≤ 3/10` the carrier `realTestsAt a` is coercively Weil-positive, sees both points of every pair, and is positive for every prime weight. | `positivity_beyond_isotropy_at_finite_aperture`, `exists_mem_realTestsAt_mellinAt_ne_zero`, `re_mellinAt_apertureProbe_pos` |
| **P7 On nonnegative tests `ζ` is the worst twin** | The full Weil functional is affine in the prime weights; on nonnegative atoms it is antitone; for `f ≥ 0` and every `w ≤ Λ` (sign twins, the Liouville twin, truncations, the prime-free weight) `Re W_Λ(f ⋆ f̃) ≤ Re W_w(f ⋆ f̃)`, so positivity there transfers to all of them; a negative atom at `n₀` makes the flipped twin strictly worse. | `weilFullFunctional_sub_eq`, `re_weilFullFunctional_le_of_le`, `re_weilTest_nonneg`, `re_weilFullFunctional_vonMangoldt_le_of_nonneg`, `liouvilleTwin_le`, `weilPositive_nonneg_transfers`, `flipTwin_lt` |
| **P8 The base is a fixed loss** | `|c(t)|^k ≤ Ce^{Lt}` gives width `≤ L/k`; bounds with linear loss `kσ` hold iff width `≤ σ`; sublinear loss gives RH; RH ⇔ one exponent bounds every tensor power of the spline correlation; the golden datum's tensor powers lose `k log φ`. | `zetaZeroWidth_le_of_tensor_bound`, `zetaZeroWidth_le_iff_linear_tensor_loss`, `riemannHypothesis_of_sublinear_tensor_loss`, `riemannHypothesis_iff_fixed_tensor_loss`, `goldenDatum_tensor_loss_ge` |
| **P9 Affine correspondences of `ℤ` have genus zero** | `(a − 1)(f^m(n) − n) = (a^m − 1)((a − 1)n + b)`; for `a ≥ 2` every iterate of `n ↦ an + b` has at most one fixed point, the same for all `m`, integral iff `(a − 1) ∣ b`; the successor has no periodic points; two distinct affine graphs meet at most once. | `affineIter_mul`, `affineIter_fixed_iff`, `fixedPoints_iter_subsingleton`, `exists_fixed_iff`, `translate_iter_ne`, `affine_graphs_meet_at_most_once` |
| **P10 The spectrum of symmetric squares is the sign** | Core lemma: `α α' = q > 0` and `(α − c)(α' − c) ≥ 0` for all real `c` force `|α|² = q`; `deg(f f′)` is a square; every eigenvalue of `(F − c)(F − c)′` is a nonnegative real iff the datum is unitary; the complex fake has `17 − 6i`, the golden datum `−1`; locally `(β − c)(β⁻¹ − c) ≥ 0` for all `c` iff `|β| = 1`, which for the Hecke symbol is `Re ρ = ½` at one prime without resonant exception. | `normSq_eq_of_symSquare_nonneg`, `prod_symSquareEig_eq_sq`, `symSquare_spectrum_nonneg_iff_unitary`, `complexFake_symSquareEig_one`, `goldenDatum_symSquareEig_two`, `symSquare_local_nonneg_iff`, `symSquare_heckeSymbol_nonneg_iff` |
| **P11 The resolution of a correspondence is its length** | `|p^{iγ} − p^{iγ'}| ≤ log p · |γ − γ'|`; a polynomial separating two critical symbols by `1` has derivative bound `C` with `1 ≤ C log p |γ − γ'|`; modulation by `cos(γu)` translates the transform, `(ĝ(s + iγ) + ĝ(s − iγ))/2`. | `norm_heckeSymbol_sub_le`, `one_le_deriv_bound_mul_length`, `mellinAt_mul_cos` |
| **P12 A budget pays a hyperbolic pair only on a finite segment** | Within a quarter period the phase turns `w e^{iγt}` to real part `≥ |w|/2`; a bounded remainder plus `2 Re(w e^{(δ+iγ)t})`, `w ≠ 0`, `δ > 0`, `γ ≠ 0`, exceeds every budget at arbitrarily large scales, before `log((|K| + |B| + 1)/|w|)/δ + π/(2|γ|)`. | `exists_abs_re_ge_half`, `exists_gt_abs_of_hyperbolic` |
| **P13 Separation is hyperbolic** | Diagonal isometries of the local form are `(au, bv)` with `a b̄ = 1`; they separate the two points iff they are boosts; antidiagonal isometries `(λv, μu)` have `λ μ̄ = 1`, square to a unimodular scalar, and fix positive lines. | `diagonal_isometry_iff`, `diagonal_isometry_separates_iff`, `antidiagonal_isometry_iff`, `antidiagonal_isometry_sq`, `localForm_swap_fixed`, `separating_isometry_is_boost` |
| **P14 Sparse annihilators need a lattice** | A nonzero polynomial with `K` monomials vanishes to order `< K` at every nonzero point; `1 − T_p^N` kills the symbol of `ρ` iff `Re ρ = ½` and `N Im ρ log p ∈ 2πℤ`; it never kills an off-line symbol. | `rootMultiplicity_lt_card_support`, `heckeSymbol_pow_eq_one_iff`, `heckeSymbol_pow_ne_one_of_re_ne` |
| **P15 The Rankin–Selberg square sees the field of the other zeros** | For a finite polar source `F = Σ m_j/(s − z_j)`, `F² = Σ m_j²/(s − z_j)² + Σ 2m_j E_j/(s − z_j)` with the field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`; on critical configurations `Re E_j = 0`; at the deepest off-line point with its reflection present `Re E_j > 0`. | `sq_sum_eq_partial_fractions`, `re_fieldAt_eq_zero_of_critical`, `re_fieldAt_pos_of_deepest` |

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
   finite budget self-improves to it (F7). It is neither a section count nor a torsion order. Its
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
   reflection (elliptic).
6. **What pays `ζ`'s own zeros?** Along any Hecke orbit an off-line pair contributes a hyperbolic
   term growing at the rate of its depth while critical zeros contribute rotations (P4, F8); a fixed
   budget pays an off-line pair only on a segment of length `≍ log(budget/weight)/depth` (P12), and
   Weil's inequality fails at every large `m` for the test that sees it (ACS
   `OffLineZerosAreLefschetzRatios`). At bounded aperture,
   intrinsic charge is paid by domination with capacity the archimedean horizon count (ACS
   `hodgeDefectAt_zeta_le_shannon`), and that positivity is source-blind (P6). Oscillatory payment
   has no capacity uniform in aperture except the one RH asserts.
7. **What are escape states?** ADR: on every finite exponent window the power-log eigenstates of the
   renormalized cofactor are exactly the translated zeros with multiplicity; hull characters of finite
   modules have radial modulus. In ACP terms an escape module is a cyclic module over the
   Dirichlet-convolution correspondence ring, and completeness is spectral synthesis for the symbol
   `ζ(s + ε)` on it. Completeness for infinite-dimensional modules is open (Q1 of the report).
8. **What is the base?** At the level of receivers, exactly a fixed-loss bound for the tensor powers
   of one orbit correlation (P8): linear loss gives the strip and nothing more, sublinear or fixed loss
   gives RH. Multiplicative amplification loses linearly (ACG gauge Jensen), relative powers of `ζ`
   are `ζ` (ACG), and the golden datum loses `log φ` per power (P8). A base must come from a structure
   whose cost does not scale with the power.
9. **How does an average become a point?** Averaging over heights or along orbits averages the
   elliptic phases of critical zeros and never isolates a fibre; isolation needs hyperbolic growth
   (an off-line zero's own) or length: a correspondence of length `L` resolves heights `≍ 1/L`, and
   separating two critical zeros at distance `δ` costs a derivative `≥ 1/(Lδ)` (P11); modulation
   moves fibres instead of acting on them. At the zero spacing this is the persistence scale `1/A`
   of ACG with `A ≍ log T`. Selection below the
   zero spacing is RH-strength (B1.4).
10. **How are shared resources paid?** The Rosati trace form is one budget for the whole ring;
    frustration is its negative index, which counts the seen off-line zeros (AOG). On configurations
    the shared budget is decided by two-term spans at all scales because hyperbolic growth exposes
    every seen pair (AOG orientation theorem); on finite windows it is not (mimics).

**The report's three questions.** Q3 (a theorem of the square over `Spec ℤ`): answered by P1, with
the conclusion that it carries no budget. Q2 (positivity beyond isotropy): answered in sharp form by
P4, P5, P6 and P7 — it exists only without localization or without source; localizing
multiplicative carriers are isotropic, additive closure is unipotent. Q1 (escape completeness):
reformulated as spectral synthesis for the cofactor symbol, open.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The theorem of the square is the missing algebraic precondition | It is an identity of normalized graphs and holds on the golden datum (P1) |
| Hecke scales failing the parallelogram law means no theorem of the square | Scale addition is not ring addition (F4 vs P1) |
| A fixed budget is what `ℤ` lacks | The budget is fixed by the similitude law; its sufficiency is RH (P2) |
| Effectivity by counting kernels gives the sign | Only in genus one; the complex fake passes every kernel count (P3) |
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

---

## 8. Tools

Built in sibling programmes: polar surfaces, curve data, the golden datum, scaling data, the
correspondence algebra with Rosati and Hecke graphs, coupled isotropy and the left-blind ideal,
positive-definite functions on `ℚ_{>0}` and `Aff(ℚ)`, the gauge torus, escaped pairings, the
window certificates, characteristic-zero Stepanov.

Built here:

- normalized graphs, their degree calculus and the theorem of the square;
- the similitude law and budget sufficiency on Weil planes;
- determinant and Rosati degrees of curve data; the complex fake;
- the local form, boosts and rotations, Lagrange localization on finite spectra;
- Hecke, symmetric Hecke and archimedean symbols; the resonance law;
- the transform `mellinAt` of real tests, its reflection law, translation and symmetric Hecke
  action; aperture probes;
- the successor defect of a source and its holomorphy;
- the affine dependence of the Weil functional on the source; dominated and flipped twins;
- the loss calculus for tensor powers of an orbit correlation.

To build: correspondence intersection theory for affine graphs; gauge-charged positivity theorems on
localizing carriers; Rosati-type effectivity from counts; an oscillatory capacity; base
constructions; escape-state classification; selection lemmas at the zero spacing; an arithmetic
Stepanov method.

---

## 9. Open research topics

1. **A localizing carrier with an elliptic local symmetry.** Local isometries separate the two
   points of an off-line pair only hyperbolically (P13), so such a carrier must isolate the pair by
   a non-isometric arithmetic operation and carry a reflection-type symmetry; build one on which
   Weil's form is positive, or prove that every localizing arithmetic carrier is multiplicative.
2. **The first gauge-charged window.** The odd-sector positivity on `[−181/500, 181/500]` is the first
   window theorem that meets a prime (`2`). Does it hold for the twin with `Λ(2)` flipped? A failure
   would make it the first unconditional positivity theorem that separates the gauge point `0` from a
   twin (P7 shows on which tests this can happen: those with a negative atom at `log 2`).
3. **Effectivity of Rosati type.** A positivity of the trace pairing `ρ ↔ ρ*` produced by an
   arithmetic count, calibrated by Castelnuovo–Severi in genus `≥ 2`: it must fail on the complex fake.
4. **Sections on correspondence surfaces.** A section count on normalized graphs (B3.5) whose
   Riemann–Roch is proved without the sign.
5. **Arithmetic Stepanov.** Auxiliary sections over `ℤ` whose forced vanishing bounds a spectral
   count. Stepanov's sparse annihilators need a lattice in the spectrum and never kill an off-line
   symbol (P14); the auxiliary sections must come from another source.
6. **The regular part of the successor.** The successor is unipotent on polar fibres; its defect
   `D_Λ` carries the near-incidence information. Quantify `D_Λ` in the strip.
7. **A base from a non-multiplicative structure** with loss independent of the tensor power.
8. **Escape completeness** as spectral synthesis for `ζ(s + ε)` on cyclic cofactor modules.

---

## 10. Success criteria and contribution standard

ACP succeeds when it produces a positivity theorem of a type the corpus does not contain — a
completeness law, a charged positivity on a localizing carrier, a budget law, a coupling law — or a
sharp no-go naming the missing layer. Its no-gos: the theorem of the square and the budget are
free (P1, P2); kernel counts are blind (P3); multiplicative symmetry is hyperbolic and the successor
unipotent (P4, P5); separation is hyperbolic (P13); non-localizing positivity is source-blind (P6);
positivity on nonnegative tests is shared by every dominated twin (P7); tensor powers need
sublinear loss (P8); affine maps have genus zero (P9); kernel counts of symmetric squares are squares
(P10); sparse annihilators need a lattice (P14).

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
