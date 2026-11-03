# Lattice Section Theory of the Scaling Surface (LST)

Namespace `GaloisForLFunctions.LatticeSectionTheory`; umbrella `LatticeSectionTheory.lean`.
Every theorem is unconditional. Statements named `riemannHypothesis_iff_*` are proved
equivalences, not proofs of RH.

## 1. Motivation

Weil's proof of RH for a curve `C/𝔽_q` has one engine: Riemann–Roch on `C × C`. Sections are
dimensions, so `h¹ ≥ 0` is free; Riemann–Roch turns that free inequality into the Hodge index,
the Hodge index on the plane of the Frobenius graph is Castelnuovo–Severi, and Castelnuovo–Severi
is `|N − q − 1| ≤ 2g√q`. Sign, precision and selection come out of one identity and one
nonnegativity.

For `ℤ` the corpus has the surface (the scaling surface of ACS: cycles `aH + bV + f`, Weil's form
as the Castelnuovo–Severi defect `δ`), the reduction of RH to an effectivity with the
Riemann–Roch and ample axioms (ACS, AET, RIT), and the refutation of every effectivity defined from
signs. It has the base: the theta `h⁰` of `Spec ℤ`, a logarithm of a Gaussian lattice count with
Riemann–Roch `h⁰(d) − h⁰(−d) = d` by Poisson summation (AOG). It lacked Riemann–Roch on the
surface for classes with a test component. The doubly exponential aperture ceiling rules out every
producer of the sign that loses a polynomial or exponential factor; an identity plus a free
nonnegativity loses nothing.

LST is the theory of **sections as lattice counts**: `h⁰` of a class is the logarithm of a
Gaussian-weighted count of lattice points, Serre duality is Poisson summation, and `h¹ ≥ 0` must
come from counting, never from the sign of Weil's form. Its central result is a splitting of `h¹`
into a part that counting pays exactly and a part that is Weil's form, together with the
classification of which lattice counts can and cannot touch the second part.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Lattice `h⁰` | `latticeH0`, `latticeRank` | `h⁰(L, d) = log θ_L(e^{−2d})`, `θ_L(t) = Σ_{x∈L} e^{−πt‖x‖²}`, `L = Bℤ^ι`: an Arakelov bundle of rank `r` |
| Base `h⁰` | AOG `arithH0`, `thetaSum` | `h⁰_ℤ(d) = log Σ_n e^{−πn²e^{−2d}}`, `χ_ℤ(d) = d` |
| Künneth count | `kunnethH0` | `h_K(x) = h⁰_ℤ(x·H) h⁰_ℤ(x·V)`: the tensor square of the base |
| Künneth `h¹`, primitive `h¹` | `kunnethH1`, `primitiveH1` | `h¹_K = h⁰_ℤ(x·H)h⁰_ℤ(−x·V) + h⁰_ℤ(−x·H)h⁰_ℤ(x·V)`; `h¹_prim = h_K(x) + h_K(−x) − χ(x) − h¹_K(x)` |
| Bidegree count | `bidegreeCount`, `PolePlaneRiemannInequality` | `h_Φ(x) = Φ(x·H, x·V)` |
| Rectangular lattice | `rectTheta`, `rectForm` | `ℤ ⊕ yℤ`, `Q_y = m² + y²n²`, `θ_y(t) = θ(t)θ(y²t)` |
| Epstein FE-pair, completed Epstein function | `rectFEPair`, `epsteinLambda` | `(θ_y, θ_{1/y})`, weight `1`, root number `1/y`; `Λ_y = Γ(s) Σ' (πQ_y)^{−s}` continued |
| Boosts, Siegel majorant | `boostAmple`, `siegelMajorant`, `siegelTerm` | `A_u = e^uH + e^{−u}V`; `P_u(x) = (x·A_u)² − x²` |
| Boost kernel and constant | `boostKernel`, `boostConstant` | `(e^{2v} + e^{−2v})^{−s}e^{2wv}`; `K(s,w) = ∫` of it |
| Split series | `splitSeries`, `splitTerm` | `Z⁺(s,u) = Σ_{m,n≥1}(e^{2u}m² + e^{−2u}n²)^{−s}` |
| Isotropic cone count | `coneCount`, `coneMellinValue` | `C(t) = Σ_{m,n≥1} e^{−2πtmn}`; `Γ(σ)(2π)^{−σ}ζ(σ)²` |
| Low-frequency divisor | ACS `lowBlindTests`, `lowGrid` | tests of aperture `a` vanishing at `i/2` and on the grid `D_a` |
| Jump count, pole cross term | `jumpCount`, `poleCross` | `J(f) = ∫_0^∞(A_f(0) − A_f(x)) e^{x/2}/sinh x dx`, `A_f` the autocorrelation; `∫ 2cosh(x/2)A_f` |
| Hecke correspondence | ACS `heckeCorrespondence` | `T_a = √a ψ_a` |

## 3. Language

- **Section count**: a function `h ≥ 0` on classes defined from lattice counts or volumes, never
  from the sign of the intersection form.
- **Poisson-dual**: `h(x)` and `h(κ − x)` are exchanged by a Poisson summation; the difference is
  the Euler characteristic. Here `κ = 0`, `χ₀ = 0`, `χ(x) = ½x²`.
- **Rank** of a count: the asymptotic slope of `d ↦ h⁰(L, d)`. **Scale**: the Gaussian degree.
- **Künneth part / primitive part** of `h¹`: the part fixed by the two fibre degrees, and the part
  carried by `x° = x − (x·V)H − (x·H)V`.
- **Bidegree count**: a count that depends on a class only through `(x·H, x·V)`.
- **Soft**: true for every lattice, every characteristic, every datum of a family. **Fake**: a count
  with every soft property whose zeta function has a zero off the line.
- **Boost**: the scaling flow on the pole plane, `A ↦ A_u`; **boost transform**: Mellin transform in
  `e^{2u}`.
- **Divisor at degree `a`**: the finitely many conditions `D_a ∪ {i/2}` outside which the primitive
  `h¹` is coercive.

## 4. Mechanisms

**A. Lattice counts, Poisson duality, rank.**
1. Poisson summation for `L = Bℤ^ι`: `h⁰(L, d) − h⁰(L*, −d) = r d + log(1/covol L)` — Riemann–Roch
   for Arakelov bundles, linear in the degree with slope the rank.
2. Poisson plus monotonicity of the dual count is Banaszczyk's inequality: the slope of `h⁰(L, ·)`
   lies in `[0, r]`; it tends to `0` at `−∞` (only the zero vector survives) and to `r` at `+∞`.
3. Hence a count of bounded rank grows at most linearly along the ample ray, while the Riemann
   inequality forces `n²` (Hilbert–Samuel). A surface `h⁰` needs section lattices whose rank grows
   with one degree while the Gaussian scale grows with the other.

**B. Künneth Riemann–Roch.**
4. The base has canonical degree `0` and `χ_ℤ(d) = d` (genus one for Riemann–Roch). With
   `u = h⁰_ℤ(−a)`, `v = h⁰_ℤ(−b)`, `h⁰_ℤ(a) = a + u`: `h(a)h(b) + h(−a)h(−b) − ab = v h(a) + u h(b) > 0`.
   The tensor square of the base pays the quadratic Euler characteristic of the pole plane exactly;
   the surface behaves like an abelian surface (`κ = 0`, `χ = ½x²`).
5. On any polar surface, `x² = 2(x·H)(x·V) − δ(x,x)` gives
   `h_K(x) + h_K(−x) = ½x² + h¹_K(x) + ½δ(x,x)`: **`h¹ = Künneth part + ½ Weil defect`**. The Künneth
   part is positive because counts are positive; the primitive part is half of Weil's form.
6. The Künneth count is bounded on degree levels everywhere (the base count is at most
   `4/(1 − d)` in degree `d ≤ 0`), so it is an effectivity function iff the Hodge index holds.

**C. Bidegree counts are blind.**
7. Every count built from the base by its own operations (Gaussian counts, Poisson, products,
   convolution in the degree) is a function of `(x·H, x·V)`. It is constant on primitive classes,
   so along `t x°` its `h¹` is `½t²δ(x°,x°) + O(1)`: the Riemann inequality for a bidegree count
   is the Hodge index plus the pole-plane inequality for `Φ`. A sign-producing count must read the
   test component beyond its degrees.

**D. Definite counts are fakes.**
8. The rectangular lattice `ℤ ⊕ yℤ` has a positive count, exact two-dimensional Poisson duality
   `θ_y(1/t) = (t/y)θ_{1/y}(t)`, a completed function holomorphic off two simple poles with
   `Λ_y(1 − s) = y⁻¹Λ_{1/y}(s)`, and Dirichlet series `Γ(s)Σ'(πQ_y)^{−s}`.
9. On the real axis `Λ_y(σ) = M_y(σ) − 1/σ − y⁻¹/(1 − σ)` with a nonnegative Mellin integral.
   Since `θ(t) ≥ t^{−1/2}`, the dual count gives `M_y(½) ≥ 2 log y − 2 + 2/y`, so
   `Λ_y(½) ≥ 2 log y − 4 > 0` for `y > e²`, while the pole term drives `Λ_y → −∞` at `1⁻`: a real
   zero in `(½, 1)`. By the functional equation the same holds for `y < e^{−2}`. `ℤ ⊕ 8ℤ` is a
   fake. At the self-dual point `y = 1` (the Gaussian integers) `θ(t)² = t⁻¹θ(1/t)²` makes the
   Mellin integral `≤ 60/π³ < 3`, so `Λ_1 < 0` on all of `(0, 1)`: the fakes are created by the
   boost.

**E. The split plane: majorants, boosts, cone.**
10. Siegel majorant: `P_u(x) = e^{2u}(x·H)² + e^{−2u}(x·V)² + δ(x,x)`. `P_u ≥ 0` ⇔ Hodge index. The
    Gaussian count along a class converges iff `P_u(x) > 0`, and is then the base count
    `θ(tP_u(x))`; on the scaling surface all primitive ones converge iff RH. A Gaussian Poisson
    summation of the Lorentzian lattice presupposes the sign.
11. On the pole plane the majorant at boost `u` is `e^{−2u}Q_{e^{2u}}`: a fixed boost is a
    rectangular lattice, fake for `|u| > 1`. The index-`p` sublattice `ℤH ⊕ pℤV` at boost `u` is `p`
    times the lattice at boost `u + ½ log p`: Hecke is a boost.
12. Each split term `(m²e^{2u} + n²e^{−2u})^{−s}e^{2wu}` is the translate by `½ log(n/m)` of one
    kernel times `m^{−(s+w)}n^{−(s−w)}`. Integrating over the boost line forgets the translations:
    `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)`. Translating the boost by `c` multiplies by `e^{−2wc}`.
    The Euler product returns only through boost equivariance.
13. The isotropic cone count `Σ_{m,n≥1}e^{−2πtmn}` has Mellin transform `Γ(σ)(2π)^{−σ}ζ(σ)²` with a
    double pole at `1`; every Gaussian Poisson pair has at most a simple pole, so the cone count is
    not Poisson-dual. Its completion is a logarithm — the `log(D²/2)` of pole-plane Riemann–Roch.
    Siegel–Weil in miniature: the boost average of the majorant counts is the cone count up to
    archimedean factors.
    The Gaussian boost count has an explicit physical completion: writing
    `B(t)=∫(θ(te^{2u})−1)(θ(te^{−2u})−1)du`, its convergent regularization
    `R(t)=∫[θ(te^{2u})θ(te^{−2u})−t^{−1/2}e^{|u|}]du` is positive and satisfies
    `R(1/t)=tR(t)`. Its axes contribute `R(t)−B(t)=log t+2/√t+c`, with `c` an
    absolutely convergent theta integral. Hence
    `B(1/t)=tB(t)+(1+t)log t+c(t−1)` and `log R(1/t)−log R(t)=log t`
    (`TheBoostCountHasLogarithmicDuality`). The exact, absolutely convergent comparison
    `B(t)=4∫₀∞ C(t cosh v)dv` identifies this completion directly on the literal cone count
    (`TheConeCountHasAnAbelCompletion`). This count concerns the pole plane.

**F. Hecke, the primitive part, and its index.**
14. `T_a` sends the bidegree `(b₁, b₂)` to `(b₁, ab₂)` (boost and scaling) and multiplies the
    primitive `h¹` and `χ` by `a`: a similitude of ratio the degree, like `deg(φψ) = deg φ deg ψ`.
    The sign of the primitive `h¹` is invariant under the whole Hecke monoid.
15. The number of negative directions of the primitive `h¹` is the Hodge defect, an even integer.
    RH, nonnegativity of the primitive `h¹`, effectivity of the Künneth count, convergence of all
    primitive Siegel counts and "fewer than two right zeros" are one statement.

**G. Prime-free cycles, jump counts, and the finite divisor.**
16. On all tests of aperture `≤ 3/10` and on ample-orthogonal smooth tests of aperture
    `≤ (log 2 + 1/50)/2` (the prime-free window `½ log 2` and past the prime 2) the Künneth count is
    an effectivity function; on any test subsurface its effectivity is Weil positivity there.
17. On a prime-free test (`2a < log 2`) the primitive `h¹` is a count: `W(f,f) = Ω(0)‖f‖² + J(f) +
    2·poleCross`, where `J(f) = ½∫_0^∞∫(f(u) − f(u+x))²du · e^{x/2}/sinh x dx ≥ 0` counts the jumps of
    `f` with the Lévy weight of the Gamma factor and `Ω(0) = −(log π + 3 log 2 + γ + π/2)`. A test
    supported in `[−a, a]` jumps to `0` across every gap `x > 2a`, and across every gap
    `x ∈ [a, 2a]` at least half its mass jumps (`A_f(x) ≤ ½‖f‖²`: the overlap sits left of `0` in
    `f` and right of `0` in its translate). With the tail `w(x) ≥ 2e^{−x/2}`,
    `J(f) ≥ ‖f‖²(½(log 2 − a/2) + log(1/2a) − (1 − 2a)/2 + 4e^{−1/2})`. For `a ≤ 1/64` these
    exterior jumps pay `|Ω(0)| < 5.373` and the pole term: `W(f,f) ≥ ‖f‖²/20` follows from the
    count, with no estimate of the Weil form.
18. At every degree `a > 0`, outside the `2#D_a + 2` real conditions of the low-frequency divisor,
    the Künneth count is an effectivity and the primitive `h¹` is coercive:
    `h¹_prim ≥ ½ c_a ∫f²`, `c_a = (10 + 68e^a)(1 − 1/π)`. This is what replaces finite genus.

**H. Calibration over `𝔽_q`.**
19. On Frobenius windows of a curve datum the Künneth count is effective on every window iff the
    datum is unitary; the golden fake fails on some window. In genus one the primitive `h¹` of the
    graph of `m − nF` is `deg(m − nF) = m² − amn + qn²`, and for `1 − F` it is the number of points:
    over a curve the primitive `h¹` is the degree of a correspondence, i.e. a count. For the curves
    `y² = f(x)` of every genus over every finite field of odd characteristic the primitive `h¹` is
    nonnegative on every window because of two counts — Stepanov's auxiliary sections and
    `|τ|² = q` — so the function-field version of the open core is solved by counting.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Poisson Riemann–Roch for lattices of every rank | `latticeH0_riemannRoch` | proved |
| Banaszczyk slope law; rank = asymptotic slope | `latticeH0_slope`, `latticeH0_le`, `tendsto_latticeH0_atBot`, `tendsto_latticeH0_sub_atTop` | proved |
| Rank law: bounded rank violates the Riemann inequality | `not_riemannInequality_of_bounded_rank`, `not_riemannInequality_latticeH0_linear` | proved |
| Künneth Riemann–Roch: `h¹ = h¹_K + ½δ`, `h¹_K > 0` | `arithH0_kunneth`, `kunnethH0_add_neg`, `kunneth_h1_sub_eq_half_defect`, `kunnethH1_pos` | proved |
| Künneth effectivity ⇔ Hodge index; pole plane unconditional; scaling surface ⇔ RH | `kunneth_effectivity_iff`, `kunnethH0_degreeBounded`, `hyperbolicPlane_kunneth_effectivity`, `riemannHypothesis_iff_kunneth_effectivity` | proved; equivalence |
| Bidegree blindness | `bidegree_h1_eq`, `riemannInequality_bidegree_iff`, `kunneth_polePlaneRiemannInequality` | proved |
| Two-dimensional Poisson; Epstein FE-pair; Dirichlet series | `rectTheta_inv`, `rectFEPair`, `epsteinLambda_one_sub`, `differentiableAt_epsteinLambda`, `hasSum_epsteinLambda` | proved |
| Epstein fakes: a positive centre forces a real zero in `(½,1)`; this holds for `y > e²` and `y < e^{−2}`; `ℤ ⊕ 8ℤ` | `exists_epsteinLambda_eq_zero_of_half_pos`, `exists_epsteinLambda_eq_zero`, `exists_epsteinLambda_eq_zero_of_lt`, `epsteinLambda_eight_has_offLine_zero`, `epsteinLambda_half_re_ge` | proved |
| The self-dual point has no real zeros: `Λ_1(σ) < 0` on `(0, 1)` | `epsteinMellin_one_le`, `epsteinLambda_one_neg`, `epsteinLambda_one_ne_zero` | proved |
| Siegel majorant law; convergence ⇔ positivity; scaling surface ⇔ RH | `siegelMajorant_eq`, `siegelMajorant_nonneg_iff_hodgeIndex`, `summable_siegelTerm_iff`, `riemannHypothesis_iff_forall_summable_siegelTerm` | proved; equivalence |
| Fixed boosts are rectangular and fake; Hecke is a boost | `hyperbolicPlane_siegelMajorant`, `exists_boost_offLine_zero`, `hyperbolicPlane_siegelMajorant_hecke` | proved |
| Boost transform `= K(s,w)ζ(s+w)ζ(s−w)`; Hecke character | `integral_splitSeries_mul_exp`, `integral_splitSeries_mul_exp_eq_zeta`, `boostConstant_pos`, `integral_boost_translate` | proved |
| Cone count `Γ(σ)(2π)^{−σ}ζ(σ)²`, double pole, not Poisson-dual; Siegel–Weil | `mellin_coneCount`, `tendsto_sq_mul_coneMellin`, `tendsto_sq_mul_Λ`, `not_exists_FEPair_coneCount`, `siegelWeil_splitPlane` | proved |
| Hecke similitude of the primitive `h¹` | `primitiveH1_heckeCorrespondence`, `eulerChar_heckeCorrespondence`, `primitiveH1_heckeCorrespondence_nonneg_iff` | proved |
| Index readings: RH ⇔ primitive `h¹ ≥ 0` ⇔ Künneth effective ⇔ primitive Siegel counts converge ⇔ fewer than two right zeros | `riemannHypothesis_primitiveH1_tfae`, `forall_primitiveH1_nonneg_iff` | equivalences |
| Prime-free effectivity | `kunneth_effectivity_realTestsAt`, `kunneth_effectivity_primitiveSmoothRealTestsAt`, `kunneth_effectivity_scalingSubsurface_iff` | proved |
| The primitive `h¹` of a prime-free cycle is a jump count; positivity from the count | `weilPair_eq_jumpCount_of_primeFree`, `jumpCount_ge`, `abs_poleCross_le`, `jumpCount_derivation_of_primeFree_positivity` (`a ≤ 1/2000`) | proved |
| Exterior jumps across gaps `≥ a`; positivity from the count for `a ≤ 1/64` | `autocorr_le_half_of_le`, `archLevySinhWeight_ge_exp`, `jumpCount_ge_exterior`, `exteriorJumps_derivation_of_primeFree_positivity`, `primitiveH1_ge_of_exteriorJumps` | proved |
| Odd quadratic correlation moment `=−(∫xF)²`; unit quadratic jump cost `≤5∫F²/12` | `odd_autocorr_second_moment`, `unit_odd_jump_second_moment`, `unit_odd_jump_second_moment_le` | proved |
| Riemann–Roch outside a finite divisor at every degree | `kunneth_effectivity_lowBlindTests`, `kunneth_primitive_h1_ge`, `exists_ne_zero_lowBlindTests` | proved |
| `𝔽_q` calibration | `unitary_iff_forall_window_kunneth`, `goldenDatum_not_forall_window_kunneth`, `genusOne_kunneth_h1_graphCycle`, `genusOne_kunneth_h1_frobenius` | proved |
| Stepanov counts pay the primitive `h¹` of hyperelliptic curves of every genus | `hyperelliptic_window_hodgeIndex`, `hyperelliptic_kunneth_effectivity`, `hyperelliptic_primitiveH1_nonneg` | proved |

## 6. Tools (developed, and to develop)

**Used from the corpus.**
- Gaussian lattice Poisson summation in every rank (`HTGeometry/GaussianLatticeTheta`).
- The base theta `h⁰` and its Riemann–Roch (`ArithmeticOrientationGeometry/TheThetaH0OfSpecZ`).
- Polar surfaces, scaling surface, subsurfaces, Hecke correspondences, curve data, golden datum,
  low-frequency divisor (ACS); the effectivity calculus (AET).
- Mathlib's Mellin FE-pairs (`WeakFEPair`), `hasSum_mellin`, Eisenstein-series summability.
- Stepanov's count and the Gauss-sum modulus for hyperelliptic curves (AET
  `hyperellipticDatum_unitary`); the Lévy identity of the Weil form (BiScaleUncertainty).

**Developed in LST.**
- Slope calculus of lattice counts: positivity, monotonicity, Banaszczyk's inequality, asymptotic
  slopes, the rank law on polar surfaces.
- Uniform decay of the base count in negative degree (`thetaSum_sub_one_le`, `arithH0_le_of_nonpos`).
- Künneth calculus of section counts and the primitive `h¹`; bidegree counts.
- Two-variable theta splitting, the Epstein FE-pair, real continuation and sign analysis of
  Epstein functions (`epsteinLambda_ofReal`, `two_log_le_epsteinMellin_half`).
- Siegel majorants of polar surfaces; convergence criterion for Gaussian counts along a class.
- Boost transforms: the translated-kernel identity `splitTerm_eq`, integrability of the boost
  kernel, the archimedean constant `K(s,w)`.
- Isotropic cone counts, their Mellin transforms, and the pole-order obstruction for FE-pairs.
- Index readings of the primitive `h¹` as one TFAE (sections, Siegel counts, index exit).
- The jump-count form of the primitive `h¹` on prime-free cycles; exterior-jump lower bounds across
  gaps `> 2a` and `[a, 2a]`; the Lévy-weight inequalities `e^{x/2}/sinh x ≥ 1/x − 1/2` and
  `≥ 2e^{−x/2}`.

## 7. Questions the programme answers

| Question | Answer |
|---|---|
| What is the section space of a class: which lattice, which metric? | A lattice whose rank grows with one fibre degree and whose Gaussian scale grows with the other; bounded rank never works (`not_riemannInequality_of_bounded_rank`). On the pole plane the tensor square of the base, with Serre duality the product of two Poisson summations (`kunnethH0_add_neg`). The Gamma factor enters as the Gaussian weight of the base. |
| Is surface Serre duality a two-dimensional Poisson summation for an indefinite lattice? | Gaussian (Siegel) counts of the intersection lattice exist exactly where the majorant is positive, i.e. under the Hodge index (`siegelMajorant_nonneg_iff_hodgeIndex`, `riemannHypothesis_iff_forall_summable_siegelTerm`). The indefinite count of the split plane is the divisor count with a double pole, not Poisson-dual (`not_exists_FEPair_coneCount`); its completion is the logarithm of pole-plane Riemann–Roch. |
| Is the explicit formula the dual side? | The primes enter only through the primitive `h¹ = ½δ`, whose value on test classes is Weil's explicit formula; no Poisson identity of a bidegree count produces them (`riemannInequality_bidegree_iff`). |
| Why `ζ` and not an Epstein zeta? | Definite counts are fakes (`exists_epsteinLambda_eq_zero`); the split plane at a fixed boost `|u| > 1` is one of them (`exists_boost_offLine_zero`), while the self-dual point `u = 0` is not (`epsteinLambda_one_neg`): the boost creates the fakes. Only the boost transform carries the Euler product, `K ζ(s+w)ζ(s−w)` (`integral_splitSeries_mul_exp_eq_zeta`). |
| What is the effectivity of a Hecke correspondence? | On the pole plane a boost by `½ log p` (`hyperbolicPlane_siegelMajorant_hecke`); on the primitive part a similitude of ratio its degree (`primitiveH1_heckeCorrespondence`). It never changes the sign. |
| What replaces finite genus over `ℤ`? | The base is genus one for Riemann–Roch and the Künneth part is finite and bounded on degree levels. The infinite part lives in the primitive `h¹`, and at each degree it is controlled outside a finite divisor of `2#D_a + 2` conditions (`kunneth_primitive_h1_ge`): the genus of `ℤ` is a finite divisor at every degree, unbounded in the degree. |
| Q1: an effectivity on prime-free cycles, and prime-free positivity from Riemann–Roch? | The Künneth count is positive, Poisson-dual, satisfies the quadratic Riemann inequality and is bounded on degree levels on all tests of aperture `≤ 3/10` and on ample-orthogonal tests past `½ log 2` (`kunneth_effectivity_realTestsAt`, `kunneth_effectivity_primitiveSmoothRealTestsAt`). Its `h¹` is the Künneth part plus the primitive part, and on prime-free cycles the primitive part is a jump count plus a constant and a pole term (`weilPair_eq_jumpCount_of_primeFree`). Up to aperture `1/64` the count alone forces positivity (`exteriorJumps_derivation_of_primeFree_positivity`); between `1/64` and `½ log 2` the positivity is known from estimates (to `3/10` for all tests) and its derivation from the count is open. |
| Q2: how do the primes enter `χ` without breaking the Riemann inequality? | Through `x² = 2(x·H)(x·V) − δ`: `χ` contains the explicit formula only via the primitive part, and the Riemann inequality of any bidegree count is then the Hodge index. Every count built from the base is blind to them. |
| Q3: is the Hodge defect an integer reading of `h¹`? | Yes as an index: the number of negative directions of the primitive `h¹ = ½δ` is the Hodge defect, which ACS (`pontryagin_law`) and AOG (`zeta_orientationIndex_law`) identify with the distinct right zeros; it is even, and every reading of it below `2` — by sections, by Siegel counts, by the index exit — is the same statement (`riemannHypothesis_primitiveH1_tfae`). A height-uniform reading remains open (B40). |
| Does any of this select `ζ` among fakes? | The soft laws do not: Epstein fakes, golden curve. Selection appears exactly where the theory reaches the primitive `h¹` (`goldenDatum_not_forall_window_kunneth`) or the boost transform. |

## 8. Open research topics

1. **The primitive `h¹` as a count.** On prime-free tests it is a jump count plus the constant
   `Ω(0)‖f‖²` plus a pole term, and the exterior jumps force positivity up to aperture `1/64`. The
   full exterior charge `½∫f(x)²(W(a − x) + W(a + x))dx`, `W(t) = ∫_t^∞ e^{x/2}/sinh x`, would reach
   about `a ≈ 0.03`. At `a = ½ log 2` the exterior charge gives only `W(a) ≈ 3.85` against
   `|Ω(0)| ≈ 5.37`: the whole prime-free window needs the interior jumps (a Poincaré inequality for
   the Lévy form on an interval) and the sign structure of the pole term (`+2A²` on even tests,
   `−2A²` on odd ones). Beyond the prime-free window the count must contain the prime comb.
2. **One two-prime Hecke lattice.** The primitive `h¹` on `⟨p⟩ × ⟨q⟩` as a sum of squares of coupling
   differences at every window size (B7).
3. **Indefinite counts with characteristics.** Zwegers–Vignéras thetas of the Hecke lattice cut by
   two ample classes: convergence, completion, sign; the cone count is their boundary case.
4. **The degree of a correspondence of `Spec ℤ` as a kernel count**, the analogue of
   `deg(m − nF) = #ker(m − nF)`.
5. **Height-uniform readings of the primitive index** (B40).
6. **The whole boost line.** Every boost `|u| > 1` is a fake and the self-dual point `u = 0` has no
   real zero in `(0, 1)`. The centre value is `2(log y − log 4π + γ)` up to exponentially small
   terms, so the true threshold is near `y ≈ 7.01` (Bateman–Grosswald) against the proved
   `e² ≈ 7.39`; where on `0 < |u| ≤ 1` the first real zero enters `(½, 1)` is open.

## 9. Traps

| Trap | Truth |
|---|---|
| A two-dimensional Poisson summation is surface Serre duality | Definite binary counts have it and are fakes |
| The split plane with a fixed metric is the split surface | It is a rectangular definite lattice, fake for every boost `|u| > 1` |
| The sum of two base `h⁰` is a surface `h⁰` | Its Euler characteristic is `log(D²/2)`; the product is quadratic |
| A bigger lattice gives a surface `h⁰` | Bounded rank means at most linear growth |
| Lorentzian Poisson duality can produce the sign | The Siegel majorant is positive exactly under the Hodge index |
| The cone count is the indefinite theta series to use | It is `ζ²` with a double pole and no Poisson duality |
| Künneth Riemann–Roch is progress on the sign | Its Künneth part is positive for free; the primitive part is untouched |
| A count built from the base can see the sign | Bidegree counts are constant on primitive classes |
| Hecke operators can push the primitive `h¹` positive | They rescale it by their degree |
| Prime-free effectivity is derived from Riemann–Roch | It is equivalent to prime-free positivity; the jump count derives that positivity up to aperture `1/64`; the rest is by Lévy estimates |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `ArithmeticCastelnuovoSeveri` | scaling surface, subsurfaces, Hecke correspondences, curve data, the low-frequency divisor; LST supplies section counts for its effectivity axioms and proves which counts can satisfy them |
| `ArithmeticEffectivityTheory` | the effectivity calculus (Riemann inequality, degree bounds), `ℙ¹ × ℙ¹` calibration; LST replaces functions of one degree by counts with rank and Künneth structure |
| `ArithmeticOrientationGeometry` | the theta `h⁰` of `Spec ℤ`, pole-plane Riemann–Roch in sum form, orientation index; LST uses the base and replaces the sum by the tensor product |
| `RenormalizedIntersectionTheory` | quadratic Riemann–Roch with a Serre-dual `h⁰` is the renormalized Hodge index; LST identifies the part of `h¹` that carries it |
| `ArithmeticLorentzianGeometry`, `ArithmeticCorrespondencePositivity` | Hecke as a boost, the theorem of the square; LST realizes the boost on lattice counts and the degree on the primitive `h¹` |
| `HTGeometry` | lattice Poisson summation in every rank |
| `RHTower` (Lévy windows) | prime-free positivity by Lévy potentials: the only count-like representation of the primitive `h¹` known |

## 11. Success criteria and criteria for contributions

The programme is complete when the primitive `h¹` is realized as a count — on the prime-free
subsurface first, then one prime at a time — or when it is proved that no lattice count can realize
it there. Every other question of §7 has a theorem as answer.

A contribution to LST must:
1. define its `h⁰` from counts or volumes, with `h⁰ ≥ 0` by construction;
2. prove its duality by an identity (Poisson-type), not by an estimate;
3. say which part of `h¹` it controls: Künneth or primitive;
4. say what it does on the fakes (rectangular lattices beyond `e²`, the golden datum, prime-flip
   twins), since a law that holds on fakes is soft;
5. be unconditional; implications into RH and equivalences must be labelled as such.

## 12. Big picture

The sign problem of RH is the nonnegativity of one `h¹`. On the scaling surface that `h¹` splits:
a Künneth part, which the tensor square of the base pays exactly by Poisson summation, and a
primitive part, which is half of Weil's form. Everything counting can do by itself is blind to the
primitive part: bounded-rank lattices cannot even reach the quadratic Euler characteristic,
bidegree counts are constant on primitive classes, Gaussian counts of the Lorentzian lattice exist
only after the sign, Hecke operators rescale the primitive part by their degrees. Definite counts
have every soft property and are fakes; the split plane selects `ζ` only through its boosts, whose
average restores the Euler product and whose indefinite cone count carries the logarithm of
pole-plane Riemann–Roch. Over `𝔽_q` the primitive `h¹` is the degree of a correspondence, a count of
kernel points. The field's remaining task is that count for `ℤ`.
