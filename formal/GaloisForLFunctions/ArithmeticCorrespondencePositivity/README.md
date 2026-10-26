# Arithmetic Correspondence Positivity (ACP)

**One question.** Over `𝔽_q` one structure — the intersection theory of correspondences on
`C × C` — supplies the sign of the explicit formula (Rosati positivity, the Hodge index), its
budget (`2g`), the base and the tensor powers. Over `ℤ` the corpus has the pairing, the Lefschetz
receivers and the exhaustion of every substitute it has tried. What is the positivity theory of
**arithmetic correspondences** — dilations (gauge invariant), affine maps and additive relations
(gauge charged), the archimedean flow — and which layers of Weil's argument exist for them, which
are free, which are provably absent, and which would have to be created?

ACP is the join of [Arithmetic Positive Duality](../ArithmeticPositiveDuality/README.md) (the
rigidity and capacity theory of positive Poisson pairs, with its exhaustion map of forcing
mechanisms) and [Arithmetic Correlation Geometry](../ArithmeticCorrelationGeometry/README.md) (the
gauge torus and its charged and invariant statistics) with the object neither of them has: **a ring
of correspondences with graphs, degrees, a Rosati involution and a budget**. Its basic object is a
*correspondence surface*: a polar surface on which a ring with involution acts by similitudes. Its
basic invariant is the **Rosati trace** `τ_x(ξ) = δ(ξ·x, x)` of a cycle `x`. Its basic question is
which arithmetic structure makes `τ_x(ξ ξ′) ≥ 0`.

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

Over `𝔽_q` the missing input is supplied by correspondences: Rosati positivity of `End(J)`, a
budget from Riemann–Roch, a theorem of the square for graphs. ACP asks for the arithmetic analogue
of each piece separately, so that a negative answer names exactly the piece that is missing.

| Programme | Interface |
|---|---|
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Scaling data, the correspondence algebra `G →₀ ℝ`, Rosati, Hecke graphs, `rosatiPositive_iff_orbitHodgeIndex`. ACP's correspondence surfaces are AOG's scaling data with graphs and degrees added. |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Polar surfaces, the scaling surface, curve data, the golden datum, genus-one graph classes and Hasse (`genusOne_hasse_tfae`), the no-go for Hecke scales (`heckeCorrespondence_no_square_relation`), the maximal blind ideal. |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Positive-definite functions on `ℚ_{>0}` and `Aff(ℚ)`, coupled isotropy (`coupled_isotropy`), the left-blind ideal, Hecke and Bost–Connes states, the Kronecker split, archimedean–successor coupling. ACP reads its states as Rosati traces. |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | Gauge torus, gauge charge, near-incidences as successor correlations, boundaries of finite presentations, loss laws, the `𝔽_q` fixed-budget law. |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md), [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md) | Boundary forcing, Fejér barrier, completed positive systems, collar capacity. |
| [ArithmeticKunnethTheory](../ArithmeticKunnethTheory/README.md) | Künneth positivity is point-count positivity (`kunneth_positivity_tfae`); product receivers see depth only through total length. |
| [ArithmeticDefectRigidity](../ArithmeticDefectRigidity/README.md) | Cofactor modules, escape states, translated-zero eigenstates (escape completeness, Q7). |
| HTGeometry | Characteristic-zero shifted-subgroup Stepanov (`stepanov_shifted_count_charZero`), the seed of an arithmetic Stepanov method. |

---

## 2. Why

**Weil's proof in layers.** Over `𝔽_q`, for the Frobenius `F` of a curve of genus `g`:

| Layer | Content over `𝔽_q` | Over `ℤ` | Forces the sign? |
|---|---|---|---|
| L1 Identities | Lefschetz `Γ_m·Δ = N_m`, adjunction `Γ_m² = q^m(2 − 2g)`, Rosati adjoint, `F F′ = q` | exact (prime comb, archimedean collar, `T_g T_g′ = e^{s}`) | no: hold on the golden datum |
| L2 Graphs | graph map `End → NS` quadratic (theorem of the square) | holds for normalized graphs of the correspondence ring | no: holds on the golden datum |
| L3 Budget | the defect of the diagonal `δ(Δ, Δ) = 2g`, unchanged along the Frobenius orbit | `δ(x, x)` for every test, unchanged along every Hecke orbit (similitude law) | no: the golden datum has budget `2` |
| L4 Effectivity | graphs are curves; degree = kernel count ≥ 0 (genus one: Hasse) | absent | only for real off-line eigenvalues |
| L5 Rosati positivity | `Tr(ξ ξ′) ≥ 0` from a polarization (Hodge index on `C × C`) | equivalent to RH | yes |
| L6 Base | even tensor powers over a base, fixed loss (Deligne) | relative powers of `ζ` are `ζ` | — |

The first three layers are identities and transfer to `ℤ` intact. They cannot force anything,
because the golden datum `1 − 5X + 5X²` (integral counts, functional equation, Witt integrality,
positive Künneth counts) satisfies all of them and violates Hasse–Weil. The budget of Weil's
inequality `|N_m − q^m − 1| ≤ 2g q^{m/2}` is not the problem: it is fixed for free, by the
similitude law of graphs. Its **sufficiency** is the problem, and sufficiency on every span
`{x, T x}` is Rosati positivity.

**Two kinds of effectivity.** Over `𝔽_q` positivity has two geometric sources. The degree of an
endomorphism is the size of its kernel: `deg(P(F)) = Π_i P(α_i) ≥ 0` (a determinant, multiplicative,
pairing each eigenvalue with its complex conjugate). The Rosati trace `Tr(P(F) P(F)′) = Σ_i P(α_i)
P(q/α_i)` (additive, pairing each eigenvalue with its **reflection** `q/α_i`) is positive because
of a polarization. In genus one the two coincide — Hasse's proof. From genus two on they separate:
the determinant is positive on every datum whose off-line eigenvalues are non-real. The zeros of
`ζ` off the critical line, if any, are non-real. A kernel-count effectivity over `ℤ` would
therefore be blind to all of them; the sign must be of trace (Rosati) type.

**The local geometry of a zero.** The Rosati trace of a cycle splits over the reflection pairs
`{ρ, ρ* = 1 − ρ̄}` of its spectrum. At a critical zero `ρ = ρ*` and the local form is definite;
every Hecke operator acts on the fibre by the unitary `p^{iγ}`. At an off-line pair the local form
is hyperbolic, of signature `(1, 1)`, and every Hecke operator acts by a **boost**
`diag(p^{ρ−½}, p^{ρ*−½})` with `|p^{ρ−½}| ≠ 1`. A positive subspace invariant under a boost is
isotropic. This is the common origin of blindness, half-blindness and isotropy: **multiplicative
symmetry is hyperbolic exactly at off-line zeros**. Positivity beyond isotropy (Q2 of the report)
is possible only on carriers whose local symmetry at an off-line pair is not hyperbolic — carriers
without convolution or Hecke closure, such as bounded-aperture carriers (which do not localize) or
gauge-charged carriers (whose correspondences do not act diagonally on fibres).

**The gauge principle for correspondences.** Dilation correspondences are gauge invariant: their
Rosati traces are built from coincidences of products, and every statement they prove holds on
the whole gauge orbit of the source (ACG). A sign specific to `ζ` must use a gauge-charged
correspondence — the archimedean place (functional equation, Gamma factor), additive relations
(affine graphs, the successor, near-incidences `ab − cd = h`), or the boundary of a finite
presentation — and keep it coupled to the dilations under positivity.

---

## 3. Objects and language

| Weil over `𝔽_q` | ACP object | Over `ℤ` | Lean |
|---|---|---|---|
| `C × C`, `NS` | correspondence surface: polar surface with a ring acting by similitudes | scaling surface with the Hecke algebra of `ℝ_{>0}` | `ScalingDatum` (AOG), `scalingSurface` (ACS) |
| `End(J)`, `ℤ[F]` | correspondence ring `G →₀ ℝ` with Rosati `ξ′(g) = ξ(−g)` | Hecke algebra; affine semigroup of `ℚ` | `Correspondence`, `rosati` (AOG) |
| graph `Γ_f` | **normalized graph** `N(y) = y + (1 − y·V)H + β(y)V`, `N(y)·V = 1`, `N(y)² = 0` | normalized Hecke graph of `ξ·x` | `normGraph` |
| `deg f = Γ_f · H` | **degree** `deg N(y) = δ(y, y)/2` | half the Weil form | `normGraph_degree` |
| theorem of the square | `N` is quadratic: second differences are fibre classes | identity of normalized graphs | `normGraph_square` |
| `Tr(ξ ξ′)` | Rosati trace `τ_x(ξ ⋆ ξ′)` | Weil form on the Hecke orbit of a test | `traceAt` (AOG) |
| `2g` | budget `δ(x, x)` of a cycle | Weil norm of a test | — |
| `#ker f = Π P(α_i)` | determinant degree of a Frobenius polynomial | — (no kernel count) | `detDegree` |
| `α ↦ q/α` | reflection pair `{ρ, ρ*}`, local form | `ρ ↦ 1 − ρ̄` | — |
| Hecke eigenvalue | boost (off line) / rotation (on line) of the local fibre | `p^{ρ−½}` | — |
| fake curve | golden datum | — | `goldenDatum` (ACS) |

Further objects: carriers (subspaces of tests or sources) and their fibres at reflection pairs;
blind, half-blind, left-blind, isotropic carriers (ACS, APD); gauge-charged correspondences
(affine graphs `n ↦ an + b`, successor shifts, near-incidence forms); the gauge family of
correspondence surfaces (twists of the prime comb); Lefschetz sequences `c_m^{(p)} = τ_x(T_p^m)`;
finite presentations with their escaped pairings (ACG); cofactor modules and escape states (ADR).

**Words.** *Correspondence surface*: polar surface + ring with involution acting by similitudes of
the pairing, preserving the fibre plane. *Normalized graph*: the unique isotropic class of unit
vertical degree in `y + ⟨H, V⟩`. *Degree*: horizontal degree of a normalized graph. *Budget*: the
self-defect of a cycle, the constant in Weil's inequality. *Sufficiency*: Weil's inequality on
every span `{x, ξ·x}`. *Determinant degree* / *Rosati degree*: the two quadratic invariants of a
ring element, multiplicative / additive. *Local form*: the restriction of the Rosati trace to the
fibre of a reflection pair. *Elliptic* / *hyperbolic* fibre: the local form is definite and the
Hecke operators are rotations / the local form has signature `(1,1)` and Hecke operators are
boosts. *Localizing carrier*: one in which the contribution of a single reflection pair can be
isolated up to an arbitrarily small remainder. *Gauge-charged correspondence*: one whose Rosati
trace has gauge mean zero.

---

## 4. Mechanisms

**Known, owned by sibling programmes.**

1. *Rosati positivity is the orbit Hodge index* (AOG `rosatiPositive_iff_orbitHodgeIndex`); for
   `ζ` one explicit orbit decides RH (AOG `riemannHypothesis_iff_splineOrbit_hasseWeil`).
2. *Eventual Hasse–Weil is Hasse–Weil* (AOG `hasseWeilAt_of_eventually_bounded`): every finite
   budget self-improves to the canonical one; the tensor-power trick.
3. *Coupled isotropy* (APD `coupled_isotropy`): point-stable coupled carriers have isotropic
   fibres; one channel: half-blind; sharp-stable: blind.
4. *Hasse in genus one* (ACS `genusOne_hasse_tfae`): degree positivity of `ℤ[F]` ⇔ `t² ≤ 4q`.
5. *Gauge projection and gauge Jensen* (ACG): multiplicative statistics are gauge invariant;
   amplification through gauge moments loses linearly.
6. *Künneth collapse* (AKT `kunneth_positivity_tfae`): positivity of products of counts is
   point-count positivity, which the golden datum has.

**ACP mechanisms.**

7. **Normalization of graphs.** Every class `y` of a polar surface has a unique normalized graph
   in `y + ⟨H, V⟩`; its degree is half the defect of `y`; the normalized graph map is quadratic. On
   a correspondence surface the degree form of the ring at a cycle is half its Rosati trace form.
8. **Similitude law of budgets.** Hecke graphs are similitudes; the budget of a cycle is carried
   unchanged along its orbit; Weil's inequality on the plane `{x, ξ·x}` is sufficiency of that
   budget.
9. **Determinant versus trace.** The determinant degree pairs eigenvalues with their conjugates
   and is positive on non-real spectra; the Rosati degree pairs eigenvalues with their reflections
   and is positive exactly on pure spectra.
10. **Local hyperbolic geometry.** At a reflection pair the local form has signature `(1, 1)`;
    multiplicative correspondences act by boosts off the line and rotations on it; positive
    boost-invariant subspaces are isotropic, and positive subspaces have at most half the local
    dimension.
11. **Localization.** Positivity constrains a fibre only where the carrier localizes; non-localizing
    carriers can be positive with full fibres.

**Mechanisms to discover** (the report's list): a *budget law* (a correspondence with a section
count whose defect on `{g, T_{p^m} g}` does not grow with `m` and whose sufficiency is proved
without the sign); a *charged positivity law* (positivity on a gauge-charged localizing carrier
that is not isotropic); a *coupling law* (a positive structure in which the archimedean and finite
components do not split); a *capacity law for oscillation*; a *completeness law* for escape; a
*base law* (a fixed loss over a base, removed by tensor roots).

---

## 5. Pillar theorems

**Foundations from sibling programmes.**

| Foundation | Statement | Lean |
|---|---|---|
| F1 Rosati = orbit Hodge index (AOG) | `τ_x(ξ ⋆ ξ′) ≥ 0` for all `ξ` ⇔ the defect is nonnegative on the orbit of `x` | `rosatiPositive_iff_orbitHodgeIndex` |
| F2 Scaling Hodge index = RH (ACS, AOG) | the scaling surface satisfies the Hodge index iff RH | `scalingSurface_hodgeIndex_iff`, `zetaScalingDatum_hodgeIndex_iff` |
| F3 Hasse in genus one (ACS) | unitarity ⇔ `deg(m − nF) ≥ 0` on `ℤ²` ⇔ `t² ≤ 4q` | `genusOne_hasse_tfae` |
| F4 Hecke scales are numerically free (ACS) | `a ↦ T_a x` satisfies no parallelogram law | `heckeCorrespondence_no_square_relation` |
| F5 Coupled isotropy (APD) | positivity on point-stable coupled carriers forces `K_ρ`-isotropy | `coupled_isotropy`, `positive_ideal_halfBlind` |
| F6 Fixed budget over `𝔽_q` (ACG) | bounded power sums force unitarity; the golden datum has none | `unitary_of_bounded_powerSum`, `goldenDatum_no_fixed_budget` |
| F7 Eventual budgets are sharp (AOG) | eventual Hasse–Weil with any constant is Hasse–Weil | `hasseWeilAt_of_eventually_bounded` |

**ACP pillars.**

| Pillar | Statement | Module |
|---|---|---|
| **P1 The theorem of the square is free** | On every polar surface the normalized graph map is quadratic, `N(y)·V = 1`, `N(y)² = 0`, `deg N(y) = δ(y,y)/2`; on a scaling datum the degree form of the correspondence ring at `x` is half the Rosati trace form, and its positivity is the orbit Hodge index; for `ζ`: RH ⇔ every normalized Hecke graph of every test has nonnegative degree; genus one: ACS's graph classes are normalized graphs; the golden datum satisfies the theorem of the square and has a graph of degree `−1`. | `TheTheoremOfTheSquareIsFree` |
| **P2 Kernel counts are blind to complex quartets** | The determinant degree is multiplicative and nonnegative on every curve datum without real eigenvalues; a genus-two impure datum passes every degree test and fails the Hodge index; a simple real off-line pair is detected by some degree. | `KernelCountsAreBlindToComplexQuartets` |
| **P3 Off-line fibres are hyperbolic** | Local form of signature `(1,1)`; Hecke symbols are boosts iff off line; positive invariant subspaces of a boost are isotropic; positive real subspaces have half dimension; the phase law of reflection-symmetric real carriers. | `TheLocalGeometryOfAReflectionPair` |
| **P4 Positivity beyond isotropy does not localize** | Bounded-aperture carriers have full fibres at every finite set of points and are Weil-positive at small aperture. | `PositivityBeyondIsotropyAtFiniteAperture` |

---

## 6. The questions

1. **What replaces `C × C`?** A correspondence surface. The scaling surface of `ℤ` with the Hecke
   algebra of `ℝ_{>0}` is one; all identities of Weil's argument (L1–L3) hold on it.
2. **Is there a theorem of the square over `Spec ℤ`?** Yes, for the normalized graphs of the
   correspondence ring (P1); no, for the scale map `a ↦ T_a` (F4). It carries no budget: it holds on
   the golden datum.
3. **What is the budget?** The self-defect `δ(x, x)` of a cycle, `2g` for the diagonal of a curve,
   carried unchanged by the similitude law. Every finite budget is the canonical one (F7). What is
   missing over `ℤ` is not a budget but its sufficiency.
4. **Which positivity is gauge charged and not isotropic?** Isotropy is forced by hyperbolic local
   symmetry (P3); multiplicative correspondences supply it at every off-line pair. Positivity
   beyond isotropy needs carriers without that symmetry: non-localizing ones (P4) or gauge-charged
   ones.
5. **How are the archimedean and finite places coupled?** Integer and Bost–Connes successors see
   only Kronecker-null dilation spectra; atomic archimedean spectra blind every successor; a
   continuous archimedean spectrum is seen by the real successor (APD). The zeros are atoms.
6. **What pays `ζ`'s own zeros?**
7. **What are escape states?**
8. **What is the base?**
9. **How does an average become a point?**
10. **How are shared resources paid?**

---

## 7. Traps

| Trap | Truth |
|---|---|
| The theorem of the square is the missing algebraic precondition | It is an identity of normalized graphs and holds on the golden datum (P1) |
| Hecke scales failing the parallelogram law means no theorem of the square | Scale addition is not ring addition (F4 vs P1) |
| A fixed budget is what `ℤ` lacks | The budget is fixed by the similitude law; its sufficiency is RH |
| Effectivity by counting kernels gives the sign | Only in genus one; from genus two on it is blind to complex quartets, and `ζ` has only complex off-line candidates (P2) |
| Positive point counts (Künneth counts) are a weak form of Weil | They are point-count positivity, which the golden datum has (AKT) |
| Positivity on a carrier with full fibres excludes zeros | Only if the carrier localizes (P4) |
| Isotropy is a defect of the carriers studied so far | It is forced by any hyperbolic local symmetry (P3) |
| A non-commutative (affine) carrier adds positivity | Induced from the dilations unless the successor is prescribed (APD) |
| Rosati positivity at one cycle is weaker than RH | For a generic cycle (the spline) it is RH (AOG) |

---

## 8. Tools

Built in sibling programmes: polar surfaces, curve data, the golden datum, scaling data, the
correspondence algebra with Rosati and Hecke graphs, coupled isotropy and the left-blind ideal,
positive-definite functions on `ℚ_{>0}` and `Aff(ℚ)`, the gauge torus, escaped pairings,
characteristic-zero Stepanov.

Built here: normalized graphs and their degree calculus; determinant degrees of curve data; the
local hyperbolic geometry of reflection pairs; aperture interpolation.

To build (the report's list): correspondence intersection theory for affine graphs on the scaling
surface; gauge-charged positivity theorems with their isotropy or non-isotropy laws; a loss-law
calculus with gauge Jensen as its sharp boundary; an oscillatory capacity; base constructions;
escape-state classification; archimedean–finite coupling beyond the Kronecker split; selection
lemmas at the zero-spacing scale; an arithmetic Stepanov method.

---

## 9. Open research topics

1. **A localizing gauge-charged carrier.** A carrier built from affine graphs or near-incidences
   that localizes at off-line pairs and on which the Weil form is positive; or a proof that
   localization forces a hyperbolic symmetry.
2. **Effectivity of Rosati type.** A positivity of the trace pairing `ρ ↔ ρ*` produced by an
   arithmetic count, calibrated by Castelnuovo–Severi in genus `g ≥ 2`.
3. **Sections on correspondence surfaces.** A section count on normalized graphs (B3.5) whose
   Riemann–Roch is proved without the sign.
4. **Arithmetic Stepanov.** Auxiliary sections over `ℤ` whose forced vanishing bounds a spectral
   count, from the characteristic-zero Stepanov lemma.
5. **The base.** A family of correspondence surfaces over a base whose even tensor powers carry
   nonnegative traces with a computable pole part.
6. **Escape completeness** (Q1) in correspondence language.

---

## 10. Success criteria and contribution standard

ACP succeeds when it produces a positivity theorem of a type the corpus does not contain — a
completeness law, a charged positivity, a budget law, a coupling law — or a sharp no-go naming the
missing layer. The report's criteria:

| Criterion | Test |
|---|---|
| Selectivity | distinguishes `ζ` from the battery: `CompletedPositiveSystem 2 1` pairs and quartets, pole-order-3 and strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems, the golden curve, `Γ_ℝ^d` solutions, signed self-dual combinations; survives single-node perturbations `Λ + δ·δ_m` |
| Gauge charge | separates the gauge point `0` from its twins; fails on the Liouville twin |
| Beyond isotropy | its proof does not force isotropy at off-line pairs |
| Sublinear loss | a term that does not scale with its amplification |
| Joint use of invariants | positivity, FE, simple pole, strip holomorphy together |
| Sees more than pole order | reaches intrinsic charge |
| Non-circularity | objects constructed before their sign |
| Uniformity across limits | aperture, height, rank, damping, window controlled together |
| Calibration | Weil for curves with budget `2g`; theorem of the square in genus one; boundary forcing and `⌊k/2⌋`; dlVP; `κ = 1` rigidity; the Kronecker split |

A contribution must:

1. be an unconditional Lean theorem about a stated object of §3;
2. name the layer of Weil's argument it concerns (L1–L6);
3. say whether its correspondences are gauge invariant or gauge charged;
4. state what it gives on the golden datum, on curves (must reproduce Weil) and on the battery;
5. state whether its positivity localizes, and its local symmetry at off-line pairs;
6. give identities where Weil's step is an identity, and keep identities apart from signs;
7. record the positive survivor of every no-go.

Principles: identities first, sign last; a budget is free, its sufficiency is the theorem;
determinants pair conjugates, traces pair reflections; multiplicative symmetry is hyperbolic off
the line; positivity constrains only what it localizes; calibrate over `𝔽_q`; a reformulation is
not a reduction.
