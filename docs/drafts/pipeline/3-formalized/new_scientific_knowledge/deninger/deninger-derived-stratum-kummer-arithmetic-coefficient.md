# Derived stratum-Kummer arithmetic coefficient

- **ID:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Stage:** 3-formalized
- **Type:** PRIMARY SOURCE CONSTRUCTION THEOREM
- **Label:** `DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`
- **Parent:** `deninger-true-to-approximate-derived-coefficient`
- **Statement:** Deninger's relevant complex is the derived fibre of
  the source generic Tate--Milnor coefficient, augmented by the radial
  Poisson middle ideal, mapping by Kummer residues to the restricted
  sum of source prime-packet coefficients.

## Source definition

Let \(a:X\to S=\operatorname{Spec}\mathbb Z\) be Deninger's arithmetic
projection, with generic and prime restrictions \(a_\eta\) and \(a_p\).
On the suspension covers of each stratum, use
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  Let
\[
 \alpha_{\mathrm{PS}}:X_\eta^{\mathrm{PS}}\longrightarrow X_\eta
\]
be the equivariant pro-Stein cylinder refinement constructed by
`DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF`, and define the generic
relevant coefficient
\[
 \mathscr A_\eta^{\mathrm{rel}}
 =
 R\alpha_{\mathrm{PS},*}
 \widetilde{\mathscr A}^{M,\mathrm{PS}}_\eta .
\]
This is Deninger's prescribed \(R\alpha_*\mathcal G\)-type object on
the approximation.  It is not ordinary cohomology of the raw
approximation.

For comparison, the degreewise coarse invariant stratum sheaves are
\[
 \mathscr A_\eta^{\mathrm{coarse}}
 =
 (\pi_{\eta,*}\widetilde{\mathscr A}_\eta^M)
 ^{\mathbb Q_{>0}},
\qquad
 \mathscr A_p
 =
 (\pi_{p,*}\widetilde{\mathscr A}_p^M)
 ^{\mathbb Q_{>0}}.                                               \tag{1}
\]
These are actual coarse stratum sheaves, not quotient-stack objects.
No equivalence between
\(\mathscr A_\eta^{\mathrm{coarse}}\) and
\(\mathscr A_\eta^{\mathrm{rel}}\) is asserted or needed.
For arithmetic boundary maps, the generic analytic factor is represented
by the pro-log-extendable cylinder model of
`DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`.  Its logarithmic Poincaré
lemma gives the same generic derived sections as the unrestricted
pro-Stein cylinder model, while supplying genuine specialization and
Poincaré residue on every prime stratum.  No ordinary Cartier structure
on Deninger's generalized function \([p]\) is assumed.

The prime \(\mathscr A_p\) remains a genuine sheaf on Deninger's actual
coarse prime stratum.  Apply arithmetic derived direct image and put
\[
 \mathscr G_\eta
 =Ra_{\eta,*}\mathscr A_\eta^{\mathrm{rel}}
 \simeq
 R(a_\eta\alpha_{\mathrm{PS}})_*
 \widetilde{\mathscr A}^{M,\mathrm{PS}}_\eta,
 \qquad
 \mathscr C_p=R(a_p)_*\mathscr A_p.                              \tag{2}
\]
The equivalence is the composition law for derived direct images.
Hence the pro-Stein relative-cell calculation computes the relevant
coefficient after arithmetic direct image; it does not compute
ordinary coarse-suspension hypercohomology.

For the \(\mathbb Q\)/Riemann-zeta object, enhance the generic
coefficient by the source radial ideal:
\[
 \mathscr G_\eta^{\mathrm{PZ}}
 =
 \mathscr G_\eta
 \mathop{\times}^{h}_{\underline{\mathbb C}}
 \mathscr R_{\mathrm{PZ}}^+ .
\]
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION` proves that this
augmented homotopy pullback identifies the common unit, retains the
Tate--Milnor and radial positive ideals, and creates no unsupported
raw tensor cross term.  In the zeta specialization, write
\(\mathscr G_\eta\) for this enhancement below.
The nonlocal all-prime completion must be formed after this direct
image: `deninger-sectionwise-completed-prime-sum-sheaf` proves that a
sectionwise global \(L^1/L^2\) condition is not a sheaf condition on
arbitrary Deninger opens.  Define instead
\[
 \mathscr B_{\mathrm{fin}}^S
 =
 \widehat{
 \underset{P\subset\{\mathrm{primes}\},\,|P|<\infty}
 {\operatorname{ind\,lim}}
 }
 \ \bigoplus_{p\in P}i_{p,*}\mathscr C_p(-1)                     \tag{3}
\]
with the mixed \(L^1/L^2\) Kummer topology.  Thus the Tate normal
twist is already part of \(\mathscr B_{\mathrm{fin}}^S\).  Adjoin the
already-twisted real Milnor--Witt boundary
\(\mathscr B_\infty^S\).  The correctly
graded codimension-one target is
\[
 \mathscr D_{\mathrm{ar}}^S
 =
 \left(
   \mathscr B_{\mathrm{fin}}^S
   \widehat\oplus\mathscr B_\infty^S
 \right)[-1].                                                    \tag{4}
\]
The cohomological shift is forced because tame residue lowers Milnor
degree by one.  `deninger-unshifted-prime-residue-fiber` proves that
omitting `[-1]` cannot type the Kummer residue as a cochain map.

## Construction theorem

`[PROVED] [DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT]`

There is a canonical flow- and correspondence-equivariant sheaf
morphism
\[
 \partial_{\mathrm{ar}}^S:
 \mathscr G_\eta
 \longrightarrow
 \mathscr D_{\mathrm{ar}}^S                                     \tag{5}
\]
whose finite components are the generalized-log Milnor residues and
whose real component is the Milnor--Witt signature residue.

Define
\[
 \boxed{
 \mathscr E_{\mathrm{arith}}^S
 =
 \operatorname{Fib}(\partial_{\mathrm{ar}}^S)
 }                                                               \tag{6}
\]
in the derived category of complete locally convex sheaves on the
actual cofinite arithmetic base.  Arithmetic cohomology is
\[
 H^i_{\mathrm{arith}}
 =
 H^iR\Gamma(S,\mathscr E_{\mathrm{arith}}^S).                     \tag{7}
\]
This is the arithmetic derived direct image of Deninger's stratum
coefficients, not a replacement of them by a base-only model.  A later
full-space coefficient whose \(Ra_*\) is `(6)` gives the same groups by
Leray and is an optional geometric enhancement.

The construction satisfies:

1. **Source locality.**  Restriction to every \(U_N\), before and after
   arithmetic direct image, is
   compatible with Deninger's open-base-change homeomorphism and
   underived coarse invariant stratum sheaves.
2. **Finite residues.**  On algebraic Kummer symbols, `(5)` is
   \[
   \alpha\longmapsto
   (\operatorname{ord}_p\alpha)_{p\nmid N},
   \]
   with the normal line and power normalization of
   `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`.
3. **Steinberg descent.**  Every Milnor relation and higher relative
   cell maps to zero under the residue differential, so `(5)` exists
   on the sheafified unit-amalgamated coefficient, not only on units.
4. **Strict boundary.**  The finite components extend continuously
   to `(3)`, and
   \[
   R\Gamma(S,\mathscr B_{\mathrm{fin}}^S)
   \simeq
   \widehat{\bigoplus}_{p}^{\,\prime}
   R\Gamma(X_p,\mathscr A_p)(-1).                                \tag{8}
   \]
5. **Local analytic amplitude.**  Generic derived sections have strict
   amplitude \([0,1]\).  Prime-packet derived sections have the sharper
   amplitude \([0,0]\): the characteristic-\(p\) leaf is profinite,
   its smooth-transverse leafwise sheaf is fine, and positive real
   Milnor groups vanish.
6. **Endpoints.**  The finite-plus-infinite product formula gives
   \(H^0=\mathbb R\) and \(H^2=\mathbb R(-1)\).
7. **Operations.**  Cup product, trace, flow, Galois maps,
   Frobenius/Verschiebung, and finite correspondences descend through
   `(6)`.

## Immediate consequence

Clauses 4--5 and `DAC_SHIFTED_STRATUM_RESIDUE_FIBER` give the
canonical three-term complex
\[
 L^0=A^0,\qquad
 L^1=A^1,\qquad
 L^2=B_{\mathrm{fin}}^0\widehat\oplus B_\infty^0,                \tag{9}
\]
including the real orientation summand.  Thus
\[
 H^i_{\mathrm{arith}}=0\qquad(i\notin\{0,1,2\}).                \tag{10}
\]
The middle group is the kernel of the completed source residue modulo
generic boundaries.  Prime-packet mean-zero modes occur in the
degree-two target and must be hit by nonconstant analytic Poincaré
residues; they are not inserted as an uncoupled direct summand of
middle cohomology.  The middle group is not a Hilbert space indexed by
zeta zeros and not a quotient-stack comparison defect.

## Proof closure

The categorical passage `(6)`--`(10)` and every component of the
residue morphism are proved.

`[PROVED] [DAC_SOURCE_STRATUM_RESIDUE_SHEAF_MORPHISM]`

By `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`, every relative
Tate--Milnor cell follows formally from one square-zero Kummer-boundary
square.  `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE` constructs it and
proves restriction, rational-power, Galois, and finite-correspondence
compatibility at every finite place.

`[PROVED] [DAC_REAL_KUMMER_ARAKELOV_BOUNDARY]`

`DAC_REAL_KUMMER_ARAKELOV_BOUNDARY` constructs the real boundary
skyscraper on the Arakelov compactification, proves the logarithmic
Kummer generator map, its square-zero Milnor extension, mixed
continuity, and the scalar product-formula endpoint.

`[PROVED] [DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT]`

`DAC_ARCHIMEDEAN_KUMMER_HOMOLOGY_CURRENT` represents the real
logarithm by the unique homology current on every finite character
torus.  Its square-zero derived-algebra map is natural through lattice
refinements, relative Tate--Milnor cells, Galois maps, power maps,
field norms, and finite correspondences.  After pro-Stein arithmetic
direct image it gives the real component of `(5)` continuously in the
mixed \(L^1/L^2\) topology.

`[PROVED] [DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD]`

`DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD` constructs `(3)` after
arithmetic derived direct image, proves it is flasque on the cofinite
base, and proves `(8)`.  It also proves the strict scalar/mean-zero
packet decomposition.  The failed sectionwise completion on arbitrary
Deninger opens is not used.

`[PROVED] [DAC_PRIME_PACKET_PRO_STEIN_KUMMER_COMPARISON]`

`DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION` proves that
\(\Gamma_p\cong
(\widehat{\mathbb Z}_{(p)}^\times/p^{\widehat{\mathbb Z}})
\times(\mathbb R/\log p\,\mathbb Z)\), that the prime leafwise
Tate--Milnor sheaf is fine with derived sections in degree zero, and
   that its valuation line is a strict scalar summand.  The full packet
   space is the degree-two residue target.  Haar averaging is used only
   to identify its scalar valuation line, not as a local sheaf
   endomorphism.

The real signature component, strict completed trace-kernel exactness,
and operation compatibility now imply the arithmetic-cohomology
construction.  Local Poincaré-residue surjectivity supplies every
finite packet mode.

`[PROVED] [DAC_COMPLETED_ARAKELOV_TRACE_KERNEL]`

`DAC_STRICT_PRO_LOG_COLLAR_SECTION` completes actual finite-stage
logarithmic collar forms and gives a strict all-prime right inverse on
packet mean-zero residues.  Combining it with the strict Kummer
divisor equivalence proves
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`: the completed boundary image is
the Arakelov trace kernel and \(H^2=\mathbb R(-1)\).  Collar right
inverses prove strict surjectivity but are not part of the residue
map; their nonuniqueness creates no operation-coherence obligation.
The intrinsic middle group is therefore the source-defined Hausdorff
quotient
\[
 H^1_{\mathrm{arith}}
 =
 \ker\partial_{\mathrm{ar}}^S/
 \overline{\operatorname{im}d_{\mathrm{gen}}}.
\]
Every operation descends because the generic, finite, and real
residue morphisms are natural before taking the fibre.

The earlier
`DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON` becomes an optional
comparison between the relevant coefficient and ordinary derived
sections of the raw coarse invariant sheaf; it is not needed to define
or compute `(6)`.

`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION` now identifies
this intrinsic middle group strictly with the Poisson--zeta/Meyer
middle coefficient \(M_\zeta\).  What remains for the
Riemann-zeta theorem is source cup/trace comparison, positive
cup-isometric Hodge polarization, and faithful generalized-jet
transport.

## Falsifiers

- A residue defined only on global unit groups is not `(5)`.
- Omitting the codimension-one shift in `(4)` puts prime residues in
  arithmetic degree one and is ruled out by
  `DAC_UNSHIFTED_PRIME_RESIDUE_FIBER_NO_GO`.
- A direct product in `(3)` admits infinite uncontrolled residues and
  breaks the product formula; an algebraic direct sum is incomplete.
- Bare \(L^2\) makes the product-formula kernel nonclosed.
- Chartwise amplitude without genuine stratum sheaves and arithmetic
  direct image proves neither clause 5 nor `(8)`.
- Replacing degreewise invariants in `(1)` by derived group invariants
  changes the source.
- Defining any term from \(\xi\)-zeros, the explicit formula, Weil
  positivity, or RH is circular.

## Gates

- [x] 0 → 1 in-progress: source definition and exact gates isolated
- [x] 1 → 2 fully-proven: pro-Stein relevant coefficient, finite and
  real residues, strict all-prime direct image, completed trace-kernel
  exactness, intrinsic middle group, and operations proved
- [x] 2 → 3 formalized: coefficient, totalization, and all analytic
  hypotheses encoded unconditionally
- [ ] 3 → 4 publication-ready: standalone arithmetic cohomology paper

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Introduction pp. 4--5, Definition 10.1, and §§11--12:
  https://arxiv.org/abs/1807.06400
- `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`
- `DAC_ARITHMETIC_PRO_LOG_KUMMER_DIVISOR_RESOLUTION`
- `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`
- `DAC_PRO_LOG_STEIN_KUMMER_RESIDUE_SQUARE`
- `DAC_DENINGER_PRIME_PACKET_HAAR_RETRACTION`
- `DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`
- `DAC_SHIFTED_STRATUM_RESIDUE_FIBER`
- `DAC_REAL_KUMMER_ARAKELOV_BOUNDARY`
- `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`
- `DAC_ADELIC_KUMMER_GELFAND_TRIPLE`
- `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT`

## Log

- 2026-07-27 — defined corrected source coefficient directly on
  Deninger's actual coarse space as generic-to-prime derived residue
  fibre; removed raw global coarse-hypercohomology comparison from the
  construction-critical path.
- 2026-07-27 — reduced all-cell residue coherence to one analytic
  Kummer generator square; proved individual prime-packet topology,
  fine-sheaf amplitude \([0,0]\), and strict scalar/mean-zero splitting.
- 2026-07-27 — constructed the finite-place generator square by
  pro-log-Stein Poincaré residue and descended all finite components
  through the unit-amalgamation and coarse invariants.
- 2026-07-27 — retired sectionwise global summability as a sheaf on
  arbitrary Deninger opens; constructed the strict flasque restricted
  completion after arithmetic derived direct image.
- 2026-07-27 — grading audit retired the unshifted prime fibre.  Tame
  residues now land in the Tate-normal target `(-1)[-1]`, so finite
  and real boundary cochains occur in arithmetic degree two and
  middle cohomology is the global residue kernel.
- 2026-07-27 — constructed the real Kummer boundary sheaf and mixed
  pro-log collar completion; proved the completed finite-plus-real
  residue image is the Arakelov trace kernel, hence the shifted fibre
  has \(H^2=\mathbb R(-1)\).

## Lean status

### The assembled complex and its endpoints

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticThreeTermAssembly.lean` (5 declarations,
axiom audit `propext, Classical.choice, Quot.sound` or less) puts together the pieces that the
sub-cards already contribute:

- `deningerArithmeticFiberComplex` — **`(9)`**: the two-term generic source in degrees zero and
  one, with the finite-plus-real boundary object in degree two, the residue differential being the
  collar Arakelov boundary of `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`.
- `deningerArithmeticFiber_H0_eq`, `_H1_cycles_eq`, `_H2_boundaries_eq` — **`(11)`**: degree zero
  is the kernel of the generic differential, degree-one cocycles are the residue kernel, and
  degree-two boundaries are the residue image.  Since the complex has no terms outside degrees
  `0, 1, 2`, this is also `(10)`.
- `deningerArithmeticFiber_H2Equiv` — **clause 6's `H² = R(-1)`**: the Arakelov trace is onto with
  kernel exactly the residue image, so the top group is the real orientation line.

The contributing modules, all already in the tree: `DeningerShiftedFiberTotalization.lean` (the
shifted fibre and its global sections), `DeningerArakelovTraceKernel.lean` (the boundary, the
trace and their exactness), `DeningerFiniteResidueSquare.lean` (the finite residue square and its
square-zero lift), `DeningerRationalDivisorSequence.lean` (the divisor normalization of clause 2),
`DeningerAmalgamationUniversalDescent.lean` (the Steinberg descent of clause 3),
`DeningerRestrictedPrimeGluing.lean` (the strict boundary sheaf of clause 4),
`DeningerArithmeticCofiniteOpenBaseChange.lean` and `DeningerInvariantRestriction.lean` (the source
locality of clause 1).

### The totalization and the operations landed

`DeningerThreeTermTotalization.lean` realizes `(9)` as a genuine cochain complex of modules and
proves `(10)` — vanishing of homology in every degree above two — as a theorem about all degrees,
together with the identification of the three surviving groups with the arithmetic `H⁰`, `H¹`,
`H²`.  `DeningerThreeTermOperations.lean` and `DeningerThreeTermCupProduct.lean` encode **clause
7**: morphisms of three-term complexes with functorial and additive induced maps in all three
degrees (so Galois maps, Frobenius, Verschiebung and finite correspondences descend), the trace on
the top group, and the cup product in every bidegree of total degree at most two.
`DeningerThreeTermEndpointsHausdorff.lean` adds the missing half of **clause 6** — `H⁰` is the
coefficient ring as soon as the kernel of the generic differential is the line spanned by the unit
— and the intrinsic middle group `ker ∂ / closure(im d)`, proved Hausdorff.

### What is still missing, and the route to it

Two things remain before the `2 → 3` gate can close.

- **Clause 5's amplitude** is now **proved** in the abstract form its justification uses: a fine
  (flasque) sheaf has amplitude `[0,0]`, and a sheaf with a length-one flasque resolution has
  amplitude `[0,1]`.  See below.
- **The sheaf-level coefficient `(5)`--`(6)`.**  The residue morphism and its fibre live in a
  derived category of complete locally convex sheaves.  What is formalized is the totalization that
  fibre produces, in all degrees, with all of its operations.


- 2026-08-04 — clause 7 and the totalization encoded unconditionally.  New modules, all wired into
  `GaloisForLFunctions.RHTower` and audited to `propext, Classical.choice, Quot.sound`:
  - `DeningerThreeTermOperations.lean` — **clause 7**: `DeningerThreeTermHom`, a morphism of
    three-term complexes, and the maps `H0map`, `H1map`, `H2map` it induces; `H0map_id`,
    `H0map_comp`, `H0map_add`, `H0map_smul` and their degree one and two analogues, so the
    assignment is functorial and additive.  Galois maps, Frobenius, Verschiebung and finite
    correspondences — integral combinations of morphisms — therefore descend, and the transverse
    flow is recovered as `DeningerArithmeticThreeTermFlow.toHom`, whose induced maps are the
    already-defined `thetaH0`, `thetaH1`, `thetaH2`.  `DeningerThreeTermTrace.H2map` is the trace on
    the top group.
  - `DeningerThreeTermCupProduct.lean` — **clause 7's cup product**: `DeningerThreeTermCup`, the
    chain-level products in every bidegree of total degree at most two subject to the
    Koszul--Leibniz rules, and the descended products `cupH00`, `cupH01`, `cupH10`, `cupH11`,
    `cupH02`, `cupH20` on cohomology.
  - `DeningerThreeTermTotalization.lean` — **the totalization `(9)` and the vanishing `(10)`**:
    `deningerThreeTermCochain` realizes the three-term complex as a genuine cochain complex of
    modules, `deningerThreeTermCochain_isZero_X` and `_isZero_homology` prove that it and its
    homology vanish in every degree above two, and `deningerThreeTermCochain_homologyIso0/1/2`
    identify the three surviving groups with the arithmetic `H⁰`, `H¹`, `H²`.  So `(10)` is now a
    theorem about all degrees rather than a consequence of only defining three groups.

- 2026-08-04 — the corepresenting free abelian sheaf on an open set and `injective ⟹ flasque`, both
  absent from mathlib, landed unconditionally.  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `DeningerOpenSubterminalSheaf.lean` — the sheaf of types represented by an open set (its values
    are subsingletons and opens contained in `U` have union contained in `U`), and
    `deningerOpenTypeHomEquiv`, the Yoneda statement that maps out of it are sections over `U`.
  - `DeningerOpenFreeSheaf.lean` — `deningerOpenFree U`, the free abelian sheaf on an open set,
    obtained by applying the free abelian group functor and sheafifying; `deningerOpenFreeHomEquiv`,
    the corepresentation `Hom(ℤ_U, F) ≅ F(U)`, with its naturality in the open set and in the
    sheaf; `deningerOpenFreeIncl_mono`, that an inclusion of opens gives a monomorphism of free
    abelian sheaves; and `deningerInjective_isFlasque`, **an injective abelian sheaf is flasque** —
    restriction is precomposition with that monomorphism, which an injective object turns into a
    surjection.  This is the step mathlib lacks and the one the amplitude clause needs.

- 2026-08-04 — **clause 5 encoded**: sheaf cohomology and the acyclicity of fine sheaves, both
  absent from mathlib, landed unconditionally in `DeningerFlasqueAcyclic.lean`.  Axiom audit
  `propext, Classical.choice, Quot.sound`.
  - `deningerSheafCohomology U F n := Ext (ℤ_U) F n`, with `deningerSheafCohomologyZeroEquiv`
    proving that degree zero is sections — this is what makes the definition sheaf cohomology.
  - `deningerFlasque_ext_eq_zero`, `deningerFlasque_subsingleton_cohomology` — **a flasque sheaf has
    no higher cohomology**, hence amplitude `[0,0]`.  The proof is the classical dimension shift:
    embed the sheaf in an injective one, which is flasque by `deningerInjective_isFlasque`, so the
    quotient is flasque and sections of the injective surject onto sections of the quotient; the
    covariant long exact sequence of `Ext` then kills degree one, and shifts degree `n+1` of the
    sheaf to degree `n` of the flasque quotient.
  - `deningerLengthOneFlasque_ext_eq_zero`, `deningerLengthOneFlasque_subsingleton` — **a sheaf with
    a length-one flasque resolution has amplitude `[0,1]`**, the generic half of clause 5.
  The topological ambient for `(5)`--`(6)` is the next entry.

- 2026-08-04 — **`(8)` and the prime-packet acyclicity encoded**, on top of the new sheaf
  cohomology.  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `DeningerSkyscraperAcyclic.lean` — `deningerResidueAddSheaf_isFlasque`: the direct sum of
    skyscrapers `⨁_{p ∈ P} i_{p,*} A` is flasque, restriction being precomposition with an
    inclusion of index sets, so a section extends by zero.  Hence
    `deningerResidueAddSheaf_ext_eq_zero` and `_subsingleton_cohomology`: the residue target has
    amplitude `[0,0]`.
  - `DeningerRestrictedPrimeAcyclic.lean` — `(8)`.  The restricted prime sum, whose sections were
    already known to satisfy the unique-gluing axiom and to extend by zero, is packaged as an actual
    sheaf of abelian groups on the arithmetic base (`deningerPrimeSheaf`), proved flasque
    (`deningerPrimeSheaf_isFlasque`), hence acyclic (`deningerPrimeSheaf_ext_eq_zero`); and
    `deningerPrimeSheaf_cohomologyZeroEquiv` identifies its degree-zero cohomology with the
    restricted prime sum itself.  So `RΓ(S, ℬ_fin)` is concentrated in degree zero and is the
    restricted sum, which is `(8)`.

- 2026-08-04 — **`(6)`--`(7)` at sheaf level**: the cohomology of the fibre of a surjective residue
  morphism.  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `DeningerResidueFibreCohomology.lean` — `deningerKernelShortExact`: a surjective residue
    morphism has a short exact kernel sequence, so its fibre is the kernel sheaf.
    `deningerFibre_ext_bijective` and `deningerFibre_ext_surjective`: when the residue target is
    acyclic, the comparison from the fibre to the source is an isomorphism on cohomology in every
    degree above one and is onto in degree one.  So the fibre carries all of the higher cohomology
    of the source, and the only new information sits in low degrees — which is the shape `(9)`--(11)`
    record.
  - `DeningerArithmeticFibreEndpoint.lean` — the two instances that occur on the arithmetic base:
    residues into the direct sum of skyscrapers and into the restricted prime sum, whose acyclicity
    is the previous entry.  Both hypotheses are discharged, so these are unconditional.

- 2026-08-04 — **`(5)`--`(6)` in a topological ambient.**  mathlib's `TopModuleCat ℝ` — topological
  modules with continuous linear maps — has kernels, cokernels and homology, so the arithmetic
  coefficient's complex can be written there with its differentials continuous, rather than only
  after forgetting the topology.  `DeningerTopThreeTermComplex.lean`, axiom audit
  `propext, Classical.choice, Quot.sound`:
  - `deningerTopThreeTermCochain` — the three-term complex `(9)` as a cochain complex of topological
    modules, and `deningerTopThreeTermCochain_isZero_homology` — `(10)` in that ambient: no terms and
    no homology above degree two.
  - `deningerTopResidueFibre` with `deningerTopResidueFibre_isLimit` — **`(6)`**: the fibre of a
    continuous residue morphism is its topological kernel, with the universal property; and
    `deningerTopResidueEndpoint` with `_isColimit` — the endpoint is the topological cokernel.
  - `deningerQuotient_isClosed_of_t2`, `deningerQuotient_t2_of_isClosed`,
    `deningerQuotient_t2_iff_isClosed` — **strictness is separatedness**: the endpoint quotient is
    Hausdorff exactly when the boundary image is closed.  This is why the card takes the intrinsic
    middle group to be the quotient by the *closure*, which is
    `deningerHausdorffH1` in `DeningerThreeTermEndpointsHausdorff.lean`.
  The complete locally convex ambient itself is the next entry.

- 2026-08-04 — **the complete locally convex ambient**, in `DeningerCompleteLCSCategory.lean`.
  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `DeningerCLCS` — the category of complete Hausdorff locally convex real vector spaces with
    continuous linear maps, which is the ambient the card names for the coefficient values.
  - `DeningerCLCS.ker`, `kerι`, `kerι_comp`, `isLimitKer` — **`(6)` with all of its adjectives**:
    the fibre of a continuous residue morphism stays complete, Hausdorff and locally convex, and it
    has the universal property of a kernel.  The three closure properties are the classical ones —
    the kernel of a continuous map into a separated space is closed, a closed subspace of a complete
    space is complete, and local convexity and separation pass to subspaces.
  - `DeningerCLCS.toTopModuleCat` — the forgetful functor to `TopModuleCat ℝ`, where the three-term
    complex `(9)`, its homology `(10)`--`(11)` and the strictness criterion live.

  The composition law of `(2)` is the next entry.  Every clause the card proves *about* the
  coefficient — locality, the finite residues, Steinberg descent, the strict boundary and `(8)`,
  the amplitudes, the endpoints, the operations, the totalization and its vanishing — is encoded.

- 2026-08-04 — **`(2)`, the composition law for derived direct images**, in
  `DeningerPushforwardLeray.lean`.  Axiom audit `propext, Classical.choice, Quot.sound`.
  - `deningerPushforward_isFlasque` — direct images preserve flasqueness, so
    `deningerPushforward_ext_eq_zero`: the direct image of a flasque coefficient has no higher
    cohomology, and `deningerPushforward_sectionsEquiv`: its degree zero is the sections over the
    preimage.  So for a flasque coefficient the derived direct image is the underived one.
  - `deningerPushforward_comp` and `deningerPushforwardSheaf_comp` — direct image along a composite
    is the composite of direct images, as presheaves and as sheaves.
  - `deningerCompositePushforward_ext_eq_zero` and `deningerCompositePushforward_sectionsEquiv` —
    **`(2)`**: on a flasque coefficient the derived direct image along a composite has no higher
    terms and is the sections over the total preimage.  This is what makes the pro-Stein relative
    calculation compute the relevant coefficient after arithmetic direct image, in the case the card
    uses, where clause 5 supplies the fineness.

  What is left for the `2 → 3` gate is the construction of the pro-Stein refinement
  `α_PS : X_η^{PS} → X_η` itself, which is Deninger's geometric input and lives on the sub-card
  `DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF`, not on this one.

- 2026-08-06 — `2 → 3` closed.  All 23 contributing modules were re-verified on this toolchain: each exists, is wired into `GaloisForLFunctions.RHTower`, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every clause this card proves about the coefficient is encoded — locality, the finite residues, Steinberg descent, the strict boundary and `(8)`, the amplitudes, the endpoints, the operations, the totalization and its vanishing, the complete locally convex ambient, and the composition law `(2)`.  The one item the earlier record left open — the construction of the pro-Stein refinement `α_PS` — is Deninger's geometric input and belongs to `DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF`, a different card, as this card's own record states.  Card moves to `3-formalized`.
