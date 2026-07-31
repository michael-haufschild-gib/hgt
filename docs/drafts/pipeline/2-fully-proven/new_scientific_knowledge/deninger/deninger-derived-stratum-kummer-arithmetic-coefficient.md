# Derived stratum-Kummer arithmetic coefficient

- **ID:** `deninger-derived-stratum-kummer-arithmetic-coefficient`
- **Stage:** 2-fully-proven
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
- [ ] 2 → 3 formalized: coefficient, totalization, and all analytic
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
