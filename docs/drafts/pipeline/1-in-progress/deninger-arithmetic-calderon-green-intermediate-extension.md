# Arithmetic Calderón--Green intermediate extension

- **ID:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE WITH LOCAL DOMAINS PROVED
- **Label:** `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** Deninger's arithmetic coefficient admits a global
  relative/extended Calderón domain whose nuclear cohomology is formed
  before Hilbert completion; its harmonic boundary defect is
  cup-isometric and faithful over the Meyer quotient.

## Why this is the remaining Hodge object

Ordinary unweighted Cheeger middle extension is canonical at the
arithmetic normal strata because their links are circles and hence
Witt.  It is nevertheless the wrong arithmetic domain:
`DAC_STANDARD_CHEEGER_MIDDLE_EXTENSION_ARITHMETIC_NO_GO` proves that
it deletes every nonzero logarithmic residue.

The correct local objects are now source-proved:

1. `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY` retains
   \(d\log z\) as extended \(L^2\) Lagrangian data at every prime;
2. `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN` makes the unitary-face
   Poisson extension the minimal-energy representative of a relative
   degree-one boundary defect;
3. `DAC_REAL_ORIENTATION_TWISTED_HODGE_APEX` supplies the real
   orientation-sign Hodge exchange;
4. `DAC_AFFINE_PRO_LOG_PRIME_HODGE_OVERLAP` identifies the oriented
   conformal stars on generic/prime overlaps.

Thus the missing object is not a local star or a local self-adjoint
extension.  It is the global incidence law that glues these
Lagrangian boundary packets through the full Tate--Milnor relative
cells and the restricted prime/real totalization.

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION]`

Let \(\mathscr A_{\mathrm{arith}}\) be the source coefficient obtained
from the equivariant Tate--Milnor unit amalgamation, strict
Rost--Schmid prime residues, and real orientation boundary.  There is
a nuclear rigged Hilbert complex
\[
 \mathcal E_{\mathrm{arith}}
 \hookrightarrow
 \mathcal H_{\mathrm{arith}}
 \hookrightarrow
 \mathcal E_{\mathrm{arith}}'
                                                               \tag{1}
\]
with a closed differential \(Q\), satisfying the following clauses.

1. **Local domain.**  On a unitary Kummer boundary chart, `(1)`
   restricts to the homogeneous relative Calderón domain of
   `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.  At a finite prime it
   restricts to the extended cylindrical domain of
   `DAC_ARITHMETIC_EXTENDED_CUSP_HODGE_BOUNDARY`.  At the real place
   it uses the orientation-sign pair.  These restrictions agree on
   every already-proved generic/prime and real overlap.

2. **Milnor incidence before completion.**  The free unit algebra,
   every Steinberg cell, every higher relative syzygy, and every
   residue/corestriction map act on the nuclear test domain before any
   Hilbert completion.  Their Green boundary maps assemble into a
   closed arithmetic Cauchy relation
   \[
    \Lambda_{\mathrm{arith}}
    \subset
    \mathcal B_{\mathrm{arith}}
      \oplus\mathcal B_{\mathrm{arith}}'                       \tag{2}
   \]
   which is Lagrangian for the sum of local Green forms.  The
   projective-ray augmentation is a derived incidence quotient, not an
   orthogonal parallel-resistor quotient.
   `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT` gives the
   precise construction target: enhance the two legs of the already
   existing derived unit pushout to Lagrangian morphisms over a
   one-shifted free-unit Green phase space.

3. **Arithmetic intermediate extension.**  The domain of \(Q\) lies
   between the compactly supported/minimal domain and the
   distributional maximal domain.  Its relative boundary quotient is
   exactly `(2)`.  It is invariant under the Hodge operator, and
   \[
    Q^2=0,\qquad
    \ker Q/\overline{\operatorname{im}Q}
    \cong\ker Q\cap\ker Q^\dagger.                              \tag{3}
   \]
   Nuclear cohomology is taken before Hilbert completion; completion
   of `(3)` is faithful.

4. **Poisson comparison.**  Smooth Deninger suspension and unit
   augmentation give a strict multiplicative chain map
   \[
    \mathcal E_{\mathrm{arith}}^\bullet
    \longrightarrow
    C^\bullet_{\mathrm{PZ}}
   \]
   inducing
   \[
    H^0=\mathbb C,\qquad
    H^1=M_\zeta,\qquad
    H^2=\mathbb C(-1).                                        \tag{4}
   \]
   The degree-one differential is the already-proved source flow sum
   \(Z=\sum_{n\ge1}(\phi^{\log n})^*\).

5. **Green supertrace identity.**  The global Green--Stokes boundary
   pairing equals the convolution supertrace defining Paugam's
   unconditional form:
   \[
    \int_{\mathcal F}\alpha\wedge\beta
    =
    \operatorname{Tr}_{+}
      (F*JG-G*JF)
    =
    \psi([F],[G]).                                             \tag{5}
   \]
   Equality is proved on the nuclear cochain core from Poisson
   summation, residue/corestriction, and the real Fourier boundary,
   before taking any spectral decomposition.
   `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION` identifies the exact
   multiplicative boundary cocycle and the required \(Z\)/Fourier
   correction terms.
   `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR` shows why the source
   object must be a closed relation/almost-projector modulo the
   nuclear ideal, not an assumed complemented splitting.  The
   remaining completion/sector statement is
   `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

6. **Positive Hodge completion.**  The local stars and coefficient
   orientation assemble to an anti-linear
   \(J^2=-1\) on harmonic degree one.  By `(5)`,
   \[
    h(x,y)=\psi(x,Jy)
   \]
   is the completed positive Dirichlet/Green energy.  The source flow
   has weight one, so \(e^{-t/2}\phi^{t*}\) is a strongly continuous
   unitary group.

7. **Riesz spectral faithfulness.**  Every order-zero Meyer
   eigenfunctional is bounded for the Hodge norm and its Riesz
   representative lies nontrivially in the completed generator
   domain.  This is the RH-only condition of
   `DAC_RIESZ_EIGENFUNCTIONAL_HODGE_PURITY`.  The full arithmetic
   theory additionally retains every finite-order generalized jet,
   domain filtration, block multiplicity, and nuclear character.

## Exact proof program

1. Form the restricted nuclear direct sum of local boundary test
   spaces, retaining place support and the product-formula
   \(L^1\)-channel.
2. Lift each relative Tate--Milnor cell to a correspondence between
   local Calderón graphs.  Construct
   `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`: the analytic
   leg is the exact graph of Poisson energy and the Milnor leg is the
   shifted conormal encoded by the full relative Sullivan resolution.
3. Prove higher-cell compatibility inductively from the homotopy
   pushout universal property; only then close the total Cauchy
   relation.
4. Use `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` to remove the
   finite-packet position--momentum fibre, then prove that its
   contracting homotopies pass strictly through the nonuniform
   nuclear system.
5. Establish maximal isotropy of `(2)` by a global Green formula and
   exactness of the arithmetic boundary complex.
6. Use local Dirichlet decompositions to construct the global harmonic
   projection.  Prove a uniform estimate on every finite
   field/place/lattice stage and pass through the strict nuclear
   system.
7. Smoothly suspend before completing.  Apply the already-proved
   projective-ray augmentation resolution and Poisson complex
   comparison.
8. Prove `(5)` on elementary Kummer/Schwartz packets.  Both sides are
   source trace expressions; extend by nuclear continuity.
   Construct and compare the global Calderón Hardy polarization
   relation as
   specified by
   `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`; a trace formula
   without the relative-polarization comparison is insufficient.
9. Prove Hodge-norm bounds and generator-domain membership for the
   pulled-back order-zero Meyer functionals.  Then prove the
   filtration-compatible statement for every higher generalized jet.
10. Apply abstract Hilbert-complex Hodge decomposition and
   `DAC_TWISTED_KAHLER_RIEMANN_FLOW_PURITY`.

## Falsifiers

- A Steinberg or higher relative cell with nonzero Green boundary
  destroys isotropy of `(2)`.
- Failure of maximal isotropy leaves an unspecified boundary
  extension and does not define arithmetic cohomology.
- Orthogonal Hilbert completion before incidence makes the scalar
  quotient seminorm zero.
- If `(5)` differs by a nonconstant spectral multiplier, local
  positivity does not transport to Deninger's cup product.
- Density of the comparison image is not faithfulness on the strong
  dual; clause 7 is mandatory.
- Any use of zeta zeros to define the boundary metric, star, incidence
  relation, or completion is circular.

## Current status

- Local unitary-face relative Calderón domain: proved.
- Local prime extended \(L^2\) residue domain: proved.
- Local real orientation-sign domain: proved.
- Generic/prime conformal overlap: proved.
- Nuclear smooth suspension and algebraic ray augmentation: proved.
- Strict source complex comparison with \(C^\bullet_{\mathrm{PZ}}\):
  proved before Hodge completion.
- Global Milnor-incidence Lagrangian closure: open.
- Green supertrace/cup identity: open.
- Harmonic faithfulness on Meyer generalized jets: open.

This card is the exact positive-Hodge gate in `docs/Deninger
program.md`.  The archimedean conormal/dual-conormal construction is a
separate Lefschetz trace domain and is not used here.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Frederic Paugam, *Spectral symmetries of zeta functions*,
  arXiv:0803.0199.
- Eugenie Hunsicker, *Extended Hodge Theory for Fibred Cusp
  Manifolds*, arXiv:1408.3257.
- Pierre Albin, Eric Leichtnam, Rafe Mazzeo, Paolo Piazza,
  *Hodge theory on Cheeger spaces*, arXiv:1307.5473.

## Log

- 2026-07-27 — Replaced the residue-killing ordinary Cheeger domain
  by a two-boundary relative/extended Calderón construction.  Closed
  both local domains and isolated global Milnor-incidence Lagrangian
  closure, Green supertrace identity, and generalized-jet faithfulness
  as the remaining theorem.
