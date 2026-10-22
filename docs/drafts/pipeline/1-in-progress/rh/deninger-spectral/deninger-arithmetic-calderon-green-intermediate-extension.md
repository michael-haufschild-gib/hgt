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

The gapless all-prime rational Kummer analytic leg is no longer part of that missing law.
`DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE` constructs a canonical nuclear completion using
multiplicative prime-exponent height.  Prime-log generator and its Green inverse are continuous
with one height-seminorm loss; global free-unit Calderón graph is closed Lagrangian; Hodge sign,
Hardy projectors, power maps, reflection, and every centered Mellin jet are continuous.
`DAC_BALANCED_WORD_HEIGHT_BAR_STRICT_CONTRACTION` further constructs the entire rational Milnor
word source: product-of-letter height plus every exponential length seminorm makes its augmented
bar complex nuclear and split strictly exact in every arithmetic-character sector.  Prime-log
Green contracts nonzero total character, while continuous extra degeneracy contracts balanced
words without division.  The first unbuilt incidence is now a strict character- and
word-height-compatible cofinal Sullivan comparison.  Its first commutative layer is already
strict by `DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE`, whose normalized exterior
coproduct gives the full completed base Milnor ideal a continuous primitive.

That comparison is no longer the first hard source gate.
`DAC_DENINGER_EULER_DEPLETED_MEYER_PERIODIZATION_EXTENSION` works directly on the actual strict
Poisson coefficient. For every prime (p), with
\[
 \Delta_p=1-\tau_{\log p},\qquad Z^{(p)}=\Delta_pZ,
\]
it proves a split strict source sequence
\[
 0\longrightarrow M_\zeta\longrightarrow M_\zeta^{(p)}
 \xrightarrow{\overline{\operatorname{Per}}_p}
 C^\infty(\mathbb R/\log p\,\mathbb Z)\longrightarrow0,
\]
whose canonical kernel is the full $M_\zeta$.  Equivalently,
\[
 \Delta_pg\in Z^{(p)}(H_\cap)
 \quad\Longleftrightarrow\quad g\in Z(H_\cap).
\]
Thus one prime already closes carrier admission and conservative boundary classification.  It
also proves that every energy factoring through the complete compact prime-circle trace vanishes
on the entire admitted middle sector.
`DAC_DENINGER_HALF_DENSITY_FLOQUET_EXACT_SEQUENCE` supplies the missing ambient weight:
half-density Floquet periodization is the unique compact trace with weight one, and its
`p^{-2}` all-prime square sum is a continuous positive-definite Hilbert energy on $H_-$.
Its exact boundary error is
\[
 \operatorname{Per}_{p,1/2}\Delta_p
 =(1-p^{-1/2})\operatorname{Per}_{p,1/2}.
\]
Matching twisted depletion kills this error but also the entire admitted $M_\zeta$ sector.
Completing the uncorrected energy does not help: its Poisson quotient is exactly the Hilbert space
of critical zeros that coincide with prime Floquet Mellin nodes, with only zero-order values.
Nonresonant modes and higher jets are erased.
Every correction bounded in that raw Floquet Hilbert norm factors through the same resonance-only
quotient. The existing secondary Meyer--Poisson regulator has now been lifted around every prime
circle; its exact all-prime radical is the full reflected Calderón graph, which strictly contains
the literal Poisson boundary graph. Canonical Möbius inversion is now a pointwise right inverse on
every Meyer cochain and proves that the literal range is exactly the cochains whose Möbius
preimage extends as an $H_\cap$ function. The hard object is now the source Gamma/co-Poisson
Green--Stokes realization of that singular endpoint/Fourier regularity defect **before Hilbert
closure**. Cofinal
Sullivan/pro-Stein, generic, real, and
Poisson incidence remain possible geometric constructions of that correction.

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
   there are nuclear-continuous source operators \(P_{\mathrm{harm}}\)
   and \(G_{\mathrm{arith}}\) satisfying
   \[
   \begin{gathered}
     P_{\mathrm{harm}}^2=P_{\mathrm{harm}},\qquad
     QP_{\mathrm{harm}}=P_{\mathrm{harm}}Q=0,\\
     1-P_{\mathrm{harm}}
     =
     QQ^\dagger G_{\mathrm{arith}}
     +Q^\dagger QG_{\mathrm{arith}},                           \tag{3a}
   \end{gathered}
   \]
   with \(G_{\mathrm{arith}}\) commuting with \(Q,Q^\dagger\) on the
   source graph core.  Consequently
   \[
    Q^2=0,\qquad
    \ker Q/\overline{\operatorname{im}Q}
    \xrightarrow{\ \sim\ }
    P_{\mathrm{harm}}\mathcal E^1_{\mathrm{arith}}
    =
    \ker Q\cap\ker Q^\dagger.                                  \tag{3}
   \]
   This is a topological isomorphism in the nuclear source category,
   not only in the Hilbert completion.  Nuclear cohomology is taken
   before Hilbert completion; completion of `(3)` is faithful.  The
   bounded algebraic identities are already formalized in
   `HTGeometry.BRSTHodgeConstraint`; the open work is their unbounded
   arithmetic-domain realization and nuclear continuity.
   `DAC_STRICT_NUCLEAR_HODGE_PROJECTOR_PASSAGE` proves the abstract
   limit step once transition compatibility and place-uniform source
   seminorm bounds are established.

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

5. **Oriented Green supertrace identity.**  After the closed source
   relation has produced an exact completed Hardy projector, the
   global Green--Stokes boundary pairing equals the oriented
   convolution trace defining Paugam's unconditional form:
   \[
    \int_{\mathcal F}\alpha\wedge\beta
    =
    \operatorname{Tr}_{+}
      (F*JG-G*JF)
    =
    \psi([F],[G]).                                             \tag{5}
   \]
   Equality is proved from Poisson summation,
   residue/corestriction, and the real Fourier boundary, with the
   source Hardy orientation retained.  It cannot be stated as a
   scalar identity before that orientation exists: the
   reflection-complete Meyer character annihilates the
   antisymmetrized integrand.
   `DAC_MEYER_TOEPLITZ_GREEN_TRANSGRESSION` identifies the exact
   multiplicative boundary cocycle and the required \(Z\)/Fourier
   correction terms.
   `DAC_MEYER_POISSON_NUCLEAR_POLARIZATION_PAIR` shows why the source
   object must be a closed relation/almost-projector modulo the
   nuclear ideal, not an assumed complemented splitting.  The
   resulting completion/sector statement is
   `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`.

6. **Positive Hodge completion.**  The local stars and coefficient
   orientation assemble to an anti-linear
   \(J^2=-1\) on harmonic degree one.  By `(5)`,
   \[
    h(x,y)=\psi(x,Jy)
   \]
   is the completed positive Dirichlet/Green energy.  The source flow
   has weight one, so \(e^{-t/2}\phi^{t*}\) is a strongly continuous
   unitary group.  Faithfulness of this completion is the exact
   radical statement `DAC_GLOBAL_GREEN_ENERGY_RADICAL`: zero source
   energy must be equivalent to membership in the closed middle
   boundary subspace.

7. **Hodge--Schwartz resolvent faithfulness.**  The smooth arithmetic
   Hodge core is dense in \(M_\zeta\) for its nuclear quotient
   topology, and every off-axis resolvent of
   \(\Theta-\tfrac12\) preserves that core.  By
   `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY`, every nonzero Meyer
   order-zero or generalized-jet eigenfunctional then lies on the
   weight-one line.  This is
   `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`.  Hodge-bounded
   Riesz representation remains a stronger sufficient alternative,
   not a construction requirement.

## Exact proof program

1. Use the proved Euler-depleted extension to fix the canonical source sector
   \(\mathcal K_p=\ker\overline{\operatorname{Per}}_p\cong M_\zeta\).  No divisor, Hilbert
   completion, or cofinal syzygy choice enters this carrier.
2. Use `DAC_DENINGER_COFINAL_PRIME_PERIODIZATION_TOMOGRAPHY` only as algebraic comparison:
   every infinite family of other prime circles separates this cochain kernel and induces an
   algebraic boundary-quotient injection, while every finite family fails. The cofinal trace map
   has nonclosed range, and its rotation-invariant energies have flow weight zero.
3. Use the existing half-density seminorm through the difference Green inverse:
   \(r_p(h)=\inf_f p_{1/2}(G_ph-Zf)\). It is already nonzero, centered-flow isometric,
   prime-independent, and controls an explicit translated Gaussian sequence invisible in every
   compact prime trace. Prove its exact open radical identity
   \[
   H_-\cap\overline{Z(H_\cap)}^{\,L^1(e^{t/2}dt)}=Z(H_\cap).
   \]
4. Start from the proved Poisson--Kummer source connection, exact critical Floquet/von-Mangoldt
   current, universal diagonal sign wall, cofinal secondary regulator, Möbius regularity
   classification, and already-constructed actual Gamma/co-Poisson Green transport. Construct the
   strict cofinal Euler--Gamma/Möbius gauge defect and prove its non-diagonal unsquared
   Green--Stokes identity annihilates the resolved Green defect before polarization. Then derive
   `DAC_DENINGER_CORRECTED_TATE_FLOQUET_POISSON_DESCENT` before completion: its boundary operator
   realizes the endpoint/Fourier singularity of the canonical Möbius preimage, with kernel exactly
   \(Z(H_\cap)\), transported by \(\Delta_p\). The induced incidence must be continuous in the
   nuclear Meyer topology but cannot extend as a bounded repair of the raw Floquet Hilbert
   completion or arise from diagonal prime-circle renormalization.
   Prove the descended form is positive and faithful on \(\mathcal K_p\), is independent of the
   auxiliary prime after the canonical cross-prime depletion comparison, and is compatible with
   the real Fourier seam and centered dilation flow.
5. Produce from this relative form the Hodge-symmetric nuclear almost-involution and the closed
   global Calderón relation.  One possible geometric construction is to continue the proved
   height-Köthe/bar/first-Sullivan source through cofinal multiplicative syzygies, generic Kummer,
   real, and Poisson incidence.  If that method is used, construct
   `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`: the analytic
   leg is the exact graph of Poisson energy and the Milnor leg is the
   shifted conormal encoded by the full relative Sullivan resolution.
6. Close the total Cauchy relation after the chosen construction: its nonzero-character Green
   contraction and balanced-word extra-degeneracy contraction are already explicit on the bar
   side, but must survive the commutative conormal, real, and Poisson attachments.
7. Use `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` to remove the
   finite-packet position--momentum fibre, then prove that its
   contracting homotopies pass strictly through the nonuniform
   nuclear system.
8. Establish maximal isotropy of `(2)` by a global Green formula and
   exactness of the arithmetic boundary complex.
9. Use local Dirichlet decompositions to construct the global harmonic
   projection and Green operator.  Prove `(3a)` and a uniform estimate
   on every finite field/place/lattice stage, then apply
   `DAC_STRICT_NUCLEAR_HODGE_PROJECTOR_PASSAGE` to pass both operators
   through the strict nuclear system.
10. Smoothly suspend before completing.  Apply the already-proved
   projective-ray augmentation resolution and Poisson complex
   comparison.
11. Prove `(5)` on elementary Kummer/Schwartz packets.  Both sides are
   source trace expressions; extend by nuclear continuity.
   Construct and compare the global Calderón Hardy polarization
   relation as
   specified by
   `DAC_ARITHMETIC_CALDERON_PAUGAM_HARDY_COMPARISON`; a trace formula
   without the relative-polarization comparison is insufficient.
12. Construct the arithmetic Hodge--Schwartz graph core, prove its
   density in the nuclear Meyer quotient, and prove off-axis
   parameter-elliptic resolvent estimates that preserve it.  This
   gives the order-zero and every higher generalized-jet statement at
   once.
13. Apply abstract Hilbert-complex Hodge decomposition and
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
- Density only in the Hodge Hilbert norm is not faithfulness on the
  nuclear strong dual; source-topology density and resolvent
  preservation in clause 7 are mandatory.
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
- One-prime Euler-depleted strict admission of all $M_\zeta$, exact conservative boundary
  classification, and full compact prime-trace Hodge no-go: proved on paper.
- Global Milnor-incidence Lagrangian closure: open; it is now an optional geometric realization
  of the relative source form, not a carrier-admission gate.
- Green supertrace/cup identity: open.
- Global Green-energy radical classification: open; abstract
  nonuniform local-to-global passage is proved and Lean-formalized.
- Hodge--Schwartz core density and off-axis source-resolvent
  preservation: open.

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
