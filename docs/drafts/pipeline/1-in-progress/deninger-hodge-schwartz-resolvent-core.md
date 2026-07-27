# Arithmetic Hodge--Schwartz resolvent core

- **ID:** `deninger-hodge-schwartz-resolvent-core`
- **Stage:** 1-in-progress
- **Type:** RH-BEARING SOURCE CONJECTURE
- **Label:** `DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE`
- **Parent:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Statement:** the global Calderón--Green Hodge Laplacian has a
  source-defined smooth nuclear core, dense in the Meyer quotient,
  which is preserved by every off-axis centered resolvent.

## Source definition

Let \(\mathcal E^\bullet_{\mathrm{arith}}\) be the strict source
cochain complex before Hilbert completion, and let
\(\mathcal H^1_{\mathrm{arith}}\) be the positive completion obtained
from the global Green form.  Put
\[
  A_q=\Theta-\tfrac q2
\]
in cochain degree \(q\), and write \(A=A_1\) on harmonic degree one.
Let \(\mathcal R\) be the source regularity family: leafwise and
transverse covariant derivatives on generic charts, fibred-cusp
vector fields at finite primes, the real orientation-apex operators,
and the seminorm/weight operators defining the restricted nuclear
direct sum.  Define the harmonic source graph core without spectral
points:
\[
  \mathcal D_{\mathrm{Hdg}}
  =
  \left\{
    u\in\mathcal E^1_{\mathrm{arith}}:
    Qu=Q^\dagger u=0,\quad
    R^\alpha A^n u\in\mathcal H^1_{\mathrm{arith}}
    \text{ for every }\alpha,n
  \right\},                                                    \tag{1}
\]
with the source and graph seminorms.  The Hodge Laplacian
\(\Delta_{\mathrm{arith}}=QQ^\dagger+Q^\dagger Q\) constructs the
harmonic projection and proves regularity of representatives; it is
not assumed to commute with the conformal flow on all cochain
degrees.  Formula `(1)` uses only source differential, Green star,
flow, and source topology.

## Conjecture

`[CONJECTURE] [DAC_ARITHMETIC_HODGE_SCHWARTZ_RESOLVENT_CORE]`

The global arithmetic Calderón--Green intermediate extension
satisfies:

1. **Nuclear density.**
   The source Green identity `(3a)` of
   `DAC_ARITHMETIC_CALDERON_GREEN_INTERMEDIATE_EXTENSION` identifies
   \(P_{\mathrm{harm}}\mathcal E^1_{\mathrm{arith}}\)
   topologically with \(M_\zeta\).
   \(\mathcal D_{\mathrm{Hdg}}\) maps continuously and densely to
   \(H^1_{\mathrm{arith}}\cong M_\zeta\) in Meyer's nuclear quotient
   topology.  Hence every nonzero Meyer strong-dual functional
   restricts nontrivially to \(\mathcal D_{\mathrm{Hdg}}\).

2. **Flow regularity.**
   \(A\) acts continuously on \(\mathcal D_{\mathrm{Hdg}}\), its
   centered flow is the restriction of the source dilation flow, and
   the inclusion into the Hodge Hilbert completion intertwines both
   actions.

3. **Off-axis source resolvent.**
   For every \(z\in\mathbb C\) with
   \(\operatorname{Re}z\ne0\),
   \[
     A-z:\mathcal D_{\mathrm{Hdg}}
       \longrightarrow\mathcal D_{\mathrm{Hdg}}                 \tag{2}
   \]
   is a continuous linear automorphism.  An alternative sufficient
   time-one form is: for \(V=e^A\),
   \[
     V-c:\mathcal D_{\mathrm{Hdg}}
       \longrightarrow\mathcal D_{\mathrm{Hdg}}                 \tag{3}
   \]
   is onto whenever \(|c|\ne1\).
   By `DAC_SKEW_ADJOINT_GRAPH_CORE_RESOLVENT`, the infinitesimal
   assertion follows once the global boundary domain makes \(A\)
   skew-adjoint and makes the harmonic source regularity operators
   strongly commute with its resolvent.  A bounded-commutator
   extension would also suffice but must supply the corresponding
   graph-seminorm estimates.

4. **Parametrix is source-geometric.**
   The inverse in `(2)` is obtained from the arithmetic heat/Green
   parametrix and the global Calderón relation.  Its finite-prime and
   real boundary corrections are the already constructed
   extended-cusp and orientation-sign parametrices.  No divisor,
   zero, or upper/lower spectral list enters its construction.

5. **Strict nuclear passage.**
   Finite field/place/lattice parametrices satisfy compatible
   bounded-set estimates.  Their limit preserves every
   Tate--Milnor incidence, residue/corestriction map, and Meyer
   \(Z\)/Fourier cross term.

## Consequence

Meyer supplies, for every nontrivial zeta zero \(\rho\), a nonzero
continuous transpose eigenfunctional on \(M_\zeta\).  Clause 1 makes
its restriction to \(\mathcal D_{\mathrm{Hdg}}\) nonzero.  Clauses
2--3 and `DAC_DENSE_RESOLVENT_TRANSPOSE_PURITY` then force
\[
  \operatorname{Re}\rho=\tfrac12.
\]
This proves RH without requiring any Meyer evaluation functional to
be Hodge-bounded or represented by a vector in the generator domain.

The same argument applied to powers of `(2)` treats every generalized
Mellin jet and excludes off-axis generalized blocks.

## Proof program

1. Construct finite-packet Green Laplacians from the proved relative
   Calderón and extended-cusp domains.
2. Prove the global boundary conditions commute with the centered
   flow and Hodge graph operators.  Apply
   `DAC_SKEW_ADJOINT_GRAPH_CORE_RESOLVENT`; no separate Hilbert
   resolvent construction is then needed.
3. Show finite parametrices commute with the explicit positive
   Hodge--Koszul contractions of every Milnor relative cell.
4. Control the nonuniform all-place limit in the restricted nuclear
   direct sum, retaining the product-formula \(L^1\) channel.
5. Identify the cross-ray parametrix defects with Meyer's nuclear
   Toeplitz \(Z\)/Fourier commutators and remove them by a convergent
   Green correction.
6. Prove `(1)` is dense in the source quotient using source heat
   regularization and the strict Poisson comparison.
7. Pass the resolvent identity through reduced cohomology and verify
   `(2)` on the completed source core.

## Falsifiers

- Hilbert-space resolvent existence alone is insufficient; its
  inverse must preserve a source-dense core on which Meyer
  functionals remain continuous and nonzero.
- Density only in the Hodge Hilbert norm is insufficient; clause 1
  requires density in the nuclear quotient topology.
- A core or parametrix defined using the zeta-zero divisor is
  circular.
- Local parametrices without uniform strict-nuclear estimates do not
  establish `(2)`.
- Ordinary Cheeger \(L^2\) domains are excluded because they erase
  nonzero logarithmic residues.
- Analytic continuation of a Hilbert resolvent as a map into the
  strong dual is not enough.  Rigged-Hilbert continuation can create
  off-axis resonances.  Clause 3 requires preservation and
  surjectivity on the actual source core, on the physical resolvent
  sheet.

## References

- Christopher Deninger and Wilhelm Singhof, *Real polarizable Hodge
  structures arising from foliations*, arXiv:math/0204111.
- Christopher Deninger, *Arithmetic geometry and analysis on foliated
  spaces*, especially the reduced Hodge realization and
  \(\Theta=\tfrac12+S\) with \(S\) skew-symmetric.
- Hayato Chiba, *A spectral theory of linear operators on rigged
  Hilbert spaces under analyticity conditions*, arXiv:1107.5858.
  This supplies the rigged-Hilbert resolvent framework and also
  explains why an analytically continued dual resolvent must not be
  confused with source-core preservation.
- `DAC_SKEW_ADJOINT_GRAPH_CORE_RESOLVENT`.
- `GaloisForLFunctions.HTGeometry.BRSTHodgeConstraint` for the
  bounded algebraic Green/Hodge identities.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact RH consequence
- [ ] 1 → 2 fully-proven: global parameter-elliptic and density proof
- [ ] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-27 — Replaced the stronger pointwise Riesz condition by
  dense source-core resolvent stability.  This is the exact
  rigged-Hilbert theorem required for Meyer's strong-dual spectrum.
