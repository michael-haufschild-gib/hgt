# Deninger--Poisson relevant-complex comparison

- **ID:** `deninger-poisson-relevant-complex-comparison`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE with exact construction target and falsifiers
- **Label:** `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`
- **Parent:** `deninger-poisson-zeta-three-term-cohomology`
- **Statement:** the Poisson--zeta analytic complex is the relative
  middle summand of the relevant derived coefficient
  \(R\alpha_*\mathcal G\) on Deninger's rational-Witt approximation.

## Deninger's missing object

Let
\[
 \alpha:X_{\mathrm{true}}[\mathbb C]
 \longrightarrow X_{\mathrm{Den}}(\mathbb C)
\]
be the conjectural map from the true arithmetic space to Deninger's
rational-Witt approximation for
\(X_0=\operatorname{Spec}\mathbb Z\).  Deninger states that cohomology
on the true space should then be computed on the approximation with a
relevant complex \(R\alpha_*\mathcal G\).

For the \(\mathbb Q\)/Riemann-zeta object, \(\mathcal G\) may have an
additional real form, but its degree-one cohomology must be equipped
with the canonical odd \(K_{\mathbb R}\) structure.  Deninger's
no-real-coefficients theorem excludes an untwisted real coefficient
only as a theory functorial over all number fields; his obstruction uses
symplectic Artin representations.  The constant and Arakelov endpoint
lines are even and retain real forms.  Accordingly `(2)` is a comparison
of complex complexes with odd degree-one parity.  Genuine no-real
quaternionic descent is a separate full-number-field extension gate.

The strict shifted stratum coefficient already constructs the algebraic
endpoint subcomplex
\[
 C^\bullet_{\mathrm{end}}
 =
 \mathbb C[0]\oplus
 [P_\mathbb Q\to D_{\mathrm{Ar},\mathbb Q}]_{[1,2]}.
\]
`DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY` constructs the remaining
source-defined analytic complex
\[
 C^\bullet_{\mathrm{PZ,mid}}
 =
 [H_\cap\xrightarrow{Z}H_-]_{[0,1]},\qquad
 Zf=\sum_{n\ge1}f(nx),                                             \tag{1}
\]
whose only cohomology is \(M_\zeta\) in degree one.

## Conjecture

`[CONJECTURE] [DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON]`

There is a flow-equivariant filtered quasi-isomorphism
\[
 R\Gamma_c\!\left(
   X_{\mathrm{Den}}(\mathbb C),
   R\alpha_*\mathcal G
 \right)
 \simeq
 C^\bullet_{\mathrm{PZ}},                                         \tag{2}
\]
with the following source-level construction.

1. **Generic Schwartz collar.**  The suspended generic stratum has the
   canonical dense Hilbert--Kummer refinement
   \[
   \alpha_{\rm HK}:X_{\rm HK}\longrightarrow
   X_{\rm Den}(\mathbb C)_\eta
   \]
   of `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`.  If
   \(\ell_P\in L^2(Y,\lambda)'\) is the bounded logarithmic-modulus
   functional of a refined character, then
   \[
   x([P,u])=u\|\ell_P\|
   \]
   is a canonical global radial coordinate on the nonunitary locus.
   The radial compactly supported Schwartz cosheaf identifies with
   \(H_-\).
   Pointwise polar decomposition splits the refined character into its
   unitary phase and Hilbert logarithmic modulus.  By
   `DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION`, the
   nonzero modulus is
   \(S(H_{\rm Kum})\times\mathbb R_{>0}\) and its sphere is
   contractible.  Thus modulus-angular ordinary cohomology is already
   reduced to the radial factor; the unitary phase remains the
   Tate--Milnor coefficient.

2. **Poisson domain.**  The even real Betti--Fourier realization of the
   generic coefficient has the closed codimension-two domain
   \(H_\cap\), characterized by vanishing of the two endpoint
   functionals \(f(0)\) and \(\mathcal Ff(0)\).

3. **Arithmetic differential.**  The derived comparison differential
   is the convergent sum of discrete positive-time flow pullbacks
   \[
   \sum_{n\ge1}(\phi^{\log n})^*,
   \]
   which becomes `(1)` in the suspended coordinate.
   `DAC_SCALAR_SUSPENSION_POISSON_TRANSFER_NO_GO` proves that the
   summands cannot be deck pullbacks: those are identities after
   descent and their partial sums diverge.  Deck and flow are distinct.
   Deninger's exact relation
   \[
   [F_nP,u]=[P,nu]=\phi^{\log n}[P,u]
   \]
   and the radial law
   \(x(\phi^t y)=e^t x(y)\) prove
   \[
   (\phi^{\log n})^*(f\circ x)
   =(x\mapsto f(nx))\circ x.
   \]
   Thus the individual Poisson summands are source-proved scalar flow
   pullbacks.  The open content is their derived domain, strict
   infinite sum, and angular acyclicity.

4. **Poisson gluing.**  Real Betti duality identifies the two
   asymptotic collars by
   \(Zf=JZ\mathcal Ff\) on \(H_\cap\).  The two omitted endpoint
   functionals map to the already-constructed weights \(0\) and \(1\),
   rather than creating extra middle classes.

5. **Finite residue compatibility.**  The Euler factorization
   \[
   Z=\prod_p(1-F_p^{-1})^{-1}
   \]
   is compatible with the strict pro-log prime residue morphisms.
   Under the trace map, its logarithmic derivative produces the
   \(p^k\)-orbit distribution with coefficient \(\log p\).

6. **Cup compatibility.**  The leafwise cup product and arithmetic
   trace transport to Paugam's source trace pairing on \(M_\zeta\).

7. **Topology.**  The transported differential is strict with closed
   range.  The resulting quotient topology is Meyer's nuclear Frechet
   topology, not a Hilbert topology chosen from the zero divisor.

8. **Coefficient parity.**  On the cover, the generic complex
   coefficient is positive Hermitian and degree-one cohomology has an
   antiunitary anti-linear operator \(J\) with \(J^2=-1\).  Its
   complex-bilinear
   alternating form is
   \(\psi_E(u,v)=-h_E(u,Jv)\), so
   \(\psi_E(v,Jv)=h_E(v,v)>0\).  It descends \(M_\zeta\) as an odd
   \(K_{\mathbb R}\)-object.  For the all-number-fields extension, its
   transition cocycle additionally has no functorial real reduction.
   The endpoint constant and Arakelov degree lines descend as even
   objects.  This clause must be proved before any spectral-divisor
   evaluation.

## Why this is not a definition by desired output

Every object in clauses 1--5 is specified before the spectral theorem:

- Deninger's power correspondences \(F_n\);
- logarithmic Schwartz decay on the suspended generic flow;
- additive Fourier transform at the real place;
- two endpoint evaluation maps;
- finite-place residues and the Arakelov trace.

Zeros enter only after taking cohomology and applying Mellin transform.
The comparison is therefore falsifiable independently of RH.

## Construction program

1. Sheafify the Hilbert--Kummer bounded character refinement and its
   global radial coordinate; retain mixed \(L^1/L^2\), nuclear, and
   residue graph topologies.
2. Extend the discrete flow pullbacks to the radial graph topology and
   prove normal convergence of their sum on the right-decaying domain.
3. Prove that real Betti realization produces additive Fourier
   transform and that the two boundary maps are exactly \(f(0)\) and
   \(\mathcal Ff(0)\).
4. Use Poisson summation to identify the intersection of generic and
   real-boundary domains with \(H_\cap\).
5. Prove that the angular and unitary-locus derived summands are
   acyclic in the relative middle complex.
6. Compare finite logarithmic residues with the Euler factors
   \(1-F_p^{-1}\).
7. Prove strictness and the quasi-isomorphism `(2)`.
8. Transport cup, trace, conjugation, and the flow through `(2)`.

## Falsifiers

The conjecture fails if any of the following occurs:

- the Hilbert--Kummer bounded locus fails to sheafify over the generic
  stratum;
- the operator-norm radial topology is incompatible with the mixed
  \(L^1/L^2\) and residue graph topologies;
- the flow sum depends on a noncanonical collar presentation;
- a non-acyclic angular or unitary-locus middle summand survives;
- real realization does not give the Poisson boundary identity;
- finite residue maps disagree with an Euler factor
  \(1-F_p^{-1}\);
- the comparison image is not closed;
- the transported cup pairing differs from Paugam's trace pairing;
- either endpoint functional survives in relative \(H^1\).
- the degree-one transition cocycle admits an ordinary functorial real
  reduction.

## Exact status

Proved independently of `(2)`:

- strict finite and real endpoints;
- the Poisson--zeta source complex;
- scalar-deck no-go;
- the canonical dense Hilbert--Kummer refinement and its global
  descended radius;
- polar phase/modulus splitting and algebraic contraction of the
  infinite-dimensional modulus sphere;
- exact identification of every Poisson dilation with a discrete
  positive-time flow pullback;
- its \(H^0/H^1/H^2\);
- zero spectrum with multiplicity;
- Weil character;
- symplectic Poincare pairing.

Open:

- sheaf/cosheaf derived pushforward from the Hilbert--Kummer refinement;
- compatibility of radial operator-norm, nuclear, mixed, and residue
  topologies;
- strict nuclear angular contraction after tensoring with the phase
  coefficient, and correct treatment of the unitary boundary;
- quasi-isomorphism `(2)`;
- packetwise geometric Lefschetz identification;
- positive Hodge realization.

No CCM object appears in this dependency chain.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400, pp. 1--5.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.
- Frederic Paugam, *Spectral symmetries of zeta functions*,
  arXiv:0803.0199.
- Christopher Deninger, *There is no "Weil-"cohomology theory with real
  coefficients for arithmetic curves*, arXiv:2204.02714.

## Log

- 2026-07-27 — Isolated the exact geometric comparison between
  Deninger's missing relevant complex and the independently constructed
  Poisson--zeta middle coefficient.
- 2026-07-27 — Corrected the comparison category using Deninger's
  no-real-coefficients theorem: degree one requires twisted complex
  quaternionic descent, not complexification of a real leaf complex.
- 2026-07-27 — Proved scalar deck pullback cannot realize Meyer's
  zeta operator and replaced the ambiguous \(F_n^{-1}\) sum by
  coefficient transfers.
- 2026-07-27 — Corrected that provisional replacement: fixed-height
  Frobenius is discrete positive-time flow.  The canonical
  Hilbert--Kummer suspension radius makes its scalar pullbacks exactly
  Meyer's dilation terms; no conjectural transfer is needed for the
  individual summands.
