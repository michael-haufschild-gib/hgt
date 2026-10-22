# Deninger--Poisson relevant-complex comparison

- **ID:** `deninger-poisson-relevant-complex-comparison`
- **Stage:** 1-in-progress
- **Type:** COMPLEX COMPARISON THEOREM WITH CUP/HODGE CONJECTURE
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

The underlying complex, topology, flow, and endpoint comparison in
`(2)` are proved by
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION`.  The remaining
content under this broader label is clauses 6 and 8 as
source-geometric cup/parity statements, plus their Hodge and Lefschetz
consequences.

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
   On the positive-radius suspension,
   `DAC_DENINGER_HILBERT_KUMMER_KAHLER_ORBIT_COLLAR` upgrades this
   radial factor canonically to
   \[
     x^{-1}(1)\times\mathbb C^\times
   \]
   by adjoining the half-density circle
   \(\{(p,z):|z|^2=x(p)\}\).  Its complex leaves have weight-one
   Kähler area, local positive \(J=*c\), the critical radial measure, and
   the same discrete Poisson flow pullbacks.  This circle is not being
   identified with the unitary-character phase.  The resulting closed
   orbit leaves have tangent flow; they are the forced collar model,
   not the still-missing dense arithmetic foliation.

2. **Poisson domain.**  The closed codimension-two domain
   \(H_\cap\) now has an exact source-geometric identification.
   `DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE` proves that for the
   radial lift \(Rf(z)=f(|z|^2)\),
   \[
     Rf(0)=f(0),\qquad
     \int_{\mathbb C}Rf\,\omega
       =\frac{\pi}{2}\mathcal Ff(0).
   \]
   Hence \(H_\cap\) is precisely the common kernel of cone-apex
   restriction and leafwise top-degree Kähler trace.  The second
   functional is not a conjectural second boundary point.

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
   pullbacks.
   `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS` supplies the derived radial
   domain and strict infinite sum, while
   `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION` proves
   angular acyclicity after retaining the Tate--Milnor phase.

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

6. **Oriented cup compatibility.**  Leafwise cup product and
   arithmetic Green trace first define an orientation-twisted Real relative
   class on the source Calderón relation.  After Green-radical
   exactness produces exact Hardy projectors, its oriented half-trace
   transports to Paugam's pairing on \(M_\zeta\).  Full Meyer trace
   cannot be used: reflection mates cancel the alternating wedge.

7. **Topology.**  The transported differential is strict with closed
   range.  The resulting quotient topology is Meyer's nuclear Frechet
   topology, not a Hilbert topology chosen from the zero divisor.
   This clause is proved before the remaining arithmetic gluing by
   `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`.

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

1. **Completed:** form the Hilbert--Kummer fine source, its radial
   nuclear cosheaf, mixed \(L^1/L^2\) and residue-graph maps.
2. **Completed:** identify the discrete flow sum with Meyer's strict
   closed Poisson embedding.
3. **Completed:** contract the modulus angle by a continuous cosheaf
   chain homotopy while retaining phase, apex, and both endpoint maps.
4. **Completed:** use augmented square-zero homotopy pullback to glue
   the radial relative domain to the Tate--Milnor/Arakelov
   totalization without a raw tensor cross term.
5. **Completed at correspondence level:** the same \(F_p\) defines
   the Euler factor \(1-F_p^{-1}\) and the \(p\)-Kummer endpoint;
   packetwise fixed-orbit trace remains separate.
6. **Completed:** obtain the strict arithmetic gluing
   quasi-isomorphism `(2)`.
7. Transport source cup, trace, and odd coefficient parity through
   `(2)`.

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
- canonical global trivialization of the positive-radius flow and its
  complex Kähler half-density leaves;
- exact identification of \(f(0)\) with cone-apex restriction and
  \(\mathcal Ff(0)\) with normalized leafwise Kähler trace;
- its \(H^0/H^1/H^2\);
- zero spectrum with multiplicity;
- Weil character;
- symplectic Poincare pairing.
- nuclearity and strict closed range of the radial Poisson complex;
- strict completed tensor transport through the phase, mixed, residue,
  and endpoint topologies;
- strict angular cosheaf contraction with phase and unitary apex
  retained.
- augmented square-zero relevant-coefficient gluing and the strict
  quasi-isomorphism `(2)`;
- identification of intrinsic arithmetic \(H^1\) with \(M_\zeta\).

Open:

- global source Calderón relation, chirality-kernel theorem, and resulting oriented cup/trace
  comparison with Paugam's pairing;
- source construction of the odd coefficient parity before spectral
  decomposition;
- packetwise geometric Lefschetz identification;
- endpoint-extended positive Hodge comparison and faithfulness on
  generalized spectral jets.

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
