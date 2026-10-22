# Unit-amalgamation derived Lagrangian enhancement

- **ID:** `deninger-unit-amalgamation-derived-lagrangian-enhancement`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE / DERIVED-SYMPLECTIC MECHANISM
- **Label:** `DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT`
- **Parent:** `deninger-arithmetic-calderon-green-intermediate-extension`
- **Statement:** the analytic Kummer and Milnor-symbol legs of
  Deninger's derived unit amalgamation are Lagrangian over a
  one-shifted free-unit Green phase space; their derived intersection
  therefore carries the canonical unshifted arithmetic cup form.

## Source-derived intersection

On a cyclotomic suspension chart, the coefficient is already defined
by
\[
 \widetilde{\mathscr A}^{M}_{F,\mathrm{geom}}
 =
 \mathscr T_{\widetilde X_F}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{M}_{F,\mathbb R},                    \tag{1}
\]
where \(\mathscr P_F\) is the free positive Tate-graded
\(E_\infty\)-algebra on the Kummer unit local system.  Passing to
derived affine spectra reverses arrows and turns `(1)` into
\[
 \operatorname{Spec}\widetilde{\mathscr A}^{M}_{F,\mathrm{geom}}
 \simeq
 \operatorname{Spec}\mathscr T_{\widetilde X_F}
 \mathop{\times}^{h}_{\operatorname{Spec}\mathscr P_F}
 \operatorname{Spec}\underline{\mathcal K}^{M}_{F,\mathbb R}. \tag{2}
\]

The base \(\operatorname{Spec}\mathscr P_F\) has no canonical
one-shifted symplectic form: its unit directions are not canonically
self-dual.  The correct ambient object is its shifted Green phase
space
\[
 \mathfrak P_F
 =
 T^*[1]\operatorname{Spec}\mathscr P_F,                       \tag{2a}
\]
which pairs unit positions with boundary momenta.  Calaque proves that
shifted cotangent stacks are canonically shifted symplectic and their
shifted conormal stacks are canonically Lagrangian.

Pantev--Toën--Vaquié--Vezzosi prove that the derived intersection of
two Lagrangian morphisms into an \(n\)-shifted symplectic derived
Artin stack is canonically \((n-1)\)-shifted symplectic.  Therefore
Lagrangian lifts of the two legs of `(2)` into `(2a)` would give an
ordinary zero-shifted symplectic Hodge enhancement.  Its projection to
the original derived unit pushout must then be proved cohomologically
faithful; equivalence is not automatic.

## Conjecture

`[CONJECTURE] [DAC_UNIT_AMALGAMATION_DERIVED_LAGRANGIAN_ENHANCEMENT]`

The source unit-amalgamation diagram has the following enhancement.

1. **Free-unit Green phase space.**  The nuclear analytic enhancement
   of `(2a)` carries its canonical one-shifted closed nondegenerate
   two-form
   \[
    \omega_{\mathrm{unit}}.                                   \tag{3}
   \]
   Its position--momentum form on the weight-one tangent core is the
   Green form
   \[
    \Omega((\varphi,\nu),(\psi,\mu))
    =
    \langle\varphi,\mu\rangle-\langle\nu,\psi\rangle
   \]
   from `DAC_KUMMER_CALDERON_GRAPH_LAGRANGIAN`.

2. **Analytic Lagrangian leg.**  The regulator leg of `(2)` lifts to an
   exact Lagrangian morphism into \(\mathfrak P_F\).  Its generating
   functional is the Poisson Dirichlet energy
   \[
    S_{\mathrm{an}}(\varphi)
    =
    \tfrac12\langle\varphi,|D_\ell|\varphi\rangle .
   \]
   Its tangent Cauchy data are
   \(\operatorname{Graph}(|D_\ell|)\), hence the weight-one
   linearization is already proved Lagrangian.

3. **Milnor conormal leg.**  The shifted conormal stack of
   \[
    \operatorname{Spec}\underline{\mathcal K}^{M}_{F,\mathbb R}
    \longrightarrow\operatorname{Spec}\mathscr P_F
   \]
   gives the Lagrangian lift of the Milnor leg into
   \(\mathfrak P_F\).  At a geometric realified chart, the relative
   Sullivan model has degree-one generators
   \[
    d w_{a,b}=a\wedge b                                      \tag{4}
   \]
   for all killed degree-two products, followed by generators killing
   every higher syzygy.  These are the derived conormal directions.
   The special Steinberg family satisfies
   \(d\log a\wedge d\log(1-a)=0\), but this tautological isotropy is
   only one check and does not replace the full conormal theorem.

4. **Arithmetic Hodge intersection.**  The derived intersection
   \[
    \mathfrak H_F
    =
    \Lambda_{\mathrm{an}}
    \mathop{\times}^{h}_{\mathfrak P_F}
    N^*[1]_{\mathrm{Milnor}}                                  \tag{5}
   \]
   of
   the analytic exact graph and Milnor shifted conormal in
   \(\mathfrak P_F\) is the constrained Poisson critical/Hodge
   object, not merely the algebraic pushout `(2)`.  Applying the PTVV
   Lagrangian intersection theorem gives a zero-shifted symplectic form
   \[
    \omega_{\mathrm{arith}}
   \]
   on \(\mathfrak H_F\).

5. **Cohomological projection.**  The forgetful projection from
   `(5)` to `(2)` has an acyclic position--momentum fibre after taking
   the source relative-middle domain.  It induces an isomorphism on
   reduced arithmetic hypercohomology and transports
   \(\omega_{\mathrm{arith}}\) to the nondegenerate alternating product
   \[
   H^1_{\mathrm{arith}}\otimes H^1_{\mathrm{arith}}
    \longrightarrow H^2_{\mathrm{arith}}\cong\mathbb R(-1).    \tag{6}
   \]
   `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY` proves this acyclicity
   at tangent level on every finite Fourier/incidence packet.
   `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` gives an explicit
   finite-stage cdga contraction.  The remaining assertion is strict
   passage through the nonuniform nuclear system and coarse suspension
   descent.

6. **Descent.**  The shifted forms and Lagrangian lifts commute
   with Galois maps, finite correspondence, power maps,
   residue/corestriction, and the real orientation-sign extension.
   Hence `(6)` descends to the coarse invariant-sheaf
   Rost--Schmid totalization.

7. **Analytic comparison.**  On the nuclear Poisson core,
   \(\omega_{\mathrm{arith}}\) equals the Green--Stokes form and
   defines an orientation-twisted Real relative trace class.  After source Green
   radical kills the chirality kernel and polar sign constructs exact
   Hardy projectors, its oriented half-trace becomes Paugam's
   convolution pairing.  It cannot become Paugam's scalar form before
   that step: reflection-complete Meyer trace cancels the alternating
   wedge.

## Why this supplies the missing cross-ray terms

The failed orthogonal ray completion treated projective Kummer rays as
independent parallel boundary channels.  It therefore allowed a fixed
scalar vector to be split among arbitrarily many rays at energy tending
to zero.

The derived intersection `(2)` retains:

- the common free-unit cotangent directions;
- every Steinberg relation;
- higher Tor/syzygy directions;
- residue and real-orientation incidence.

The pairing from a Lagrangian derived intersection couples precisely
these tangent and obstruction directions.  It is therefore a
source-defined candidate for the non-diagonal terms required by the
global Calderón form.  No arbitrary ray weights or chosen spectral
atoms enter.

## Exact proof program

1. Write the completed relative cotangent complexes of
   \(\mathscr P_F\), \(\mathscr T_{\widetilde X_F}\), and
   \(\underline{\mathcal K}^{M}_{F,\mathbb R}\) on each finite
   pro-Stein chart.
2. Construct the finite-stage shifted cotangent phase stack and prove
   that its canonical form restricts to the Green position--momentum
   pairing.
3. Construct the analytic exact graph from \(S_{\mathrm{an}}\);
   identify its nondegeneracy map with the proved Calderón trace
   isometry.
4. Compute the shifted conormal of the Milnor leg using the relative
   Sullivan model `(4)` and all higher generators.
5. Form the Hodge intersection `(5)` and apply the PTVV
   Lagrangian-intersection theorem.
6. Prove the position--momentum fibre is acyclic on the
   relative-middle domain and establish clause 5.
7. Pass through finite-stage Cartan acyclicity, strict filtered
   colimits, Galois invariants, and Rost--Schmid totalization.
8. Compute the induced form on elementary Schwartz/Kummer packets and
   compare it with Paugam's trace formula.

## Falsifiers

- \(\operatorname{Spec}\mathscr P_F\) itself is not silently declared
  shifted symplectic.  Failure to construct the shifted cotangent
  analytic phase space blocks the route.
- Steinberg isotropy alone is insufficient: the realified geometric
  Milnor quotient kills all positive products, and the full relative
  Sullivan conormal is load-bearing.
- A homotopy pushout of algebras is not automatically a Lagrangian
  intersection.  Clauses 1--5 are load-bearing extra structures.
- The shifted cotangent/conormal intersection generally has extra
  position--momentum directions.  If their relative fibre is not
  acyclic, \(\mathfrak H_F\) is not a Hodge realization of the source
  coefficient.
- PTVV is an algebraic derived-Artin theorem.  Application to nuclear
  analytic sheaves requires a finite-stage algebraic model plus a
  separately proved strict analytic passage.
- A zero-shifted symplectic form supplies Poincaré duality, not
  positivity.  The compatible real Hodge/Calderón metric and
  generalized-jet faithfulness remain separate obligations.
- No zeta zero may define `(3)`, either Lagrangian leg, or the
  completion.

## Current status

- Derived unit-amalgamation identity `(1)`: proved.
- Full functorial relative Sullivan/Milnor cell resolution: proved
  algebraically.
- Analytic weight-one Calderón graph: proved Lagrangian.
- Global rational free-unit analytic leg: now proved on the nuclear prime-log height-Köthe
  completion.  Its Green inverse has a one-source-height-step estimate, its graph is closed
  Lagrangian, its Hardy projectors are exact, and all centered Mellin jets remain continuous.
- Entire rational Milnor word leg: now proved on the product-letter-height/exponential-length bar
  completion.  Every arithmetic-character sector is split strictly exact; prime-log Green/Hodge
  operators extend as chain operators, and the balanced sector is contracted by extra degeneracy.
- First commutative Sullivan leg: linearized quadratic attachment and normalized exterior
  coproduct now give a continuous primitive for the full completed base Milnor ideal, including
  balanced character zero.
- Direct actual-coefficient admission: the Euler-depleted Meyer periodization theorem gives at
  every prime a split strict extension with $M_\zeta$ as the canonical zero-periodization
  kernel. It proves one-prime boundary conservativity and rules out every compact prime-trace
  energy on the admitted sector.
- Ambient cochain Hodge energy: half-density Floquet periodization and its $p^{-2}$ all-prime sum
  give continuous positive-definite weight-one energy. Its ordinary Euler-boundary leakage and
  matching-depletion annihilation alternative are computed exactly. Its Hilbert quotient is
  resonance-only and every bounded repair factors through it. The cofinal secondary two-collar
  lift has exact radical equal to the reflected Calderón graph, strictly larger than the Poisson
  range. Canonical Möbius right inversion identifies the range exactly by $H_\cap$ regularity of
  its preimage.
- Finite positive graph--conormal fibre: proved transverse and
  acyclic, including formal complementary-sum theorem in Lean.
- Finite positive Hodge--Koszul fibre: explicit cdga contraction
  proved.
- Canonical shifted cotangent/conormal theorem: literature-proved in
  the derived-Artin category.
- Cofinal linearized completion of genuine multiplicative syzygies beyond the first Sullivan
  attachment, and its strict comparison with the height-Köthe bar/pro-Stein conormal: open but no
  longer a carrier-admission gate. It is one possible geometric realization of the upstream strict
  cofinal Euler--Gamma/Möbius gauge defect and its non-diagonal Green--Stokes source differential.
  The actual Gamma/co-Poisson Green transport already exists; corrected Tate--Floquet/Möbius
  endpoint/Fourier descent is a downstream interface induced by the missing source differential. The
  comparison must carry Green contraction on nonzero character and incidence contraction on
  balanced words; algebraic augmentation to the same two-term target does not prove strictness
  after completion.
- Hodge-intersection construction and relative fibre acyclicity: open.
- Nuclear analytic PTVV passage: open.
- Paugam comparison: open.

## References

- Tony Pantev, Bertrand Toën, Michel Vaquié, Gabriele Vezzosi,
  *Shifted Symplectic Structures*, arXiv:1111.3209, Lagrangian
  intersection theorem.
- Damien Calaque, *Shifted cotangent stacks are shifted symplectic*,
  arXiv:1612.08101.
- `DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION`.
- `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.
- `DAC_KUMMER_RELATIVE_CALDERON_POISSON_DOMAIN`.
- `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION`.
- `DAC_UNIT_AMALGAMATION_RESIDUE_UNIVERSAL_DESCENT`.

## Log

- 2026-07-27 — Identified the derived unit pushout as the exact
  location for cross-ray Green terms and formulated the PTVV
  shifted-cotangent/conormal enhancement, retaining the full relative
  Sullivan cell tower and explicit analytic/functorial falsifiers.
- 2026-07-27 — Formalized finite graph/conormal direct-sum
  transversality; no finite linear derived excess remains.  Open
  content is analytic Lagrangian lifting and strict nuclear descent.
