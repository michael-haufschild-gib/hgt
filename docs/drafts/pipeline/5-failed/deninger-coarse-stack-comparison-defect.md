# Coarse/stack comparison defect

- **ID:** `deninger-coarse-stack-comparison-defect`
- **Stage:** 5-failed
- **Type:** RETIRED DIAGNOSTIC CONJECTURE
- **Label:** `DAC_COARSE_STACK_COMPARISON_DEFECT`
- **Parent:** `deninger-frobenius-coherence-defect-spectrum`
- **Statement:** a coarse-to-derived comparison cone is a valid
  diagnostic object but is not a source construction of Deninger's
  middle arithmetic cohomology.

## Retraction

The comparison triangle below exists formally, and
`DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER` remains a correct abstract
homological-algebra theorem.  Promoting its fiber to the definition of
the arithmetic middle degree was nevertheless a wrong research
priority: it makes an auxiliary derived quotient computation control
Deninger's theory, although Deninger's source is already the
underived invariant sheaf followed by its own hypercohomology.

No theorem identifies the derived quotient with the arithmetic
endpoint, and the free abelian rational-power group contributes
higher Koszul directions.  More importantly, none of this is needed
to define or calculate the source complex.

**Strongest positive survivor:** failure of exact invariants remains a
useful no-go against scalar collapse.  Constructive work moves to
`DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`, which
computes the coarse invariant sheaf intrinsically over the arithmetic
curve.

## Canonical defect object

For
\[
 c:[\widetilde X/\mathbb Q_{>0}]
 \longrightarrow X
\]
and the corrected analytic arithmetic Tate--Milnor coefficient
\(\widetilde{\mathscr A}_{\mathrm{arith}}\), after finite
Rost--Schmid localization and real signature gluing, define
\[
 \mathscr D_c
 =
 \operatorname{Cone}\!\left(
 c_*\widetilde{\mathscr A}_{\mathrm{arith}}
 \longrightarrow
 Rc_*\widetilde{\mathscr A}_{\mathrm{arith}}\right)[-1].           \tag{1}
\]
There is a flow-equivariant triangle
\[
 \mathscr D_c
 \longrightarrow c_*\widetilde{\mathscr A}_{\mathrm{arith}}
 \longrightarrow Rc_*\widetilde{\mathscr A}_{\mathrm{arith}}
 \longrightarrow\mathscr D_c[1].                                  \tag{2}
\]

The middle term of `(2)` is the corrected coefficient after applying
Deninger's degreewise invariant-sheaf construction.  It is
`DAC_TRUE_TO_APPROXIMATE_DERIVED_COEFFICIENT`, not the raw
rational-Witt sheaf.  The right term is an algebraic endpoint
comparison target, not the definition of arithmetic cohomology.
`DAC_COARSE_STACK_EXACTNESS_SCALAR_SPECTRUM_NO_GO` proves that
exact coarse/stack comparison cannot by itself produce the desired
spectrum.  `DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER` proves that
\(\mathscr D_c\) exhausts the middle degree as soon as the derived
term has exactly Milnor--Arakelov endpoint cohomology and the canonical
map is an isomorphism in degrees zero and two.

## Conjecture

`[CONJECTURE] [DAC_COARSE_STACK_COMPARISON_DEFECT]`

1. The quotient groupoid and the complete locally convex coefficient
   admit derived direct image, and `(1)` is defined in the same
   topological derived category as
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
2. On the quotient-adapted pro-Stein chart basis, the local scalar
   Frobenius homotopies define the cocycles
   \[
     c_{m,n}=h_{mn}-F_mh_n-a_nh_m
   \]
   of `DAC_LOCAL_FROBENIUS_HOMOTOPY_DEFECT`; their Čech classes map
   canonically into \(\mathbb H^1(X,\mathscr D_c)\).
3. Change of local homotopies changes these representatives only by a
   boundary in `(1)`.
4. After the standard finite-correspondence analytic realization,
   Rost--Schmid localization, and real signature gluing, prove
   `DAC_DERIVED_QUOTIENT_MILNOR_ARAKELOV_ENDPOINT`:
   \[
    R\Gamma\!\left(
      X,Rc_*\widetilde{\mathscr A}_{\mathrm{arith}}\right)
    \simeq C_{\mathrm{end}}(\mathbb Q).
   \]
   The coarse-to-derived map is the connected-rank isomorphism in
   degree zero and the degree/trace isomorphism in degree two.
5. The coarse complex has amplitude \([0,2]\).  Then
   `DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER` identifies
   \(R\Gamma(X,\mathscr D_c)\) canonically with the entire
   \(H^1_{\mathrm{Den}}[-1]\); higher comparison-defect degrees vanish
   as a theorem rather than by a declared truncation.
6. The mixed adelic/nuclear test scale extends to `(1)`, the centered
   flow is non-scalar on its harmonic image, and prime-power
   correspondence germs compute its local trace.

## Construction program

1. Present the quotient stack by the transformation groupoid and
   construct \(Rc_*\) in complete locally convex sheaves.
2. Compute the truncation filtration of `(1)` on finite
   pro-Stein/Galois/power charts.
3. Map the explicit homotopy cocycles into the first truncation piece
   and prove independence of choices.
4. Compute the derived quotient term through the generic/prime
   Rost--Schmid hypercover and identify it with the real
   Milnor--Arakelov endpoint complex.
5. Prove coarse amplitude and endpoint isomorphisms; apply the
   canonical fiber theorem.  Do not truncate group cohomology by
   declaration.
6. Extend the cup pairing and Kähler Hodge metric to the harmonic image
   of the defect.
7. Compute fixed-correspondence traces before any zeta-divisor
   comparison.

## Falsifiers

- If `(1)` is acyclic, this mechanism is eliminated by the scalar
  no-go.
- If the degreewise invariant sheaf cannot be constructed from the
  corrected equivariant coefficient, `(1)` is not Deninger's object.
- Nonzero middle or higher cohomology in the derived quotient term
  falsifies the endpoint conjecture and prevents exhaustivity.
- The free abelian group \(\mathbb Q_{>0}\) has higher Koszul
  syzygies; an unexplained two-term group-cohomology truncation is
  invalid.
- A defect built from Xi zeros or an RH-equivalent metric is circular.
- Non-scalar action without the source prime trace does not identify
  zeta spectrum.

## Current status

- Corrected equivariant cover sheaf, canonical comparison triangle,
  exactness no-go, and canonical middle-fiber theorem: paper-proved.
- Universal Frobenius homotopy cocycle: paper-proved; Lean written.
- Topological derived direct image, cocycle identification, amplitude
  cancellation, Hodge completion, and trace: open.

**Verdict:** `RETIRED AS SOURCE CORE; COMPARISON CONE RETAINED ONLY AS
A DIAGNOSTIC NO-GO.  POSITIVE SURVIVOR IS THE COARSE-SHEAF
LERAY--ROST--SCHMID RESOLUTION`.

## Log

- 2026-07-26 — Replaced an ad hoc defect target by the canonical
  coarse/quotient-stack comparison cone.
- 2026-07-27 — Applied the comparison to the corrected arithmetic
  Tate--Milnor sheaf.  The canonical fiber theorem upgrades the defect
  from a possible summand to the entire middle degree conditional only
  on the derived quotient endpoint computation.
- 2026-07-27 — Retracted that promotion.  Source construction now
  computes Deninger's coarse invariant sheaf directly; no derived
  quotient endpoint is a dependency.
