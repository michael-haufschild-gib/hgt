# Universal HT constraint--orientation product geometry

- **ID:** `universal-constraint-orientation-product-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / candidate theorem and publication route
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [TARGET SIGNIFICANCE 90/100]`
- **Statement:** `[CONJECTURE]` One fixed prime-log maximal-translation HT field has a rational-gauge
  moduli fiber whose finite residue chambers and finite Stanley--Reisner sewing geometries vary as
  an exact Cartesian product: every finite constraint matroid occurs in every finite sign chamber,
  while the embedded differential-translation field, Schwarz structure, generator class modulo
  `C(z)`, and prime-log pole support remain fixed.

## Goal

Upgrade single-source finite-constraint completeness from one free coordinate to a two-axis
geometry.  The first axis is the complete class of finite nonlinear differential constraint
matroids.  The second is the direct-limit cube of finite residue-sign chambers, graded by exact
negative residue index and, analytically, by Krein negative-square index.  The theorem must prove
that these axes are independent over one unpointed HT field and must identify positivity as a
distinguished coherent orientation, not a property of the unpointed field.

The proposed scientific law is positive:

> A maximally free HT field carries a universal product of finite constraint geometry and finite
> polarization geometry.  Arithmetic positivity can therefore live only on a distinguished
> cofinal section coupling the two coordinates.

For RH, the target is not an abstract no-go.  It is the necessity of an Euler-marked, FE-compatible
cofinal section which selects the positive chamber while sewing the finite-prime geometries
compatibly through the horizontal `1/log N` boundary layer.

## Exact candidate theorem

Let `B=C(z)`.  Seek one real meromorphic prime-log generator `g_*` and its embedded field

```text
K_*=B< D^n T_h g_* : n>=0, h in C >
```

with the following properties.

1. **Universal free orbit.**  A fixed countable palette of translates of `g_*` is differentially
   algebraically independent over `B` and contains the complete facet--Laurent palette of every
   finite simplicial complex.
2. **Fixed-support rational gauge fiber.**  For every finitely supported real sequence `c`, replace
   finitely many prime-log residues of `g_*` by the corresponding signed residues and call the
   result `g_c`.  Then

   ```text
   K(g_c)=K_*,   [g_c]=[g_*] in K_*/B,
   ```

   with the same Schwarz involution and the same pole support whenever no modified residue is zero.
3. **Cubical polarization.**  On a finite modified support `S`, the walls are `c_p=0`; the chambers
   are indexed by `J subset S`, and the negative residue index is

   ```text
   kappa_res(g_c)=#{p in S:c_p<0}=dist_cube(empty,J).
   ```

   The compatible finite chamber systems form the direct-limit cube.  The Pick kernel has the same
   exact negative-square index; in the FE-even realization the grading is doubled.
4. **Product completeness.**  For every finite simplicial complex `Delta`, every finite localized
   structural family, and every chamber `J`, facet sewing applied to `g_c` realizes exactly the
   localized Stanley--Reisner differential matroid of `Delta`, independently of `J`.  Conversely,
   the chamber index is independent of `Delta`.  Thus the realization map is surjective onto

   ```text
   {finite localized Stanley--Reisner differential matroids}
     x {finite subsets of N}.
   ```
5. **Pointing law.**  No exact residue/Krein positivity selector can factor through the unpointed
   structured field, its generator class modulo `B`, or any finite sewn differential matroid.  It
   must retain a rational-gauge-sensitive representative, equivalently a coherent orientation of
   the residue cube.

## Why this may clear the 90 threshold

The candidate is not the conjunction of two prior facts.  Its proposed new object is a universal
moduli product over one fixed analytic field.  It classifies which finite data are freely variable
and isolates the additional datum that a constraint-fixed HT object does not generate: a coherent
polarization.  The theorem would simultaneously contain:

- one fixed analytic field rather than one source per complex;
- every finite nonlinear differential constraint geometry;
- every finite polarization chamber and every finite negative index;
- exact orthogonality of those coordinates;
- a forced global section as the only possible location of arithmetic selection.

The 90-point claim is not granted.  It survives only if the exact product statement is not a
formal repackaging of independent parent theorems and if the analytic Pick-index coordinate is
proved, not merely named.

## RH corpus synthesis motivating the section law

The pipeline and formal tree repeatedly identify four compatible obligations.

1. Finite Euler-unit tangents are dense after the divisor is fixed; the surviving continuous datum
   is a critical all-prime tail class coupled nonseparably to the global divisor.
2. FE reciprocity lives on a signed Lagrangian graph; positivity requires a distinguished
   polarization, while the unpointed hyperbolic plane is rate-blind.
3. Finite-prime zero transfer occurs in the horizontal boundary layer `epsilon asymp 1/log N`; a
   useful finite section must be cofinal and zero-preserving or carry a stable quantized invariant.
4. Successful prime--Gamma seams require a genuinely growing resource: prime incidence rank,
   relative negative index, renormalization rank, Schatten depth, or an equivalent nonlocal carrier.

Together these suggest the following application, not yet a theorem:

> `[CONJECTURE — RH CARRIER LAW]` An HT-based RH architecture must construct an Euler-marked
> compatible section of the constraint--orientation product over increasing prime cutoffs.  The
> section must retain unbounded prime incidence, choose the FE-even zero-index chamber, and cross
> the `1/log N` layer by locally uniform zero-preserving convergence or a stable integer charge.

## Adversarial attacks

1. **Product-of-known-results attack.**  A mere pairing of the universal sewing theorem with the
   finite-atomic chamber theorem is below 90.  The proof must exhibit one common analytic field,
   prove rational-gauge invariance of the complete universal palette, and establish a genuine
   universal property or factorization theorem for the product geometry.
2. **Artificial-marking attack.**  A diagonal sign form attached by hand is insufficient.  The
   chamber grading must be the exact negative-square index of the meromorphic Pick kernel, or the
   promoted theorem must state only the residue-polarized geometry and clearly demote the analytic
   Krein claim.
3. **Support-change attack.**  Zeroing a residue deletes a pole.  Fixed-support conclusions apply
   only to open chambers; walls belong to the closure and must be treated separately.
4. **Sewing-dependence attack.**  The same translate palette must remain differentially independent
   after every rational gauge.  This requires an invertible base-field translation on every finite
   jet packet, not an appeal to genericity for each chamber.
5. **Coefficient-uniformity attack.**  The matroid theorem must retain arbitrary complex operator
   coefficients and arbitrary finite localized structural families.
6. **FE attack.**  Reflection symmetry supplies only the even grading.  It does not select the
   positive chamber.  Any claim that FE itself provides the section is false.
7. **RH-circularity attack.**  A section chosen from the Xi divisor or from the sign of an
   RH-equivalent Weil form is not source-defined.  The application must distinguish a necessary
   carrier law from an RH proof.
8. **Classical-moduli attack.**  If the product reduces to a routine product of a Stanley--Reisner
   representation space and an orthant arrangement, retire the 90-point route.  New content must be
   the simultaneous realization inside one fixed maximal-translation meromorphic field and the
   resulting pointing theorem.

## Proof program

1. Prove an abstract base-gauge invariance lemma: coordinatewise addition of elements of the base
   differential field preserves differential independence of every finite indexed family.
2. Specialize it to finite rational residue surgery of the universal prime-log source and all of
   its palette translates.
3. Re-run the exact operator-row and facet-restriction theorem without choosing a new source.
4. Prove the compatible cube law and exact residue index.
5. Prove the exact Pick negative-square formula over the positive infinite background, including
   the pole-localized lower bound.
6. Package product completeness and the factorization obstruction for selectors.
7. Construct the FE-even version and prove index doubling.
8. Audit parent literature in differential algebra, universal/hypercyclic translation theory,
   generalized Nevanlinna theory, orthant arrangements, matroid realization spaces, and moduli of
   polarized objects.

## Gates

- [x] 0 -> 1: exact candidate, source-pure construction, RH application boundary, and attacks stated
- [ ] 1 -> 2: complete paper proof of the product theorem and exact Pick index
- [ ] 2 -> 3: exact unconditional Lean theorem, with no project axioms or placeholders
- [ ] novelty: no parent theorem for the one-field universal product geometry
- [ ] significance: independent audit score at least 90/100
- [ ] 3 -> 4: standalone publication-ready paper with no Lean-facing narrative

## Log

- 2026-07-12 -- Pipeline and formal audit identified the recurring local-freedom, signed-orientation,
  noncompact-escape, and cofinal-resource pattern.  Opened the product-law route and retained the
  analytic Pick-index step as the first hard falsification gate.
