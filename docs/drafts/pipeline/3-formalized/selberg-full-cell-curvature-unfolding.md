# Full-cell unfolding of actual compact Maass curvature tests

- Stage: 3-formalized; complete paper proof and Lean audits passed.
- Parent: [Selberg conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 37.
- Goal: compare the literal full SL(2,Z) compact periodization with standard hyperbolic cell integration, then apply it to the original fixed-regulator curvature and its proved compact-test limit.

## Dependency-closed paper argument

The checked ModularStripUnfolding theorem identifies two matrices in PSL(2,Z) exactly when they differ by sign. No integral determinant-one matrix equals its own negative: multiplication by its inverse would imply 1=-1, contradicted by the top-left matrix entry over the integers. Thus every projective fiber has precisely two elements. Compact support and proper discontinuity make the original SL(2,Z) orbit series summable. Regrouping by projective fibers gives P_SL(g)=2 P_PSL(g), with elliptic stabilizer repetitions still present on both sides.

The checked compact_orbit_cell_bound theorem bounds the height of every point having a translate in the compact support of g. A finite height truncation of the closed modular cell is compact. Proper discontinuity therefore shows that only finitely many translates contribute anywhere on that entire cell. This establishes summability of the absolute translate integrals. For an integrable compactly supported real field g, invariance of hyperbolic volume establishes integrability on each translated cell. The proved PSL fundamental-domain theorem and the finite interchange give integral_fd P_PSL(g)=integral_H g. Hence integral_fd P_SL(g)=2 integral_H g.

For a compact continuous test g and continuous invariant real field u, the product gu is continuous with compact support and therefore genuinely integrable. Invariance gives P_SL(gu)=P_SL(g)u. Consequently integral_fd P_SL(g)u=2 integral_H gu. No limiting measure's seam-null assertion enters this fixed-density identity.

For the original Maass source, the proved regularized curvature weight is continuous on the upper half-plane. Multiplication by height squared gives the continuous hyperbolic density q_e, whose actual modular invariance is already proved. The existing chart transport identifies the original planar regulator pairing J_e(g) with integral_H g q_e. Therefore integral_fd P_SL(g)q_e=2 J_e(g). The already proved original compact-test limit then gives convergence of these standard-cell pairings to twice the constructed positive orbit functional.

## Scope and next conjecture

The real planar domain and the hyperbolic cell agree pointwise under the coordinate chart. Indicator transport, the proved height-squared chart cancellation, and the complex/real-product volume equivalence therefore identify integral_fd q_e with the original full planar retained-curvature integral. The existing source budget identifies this integral with lambda times the full regularized amplitude mass; it is strictly positive in the exceptional interval. As in the inspected EinastoGammaMoments proof, this nonzero actual integral discharges full-cell integrability. It is bounded by lambda times the finite full unregularized amplitude mass M, uniformly in e.

For a compact orbit field F=P_SL(g) with 0<=F<=1, positivity gives integral_fd F q_e<=lambda M. Passing along the already proved original compact-test limit yields 2 Q(F)<=lambda M. The signed strengthening follows from |integral F q_e|<=integral |F| q_e: whenever |F|<=1, 2|Q(F)|<=lambda M. Thus every previously constructed normalized compact weight has this same source-derived finite budget, independently of the compact region on which its periodization equals one. No total-mass equality is needed for this bound.

This establishes the normalization, the original compact-orbit limit, and the uniform functional budget. Equality of total limiting quotient mass with lambda M/2 still needs an original-source no-escape argument. The quarter lower comparison remains unproved. All boundary contributions remain in the literal full sums.

## Corpus mechanism audit

Explicit --any fiber-sum/quotient-sum/kernel-cardinality/finite-kernel/multiplicity discovery covered 4036 declarations in 1559 modules. The earlier broad unfolding discovery covered 56520 declarations in 12321 modules. These are index coverage counts, not full-source inspection counts. Inspected mechanisms: ModularStripUnfolding's exact projective fibers and sign multiplicity, ThetaCuspHawkingBMCompactModularPeriodization's actual orbit height bound and compact closed-cell truncation, and ThetaCuspHawkingBMCompactTestUnfolding's finite translate interchange. The new proof transfers these mechanisms to real compact tests and applies them to the actual Maass regulator density.

## Lean verification

- SelbergModularCellUnfolding.lean: 7 public declarations plus 3 private fiber helpers. SelbergMaassCellCurvature.lean: 14 public declarations.
- Both complete scratch proofs and needed source olean checks passed without warnings.
- Serialized final single-module builds passed, each rebuilding only its own target: unfolding 41s, source cell curvature 4.0s. Existing EvenL2LogUnitary informational replay only. Logs: /tmp/selberg_cell_unfolding37_build.log and /tmp/selberg_cell_curvature37_build.log.
- All 21 public declarations passed /tmp/selberg_cell_curvature37_axioms.lean, each using only propext, Classical.choice, and Quot.sound. The private helpers are covered by their public dependents. No added axiom or admission.
- Both finished modules are wired into RHTower.lean. Refreshed corpus audit includes all 21 public declarations and the 3 private helpers: /tmp/selberg_cell_curvature37_corpus_audit.json.
- Repository formal lint passed with existing large-file warnings: /tmp/selberg_cell_curvature37_lint.log. Source/card/umbrella whitespace checks passed. All task-owned Lean/build handles are terminal; final inspection observed separate Fokas-time and horizon-domain Lean checks, left untouched. No task commit or push.
- Selberg remains unproved. The new signed finite quotient-functional bound is not the missing spectral lower comparison.
