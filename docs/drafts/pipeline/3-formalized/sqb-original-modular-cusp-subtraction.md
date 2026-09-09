# SQB original modular cusp subtraction

Status: 32 public declarations formalized and individually audited. All public
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
RH remains unproved. Frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Source construction

For an actual Xi copy rho, retain the physical parameter u=(rho−1)/2 and the
complete original field E_u. Let P_u be its full Weyl principal part and eta(y)
the existing smooth cutoff, zero below two and one above three. On the closed
modular cell set r=E_u−eta P_u.

Translations preserve this literal expression. Every nontranslation overlap
of the closed cell lies below two in both charts, where r=E_u. Original scalar
modularity therefore proves compatibility of full germs. The existing cell-germ
extension constructs a globally smooth modular R, equal to r on the cell and
equal globally to E_u minus the full periodization of the original cutoff seed.
The high-cell remainder is the complete Fourier tail. Its uniform bound,
combined with compact lower-cell control, gives bounded R and finite native L² norm.

The source is nonzero without a selected-value premise. At height 3/2 the full
horizontal mean is the nonzero original Weyl coefficient times its height power.
A nonzero point can be relocated to the closed cell; the actual orbit-height
bound keeps its height below two. Thus R retains a nonzero original field value.
Continuity and closure of the cell interior transfer this nonvanishing to its
native Hilbert vector.

Applying the already constructed injective entire covariance C produces a
nonzero vector in the actual domain of T=C^(-1)−2. Its exact residual at the full
Xi target mu is R−(2+mu)CR. This construction must not be called spectral
occurrence unless that retained residual is proved to vanish or normalized
approximation is constructed independently.

## Corpus evidence and plan

Broad OR searches covered 342 declarations in 108 modules for cusp means,
Poincare inequalities, spectral gaps, covering multiplicity, modular strips and
horizontal energy; another covered 53 declarations in 26 modules for cusp
subtraction, Poincare response, modular extension, cutoff source, bounded
automorphy and source residual. Counts describe index coverage only.
Inspected actual square-residual gluing, cell-germ extension, orbit-height bounds,
uniform full-tail bounds, and the existing entire covariance graph identity.

- [x] Source and dependency-closed paper construction identified.
- [x] Formalize literal linear residual, full modular extension and norm admission.
- [x] Prove source-derived nonvanishing in the original Hilbert space.
- [x] Construct its actual entire-domain vector and retain its full Xi residual.
- [x] Audit scratch, isolated modules, axioms, umbrella wiring and formal lint.


## Exact source equation and retained transition forcing

Write `lambda=(rho/2)(1−rho/2)` and `B=eta P_u`. The actual complete scalar
source satisfies `Delta_H E_u=−lambda E_u`; the two original Weyl terms satisfy
the same equation individually. The proved linearity identity gives

`(−Delta_H−lambda)r = Delta_H B + lambda B = cutoffForcing`.

The expression on the right retains every derivative of the smooth cutoff.
Below height two, B is identically zero on a neighborhood. Above height three,
B agrees with P_u on a neighborhood. Locality of the actual second derivative
and the principal equation prove that the forcing is zero in both open regions.
On the closed modular cell, the extension retains the entire residual germ by
`cellGermExtension_germ`, so gluing introduces no seam mismatch. The forcing
statement concerns the original cell expression; it does not assert that a
modularly extended forcing vanishes outside the same height band in every chart.

## Native Hilbert nonvanishing and transformed equation

The source norm uses the existing native measure `volume.restrict fd`. Global
boundedness and continuity prove `MemLp R 2 measure`. Define V to be the actual
L² class of R, with its proved almost-everywhere representative identity.

If V were zero, R would vanish almost everywhere on the cell. The actual
hyperbolic volume is positive on nonempty open sets. Continuity, together with
`fd=closure(interior fd)`, upgrades that equality to pointwise vanishing on the
whole closed cell, contradicting the retained nonzero source value. Thus V is
nonzero as a Hilbert vector, not merely at a chosen measure-zero point.

Let C be the already constructed injective entire covariance, T=C^(-1)−2 on
range C, and `mu=F((rho/2)(1−rho/2))` the complete transformed target. Define

`W=CV`, `U=W/||W||`, `G=V−(2+mu)CV`.

Injectivity proves ||W||>0. Both W and U belong to the actual T domain and
||U||=1. The full transformed equations are

`(T−mu)W=G`,

`||(T−mu)U||=||G||/||CV||`.

Here G is the retained Hilbert-space forcing. It is **not identified with the
cell cutoffForcing** from the second-order equation. No vanishing, smallness,
approximation limit, or occurrence statement for G is proved. The construction
retains rho in the original field and in mu; it does not replace rho by its
ordinate. What remains is independent control of this full transformed residual
or another source-derived occurrence construction.

## Lean modules and validation

`GaloisForLFunctions.RHTower.SelbergScatteringCuspSubtraction` contains 20 public
declarations in `RHTower.SelbergScatteringCuspSubtraction`: full physical scalar
modularity, literal low/high residual identities, compatible cell germs, smooth
modular extension, exact complete orbit subtraction, boundedness, source-derived
nonzero cell value, and the full cutoff-forced equation with its two exterior
vanishing statements.

`GaloisForLFunctions.RHTower.SelbergScatteringSourceVector` contains 12 public
declarations in `RHTower.SelbergScatteringSourceVector`: native norm admission,
its actual L² vector and representative, proved nonvanishing, positive covariance
norm, actual domain vector, exact unit normalization, full residual, and its exact
transformed equation and residual norm.

Both complete scratches passed `lake env lean`: `/tmp/sqb8_subtraction.lean`
and `/tmp/sqb8_vector.lean`. Each final `lake build` named exactly one module;
preflights showed only that module stale, and all build-log `Built` lines were
checked. The subtraction module built in 6.7s and the vector module in 4.6s.
Neither new module emitted a warning. Each umbrella import occurs exactly once.

All 32 public declarations passed separate `#print axioms` checks in
`/tmp/sqb8_axioms.lean`; all were found in the refreshed corpus index. Repository
`python3 scripts/formal_tools.py lint` passed, with existing file-size warnings.
No numerical experiment, new axiom, placeholder, or computed proof input was used.
Audit logs: `/tmp/sqb8_subtraction_build.log`, `/tmp/sqb8_vector_build.log`,
`/tmp/sqb8_axioms.log`, `/tmp/sqb8_index_audit.json`, `/tmp/sqb8_lint.log`.
