# SQB full modular operator core

Status: eleven public declarations formalized, individually built and axiom-audited.
RH remains unproved. Frontier map is read-only.

Full chain: original modular source → entire-transform operator → independent
occurrence at every full Xi parameter → critical-line classifier → RH.

## Exact compact representation

Let f be any member of the original smooth modular core: it is globally smooth,
PSL2Z-invariant, and supported on a compact subset K when restricted to the
closed modular cell. No condition removes modular seams or elliptic points.

The existing smooth compact cutoff theorem gives a real planar bump chi equal
to one near the complex-coordinate image of K, with compact support strictly
inside the upper half-plane. Set b=chi² and p=the full projective periodization
of b. Proper discontinuity proves each compact orbit sum has finite support.
Thus Re p≥0 and Re p≥b. If f(z)≠0, move z into the closed cell. Its image lies
in K, where b=1. Invariance of f and p gives Re p(z)≥1.

Define the smooth normalization

`d(z)=p(z)+1−smoothTransition(2 Re p(z)−1)`.

It never vanishes. For Re p≤1/2, the transition is zero and Re d=Re p+1>0.
For Re p>1/2, the transition is at most one and Re d≥Re p>0. Where Re p≥1,
the transition equals one, hence d=p. Both p and d are modular invariant.

The planar field `g=b f/d`, using the actual upper-half-plane chart, has compact
support strictly inside the upper half-plane. Smoothness there follows by
division by the proved nonzero denominator; outside the support, g vanishes
on a neighborhood. It therefore defines an admitted compact planar test.
Its full periodization is exactly

`periodize(g)=p f/d=f`.

At points where f is zero this is immediate; elsewhere d=p. This identity
retains every projective translate and its elliptic stabilizer multiplicity.
It constructs a compact planar representative of every original core field.

## Literal differential transport

For any compact smooth chart test, proper discontinuity supplies one finite
set of translates containing every nonzero summand on a neighborhood of a
given point. All omitted translates vanish on that neighborhood, so their
actual first and second derivatives vanish there. Differentiating the retained
finite sum twice is therefore legitimate.

The existing Möbius derivative and height laws prove covariance of the literal
hyperbolic Laplacian. Combining covariance, finite-sum differentiation and
germ locality proves the exact identity

`Delta_H(periodize g)=periodize(Delta_H g)`.

The existing compact planar operator theorem already admits the full
periodization of g to the native Friedrichs domain and gives its value minus
the admitted periodization of the actual test Laplacian. The constructed
representation transfers this theorem to every original compact core field f.
The previous commutation identity identifies that Laplacian vector with the
actual pointwise Delta_H f, almost everywhere in the native measure.

The Laplacian itself is another full compact periodization, so it remains a
smooth invariant core field with compact quotient support. Consequently

`fieldVector(f) belongs to domain(A)`,

`A(fieldVector(f))=fieldVector(f)−fieldVector(Delta_H f)`.

Both vectors use the original native L² measure. The representative identity
also states the literal pointwise action `f−Delta_H f` almost everywhere.

## Scope and remaining source obligation

This is a theorem about the entire existing compact modular core, not an
assumed domain rule for arbitrary smooth L² fields. The corrected Xi source V
has a noncompact rapidly decaying tail. To use the present result for V, the
remaining construction must produce actual compact modular approximants and
prove convergence of both values and complete operator images. Closedness of
A can then admit V and identify its retained source forcing. None of those
noncompact convergence or spectral-occurrence conclusions is asserted here.

## Lean module and audit

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullCoreOperator`.
Namespace: `RHTower.D4BMModularCore`.

The eleven public declarations comprise compact orbit summability; existence,
construction and equality of the full planar representation; original core
domain admission; exact Laplacian-periodization commutation; the planar
Laplacian vector representative; the core operator representative; the literal
core Laplacian construction and its field identity; and exact operator action.

The complete scratch passed `lake env lean /tmp/sqb9_core.lean` without
diagnostics. The final isolated `lake build` compiled only this module in
6.5s, with no new warnings; preflight and every `Built` line were checked.
All eleven public axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`. All public declarations are in the refreshed corpus index;
the umbrella imports the module once. No numerical proof input or placeholder
was used. Logs: `/tmp/sqb9_core_build.log`, `/tmp/sqb9_core_axioms.log`,
`/tmp/sqb9_index_audit.json`.

The repository-wide formal lint run reports one unrelated, untracked module
missing from its umbrella: `GaloisForLFunctions.HTGeometry.FokasLenellsRegularOrigin`.
Neither new SQB module has a lint error. The unrelated module was left untouched.
