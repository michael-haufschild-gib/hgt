# SQB: native scattering versus real polynomial spectral transport

- **ID:** SQB-SCATTERING-POLYNOMIAL-REALITY
- **Stage:** 5-failed (fixed polynomial occurrence subclass only)
- **Type:** FALSIFIED; quantitative positive survivor formalized
- **Goal:** Audit the independent Xi-to-automorphic occurrence gate without assuming the Selberg quarter bound or RH.
- **Scope:** New occurrence audit and its Lean certificates. The frontier map is read-only. The active scalar-curvature work is separate.

## Full proof chain

Original Maass source → positive modular curvature with uniform cusp tails → exact total orbit mass → source quarter domination → Selberg quarter bound → independently constructed Xi occurrence in the required spectral domain → RH.

`SelbergMaassQuotientMass.totalOrbitCurvature_eq` already closes total orbit mass, with the exact full-SL/projective factor two. Quarter domination and Xi occurrence remain unproved. Native scattering has Xi poles at s=rho/2. Its Casimir s(1-s) is nonreal even at critical-line zeros, so direct Maass occurrence cannot be assumed.

## Plan

- [x] Read SQB ledgers and current source-mass proofs; preserve newer shared-tree work.
- [x] Broad OR discovery across the full indexed corpus: spectral transforms (3543 declarations, 1156 modules), automorphic/Hecke/representation mechanisms (1412, 320), geometric curvature/capacity mechanisms (13010, 1783), and polynomial/reflection mechanisms (20536, 5472). Counts describe returned metadata, not full proof inspection.
- [x] Inspect actual polynomial period rigidity, Schwarz coefficient conjugation, Hardy's dyadic zero theorem, native scattering normalization, and finite graph gap assumptions.
- [x] Prove the exact polynomial-real-locus classification for the native critical scattering parabola; direct source check and final targeted build passed.
- [x] Apply the classification to genuine critical-line zeros, including arbitrarily large heights; complete source-endpoint scratch passed.
- [x] Formalize the stronger divergence of distance from the entire real axis and attach it to arbitrarily high actual scattering poles.
- [x] Extract the strongest positive survivor and distinguish the excluded transport class from the full SQB candidate.
- [x] Check scratch and source with one foreground Lean process; wire only completed modules; run final targeted module and axiom/lint audits.

The requested update_plan tool is unavailable; this card carries the plan.

## Closed paper argument

At rho=1/2+it, the native Casimir is k(t)=3/16+t²/4+it/4. For any complex polynomial P, let Q(t)=P(k(t)). If Q is real at infinitely many real t, polynomial identity forces Q to equal its coefficientwise conjugate. The quadratic k is invariant under t↦-t-i. Conjugation supplies invariance under t↦-t+i, and composing these gives period 2i. The corpus proves a nonconstant complex polynomial has no nonzero additive period. Thus Q, and hence P, is constant. The constant must be real. Conversely every real constant works.

Consequently a fixed nonconstant P has only finitely many real t with P(k(t)) real. The unconditional Hardy dyadic theorem supplies genuine critical-line zeros at arbitrarily large heights outside that finite set. This excludes fixed polynomial spectral reparametrization of every native scattering pole into any real Maass spectrum. It does not exclude nonlinear source reconstruction, an unbounded-order transform, or a different independently constructed occurrence.

## Audit risks and positive survivor

Complex coefficients must be allowed; restricting to real P would understate the obstruction. The real-locus theorem must be attached to actual zeta zeros, not merely auxiliary parameters. No scalar transformation is presumed to preserve a differential eigen-equation or the Maass domain.

Positive survivor: exact classification of admissible global polynomial transports, and finite exceptional real-valued locus for every nonconstant transport. Paper mechanism and its stronger quantitative separation theorem are now Lean-certified. This is not a proof or falsification of RH, and the full SQB route is not retired.

## Stronger positive statement exposed by the proof

Let R(t)=Im(P(k(t))), the actual coefficientwise imaginary polynomial of P composed with k. If R were constant b, subtracting ib from P would make the composed polynomial real on the entire real line. The proved classification would force P-ib, hence P, constant. Thus nonconstant P forces positive degree of R. The corpus/mathlib real-polynomial asymptotic theorem gives |R(t)|→∞ as t→∞. Since |Im(w)|≤|w-r| for every real r, distance from P(k(t)) to the entire real axis tends to infinity. Hardy's dyadic zero theorem then supplies actual scattering poles beyond every height and outside every fixed distance budget.

This is a quantitative positive separation theorem. It rules out bounded-error polynomial approximation to any real spectrum in this specified source coordinate. It supplies no comparison for a nonpolynomial or independently reconstructed source.

## No-go closure

- **Exact killing theorem:** `RHTower.SelbergScatteringPolynomialReality.real_on_all_xi_copies_iff` classifies all fixed complex polynomials real on the full actual Xi divisor: exactly real constants. `real_on_critical_zeros_iff` proves that the unconditional critical-line zeros alone force this classification.
- **Strongest positive survivor:** `abs_imaginary_tendsto_atTop` proves divergent absolute imaginary part for every nonconstant polynomial; `eventually_far_from_real` makes the separation uniform over the entire real axis. `exists_critical_pole_far_from_real_above` realizes this at genuine critical-line scattering poles beyond every height and beyond every prescribed distance budget.
- **New insight:** fixed finite-degree scalar changes of native scattering energy cannot even approximate real spectral occurrence with a bounded error. A new source construction must leave that class; no viable replacement is assumed.
- **Status:** complete paper proof and three audited Lean modules, 19 exported declarations, standard axioms only. [Proof, exact source scope, and audit](../3-formalized/sqb-polynomial-scattering-separation.md). The entire SQB candidate is not retired; its quarter inequality and independent Xi occurrence remain open.
- **Process qualification:** final Lake audit rebuilt some required Hardy dependencies in parallel before the remaining checks were serialized. The audit report records this departure from the requested process discipline and the existing dependency warning. No full build ran and no task-owned Lean process remains.

## Constructed survivor outside the retired class

An explicit nonpolynomial entire function now satisfies
F(1/4+w²)=cosh(8πw) and F(k(t))=cosh(4πt) for every real t. Its complete
real-native preimage classification on the open Xi strip is Lean-proved:
F(lambda)=F(k(z)), for real lambda and Re z≠0, holds exactly when Im z=0 and
lambda=1/4+(Re z)²/4. This is a genuine entire construction outside the excluded
polynomial class. Its actual-Xi endpoint states that existence of a matching real
parameter is exactly critical placement of the zero; no spectral occurrence is
assumed or supplied. [Entire construction, sharp alias, and preimage proof](../3-formalized/sqb-entire-casimir-transform.md).
