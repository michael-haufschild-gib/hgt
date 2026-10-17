# Continuum coprime shear and affine uncertainty

- **ID:** continuum-coprime-shear
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Lift Pillar VII to logarithmic coordinates with actual additive Dirichlet energy, exact interpolation defects, and multiplicative graph coupling.

## Scope and completion

Independent BiScaleUncertainty research; no RH work and no hgtl7 workflow.
User's attachment requires 100 significant contributions. Count mathematical
packages, not supporting lemmas. Goal remains active until that target and its
verification obligations are met.

Knowledge ledger: `docs/reports/BiScaleUncertainty/ContinuumCoprimeShear-FACTS.md`.
The requested `update_plan` tool is unavailable; this card records the plan.

## Plan

1. Read field context, search corpus and external parent theories.
2. Prove exact continuum energy/remainder identity before formalization.
3. Formalize logarithmic shear and finite-cell energy bridge without unproved
   analytic inputs. Extend explicitly constructed continuous primitives to L2 velocities.
4. Compact-source coercivity and rigidity are proved. Construct the rough
   modulus state, extend admission beyond compact support, and identify closed-graph APIs.
5. Audit each leaf directly, axioms, umbrella wiring, lint, and indexes.
6. Continue conjecture/proof/failure cycles toward 100 substantive packages.

## First candidate

For continuous q, let F(t)=integral from 0 to t of q, f(x)=F(exp x), and
E[a,b]=integral from a to b of q(t)^2. For a<b, c=(F(b)-F(a))/(b-a),

    E[a,b] = (F(b)-F(a))^2/(b-a) + integral_a^b (q(t)-c)^2 dt.

Under t=exp x, E[exp u,exp v]=integral_u^v exp(-x) f'(x)^2 dx.
Equal physical cells therefore have unit resistance even though their logarithmic
lengths shrink. Summation over dilated integer cells gives Pillar VII's factor k
with an exact nonnegative continuum defect.

## Boundaries

The elementary energy principle and affine group relation have classical parent
theories; no external novelty claim. Literal positive translation is a semigroup
on the positive half-line, not a globally invertible unitary action. Ordinary
unweighted logarithmic H1 energy is a different form. Exact support on a discrete
set cannot itself define a nonzero continuous state; coprime support belongs to
traces or a constructed interpolant.

## Gates

- [x] Context and initial corpus search; semantic coverage unmeasured.
- [x] Dependency-closed paper proof of the first trace/edge package, including
  arbitrary logarithmic velocities and quantitative affine commutator control.
- [x] First package: direct Lean leaf and all-theorem axiom audit; two leaves,
  34 theorem declarations counted as one contribution. Umbrella imports and
  generated indexes updated. Global lint has three unrelated concurrent wiring errors.
- [x] Finite coprime trace realization with actual L2 velocities, rough logarithmic
  derivatives, sharp coefficient two, and explicit competitor defect; four leaves,
  55 public theorems and their dependencies audited as one contribution.
- [x] Exact extended-energy transfer over a constructed diffuse/countable-line
  edge measure, including nonnegative slack and nodal control; two leaves,
  34 public theorems and 3 measure instances audited as one contribution.
- [x] Compact-source finite resistance mass, bounded supported congestion, and
  finite source-mass/jump/slack/nodal energies for every physical L2 velocity;
  two leaves, 32 public theorems, all 40 public declarations audited.
- [x] Compact-source variance coercivity and zero-energy rigidity across disconnected
  source regions; two leaves, 21 public theorems, all 27 public declarations audited.
- [ ] Closed-form identification and full affine operator uncertainty.
- [ ] 100 significant contributions.

Certified count: **5 / 100**. Formalized packages:
`../3-formalized/continuum-trace-affine-edge-control.md` and
`../3-formalized/coprime-logarithmic-sobolev-traces.md`, and
`../3-formalized/infinite-edge-logarithmic-path-congestion.md`, and
`../3-formalized/compact-source-graph-admission.md`, and
`../3-formalized/compact-source-variance-coercivity.md`.

## Current exact result and next frontier

The first package proves the correct weighted logarithmic Dirichlet form, exact
trace/interpolation defects, the continuum dilated-cell inequality, and finite
weighted multiplicative/nodal edge control. A second square-completion argument
removes the artificial requirement that physical velocities extend across zero.
The affine commutator is controlled by the exact physical interval length
`b * (exp s - 1)`. No unitary-group or self-adjoint-generator conclusion is claimed.

Extended path-congestion transfer is now proved for constructed mixed measures.
The ledger fixes the remaining concrete congestion and finite graph-domain
obligations. Finite coprime interpolation already has an exact weighted derivative-energy law.

## Certified package 2: Sobolev coprime trace realization

Extended the primitive and exact trace defect from continuous velocities to genuine
L2 velocities, proving absolute continuity and the a.e. derivative from the
construction. The sharp coprime interpolant is piecewise affine in physical t
(exponential-affine in log t); its derivative has jumps, so C1 is insufficient.
Proved: a constructed finite divisor-trace extension with energy exactly twice
the squared active trace norm, plus exact competitor decomposition, corrected
lower bound, finite weighted derivative energy, and nonlinear rough shear control.
No trace-support or integrability premise stands in for the construction.

The package has a durable paper proof and fact ledger. The full 100-package goal
remains unchanged and active.

## Certified package 3: infinite-edge congestion and exact slack

Constructed a nonnegative edge measure from a diffuse density and countably many
weighted horizontal jump lines. Proved s-finiteness from this construction; an
unrestricted measure does not justify Tonelli. For an edge e=(h,u), use ordered
logarithmic endpoints a=min(u,u+h), b=max(u,u+h), resistance R=exp b−exp a,
and path kernel R times the indicator of (a,b]. Proved the extended-valued identity

    integral K(y) exp(−y)|f'(y)|² dy = jump energy + integrated edge slack,

where K is the exact congestion kernel and slack is the local trace defect.
It proves infinite-edge jump and nodal estimates without integrability
or finite-energy admission premises. Full graph-domain finiteness still needs
a concrete congestion estimate. Preserve the distinction between an extended
energy comparison and a finite graph-domain theorem.

All 37 public theorem/instance declarations passed axiom audit; both direct leaf
checks passed without diagnostics. Imports and indexes are updated. Global lint
reports six unrelated concurrent missing imports; exact names are in the ledger.
This turn is **progress**. No owned process remains live.

## Certified compact-source mixed graph admission

Constructed mixed weights from a compact continuous ψ: diffuse density
w_arch(h)ψ(u)²ψ(u+h)² and arbitrary nonnegative coefficients on lag lines
log(n+2). Proved that every physical L2 velocity has finite graph and nodal
energy. Compact source support bounds both endpoints, leaves finitely many
integer lag lines, and the resistance factor cancels the diffuse 1/h singularity.
The exact K has a finite, compactly supported majorant. Local integrability of
the rough derivative density gives admission; source mass is also finite.

Paper mechanism for this candidate: replace the singular resistance-weighted
diffuse density, on h>0, by the continuous function
`2 exp(u+h/2)/(1+exp(-h)) ψ(u)^2 ψ(u+h)^2`. Its support lies in
`[-2B,2B] × [-B,B]`, where B is the existing radius of the actual source.
Its integral is finite by continuity and compact support. The same source
support kills every atom with `log(n+2)>2B`, leaving finitely many continuous,
compactly supported resistance densities. Thus total resistance mass C is
finite, and `K(y) ≤ C 1_[-B,B](y)`. Local integrability of the already constructed
rough Dirichlet density gives finite congestion, jump, slack and nodal energies.
This uses a constructed finite coefficient, not an assumed congestion bound or
summability condition on the arbitrary atom weights. The corpus search found no
existing compact-source admission theorem; generic Sobolev/jump-domain methods
are classical and carry no novelty claim here.

Both final direct leaf checks passed without diagnostics; all 40 public
declarations have only standard Lean axioms. Umbrella wiring, generated indexes,
formal lint and whitespace checks passed. Formal lint's earlier concurrent
wiring errors are absent from the current run. This turn is **progress**.
No owned process remained live at the package-4 checkpoint.

## Certified package 5: variance coercivity and nullspace

For the actual compact mixture and every physical L2 primitive f (with arbitrary
added constant), proved `0 ≤ MQ−A² ≤ sinh(2B) J`, where M=∫ψ², A=∫ψ²f,
Q=∫ψ²f² and J is finite jump energy. Also proved `J=0` iff f is constant on
the whole nonzero source, including disconnected regions. Exact pair/positive-lag
variance identities justify the comparison. Compact admission gives the additive
Dirichlet consequence. No positive-mass, connected-support, atom-summability or
energy-admission premise is assumed.

Both final leaf checks and all 27 public-declaration axiom audits passed.
Imports and indexes are current. Global lint reports seven unrelated concurrent
missing imports, listed in the fact ledger; neither new leaf has a lint error.
This turn is **progress**; goal remains active at **5/100**.

## Next candidate

`../0-backlog/rough-sobolev-modulus-nodal-defect.md`: construct the actual L2
velocity of |f|, prove its primitive identity and local Dirichlet-energy equality,
then prove exact mixed-graph decomposition `J(f)=J(|f|)+nodalEnergy(f)`.
Existing nodal algebra does not construct this rough-state domain realization.
The zero-level-set derivative issue must be proved, not assumed. Not yet counted.
