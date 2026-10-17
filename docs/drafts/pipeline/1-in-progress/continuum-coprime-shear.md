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
4. Compact-source coercivity, rigidity and the actual rough modulus are proved.
   Nodal mass coercivity, strict modulus contraction and actual Markov clamping are proved.
   Infinite coprime extension, exact projection, and gcd/lcm classification of
   projection interactions, sharp angles and exact alternating rates are proved.
   Joint two-grid trace extension, sharp stability and the closed sum are proved.
   Finite divisor families now have sharp longest-run constants and actual sine attainers.
   Arbitrary divisor families now have an exact run-gap/closed-range classifier.
   Their physical energy completion, conservation laws and escaping trace producers are proved.
   Explicit physical component projections and exact convergent approximation error are proved.
   Actual dilation/block coisometry, convergent variance and sharp packets are proved.
   Extend to physical affine commutator producers, SourceGraph coupling and closed-graph APIs.
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
- [x] Actual rough modulus realization with unchanged additive energy, exact nodal
  jump loss and path-slack gain; two leaves, 25 theorems, all 27 public declarations audited.
- [x] Quantitative nodal mass coercivity and exact strict modulus-contraction classifier;
  two leaves, 22 theorems, all 26 public declarations audited.
- [x] Actual rough unit clamp, exact local energy splitting, firm full-graph/form
  contraction and equality classification; two leaves, all 39 public declarations audited.
- [x] Infinite coprime extension and exact best-approximation projection;
  two leaves, all 52 public declarations audited.
- [x] Arithmetic classification of infinite projection commutators and range
  intersections; three leaves, all 30 public declarations audited.
- [x] Sharp arithmetic projection angles, norm attainment and exact alternating
  errors; four leaves, all 45 public declarations audited.
- [x] Joint infinite two-grid traces, exact adjacent energy, sharp attained stability,
  closed algebraic sum and minimum-energy defect; four leaves, 49 declarations audited.
- [x] Finite divisor-family interpolation, sharp longest-run factors, explicit
  sine attainers, closed range and exact mismatch; eight leaves, 124 declarations audited.
- [x] Arbitrary divisor-family closed-range/coercivity/run-gap classification,
  sharp bounded factors and normalized near-null producers; five leaves, 76 declarations audited.
- [x] Physical energy completion, finite-component conservation, exact trace recovery,
  and explicit ramp producers with error1/N; five leaves,73 declarations audited.
- [x] Explicit component averaging, unique physical best approximation and exact
  convergent error with negative-half-line accounting; five leaves,87 declarations audited.
- [x] Actual physical dilation, integer block producers, exact infinite variance,
  successor covariance and sharp equality; five leaves,72 declarations audited.
- [ ] Closed-form identification and full affine operator uncertainty.
- [ ] 100 significant contributions.

Certified count: **17 / 100**. Formalized packages:
`../3-formalized/continuum-trace-affine-edge-control.md` and
`../3-formalized/coprime-logarithmic-sobolev-traces.md`, and
`../3-formalized/infinite-edge-logarithmic-path-congestion.md`, and
`../3-formalized/compact-source-graph-admission.md`, and
`../3-formalized/compact-source-variance-coercivity.md`, and
`../3-formalized/rough-sobolev-modulus-nodal-defect.md`, and
`../3-formalized/compact-nodal-mass-coercivity.md`, and
`../3-formalized/rough-markov-clamp-domain.md`, and
`../3-formalized/infinite-coprime-trace-extension.md`, and
`../3-formalized/coprime-projection-arithmetic-commutator.md`, and
`../3-formalized/coprime-projection-angle-gap.md`, and
`../3-formalized/two-grid-coprime-trace-extension.md`, and
`../3-formalized/finite-grid-run-length-coercivity.md`, and
`../3-formalized/infinite-divisor-run-gap-classification.md`, and
`../3-formalized/divisor-trace-energy-completion.md`, and
`../3-formalized/divisor-component-averaging-projection.md`, and
`../3-formalized/integer-dilation-cell-coisometry.md`.

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
Package 5 was **progress**.

## Certified package 6: actual rough modulus and exact nodal slack

Constructed the L2 velocity of |c+primitive q|, proving its zero-level derivative
law, sign formula and pointwise primitive identity. Every local physical and
weighted logarithmic Dirichlet energy is unchanged. The full constructed mixed
measure satisfies `J(q)=J(modulus q c)+N(q,c)` and
`slackEnergy(modulus q c)=slackEnergy(q)+N(q,c)`, even when total energies are
infinite. Every individual path budget and total congestion are unchanged.
Compact sources give finite real energy differences and preserve source mass.

Both final serial direct leaf checks passed without diagnostics. All 27 public
declarations use only standard Lean axioms; seven main signatures were inspected.
Imports, all 25 theorem names in generated API, and whitespace check passed.
Global lint reports four unrelated concurrent missing imports, listed in the
fact ledger; no error concerns either new leaf. All owned processes are terminal.
This turn is **progress**; goal remains active at **6/100**.

## Certified package 7: nodal mass and strict modulus contraction

Proved `Vψ(f)−Vψ(|f|)=4PN≤sinh(2B)[J(q)−J(modulus q c)]` for actual rough
states and the full compact mixture. Modulus strictly lowers graph energy iff
both signs occur where ψ is nonzero. Equality needs only one sign, whereas
zero jump energy needs constancy. No extra analytic admission premise.

Both direct leaf checks passed without diagnostics; all 26 public declarations
have only standard axioms and seven main signatures were checked. Imports,
field maps, all 22 theorem names in the generated API and whitespace check pass.
Global lint reports five unrelated concurrent missing imports, recorded in the
fact ledger. All owned processes are terminal. This turn is **progress**;
certified count **7/100**, goal active.

## Certified package 8: actual Markov clamp and firm graph control

Constructed the actual L² velocity of T(c+primitive q), T(a)=min(max(a,0),1),
and its residual. Proved a.e. band localization, absolute continuity, exact
physical/logarithmic energy and congestion splitting, firm jump/source-mass
contraction, and removed-state variance control. Graph energy is unchanged iff
source values are constant or all lie in [0,1], including disconnected/zero sources.

Both direct leaf checks, all 39 public axiom audits and ten main signatures pass.
Imports, field maps, all 36 theorem names in generated index, global formal lint
and whitespace checks pass. Existing large-file warnings remain. No added axiom,
full build, numerical experiment or heartbeat increase. All owned processes terminal.
This turn is **progress**, certified count **8/100**, goal active.

## Certified package 9: infinite coprime traces and exact projection

Constructed actual ℓ²-to-L² tent extension E with every integer trace and energy
2Σv². For arbitrary physical q, centered second differences a_j are derived as
square-summable data; Pq=E(a/2) is the projection onto the closed extension range.
Proved exact energy splitting, exact best-approximation error, idempotence,
residual orthogonality and both equality classifiers. No extra analytic premise.

Both final direct leaf checks and all 52 public axiom audits pass without
warnings; twelve main signatures inspected. Imports/maps/index/scoped whitespace
checks pass. Global lint reports nine unrelated concurrent unreachable modules,
listed in the ledger; no error concerns these leaves. All owned processes terminal.
This turn is **progress**; certified count **9/100**, goal active.

## Certified package 10: arithmetic projection commutators

For actual infinite tent spaces, V_m∩V_n=V_lcm(m,n) for every m,n≥2.
The projections commute exactly when gcd(m,n)≥2; their product is then the lcm
projection. Coprime spacings have an explicit tent witness with commutator
primitive trace exactly 1/2, including spacing two. The infinite steps use
actual convergent series and exact traces, without analytic admission premises.

Three direct leaf checks and all 30 public axiom audits pass; nine main
signatures inspected. All imports and generated API entries present. The
relocated field README was read fully and left read-only. Global lint details
are in the fact ledger. This turn is **progress**; certified count **10/100**,
goal active.

## Certified package 11: sharp angles and exact alternating errors

For T=P_mP_n−P_lcm, proved T²=cT and ‖T‖²=c. The commutator has squared
norm c(1−c), with c=0,1/4,1/2 determined by gcd and the spacing-two exception.
Both norms are attained by actual nonzero velocities. Every positive iterate
has exact error (P_mP_n)^k−P_lcm=c^(k−1)T and squared norm c^(2k−1).
Main statements are unconditional; no admitted decomposition or spectral premise.

Four direct leaf checks, all 45 public axiom audits and twelve main signatures
pass. All imports and generated API entries verified at current source lines.
Field README remained read-only. Repository lint details are in the fact ledger.
This turn is **progress**; certified count **11/100**, goal active.

## Certified package 12: joint infinite trace interpolation

Actual nonredundant ℓ² data realize all union-grid integer/logarithmic traces.
Exact adjacent energy has sharp attained factors (2,2), (1,3), or
(2−√2,2+√2) according to arithmetic spacings. Extension is injective, with
closed range equal to the algebraic sum of both individual ranges. Unconditional
competitor identity retains trace mismatch; matching all integer traces yields
exact minimum-energy defect and uniqueness.

Four final direct checks, all49 public axiom audits, thirteen main signatures,
four imports and all48 catalog-supported entries pass. Named instance is
separately audited. Global lint has ten unrelated concurrent missing imports,
recorded in the fact ledger. README remains read-only. Package12 is progress;
goal remains active at12/100.

## Certified package 13: sharp finite-family run coercivity

For every actual finite nonempty divisor family, maximum active run r is
constructed, positive, below the lcm period, and attained in one period.
The physical L² producer S(v−Rv) realizes every integer/log trace and has
sharp factors 2±2cos(π/(r+1)). Actual finite sine packets attain both factors.
The masked successor is proved contractive and nilpotent at r; no gap is
assumed. Closed range, exact adjacent energy, unconditional mismatch, unique
minimum for matching traces, and the two-grid r=1,2,3 recovery all check.

Eight leaf checks and all 124 public-declaration axiom audits pass cleanly;
only standard axioms. Eight imports and 123 supported API entries verified.
Global lint reports fourteen unrelated concurrent unreachable modules plus
generated drift; index refreshed afterward. Exact details are in the ledger.
README was fully read and kept read-only; Trap 10 is applied through actual
producers and proved errors. This turn is progress; goal remains active at 13/100.

## Certified package 14: arbitrary-family gap and closed range

For every family d:ℕ, D:Set ℕ, actual extension has closed range iff it is uniformly
coercive iff active runs are uniformly bounded. In the bounded regime, the exact
factors 2±2cos(π/(r+1)) are attained. Otherwise actual unit sine packets have
energy tending to zero; the exact unit-energy infimum 0 is unattained. Injectivity
and all integer/log traces hold in both regimes. The full family gives a concrete
nonclosed range. Main classifiers take only d,D, with no analytic admission premise.

Five direct leaf checks and all 76 public axiom audits pass;19 signatures inspected,
30 mathlib API probes passed, five imports and 75 catalog entries verified.
Global lint has 15 unrelated missing imports plus generated drift; index refreshed
and own coverage rechecked. This turn is progress; goal active at 14/100.

## Certified package 15: physical energy completion

The exact physical closure is the isometric synthesis of ℓ² cell currents
with zero cumulative trace at inactive nodes, equivalently zero sum on every
finite active component. Orthogonal currents are constant along active edges
and zero on infinite active tails. Completed traces recover old data exactly
when square-summable; universal recovery is equivalent to bounded active runs.
For the full family, unitCell1 has no old preimage, while explicit finite ramps
approximate it with exact squared error1/(n+1). This is one connected contribution.

All five direct leaf checks and all73 public-declaration axiom checks pass;
only standard axioms.13 principal signatures and52 API probes inspected.
Five imports and72 catalog entries verified. Global lint exits1 solely for
six unrelated unreachable modules, listed in the card and ledger; no own or
generated-index error. Paper preceded Lean; README remains read-only.
Package15 is counted once toward the active goal.

## Certified package 16: explicit component averaging

For every physical L² input, integrate on unit cells, subtract each finite
arithmetic component mean, retain infinite-tail coefficients, and synthesize.
This is the unique nearest completed divisor state. Its exact error equals
noncellular energy plus the convergent sum of squared component primitive
increments divided by component lengths. First-cell and negative-half-line
errors are explicit; full-family correction is just the first-cell average.
No analytic admission premise. One connected contribution.

All five direct leaves and all87 public axiom checks pass, only standard
axioms;17 principal signatures and50 API probes checked. Five imports and87
catalog entries verified. Global lint exits1 for eight unrelated unreachable
modules and concurrent generated-index drift; exact list in card and ledger.
Indexes refreshed separately. README remains read-only. Certified16/100.

## Certified package 17: integer dilation and block producers

Actual physical dilation A_aq(t)=a q(at) has exact energy |a|‖q‖² and
primitive F_q(at). Integer block aggregation intertwines cell analysis with
dilation, has sharp norm√m, explicit replication adjoint/right inverse, and
successor covariance H_mR^m=R H_m. The convergent block-variance series is
the exact defect. The physical defect also retains noncellular energy.
Explicit packet S(T_mδ_0) attains energies m and m². Equality is classified.
Dilation by2 moves unitCell1 outside every completed divisor domain; the
unrestricted positive operator/producer calculus is fully formalized.

All five direct leaves pass without diagnostics; all72 public axiom checks
use only standard axioms.23 principal signatures and53 API probes checked;
five unique imports and72 exact catalog locations verified. Global lint
exits1 for nine unrelated unreachable modules and concurrent index drift,
listed in paper/card/ledger; no own or proof-debt error. Index refreshed.
Trap10 applied through explicit unconditional producers. README fully read
and unchanged. Paper preceded Lean. Counted once:17/100, goal active.

## Next candidate

`../0-backlog/physical-affine-commutator-producers.md`: construct actual
physical translations and anchored affine action; determine sharp
commutator norm/nonattainment with explicit alternating finite packets.
Unproved and uncounted; no Lean assigned. Primary-source and paper-proof
audits still required. Preserve full-space versus half-line distinctions.
