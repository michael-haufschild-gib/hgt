# Contribution 007: all-parameter theta BV current with literal Meyer source

Status: formalized and audited; contribution 007 of 100.
Previous goal turn made verified progress: global actual-source Xi synthesis
and zero Meyer invisible sector, with eight direct Lean and eighteen
standard-axiom audits. The current worktree retains those theorems.

Goal: one further substantial structural advance, not a routine consequence
of global faithfulness or a reformulation of a sign/RH receiver. Read the
current Lean corpus, use documented research search, and cycle conjecture,
attack, failure/survivor, proof. No web, external novelty check, numerical
experiments, new axioms, hypotheses on the final result, or heartbeat hacks.
One owned foreground Lean process at a time; no full/umbrella builds or
subagents. Preserve concurrent edits.

Initial independent leads: exact infinite Xi-jet admission and clustered
spectral synthesis; source-native residue/Krein pairing beyond finite
packets; heat normal-block operator realization. Compare those against
other current frontier routes before committing to a mechanism.

Searches completed: deep corpus queries for admission/rapid interpolation,
residue pairing/full multiplicity, and heat normal blocks/operator
completion. Reported coverage and actual Lean statements were inspected. A
positive result must identify the hard obstacle removed and what new
source constructions it enables. Do not count estimates, receiver spaces,
or finite-corollary packaging.

## Conjecture audit

- Unrestricted infinite Xi packets: false, already excluded by
  `DeningerMeyerFullXiJetAdmissionBoundary`; even the unit packet fails.
- Removing the theta derivative history while preserving nonzero Jordan
  blocks: already proved by `HedenmalmThetaDerivativeHistoryQuotient`.
  Injectivity or completeness of that quotient does not follow from its
  nonzero spectrum. No new contribution counted.
- Full native Gaussian heat trace / finite-mode density: requires a new
  convergence theorem in the original topology. Global jet faithfulness
  alone does not give this. No theorem asserted.
- Global Weil radical: finite-packet and Hilbert inertia are already far
  developed. Merely pulling back coordinate forms would not remove the
  admission problem. No contribution counted.
- Prime Euler inverses modulo Poisson boundaries: promising, but full
  surjectivity requires surjective periodization of actual boundaries;
  finite jet inverses do not establish it. Deferred, not claimed.

## Selected conjecture: localize the singular theta domain defect

Construct an actual bounded-variation quantile mode for every complex
parameter and every interior cut, retaining the full Xi divisor as one
explicit interior point charge. This combines RN's all-parameter right-ray
variation theorem, the theta source connection/reflection formula, and the
full-multiplicity source jet results. It is a producer of actual modes and
currents, not a sign condition or an RH equivalence.

Dependency-closed paper argument: write q_z(x) for `flatQuotient z x`.
The upper-tail formula gives finite variation on every right ray, for every
z. Reflect the opposite parameter to obtain a left-ray branch
l_z(x)=q_{-z}(-x). The exact connection identity gives

    q_z(x)-l_z(x) = -i z XiC(z) exp(-i z x) / k(x).

For a finite cut a, glue l_z on x<a to q_z on x>=a. Both ends have trace
-1. The two finite ray variations plus the finite jump give global BV.
Push through the actual increasing theta CDF and assign -1 at both compact
interval endpoints. No zero condition is needed. Each closed half is
continuous, differentiable inside, and BV; hence its actual derivative is
L1, and the fundamental theorem applies on that half. Integration by parts
on both halves gives the exact weak derivative: the two L1 derivative
densities plus one Dirac mass at cdf(a), with coefficient
-i z XiC(z) exp(-i z a)/k(a). The compact endpoints contribute only their
known trace; there is no missing seam mass. At any nonzero Xi zero this
coefficient has exactly the original analytic multiplicity, because the
remaining factor is holomorphic and nonvanishing there. On the divisor
(and at z=0), the glued mode is the original mode pointwise.

Structural survivor: the domain obstruction of the original mode is
converted into a movable, explicit, finite interior current. All complex
parameters become available in one BV/weak-current construction, while the
original divisor and multiplicities remain unchanged. No positivity,
spectral completeness, or parameter-differentiated BV admission is claimed.

The native equation is retained as well. With h=ρ'/ρ and source quantile
speed v=1/ρ, each source branch solves q'+izq+h(q+1)=0. Thus away from the
interior cut, the compact derivative equals

    v(t) * (-iz M_z(t) - h(Q(t))*(M_z(t)+1)).

This combined expression is L1 because it equals the already constructed
actual derivative almost everywhere. Its terms are never separated into
unpaid improper integrals. Substituting it into the weak-current identity
produces the original source differential current, with the same explicit
point charge. This is the additional cancellation-preserving step required
to make the BV construction an actual source parametrix.

Lean status: source BV, compact branches, compact weak current, the combined
native density, full multiplicity, and the actual Meyer source bridge all
audited. Six leaves and 21 axiom checks passed; repository lint passed.

## Exact HF/RN source bridge

Audit found that an import of the Hedenmalm jet module alone did not establish
the requested multi-route synthesis. Add the actual Meyer source bridge to
the current, without claiming parameter-differentiated BV admission. The
corpus theorem `deningerMeyerHedenmalmSource_transform` identifies each literal
Meyer causal source with the corresponding removable Xi divided chain.
Its exact partial factorization makes the interior charge, for every complex
parameter, the cut gauge times `(z-alpha)^k` times that literal source's
centered Mellin transform, for every slot through the full multiplicity.

Paper proof of the terminal law: write the charge as `g(z) XiC(z)`, where
`g(z)=-iz exp(-iza)/k(a)`. In its multiplicity-order Leibniz derivative, every
term except `g(alpha) XiC^(m)(alpha)` vanishes by the full Xi multiplicity
theorem. The source-jet theorem identifies this derivative with an explicit
theta moment; the actual Meyer divided source identifies it also with
`m! g(alpha)` times its centered Mellin value. Substitution into the already
paid weak-current identity gives a literal HF-source realization of the RN
interior current, including repeated zeros. This belongs to contribution007,
not a separate count. The relevant routes are RN and HF; no TT/Wold result is
used and no TT progress is claimed.

## Verified implementation

All modules are in `formal/GaloisForLFunctions/RHTower/`, namespace
`RHTower.PaperThetaEndpoint`:

- `PaperThetaCutParametrix`: actual reflected source branch, exact connection
  charge, two-ended BV admission for every parameter, native agreement on the
  original divisor-or-zero domain, and cut-gauge conservation.
- `PaperThetaCutBranches`: both compact half-branches have the paid continuity,
  variation and derivative integrability needed at the singular endpoints.
- `PaperThetaCutCurrent`: the literal compact mode is BV; its exact weak
  derivative consists of its integrable density and the one interior charge.
- `PaperThetaCutSourceEquation`: the original source ODE survives reflection
  and quantile transport; the combined singular expression is L1 and supplies
  the weak current without separating divergent pieces.
- `PaperThetaCutDivisor`: the charge is entire and has exactly the Xi analytic
  multiplicity at every support point. `thetaCutParametrix_current` constructs
  the BV mode, its L1 native source density, both endpoint traces, and the
  full weak-current law unconditionally for every parameter and interior cut.
- `PaperThetaCutMeyerCurrent`: each actual Meyer causal source factors the
  interior current. Lower jets vanish; the multiplicity-order jet is nonzero
  and equals both an explicit theta moment and a factorial-weighted actual
  Meyer source value. `cutQuantileMode_meyer_source_current` is the exact HF/RN
  current bridge.

Key corpus inputs: `boundedVariationOn_flatQuotient_Ici`, native source
reflection and quantile differentiation; `XiC_analyticOrderAt_support`;
`xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip` and the exact
Fourier–Laplace jet theorem; `xiThetaDividedChain_partial_factorization`;
`deningerMeyerHedenmalmSource_transform`. These were read in current Lean
source and used in compiler-checked proofs. The final bridge search reported
72,546 inventoried files, complete inventory, and no unfinished search stage.
Compiler metadata still had pending/stale entries and semantic coverage was
not certified; search hits were leads, not proof certificates.

## Audit and limits

Each of the six leaves passed a direct foreground command of the form
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<Module>.olean GaloisForLFunctions/RHTower/<Module>.lean`,
from `formal/`, in dependency order. All six are wired into `RHTower.lean`.
No umbrella or full build ran. The `/tmp` axiom audit passed with only
`propext`, `Classical.choice`, and `Quot.sound` for all 21 selected structural
theorems. `scripts/formal_tools.py lint` passed with existing large-file
warnings. No holes, added axioms, numerical experiments or heartbeat changes.

The new construction is an actual BV/source-current family for every complex
parameter, not a claim that the original off-divisor mode became BV. It agrees
with that original mode on its full native BV domain. Entire dependence is
proved for the scalar charge; norm-holomorphic BV dependence and admission of
parameter derivatives of the modes are not proved. Nonlinear and prime–Gamma
boundary-work orientation, positivity, and spectral completeness remain
outside this contribution. Routine charge and finite-chain corollaries belong
to 007 and must not be counted separately.
