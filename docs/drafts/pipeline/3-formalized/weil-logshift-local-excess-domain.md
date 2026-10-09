# Local excess moments replace global finite excess

Status: [FORMALIZED; GLOBAL LINT HAS ONE UNRELATED UMBRELLA ERROR]
Date: 2026-10-09
Source policy: our Lean corpus only; no web or external papers.

## Objective and plan

Replace global summability of positive normalized deviation by its weighted
moment at the individual probe. Prove an exact domain criterion, propagate it
to cofinal probes and coefficient growth, and certify that the enlargement is
strict with a concrete sequence.

1. Audit the probe identity, signed/excess/deficit split, and divergence proofs.
2. Formalize local excess comparison and the strengthened divergence alternative.
3. Prove local and cofinal domain equivalences, local growth bounds, and the
   subexponential coefficient characterization without global finite excess.
4. Exhibit infinite unweighted excess with convergent weighted moments at every
   real shift. Compile/export, audit every public declaration, wire/index/lint,
   promote, save memory, clean owned scratch.

## Dependency-closed paper proof

Let a=normalized deviation, e=max(a,0), v=max(-a,0), P_y(n) the paired full
kernel, and T_w(L,y) its truncated weighted sum. Since P_y>=0 and e<=|a|,
summability of a*P_y implies summability of e*P_y. Given the latter, a=e-v
shows signed and deficit moments are summable together.

At every real cutoff all truncated sums have finite support. The exact probe
identity and a=e-v give

 Q_L(c) = W_L(c)+2*(T_e(L,c)-T_v(L,c)-T_e(L,0)+2*D_v(L)),

where D_v(L)=sum v(n)K_L(log n). If E_c=sum e(n)P_c(n) is finite, then
T_e(L,c)<=E_c and T_e(L,0)>=0. Hence

 Q_L(c)<=W_L(c)+2E_c+4D_v(L)-2T_v(L,c).

For c=log m, m>=2, the positive-shift gain supplies
4D_v(L)<=T_v(L,c)+4H. Divergent origin mass therefore forces Q_L(c)->-infinity.
If origin mass is finite but the sampled deficit moment diverges, the origin
term stays bounded and T_v(L,c)->infinity, again giving Q_L(c)->-infinity.
Thus, assuming only the local excess moment, failure of signed sampled
summability forces divergence to minus infinity. An eventual lower bound on
integer cutoffs excludes this. Conversely signed sampled summability gives
its local excess moment and, by strict inward transfer, the origin convergence
needed for the exact finite real-cutoff probe limit. That limit supplies an
eventual integer-cutoff lower bound.

Consequently signed sampled summability is equivalent to the conjunction of
local excess summability and an eventual probe lower bound. Local critical-rate
theorems then give every coefficient growth bound above 2*pi/m from these two
conditions, with no unweighted excess condition.

On any cofinal sequence of integer-log probes, whole-line signed convergence
is equivalent to whole-line excess convergence plus individual lower bounds.
For the converse, given y choose a probe log(m_j)>=|y|+1, which ensures m_j>=2;
the local criterion and strict inward transfer give convergence at y. The
forward direction uses the exact finite limit at each probe, including m=0,1.
By the existing whole-line/subexponential equivalence this says: a is
subexponential iff e is subexponential and the cofinal probes are individually
bounded below. No uniform bound or cutoff across probes is required.

For strictness take lam(n)=vonMangoldt(n)+sqrt(n). Its normalized deviation and
positive excess are 1 for n>=2 and 0 otherwise. The unweighted excess series
diverges, while the constant bound and positive local decay rate make every
weighted potential summable. This also supplies finite probe limits everywhere.

This does not remove the local excess moment from the converse, settle the
critical growth endpoint, or extend uniform-panel positivity without further
proof. No new analytic assumption or external novelty claim is introduced.

## Corpus audit

Direct lexical search in WeilLogShift modules: 131 declarations, 19 modules,
37 eligible entries. Cached output has no partial/coverage fields. Relevant
source: SignedDivergence's exact split/upper bound, SingleProbeDomain's positive
shift gain and inward transfer, LocalDecayThreshold's growth bounds, and
SubexponentialDomain's unconditional whole-line characterization. Global excess
was used only to bound the positive sampled term in the old local divergence
argument. The proposed local replacement matches that exact use.

## Verification

- `WeilLogShiftLocalExcessDomain.lean` compiled and exported directly with
  `lake --old env lean <leaf> -o <local olean>`; exit 0, no diagnostics.
- Nine public theorems cover the local and cofinal criteria, the growth
  consequence, and the concrete strictness witness.
- All nine public theorems passed scratch `#print axioms`; only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- The umbrella import is added. Index refresh succeeded and all nine public
  API rows were inspected. Scoped `git diff --check` passed.
- Global formal lint exited 1 on one unrelated module unreachable from the
  RHTower umbrella: `CCMRestrictedWeilCrossFormBound`. Its source/imports were
  not modified. The two other unrelated umbrella errors from the preceding
  increment no longer occur in this gate output.
- All owned jobs exited. Owned `/tmp/hgt-weil-local-excess-*` scratch files were
  removed after recording this evidence. No numerical experiments, new axioms,
  unproved analytic inputs, heartbeat increases, full/umbrella builds, commits,
  or subagents.
- The existing uniform-positivity receiver still assumes global finite excess;
  no stronger uniform-positivity theorem is asserted by this increment.

All scoped proof steps are formalized. The exact new insight is that a probe's
own positive-excess moment is the only positive budget needed to recover its
convergence domain from a lower bound. Unweighted finite excess is strictly
stronger, as the formal unit-deviation witness demonstrates. On cofinal probes,
this changes the global coefficient class from summable positive excess to
subexponential positive excess.

## Next conjecture, not formalized here

Reflection about von Mangoldt, lam'(n)=2*Lambda(n)-lam(n), should exchange excess
and deficit and negate normalized deviation. The exact probe identity should
give Q_lam+Q_lam'=2W. This would dualize the local excess/minus-infinity result:
finite local deficit with nonsummable signed potential should force plus infinity.
Positive exponential deviation above the local critical rate would then provide
a sharp counterexample to dropping the excess moment from the lower-bound
criterion. Audit reflection and the finite-index exceptions before implementation.
