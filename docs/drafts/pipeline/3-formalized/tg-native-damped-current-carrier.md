# TG C9.29 — actual current Mellin formula and fixed-carrier meromorphic obstruction

- **ID:** TG-C9.29
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/tg-principal-polar-operator-cancellation.md; ../1-in-progress/tg-joint-prime-gamma-relative-lift.md
- **Statement:** The literal two-leg prime–polar current has an exact physical Mellin formula on its absolute-convergence half-plane and no fixed-Sonin-L2 meromorphic half-plane continuation into negative damping, for every nonnegative lower polar endpoint.

## Exact source and positive theorem

Let f0 be the literal indicator of [-1,1] and D_r the normalized physical dilation.
For Re z>1/2 the norm-convergent all-prime-power sum and strong polar integral are

    V_b(z) = sum_(n>=2) Lambda(n) n^(-z-1/2) (D_n+D_(1/n)) f0
             - integral_b^infinity exp(-z*u) 2 cosh(u/2)
                            (D_(exp u)+D_(exp(-u))) f0 du.

Every prime power and both physical legs are retained. For Re w>1/2 the head
Mellin functional ell_w(f)=integral_0^1 x^(w-1)f(x)dx is continuous on physical
L2 and holomorphic in w. With R=regularizedCriticalMellinDefect, the exact formula is

    w ell_w(V_0(z)) = -R(z+w-1)-R(z).

For every b>=0, V_b=V_0+P_b on the convergence half-plane, where P_b is the
literal finite polar integral from 0 to b. The physical vector P_b(z) is entire.
Its head pairing remains explicitly present in the formula for V_b. In particular,
b=log 2 is covered. No fitted probe or discarded expanding leg is used.

## Exact obstruction and paper proof

There are no b>=0, c<0 and meromorphic F:{Re z>c}->SoninL2 agreeing with V_b
throughout Re z>1/2. The corresponding bounded-operator-valued family with
this actual ground column is also impossible. These are closed negated-existence
Lean theorems with no unproved mathematical premises.

For b=0, restrict to -1/2<c<0 and choose a regular negative-damping point z0.
For each Re w>2, the complete expanding-leg term cancels in

    H_w(z)=w ell_w(F(z))-3 ell_3(F(z))+R(z+w-1)-R(z+2).

The two shifted R terms are holomorphic on the whole continuation half-plane.
The actual source formula makes H_w zero on Re z>1/2. Meromorphic uniqueness
makes it zero at z0. Thus the physical vector F(z0) realizes the forbidden
Mellin row on a far-right half-plane. Its head-Laplace holomorphy and analytic
uniqueness would extend R past the genuine Hardy-zero pole, contradicting the
corpus's unconditional Hardy nonextension theorem. Subtracting the entire P_b
reduces every b>=0 to b=0. Continuous evaluation at f0 gives the operator result.

## Lean and validation

- `SoninDampedPrimePolarCurrent.lean`: 22 public definitions/theorems; actual physical sum/integral and exact weak formula.
- `SoninDampedCurrentMeromorphicObstruction.lean`: 5 public theorems; current and operator-family exclusions, finite polar entirety, original endpoint transfer.
- Both final foreground `lake --old env lean <leaf> -o <olean>` audits passed, exit 0, empty diagnostics. Both imports are wired in RHTower. No umbrella/full build.
- Separate /tmp API and transitive axiom audit passed, exit 0, all 27 public declarations use only propext, Classical.choice and Quot.sound. Its first harness run needed explicit universe annotations; production proofs were unchanged.
- `scripts/formal_tools.py index` passed; all 27 API entries verified.
- Authoritative `scripts/formal_tools.py lint`: exit 1 on 18 unrelated unreachable modules; no finding for either new leaf. Existing large-file warnings remain.
- Logs: /tmp/tg-c929-current-final.log, /tmp/tg-c929-family-final.log, /tmp/tg-c929-axioms.log, /tmp/tg-c929-index.log, /tmp/tg-c929-lint.log. Final axiom source: /tmp/tg-c929-axioms.lean.

## Scope and remaining hard problems

This closes the fixed physical meromorphic half-plane continuation candidate
for the von Mangoldt current. It does not prove or falsify RH, prove the signed
Q bound, admit the original logarithmic source at zero damping, construct the
Gamma-completed relative class, or establish its Hardy cubic and strict sub-unit
budget. The original logarithmic source/current derivative identity has not
been formalized here. Varying carriers and relative quotients are not excluded.
The optional critical-current boundary conjecture below remains unproved and
is not part of this completed theorem.

Failed candidate and positive-salvage record:
`../5-failed/tg-fixed-carrier-meromorphic-current.md`.

## Gates

- [x] Concrete literal source and carrier.
- [x] Dependency-closed paper proof.
- [x] Exact positive survivor and obstruction formalized; named-leaf and axiom audits pass.
- [ ] Publication-ready standalone paper.

## Historical research log

- 2026-10-04: Candidate based on SoninPrimePolarSignedEnergy's native operator,
  SoninMellinFunctional's L2 power probes, SoninExtendedFunctionalEquation's
  head power integrability, and CCMHardyCriticalMellinNonextension's actual
  Hardy-zero pole argument. Deep search /tmp/tg-c929-operator-continuation-search.json
  running. No Lean edit or formal result yet.

## C9.29 paper refinement: complete current at lower endpoint zero

After differentiating the logarithmic source, its polar density is 2 cosh(u/2),
which is regular at u=0. Define V_0 using lower endpoint zero. The b=log 2
source differs by the original finite polar integral on [0,b]; retain this
explicit correction when transferring a conclusion back to that source.
The negative-damping result is not yet a statement about the Gamma completion.

The source definition in CCMComplexMellinColligation and the proved equality
in CCMInverseTiltedCriticalMellinFactorization give, with
R(u)=regularizedCriticalMellinDefect(u),

    w*ell_w(V_0(z)) = -R(z+w-1)-R(z)

on Re z>1/2, Re w>1/2. This is the planned actual-source positive theorem;
its physical source interchange is still to formalize. Both legs are explicit.

The negative-damping carrier implication reduces exactly to the corpus's
Hardy nonextension theorem. For -1/2<Re z<0, an L2 vector f and any constant c
satisfying w*ell_w(f)=-R(z+w-1)+c on Re(z+w)>1 would give

    A(u)=-(u+1-z)*ell_(u+1-z)(f)+c.

The head-chart isometry and half-line L2 Laplace theorem make A holomorphic on
Re u>Re z-1/2, and the displayed row identity makes A=R on Re u>0. This
contradicts no_analytic_extension_regularizedCriticalMellinDefect_pastHardy.
The arbitrary c includes the actual expanding-leg constant; no leg is dropped.

A stronger boundary conjecture is exposed, not yet certified: the differentiated
current at z=0 should also lack an L2 representative. The continuous head
functional has norm at most const/sqrt(Re w-1/2), while a genuine Hardy-zero
simple pole of R has inverse-linear radial growth. This concerns the CURRENT,
not the original logarithmic primitive: it does not disprove critical native
prime–polar admission. Check the existing corpus before formalizing this
stronger statement. Search /tmp/tg-c929-critical-current-search.json is running.

## Formal work in progress

- /tmp/tg-c929-api.lean: explicit-import API check passed (exit 0). Initial
  omitted-import/name probes failed and were corrected; no dependencies rebuilt.
- /tmp/tg-c929-head.lean: head continuous linear functional, exact head/Laplace
  representation and holomorphy passed scratch Lean checking (exit 0).
- The same scratch now includes the negative-current-row obstruction and the
  indicator pairing needed for physical dilation atoms; latest audit running.
  One earlier obstruction check needed an explicit inner function in AnalyticAt.comp.
- No production Lean file or umbrella changed. No new final leaf/axiom audit,
  no completed no-go, and no RH claim yet.

Search audit: operator-continuation search partial (unfinished filter_and_judge),
head-Mellin search nonpartial. Both had full source inventories and incomplete
compiler refresh. All candidate/source/idea/ingredient sections inspected.
Moment-coupling receivers and scalar-probe trace realizations were not used as
physical operator producers. Serena symbol lookup on the Lean source was
rejected because the path is ignored; source reads and direct Lean checks used.

### Scratch checkpoint: head and literal current assembly

The head scratch audit completed with exit 0, including the band-indicator
pairing and the negative-damping row obstruction. The only indicator repair
was using the implicit restricted-measure argument of `EventuallyEq.restrict`.
These are checked scratch results, not yet production theorems or final audits.

The actual source scratch now defines the all-prime-power sum with its original
LSeries coefficient and the full symmetric physical orbit, plus the complete
polar integral. Its first audit is running. The source norm uses the two
isometric dilation legs and the corpus's unconditional von Mangoldt absolute
convergence, only on Re z>1/2. A separate assembly draft pairs that physical
sum/integral with the head functional and identifies both translated defects.
No claim of convergence at zero or negative damping is made.

The critical-current search completed nonpartial, with the complete source
inventory and incomplete compiler refresh. Candidate lemmas, source arguments,
proof ideas and ingredient sets were inspected. Returned conditional Chebyshev
power spectra do not produce the missing physical vector. No matching boundary
current L2 impossibility theorem was identified in the returned hits; this is
not an exhaustive nonexistence claim. Stronger boundary work remains deferred
until the exact physical-source formula is audited.

Relevance assessment: this checks the proposed fixed-carrier operator
continuation. It does not establish signed-Q cancellation, original logarithmic
critical source admission, the full Gamma completion, or the Hardy cubic budget.

## Stronger C9.29 family conjecture: from the actual source, not an assumed row

New dependency-closed paper argument to audit: for -1/2<c<0, there is no
SoninL2-valued meromorphic F on Re z>c which agrees with the actual V_0(z)
on Re z>1/2. This supplies the missing continuation implication, rather
than assuming the forbidden row at a negative point.

Choose a regular point z0 of F with c<Re z0<0; meromorphy makes such points
available in every small punctured neighborhood inside that strip. For each
w with Re w>2, take the difference of the physical head probes at w and 3:

    H_w(z) = w ell_w(F(z)) - 3 ell_3(F(z))
             + R(z+w-1) - R(z+2).

Both shifted R terms are holomorphic throughout Re z>c, since c>-1/2.
The actual source formula gives H_w=0 on Re z>1/2. The meromorphic identity
principle therefore gives H_w(z0)=0 at the chosen regular point. Hence

    w ell_w(F(z0)) = -R(z0+w-1)+C,
    C=3 ell_3(F(z0))+R(z0+2),

for every Re w>2. No z-dependent expanding-leg term is assumed analytic:
it cancels before continuing. This is the key complete-source improvement.
The earlier head construction then gives A(u) holomorphic past Re u=-1/2,
agreeing with R for Re u>2. Analytic uniqueness on Re u>0 supplies the full
agreement needed by the existing unconditional Hardy nonextension theorem.

Corpus basis: HTGeometry/L2MeromorphicAlgebra's continuous-linear-map
preservation of Banach meromorphic germs; mathlib's isolated analyticity and
connected meromorphic-order propagation; the actual source row being audited.
Search /tmp/tg-c929-meromorphic-family-search.json is running. This family
argument is paper-only until direct Lean checking. Its extension to the b>0
family still needs the finite polar segment's parameter analyticity; no
meromorphic-family statement about the logarithmic primitive or Gamma
completion is claimed.

### Production current leaf under final audit

The complete scratch source passed `lake --old env lean` with exit 0,
including the literal all-prime-power/Bochner-integral formula, its four
polar Cauchy terms, arbitrary finite lower-endpoint correction, and the
negative-damping row exclusion with that correction. The new production
leaf is `SoninDampedPrimePolarCurrent.lean`; its final foreground audit is
running. No axiom audit, umbrella wiring or lint claim yet.

The family search completed partial (unfinished text_retrieval), with full
source inventory and incomplete compiler refresh. All result sections were
inspected. Its scalar continuation suggestions do not supply a Banach source
family. The applicable continuous-linear-map lemma was located in the actual
L2MeromorphicAlgebra source and checked against its statement. The stronger
family proof is drafted in /tmp/tg-c929-family.lean and has not been checked.

C9.29 current-leaf final audit completed with exit 0 and empty diagnostics:
`lake --old env lean GaloisForLFunctions/RHTower/SoninDampedPrimePolarCurrent.lean
-o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninDampedPrimePolarCurrent.olean`.
The import is wired into RHTower. The stronger family scratch is now running.
Its primary statement has no parameters or assumptions: no negative c and
SoninL2-valued meromorphic family can agree with the actual complete V_0 on
Re z>1/2. A bounded-operator corollary evaluates the proposed family at the
literal ground indicator. These family claims remain unverified until audit.

### Stronger family scratch passed; original endpoint transfer in progress

/tmp/tg-c929-family.lean passed `lake --old env lean` with exit 0. It proves
an unconditional negated-existence statement for meromorphic SoninL2 families
on any half-plane Re z>c with c<0, agreeing with V_0 on Re z>1/2. Evaluation
at the literal indicator also excludes bounded-operator-valued meromorphic
families with that actual ground column. The proof first cancels the complete
expanding-leg term by taking two head probes; it does not assume the forbidden
row at the negative point. Initial filter elaboration errors were repaired.
No family production leaf or final family/axiom audit yet.

To finish the original b>0 endpoint transfer, /tmp/tg-c929-finite.lean now
attempts entire parameter dependence of the literal finite polar integral.
The direct paper proof differentiates the vector exponential under the finite
integral, using a compact product to bound its derivative, then subtracts this
entire physical vector from any proposed continuation of V_b. The new search
/tmp/tg-c929-finite-polar-analytic-search.json remains running. Corpus's
HalfPlaneGapApproximation has the scalar version of the same dominated-kernel
argument; the new helper is for the actual Banach-valued physical orbit.

### Both final leaves audited; kernel audit pending

The compact-vector Laplace scratch passed after explicit function unfolding
and using global differentiability for complex analyticity. The merged
production family leaf needed one explicit beta reduction in the finite
endpoint corollary; its rerun passed with exit 0 and empty diagnostics:
`lake --old env lean GaloisForLFunctions/RHTower/SoninDampedCurrentMeromorphicObstruction.lean
-o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninDampedCurrentMeromorphicObstruction.olean`.
Both production imports are now wired. No umbrella or full build was run.

The final family result covers every b>=0, including b=log 2, and has no
unproved mathematical premise. Its scope is meromorphic families on an entire
half-plane extending into negative damping, on the unchanged physical L2
carrier (or bounded operators on it). The exact strong prime sum and polar
integral on Re z>1/2, their two-probe Mellin identity, and entire finite polar
segment supply the positive survivor. This is not a theorem about the
original logarithmic source's critical boundary, a Gamma-completed relative
class, or the signed Q bound.

The finite-polar analyticity search completed nonpartial with full inventory
and incomplete compiler refresh. All four result sections were inspected.
The final separate /tmp API and transitive axiom audit for all 27 public
declarations is running. Index/lint and final card closure remain pending.

## Final closure — 2026-10-04

Both final leaf audits and the separate 27-declaration API/axiom audit passed.
Only propext, Classical.choice and Quot.sound occur transitively. The API harness
universe annotations were fixed without changing production proofs. Index exit 0;
all 27 public API entries verified. Authoritative lint exit 1 reports 18 unrelated
unreachable modules, with no new-leaf finding. The exact false candidate and
positive survivor are now recorded in the linked failed-route card. All owned
Lean/search/index/lint processes have exited. No proof source changed after its
successful final audit. RH remains unresolved and the main goal remains active.

Cleanup: eight superseded owned scratch proof/fragment files removed after the final proofs and audits were recorded. Final audit source/logs and search evidence retained. Cross-session memory: rh/tg-damped-current-meromorphic-carrier-2026-10-04.
