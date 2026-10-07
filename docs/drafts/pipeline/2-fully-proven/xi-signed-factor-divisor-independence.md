# Signed Xi factors retain independent labelled division classes

- **ID:** RH-XSFDI-20261007
- **Stage:** 2-fully-proven; exact square-class criteria formalized; complete halves fields remain a separate formal task
- **Parents:** `../2-fully-proven/xi-exponential-translate-square-rigidity.md` and
  `../2-fully-proven/xi-global-kummer-parity-transport.md`
- **Objective:** determine whether the additional translated-section classes retain
  all integer labels after the original sections' classes collapse to one class.

## Competing conjectures

Write `D_(epsilon,n)=1+epsilon*n^(-s)*xi(s)`, with `epsilon=+1,-1` and integer `n>=2`.
The classes of the positive companions could satisfy hidden relations, could have
finite rank, or could remain independent together with Xi and all negative factors.
The selected exact statement is the last: their finite-support span in
`M(C)^*/M(C)^*2` is free on Xi and every signed integer label.

Consequently, after adjoining all roots of `xi*D_(-1,n)`, the surviving classes
`[xi]` and `[D_(+1,n)]` are independent. For any finite nonempty set S, the full
halves fields of the translated sections together should have degree `2^(|S|+1)`
over this marked field. Original sections still share the single quadratic field.
The assertion concerns the algebraic directed union, not a completion.

## Internal and external audit

- Global nonsquareness of every individual signed factor is now available from the
  two parent cards; nonsquareness alone does not prove independence of their products.
- `RootExistence.exists_root_iff_orders_dvd` is already in the corpus: on a convex
  open set, locally finite zeros with orders divisible by two give an analytic root.
  The documented deep search returned complete retrieval (`partial=false`); source
  inspection confirms the statement. Applicability still needs a Lean check.
- The existing Riemann-kernel transform and nonnegativity are in
  `DeBruijnNewmanHalfBound.lean` / `WeilFullConeRiemannKernelRigidity.lean`.
  We only need the elementary boundary consequence `|xi(it)|<=xi(0)=1/2`.
- Exact external searches for Xi square classes, Kummer division fields, and disjoint
  exponential-factor zeros found no matching theorem. Classical parents remain
  [Milne, Theorem 5.30 and Remark 5.32](https://jmilne.org/math/CourseNotes/FT.pdf)
  and [Zarhin's explicit two-division formulas](https://arxiv.org/abs/1605.09279).
  Number-field elliptic Kummer results do not automatically apply to `M(C)`.

Hostile verdict: **SURVIVES PRELIMINARY ATTACK** as an exact source classification;
classical mechanism, novelty not certified. The first `[OPEN CORE]` for formal work
is the sharp boundary bound and its use to separate the actual signed divisors.

## Paper mechanism

The existing bilateral Riemann-kernel representation has nonnegative kernel Phi:
`xi(s)=integral Phi(x)*exp((s-1/2)*x) dx`. At `Re(s)=0`, taking norms under the
integral gives `|xi(s)|<=integral Phi(x)*exp(-x/2) dx=xi(0)=1/2`.
This uses the established exact kernel representation, with no numerical threshold
and no new analytic estimate toward RH.

If two differently labelled signed factors vanish at s, then
`xi(s)=-epsilon*n^s=-eta*m^s`. For distinct n,m, taking norms gives
`exp(Re(s)*log(n/m))=1`, hence `Re(s)=0`. The same equations give `|xi(s)|=1`,
contradicting the boundary bound. If n=m, opposite signs are incompatible directly.
Thus all signed factor zero sets are pairwise disjoint. No signed factor vanishes
at a Xi zero, since its value there is one.

Each factor is entire, nonzero at zero, and globally nonsquare by the parent results.
If all its zero orders were even, the existing analytic-root theorem on C would
produce an entire square root. Therefore each factor has an odd-order zero. Xi has
an existing odd-order zero too. At an odd-order zero of any selected factor, every
other factor and Xi is a unit. A product containing that factor to an odd power has
odd order, so it cannot be a meromorphic square. This proves the proposed freeness.

Kummer theory says that adjoining the marked roots kills exactly the span of
`[xi]+[D_(-1,n)]`. Freeness leaves the basis `[xi]` and all `[D_(+1,n)]` intact.
Every relation or radical in the infinite algebraic union occurs at a finite stage.

For Q on `y^2=x(x-1)(x-lambda)`, put `d=n^(-s)xi`, `lambda=1+d`, and
`x(Q)=lambda/d`. Its three two-descent coordinates have square classes
`[xi]+[lambda]`, `[xi]`, and `[lambda]` on the marked field. The explicit halves
formula gives the claimed fields and degrees. For P the classes span only `[xi]`.

## Verification plan and limits

- [x] Exact competing statements, relevant corpus search, and external parent audit.
- [x] Formalize the boundary bound and disjointness of signed source divisors.
- [x] Derive odd-order witnesses from existing global root existence.
- [x] Prove full signed-factor independence and marked-field persistence.
- [ ] Formalize the corresponding complete division fields and degrees.
- [x] Actual-source checks, axioms, imports, index/lint snapshot, scientific audit.

This would locate surviving prime-labelled information in the translated sections,
correcting any inference that the common class of the original sections erases all
labelled division data. It still supplies no arithmetic comparison selecting a real
form of a zero component and no discharged RH zero-location premise.

### Stronger separation statement exposed by the proof

For a fixed radius r>1/2, two functions `xi(s)+c*exp(h*s)` and
`xi(s)+d*exp(k*s)`, with real h,k and `|c|=|d|=r`, can share a zero only
when h=k and c=d. This is the same norm argument; it does not need h,k
nonzero. Combining it with the parent nonsquareness theorem would give
independent classes for all such labels with nonzero rates. This stronger
pencil statement is a separate conjectural consequence pending its own
formal and novelty audits; the implementation target remains signed integers.

### Formal audit checkpoint: odd divisors and exact finite criterion

The generic odd-zero extraction passes its scratch check. It instantiates the
existing analytic-root theorem on all of C, derives local finiteness from the
closed-ball divisor theorem, and contradicts global nonsquareness if every
zero order were even. A second checked lemma preserves the obstruction under
multiplication by a function nonzero at the odd zero.

The general equal-radius zero-separation theorem passed its initial scratch check.
Its signed-integer specializations and the generic odd-divisor lemmas are promoted
as `XiSignedFactorZeroSeparation.lean` and `EntireOddDivisorSquareClass.lean`, with
imports wired; their targeted build is underway. The assembled square-class proof
is still a scratch candidate. Its exact base-field target is
`IsSquare(xi^e * prod_negative(S) * prod_positive(T))` iff
`Even(e) and S=empty and T=empty` for admissible integer labels.
The marked-field target is `IsSquare(xiMarked^e * prod(lambda_n,T))` iff
`Even(e) and T=empty`. These criteria make every finite relation explicit.

### Exact square criteria pass Lean

The corrected assembled scratch passes with no diagnostics. It proves both iff
criteria above, including arbitrary natural Xi exponent and every finite set of
labels, in the global meromorphic field and the actual infinite marked field.
The two prerequisite leaves have targeted-build PASS. The final source leaf is
`XiSignedFactorSquareClasses.lean`; targeted build, direct actual-source checks
for all three leaves, and all 17 public declaration axiom audits are running.

The remaining complete-halves-field task has its own paper card:
`../1-in-progress/xi-legendre-complete-halving-criterion.md`. A separate generic sufficient-half
construction is prepared in scratch, not yet compiled or promoted. The main
square-class result is independent of that unfinished geometric sufficiency step.

## Verification closure

All three new leaves pass their targeted `lake --old build` and final direct
`lake env lean <actual source>` checks. Each final source log is empty.
Every one of the 17 public declarations was checked with `#print axioms` in
an external scratch audit: only `propext`, `Classical.choice`, and `Quot.sound`.
Imports are wired and the index command passes. No admissions, additional axioms,
numerical research computations, full builds, or heartbeat increases were used.

The authoritative lint snapshot fails on five unrelated unwired HTGeometry leaves:
`ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
`ApertureOpenHistoryIdeal`, and `BoundaryCoronaCStarAlgebra`. No error names this
card's three leaves. Concurrent work is left untouched; this is not a global lint PASS.
Logs: `/tmp/rh-signed-factor-separation-build-20261007.log`,
`/tmp/rh-signed-factor-squareclasses-build-20261007.log`,
`/tmp/rh-{EntireOddDivisorSquareClass,XiSignedFactorZeroSeparation,XiSignedFactorSquareClasses}-final-20261007.log`,
`/tmp/rh-signed-factor-axioms.log`, and the corresponding index/lint logs.

The auxiliary nonempty-positive-packet theorem even permits negative labels 0 and 1:
its odd positive-factor zero is a unit of every negative factor, independent of that
factor's own nonsquareness. This is covered by the same paper unit argument, not a
claim of negative-label independence at 0 or 1 (those two factors coincide).
The exact free-family criterion retains the stated label restriction n>=2.

**Final scientific verdict:** source square-class independence and its persistence
are established without an unproved source premise. The common class of the original
sections does not erase the independent labelled classes carried by their translates.
Complete actual halves fields and degrees remain on the follow-up card. No RH
zero-location, arithmetic comparison, or new literature-novelty claim is made.
