# Reporter meet, refinement monotonicity, and conservation-veto law

- **ID:** ULF-OPM-8
- **Stage:** 3-formalized
- **Type:** COMPOSITION LAW FOR PROMOTION SELECTORS
- **Statement:** Combining conserved reporters intersects their future envelopes. Strict-promotion
  admissibility composes by conjunction, and any one detecting reporter vetoes strictification.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [SELECTOR COMPOSITION] [NO SCALAR TRADEOFF] [LEAN-CERTIFIED] [NOT RH]

## 1. Reporter meet

Let `f,g:X->X`, and let

\[
 r:X\to B,
 \qquad
 s:X\to C.
\]

Their joint reporter is

\[
 (r\times s)(x)=(r(x),s(x)).
 \tag{RM.1}
\]

### Theorem 1.1 -- future-envelope meet law

\[
 K_{r\times s}^\infty
 =K_r^\infty\cap K_s^\infty.
 \tag{RM.2}
\]

### Proof

Equality of pairs after every future law word is equivalent to equality of each coordinate after
every word. QED.

Therefore reporter combination does not average, add, or cancel conservation constraints. It takes
their logical meet.

## 2. Promotion admissibility composes by conjunction

### Theorem 2.1

There exists an `(r x s)`-conserving strict exchange promotion if and only if both an `r`-conserving
and an `s`-conserving strict exchange promotion exist:

\[
 \mathrm{Strict}(r\times s)
 \Longleftrightarrow
 \mathrm{Strict}(r)\land\mathrm{Strict}(s).
 \tag{RM.3}
\]

### Proof

ULF-OPM-5 identifies strict admissibility with containment of the minimal exchange congruence in
the future reporter envelope. Apply `(RM.2)`. QED.

This is the first exact composition law for promotion selectors. Separate strict repairs need not be
chosen and reconciled: the same minimal exchange congruence works for both exactly when both tests
pass.

## 3. Refinement monotonicity

Suppose `r=h o s`, so `s` is at least as informative as `r`.

### Theorem 3.1

\[
 K_s^\infty\subseteq K_r^\infty.
 \tag{RM.4}
\]

Consequently

\[
 \mathrm{Strict}(s)\Longrightarrow\mathrm{Strict}(r).
 \tag{RM.5}
\]

### Proof

Future equality under `s` remains equal after applying `h`; then use the corridor criterion. QED.

Adding reporter resolution can invalidate strictification but can never create a strictification
that the coarser reporter forbade.

## 4. Conservation veto

### Corollary 4.1

If one reporter in a declared family detects an exchange residual in any future context, then no
strict promotion conserving the full family exists. Adding arbitrarily many blind reporters cannot
compensate for the detecting reporter.

This rules out scalarized promotion scores: a large number of satisfied conservation tests cannot
outvote one exact conserved charge.

## 5. Five-state calibration

Use the delayed-detection system from ULF-OPM-5. Let `u:X->Unit` be the constant reporter.

- `u` admits strict exchange promotion, because it is blind in every context;
- the delayed reporter `r` does not;
- the joint reporter `(u,r)` does not.

Thus present blindness, majority vote, or number of conserved scalars cannot replace the meet law.

## 6. Field consequence

Reporter doctrines form a contravariant order against quotient strength:

- more conserved reporters;
- smaller future envelope;
- fewer legal strict promotions.

This is a mechanism of law selection. It predicts how changing observation changes the space of
legal law changes, without postulating a universal state space or curvature tensor.

## 7. Sharp boundaries

1. The law governs strict promotion only; other promotion modes may retain the detecting reporter.
2. Reporter families are bundled by products; size and topological product admission are separate
   questions for infinite families.
3. No weighting or approximate tolerance is included.
4. Reporter provenance remains external to this theorem.
5. No proof route, positivity, HT, physical cost, or RH claim appears.

## Lean certification

Formalized without project axioms in
`GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion`:

1. paired reporter and exact future-kernel intersection;
2. strict-promotion existence iff conjunction;
3. reporter-factor refinement monotonicity;
4. constant reporter strict admissibility;
5. delayed reporter plus constant reporter conservation veto;
6. bundled selector-composition theorem.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Log

- 2026-08-09 -- derived meet-semilattice composition law for conserved reporter selectors.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
