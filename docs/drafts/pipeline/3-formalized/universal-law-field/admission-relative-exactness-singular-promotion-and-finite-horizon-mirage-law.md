# Admission-relative exactness, singular promotion, and finite-horizon mirage law

- **ID:** ULF-OPM-7
- **Stage:** 3-formalized
- **Type:** ALGEBRAIC-VERSUS-SINGULAR PROMOTION SELECTOR
- **Statement:** Exactness is doctrine-relative. A residual can have an algebraic primitive while
  having no admitted primitive, even though every finite horizon admits an exact local primitive.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [SINGULAR-PROMOTION SELECTOR] [FINITE-GLOBAL SEPARATION] [LEAN-CERTIFIED] [NOT RH]

## 1. Exactness under an admission law

Let `D:C->R` be a residual-production law and let `Adm(c)` be the current admission predicate on
compensators. For a residual `rho in R`, define

\[
\begin{aligned}
 \mathrm{Exact}(\rho)&\Longleftrightarrow \exists c,\ Dc=\rho,\\
 \mathrm{Exact}_{\mathrm{Adm}}(\rho)&\Longleftrightarrow
   \exists c,\ \mathrm{Adm}(c)\text{ and }Dc=\rho.
\end{aligned}
\tag{AR.1}
\]

### Theorem 1.1 -- promotion trichotomy

Exactly one of the following mode tests holds:

1. `rho` is admitted-exact;
2. `rho` is algebraically exact but not admitted-exact;
3. `rho` is not algebraically exact.

The three cases have different mechanism meanings:

- case 1 permits strict gauge repair inside the current doctrine;
- case 2 forces an admission change, singular compensator, or retained relative class;
- case 3 requires extension/higher promotion or abandonment.

### Proof

Admitted exactness implies algebraic exactness. Split first on admitted exactness and then on
algebraic exactness. The cases are disjoint by logic. QED.

The point is not the trichotomy itself. The load-bearing statement is that a law-selection theory
must carry `Adm`; algebraic vanishing alone cannot choose the promotion.

## 2. Universal discrete singular cell

Let a calibration be a sequence `b:N->Z` and define its forward-difference residual

\[
 (Db)(n)=b(n+1)-b(n).
 \tag{AR.2}
\]

Take the constant residual

\[
 \rho(n)=1.
 \tag{AR.3}
\]

Declare a calibration admitted when it is bounded above:

\[
 \mathrm{Adm}(b)\Longleftrightarrow
 \exists C\in\mathbb Z\ \forall n,\ b(n)\le C.
 \tag{AR.4}
\]

### Theorem 2.1 -- algebraically exact, admission-singular

The residual `(AR.3)` is algebraically exact: `b(n)=n` satisfies `Db=rho`. But no admitted
calibration satisfies `Db=rho`.

### Proof

The counting calibration gives

\[
 (n+1)-n=1.
\]

Conversely, if `Db=1`, induction gives

\[
 b(n)=b(0)+n.
 \tag{AR.5}
\]

The right side is unbounded above, contradicting `(AR.4)`. QED.

Thus the same residual is trivial in the algebraic doctrine and nontrivial in the admitted doctrine.
The promotion selector is not cohomology alone; it is cohomology relative to legal primitives.

## 3. Finite-horizon mirage

For `N in N`, define the capped primitive

\[
 b_N(n)=\min(n,N).
 \tag{AR.6}
\]

### Theorem 3.1

Every `b_N` is admitted and

\[
 Db_N(n)=1
 \qquad(0\le n<N).
 \tag{AR.7}
\]

### Proof

`b_N(n)<=N`, so it is admitted. For `n<N`, both `n` and `n+1` are at most `N`, hence
`b_N(n)=n` and `b_N(n+1)=n+1`. QED.

Every finite observer therefore sees an exact admitted repair. No global admitted repair exists.
This gives a sharp mechanism-level finite/global warning:

> Compatible local-looking repairs do not imply one admitted global promotion unless their
> compensators obey a common admission bound or a separate compactness/coherence law.

## 4. Interaction with the promotion differential

ULF-OPM-6 decides whether a compensator closes algebraically by applying a promotion differential.
ULF-OPM-7 adds an independent question:

\[
 \text{Does a closing primitive belong to the legal doctrine?}
 \tag{AR.8}
\]

Together they produce a mechanism table:

| algebraic residual | admitted primitive | selected response |
|---|---|---|
| zero/exact | yes | strict or gauge repair permitted |
| zero/exact | no | singular admission promotion forced |
| nonzero at next differential | irrelevant at current level | higher coherence born |

This separates higher promotion from singular promotion by a law, not by choosing different
objects after the fact.

## 5. Withheld prediction

Any proposed finite-stage algorithm inspecting only residual values on `{0,...,N-1}` accepts the
capped primitive `b_N`. Therefore no such algorithm can certify global bounded admission. A valid
global selector must inspect a cofinal bound, compactness condition, or a reporter that survives the
limit.

This prediction was not used to define the residual or the admission predicate; it follows from the
same exact recurrence law.

## 6. Sharp boundaries

1. Bounded-above admission is a minimal laboratory, not a claim that every source uses this
   doctrine.
2. Finite repairs `b_N` are not a coherent inverse system of bounded calibrations with one common
   bound.
3. Changing admission may be legal or illegal; source law must decide.
4. No topology beyond the explicit boundedness predicate is assumed.
5. No proof route, positivity, recurrence, HT, or RH claim appears.

## Lean certification

Formalized without project axioms in
`GaloisForLFunctions.HTGeometry.ConstitutiveAdmissionRelativePromotion`:

1. generic algebraic/admitted exactness and exact trichotomy;
2. forward difference and counting primitive;
3. recurrence classification of every primitive of the constant residual;
4. no upper-bounded global primitive;
5. capped finite-horizon admitted primitives;
6. bundled singular-promotion mechanism theorem.

The module is wired into `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Log

- 2026-08-09 -- exactness made admission-relative; finite-horizon mirage isolated as singular
  promotion selector.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
