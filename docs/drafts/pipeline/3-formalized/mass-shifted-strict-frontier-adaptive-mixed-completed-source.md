# Mass-shifted strict-frontier adaptive mixed/completed source

- **ID:** `mass-shifted-strict-frontier-adaptive-mixed-completed-source`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Every finite first Padé contact at an occupied physical strict frontier is carried by a literal adaptive mixed/completed `P^sharp` source: diagonal completed source at even contact, nondegenerate null-flag completed source at odd contact.

## Goal

Replace the parity-uniform bilinear contact producer by the native source algebra requested by the
route.  Admission chooses the monic null amplitude first.  Contact parity then selects either its
diagonal adaptive mixed completion or its nondegenerate null-flag completion before rational--Gamma
and von Mangoldt aggregation.  No divisor orientation, post-aggregation reporter, or RH premise is
allowed.

## Gates

- [x] 0 → 1 in-progress: exact claim, source-pure producer, falsifiers, and corpus dependencies identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted build and axiom gate green
- [ ] 3 → 4 publication-ready: standalone proof and independent priority review

## Conjecture → proof/fail ledger

1. `[FALSIFIED]` One diagonal adaptive mixed source carries every contact order.  Its source
   polynomial has even top degree, so it can expose only even first Padé contacts.
2. `[FALSIFIED]` Trace-coupled degree-centered completion repairs odd contact by itself.  Its
   landing contains `P.nextCoeff^2`; a zero admitted barycenter erases a nonzero odd defect.
3. `[PAPER-PROVED]` Nondegenerate null-flag completion adds a unit odd channel inside the source
   polynomial.  It lands on twice every first odd defect independently of the adjacent amplitude.
4. `[PAPER-PROVED]` Parity splice with diagonal adaptive mixed completion gives a native
   adaptive-mixed/completed source at every finite first contact.

## Approach

Let `P` be the terminal-normalized monic null polynomial of degree `m`, and let `d>0` be first
contact order.  If `d=2r`, use admitted amplitude `P X^(r-1)` in the literal diagonal adaptive
mixed completed source.  If `d=2r+1`, use `P X^r` in both entries of the nondegenerate null-flag
completed source.  Existing exact even- and odd-contact landing theorems identify these sources
with positive scalar multiples of first live Padé defect.  Right-chamber contact sign then gives
same alternating strict sign to literal source.

## External audit

Classical Hankel/Padé and Toda theory supplies parity of determinant contact but not shifted-Xi
rational--Gamma-minus-von-Mangoldt source formation with admission performed before aggregation.
Priority of exact parity-complete source law remains `[NOVELTY UNVERIFIED]`.

## Dependency-closed paper proof `[PROVED HERE]`

Fix `w>1/2`, degree `m>0`, terminal-normalized null vector `c`, and finite first contact `d>0`:

```text
delta_k = 0  for k < 2m+d.
```

Let `P=P_c`.

If `d` is even, write `d=2r`.  Positivity of `d` gives `r>0`.  Put
`A=P X^(r-1)`.  The exact even-contact theorem for the completed odd packet, followed by the
already-proved arithmetic identification of that packet, gives

```text
AdaptiveMixedCompletedSource_w(A) = (2m+d) delta_(2m+d).
```

This is one common-amplitude rational--Gamma-minus-von-Mangoldt formation; amplitude is chosen
before aggregation.

If `d` is odd, write `d=2r+1` and put `A=P X^r`.  The degree-centered source alone can lose the
odd defect when `A.nextCoeff=0`.  The nondegenerate null-flag completion adds the unit `X A^2`
channel inside source polynomial, while all lower even completion channels vanish against null
ideal because every lower Padé defect is zero.  Exact odd-contact landing theorem therefore gives,
for any adjacent amplitude `B` and hence for `B=A`,

```text
NondegenerateNullFlagCompletedSource_w(m+r,A,A) = 2 delta_(2m+d).
```

Both multipliers, `2m+d` and `2`, are positive.  Consequently any strict alternating contact sign
`(-1)^d delta_(2m+d)>0` transfers to literal selected source.  Every positive integer is even or
odd, so cases are exhaustive.  QED.

## Log

- 2026-08-13 — card opened after bilinear all-contact law exposed mismatch with requested native adaptive mixed/completed `P^sharp` aggregate.
- 2026-08-13 — diagonal-all-contact and trace-only conjectures killed; nondegenerate parity splice paper proof closed.
- 2026-08-13 — parity-complete generic law, strict-frontier specialization, and premise-free cofinal phase formalized in `XiShiftedStrictFrontierAdaptiveMixedCompletedSource.lean`; direct Lean, targeted module build, and axiom audit passed. Global lint remains blocked only by unrelated concurrent untracked RHTower modules missing umbrella imports.
