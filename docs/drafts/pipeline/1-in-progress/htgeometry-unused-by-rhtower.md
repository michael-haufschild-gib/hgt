# 82% of HTGeometry is unreferenced by the RH tower — and the creator we were missing is in it

- **ID:** `htgeometry-unused-by-rhtower`
- **Stage:** 1-in-progress
- **Type:** MEASUREMENT + FINDING
- **Scientific status:** `[MEASUREMENT OF CORPUS STATE]` `[NOT AN RH PROOF]`
- **Follows:** `positivity-creators-versus-transporters.md`, which concluded that every RH-adjacent
  positivity in the corpus *transports* and that **counting** is the only creator that survives.

## 1. The measurement

```text
HTGeometry modules                       2571
referenced anywhere in RHTower            547
never referenced by RHTower              2121   (82%)
of those, RH-suggestive by name            217
```

(Names matched on `prime|zero|critical|positiv|herglotz|zeta|euler|dirichlet|explicit|weil|hadamard|
entire`. Reference counted as any occurrence of the module's full name in `RHTower/*.lean` or the
umbrella, so this over-counts usage if anything.)

Separately: **no HTGeometry module mentions `RiemannHypothesis` at all** — `grep` over all 2571
returns nothing. That is by design (`formal/CLAUDE.md` reserves HTGeometry for reusable
infrastructure), and it means "use HTGeometry" can only mean *consume more of it from RHTower*.

## 2. The finding: the creator is already there, and unused

`positivity-creators-versus-transporters.md` §3 concluded that the only positivity mechanism that
creates rather than transports is **counting**, and §7 that the corpus had no counting creator
reaching zero location. The first half of that is now sharper and the second needs qualifying,
because HTGeometry contains a counting creator that RHTower never references:

**`HTGeometry/CountPositivityConductorBound.lean`**

> *"A Riemann–von Mangoldt count has the shape `A·T·log T + B·T + E(T)` with `|E(T)|` logarithmic.
> Because a count is never negative, the linear coefficient `B` cannot be very negative… For a
> zero-counting function `A = d/2π` and `B = (log q)/2π` with `q` the conductor, so the conclusion
> reads `q ≥ exp(−2π·C·(1 + log 3))`: **a nonnegative zero count forces a positive lower bound on the
> conductor**, with the bound governed solely by the uniformity of the error term."*

with `linear_coeff_ge_of_nonneg`, `linear_coeff_ge_of_nonneg_at_one`, `conductor_ge_of_count_nonneg`.

This is exactly the shape the inventory asked for: **no positive input.** The only hypothesis is that
a count is a count. Nonnegativity is created by the definition and then converted into an arithmetic
inequality. Nothing else in the corpus's RH-adjacent positivity does that.

A second unused item of the same family:

**`HTGeometry/AtomicHerglotzResidueCone.lean`** — a finite real Cauchy divisor over the universal
positive background has nonnegative imaginary part on the upper half-plane **exactly when every
residue is nonnegative**, with `exists_upper_im_neg_of_continuous_add_negativeCoefficientAtom` giving
an explicit negativity witness for any negative residue. That is a *rigidity*: Herglotz-ness detects
the sign of every residue individually, not on average. Also unreferenced by RHTower.

## 3. Why this changes the target

The inventory's §7 asked for a counting creator that sees **zero location** and answered negatively,
because Rankin–Selberg pole orders see factorization multiplicity only. `CountPositivityConductorBound`
does not see zero location either — it sees the *linear coefficient of the counting asymptotic*, i.e.
the conductor. But it establishes the pattern, and the pattern is what the inventory was looking for:

> take a quantity that is nonnegative **because it counts**, expand it asymptotically, and read an
> inequality off the coefficients.

The question that pattern makes concrete, and which is now the target:

> **Apply the same argument to `N(σ,T)`, the count of zeros with real part `> σ`.** It is nonnegative
> because it counts. If it admits an asymptotic expansion with a computable main term for `σ > 1/2`,
> the same coefficient argument constrains that main term — and under RH the main term is `0`, so any
> unconditional *lower* bound on the main term that is positive would refute RH, while the coefficient
> inequality runs the other way.

Whether `N(σ,T)` has such an expansion unconditionally is the classical zero-density question, so
this does not evade §7's conclusion. What it changes is that the corpus now has the *mechanism*
formalized and can state the question in its own terms rather than importing it.

## 4. Honest grade

The measurement is bookkeeping — `comm` on two sorted lists — but it is bookkeeping nobody had done,
and 82% is large enough to be the main finding of this card. The identification of
`CountPositivityConductorBound` as a genuine creator is a reading of an existing module against an
inventory written the same day; the module's own docstring states the mechanism plainly and claims
nothing more.

**What I would defend:** the RH tower has been reasoning about positivity while a proved
positivity-*creator* sat unreferenced in the sibling area, and the inventory that identified creators
as the scarce resource was written without checking HTGeometry for one. Both facts are corrected
here.

## Gates

- [x] measurement: 2121 of 2571 HTGeometry modules unreferenced by RHTower; 217 RH-suggestive
- [x] no HTGeometry module mentions RH — the area is infrastructure by design
- [x] `CountPositivityConductorBound` identified as a counting creator, unreferenced
- [x] `AtomicHerglotzResidueCone` identified as a per-residue sign rigidity, unreferenced
- [ ] triage the 217 RH-suggestive unreferenced modules
- [ ] apply the counting-creator pattern to `N(σ,T)`
- [ ] independent audit (Codex)

## Log

- 2026-07-27 (Claude): written after being told, correctly, that I was narrowing onto classic routes
  instead of using the HTGeometry research. The measurement was the first thing I should have run and
  I ran it last.
