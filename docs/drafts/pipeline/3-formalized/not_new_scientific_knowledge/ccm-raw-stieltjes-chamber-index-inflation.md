# Raw CCM Stieltjes chambers have cofinally unbounded negative index

- **ID:** `ccm-raw-stieltjes-chamber-index-inflation`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (Lean) / NO-GO / POSITIVE CLASSIFICATION
- **Scientific status:** `[LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Source:** `CCMPolarPrimeStieltjesAutocorrelation.lean` + the HTGeometry finite-atomic chamber law
- **Statement:** Every finite packet of distinct active critical-Mellin prime-power atoms produces
  one independent negative Pick direction per atom near the real boundary, despite the positive
  polar continuum.  Hence the raw polar-minus-prime Jordan carrier has cofinally unbounded negative
  index and cannot itself be a Hilbert or fixed-index Pontryagin aperture metric.

## Goal

Classify the raw signed Stieltjes carrier before trying to Hilbertize it.  For aperture `A`, its
source measure is

```text
dR_A(h) = 1_(0,2A](h) 2 cosh(h/2) dh
           - sum_(2 <= k <= exp(2A)) k^(-1/2) Lambda(k) delta_(log k).
```

At distinct selected prime-power nodes `a_j=log k_j`, use the Pick points
`z_j=a_j+i y`.  After multiplying the Pick Gram by `y^2`, the atom at `a_j` tends to the negative
diagonal coefficient `-k_j^(-1/2) Lambda(k_j)`, every other atom tends to zero, and the polar
continuum tends to zero because it is non-atomic.  Therefore the selected Gram is negative definite
for every sufficiently small nonzero `y`.  Arbitrarily large packets exist, so the negative index
is unbounded cofinally in the aperture.

This is source-pure: the nodes and coefficients come from the von Mangoldt source and no Xi zero,
RH-equivalent positivity assumption, or numerical evidence enters.

## Hostile audit and novelty boundary

The signed-atomic negative-square mechanism is a concrete case of classical Krein--Langer
generalized Nevanlinna theory.  HTGeometry already proves the general finite-atomic chamber law and
its rational-gauge invariance.  Consequently neither that parent theorem nor the statement
"hypertranscendence does not select the positive chamber" is new here.

The exact CCM specialization is useful as a route-closing theorem, not presently claimed as new
scientific knowledge.  Its RH significance is representational: the raw Jordan split is provably
the wrong place to seek the requested aperture Hilbert metric.

## No-go closure

- **Exact killing mechanism:** each uncancelled negative von Mangoldt atom has a boundary-localized
  Pick direction on which the positive polar continuum vanishes after the natural `y^2` scaling.
  No fixed positive background can absorb cofinally many such directions.
- **Strongest positive survivor:** the atom count is an exact chamber grading.  More importantly,
  the already formalized Stieltjes integration-by-parts identity rewrites the same aperture pairing
  through the cumulative critical-Mellin error.  Thus the first viable replacement is a
  **pre-Jordan primitive/source cancellation**: combine polar and prime terms before forming
  positive and negative norm channels.
- **New insight for the RH architecture:** a true aperture Hilbert metric cannot be the raw
  polar-minus-prime measure or any finite rational-atomic repair of it.  It must be built from the
  completed primitive/cumulative source (or an equivalent all-place factorization) whose defining
  operation erases the atomwise chamber grading before Hilbertization.
- **Status:** parent mechanism classical; exact CCM paper proof dependency-closed and formalized in
  `RHTower.CCMRawStieltjesChamberIndexInflation`.

## Lean result

The RHTower module `CCMRawStieltjesChamberIndexInflation.lean`, without modifying the shared
HTGeometry chamber modules, proves:

1. the critical-Mellin polar measure is finite and non-atomic on every finite aperture;
2. selected distinct positive prime-power atoms have strictly negative coefficients with a uniform
   finite margin;
3. their actual scaled Stieltjes Pick Gram is eventually negative definite, with chamber grade equal
   to the packet size;
4. a cofinal corollary supplies packets of every finite size.

## Gates

- [x] 0 -> 1: source-pure statement, collision audit, classical parent boundary, no-go, and positive
  replacement isolated
- [x] 1 -> 2: complete paper proof including the cofinal packet construction
- [x] 2 -> 3: unconditional Lean theorem, targeted leaf check green, axiom audit clean
- [ ] 3 -> 4: only after an independent novelty decision; do not promote a classical specialization
  as new science

## Log

- 2026-07-19 — Opened after the completed-Xi pole-resonance no-go forced cancellation before
  translation packets.  Whole-corpus comparison with HTGeometry shows the analogous source-side
  obstruction: cancellation must also precede the polar/prime Jordan split.
- 2026-07-19 — Formalized the exact polar measure, selected-packet chamber law, enumeration of all
  active nonzero von Mangoldt atoms, exact full-aperture chamber grade, and cofinal unboundedness.
  The targeted leaf check passed without warnings.  The four capstones use only `propext`,
  `Classical.choice`, and `Quot.sound`.
