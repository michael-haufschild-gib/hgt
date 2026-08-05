# Stokes contact tomography: realization layer closed (2026-08-05)

Card `stokes-cartan-contact-complexity-tomography` advanced 2 -> 3.

## What was missing and is now built

The whole U1/U2/U3 tomography layer (`StokesContactTomography`, `StokesDecoratedCore`,
`StokesRootedCutConstruction`, `StokesEnergyTree`, `StokesUniversalContactLaw`) was stated for a
**supplied** `DecoratedStokesCore.RootedRealization` / `CertifiedFissionDatum`.  Nothing in the
corpus constructed one, so every capstone was potentially vacuous.

New modules (all in `formal/GaloisForLFunctions/HTGeometry/`, wired into the umbrella):

- `StokesContactRealization.lean` — reconstructs the skeleton from the contact matrix.
  `ContactMatrix n` = symmetric + acute (`val i j <= max (val i k) (val j k)`) + strict diagonal.
  Vertices `ContactMatrix.Vtx` = contact balls `ball i (val i j)`; order is **reverse inclusion**
  (root = `univ` = bottom); `inf` = ball around a chosen centre with radius `sup` over the union;
  `pred` = minimum-cardinality strict superset; height `kappaV` = contact diameter.
  Capstones: `exists_realization`, `realization_contact`,
  `DecoratedStokesCore.nonempty_rootedRealization_iff` (an **iff**).
- `StokesFissionRealizationExistence.lean` — `IntegerContactHierarchy` (integral symmetric acute
  matrix with strictly smallest diagonal) with trivial ramification gives a realizable core;
  `twoLevelHierarchy f` from any partition; `nonempty_certifiedFissionDatum` (`1 < n`);
  `exists_certifiedFissionDatum_master_law`.
- `StokesRootedTripleLaw.lean` — `RootedContactTree.rootedTriple_iff` (the card's (RT)) and
  `DecoratedStokesCore.energy_eq_diagram` (the card's (8.4)).

## Reusable technique

Building a mathlib `RootedTree` by hand: supply `SemilatticeInf`, `OrderBot`, `PredOrder`,
`IsPredArchimedean` on a bespoke vertex type.  Traps hit:
- make the vertex type a **`structure`**, not a subtype/abbrev, or generic `Subtype` order
  instances collide with the intended reverse-inclusion order;
- `Fintype` via `Fintype.ofInjective` on the underlying `Finset`; `DecidableEq` via
  `Classical.decEq`; `Real.decidableLE` forces `noncomputable` on anything using `Finset.filter`
  over a real inequality;
- `IsPredArchimedean` proved by induction on `card a - card b` with `Function.iterate_succ_apply`;
- `PredOrder.pred` built from `Finset.exists_min_image ... |>.choose`.
- `push_neg` is deprecated on this toolchain: use `push Not at h` (the lint gate fails on warnings).

## Ultrametric facts used (all elementary from the three axioms)

every point of a ball is a centre; two clusters meeting in a point are nested; the diameter of a
cluster equals the radius measured from any of its points; a proper subcluster has strictly
smaller diameter.
