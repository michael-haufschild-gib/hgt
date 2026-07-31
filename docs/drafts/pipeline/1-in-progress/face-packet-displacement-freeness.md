# Freeness of the face displacement labelling

- **ID:** face-packet-displacement-freeness
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** the largest open row of `prop-interface-discharge-audit` — the mathlib-`Prop` premise
  `Function.Injective (facePacketDisplacementSlice τ hτ J hq)` (`hinjD`), consumed by
  `facePacket_no_telescoping_of_free` and `facePacket_differentialIndependent_of_free`.

## What the labelling is

`facePacketDisplacementSlice τ hτ J hq : ↥(packet J) → ↥(slice (insert q J) q)` is `y ↦ T_{τ q} y − y`.
The packet is the external-lattice orbit of the face coordinate and the coface equation is
`T_{τ q} Ψ_J − Ψ_J = Ψ_{J ∪ {q}}`, so the labelling is

  `T_g Ψ_J ↦ T_g Ψ_{J ∪ {q}}`,   `g ∈ faceShiftLattice τ J`.

## The universal law (formalized, unconditional)

`HTGeometry/FacePacketDisplacementFreeness.lean`.

**`facePacketDisplacementSlice_injective_iff_period`** — freeness *is* a comparison of translation
stabilizers, with no side condition at all:

  `Injective (displacement) ↔ ∀ h ∈ faceShiftLattice τ J, T_h Ψ_{J∪{q}} = Ψ_{J∪{q}} → T_h Ψ_J = Ψ_J`.

Forward: the two packet elements `T_h Ψ_J` and `Ψ_J` have equal displacements exactly when `h`
fixes the deeper coordinate.  Backward: two packet elements with equal displacements are external
translates whose difference fixes the deeper coordinate (`faceShiftLattice_sub`).

Supporting theorems in the same module:

- `facePacketDisplacementSlice_coe` — the displacement of `T_g Ψ_J` is `T_g Ψ_{J∪{q}}`;
- `faceShiftLattice_sub`, `faceShiftLattice_zero` — the external lattice is a group;
- `addTranslationMeroEquiv_intCast_multipleEllipticGammaLogDerivFaceMero` — **every integer
  translation fixes every face coordinate**, the unit period transported through
  `meromorphicTranslationStabilizer`; hence `ℤ ⊆ Per(Ψ_L)` for every face `L`, and
  `facePacketDisplacementSlice_injective_of_integral_period` reduces freeness to the one-sided
  statement `Per(Ψ_{J∪{q}}) ∩ faceShiftLattice τ J ⊆ ℤ`;
- `multipleEllipticGammaLogDerivFaceMero_fix_insert_of_fix` — a translation fixing a face
  coordinate fixes every deeper face coordinate, so the stabilizers only grow down the tower.

## The three regimes

Write `d = ((insert q J)ᶜ).card` for the number of parameters surviving the deeper face.
`facePacketDisplacementSlice_freeness_trichotomy` packages them.

- **`d ≥ 2`** — settled.  `FaceTranslateInjective.facePacketDisplacementSlice_injective`
  (concurrent lane) proves freeness from `PeriodsIntegrallyIndependent τ`, by descending to the
  two-surviving-parameter face where it is the nonvanishing of a nonresonant order-one defect.
  Read through the universal law this yields a period statement that was not otherwise available:
  **`multipleEllipticGammaLogDerivFaceMero_period_comparison`** — for `d ≥ 2` an external lattice
  shift fixing the deeper face coordinate fixes the face coordinate itself.
- **`d = 0`** (terminal face, `insert q J = univ`) — the deeper coordinate is the constant `−2πi`,
  so the labelling is *constant on the whole packet*:
  `facePacketDisplacementSlice_eq_of_terminal`, and
  `facePacketDisplacementSlice_injective_iff_subsingleton_of_terminal`,
  `facePacketDisplacementSlice_injective_iff_period_of_terminal`:

    `Injective ↔ Subsingleton (packet J) ↔ faceShiftLattice τ J ⊆ Per(Ψ_J)`.

  Here `Ψ_J` has exactly one surviving parameter, and its external lattice is spanned by the
  deleted ones.  So at the terminal face `hinjD` is *not* a freeness condition at all — it demands
  that the whole external lattice act trivially.  Any theorem consuming `hinjD` at the terminal
  face is therefore vacuous as soon as one external shift moves the rank-one face coordinate.
- **`d = 1`** — closed by `facePacketDisplacementSlice_injective_one_surviving`, see the closure
  section at the end.

## The rank-one period classification — **closed**; the routes below are the attempt record

> For a face `L` with exactly one surviving parameter `σ` (`Im σ > 0`), `Per(Ψ_L) = ℤ`.

This closes `d = 1` (the comparison target becomes `ℤ`, and `ℤ ⊆ Per(Ψ_J)` is proved), and it
settles `d = 0` negatively as soon as one external shift is not an integer.  The containment
`ℤ ⊆ Per` is proved; what is missing is `Per(Ψ_L) ⊆ ℤ`.

For one surviving parameter the coface equation is `T_σ Ψ − Ψ = −2πi`, so `T_{k+mσ} Ψ = Ψ − 2πi m`
and **no lattice element outside `ℤ` is a period**.  The whole gap is the containment
`Per(Ψ) ⊆ ℤ + ℤσ`.

- **Route A (pole set).**  `Ψ = N/D` with `D = F·B` entire.  `T_h Ψ = Ψ` gives the entire-function
  identity `N(z+h) D(z) = N(z) D(z+h)`; at `z = 0`, `B(0) = 0` and `F(0) ≠ 0`, so `N(0) = ±F(0)B'(0)`
  and `D(h) = 0` as soon as `B'(0) ≠ 0`.  `tprod_one_add_ne_zero_of_summable` then puts `h` on the
  zero set of a single factor, i.e. in `ℤ + ℤσ`, by `Complex.exp_eq_exp_iff_exists_int`.
  Missing input: **`B` has a simple zero at `0`**.  `Multipliable.tprod_eq_mul_tprod_ite` splits off
  the `n = 0` factor; the analytic half is locally uniform convergence of the complementary product.
- **Route B (period subgroup).**  `PeriodSubgroupCyclic` proves that the period group of a
  hypertranscendental meromorphic function is trivial or infinite cyclic, and
  `hypertranscendentalOver_multipleEllipticGammaLogDerivMero_iff_rankThreeMinor` makes `Ψ_L`
  hypertranscendental exactly when the surviving parameters carry a rank-three minor.  Since
  `1 ∈ Per(Ψ_L)`, a cyclic period group has a real generator `1/n`, so `Per(Ψ_L) ⊆ ℝ`; for the
  prime-logarithm family the external lattice meets `ℝ` only in `0`.  Missing input: the bridge from
  `meromorphicTranslationStabilizer` on `meroField` to `periodSubgroup` of the represented
  meromorphic function.  **Route B cannot reach the rank-one face** — no rank-three minor exists
  with one surviving parameter — so it would only re-derive the `d ≥ 2` case.

Neither route was needed: the containment is already proved for the Jacobi theta, and the missing
identification comes from a coface, not from a product formula.  See the closure section.

## Gates

- [x] 0 → 1  in-progress: freeness identified with the stabilizer comparison
- [x] 1 → 2  fully proven on paper: every regime settled, including `Per(Ψ) ⊆ ℤ + ℤσ` for one
  surviving parameter
- [x] 2 → 3  formalized: `FacePacketDisplacementFreeness.lean`, `FaceOneSurvivingTheta.lean`
- [ ] 3 → 4  n/a (infrastructure card)

## Log

- 2026-07-31 — `HTGeometry/FacePacketDisplacementFreeness.lean` created and registered:
  displacement identity, external-lattice group laws, the stabilizer-comparison equivalence,
  integer periods of every face, the climbing lemma, the terminal-face collapse, the period
  comparison for `d ≥ 2`, and the trichotomy.  `lake env lean` clean; `#print axioms` on all eight
  capstones gives `[propext, Classical.choice, Quot.sound]`.

## The rank-one core, sharpened

The analytic input needed for `d = 1` is *already proved in the corpus for the Jacobi theta*:

`MeromorphicThetaDefect.thetaLogDerivDefectMero_ne_zero_of_nonlattice` —
`ThetaNonlatticeShift τ h → T_h (thetaLogDerivMero τ) − thetaLogDerivMero τ ≠ 0`,
and the stronger `thetaLogDerivDefectMero_ne_const_of_nonlattice`.  That *is*
`Per(thetaLogDerivMero τ) ⊆ ℤ + ℤτ`.

With it, `d = 1` closes without any period computation in the `τ`-direction: for a deeper face whose
only surviving parameter is `τ r` (`r ∉ J ∪ {q}`), an external shift `h = ∑_{j∈J} n_j τ_j` that is
also `m + n τ r` is an integral relation among `1` and pairwise distinct parameters, so
`PeriodsIntegrallyIndependent τ` forces `h = 0`.

So the entire remaining gap is one identification:

> **`multipleEllipticGammaLogDerivMero ![σ]` is a translate of `thetaLogDerivMero σ`** —
> the rank-one analogue of `multipleEllipticGammaLogDerivMero_fin_two`.

This looked like it needed the **Jacobi triple product identity** — the rank-one multiple elliptic
gamma is an infinite *product* while `thetaLogDerivMero` is built from the *series* `jacobiTheta₂`,
and no product formula for `jacobiTheta₂` exists in mathlib or the corpus.  It does not: the rank-one
face is a *coface* of a rank-two face, and the crossing at rank two is already in the corpus
(`ellipticGammaLogDerivMero_source_face_sigma`).  See the closure section.

Two ways to finish, both genuine developments:

- **A — the triple product.**  Prove `jacobiTheta₂ z τ = ∏' …` and inherit the whole theta pole
  layer (exact zero set `jacobiTheta₂_eq_zero_iff_thetaHalfPeriod_add_lattice`, simple-pole orders
  `meromorphicOrderAt_thetaLogDerivDefect_base/shifted`).  Widest reuse: it gives the corpus a
  product-side handle on `jacobiTheta₂` that the whole theta layer would inherit.
- **B — the product zero set.**  Repeat the pole argument directly for the product-defined rank-one
  gamma.  `Ψ = N/D` with `D = F·B`; the single missing lemma is that `B` has a **simple zero at the
  origin**, after which `tprod_one_add_ne_zero_of_summable` and `Complex.exp_eq_exp_iff_exists_int`
  put every period in `ℤ + ℤσ`.

Route A subsumes B and is the recommended target.

## Closed: the rank-one core, and the exact criterion

The triple product is **not** needed.  The rank-one face is reached as a *coface* of a rank-two
face, and the corpus already crosses the product hierarchy to the series-side theta at rank two:
`ellipticGammaLogDerivMero_source_face_sigma` states that the `σ`-defect of the order-one elliptic
gamma is `thetaLogDerivMero τ` plus a constant.  Composing it with
`multipleEllipticGammaLogDerivFaceMero_two_surviving` and the coface equation gives the missing
identification directly.

`HTGeometry/FaceOneSurvivingTheta.lean` (built, registered, axioms clean):

* **`multipleEllipticGammaLogDerivFaceMero_one_surviving`** — a face `L` with exactly one surviving
  parameter `b` and any deleted `a ∈ L` satisfies
  `Ψ_L = T_{-(1+τ b)/2} (thetaLogDerivMero (τ b)) + c` for a constant `c`.  Proof: apply the coface
  equation to `L.erase a`, identify that two-survivor face with the order-one elliptic gamma, and
  use the source-face identity; translations commute and fix constants.
* **`exists_lattice_of_fix_one_surviving`** — hence `Per(Ψ_L) ⊆ ℤ + ℤ(τ b)`: a fixing translation
  makes `thetaLogDerivDefectMero` vanish, and `thetaLogDerivDefectMero_ne_zero_of_nonlattice`
  forbids that off the lattice.
* `faceShiftLattice_eq_zero_of_theta_lattice` — an external lattice vector of the face `J` that is
  also `m + n·τ r` for `r ∉ J` is zero: the two presentations form an integral relation with the
  unit period, killed by `PeriodsIntegrallyIndependent`.
* **`facePacketDisplacementSlice_injective_one_surviving`** — the `d = 1` regime, closed.
* **`not_facePacketDisplacementSlice_injective_of_terminal`** — the `d = 0` regime, closed
  *negatively*: for `insert q J = univ` and `J` nonempty the labelling is **not** injective, since
  `Ψ_J` is then itself a translated theta coordinate and no nonzero external shift lies in its
  lattice.  This is an unsatisfiability proof, not a gap: every consumer of `hinjD` at the terminal
  face with a nonempty deleted set is vacuous.

### The universal law

**`facePacketDisplacementSlice_injective_iff`** — for an integrally independent period family,

  `Injective (displacement) ↔ insert q J ≠ univ ∨ J = ∅`.

The three regimes are exactly the three ways this criterion is met or missed: `d ≥ 2` and `d = 1`
give the left disjunct, `J = ∅` gives the right one (its packet is a single germ), and the terminal
face with nonempty `J` is the only failure.

### The premise, discharged at the consumer

**`facePacket_differentialIndependent_of_periodsIntegrallyIndependent`** — the descending
face-lifting lemma with **both** of its arithmetic premises removed: rational independence of
`![1, τ q, τ u]` follows from `PeriodsIntegrallyIndependent` and freeness follows from the criterion,
leaving only the inductive independence of the target packet over the complementary base.

`#print axioms` on all six: `[propext, Classical.choice, Quot.sound]`.

### The layer, with its arithmetic premises discharged

`multipleEllipticGammaFaceLayer_diffIndepOn_deeper_of_periodsIntegrallyIndependent` — one uniform
face layer is jointly differentially independent over the deeper face field with **no** rational
independence and **no** freeness premise: for an integrally independent period family whose chosen
surviving directions are distinct and keep the next face nonterminal, both are automatic.  What
remains are the genuinely analytic star inputs (`hfree`, `hStarInj`, `hOffDA`).

`#print axioms`: `[propext, Classical.choice, Quot.sound]`.

- 2026-07-31 (later) — `HTGeometry/FaceOneSurvivingTheta.lean` created and registered in the
  `HTGeometry` umbrella; `lake env lean` clean, `lake build` of the module green, `#print axioms` on
  all seven capstones `[propext, Classical.choice, Quot.sound]`.
