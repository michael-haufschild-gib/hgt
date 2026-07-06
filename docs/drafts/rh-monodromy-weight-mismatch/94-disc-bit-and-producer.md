# 94 — The DISC bit typed and decided; the producer interface welded

The two objects doc 93 §7 named are now built.  Four new Lean modules — `DiscWindow.lean`,
`DiscExtraction.lean`, `WindowProducer.lean` (plus the geometry they needed) — all axiom-clean
`[propext, Classical.choice, Quot.sound]`, RHTower + MainTheorems green (9139 jobs), lint passed.

## 1. The second boundary functional exists and, jointly with the loop, decides the rung

**The DISC theorem** (`deckClass_eq_line_iff_right_dvd`, ξ-instance
`xi_deckClass_eq_line_iff_right_dvd`): for a reflection-closed enclosed configuration with
reflection-invariant multiplicities, the deck class of level-`2^{k+1}` roots on the annular slit
charts equals the **line-predicted class** `exp(2πi·L/2^{k+1})` — computable from on-line data
alone — **iff** `2^k ∣ N`, the right-half order sum.  The discrepancy `(loop class)·(line
prediction)⁻¹` IS the window's rung datum.  Combined with the banked `deckClass_blind_to_split`
(the loop class alone cannot separate `L` from `D`): the line order sum is precisely the second
boundary functional; the pair (loop class, line data) is jointly complete where either alone is
blind.

Supporting geometry, new and reusable:
- `chartRA/LA_eq_image_slitAnnulus` — the annular slit charts are translated slit annuli;
  `isSimplyConnected_chartRA/LA`.  Consequently (`exists_annular_roots_of_enclosed`) **roots
  exist on the annular charts of every enclosed configuration** — the DISC reading is never
  vacuous.
- `exists_multi_peel_orders` — enclosed factorization with the TRUE vanishing orders as
  exponents (iterated peel, orders preserved at the remaining zeros).

## 2. The extraction: the family of DISC bits decides the rung PER ZERO

`LineHolography k` := every reflection-closed enclosed ξ-presentation with true-order
multiplicities has level-`2^{k+1}` deck class equal to its line prediction.

**`rhLadder_iff_lineHolography : RHLadder k ↔ LineHolography k`** — with the hard direction the
extraction (`rhLadder_of_lineHolography`): a single presentation reads only the SUM of enclosed
box orders (the blindness), but the *family* over all presentations reads each zero separately.
Mechanism, machine-checked: around a hypothetical right-half zero `ρ`, choose a **generic line
center** (`exists_good_line_center`: for each other zero the equal-distance heights solve a
linear equation — a finite bad set, avoidable since `Ioo` is infinite; the mirror pair is the
only degenerate case and is harmless, as `lineReflect ρ` falls left of the line); then two
nested presentations through that center — just inside and just outside the pair circle — have
right-half sums differing by exactly `m(ρ)`, and the two divisibilities subtract.
`rh_iff_forall_lineHolography` is the capstone: **RH ⟺ at every level, every boundary loop
agrees with its line prediction.**

## 3. The producer interface (`WindowProducer`)

- **`WindowLinePackage T`** — the named per-window line-data package (EM remainder bound,
  `emCarrier`/`gN` closeness `δ`, LOW floor `ε₁+δ` on the charts, strict ξ sign table, count
  budget), the exact hypothesis family of the window seam.
- **`rh_of_cofinal_windowLinePackages`**: packages on a *cofinal family of heights* give RH
  (`rhLadder_of_cofinal_windowLinePackages` per rung).  Monotonicity spreads cofinal
  certificates to all windows; nothing below the packages is open.
- **The assembly brick** (`exists_alternation_chain_of_strict_brackets` via `altChain`): `s`
  disjoint ordered strict sign brackets for a real function compose into ONE strictly increasing
  chain with `s` consecutive strictly negative products — the sign-table shape the package
  consumes.  One pass: from each bracket take the endpoint opposing the current chain end; if
  the near endpoint agrees in sign, the strict bracket forces the far endpoint to oppose.
  This welds the banked moment machinery (`exists_completedGN_sign_bracket_of_*`,
  `HardySignChange`: second-moment floor + closed first-moment budgets ⟹ bracket per segment)
  to the package's table shape: brackets on disjoint segments now assemble.

## 4. Status of the open supply (labelled, not proven)

The producer reduces RH to the supply of `WindowLinePackage` on cofinal heights.  Its faces:
(i) strict ξ sign tables — brackets are supplied by the banked moment budgets; the strict-vs-weak
gap and the ξ-vs-carrier seam remain the Hardy-grade open inputs; (ii) LOW floors and
`emCarrier`/`gN` closeness — budget-typed in `DpolyBallFloor`/`SeamCongruence`, open
quantitatively; (iii) the count budget — Jensen-typed, open quantitatively.  `[OPEN CORE]` These
are the exact analytic residue; everything else in both objects is unconditional Lean.

## 5. What this opens

The DISC theorem turns the boundary program into an equation-solving problem: the rung fails at
`ρ` iff SOME presentation's loop class misses its line prediction by a specific root of unity
(`exp(2πi·m(ρ)·2/2^{k+1})` on the isolating shell).  The next object is the **discrepancy
spectrum**: the map sending each line-centered window to its DISC value is a root-of-unity-valued
functional of the window, constant `1` under RH, and its value at any single window is finitely
computable from (loop data, line data).  Two forward moves: (a) transport the DISC functional to
the FINITE carrier (`completedGN`) through the banked order-equivariance package, where its
window values are decidable — a finite-side DISC census is a new instrument the tree can already
type; (b) collide the extraction's generic-center freedom with the `V₄`-symmetry: the DISC value
is constant along the center height `y` between zero heights (the presentations deform without
crossing zeros), so DISC is a locally-constant function on center space whose jump set is the
zero heights — a new discrete object (the DISC jump divisor) living on the line, made from bulk
data, that the boundary program can interrogate instead of the zeros themselves.
