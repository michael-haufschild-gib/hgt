# 111 — (AFE) and (LOW) discharged: the rung interface collapses to one finite parity

[PROVED HERE, Lean: `EMAnnulusSupply.lean`, `SymmetrizedEMCarrier.lean`] — the two named
analytic residues of doc 110 are gone. On a FIXED isolating annulus the accuracy demand
is not the hard exponential-sum core at all: the annulus is compact, so the elementary
Euler–Maclaurin tail (banked in `EMCarrier.lean`, no van der Corput, no cited constants)
gives `‖ζ − emCarrier N‖ → 0` there as `N → ∞`, and isolation gives ζ a positive floor by
compactness. Domination is therefore UNCONDITIONAL, and with it the entire analytic side
of the base rung.

## What was built

### The EM lane (`EMAnnulusSupply.lean`)

- `xi_zero_re_lt_one` — right-half ξ-zeros lie in the open strip (1-line nonvanishing).
- `completedEM N = archFactor · emCarrier N`; `completedEM_domination_iff` (arch divides
  out); `completedEM_analyticOnNhd_strip`.
- `zeta_annulus_floor` — ζ holds a positive floor on the closed annulus of an isolating
  ball (compactness + isolation), machine-checked.
- `exists_em_domination_on_annulus` — **∃ N with raw domination on the closed annulus**:
  the EM remainder `≤ (‖ρ‖+R)·N^(−σ₀)/σ₀` decays below half the floor.
- `exists_isolating_em_domination` — at EVERY strip point: an isolating annulus, a
  truncation length, and completed-member domination on the two slit charts. No
  hypothesis.
- `EMSplitData` + `emSplitData_exists` — dominating splits exist unconditionally;
  `emSplitData_count_eq` — every such split's hole count IS the central vanishing order.
- `rhLadder_of_em_split_multiplicity` (every rung k), `rhLadder_one_of_em_split_parity`
  (base rung), `riemannHypothesis_of_em_split_multiplicity` (RH itself): the whole
  2-adic ladder transports onto the finite member.

### The symmetric lane (`SymmetrizedEMCarrier.lean`)

The RS carrier `gN` has the exact FE but classical-debt accuracy; the EM carrier has
machine-checked accuracy but no FE. χ-symmetrizing the EM carrier yields BOTH:

- `semCarrier N = emCarrier N + χ·emCarrier N(1−·)` targets `2ζ` (the FE folds the two
  EM errors together): `two_zeta_sub_semCarrier_norm_le`, explicit two-term bound.
- `completedSEM N = archFactor·semCarrier N/2` satisfies the exact EVEN functional
  equation (`completedSEM_one_sub`) and Schwarz reality (`completedSEM_conj`), hence the
  full line reflection `completedSEM_lineReflection` — the finite member carries BOTH
  symmetries of ξ at every truncation length.
- `completedSEM_orderAt_one_sub` — **the mirror certificate is free**: vanishing orders
  pair exactly under s ↦ 1−s.
- `sem_uniform_decay_on_annulus` (constants from compactness: re-min, re-max, sup‖χ‖) +
  `exists_domination_of_uniform_decay` (generic: decay vs a nonvanishing target on a
  compact ⟹ some member dominates) ⟹ `exists_isolating_sem_domination` —
  unconditional domination for the FE-exact member.
- `SEMSplitData`, `semSplitData_exists`, `semSplitData_count_eq`, all rungs
  (`rhLadder_of_sem_split_multiplicity`), the base rung
  (`rhLadder_one_of_sem_split_parity`), and
  `riemannHypothesis_of_sem_split_multiplicity`.

All 22 endpoints: axioms exactly `[propext, Classical.choice, Quot.sound]`.

## Route state after this pass

```
RHLadder k  ⟸  per off-line zero ρ: for every dominating split of the finite member
               (completedEM N or completedSEM N) on every isolating annulus at ρ,
               2^k ∣ (hole count).                       [splits EXIST unconditionally]
RH          ⟸  the same for all k.
```

(AFE) and (LOW) no longer appear. The rung interface has zero analytic residue: the ONLY
open input is the divisibility of the hole-zero count of an explicit finite object — a
length-N Dirichlet block plus one pole term (plus its χ-reflection in the symmetric
lane), with N ours to choose and infinitely many valid witnesses per zero.

Faithfulness check (no slack, no cheat): `emSplitData_count_eq` pins every realizable
count to the central order, so the parity demand is exactly the order parity — the
interface is a lossless transposition of the rung onto finite data, not a weakening.

## Where the discriminator now sits

The symmetric member makes doc 108's F3 verdict finite: `completedSEM` is
FE-exact and Schwarz-real, so every mirror-symmetric functional of its boundary data is
parity-blind (the s ↦ 1−s order pairing is a theorem, and the pooled two-hole count is
automatically even). The parity of ONE hole's count — the open weld — is precisely the
datum the mirror structure cannot see, and the anchor tilt/defect instruments
(`AnchorTilt.lean`) are the designated symmetry-breakers. The Davenport–Heilbronn filter
survives intact: a D–H analogue admits the same EM machinery, so the discriminator must
use what ζ has and D–H lacks — the Euler product — inside the hole-count parity of the
finite member.

## Next objects

1. **Finite-member tilt coupling**: evaluate `anchorTilt`/`anchorMirrorDefect` against
   `semCarrier N` boundary phases on the isolating annulus — the deck cocycle of
   `√completedSEM` (`split_deckClass_one_iff_even`) as a function of the defect angle.
2. **Same-height order pairing**: the antiholomorphic order lemma
   (order at `1−conj ρ` = order at `ρ` for `completedSEM`), completing the value-level
   `completedSEM_lineReflection` at the order level.
3. **Truncation-length steering**: the count is N-independent (all = order), but the
   SPLIT GEOMETRY (positions of the zs inside the hole) moves with N — a new degree of
   freedom the anchored instruments can steer that did not exist for ξ itself.
