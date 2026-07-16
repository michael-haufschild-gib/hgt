# Lee–Yang localization (G7) — RH is the marginal point where the crystalline forcing degenerates

- **ID:** lee-yang-localization
- **Stage:** 0-backlog (physical); split done per Leaner note — the fully proven structural half
  is Lean-anchored in `../3-formalized/not_new_scientific_knowledge/lee-yang-marginal-forcing-structure.md`;
  this card is ready for restaging to `2-fully-proven/not_new_scientific_knowledge/` (relocation
  deferred to the pipeline maintainer, see library-backlog ticket 2026-07-16)
- **Type:** THEOREM (paper, structural) + CONJECTURE (the apex)
- **Grade:** BRIDGE (substrate) — the statistical-mechanics face of the no-margin / localization keystone.
- **Source:** #96 / SEED-E §81–82 + §81.3 (`bucket-new-sibling-conjectures`); the FE⟺crystalline side is
  `../2-fully-proven/fe-fourier-quasicrystal.md` (Professor, SEED-F §80). Connects: `dewitt-supermetric-no-margin.md`
  (`λ_c=1`), `no-margin-uniform-bound.md` (#89), Λ_dBN (de Bruijn–Newman, `Λ≤0⟺RH`, support-log L649),
  `omega-rh-coupling-vs-orthogonality.md` (decoupling), `intrinsic-rh-locus-pure-polarized.md` (#98, the fakes),
  #32/#33 (`κ₋`). Prior research checked (standing order): SEED-E/F are the seeds; the off-line DMV fakes are
  the foil; no 5-failed prior on Lee–Yang.
- **Statement (G7):** RH = the arithmetic (Poisson) base lies on the **marginal boundary** of the
  Lee–Yang / Kurasov–Sarnak crystalline locus — real-rootedness **marginal**, not forced. **Resolved
  structurally:** this marginality **is** the no-margin (`Λ_dBN=0 = λ_c=1 = κ₋=0`), and the degeneration of
  the forcing at the arithmetic point is a **structural reason RH is hard**.

---

## §1 The Lee–Yang forcing dichotomy and the arithmetic degenerate point `[SEED-E import + structure]`
For Beurling generalized-prime systems (`§79`), the Kurasov–Sarnak / Lee–Yang mechanism (SEED-E §81–82,
import) **forces** real-rootedness (the RH-analogue) when the FE-crystalline measure is in the
"strong-interaction" interior — by construction, like the ferromagnetic Lee–Yang circle theorem confines
partition-function zeros. Two failure modes flank it:
- **forced on-line** (interior, strong interaction) — RH-analogue holds *for free*;
- **forced off-line** (the **DMV off-line Beurling fakes**, Diamond–Montgomery–Vorhauer) — wrong-sign /
  "anti-ferromagnetic" forcing pushes zeros off the line; RH-analogue *fails*.

The **arithmetic ζ** is **neither**: it sits at the **Poisson/lattice degenerate point (§81.3) where the
forcing mechanism FAILS** — real-rootedness is **marginal**, not forced. ∎(§1, the dichotomy + the
degenerate point)

## §2 Marginality = the no-margin `[the consolidation]`
The marginal boundary is not a vague locus — it is the **no-margin**, in four equivalent presentations:
- **de Bruijn–Newman:** the tunable "interaction/temperature" parameter is the **dBN heat time `t`**; the
  arithmetic point is `t = Λ_dBN`, and real-rootedness is marginal there ⟺ `Λ_dBN = 0` ⟺ RH (`Λ≤0⟺RH`,
  Rodgers–Tao `Λ≥0`; support-log L649). "Marginal not forced" = `Λ_dBN` pinned to `0`.
- **DeWitt supermetric:** `= λ_c = 1` (the positivity-cone boundary, `dewitt-supermetric-no-margin` Finding 3;
  `λ_c≥1` free = Rodgers–Tao, RH = `λ_c=1`).
- **carrier:** `= κ₋ = 0` (#32/#33), the faithful signed index at the boundary.
- **quasicrystal:** the FE⟺crystalline self-duality (`fe-fourier-quasicrystal`, SEED-F) holds at the
  arithmetic point; G7 is its **localization** complement (real-rootedness), not the FE-rigidity.

So G7's "marginal real-rootedness" **is** the no-margin; Lee–Yang is the **statistical-mechanics language**
for it. ∎(§2)

## §3 Decoupling-consistency and fake-rejection `[structure]`
Per `omega-rh-coupling-vs-orthogonality` (the decoupling): the marginal real-rootedness (RH / localization
positivity) is the **κ₋=0 polarization positivity**, **separate** from realization (`ω=0`/DSS). The
Lee–Yang "interaction" that would force on-line zeros is the **polarization sign** — an archimedean datum,
not the realization. The **DMV fakes** are *realized* Beurling systems (have an Euler-like structure / an FE)
whose forcing is wrong-sign (zeros off-line) — **realized-but-not-positive**, rejected exactly as in
`intrinsic-rh-locus-pure-polarized` (#98). So G7 rejects the fakes by the **sign** of the forcing, matching
the realization-vs-positivity decoupling. ∎(§3)

## §4 The structural payload — WHY RH is hard `[the genuine new content]`
> **RH is hard because the arithmetic ζ sits exactly at the degenerate Poisson point where the Lee–Yang
> forcing mechanism fails.** It is on a **knife-edge**: not in the forced-on-line interior (no free proof),
> not in the forced-off-line fake region (not refuted) — the forcing is **marginal**. So no Lee–Yang /
> crystalline forcing argument can *force* RH for ζ: the very mechanism that would, **degenerates there**.

This is the **no-margin / exceptional-point** (#89/#93) given a *mechanism*: the marginality is not a
coincidence but the Poisson/lattice degeneracy of the forcing. It explains structurally why ζ is the hard
case among Beurling systems (RH is "rare", support-log L894): generic Beurling systems are forced (on- or
off-line); ζ is the measure-zero marginal stratum. ∎(§4)

## §4b The invariant decomposition — the mechanism ends exactly at the margin `[PROVED, Lean]`
The complete pointwise invariant of a monotone forcing locus `L` at a point is the pair
**(margin sign, boundary bit)**, and the forcing mechanism computes only the first coordinate:
- off the threshold, membership is a function of the margin sign alone
  (`IsForcingFamily.mem_iff_threshold_lt`); below-threshold rejection is §3's wrong-sign rejection
  (`notMem_of_lt_threshold`);
- for **closed** loci (the dBN locus `[Λ,∞)` is closed — de Bruijn–Pólya + Hurwitz) the boundary
  bit is **free**: the threshold is attained (`csInf_mem_of_isClosed`). So the apex is *not*
  "attainment at the margin" — attainment is free; the apex is the **threshold-location equality**;
- **no-margin equivalence**: closed locus + free half `t₀ ≤ sInf L` (the Rodgers–Tao side) give
  `t₀ ∈ L ↔ t₀ = sInf L` (`mem_iff_eq_csInf_of_le`) — §2's "marginality = no-margin" and §5's
  "achieved at the margin" are one statement; the four presentations transport by
  `marginal_transport` (affine presentation-independence of the axis);
- **degeneracy as theorem**: the full mechanism data-type (up-set + closed + free half) admits
  witnesses with identical structure that disagree at the physical point
  (`closed_forcing_data_not_decide_marginal`); without closedness even the boundary bit is
  undecided (`threshold_membership_undetermined`, `no_threshold_decision_rule`). §4's "no
  Lee–Yang/crystalline forcing argument can force RH" is now a formal underdetermination result;
- **mechanism of the degeneration** (two-spin miniature): at the marginal coupling `|b|=1` the
  Lee–Yang polynomial **factorizes** — the interaction decouples and the circle zeros **collide**
  at one pinned point (`leeYangTwoSpin_marginal_pos`, `leeYangTwoSpin_marginal_diagonal_sq`): the
  degeneration is a collision/decoupling, the exceptional point (#89/#93) in miniature;
- **ζ-side**: the carrier interaction locus is `{0}` — pure margin, empty interior, monotone
  forcing fails at the arithmetic carrier (`carrierInteractionLocus_eq_singleton`,
  `not_isForcingFamily_carrierInteractionLocus`); RH ⟺ every hypothetical right-half zero coupling
  is marginal (`riemannHypothesis_iff_zero_coupling_marginal`), unconditional, RH not asserted.
∎(§4b; Lean anchors in `lee-yang-marginal-forcing-structure`)

## §5 The open apex
Whether real-rootedness is **achieved** at the marginal point (= `Λ_dBN=0` = `κ₋=0` = RH) is the no-margin
**upper half** — the open apex (the lower half `Λ_dBN≥0`/`λ_c≥1` is Rodgers–Tao, free). §1–§4 place
G7 as the Lee–Yang no-margin and explain the hardness; they do **not** prove RH.
**Sharpened by §4b `[OPEN CORE]`:** for the closed dBN locus, attainment at the threshold is free;
the open half is exactly the equality **physical point = threshold** (`0 = Λ_dBN`, equivalently
`λ_c = 1`, `κ₋ = 0`), and by `closed_forcing_data_not_decide_marginal` no data of the forcing
mechanism's type decides that equality — deciding it requires an input orthogonal to the mechanism
(the arithmetic realization). `[CONJECTURE]` (the apex, unchanged): the equality holds — RH.

## Door passport — BRIDGE (substrate)
- **Door-2:** the Kurasov–Sarnak forcing is import; the marginality=no-margin identification and the
  why-RH-is-hard mechanism are structural / parent-reachable ⟹ BRIDGE; substrate-load-bearing (it unifies
  Lee–Yang, dBN, supermetric, κ₋, quasicrystal as one marginal locus).
- **Door-5:** over `F_q` the system is in the **forced interior** (single Frobenius / Hard-Lefschetz forces
  real-rootedness = Deligne), **not** marginal — so the marginality (no-margin) is **number-field-only**,
  matching `dewitt-supermetric` Finding 3 / the decoupling F_q calibration.

## Gates
- [x] 0 → 1: well-posed, source-pure (a prime measure, not the zeros); attack (Beurling family) sketched.
- [x] 1 → 2: §1 (forcing dichotomy + arithmetic degenerate point), §2 (marginality = no-margin, four
  presentations), §3 (decoupling-consistency, fakes rejected by sign), §4 (why RH is hard — the mechanism).
  BRIDGE (substrate). Real-rootedness-at-the-margin (=RH) stays the open apex (§5).
- [x] 2 → 3 (structural half): split ticket
  `../3-formalized/not_new_scientific_knowledge/lee-yang-marginal-forcing-structure.md` — four
  unconditional Lean modules (`HTGeometry/LeeYangForcingThreshold`, `HTGeometry/LeeYangTwoSpinCircle`,
  `HTGeometry/PencilPositivityRay`, `RHTower/LeeYangMarginalCarrier`), zero warnings, standard
  axioms only. The apex (§5) is quarantined there as unasserted `↔` statements; the marginal
  real-rootedness itself stays open.
- [ ] 3 → 4: "RH is the marginal stratum where crystalline forcing degenerates — why ζ is the hard Beurling case."

## Cross-references
- `../2-fully-proven/fe-fourier-quasicrystal.md` (Professor) — the FE⟺crystalline side; G7 is the
  real-rootedness/localization complement.
- `../2-fully-proven/dewitt-supermetric-no-margin.md` (`λ_c=1`), `no-margin-uniform-bound.md` (#89) — the
  no-margin G7 equals.
- `../2-fully-proven/omega-rh-coupling-vs-orthogonality.md`, `intrinsic-rh-locus-pure-polarized.md` (#98) —
  decoupling + fake-rejection (§3).
- `carrier-herglotz-rh.md` (#33), #32 — `κ₋=0` = the marginal real-rootedness.

## Log
- 2026-06-19 — created in 0-backlog (G7, SEED-E: RH = marginal-crystalline).
- 2026-06-19 (DeWitt) — **resolved → 2-fully-proven (BRIDGE substrate).** §1: the Kurasov–Sarnak/Lee–Yang
  forcing dichotomy (on-line interior / off-line fakes) with the arithmetic ζ at the Poisson degenerate point
  where forcing fails (SEED-E §81.3). §2: that marginality **is** the no-margin (`Λ_dBN=0=λ_c=1=κ₋=0`; the
  tunable parameter = the dBN heat time). §3: decoupling-consistent (the forcing sign = the polarization
  positivity, separate from realization; DMV fakes = realized-but-wrong-sign, rejected). §4: **structural
  reason RH is hard** — ζ is the knife-edge where the forcing mechanism degenerates. Open apex = real-rootedness
  achieved at the margin (=RH). Door-5: forced interior over `F_q`, marginality number-field-only. Grep'd; no
  web, no runpod.

## Lean formalizer return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven` to `0-backlog-lean` because the ticket is not a single fully paper-proven theorem ready for Lean formalization.

Defect: the metadata states `Type: THEOREM (paper, structural) + CONJECTURE (the apex)`, and §5 explicitly says real-rootedness at the marginal point (= RH) remains the open apex. The paper proof establishes a structural localization/no-margin interpretation, not the full real-rootedness/RH apex in the same ticket.

Per the synchronization rule, I did not narrow or rewrite the paper theorem. Please split out a fully proven theorem ticket or supply the missing proof for the open/conjectural component before returning this to `2-fully-proven`.

## Log (continued)
- 2026-07-16 (Fable) — **Leaner's split requirement discharged.** Created the exact split ticket
  `../3-formalized/not_new_scientific_knowledge/lee-yang-marginal-forcing-structure.md` carrying the
  fully proven structural half in four unconditional Lean modules (threshold trichotomy + marginal
  underdetermination; two-spin Lee–Yang trichotomy with marginal factorization/collision; pencil
  positivity ray with no-margin corollary; carrier interaction locus `{0}` + RH-as-marginality
  equivalences via in-tree `carrierHerglotz_iff_onLine` / `rh_iff_xi_ne_zero_right`). All
  `#print axioms` = `[propext, Classical.choice, Quot.sound]`; zero build warnings. **Research
  sharpening (§4b):** the invariant decomposition (margin sign ⊕ boundary bit) shows the boundary
  bit is free for closed loci, so the apex is exactly the threshold-location equality, and the
  formal underdetermination theorems make §4's "the forcing degenerates at the arithmetic point"
  a theorem rather than prose. §5 apex unchanged, `[CONJECTURE]`. rng session seed
  317826398794344498; drawn move `invariant`; collision domains auction-theory (RH = the
  tie-breaking datum the price mechanism is silent about) and renormalization (physical point =
  fixed point where the decision flow stalls — consistent with constraint-not-flow). Deferred to
  maintainer (no-builds directive): umbrella builds, lint gate run, index regeneration, physical
  relocation of this card to `2-fully-proven/not_new_scientific_knowledge/`. **Next generative
  move:** the underdetermination theorem says any RH-deciding datum must be orthogonal to the
  forcing data-type — formalize *which* orthogonal datum the two-spin miniature uses (the
  factorization certificate) and hunt its ζ-analogue on the pencil side (the `λ_c`-norm
  identification flagged in `dewitt-supermetric-no-margin` gate 2→3).
