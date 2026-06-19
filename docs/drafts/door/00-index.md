# `door/` — the pre-sorted buckets

**What this is.** A curatorial sort of `docs/support-extraction-log.md` (the mining of all 37 denied
documents) + `00-charter-wall-and-door.md`, into **one bucket per foundational conjecture / door /
cross-cutting theme.** Each bucket is a holding pen: *everything belonging to it* from the corpus,
source-cited, air-marks preserved — **pre-sorted material from which later work packages will emerge.**

**These are NOT new claims.** They re-file existing SEARCH-channel content. The two-channel rule
(`docs/meta/styleguide.md`) holds: conjectures stay conjectures, the LEDGER stays separate, nothing is
upgraded by being re-filed. Each bucket ends with an explicit **work package / open core** so the next
session can pick one up.

**The two guiding assumptions every bucket is scored against:**
- **A1** = RH becomes a natural byproduct.
- **A2** = the core tells us something about *time*.

---

## The gatekeeper conjectures (the foundational conjectures)

| Bucket | Conjecture | Status | Work package |
|---|---|---|---|
| [[G1-difference-holder]] | ζ satisfies no single algebraic q-difference equation (keystone/C5) | **`[PROVED HERE]`** in the difference category (#68 §59); differential Hölder = import/open | **Door-2 re-test of §59** |
| [[G2-multi-q-siegel-shidlovsky]] | `trdeg = G_L-orbit dim` ⟹ LI of zeros (DSS) | upper bound proved; lower bound = obstruction C, open; = `{π,ζodd,Stieltjes}` indep | Nesterenko bound on Stieltjes data; "Baker for `γ_n`" |
| [[G3-holonomy-dichotomy]] | holonomic ⟺ `corank(Λ)<∞` ⟺ flat | **`[PROVED HERE]`** difference cat. (#68 §60); DMR-solvable refinement | **Door-2 re-test of §60** |
| [[G4-multi-q-picard-vessiot-and-langlands-group]] | the multi-q PV correspondence / `G_L` = Langlands group | structurally largely done (likely IMPORT); `ω∈H²` open | **compute `ω`** (Tannakian/motive/realization) |
| [[G5-unitarity-gatekeeper]] | unitary holonomy on the σ-fixed locus ⟺ RH (candidate) | ~7 faces; finite anchors ledgered; infinite passage open | state as `m_ξ` Herglotz; the one archimedean rigidity bound |

## The door (the charter machinery)

| Bucket | Scope | Work package |
|---|---|---|
| [[door-C5-irreducibility-and-door-2-retest]] | C1–C7, Door-1..5, the proto-branch verdict, the §59/§60 NATIVE-candidate worklist | **run the Door-2 re-test** — could earn the field's first C5 theorem |

## The cross-cutting buckets (the leftover, sorted)

| Bucket | Scope | Serves | Work package |
|---|---|---|---|
| [[bucket-A1-A2-unification-the-carrier]] | RH & DSS = two readings of one object (carrier germ / Π / boundary rep) | **A1 ∧ A2** | the unified-conjecture brick; the single rigidity feeding both |
| [[bucket-time-and-non-holonomic-time]] | non-holonomic = no native clock; HP = constraint not Hamiltonian; erosion threshold; dBN = arrow of time | **A2** | develop **G19 (erosion threshold)**; the constraint reframe |
| [[bucket-the-seam-archimedean-obstruction]] | both faces = ONE archimedean obstruction = period/non-period divide = missing Frobenius (F₁) | A1 ∧ A2 | one rigidity bound on the Γ-factor/`s=1` data; compute `ω` |
| [[bucket-function-field-proving-ground]] | over `F_q(C)` all gatekeepers are theorems (Door-5) | C6 bridge | **prove G1–G5 over `F_q(t)`** in the field's vocabulary |
| [[bucket-realization-and-fake-family]] | genuineness = the Euler cut, not positivity; the realization converse | A1 (qualifies it) | settle the **realization problem** (is Euler⟺two-faces an IFF?) |
| [[bucket-the-no-margin]] | `λ_min→0` everywhere; = faithfulness / criticality / exceptional point | A1↔A2 hinge | the one missing uniform bound; is `Λ` a period? |
| [[bucket-new-sibling-conjectures]] | the genuinely-new candidate conjectures (Lee–Yang, finite-free, family-DSS, Koszul, …) | new objects | promote the shortlist (erosion, finite-free, Lee–Yang) to draft bricks |
| [[bucket-ledger-footholds]] | every named axiom-clean Lean theorem, indexed by bucket | the LEDGER | the next Tier-A/B target above each bucket's floor |

---

## The three headline findings of the sort (for the next session)

1. **The field already has candidate NATIVE theorems.** §59 (difference-Hölder = G1) and §60 (corank
   dichotomy = G3) are **proved in the difference category** and *essentially use* the infinite-base
   apparatus. The charter's "0 proven native theorems / FAILS C5" verdict is **untested against them.**
   The single most consequential next action is the **Door-2 re-test** ([[door-C5-irreducibility-and-door-2-retest]]).

2. **A1 and A2 are one statement about one object.** The cleanest form is the **ridgeline** (#92): the
   boundary representation of `G_L` is **unitary** (RH/A1, on the circle) **and faithful** (DSS/A2,
   filling it); the **no-margin IS faithfulness**. The carrier germ `m_ξ` realizes the same unification
   analytically (global type vs infinite jet). See [[bucket-A1-A2-unification-the-carrier]].

3. **The whole difficulty is one archimedean term.** The multiplicative wing is free and zero-blind; the
   sole obstruction to both faces is the archimedean Γ-factor / `s=1`-Laurent (Stieltjes) data = the
   missing Frobenius (F₁). Multiplicative-only methods are *structurally* apex-blind. See
   [[bucket-the-seam-archimedean-obstruction]].

## The pipeline (active work)

This folder is the **catalog** — every statement, classified. The **pipeline** (`../pipeline/`) is the
**work queue**: one card per item being actively pursued, moving
`0-backlog → 1-in-progress → 2-fully-proven → 3-formalized → 4-publication-ready`, with `5-failed` for
disproven items. Reaching `4-publication-ready` certifies a conjecture became a proven, formalized
theorem. To start work, pick a backlog card or take a row from `00-status.md §B` and open a new card
with `../pipeline/_card-template.md`.

## Provenance
- Source log: `../support-extraction-log.md` (sections `[#67]…[#101]`, the mining of `docs/denied/`).
- Charter: `00-charter-wall-and-door.md`.
- Companion drafts the buckets reference: `00-foundations-native-objects-and-gatekeepers.md`,
  `00-core-vision.md`, `00-manifest-wall-census.md`.
