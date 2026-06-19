# Bucket X1 — The A1/A2 unification (the carrier)

**Bucket grade:** organizational (SEARCH channel). Sorted from `docs/support-extraction-log.md`.
**Scope (one line).** RH (A1) and DSS/transcendence (A2) are **two readings of ONE object** — the
carrier germ `m_ξ` / the period matrix `Π=[p^{iγ}]` / the boundary representation of `G_L`.
**Work package this seeds.** State the **unified conjecture** ("one object, two readings") as a draft
brick, and pursue the **single rigidity statement** that, applied to the one germ, forces both faces.

> **The two guiding assumptions.** **A1** = RH becomes a natural byproduct. **A2** = the core tells us
> something about *time*. This bucket is the evidence that A1 and A2 are the *same* statement about a
> *single* native object — the deepest result the program names.

---

## The cleanest unification — one carrier germ, two readings (#76)
- The carrier `m_ξ(z) = −Ξ′/Ξ(z) = Σ_ρ 1/(ρ−z) = Σ_{k≥0} P_{k+1} z^k`. The secular moments `{P_k}`
  **ARE the Taylor coefficients of the carrier at 0.** The two assumptions are two coordinate systems
  on this one analytic germ:
  - **A1 (RH / positivity) = the germ's GLOBAL analytic type:** `m_ξ` Herglotz ⟺ `κ₋=0` ⟺ RH.
  - **A2 (DSS / transcendence / time) = the germ's INFINITE JET at 0:** `{P_k}` algebraically
    independent.
  *"RH reads the germ's monodromy/positivity type; DSS reads its infinite jet at a point. They are
  independent readings of the SAME function — which is exactly why neither implies the other, and why
  the field needs both wings."*
- **The payoff (the deepest result the user named):** because both faces live on **one germ**, a
  *single* rigidity statement feeds both — any bound forcing the germ transcendentally generic at 0
  (A2) is, by analytic continuation of the same germ, a constraint on its global pole structure (A1).
  **The common ingredient = the multiplicity estimate on `G_L`.** *The candidate mechanism by which the
  time-core would FORCE unitarity.*
- Both finite layers **ledger-proven:** `multiPair_carrier_exact_neg_inertia` (A1, κ₋ exact) +
  `spectrum_esymm_algIndep` (A2, finite jet independence). The open core is the infinite passage.

## The ridgeline — unitary ∧ faithful, one boundary representation (#92 — STRONGEST form)
- §3 the ridgeline: a zero `w_ρ=e^{iθ}` on the unit circle has two coordinates of the boundary
  representation of `G_L` (`μ_L=Σ_ρ δ_{w_ρ}`):
  - **RADIAL** (`|w|=1`? on the shoreline?) = **RH ⟺ the boundary representation is UNITARY.**
  - **ANGULAR** (`{θ_ρ}` genuinely spread / ℚ-independent?) = **DSS ⟺ the boundary representation is
    FAITHFUL.**
  > *"RH and transcendence are not two theorems that happen to be true together; they are the two ways
  > a faithful unitary representation of a compact group can be described — ON the circle (unitary/RH),
  > and FILLING it (faithful/DSS)."*
- **The no-margin = the SIGNATURE of faithfulness (key insight):** a faithful rep has spectrum DENSE on
  the circle (no gap); a uniform positive margin = a gap = a place the angles never reach = a hidden
  relation = the FAILURE of faithfulness. **"No margin ⟺ no spectral gap ⟺ faithful ⟺ the secret
  numbers are independent."** *The knife's-edge is the PRIZE wearing the mask of an obstacle — it IS
  DSS/A2.* (→ [[bucket-the-no-margin]]) Candidate **G20 (ridgeline).** Ledger: `multiPair_carrier_exact_neg_inertia`,
  `satake_trace_re_mem_Icc`, `linearIndependent_log_primes`.

## The period comparison — purity ∧ period-fullness of one matrix Π (#82, #83)
- The period matrix `Π = [p^{iγ_n}]` (rows = zeros = Betti/cycles, columns = primes = de Rham/forms,
  explicit formula = the comparison, `G_L` = motivic Galois group). **The whole field = the study of
  this one matrix.**
  - **A1/RH = PURITY:** `Π` pure of weight ½ (= Deligne's purity transported); FE = the polarization.
  - **A2/DSS = PERIOD-FULLNESS:** `trdeg(Π entries) = dim G_L` (Grothendieck period conjecture for Π).
  - §6 keystone: RH, DSS, GRH, GSH, `ζ(½)`-transcendence = **the purity and the period-fullness of ONE
    comparison Π.** Candidate **G18 (period-comparison).**
- #83 §1 the period matrix is **COMPUTED, not abstract**: entries = the secular moments
  `P_k=1−(−1)^k ζ(k)/2^k − a_{k−1}` = archimedean ζ-block ⊕ prime `a_j`-block. §5 **the unified stone
  (cleanest form):** *"the two places of `G_L` do not conspire — neither in SIGN (positivity ⟹ RH/A1)
  nor in ALGEBRA (independence ⟹ DSS/A2)."* One computed object, two questions: is it positive, is it
  generic. (the same archimedean non-conspiracy → [[bucket-the-seam-archimedean-obstruction]])
- #82 positioning: Deninger supplies the de Rham side, Connes' 1999 trace formula the analytic
  pairing + positivity (Face A). **The field's distinctive new layer = the TRANSCENDENCE (period)
  question (Face B)** neither program asks.

## The two-faces law / cone∩generic (#69 SEED-J, #70 SEED-P, #72 §9c)
- #69 §18/§20 **Object-X = the single point `(Σ_ρ ρ^{−k})_{k≥1}`** in moment space, with the Li
  coefficients `λ_n` ℤ-equivalent to `{P_k}` (triangular-unipotent, **ledger-proven**
  `li_secular_pointwise`): **Face A (RH) = a CONVEX-CONE condition** (`λ_n≥0`, Li's criterion);
  **Face B (DSS) = a GENERICITY condition** (`{P_k}` alg. independent). Candidate **G10 (cone∩generic):**
  the secular point lies in the Li-cone interior AND is transcendentally generic.
- #70 SEED-P/G14: **Face A ⊥ Face B are orthogonal difficulty axes** (the instantiation grid: ζ/L =
  A-hard∧B-hard apex; Ihara graph ζ = B-collapses; function field = A-theorem(Weil)∧B-algebraic).
  Candidate **G14 (orthogonality theorem):** "RH is the coincidence of both being hard in one spectrum"
  — provable first on the function-field row. *This is the structural statement of WHY the gatekeepers
  G1–G4 (all Face B) don't deliver RH (Face A).*
- #72 §9 the RH face in explicit Object-X coordinates (PROVED + numeric): `λ_n=n·P_1+(1−n)+Z_n−A_n`;
  **RH ⟺ the positive archimedean `Z_n` dominates the prime-period `A_n` ∀n = "Ω_∞ ≻ Π".** §9c: RH
  (positivity balance) and DSS (independence) are **two questions about ONE point driven by the SAME
  two-place split** `P_k = ζ-block − a_j-block`.

## μ's pseudorandomness = RH + LI, in analytic-NT language (#97 §6)
- `M(x)/√x ≈ Σ_γ e^{iγ log x}/(ρζ'(ρ)) + c.c.` is DETERMINISTIC almost-periodic (frequencies = the
  zeros); it only LOOKS random because the γ are ℚ-LI (Baker), so it equidistributes (Kronecker–Weyl).
  **μ's pseudorandomness = RH (γ real ⟹ bounded) + LI (γ independent ⟹ equidistribution).** *A1 and A2
  unified as a single statement — "μ is pseudorandom."* The LIL overshoot (te Riele, `limsup>1.06`) =
  Kronecker–Weyl resonance of ℚ-independent frequencies, NOT coin-flip stochasticity. *Caveat: soft
  (correlation-randomness) methods are amplitude-blind, structurally cannot reach RH.*

---

## The unification in one screen
| Object (one) | A1 reading (RH) | A2 reading (DSS/time) | Source |
|---|---|---|---|
| carrier germ `m_ξ` | Herglotz / `κ₋=0` (global type) | `{P_k}` alg. indep. (infinite jet) | #76 |
| boundary rep of `G_L` | UNITARY (on the circle) | FAITHFUL (filling it) | #92 |
| period matrix `Π=[p^{iγ}]` | PURE of weight ½ | period-full (`trdeg=dim G_L`) | #82,#83 |
| secular point `(P_k)` | in the Li-cone (`λ_n≥0`) | transcendentally generic | #69,#72 |
| Möbius `M(x)/√x` | bounded (γ real) | equidistributes (γ ℚ-LI) | #97 |
| no-margin | knife-edge positivity | = faithfulness / no gap | #92 |

**The single sentence:** *the two places of `G_L` do not conspire — not in sign (A1/RH), not in algebra
(A2/DSS); both non-conspiracies are the SAME archimedean rigidity on one computed object.*

## Open core / the work package
Write the **unified conjecture brick** (one object, two readings) and identify the **single rigidity
statement** — the multiplicity estimate on `G_L` — that would force both faces simultaneously. This is
the program's deepest target: "make RH and time one statement." The obstruction is archimedean
([[bucket-the-seam-archimedean-obstruction]]).

## Cross-references
- [[G5-unitarity-gatekeeper]] — the A1 face (unitary) made concrete.
- [[G2-multi-q-siegel-shidlovsky]] — the A2 face (faithful / DSS).
- [[bucket-time-and-non-holonomic-time]] — A2 *is* the time content; the carrier's jet = the clock.
- [[bucket-the-no-margin]] — the no-margin is the unification's hinge (= faithfulness).
- [[bucket-the-seam-archimedean-obstruction]] — both faces = one archimedean non-conspiracy.
