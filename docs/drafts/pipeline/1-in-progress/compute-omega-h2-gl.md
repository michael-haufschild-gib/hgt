# Compute the monoidality obstruction ω ∈ H²(G_L) (G4 open core)

- **ID:** compute-omega-h2-gl
- **Stage:** 0-backlog
- **Type:** OPEN CORE → CONJECTURE (native)
- **Priority:** FIELDS MEDAL
- **Source:** ../../door/G4-multi-q-picard-vessiot-and-langlands-group.md (#73 §4, open core), ../../door/bucket-the-seam-archimedean-obstruction.md (#90) · 00-status rows #27, #28, #71
- **Statement:** Compute (or bound) the **monoidality obstruction `ω ∈ H²(G_L)`** — the 2-cocycle by
  which the de Branges `⊗↦⊕` and the cup product `∧` disagree. **`ω = 0 ⟺ G_L is Tannakian ⟺ a genuine
  motive exists ⟺ the zero-realization succeeds`**, and at operator level **`ω = 0 ⟺ D trace-class
  (F₁-regularized) ⟺ Hilbert–Pólya ⟺ RH`** (unifies 5 programs: B5 monoidality, Deninger, B8 F₁, B35
  q→1, B18 HP). Apex: the difference-Galois group `G_𝒜` **is** the Langlands group `L_ℚ` (#28; the
  Rankin–Selberg `⊗`-half is already a theorem).

## Goal
One explicit `H²` class is the **single hinge** of three otherwise-separate gates: autonomy/C7 (a
Tannakian `G_L`), a genuine motive carrying the zeros, and the zero-realization that
`carrier-herglotz-rh.md` (G5) needs. The infinite-base Galois correspondence and inverse-Galois are
**built** (#68 §43.1/§55) but flagged **likely IMPORT** under Door-2 (Etingof / classical IGP / Deligne
as proof engines); the *uncomputed* piece — and the only one that is not a reframing — is whether
`ω = 0`.

## Door passport
- **Door-3:** `ω` is a native cohomological invariant intrinsic to the simultaneity of the `σ_p` (the
  `⊗↦⊕` mismatch is a property of the joint difference structure, not a single shift).
- **Door-2:** the surrounding Tannakian machinery is likely IMPORT; **computing `ω` natively** (via the
  prime-lattice Koszul complex, not Tannakian reconstruction) is the part that could be irreducible.

## Gates
- [x] 0 → 1  in-progress: `ω` defined as the `⊗↦⊕` vs `∧` 2-cocycle; the SEED-R Koszul reading pinned; the
  finite `e–h` shadow (`eh_koszul_duality`) identified as the testable floor. **Done** + §R extends it.
- [~] 1 → 2  fully-proven: **partial** — §R **locates** `ω` (the obstruction to deciding it): the
  multiplicative Koszul part is acyclic in the `∏_p` limit, so `ω` is a **purely archimedean class**
  (SEED-R-conditional BRIDGE). Deciding `ω=0` stays Fields-Medal (`ω=0⟺RH`); the residual is the archimedean
  Koszul-homology defect of the Γ-factor/`s=1` regularization.
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
**SEED-R:** read `ω` as the **Koszul homology of the prime lattice in the `∏_p` limit** — `ω = 0 ⟺ the
∞-prime Koszul complex stays acyclic`. The finite Euler shadow `Σ_{i+j=k}(−1)^i e_i h_j = 0` is
**ledger-proven** (`EHKoszulDuality`). Decisive test: does the finite `e–h` acyclicity **survive the
renormalized `∏_{p≤P} → ∏_p` limit**? (the homological "fourth language" for the renormalization wall,
alongside ξ-outer condensation / LP-survival / explicit-formula limit). At operator level: `Γ-factor =
ζ-regularized det of D = Kurokawa absolute zeta`; `ω=0 ⟺ D is trace-class`.

## §R Result (2026-06-19, Professor) — ω is purely archimedean: the multiplicative Koszul part is acyclic
> **Prior art (standing-order check):** the *conclusion* "ω is purely archimedean" is **already in
> `support-extraction-log.md` #90 / Attack 6** (L1423): "ω = additivity of the archimedean place = missing
> Frobenius at ∞; trace defect = Γ-factor = Kurokawa absolute zeta." §R is a **new proof/mechanism** (the
> ∞-prime Koszul acyclicity `H(t)E(−t)=1` in `Λ`) for that known conclusion — **not a new discovery.**

**Setup (SEED-R).** Read `ω` as the Koszul-homology class of the prime lattice in the `∏_p` limit (#73 §6).
The multiplicative model is the λ-ring `𝓜 = ℚ[p_m] = Λ` (symmetric functions in **infinitely** many
variables; the power sums `p_m` = Adams operations are free polynomial generators, Macdonald I.2). The e–h
Koszul differential's acyclicity is the generating-function relation
```
   H(t)·E(−t) = 1   in Λ[[t]] ,      i.e.   Σ_{i+j=k} (−1)^i e_i h_j = 0   (k ≥ 1).
```

**[PROVED — unconditional algebra].** `H(t)E(−t)=1` holds in `Λ` itself — the standard relation between the
complete-homogeneous and elementary symmetric functions (Macdonald I.2), valid **in infinitely many
variables**, not merely a finite truncation. The finite Euler shadow `Σ_{i+j=k}(−1)^i e_i h_j = 0` is
ledger-proven (per the G4 bucket; `eh_koszul_duality` / `EHKoszulDuality`), and it **survives the
variable-count limit** because the identity is a formal identity in the inverse-limit ring `Λ`. Hence the
**unregularized ∞-prime Koszul complex is acyclic** (zero homology).

**[BRIDGE — SEED-R-conditional localization of ω].** Under the SEED-R reading, the multiplicative shadow of
`ω` is exactly this Koszul homology — which **vanishes**. Therefore `ω` carries **no multiplicative / Euler
content**: any nonzero `ω` is supported entirely on what the symmetric-function limit omits — the
**archimedean regularization counterterm** that turns the divergent `∏_p` into `ξ = Γ-factor × ζ`. **`ω` is
a purely archimedean class.**

**Answering the SEED-R test (#73 §6: "does finite e–h acyclicity survive the renormalized
`∏_{p≤P}→∏_p` limit?").** **Yes for the algebra, not necessarily for the analysis.** The multiplicative
(symmetric-function) acyclicity survives the limit trivially (`H(t)E(−t)=1` is exact in `Λ`); the
obstruction can only enter through the **analytic renormalization** (the archimedean counterterm), which the
algebraic limit does not see. This **splits the renormalization wall**: its multiplicative half is
Koszul-acyclic and inert; its archimedean half carries all of `ω`.

**Consequences.**
- Cohomological form of #74 ("multiplicative-only methods are apex-blind"): `ω∈H²(G_L)` is invisible to the
  Euler/Satake structure — a *proof* that the multiplicative wing cannot reach the realization obstruction.
- Places `ω` squarely in the **seam** (#71/#90): `ω` = the archimedean obstruction, the same single F₁ as
  the corank-∞ / Stieltjes face. The seam now has a **G4-cohomological face** alongside G1, G2, and the
  Stieltjes weld (`../2-fully-proven/stieltjes-log-weld.md`).
- Reduces compute-`ω` to a **purely archimedean** computation: `ω` = the Koszul-homology defect of the
  Γ-factor / `s=1` regularization, no longer entangled with the prime lattice. (Core stays Fields-Medal:
  `ω=0 ⟺ RH`.)

## Cross-references
- `koszul-acyclicity.md` — the SEED-R Koszul sharpening of `ω` (the sibling that *is* the testable form).
- `carrier-herglotz-rh.md`, `weil-positivity-operator.md` — the G5 zero-realization `ω=0` enables.
- `c7-autonomy-foundational-core.md` — `ω=0` (Tannakian `G_L`) is the cleanest autonomy witness.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — `ω` is the seam's central quantity.

## Log
- 2026-06-19 — created in 0-backlog. The G4 open core (compute `ω`), which simultaneously serves G4
  autonomy/C7, the G5 realization, the Langlands-group identity, and the seam.
- 2026-06-19 — Professor: pulled to 1-in-progress; completed the 0→1 deliverables and proved §R. The
  **unregularized ∞-prime Koszul complex is acyclic** (`H(t)E(−t)=1` in `Λ`, the e–h relation in infinitely
  many variables; finite shadow ledgered), so under SEED-R the multiplicative shadow of `ω` vanishes and
  **`ω` is a purely archimedean class** (no Euler content; cohomological form of #74). Answered the SEED-R
  renormalization-wall test: algebra survives the limit, the obstruction is purely analytic/archimedean.
  Adds a **G4-cohomological face to the seam**. Core `ω=0⟺RH` stays Fields-Medal; `ω` now reduced to the
  archimedean Γ-factor/`s=1` Koszul defect.
