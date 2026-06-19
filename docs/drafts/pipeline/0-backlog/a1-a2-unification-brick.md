# The A1/A2 unification brick — one object, two readings (the single rigidity)

- **ID:** a1-a2-unification-brick
- **Stage:** 0-backlog
- **Type:** CONJECTURE (native) — the program's deepest target
- **Priority:** FIELDS MEDAL
- **Source:** ../../door/bucket-A1-A2-unification-the-carrier.md (#76, #92, #82/#83, #69/#72) · 00-status rows #51, #52, #53, #55, #56, #57
- **Statement:** RH (A1) and DSS (A2) are **two readings of ONE object**. Write the unified-conjecture
  brick and identify the **single rigidity statement** — the **multiplicity estimate on `G_L`** — that
  forces both faces at once. The one object has four equivalent presentations:
  - **carrier germ `m_ξ = −Ξ′/Ξ = Σ_{k≥0} P_{k+1} z^k`:** A1 = global type (Herglotz / `κ₋=0`); A2 =
    infinite jet at 0 (`{P_k}` alg. independent). (#76)
  - **boundary representation of `G_L` (the ridgeline, G20):** A1 = **unitary** (zeros on `|w|=1`); A2 =
    **faithful** (angles `{θ_ρ}` ℚ-independent, dense). **The no-margin = the signature of
    faithfulness** (no spectral gap). (#92)
  - **period matrix `Π = [p^{iγ_n}]` (G18):** A1 = **pure** of weight ½ (Deligne purity, FE = the
    polarization); A2 = **period-full** (`trdeg(Π) = dim G_L`, GPC for Π). (#82/#83)
  - **secular point `(P_k)` (G10):** A1 = in the Li-cone (`λ_n ≥ 0`); A2 = transcendentally generic. (#69/#72)

## ⚠️ Decoupling correction (2026-06-19, DeWitt — propagating `omega-rh-coupling-vs-orthogonality`)
The banked decoupling (`../2-fully-proven/omega-rh-coupling-vs-orthogonality.md`, verdict **(II)**) **refutes
the strong form** of this card's central claim. Specifically:
- **REFUTED:** "a **single** rigidity (the multiplicity estimate on `G_L`) forces **both** faces" and "both
  non-conspiracies are the **SAME** archimedean rigidity." The multiplicity estimate on `G_L` is a
  **transcendence-side** datum; it forces **A2 (DSS)** but **not** A1 (RH). RH = the **faithful `κ₋=0`
  polarization positivity**, an archimedean datum **distinct** from the multiplicity/orbit structure
  (#137/#148; the F_q calibration: realization ≠ polarization-positivity). So `ω=0`/DSS ⇏ RH.
- **SURVIVES (the honest unification):** the two faces still live on the **one germ `m_ξ` at the one
  archimedean place** — but they are forced by **TWO DISTINCT archimedean rigidities**, not one:
  > A2/DSS ⟸ the multiplicity estimate on `G_L` (transcendence); A1/RH ⟸ `κ₋(m_ξ)=0` (the polarization
  > positivity). **Neither forces the other** (faces-orthogonality #54, now banked via the decoupling).
- So the slogan weakens from *"one rigidity forces both"* to **"one germ, two readings, two distinct
  archimedean inputs"** — the unification is the **shared archimedean LOCUS (the seam / the place at `∞`)**,
  not a shared rigidity. The card stays the **FIELDS-MEDAL apex**, but the apex is now **two** apexes
  (DSS, RH) co-located on `m_ξ`, not one. (Each "A1=…; A2=…" presentation below is correct as a *reading*;
  it is the *forcing* that is two-input, not one.)

## Goal
The deepest result the program names: **"make RH and time one statement."** Both faces live on **one
germ** `m_ξ` at the **one archimedean place** — that co-location is the surviving unification. **But (per the
correction above) the forcing is two-input, not one:** a bound forcing the germ transcendentally generic at 0
(A2/DSS) is supplied by the **multiplicity estimate on `G_L`**; the pole/sign structure (A1/RH) is supplied
**separately** by the polarization positivity `κ₋(m_ξ)=0`. The honest single sentence: *the two places of
`G_L` do not conspire — neither in SIGN (A1/RH) nor in ALGEBRA (A2/DSS); both non-conspiracies are
**archimedean and co-located on `m_ξ`**, but they are **two distinct rigidities**, neither implying the other
(the decoupling).*

## Door passport
- **Door-1:** the object is the boundary representation of `G_L` / the carrier germ — native.
- **Door-3:** uses `G_L` and the difference-trdeg jointly (the multiplicity estimate is on `G_L`).
- **Door-4:** the obstruction is **archimedean** (the seam) — the native zone where the single place at
  infinity governs both faces.

## Gates
- [ ] 0 → 1  in-progress: the unified brick written (the four presentations as one conjecture); the
  single rigidity (multiplicity estimate on `G_L`) stated precisely as what forces both faces
- [ ] 1 → 2  fully-proven: the single rigidity proven (forces `κ₋=0` [A1] **and** DSS-cross [A2]) — the apex
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
Both **finite** layers are already ledgered: `multiPair_carrier_exact_neg_inertia` (A1, `κ₋` exact) and
`spectrum_esymm_algIndep` (A2, finite jet independence). The open core is the **infinite passage**: **two
distinct** archimedean inputs (per the correction above), co-located on `m_ξ` — the Nesterenko arithmetic
lower bound forcing DSS-cross [A2] *and*, **separately**, the Herglotz/positivity input forcing `κ₋(m_ξ)=0`
[A1]. The orthogonality (`faces-orthogonality.md`) — now banked via the decoupling — explains why neither
face implies the other; the unification is the **shared archimedean locus** (`m_ξ` at `∞`), **not** a
converse welding (the decoupling refutes a single rigidity forcing both).

## Cross-references
- `carrier-herglotz-rh.md` — the A1 face (`m_ξ` Herglotz) made concrete.
- `g2-dss-lower-bound.md` — the A2 face (DSS-cross / faithful).
- `faces-orthogonality.md` — why the two faces are independent (the dual of this unification).
- `no-margin-uniform-bound.md` — the no-margin = faithfulness is the unification's hinge.
- `realization-problem.md` — the unification stated as existence-of-`g`.
- `../../door/bucket-the-seam-archimedean-obstruction.md` — both faces = one archimedean non-conspiracy.

## Log
- 2026-06-19 — created in 0-backlog. The unified-conjecture brick (one object, two readings) + the single
  rigidity statement, the bucket-A1-A2 work package and the program's deepest target.
- 2026-06-19 (DeWitt) — **propagated the ω/RH decoupling** (`../2-fully-proven/omega-rh-coupling-vs-orthogonality.md`).
  Added the ⚠️ Decoupling correction: the strong claim ("a SINGLE rigidity / the SAME archimedean rigidity
  forces both faces") is **REFUTED**; the multiplicity estimate forces A2/DSS but not A1/RH (= κ₋=0 polarization
  positivity, a distinct archimedean datum, #137/#148). Surviving unification (weak form): **one germ m_ξ at
  the one archimedean place, two distinct archimedean rigidities, neither forcing the other.** Reconciled the
  Goal + Approach. Card stays 0-backlog (FIELDS-MEDAL apex — now two co-located apexes, not one). Coherence
  fix, not an apex resolution. No web, no runpod.
