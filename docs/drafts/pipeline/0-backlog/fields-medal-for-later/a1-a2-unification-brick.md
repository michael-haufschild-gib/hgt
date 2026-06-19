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

## Goal
The deepest result the program names: **"make RH and time one statement."** Both faces live on **one
germ**, so a *single* rigidity statement feeds both — any bound forcing the germ transcendentally generic
at 0 (A2) is, by analytic continuation of the same germ, a constraint on its global pole structure (A1).
The common ingredient = the **multiplicity estimate on `G_L`**. The single sentence: *the two places of
`G_L` do not conspire — neither in SIGN (A1/RH) nor in ALGEBRA (A2/DSS); both non-conspiracies are the
SAME archimedean rigidity on one computed object.*

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
`spectrum_esymm_algIndep` (A2, finite jet independence). The open core is the **infinite passage**: one
archimedean rigidity input feeding both — the Nesterenko arithmetic lower bound forcing DSS-cross [A2]
*and* the Herglotz/positivity input forcing `κ₋(m_ξ)=0` [A1]. The orthogonality
(`faces-orthogonality.md`) explains why neither face implies the other; the unification is the converse
welding via the shared germ.

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
