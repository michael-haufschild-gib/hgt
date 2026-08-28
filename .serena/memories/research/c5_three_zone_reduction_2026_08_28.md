# C₅ gate: three-zone reduction via Gaussian deviation form (2026-08-28)

Paper attack on the CLG/TTF rank-four open core (`C₅(u,t) ≥ 0`), entered through ∂ₜG ≤ 0 and
completed as a strictly easier direct reduction. Full note with derivations, measured margins, and
lemma ledger: `docs/drafts/pipeline/2-fully-proven/computations/2026-08-28-c5-bezoutian-tp-li-precert/dtG-attack-note.md`
(companion data `dtg_map.jsonl.gz`, `run_dtg.py`, `dev_analysis.py`; precert background in
`mem:research/numerical_precert_c5_bezoutian_tp_li_2026_08_28`).

## Core identities (verified to 1e−40)

With `q` the reflected log action, `r = e^q−1`, `α = tq₁`, `β = t²q₂`: gate ⟺
`T = 24r² − 9αr + 5rβ − 4α² − 5α²r ≥ 0`. Deviation form with `A = α−2q`, `B = β−2q`
(exact link `B = (tA)′`):

`T = F_gauss(q) + 5rB − (9r+16q+20qr)A − (4+5r)A²`, `F_gauss = 24r² − 8qr − 20q²r − 16q²`.

`F_gauss` = value of T on a pure-Gaussian fibre; all theta content is in the moduli (A, B).
Cusp: `s²`,`s³` coefficients of T vanish identically;
`T|_{s⁴} = 40κμ −16λ² −24κ²λ + (8/3)κ⁴ = 1120·Hankel/P₀²` — strictness already Lean-proved
(`thetaCuspFullSourceReflectionSecondSixthCurvature_pos`).

## Zone ledger

- **V1 (proved on paper):** `F_gauss ≥ 0`, with `F_gauss/r² ≥ (8/3)q² − q³/3 − q⁴/9` on `q ≤ 3`
  via `x = q/(e^q−1) ≤ 1 − q/2 + q²/12` (Bernoulli bound; alternating tail on `q < 2π`).
- **L1 far zone `q ≥ 3`:** 24r² dominates via polynomial L-envelopes (α ≤ 2r alone is NOT enough).
- **L3 cusp `q ≤ q₀`:** quantitative t⁸-Taylor remainder + uniform Hankel lower bound on compacts.
  Independent |A|,|B| caps CANNOT work here (the two 2026-08-28 no-gos) — only the fourth-order
  modulus comparison decides.
- **L4 bulk `q ∈ [q₀,3]`, `u ≤ u₀` — the one substantive new lemma:**
  `Ψ := (9r+16q+20qr)A + (4+5r)A² − 5rB ≤ (1−δ)F_gauss`. Measured `T/F_gauss ≥ 0.689` on the whole
  window (min at u=0, t≈0.073, q≈0.10). Route: explicit first-atom action rational enclosure +
  tilted-Laplace likelihood jet caps (`ThetaCuspAtomLikelihoodCrossDomination` style) **extended to
  the difference chamber t > u** (needed only to jet order 2). The 08-28 no-go profile violates C₅
  at q≈1.18 = exactly an L4 failure — L4 is the theta-vs-generic discriminator.
- **L5 large center `u ≥ u₀`, `q ≤ 3`:** atom domination ⟹ moduli ≤ ε(u₀)q² ⟹ Gaussian comparison.

## Numerical facts recorded

∂ₜG ≤ 0 at all 36,300 points (monotone criticality — true but NOT needed; needs third-jet control,
skip it). Riccati margin `2q₁q₂ − q₃ ≥ 0` also held on all of `t > u` (Lean has only `t ≤ u`;
cheap extension available). Moduli sizes on `q ≤ 2`: `|A| ≤ 0.068q²`, `|B| ≤ 0.340q²`, maxima at
u=0; moduli → 0 as u → ∞ (Gaussian limit).

**Next Lean steps in order:** (1) V1; (2) L1; (3) difference-chamber likelihood caps to order 2;
(4) L4 atom enclosure on the compact box; (5) L3 remainder engineering. Do NOT restart jet-sign or
Riccati-axiom approaches — no-go'd.
