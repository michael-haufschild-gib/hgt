# OWU: the pole-density law and the dilation ray at short scales

- **ID:** owu-pole-density-law-and-short-scales
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + loop ledger on the three OWU targets (β = 0 source, positive pole
  weights, the ray inequality)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU; successors of
  `3-formalized/owu-dilation-ray-criterion-2026-10-16.md` and
  `3-formalized/owu-odd-window-closed-at-one-2026-10-16.md`
- **Statements:**
  1. (pole-density law) odd Weil positivity at pole weight `β ≥ 0` forces the Abel density of the
     weights at `s = 1` to be at least `β`: for every `ε > 0` there is `σ₀ > 0` with
     `β − ε ≤ σ Σ_{n≥2} lam(n) n^{−1−σ}` for `0 < σ < σ₀` (`abel_density_ge_of_weilPositiveOddAt`).
     Hence weights with vanishing Abel density, in particular weights with `Σ|lam(n)|/n < ∞` and the
     tempered prime weights `c log p/√p`, are not odd Weil-positive at any positive pole weight
     (`not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero`, `not_weilPositiveOddAt_of_pos_of_summable_div`,
     `not_weilPositiveOddAt_temperedWeight`).
  2. (short scales) for every weight `lam` and every `0 < T ≤ 1/9`,
     `Re W_lam(φ_T ⋆ φ̃_T) ≥ 0` (`weilFullFunctional_dilate_nonneg_of_le_ninth`): the autocorrelation
     of the dilate is blind (support in `[−4T, 4T] ⊂ (−log 2, log 2)`) and the corpus's unconditional
     window positivity on `(0, 4/9)` applies to the translate `φ_T(· − 2T)`.

## Structural content

The three targets of the loop were: (1) close the pole-free source `λ(p) = c log p/√p`, (2) decide
whether density-`β` sources without critical zeros exist, (3) the ray inequality `W_Λ(φ_T) ≥ 0`.

- Target 2, provable half: a source at pole weight `β > 0` must have Abel density `≥ β` (this
  card), and `≤ 1` (corpus ceiling); the tempered candidates of target 1 are confined to pole weight
  `≤ 0` by a theorem, not a heuristic. Any density-positive source is a mean-`β` Dirichlet series
  whose boundary real part on the critical line is dominated by the archimedean density.
- Target 3, proven range: the ray inequality holds unconditionally for `T ≤ 1/9`, for every weight;
  it is open exactly where the nodes enter (`4T ≥ log 2` needs `T ≥ 0.173`; between `1/9` and
  `log 2/4` it is the window programme's remaining gap `4/9 → log 2`).

Lean modules (wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
`OddSectorPoleDensityLaw.lean` (namespace `RHTower.OddSector`: `farLaplace_ge`,
`abel_density_ge_of_weilPositiveOddAt`, `not_weilPositiveOddAt_of_pos_of_tendsto_abel_zero`,
`abs_mul_oddDirichlet_le`, `not_weilPositiveOddAt_of_pos_of_summable_div`, `temperedWeight`,
`summable_temperedWeight_div`, `not_weilPositiveOddAt_temperedWeight`) and
`WeilDilationRayShortScales.lean` (namespace `RHTower.OddResolvent`: `shiftedDilate`,
`weilTest_shiftedDilate`, `dilate_eq_zero_of_lt`, `weilFullFunctional_dilate_nonneg_of_le_ninth`).

## Paper proofs
1. The far-bump Laplace bound of the pole-weight cap reads
   `βJ² − 2σ(2βJ² + A₀)/(1+2σ) ≤ K(σ)·σF(σ)` with `K(σ) = ∫ k(u)e^{(½+σ)u}du` for the far kernel
   `k` (supported in `|u| ≤ 1/6`), so `e^{−σ/6}J² ≤ K(σ) ≤ e^{σ/6}J²`. If `σF(σ) < β − ε` then
   `K(σ)σF(σ) < K(σ)(β − ε)`, bounded by `(1 + σ/3)J²(β−ε)` when `β ≥ ε` and by `(1 − σ/6)J²(β−ε)`
   otherwise; with `σ(2(2βJ² + |A₀|) + J²(β+ε) + 1) ≤ εJ²` both cases give `εJ² < εJ²`.
2. `|σF(σ)| ≤ σΣ|lam(n)|/n` since `n^{1+σ} ≥ n`; the tempered weights have
   `|c| log p/(√p·p) ≤ 4|c| p^{−5/4}` by `log x ≤ 4x^{1/4}`.
3. For `T ≤ 1/9`, `k_T(±log n) = 0` for all `n ≥ 2` (`4T < log 2`), so the functional is the
   archimedean part of the translate, and the window theorem applies with `L = 4T ≤ 4/9`.

## Conjecture ledger (this loop)
1. Target 1 (β = 0 tempered source): odd positivity of `λ_c(p) = c log p/√p` at pole weight `0`
   is, by Parseval against the boundary values of `P₁(1+iτ) = Σ_p log p·p^{−1−iτ}`, the pointwise
   inequality `2c Re P₁(1+iτ) ≤ w(τ)` for `τ ≠ 0` (the boundary atom `πδ₀` of `Re P₁` is the
   `r = 0` atom that odd tests cannot see and even tests do see, consistent with the even-sector
   uniqueness theorems: no tempered weight is even-positive at `β = 0`). Modulated tempered weights
   `(1 + ε cos(τ₁ log p))` are excluded: they put poles of `D` on the critical line at `±τ₁ ≠ 0`
   with positive residue, i.e. negative atoms of the odd Nevanlinna measure. Only slowly varying
   profiles in `log p` remain, and the inequality is tight at the crossing `τ ≈ 6.3` of the
   archimedean density; its truth there is a numerical question (no computation allowed), so the
   tempered `β = 0` source is not closed. It cannot be promoted to any `β > 0` (this card).
2. Target 2: sub-critical cones satisfy `C_β ⊇ βC_1 + (1−β)C_0`; under RH the segment
   `(1−ε)Λ + ε λ_temp` lies in `C_{1−ε}`. The dichotomy conjecture (every density-positive source
   is `Λ`-like, i.e. carries the critical zeros) is supported by the lattice-resonance obstruction
   on the line and by this card's density law, but its no-fake half is open (it contains Q*).
3. Target 3: `W_Λ(φ_T) ≥ 0` is proven for `T ≤ 1/9` (every weight); for `T > 1/9` it is the
   smoothed square-root prime number theorem at scale `e^{4T}` with the archimedean correction,
   i.e. RH (Wall 1); under failure of RH the off-line quadruple terms `4Re[φ̂_T(γ₀ − iδ)²]`
   dominate and oscillate in `T`, so the ray detects every off-line zero.

## Validation
- `lake --old env lean` on both modules: no output. `lake build --old`: built.
- Axiom audit (scratch, removed): four theorems, standard axioms. Lint: only other agents'
  unwired modules. Umbrella imports appended; scratch cleaned.

## Log
- 2026-10-16 — created; two Lean modules compiled, audited, wired; moved to 3-formalized
