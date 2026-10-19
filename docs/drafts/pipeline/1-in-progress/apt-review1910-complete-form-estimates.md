# APT complete-form estimates and detection

- **ID:** APT-REVIEW1910-A1-A3
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME / OPEN
- **Source:** ../../../reports/review-1910/astra.md, §3
- **Statement:** Resolve A1–A3 for an explicit arithmetic family, retaining the complete signed form and the parameter costs needed to enlarge the family.

## Requirements

- [ ] **A1:** Determine the sign of the complete limiting critical prime quadratic form; obtain explicit coefficient bounds or an actual finite negative witness. Distinguish this prime channel from the prime–Gamma–polar Weil form.
- [ ] **A2:** Prove a quantitative approximation theorem for the chosen family controlling prime, Gamma, and polar errors jointly. State support, aperture, coefficient, and scale dependence; fixed-pattern convergence alone is insufficient.
- [ ] **A3:** Prove detection or a scoped failure of detection on explicit off-line configurations. Retain the diagonal budget and reflection defect. A model theorem is not a statement about all arithmetic axioms of zeta.
- [ ] Audit implications, strongest positive survivors, existing-corpus priority, and scientific significance.
- [ ] Formalize dependency-closed conclusions without additional mathematical premises or axioms; wire leaves and run direct-file Lean/axiom/lint audits.

## Established input and first open dependency

The complete translated prime limit, harmonic charge classification, common-density
formula, continuous reflected cell kernel, and exact positive weight mass already
exist. Reuse the modules named in
`apt-critical-prime-kernel-signature-2026-10-19.md`; do not repeat their construction.
That prior card is a historical paused task; the present request resumes its sign
question under the broader A1–A3 scope.

For the singleton pattern, the old analytic candidate isolates the negative charge
at harmonic two and bounds every positive harmonic plus the infinite tail. Its
finite rational bookkeeping was checked, but its harmonic estimates were not.
**[OPEN CORE A1]** Prove those estimates for the native harmonic defect, or replace
them with a sharper dependency-closed comparison. No sign premise may be imported.

**[OPEN CORE A2]** Control the complete receiving form in a joint growing regime;
the existing critical physical affine error does not control the prime form by itself.
**[OPEN CORE A3]** Match the selected family and its normalization to an explicit
off-line model and prove a negative complete-form readout or a sharp detection boundary.

## Proof and audit discipline

No numerical experiments, full/umbrella builds, heartbeat increases, commits, or
changes to concurrent work. One owned foreground Lean process at a time. Use
`lake --old env lean <actual-file>` for final audits and `/tmp` for API/axiom probes.
Persist crisp reusable facts and failures in `logs/apt-review1910-knowledge.md`.
Keep research changes in this card, owned Lean leaves, and their umbrella imports.
Persisted corpus-only instructions preclude an external novelty certification here.

## Plan

1. Audit native harmonic bounds and complete-form/detection machinery in the corpus.
2. Close a dependency-closed analytic sign argument, then formalize it.
3. Derive full-form approximation costs and test detection without discarding signed terms.
4. Audit every requirement against actual theorem statements and verification output.

## Dependency-closed small-harmonic argument

Write `a=π/6` and `γ(u)=u⁻²(1−cos(au))`. The existing singleton/common-tail
and exact-mass theorems give, for every natural `m`,
`J_m=m(π²/12−∫₀ᵐγ(u)du)`, including `m=0` directly.
The corpus's global alternating cosine inequalities give, for `u>0`,

`a²/2−a⁴u²/24+a⁶u⁴/720−a⁸u⁶/40320 ≤ γ(u)`

`γ(u) ≤ a²/2−a⁴u²/24+a⁶u⁴/720`.

The value at zero is immaterial to integration. Integrate these polynomials and
use the exact head identity. With `θ=πm/6`, the resulting bounds are

`πθ/2−θ²/2+θ⁴/72−θ⁶/3600 ≤ J_m`

`J_m ≤ πθ/2−θ²/2+θ⁴/72−θ⁶/3600+θ⁸/282240`.

Specialization to `m=2,3,5,6`, with `157/50<π<22/7`, gives respectively
`J₂≥10/9`, `J₃≤4/3`, `J₅≤4/3`, and `J₆≤7/6` by rational inequalities.
This proof uses the complete native harmonic mass; it has no Laplace-transform
premise. These four bounds are support for the pending sign argument, not a
complete sign theorem or a novelty claim.

**Lean support result:** `FactorialCriticalHarmonicTaylorBounds.lean` proves the
exact head identity, both global Taylor inequalities, and all four displayed
small-harmonic bounds. The actual file passed `lake --old env lean -j 1 -o ...
-i ... <actual-file>` and is umbrella-imported. Two redundant-tactic warnings
remain to remove before the final audit. Axiom and lint audits remain pending.

## Oscillatory tail replacement

For `p>1`, define `C_p(θ)=∫₁∞v⁻ᵖ cos(θv)dv` and
`S_p(θ)=∫₁∞v⁻ᵖ sin(θv)dv`. Absolute integrability gives
`|C_p|,|S_p|≤1/(p−1)`. Integration by parts, with vanishing boundary at infinity,
gives `θ C₂=−sin θ+2S₃` and `θ S₃=cos θ−3C₄`.
Consequently the native defect, at `θ=πm/6>0`, satisfies

`|J_m−1|≤2/θ`,

`J_m≤1+sin θ/θ+2(1−cos θ)/θ²`.

These bounds replace the unproved Laplace representation. The first gives
`J_m≤6/5` for `m≥20`, a slightly larger infinite-tail budget than the prior
candidate's `11/10`. The second retains the phase needed for harmonics
`7,9,10,11,13,14,15,17,18,19`. The final arithmetic budget must be recomputed
symbolically with `6/5`; the old margin cannot be reused unchanged.

The old tail coefficient `671/86640` is replaced by `61/7220`, using
`log19≤(13/3)log2` and `log2≥2/3`. The increase is `61/86640`.
Since `1/300−61/86640>1/390`, the proposed complete singleton budget still
has room for `Σ A(m)J_m/m⁴≤−log2/390`. This is exact rational bookkeeping,
conditional only at the planning level on the analytic estimates still being
formalized; it is not a Lean endpoint or an imported theorem premise.
