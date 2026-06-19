# The archimedean×prime cross-term — where the weld lives, and the first candidate native quantity (the C5 entry)

- **ID:** archimedean-prime-cross-term
- **Stage:** 0-backlog
- **Type:** CONJECTURE / COMPUTATION (the research entry point to the C5 weld)
- **Priority:** FIELDS MEDAL
- **Source:** the Hölder-recentering — the C5 keystone is the **weld** (charter §5; `door-C5` "Second carrier
  dimension"); builds on `gamma-module-construction.md` (`M_∞`), `completed-connection-category.md` (`M_Λ`);
  connects to the Weil form `H_W=−Δ_prime+V_arch` (`weil-positivity-operator.md`, #88 §8); 00-status rows
  #38, #39
- **Statement (to shape).** The native frontier is the **archimedean×prime weld** — the irreducible
  interaction of Source A (`M_∞`, polynomial multiplier) and Source B (`M_ζ`, constant multipliers) on the
  completed `M_Λ = M_∞ ⊗ M_ζ`. **Honest first question:** on the base, `[∂_s, σ_p] = 0` (they commute), so
  the interaction is **not** an operator commutator — it lives in the **completion**:
  > the joint `(σ_p, ∂_s)`-connection on the *tensor* `M_Λ` (where `∂_s` acts diagonally on **both** factors
  > while `σ_p` acts only on `M_ζ`), and the **functional equation** `Λ(s)=Λ(1−s)` — a symmetry that
  > **neither factor has alone** (`Γ_ℝ(s)≠Γ_ℝ(1−s)`, `ζ(s)≠ζ(1−s)`; only the product is symmetric).
  *Conjecture:* the first candidate **native (C5) quantity** is the **FE-conspiracy cocycle** — the
  obstruction to factoring the `s↦1−s` symmetry across the two factors — and it is irreducibly joint
  (reachable from neither Source A nor Source B alone).

  **One sentence:** since the operators commute, the weld is not in `[∂_s,σ_p]` but in the *completion* — the
  tensor `M_∞⊗M_ζ` and the FE that only the product satisfies; that "only-the-product" is the native object.

## Why this is the C5 entry (and how it differs from the existing C5 cards)
The existing C5 carriers are **prime×prime** (combination modes `m_pδ_p+m_qδ_q`: `combination-mode-baker`,
`finite-free`, `cross-prime-curvature`). This card is the **archimedean×prime** carrier — the *other*,
arguably more fundamental, cross-direction the Hölder-recentering exposed, because it couples the two
genuinely different **multiplier types**. It is the concrete computation that turns "the keystone is the
weld" (charter §5) into an attackable object.

## Concrete first steps (the actual research)
1. **Locate the interaction.** Confirm `[∂_s,σ_p]=0` on `R⁺`, then compute the joint connection on
   `M_Λ=M_∞⊗M_ζ`: `∇_s = ∇_s^{M_∞} ⊗ 1 + 1 ⊗ ∇_s^{M_ζ}` against the `σ_p` (which act only on the second
   factor). Identify the cross-block — the part of the integrability/`F`-data coupling the `Γ`-direction to
   the prime directions.
2. **The FE-conspiracy cocycle.** Make precise the obstruction to factoring `ι:s↦1−s` as `ι_∞⊗ι_ζ`:
   `ι` is a symmetry of `M_Λ` but not of either factor. Compute this cocycle; conjecture it **is** the
   native C5 quantity (it uses both lanes irreducibly). Relate to the monoidality class `ω` (the
   non-factoring = `ω≠0`, seam) and to the vision's "non-conspiracy of the two sources" (§3).
3. **The analytic shadow.** Connect to the **Weil explicit formula / `H_W=−Δ_prime+V_arch`** (#88 §8): the
   explicit formula is literally `Σ_zeros = (prime term) + (archimedean Γ term)`; the cross-term here is the
   algebraic/Galois source of that archimedean–prime coupling, and RH (`H_W⪰0`) is its positivity. Check the
   module cross-term reproduces the Weil-form coupling.
4. **Door-2 the result.** Does the FE-conspiracy cocycle use `σ_p` **and** `∂_s` irreducibly (no single
   parent)? If yes — the first **NATIVE/C5** candidate of the reorientation. If it reduces to one lane,
   record honestly.

## Door passport
- **Door-2/4:** the weld is the native zone by construction (charter §3, revised Door-4); the cocycle is the
  candidate native quantity. The grade is the deliverable.
- **Door-5:** over `F_q` no `M_∞` ⟹ no tensor cross-block ⟹ the FE is the bare L-polynomial symmetry (Weil),
  no conspiracy ⟹ the weld is **number-field-only** (consistent with corank ∞ vs 1, and with the seam).

## Gates
- [ ] 0 → 1  in-progress: `[∂_s,σ_p]=0` confirmed; the interaction located in `M_Λ`'s tensor connection +
  the FE; the FE-conspiracy cocycle defined; links to `ω` and `H_W` stated; Door passport
- [ ] 1 → 2  fully-proven: the cross-block / FE-cocycle computed; its Door-2 grade decided (native vs
  reduces-to-a-lane); the Weil-form shadow checked; `F_q` degeneration
- [ ] 2 → 3  formalized: Lean — the tensor-connection cross-block on a finite model; reuse `M_∞`/`M_ζ`
  fragments and the Weil-form ledger anchors (`Q_W`, `BoundaryModulus`)
- [ ] 3 → 4  publication-ready: "the archimedean–prime weld: the functional equation as the irreducible
  cross-term of the two hypertranscendence sources"

## Notes / risk
- **No RH claim.** The card builds and grades the *object*; RH (the weld's positivity) is G5.
- The honest crux is step 1–2: because the operators commute, the native content must be in the completion
  (tensor + FE). If the cocycle factors after all, the weld is less native than hoped — that negative is
  itself informative (it would push C5 back toward the prime×prime carriers).

## Cross-references
- `gamma-module-construction.md` (`M_∞`), `completed-connection-category.md` (`M_Λ`, FE=flatness) — inputs.
- `weil-positivity-operator.md` (#88 §8), `../../door/bucket-the-seam-archimedean-obstruction.md` (`ω`) — the
  analytic/obstruction shadows of this cross-term. **Coordinate; do not duplicate.**
- `../../door/door-C5-irreducibility-and-door-2-retest.md` ("Second carrier dimension") — this is that
  carrier's concrete object; the prime×prime carriers (`combination-mode-baker`, `finite-free`) are siblings.

## Log
- 2026-06-19 — created in 0-backlog as the **C5 research entry** of the reorientation. Honest first finding:
  `[∂_s,σ_p]=0`, so the weld is not the operator commutator but the **completion** — the tensor `M_∞⊗M_ζ`
  and the FE that only the product satisfies. Candidate native quantity = the **FE-conspiracy cocycle**
  (the obstruction to factoring `s↦1−s` across the two sources). First step = compute the tensor
  cross-block and define the cocycle; Door-2 it.
</content>
