# Constructing the F_1-Hodge cohomology — the object (H¹_{F₁}, Frob_∞, W•, Q_W) assembled

> **⚠ rh-corp reconciliation (2026-06-19): NOT NEW — `docs/rh-corp` route #2** (F₁/Connes/intrinsic Hodge-index,
> 25–30%, *"too large"*; `speculation.md` §2). The Connes/Deninger object is adopted, not built here. rh-corp
> ranks the **faithful κ₋=0 source proof** (#1) above this. **Re-derivation, not a fresh lead.**

- **ID:** f1-hodge-cohomology-construction
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / CONSTRUCTION (the bedrock object — built, not just located)
- **Source:** the located bedrock (`archimedean-weil-ii-bedrock.md`, `deligne-weil-ii-transport-audit.md`:
  the one missing object); **#78 §19–22** (RH = Hodge–Riemann positivity of the Weil rep of `SL₂(ℝ)`,
  ledgered anchors); **#123** (G4 weight/angle split, `dim W = corank`); the completed module `M_Λ ∈ 𝓜⁺`
  (`completed-connection-category.md`, `gamma-module-construction.md`); orthogonality #135; #137 (`Q_W=𝔇`,
  certified); imports: Connes 1999 (adele class space), Deninger (regularized cohomology), Deligne (Weil II)
- **Goal (Anti-LLM-Cage: build it now).** Assemble the bedrock object the audit located —
  `(H¹_{F₁}, \mathrm{Frob}_\infty, W_\bullet, Q_W)` — from materials in hand. Three of its four parts already
  exist (the space+Frobenius from Connes/Deninger; the polarization from the certified Weil form); the **new
  construction** is the **weight/angle F₁-Hodge structure** built from the `(σ_p,∂_s)`-module. The one part
  that stays open — that `Q_W ⪰ 0` (RH) — is isolated as a **Hodge index theorem** in the companion
  (`f1-hodge-index-theorem.md`).

  > **Built here:** `H¹_{F₁}` (Connes/Deninger regularized cohomology, scaling Frobenius, spectrum = the
  > zeros) **+** a **mixed Hodge structure** whose weight filtration `W_\bullet` is the archimedean `∂_s`/Tate
  > part (**Source A**) and whose graded `\mathrm{Gr}^W` carries the prime-angle monodromy `G^0_{geom}`
  > (**Source B**) **+** the polarization `Q_W` = the FE cup product = the certified DeWitt/Weil form. **RH =
  > Hodge–Riemann positivity of `Q_W`.**

---

## §1 The space + Frobenius `[adopt: Connes/Deninger]`

- **`H¹_{F₁}` :=** the `ζ`-regularized first cohomology — concretely Connes' `L²(𝔸_ℚ/ℚ^×)_0` (the Sonine
  cokernel of the adelic cutoff), or Deninger's conjectural `H¹` with `ξ(s)=\det_\infty\!\big(\tfrac{s-Θ}{2π}\big)`.
- **`\mathrm{Frob}_\infty` :=** the scaling generator `Θ = D = x\,d/dx = ∂_s` (the archimedean clock,
  `constraint-not-flow-theorem`). **Its spectrum is the zeros `{γ}`** (Connes' absorption spectrum / Deninger's
  eigenvalues). This handles Deligne-audit steps 2/5 (the "cohomology with Frobenius" and the "finiteness")
  via **`ζ`-regularization**, not literal finite-dimensionality. *(IMPORT — the regularized framework is
  Connes/Deninger; adopted.)*

## §2 The weight/angle Hodge structure `[NEW — from the (σ,∂)-module]`

This is the part the F₁ program lacked and the session's apparatus supplies. From `M_Λ ∈ 𝓜⁺`:
- **Weight filtration `W_\bullet` = the `∂_s`-grading (Source A).** The archimedean factor `Γ_ℝ(s)=π^{-s/2}Γ(s/2)`
  is the **Hodge/Tate datum**: the `∂_s`-weight (the "infinite-Frobenius weight"). The **weight torus `W`** of
  #123 (`dim W = corank`: `1` over `F_q`, `∞` over ℚ) **is** the graded of `W_\bullet`. So the weight
  filtration is the archimedean/Tate direction — exactly where RH lives (#123: `W` carries G5/RH).
- **`\mathrm{Gr}^W` carries the prime-angle monodromy (Source B).** The `σ_p` act on the graded pieces as the
  **Frobenius angles** — the geometric monodromy `G^0_{geom}` (#123), the Satake/Sato–Tate data
  (`satake_trace_re_mem_Icc`, ledgered). So `\mathrm{Gr}^W_w` is a `G^0_{geom}`-representation: the
  prime/angle content.
- **The MHS = (weight `W_\bullet` from `∂_s`) ⋉ (angle monodromy from `σ_p`).** This realizes the two sources
  as the two axes of one Hodge structure — the **A1∧A2 carrier** (`bucket-A1-A2-unification-the-carrier`) made
  into an explicit F₁-MHS. *(NEW: the weight/angle split #123 + the `(σ,∂)`-module = the F₁-Hodge structure.)*

## §3 The polarization `[adopt + identify]`

- **Poincaré duality = the functional equation.** The pairing `H¹_{F₁} × H¹_{F₁} → H²_{F₁} = ℝ(−1)` is the
  `s↔1−s` pairing: `⟨f,g⟩ = ` the **Weil explicit-formula form** `W(f*\tilde g)`. The FE `Λ(s)=Λ(1−s)` **is**
  the Poincaré self-duality (`f ↔ \tilde f`).
- **`Q_W = 𝔇` (certified).** This cup product is the certified DeWitt/Weil quadratic form (`Q_W=𝔇`, 1.1e-31,
  #94/#137) `= H_W = −Δ_{prime}+V_{arch}` (#88 §8). So the polarization is **already in hand, numerically
  anchored**; the prime block is positive for free (`satake_trace_re_mem_Icc`), the obstruction is the single
  archimedean (weight) direction `κ₋` (#137).

## §4 The object, assembled, and what's open `[verdict]`

```
   H¹_{F₁}        = Connes/Deninger regularized cohomology            [adopt]
   Frob_∞ = Θ = ∂_s,  spec(Θ) = {γ} (the zeros)                       [adopt]
   W_•   = ∂_s-weight filtration (Source A; the weight torus #123)     [NEW]
   Gr^W  carries σ_p-angle monodromy G^0_geom (Source B; Satake)       [NEW]
   Q_W   = FE cup product = Weil form = 𝔇 (certified)                  [adopt/identify]
   RH    ⟺  Q_W ⪰ 0  ⟺  Hodge–Riemann positivity of the F₁-MHS         [OPEN — f1-hodge-index-theorem]
```
**Three of four parts are built; the fourth (the weight/angle MHS) is the new construction.** The object
exists as a candidate; **the sole open core is `Q_W ⪰ 0`** = the **F₁ Hodge index theorem** (companion card),
which is RH. So the bedrock is no longer "an undefined missing object" — it is **this assembled object, whose
positivity is the one remaining theorem.**

## §5 Consistency checks
- **`F_q` recovery (Door-5).** Over `F_q(C)`: `H¹_{F₁} ↦ H¹_{ét}(C)` (finite-dim), `Θ ↦ Frob_q`, `W_\bullet ↦`
  the weight filtration (`dim W=1`, #123), `\mathrm{Gr}^W` = the geometric monodromy, `Q_W ↦` the cup product
  / Poincaré duality. `Q_W ⪰ 0` = the Hodge index theorem on the curve = **Deligne's purity (proven)**. So the
  construction **specializes to the actual Weil-II object over `F_q`** — the strongest check that it is the
  right object.
- **`corank` consistency.** `dim W = corank`: `1` over `F_q` (one weight = one Frobenius), `∞` over ℚ (the
  missing single Frobenius). The infinite-dimensionality of `H¹_{F₁}` over ℚ = `corank ∞` = the regularization
  is genuinely needed (Deninger), matching §1.
- **`constraint-not-flow`.** `Θ` is the order-2/weight constraint generator (the FE), `ζ`-regularized — not a
  Hamiltonian. So `H¹_{F₁}` is a **constraint cohomology**, consistent with `constraint-not-flow-theorem`.

## §6 Door / grade
- **Construction grade: CONJECTURE/BRIDGE-assembly.** §§1,3 are imports (Connes/Deninger/Weil); §2 (the
  weight/angle F₁-MHS from the `(σ,∂)`-module) is the **new content**, built from #123 + `𝓜⁺`. §5 shows it is
  the right object (recovers Weil II over `F_q`).
- **The open core is open** (= RH = §4's positivity), isolated in `f1-hodge-index-theorem.md`.
- **Not claimed:** RH. Claimed: the bedrock object is **assembled and specializes correctly**, reducing the
  whole question to one positivity (a Hodge index).

## Gates
- [x] 0 → 1  in-progress: the four parts assembled (§§1–4); the new weight/angle MHS built (§2); `F_q`
  recovery + corank + constraint checks (§5); Door passport.
- [ ] 1 → 2  the construction banked: §2 (the F₁-MHS from `(σ,∂)`) verified and graded; the `F_q`
  specialization to Weil-II's object proven (Door-5); the object stated as the bedrock, positivity isolated.
- [ ] 2 → 3  formalized: reuse `satake_trace_re_mem_Icc` (`\mathrm{Gr}^W` positivity), `Q_W=𝔇` (#94),
  `dim W=corank` (#123); the weight filtration fragment.
- [ ] 3 → 4  publication-ready: "the F₁-Hodge cohomology of `ζ`: the bedrock object, assembled."

## Cross-references
- `f1-hodge-index-theorem.md` — the open core (`Q_W ⪰ 0` ⟸ monodromy maximality), the companion.
- `archimedean-weil-ii-bedrock.md`, `deligne-weil-ii-transport-audit.md` — the object this builds.
- `../../door/bucket-A1-A2-unification-the-carrier.md`, **#78 §19–22** — RH = Hodge–Riemann (the carrier).
- `#123` (G4 weight/angle), `../2-fully-proven/constraint-not-flow-theorem.md` (Θ = constraint), `#137`/`#94`
  (`Q_W=𝔇`), `weil-positivity-operator.md` (#88 §8).

## Log
- 2026-06-19 — created in 1-in-progress and **built** (Anti-LLM-Cage: construct now). Assembled the bedrock
  object `(H¹_{F₁},Θ,W_\bullet,Q_W)`: space+Frobenius from Connes/Deninger (regularized; `spec Θ={γ}`);
  **new** weight/angle **F₁-Hodge structure** from the `(σ_p,∂_s)`-module (`∂_s`=weight/Source A = the weight
  torus #123; `σ_p`=angle/Source B = `G^0_{geom}`); polarization = FE cup product = certified Weil form
  `Q_W=𝔇`. **Specializes to Weil-II's object over `F_q`** (Door-5 — Deligne's purity = the Hodge index there).
  Three of four parts adopted, one (the MHS) new. **Sole open core = `Q_W ⪰ 0` = the F₁ Hodge index = RH**,
  isolated in the companion. The bedrock object is no longer undefined — it is assembled.
</content>
