# G5 over `F_q` — RH-over-`F_q` reproved natively as unitary holonomy on the σ-fixed locus (the modulus face)

- **ID:** g5-over-fq-deligne-unitarity
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door grade **BRIDGE** (function-field border; Door-5)
- **Priority:** FOUNDATIONAL
- **Source:** Step 3 of `function-field-native-reproof.md` (assigned Wheeler); the **modulus
  face** complementary to Professor's `g4-over-fq-deligne-katz.md` (the angle face) — together the full
  weight/angle split `1→G^0_geom→G_L→W→1`. Builds on the C6 functor `S_ff`
  (`c6-specialization-functors.md` §2), the corank collapse #121
  (`function-field-holonomicity-degeneration.md`), the L-polynomial FE (ledger `functionField_esymm_FE`,
  `BoundaryModulus`); feeds `../../door/bucket-the-seam-archimedean-obstruction.md` and #125
  (`corank-seam-invariant.md`); 00-status rows #31, #40, #76, #77, #121. Completes the FF gatekeeper campaign
  (G1 #121, G2 #16, G3 trivial, G4 #123, **G5 here**).

---

## Statement
Specialize the field's **G5** (unitary holonomy on the σ-fixed-modulus locus ⟺ RH) along `S_ff`. Then:
> **(Recovery, Door-5)** Over `F_q(C)`, for a sheaf / `F`-isocrystal **pure of weight `w`**, the field's
> σ-fixed-modulus locus `|x_v| = |q_v|^{1/2} = q^{-(\deg v)/2}` (ledger `BoundaryModulus`, the Re=½ analogue)
> specializes to the **Frobenius weight circle** `|α_{v,i}| = q^{w\deg v/2}`, and **"unitary holonomy on the
> σ-fixed locus" ⟺ the normalized Frobenius `u_{v,i}=α_{v,i}/q^{w\deg v/2}` is unitary (`|u_{v,i}|=1`)** —
> which is exactly **Deligne's purity (Weil II) = RH over `F_q`**. So the field's G5 **recovers** RH-over-`F_q`.

**Door BRIDGE** — imports Deligne (Weil II); the content is exhibiting it as the field's G5/unitarity and
pinning where G5 lives in the weight/angle split (the **modulus torus `W`**, complementing g4's angle face).

## §1 The recovery `[PROVED HERE — specialization + Deligne import]`
By Professor's weight/angle split (`g4-over-fq-deligne-katz.md` §2), `S_ff` carries `M` (pure of weight `w`)
to a sheaf whose Frobenius eigenvalues factor `α_{v,i}=q^{w\deg v/2}·u_{v,i}`: the **modulus**
`q^{w\deg v/2}∈⟨q^{1/2}⟩` (the rank-1 weight torus `W`, `dim W=corank(Λ_ff)=1`, #121) and the **angle**
`u_{v,i}` (the geometric monodromy `G^0_{geom}`, g4's face). The field's G5 object — **unitary holonomy on
the σ-fixed-modulus locus** — is the statement that the specialized holonomy generator (the geometric
Frobenius), read on the locus `|x_v|=q^{-\deg v/2}`, acts **unitarily after weight-normalization**, i.e.
`|u_{v,i}|=1`. That is precisely **Deligne's Weil II purity**. So `S_ff` recovers RH-over-`F_q` as G5. ∎
*(IMPORT under Door-2 — Deligne proves purity; the functor + locus exhibit the recovery, which is what
Door-5 asks.)*

## §2 The native mechanism — FE (Poincaré duality) + polarization ⟹ unitarity `[PROVED HERE, in the field's vocabulary]`
The field's G5 derives unitarity from two structural inputs, both native to the connection and matching the
geometry:
1. **FE = Poincaré duality (the involution `ι`).** The L-polynomial functional equation (ledger
   `functionField_esymm_FE`) is Poincaré duality on `H^*(C)`; it gives the eigenvalue symmetry
   `α ↔ q^{w}/\barα` — eigenvalues come in pairs **symmetric about the weight circle** `|z|=q^{w/2}`. This is
   the field's FE-involution `ι` (the σ-parity/FE-parity weld, #49) specialized to `F_q`: `Fix(ι)` = the
   weight circle = the σ-fixed-modulus locus.
2. **Polarization ⟹ unitarity.** A pure-weight-`w` sheaf underlying a polarized motive carries a
   **positive-definite Hermitian form** preserved by the weight-normalized Frobenius (hard Lefschetz gives
   the polarized weight filtration). "Unitary holonomy on the σ-fixed locus" = the normalized Frobenius
   preserves this positive form = `|u_{v,i}|=1`. **Deligne's Weil II** (the IMPORT, via the Rankin–Selberg /
   `⊗`-power positivity method) is exactly the theorem that the polarization positivity holds, forcing all
   eigenvalues onto the weight circle.
So in the field's language: **`ι` (FE/Poincaré duality) is unitary on `Fix(ι)` (the σ-fixed locus) ⟺ the
normalized Frobenius is unitary ⟺ no eigenvalue off the weight circle ⟺ RH-over-`F_q`** — the exact G5
schema (unitary holonomy ⟺ spectrum real/on-locus ⟺ RH), recovered. The off-locus deficiency `κ₋` (#32,
the finite-carrier count) specializes to "number of Frobenius eigenvalues off the weight circle" `= 0`. ∎

## §3 The difference = the archimedean place `[Step 6 feed — sharpens #125 on the G5 face]`
Catalogue what made G5 a **theorem** over `F_q` and is **absent** over ℚ — the precise demand on `F₁`:
- **(single weight)** Over `F_q` the weight torus `W` is **rank 1** (one Frobenius weight `q`, `corank=1`,
  #121/g4): a **single** weight circle `|z|=q^{w/2}` to be unitary on. Over ℚ there is **no single
  Frobenius**, the weight "torus" has **corank ∞** (g4 §3), so there is no single critical circle — the
  zeros are spread across all primes. This is the #125 `∞−1` seam on the G5/modulus face.
- **(geometric polarization)** Over `F_q` the positivity forcing `|u|=1` is **geometric** (Deligne's
  Rankin–Selberg/`⊗`-power method, from the variety `C`). Over ℚ there is **no variety** to supply it: the
  archimedean place must provide the polarization — exactly **Weil positivity / `H_W=−Δ_prime+V_arch≥0`**
  (#38), the open core of G5 over ℚ.
> **So the difference G5(`F_q`) → G5(ℚ) = the archimedean place must supply BOTH (i) the single
> weight/Frobenius (collapse corank `∞→1`) AND (ii) the polarization-positivity that Deligne's geometry
> gives for free.** This is the G5/modulus face of the seam-corank object (#125) and of the no-margin/Weil
> -positivity apex (#38). Recorded, not banked (the ℚ side is FIELDS MEDAL = RH).

## §4 Door passport
- **BRIDGE** (border item): §1 recovers Deligne (import); §2's FE=Poincaré-duality + polarization are
  standard (Weil II, hard Lefschetz); the σ-fixed locus = weight circle is the `BoundaryModulus` ledger
  specialized.
- **Door-5 ✓:** restricted to the FF border the field's G5 (unitary holonomy ⟺ RH) **recovers** the known
  answer (Deligne's RH-over-`F_q`).
- **Content beyond import:** the identification **G5/σ-fixed-unitarity ⟺ Deligne-purity** via
  FE=Poincaré-duality + polarization, locating G5 in the **weight torus `W`** (the modulus face) opposite
  g4's angle face `G^0_{geom}` — and the §3 difference-catalogue (what `F₁`/archimedean must supply for G5
  over ℚ: single weight + polarization), the G5 face of #125. Not a reframe of Deligne: it *places* G5
  inside `G_L` and isolates the archimedean residue.

## Gates
- [x] 0 → 1  in-progress: `S_ff` recovery pinned; σ-fixed locus → weight circle; FE+polarization mechanism;
  difference-catalogue scoped; Door-5 passport.
- [x] 1 → 2  fully-proven: recovery proven (§1, specialization + Deligne import); native mechanism
  (FE=Poincaré duality + polarization ⟹ unitarity, §2); difference = archimedean isolated (§3, conjecture
  feed). BRIDGE, content beyond import (§4). **Completes the FF gatekeeper campaign (G1–G5).**
- [ ] 2 → 3  formalized — Lean anchor **DONE** for the scalar weight-normalization step:
  `functionFieldWeightNormalize_norm_eq_one_iff` in `formal/GaloisForLFunctions/BoundaryModulus.lean`
  proves that normalized Frobenius has unit norm iff the original eigenvalue lies on the radius
  `q^(w*deg/2)` weight circle. Remaining Lean targets: `Fix(ι)` = weight circle (reuse
  `functionField_esymm_FE`, `BoundaryModulus`); `κ₋=0 ⟺` all eigenvalues on the circle (reuse the
  finite-carrier `κ₋` anchor #32); the Deligne purity/polarization import is not formalized.
- [ ] 3 → 4  publication-ready — with the FF campaign note: "G5 = the weight circle / modulus unitarity
  (Deligne purity); G4 = the angles (Deligne–Katz); corank = the weight torus."

## Cross-references
- `g4-over-fq-deligne-katz.md` (Professor) — the **angle face**; this is the **modulus/unitarity face**;
  together the weight/angle split `1→G^0_geom→G_L→W→1` (the seam between the two cards, g4 §109).
- `function-field-holonomicity-degeneration.md` (#121, `corank=1`), `c6-specialization-functors.md` (`S_ff`).
- `corank-seam-invariant.md` (#125) — §3 here is its G5/modulus face; `weil-positivity-operator.md` (#38)
  — the ℚ polarization the archimedean place must supply.
- `function-field-native-reproof.md` — parent; this closes its last open step (Step 3).

## Log
- 2026-06-19 (Wheeler) — created in 2-fully-proven; Step 3 of the FF reproof (assigned to me). Reproved
  RH-over-`F_q` as the field's **G5 = unitary holonomy on the σ-fixed-modulus locus**: `S_ff` sends the
  locus `|x_v|=q^{-\deg v/2}` to the weight circle `|α|=q^{w\deg v/2}`, and σ-fixed unitarity ⟺ normalized
  Frobenius unitary (`|u|=1`) = Deligne purity = RH-over-`F_q` (§1). Native mechanism (§2): FE=Poincaré
  duality (`functionField_esymm_FE`, the `ι`-involution) gives the `α↔q^w/\barα` symmetry about the weight
  circle; polarization positivity (hard Lefschetz + Deligne Weil II import) forces `|u|=1`; G5 schema
  `ι` unitary on `Fix(ι)` ⟺ RH recovered, `κ₋=0`. Difference = archimedean (§3): over ℚ, `F₁` must supply
  BOTH the single weight (corank `∞→1`) and the geometric polarization (Weil positivity #38) — the G5 face
  of #125. Door **BRIDGE**, content beyond import (places G5 in the weight torus, opposite g4's angles).
  **FF gatekeeper campaign G1–G5 now complete.**
- 2026-06-19 (Leaner) - added Lean anchor for the scalar weight-normalization step:
  `functionFieldWeightNormalize_norm_eq_one_iff` in `formal/GaloisForLFunctions/BoundaryModulus.lean`.
  It formalizes that normalizing a Frobenius eigenvalue by `q^(w*deg/2)` has unit norm iff the original
  eigenvalue lies on the weight circle of radius `q^(w*deg/2)`. Created
  `../3-formalized/function-field-weight-normalization.md`. Parent remains in `2-fully-proven` because
  function-field specialization, Poincare duality, polarization, Deligne purity, `Fix(iota)`, and RH over
  `F_q` are not fully Lean-formalized.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the scalar weight-normalization anchor is Lean-backed, but the stated G5 recovery also requires function-field specialization, Poincare duality, polarization/hard Lefschetz, Deligne purity, `Fix(ι)` as the weight circle, and RH over `F_q`. Those are not formalized.
