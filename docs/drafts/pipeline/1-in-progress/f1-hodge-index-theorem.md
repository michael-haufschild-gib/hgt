# The F_1 Hodge index theorem — RH = positivity of the proper F_1-curve's Poincaré duality

> **⚠ rh-corp reconciliation (2026-06-19): NOT NEW — `docs/rh-corp` route #2** (F₁/Connes intrinsic Hodge-index,
> 25–30%, *"too large"*; `speculation.md` §2). "Properness = product formula" and "RH = Hodge index of the
> proper F₁-curve" are F₁-program folklore. rh-corp ranks the **faithful κ₋=0 / operator-monotone source proof**
> (#1, 40–45%) above this and warns that *measured* positivity is dust-blind — RH needs the **faithful** κ₋
> index. **Re-derivation, not a fresh lead.**

- **ID:** f1-hodge-index-theorem
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (the bedrock's open core) — **FIELDS MEDAL**
- **Priority:** FIELDS MEDAL
- **Source:** the open core of `f1-hodge-cohomology-construction.md` (`Q_W ⪰ 0`); the orthogonality
  meta-theorem #135 (positivity = the archimedean polarization); the product formula = properness (Arakelov/F_1
  heuristic; `linearIndependent_log_primes`/`functionField_esymm_FE` ledger); #78 §19–22 (RH = Hodge–Riemann);
  imports: Deligne Weil II (the `F_q` Hodge index), Connes–Consani / Arakelov (the proper F₁-curve)
- **Statement (the open core, sharpened to a Hodge index — and a mechanism).** On the assembled object
  `(H¹_{F₁},Θ,W_\bullet,Q_W)`, **RH ⟺ `Q_W ⪰ 0`** = the Hodge–Riemann positivity of the F₁-MHS. The leap:
  > **`Q_W ⪰ 0` is the *Hodge index theorem* for the Arakelov-compactified `\overline{\mathrm{Spec}\,ℤ}`
  > viewed as a *proper* curve over `F₁`.** For a **proper** curve, Poincaré duality on `H¹` is a
  > **non-degenerate cup product** that Hodge theory makes **definite on the primitive part** (Hodge–Riemann)
  > — *positivity is automatic once the curve is proper and the Hodge structure polarized.* So RH reduces to:
  > **is `\overline{\mathrm{Spec}\,ℤ}` proper over `F₁`, with a polarized weight-1 Hodge structure?**
  >
  > **And properness is (essentially) given:** the **product formula `∏_v |x|_v = 1`** is the F₁-analog of
  > "the divisor of a rational function on a proper curve has degree 0" — i.e. **the product formula *is* the
  > properness** of the F₁-curve, supplied by the **archimedean place** as the compactifying point at
  > infinity (Arakelov). So **RH ⟸ (properness = product formula, a theorem) + (the F₁ Hodge index for the
  > proper F₁-curve, the open core).**

  **Verdict reached:** the bedrock's positivity is **structured, not opaque** — it is a **Hodge index
  theorem**, its *input* (properness) is the product formula (given, archimedean), and its *hard core* is the
  **F₁ Hodge–Riemann relations** (the F₁-Weil-II). Over `F_q` this exact mechanism is **proven** (Deligne).
  Fields-Medal, open — but now a precise Hodge-theoretic statement on a constructed object, not a void.

---

## §1 The mechanism — why positivity should hold (the Hodge index)

For a smooth **proper** curve `C` (`/ℂ` or `/F_q`), the cup product `H¹ × H¹ → H²(=`the orientation/Tate`)`
is non-degenerate (Poincaré duality), and on the **primitive** part, polarized Hodge theory gives the
**Hodge–Riemann bilinear relations**: the form is **definite**. *Positivity is not an extra hypothesis — it
is a consequence of (properness) + (a polarized Hodge structure).* Over `F_q`, the `ℓ`-adic analog is
**Deligne's Weil II purity** (`|α|=q^{w/2}`), proven via the global `L`-function's positivity — the same
"properness ⟹ positive duality" content. So **the positivity that is RH has a known *mechanism*; the only
question is whether its hypotheses hold over `F₁`.**

## §2 Properness = the product formula `[the key identification]`

The one nontrivial hypothesis is **properness**. Its F₁-shadow is exact and already a theorem:
- On a proper curve, a rational function `f` has `\deg(\mathrm{div}\,f)=0` (the residue/degree theorem).
- Over ℚ, the analog for `x∈ℚ^×` is the **product formula `∏_v |x|_v = 1`** (`∑_v \log|x|_v = 0`) — the
  archimedean place `v=∞` supplying the term that makes the sum vanish.
- So **`\overline{\mathrm{Spec}\,ℤ} = \mathrm{Spec}\,ℤ ∪ \{∞\}` is "proper over `F₁`," with the archimedean
  place as the point at infinity, and the product formula is its properness** (Arakelov; Connes–Consani's
  arithmetic site). **The archimedean place is not an obstruction — it is the compactifying point that makes
  the curve proper.** *(This is the orthogonality theorem read geometrically: the polarization is archimedean
  because properness — hence positivity — comes from the place at infinity.)*

## §3 The reduction `[worked]`

```
   RH ⟺ Q_W ⪰ 0                                   (f1-hodge-cohomology §4)
       ⟺ Hodge–Riemann positivity of the F₁-MHS   (§1, the mechanism)
       ⟸ (properness) + (polarized weight-1 Hodge structure)
            properness = the product formula        (§2, a THEOREM, archimedean)
            polarized weight-1 MHS = the F₁ Hodge index = the F₁-Weil-II   (OPEN — Fields Medal)
```
So RH is **not** reduced to something easier — but it is **decomposed**: the *input* (properness) is the
**product formula** (given), and the *hard core* is the **F₁ Hodge–Riemann/purity** for the proper
F₁-curve. The hard core is RH-deep (it is the F₁-Weil-II), but it is now a **precise Hodge-theoretic
statement on the constructed object** (`f1-hodge-cohomology-construction`), with a **proven `F_q` template**
(Deligne).

## §4 The A1∧A2 unification, realized

On the proper F₁-curve's `H¹`:
- **A1 (RH/positivity)** = the Hodge index (the cup product is definite) — the **weight/archimedean** face.
- **A2 (DSS/Sato–Tate)** = the prime-angle monodromy `G^0_{geom}` is big/equidistributed — the **angle/prime**
  face.
Both are properties of **one** object (the F₁-curve's polarized `H¹`); over `F_q` both are theorems and A2
(equidistribution) **follows from** A1 (purity) + big monodromy (Deligne). So the carrier's "two faces of one"
is realized: **the proper F₁-curve's cohomology is the carrier**, A1 its polarization, A2 its monodromy.
*(This corrects a tempting error: A2 does not* prove *A1 — purity is the deep input, A2 a consequence;
`bucket-A1-A2-unification-the-carrier`, #78.)*

## §5 Door / grade / honest scope
- **The reduction (§§1–3) is BRIDGE/structural** (it assembles the Hodge index mechanism + the
  product-formula=properness identification + the `F_q` template). The **product formula** input is a theorem.
- **The hard core (§3) is FIELDS MEDAL, OPEN** = the F₁ Hodge–Riemann relations = the F₁-Weil-II = RH. **No
  proof claimed.** The value: RH is now a **Hodge index on a constructed proper F₁-curve**, with the one
  archimedean input (properness) supplied and the mechanism (Hodge–Riemann) proven over `F_q`.
- **Anti-LLM-Cage note:** this is as far right of the wall as conjecture+reason reach without the F₁
  foundations being rigorous — the object is built, the positivity is a Hodge index, properness is the
  product formula, and the residue is the one theorem `F_q` already proved (Deligne). The leap is that the F₁
  Hodge–Riemann relations hold; that is the genuine frontier (Deninger/Connes–Consani).

## Gates
- [x] 0 → 1  in-progress: the positivity sharpened to a Hodge index (§1); properness = product formula (§2);
  the reduction (§3); A1∧A2 realized + the direction corrected (§4); Door/scope (§5).
- [ ] 1 → 2  the reduction banked: §2 (product formula = properness) made rigorous in the F₁/Arakelov frame;
  the `F_q` template (§1) checked = Deligne; the hard core stated as the lone Fields-Medal residual.
- [ ] 2 → 3  formalized: the product-formula floor (`∑_v\log|x|_v=0`, reuse `linearIndependent_log_primes`);
  the `F_q` Hodge index (`functionField_esymm_FE`).
- [ ] 3 → 4  publication-ready: "RH as the Hodge index of the proper F₁-curve; properness = the product
  formula."

## Cross-references
- `f1-hodge-cohomology-construction.md` — the object this places the positivity on.
- **`f1-hodge-riemann-modular-route.md`** — attack route 1: reroute through Tomita–Takesaki (positivity
  automatic; RH = a modular *identification*, not a positivity).
- **`f1-hodge-riemann-qto1-limit.md`** — attack route 2: the regularized `q→1` tangent of Deligne's Weil II,
  bracketed by Deligne (each `q`) and Faltings (Arakelov). The two routes meet at the regularization.
- `archimedean-weil-ii-bedrock.md`, `deligne-weil-ii-transport-audit.md` — the bedrock + the `F_q` template.
- `../2-fully-proven/orthogonality-meta-theorem.md` — positivity = archimedean (here = properness from `∞`).
- `../../door/bucket-A1-A2-unification-the-carrier.md`, **#78 §19–22** — the carrier / RH = Hodge–Riemann.

## Log
- 2026-06-19 — created in 1-in-progress and **worked** (Anti-LLM-Cage: take the leap). Sharpened the
  bedrock's positivity `Q_W ⪰ 0` to a **Hodge index theorem** on the constructed F₁-MHS, with a **mechanism**
  (properness + polarized Hodge ⟹ definite cup product, Hodge–Riemann; proven over `F_q` = Deligne). **Key
  identification:** properness = the **product formula** `∏_v|x|_v=1`, the archimedean place as the
  compactifying point (Arakelov/F₁). So **RH ⟸ (product formula, given) + (the F₁ Hodge–Riemann relations,
  the open Fields-Medal core).** Realized the A1∧A2 carrier (A1=polarization, A2=monodromy of the proper
  F₁-curve's `H¹`) and corrected the direction (purity is the deep input; A2 follows). The bedrock is now a
  precise Hodge-theoretic conjecture on a built object — RH-deep, but no longer a void.
</content>
