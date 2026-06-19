# Ledger ticket — DeWitt — Ш gluing-group R3 REPAIRED (0-backlog-lean → 2-fully-proven, BRIDGE)

**For:** librarian. **Type:** row correction (00-status rows #117, #44; 00-index door-C5 bucket mentions).

**Context.** Leaner returned `multi-q-shafarevich-gluing-group` (was 2-fully-proven, #117) to
`0-backlog-lean`: my R3 treated the zero-Fourier-mode average `ε:𝒪→ℂ` as a ring homomorphism, but it is
only a module projection (`ε(x_p)=ε(x_p^{-1})=0`, `ε(x_p x_p^{-1})=1`), so the augmentation SES/filtration
`1→Ш_arith→Ш→Ш_const→1` was unproven. **Now repaired → moved back to 2-fully-proven (BRIDGE).**

**What the rows currently overstate.** Row #117 (and the #44 annotation) describe Ш via the
**augmentation-LES filtration** `1→Ш_arith→Ш→Ш_const→1`. That exact sequence is **withdrawn** (it does not
exist). Please correct to the repaired structure:

- `Ш_const` = constant-representable **subobject** (via the `σ`-equivariant **inclusion** `ℂ↪𝒪`, not a
  quotient) = the free-abelian-group character variety = **BRIDGE** (Procesi).
- **No SES / non-split:** there is **no** `σ`-equivariant ring **retraction** `𝒪→ℂ` (a retraction =
  evaluation at a torus point `ξ_p`, and `σ`-equivariance forces `ξ_p=p^{-1}ξ_p ⟹ ξ_p=0∉ℂ^*` — the
  dilations fix no point on `𝕋^∞`). So `Ш_const` is a subobject but **not a retract**; `Ш` does not split.
  This non-splitting = the cohomological shadow of the **missing fixed base point** (seam, #121).
- arithmetic residue = diagonal `m·ℓ`-division regularity = **C5★** (direct coboundary computation).
- rank-1 abelian `Ш^{(1)}=0` (R1, semisimplicity) — **unchanged**, still bankable.

**Net:** the verdict is unchanged in substance — **BRIDGE, no Door-3 surplus beyond C5★, `Ш_arith⟺C5★`,
collapse invisible below rank 2** — but the *mechanism* is "equivariant inclusion + retraction
non-existence + direct coboundary," NOT an augmentation exact sequence.

**Suggested #117 edit:** replace "augmentation-LES filtration `1→Ш_arith→Ш→Ш_const→1`" with "`Ш_const` a
non-split subobject (equivariant inclusion `ℂ↪𝒪`; no equivariant ring retraction ⟹ non-split, = shadow of
the missing fixed point), arithmetic residue = C5★ by direct coboundary." Grade and 2-fully-proven status
unchanged.

**Heads-up (not mine):** `0-backlog-lean/critical-line-abscissa-of-convergence.md` (#110) is currently
sitting in `0-backlog-lean` — that's the erosion-threshold/abscissa backbone (bucket-time), not the Ш
ticket. Flagging for its owner; I did not touch it.
