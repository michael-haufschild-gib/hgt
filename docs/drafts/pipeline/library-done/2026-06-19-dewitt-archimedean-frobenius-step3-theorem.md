# Library-backlog ticket — door/status update (DeWitt, 2026-06-19)

**For:** librarian (apply to `door/00-status.md` and `door/00-index.md`; do not let me edit directly to avoid races).

**What changed (factual):** On `pipeline/1-in-progress/moonshot-2pi-monodromy-frobenius.md` (the archimedean
one-sided Frobenius / F₁ lane, #27/#71), **Step 3 was upgraded from a mechanism to a theorem**:

- **Index obstruction (theorem).** The archimedean factor is the inverse ζ-det of the number operator
  `N=a†a` on `ℓ²(ℕ)` (from the verified grounding `Γ(a)·det_ζ(N+a)=√2π`). Its shift `S=a†` is an
  isometry of **`index S = −1 ≠ 0`**, so by Wold it has no unitary completion on its own space ⟹
  **no archimedean Frobenius *automorphism*, only the one-sided isometry** = the precise proven content
  of "F₁ is missing". Grade: Source-A archimedean ⟹ **BRIDGE/substrate** (Door-2), the F₁/seam/ω
  program / D-axis keystone-dual — not a C5 weld.
- **FE-balance order parameter (certified).** `Δ(s)=log|Γ_ℝ(s)/Γ_ℝ(1−s)|` is odd under `σ↦1−σ`,
  `=0` exactly on `Re s=½` (dps=40, `t∈{1,10,50}`), strictly monotone in `|σ−½|` off-line; the two
  ladder ground states `s/2,(1−s)/2` coincide iff `s=½`; on the line `|R|=1` (pure phase). Reading:
  **balanced unitary ⟺ critical line; one-sided isometry ⟺ off-line** — the #275 decoupling as the two
  boundary conditions of one Γ-ladder, fused by the FE at `s=½`.
  Archive: `computations/2026-06-19-archimedean-frobenius-bilateral-balance.{py,txt}`.

**Suggested status edits:**
- In the **G4 row** / **#27 / #71 / #70 (missing-Frobenius/F₁)** entries and the
  `bucket-the-seam-archimedean-obstruction` / `bucket-archimedean-generator` lines: note that the
  archimedean `F₁` now has a **proven index-obstruction core** (`index S=−1`, no automorphism) plus the
  FE-balance certificate, with the remaining open core being **Step 2: `index S=−1 ↔ ω∈H²(G_L)`** via
  Toeplitz/Bott transgression (`ω=c₁=index`). Keep the apex FIELDS-MEDAL; this is a BRIDGE/substrate
  sharpening of the F₁ object, not a C5 or an RH implication (RH stays decoupled, #191).
- The dead `2πiℤ` sub-route remains dead; this is its live one-sided-ladder successor (already noted in
  index row for #206/#347).

**Not for status (chat-only):** announced as result id=357 in #hgt.
