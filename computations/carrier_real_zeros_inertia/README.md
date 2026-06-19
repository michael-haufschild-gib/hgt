# Stage-1 exact inertia validated on the actual ζ-zeros (+ the FE-doubling refinement)

**Theorist, 2026-06-19.** Numerical validation of the PROVEN theorem
`GaloisForLFunctions.multiPair_carrier_exact_neg_inertia` (κ₋ = #off-line conjugate pairs) against the
real Riemann ξ-zeros, via the carrier `m(z)=Σ_poles 1/(p−z)` Pick-matrix signature. numpy + mpmath
`zetazero`.

## Findings
- **RH-true** (all zeros on the line, poles `{±γ_n}` real, first 8 zeros): carrier Pick matrix is
  PSD, **κ₋ = 0** — the on-line spectrum gives a Herglotz carrier, exactly the RH face. (`output.txt`,
  `quadruple_output.txt`)
- **Off-line**: an off-line zero `z₀=γ+iδ` forces, by the functional equation `Ξ(z)=Ξ(−z)` and
  `Ξ(z̄)=conj Ξ(z)`, the **quadruple** `{γ+iδ, γ−iδ, −γ+iδ, −γ−iδ}` (so the carrier is real on ℝ).
  That quadruple is **two** conjugate pairs (Im>0 representatives `γ+iδ`, `−γ+iδ`). So
  **`κ₋ = 2·#{off-line zeros}`** — confirmed `κ₋ = 2k` for `k = 1,2,3,4` once enough nodes are placed
  near the pole heights (`realzeros3.py`). With too few / badly-placed nodes the finite signature
  under-counts (`n₋ ≤ κ₋`; equality needs nodes resolving each negative square) — itself a clean
  illustration of the finite-node resolution law.

## Reading
The proven exact-inertia theorem holds on the genuine ξ-zeros, with the **FE-doubling refinement**:
each off-line zero contributes **two** negative squares to the carrier Pick form (not one), because the
functional equation's `z↦−z` and `z↦z̄` symmetries quadruple it. Either way **RH ⟺ κ₋ = 0**. This
anchors Stage-1 on the real object and sharpens the off-line count. Numeric tier; the theorem itself is
ledger-proven.

## Repro
`python3 realzeros2.py` (FE quadruple), `python3 realzeros3.py` (nodes near pole heights ⟹ κ₋=2k exact).
