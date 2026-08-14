# Route T fixed-contour moment Littlewood bridge

- **ID:** route-t-fixed-contour-moment-littlewood
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route T C62 / Ingham open core
- **Statement:** A single zero-free-boundary rectangle, weighted by `z ↦ z-c`, gives the exact
  analytic-multiplicity-weighted horizontal zero mass required by Littlewood's lemma; no family of
  moving vertical contours and no distinct-abscissa encoding is needed.

## Goal

Close the first analytic identity in the Ingham/Hoheisel bridge with the actual entire zeta residue
unit.  The output must retain analytic multiplicity, permit interior zeros, and have an
unconditional selected-contour corollary.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, named module build green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone statement, proof, Lean certificate, and Route T use

## Claim ledger

### C1 — existing moving-edge assembly instantiates the zeta zero packet `[FALSIFIED] [CORPUS]`

`RectIntegralEdges.littlewood_from_edges` uses a `Finset ℝ` of abscissae.  It cannot represent
analytic multiplicity or two distinct zeros with the same real part.  More seriously,
`BoxFubini.integral_left_edge_eq_logPair` assumes `f ≠ 0` at every point of the closed box.  For the
function whose interior zeros are being counted, that premise forces the zero packet to be empty.
Thus these two theorems do not compose into Littlewood's lemma for zeta with interior zeros.

This is a corpus defect/representation mismatch, not a disproof of Littlewood's classical lemma.

### C2 — fixed-contour moment principle `[PROVED HERE] [FORMALIZED] [CLASSICAL CORE] [CORPUS-NOVEL SYNTHESIS]`

Let `f` be analytic near a positively oriented rectangle with zero-free boundary, and let `Z` be
its finite interior zero packet with analytic multiplicities `m(w)`.  For every analytic weight
`g`,

```text
Im ∮ g(z) f'(z)/f(z) dz = 2π Re Σ_{w∈Z} m(w) g(w).
```

For `g(z)=z-c`, this is

```text
2π Σ_{w∈Z} m(w) (Re(w)-c)
  = Im ∮ (z-c) f'(z)/f(z) dz.
```

This follows directly from the weighted argument principle already formalized in
`ZetaResidueUnitRectanglePeeling.lean` and `RectIntegralEdges.im_rectIntegral`.  It retains both
multiplicity and coincident abscissae.  The identity is classical; the fixed-contour replacement
for the unusable moving-edge corpus path is new internal synthesis.  No external novelty is
claimed.

### C3 — branch-free Littlewood boundary reduction `[PROVED HERE] [FORMALIZED] [CLASSICAL]`

Write the rectangle as `[c,d] × [T₁,T₂]`, put `L_a(t)=log|f(a+it)|`, and
`q=f'/f`.  Boundary nonvanishing gives

```text
d/dt L_a(t) = -Im q(a+it),
d/dx log|f(x+iT)| = Re q(x+iT).
```

Expanding C2 edge by edge and integrating `t L'_a(t)` by parts cancels all four endpoint terms
against the unweighted horizontal real-part integrals.  The exact result is

```text
2π Σ m(w)(Re(w)-c)
 = ∫[T₁,T₂] log|f(c+it)| dt - ∫[T₁,T₂] log|f(d+it)| dt
   + (d-c) ∫[T₁,T₂] Re q(d+it) dt
   + ∫[c,d] (x-c) Im q(x+iT₁) dx
   - ∫[c,d] (x-c) Im q(x+iT₂) dx.
```

No branch of complex logarithm and no interior nonvanishing premise occurs.

### C4 — unconditional zeta selected-contour corollary `[PROVED HERE] [FORMALIZED] [CORPUS]`

Apply C2/C3 to `f=zetaResidueUnit`, its exact closed-rectangle zero packet, and the contour selected
by `exists_zetaResidueUnit_zeroFreeBoundary_rectangle`.  The conclusion quantifies only the input
box ranges and returns `c,d,T` plus the exact multiplicity-weighted identity; it has no boundary
avoidance premise.

## Hostile audit

- Interior zeros are allowed; only four boundary edges are nonzero.
- Multiplicity is `(analyticOrderAt zetaResidueUnit w).toNat` and stays inside the sum.
- Distinct zeros with equal real part remain distinct `Finset ℂ` entries.
- Selected contours avoid all four edges by finite avoidance; no generic-height assumption survives
  in C4.
- C2/C3 alone do not prove Ingham density.  Remaining debt after them is quantitative control of
  the right and horizontal boundary terms, followed by Gabriel/fourth-moment input.
- External novelty: unchecked for the exact formal packaging; underlying analytic identity is
  classical and must not be advertised as a new theorem of analytic number theory.

## Approach

1. Prove a generic real-moment edge identity from a weighted rectangle-integral value.
2. Instantiate it with the exact zeta residue-unit weighted argument principle.
3. Prove vertical log-modulus differentiation and integration by parts.
4. Assemble the branch-free boundary formula and the unconditional selected-contour zeta theorem.
5. Audit axioms and wire the module into `RHTower.lean`.

## Lean certificate

- `RHTower/WeightedLittlewoodRectangle.lean`
  - `two_pi_mul_weighted_re_sum_eq_edges`
  - `hasDerivAt_log_norm_vertical`
  - `integral_id_mul_neg_im_logDeriv_vertical`
  - `weighted_littlewood_from_rectIntegral`
- `RHTower/Sieve/ZetaResidueUnitWeightedLittlewood.lean`
  - `zetaResidueUnit_weighted_littlewood_rectangle`
  - `two_pi_mul_zetaLittlewoodZeroMass_eq_boundary`
  - `exists_zetaLittlewoodZeroMass_eq_boundary`
- Named module build: `8797/8797`.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Formal lint: pass.
- Both modules are imported by `RHTower.lean`.

## Log

- 2026-08-14 — C1 falsified by direct theorem-signature audit.  C2–C4 opened as the fixed-contour
  pivot.  This removes the false belief that existing `BoxFubini` closes Littlewood for a box
  containing zeros.
- 2026-08-14 — C2–C4 paper-proved and formalized.  Fixed-contour weight `z-c` retains analytic
  multiplicity and coincident abscissae, vertical `log‖f‖` integration by parts cancels endpoint
  terms exactly, and finite avoidance discharges every zeta boundary premise.  Remaining Ingham
  debt is quantitative boundary control, not zero bookkeeping or Littlewood assembly.
