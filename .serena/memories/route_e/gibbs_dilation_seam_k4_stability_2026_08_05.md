# Cycle 4: dilation seam + homotopy reduction + k=4 stability (2026-08-05)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-4 section).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsDilationSeam.lean` (wired, built, clean).

## Established
- O1 (Lean): P_S(z,·) = ∏_{p∈S}(1+z·dilate p) applied to e^{−·}; dilate semigroup
  M_pM_q = M_{pq}; T0 = factor peeling (`gibbsDiag_insert_dilate`);
  `integral_dilate_sq`: ∫(f(px))² = p⁻¹∫f² — the p^{−1/2} law.
- O2 (paper): Mellin diagonalizes {M_p} with symbol p^{−s} on Re s = 1/2 — the seam IS
  the critical line, unconditionally. FLAG: the z=−1 L²-approximation reading is
  Nyman–Beurling-adjacent (known re-encoding class); the new content is the z-deformation.
- O3 (paper): all-k stability ⟸ (anchor at one x) + (no imaginary-axis zeros ∀x).
  Anchor: LARGE x ⟹ Kurtz dominance c_j² > 4c_{j−1}c_{j+1} (from p_{j+1}+1/p_j > 2)
  ⟹ real-rooted: Lee–Yang reality RESTORED at strong coupling — the gas has a reality
  phase transition in x (weak-coupling vortex ↔ strong-coupling reality).
  Axis nonvanishing ∀x = the Routh–Hurwitz minor chain for the gas.
- O4 (paper, NEW technique): k=4 minor A₁A₂A₃ > A₀A₃² + A₁²A₄ for ALL x by ENERGY
  INJECTION: map each RHS index to a strictly-lighter LHS index (uniform in x since
  u<v ⟹ e^{−xu} > e^{−xv}); A₀A₃²: (T,T') ↦ (min T, T∖min, T'), drop
  (t₁−1)(t₂t₃−1) > 0, range {a < min P}; A₁²A₄: (a,a') ↦ (a, {a',b}, S∖{b}),
  b := min(S∖{a'}), drop ⟺ a' < ∏(S∖b), range {min P = min S ≤ a}; ranges disjoint,
  both injective (b = pair∖triple). ⟹ 4-element gas Hurwitz-stable at every coupling.
  The injection technique is the engine candidate for the whole minor chain (all k).

## Queued Lean
Quartic Routh–Hurwitz criterion (s+it elimination; R(s=0) = −Δ₃; needs the full
negativity argument — classical, heavier than cubic); the O4 injection (32 term
comparisons, ordered p<q<r<s); Kurtz's dominance theorem (c_j² > 4c_{j−1}c_{j+1} ⟹
real-rooted) — check literature form (Kurtz 1992) and corpus interlacing assets first.

## Lean traps
- `integral_comp_mul_left` lives at `MeasureTheory.Measure.integral_comp_mul_left`
  (inside namespace Measure!), value |a⁻¹| • ∫.
