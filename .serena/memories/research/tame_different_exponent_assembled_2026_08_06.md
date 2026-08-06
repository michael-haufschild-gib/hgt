# THE TAME DIFFERENT EXPONENT — assembled (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **50**.
Closes the arc begun at module 36.  Continues
[[research/minpoly_degree_uniformizer_2026_08_06]].

## `DifferentExponentTame.lean`

**`differentIdeal_eq_span_pow`** — for `A → B` a finite extension of DVRs with

- `addVal B (algebraMap A B πA) = e` (ramification index),
- trivial residue extension (`∀ b, ∃ a, addVal B (b − algebraMap a) ≠ 0`),
- `algebraMap πA ∣ x^e` for a uniformizer `x`,
- `e` invertible at the place (tameness),
- a monic degree-`e` relation (supplied by the charpoly, module 42),

    differentIdeal A B = Ideal.span {x ^ (e − 1)}

## Arc summary (modules 36–50)

36 monic shape freed · 37 coefficient bound derived · 38 root ⇒ uniformizer · 39 strict-min
principle · 40 Eisenstein criterion (no completeness) · 41 different from a monogenic presentation ·
42 monic relation from Cayley–Hamilton · 43 digit expansion · 44 monogenicity (Nakayama) ·
45 conductor = ⊤ · 46 fraction-field transport · 47 different = span of the derivative ·
48 power basis + `finrank = e` · 49 `natDegree minpoly = e` · **50 assembly**.

**Nothing in the chain assumes completeness, monogenicity, Eisenstein-ness, or the rank.**  All are
derived from: finite extension of DVRs, trivial residue extension, tameness.

## Significance for the card

This is the `e − 1` of the ramification order law (8) — the Jacobian contribution of tame
ramification — now proved from the *definition of the different*, not posited.  Combined with the
scheme-level horizon theorem (module 20) and the toric certificate (29), the card's Theorem A rests
on: the eigenvolume condition (Step 1, module 34), this different computation, and Step 4's
`e > 1`.

## Remaining for Theorem A

1. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
2. Step 4's `e > 1`: `N¹` + int-amplification (shown unavoidable in module 35).
3. Corollary B: MMP.
