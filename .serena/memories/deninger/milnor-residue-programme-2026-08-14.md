# Programme: the Milnor residue map in all degrees (serves both open Deninger cards)

Date: 2026-08-14. Card 2's arithmetic consequence 2 ("a Rost--Schmid resolution over `Spec ℤ` has
residue length one") needs the two-term Gersten complex `K_n^M(K) → ⊕_v K_{n-1}^M(κ(v))`, hence
residue maps in **all** degrees, not only the degree-two tame symbol in `MilnorKTameSymbol.lean`.
The same construction is the model for Morel's Milnor--Witt residue (card 3's Rost--Schmid
language).

## Landed (all build green, axioms `propext, Classical.choice, Quot.sound`)

- `HTGeometry/MilnorKGradedRingAssoc.lean` — `milnorDegCongr`, `milnorDegCongr_class`,
  `milnorSymbolAppend_assoc`, **`milnorMul_assoc`**, `milnorOne`, `milnorOne_mul`, `milnorMul_one`.
- `HTGeometry/MilnorKResidueData.lean` — **`ResidueData K k`** extends `TameData K k` with
  `unif`, `v_unif`, and **`oneSub_res`** (the residue of `1 - a` is `1 - res a` when both have
  valuation zero). `val'`, `unitPart`, `unitPart_mem/_mul/_of_mem_ker/_unif`, **`residueUnit`**,
  `residueUnit_mul/_unif/_of_mem_ker/_one`.
- `HTGeometry/MilnorKResidueStep.lean` — `resSymbol`, `resSymbol_mul`, `resSymbol_one`,
  **`resSymbol_neg_one_add_self`** (`{-1}+{-1} = 0`), `resSymbol_neg`, `mulSymbol`, `mulSymbol_mul`,
  **`resStepHom`** (multiplication by `[ū_a] + v(a)ξ`), **`resStepHom_mul`** (additive in `a` =
  multilinearity), **`resPair`** (the fold over a symbol).
- `HTGeometry/MilnorWittGradedAppend.lean` — vanishing words stay vanishing inside longer words.

## The remaining Steinberg computation — worked out on paper, NOT yet in Lean

Goal: `resStepHom D a (n+1) ∘ resStepHom D (oneSubUnit ha) n = 0`.
Write `α = v(a)`, `β = v(1-a)`, `A = [ā]`, `B = [b̄]`, `E = [-1]`, input `p = (x, y)`.
Step 1 gives `X = B x`, `Y = B y + (-1)^n β x + (-1)^{n+1} β (E y)`.
Step 2 gives `(A X, A Y + (-1)^{n+1} α X + (-1)^n α (E Y))`.

- **α > 0**: `oneSub_of_pos` ⟹ `β = 0` and `b̄ = 1`, so `B = [1] = 0` and `(X, Y) = 0`. Done.
- **α = 0, β > 0**: `oneSub_of_zero` ⟹ `ā = 1`, so `A = 0`; and `α = 0` kills the other two terms.
- **α = 0, β = 0**: needs `A·B = {ā}{1-ā} = 0`, the Steinberg relation **in the residue field** —
  this is exactly why `TameData` is not enough and `ResidueData.oneSub_res` was added. Note
  `b̄ = 1 - ā ≠ 0` forces `ā ≠ 1`, which is the side condition Steinberg needs.
- **α < 0**: `oneSub_of_neg` ⟹ `β = α` and `ā = -b̄`, so `A = E + B` and `A·B = {-b̄}{b̄} = 0`.
  Expanding, everything cancels **except** terms with integer coefficients `2`, `α(α+1)` or
  `α(α-1)` multiplying `E`-containing products; all of those vanish because
  `2E = 0` (`resSymbol_neg_one_add_self`) and `α(α±1)` is even. Anticommutativity `B E = -E B`
  (`milnorPairClass_anticomm`) is used to merge the two `E B y` terms.

Sanity check in degree 2 (`n = 0`, `y = 0`, `x = 1`): the composite is `α(1+α)·{-1}`, matching the
classical tame symbol `(-1)^{αβ} a^β/b^α = (-1)^{α(α+1)} = 1`.

## Then

- descend `resPair` to `∂ : K_n^M(K) → K_{n-1}^M(k)` (multilinearity + Steinberg kill the relations);
- characterizing identities `∂{π,u_2,…} = {ū_2,…}` and `∂{u_1,…} = 0`;
- a `ResidueData` constructor from a `Valuation` (extend `tameDataOfValuation`), needed to keep
  everything instantiable;
- the Gersten complex for a Dedekind domain, with finite support.

## Standing blockers (both genuinely deep, unchanged)

- Card 2: `K_2(𝒪_K)` torsion for a number field = Garland 1971 / Quillen + Borel.
- Card 3: the `∞`-categorical layer (free `E_∞`-algebras, homotopy pushouts, connective
  `t`-structures) — no mathlib counterpart; the card carries the graded-ring shadow instead.
