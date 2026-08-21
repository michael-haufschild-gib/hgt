/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Borel–Weil–Bott in rank one

The flag variety of `SL₂` is the projective line, whose line bundles are the Serre twists `O(d)`,
`d ∈ ℤ`.  Their cohomology is computed by the Čech complex of the standard two-chart affine cover
`{X ≠ 0}, {Y ≠ 0}`, which for the twist `O(d)` reads

`0 → (k[X,Y]_X)_d ⊕ (k[X,Y]_Y)_d → (k[X,Y]_{XY})_d → 0`.

Writing a Laurent monomial `X^a Y^{d-a}` by its exponent `a ∈ ℤ`, the degree-`d` part of
`k[X,Y]_{XY}` is `ℤ →₀ k`, the first chart contributes the functions supported in `{a ≤ d}` and the
second those supported in `{0 ≤ a}`.  Hence

`H⁰(O(d)) = supported {a ≤ d} ⊓ supported {0 ≤ a}`,
`H¹(O(d)) = (ℤ →₀ k) ⧸ (supported {a ≤ d} ⊔ supported {0 ≤ a})`,

and all higher cohomology vanishes because the complex has length one.  This file proves the
resulting **Bott dichotomy**: writing `s · d = -d - 2` for the `ρ`-shifted (dot) action of the
nontrivial Weyl element,

* `d ≥ 0` (dominant): `H⁰` has dimension `d + 1` and `H¹ = 0`;
* `d = -1` (`d + ρ` singular): all cohomology vanishes;
* `d ≤ -2`: `H⁰ = 0` and `H¹` has dimension `-d-1`, the dimension of `H⁰(O(s · d))`.

## Main results

* `finrank_bottH0`, `finrank_bottH1` — the dimensions.
* `bott_dot_action` — `dim H¹(O(d)) = dim H⁰(O(-d-2))` for every `d`.
* `bottH1_subsingleton_of_neg_one_le`, `bottH0_eq_bot_of_neg` — the vanishing statements.
* `bott_euler_characteristic` — `dim H⁰ - dim H¹ = d + 1`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Finsupp

variable (k : Type*) [Field k]

/-- Degree-`d` sections of `O(d)` over the chart `X ≠ 0`, in Laurent-exponent coordinates. -/
def cechC0 (d : ℤ) : Submodule k (ℤ →₀ k) := Finsupp.supported k k {a : ℤ | a ≤ d}

/-- Degree-`d` sections of `O(d)` over the chart `Y ≠ 0`, in Laurent-exponent coordinates. -/
def cechC1 (d : ℤ) : Submodule k (ℤ →₀ k) := Finsupp.supported k k {a : ℤ | 0 ≤ a}

/-- `H⁰(ℙ¹, O(d))`. -/
noncomputable def bottH0 (d : ℤ) : Submodule k (ℤ →₀ k) := cechC0 k d ⊓ cechC1 k d

/-- The image of the Čech coboundary, i.e. the sum of the two chart contributions. -/
noncomputable def cechImage (d : ℤ) : Submodule k (ℤ →₀ k) := cechC0 k d ⊔ cechC1 k d

/-- `H¹(ℙ¹, O(d))`. -/
abbrev bottH1 (d : ℤ) := (ℤ →₀ k) ⧸ cechImage k d

variable {k}

theorem bottH0_eq_supported (d : ℤ) :
    bottH0 k d = Finsupp.supported k k (Set.Icc (0 : ℤ) d) := by
  rw [bottH0, cechC0, cechC1, ← Finsupp.supported_inter]
  congr 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem cechImage_eq_supported (d : ℤ) :
    cechImage k d = Finsupp.supported k k ({a : ℤ | a ≤ d} ∪ {a : ℤ | 0 ≤ a}) := by
  rw [cechImage, cechC0, cechC1, Finsupp.supported_union]

theorem compl_union_eq_Ioo (d : ℤ) :
    ({a : ℤ | a ≤ d} ∪ {a : ℤ | 0 ≤ a})ᶜ = Set.Ioo d 0 := by
  ext a
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_Ioo, not_or, not_le]

theorem finrank_supported_finset (s : Finset ℤ) :
    Module.finrank k (Finsupp.supported k k (↑s : Set ℤ)) = s.card := by
  classical
  haveI : Fintype (↑s : Set ℤ) := FinsetCoe.fintype s
  rw [(Finsupp.supportedEquivFinsupp (M := k) (R := k) (↑s : Set ℤ)).finrank_eq,
    (Finsupp.linearEquivFunOnFinite k k (↑s : Set ℤ)).finrank_eq,
    Module.finrank_fintype_fun_eq_card]
  simp

/-- The dimension of `H⁰(ℙ¹, O(d))`. -/
theorem finrank_bottH0 (d : ℤ) : Module.finrank k (bottH0 k d) = (d + 1).toNat := by
  rw [bottH0_eq_supported, ← Finset.coe_Icc, finrank_supported_finset, Int.card_Icc]
  congr 1
  omega

/-- `H¹` is the quotient by a complemented submodule, hence a copy of the missing exponents. -/
noncomputable def bottH1Equiv (d : ℤ) :
    bottH1 k d ≃ₗ[k] Finsupp.supported k k (Set.Ioo d 0) := by
  refine Submodule.quotientEquivOfIsCompl _ _ ?_
  rw [cechImage_eq_supported, ← compl_union_eq_Ioo d]
  refine ⟨Finsupp.disjoint_supported_supported ?_, Finsupp.codisjoint_supported_supported ?_⟩
  · exact disjoint_compl_right
  · rw [codisjoint_iff]
    exact Set.union_compl_self _

/-- The dimension of `H¹(ℙ¹, O(d))`. -/
theorem finrank_bottH1 (d : ℤ) : Module.finrank k (bottH1 k d) = (-d - 1).toNat := by
  rw [(bottH1Equiv (k := k) d).finrank_eq, ← Finset.coe_Ioo, finrank_supported_finset,
    Int.card_Ioo]
  congr 1
  omega

/-- **The Bott dot action.**  The first cohomology of `O(d)` has the dimension of the space of
sections of `O(s · d)` where `s · d = -d - 2` is the `ρ`-shifted reflection. -/
theorem bott_dot_action (d : ℤ) :
    Module.finrank k (bottH1 k d) = Module.finrank k (bottH0 k (-d - 2)) := by
  rw [finrank_bottH1, finrank_bottH0]
  congr 1
  omega

/-- **Vanishing of `H⁰` for negative degree.** -/
theorem bottH0_eq_bot_of_neg {d : ℤ} (hd : d < 0) : bottH0 k d = ⊥ := by
  rw [bottH0_eq_supported, Set.Icc_eq_empty (by omega), Finsupp.supported_empty]

/-- **Vanishing of `H¹` for degree at least `-1`.** -/
theorem bottH1_subsingleton_of_neg_one_le {d : ℤ} (hd : -1 ≤ d) :
    Subsingleton (bottH1 k d) := by
  have htop : cechImage k d = ⊤ := by
    rw [cechImage_eq_supported, ← Finsupp.supported_univ (M := k) (R := k) (α := ℤ)]
    congr 1
    ext a
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    omega
  exact Submodule.Quotient.subsingleton_iff.mpr htop

/-- **Total vanishing at the singular weight.**  For `d = -1` both cohomology groups vanish. -/
theorem bott_singular_vanishing :
    bottH0 k (-1) = ⊥ ∧ Subsingleton (bottH1 k (-1)) :=
  ⟨bottH0_eq_bot_of_neg (by norm_num), bottH1_subsingleton_of_neg_one_le (by norm_num)⟩

/-- **Non-vanishing of `H⁰` in the dominant range.** -/
theorem finrank_bottH0_of_nonneg {d : ℤ} (hd : 0 ≤ d) :
    Module.finrank k (bottH0 k d) = (d + 1).toNat ∧ 0 < Module.finrank k (bottH0 k d) := by
  refine ⟨finrank_bottH0 d, ?_⟩
  rw [finrank_bottH0]
  omega

/-- **Non-vanishing of `H¹` below the singular weight.** -/
theorem finrank_bottH1_of_le {d : ℤ} (hd : d ≤ -2) : 0 < Module.finrank k (bottH1 k d) := by
  rw [finrank_bottH1]
  omega

/-- **Riemann–Roch for `ℙ¹`.**  The Euler characteristic of `O(d)` is `d + 1`. -/
theorem bott_euler_characteristic (d : ℤ) :
    (Module.finrank k (bottH0 k d) : ℤ) - (Module.finrank k (bottH1 k d) : ℤ) = d + 1 := by
  rw [finrank_bottH0, finrank_bottH1]
  omega

end GaloisForLFunctions.HTGeometry.BorelWeil
