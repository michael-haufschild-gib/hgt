import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Tate cohomology of an involution, and the `ℤ/2` Herbrand quotient

For an involution `σ` of a `ℤ`-module `Λ` (i.e. an action of `ℤ/2`) the Tate cohomology groups are

* `InvolutionTate.H0 σ = ker (σ - 1) / im (σ + 1)`,
* `InvolutionTate.H1 σ = ker (σ + 1) / im (σ - 1)`.

The central computation of this file is the exact sequence

```
0 → Λ / (Λ⁺ ⊕ Λ⁻) --(σ-1)--> Λ⁻ / 2Λ⁻ → Ĥ¹(σ) → 0
```

(`InvolutionTate.card_defect_mul_card_H1`), which yields

```
#(Λ / (Λ⁺ ⊕ Λ⁻)) · #Ĥ¹(σ) = 2 ^ rank Λ⁻ .
```

Replacing `σ` by `-σ` swaps `Λ⁺ ↔ Λ⁻` and `Ĥ¹ ↔ Ĥ⁰` while leaving `Λ⁺ ⊕ Λ⁻` unchanged, so the same
formula holds with `Ĥ⁰` and `rank Λ⁺`.  Dividing the two gives the **Herbrand quotient formula**

```
#Ĥ⁰(σ) · 2 ^ rank Λ⁻ = #Ĥ¹(σ) · 2 ^ rank Λ⁺
```

(`InvolutionTate.herbrand`), and in particular `#Ĥ⁰(σ) = #Ĥ¹(σ)` whenever `Λ⁺` and `Λ⁻` have equal
rank (`InvolutionTate.card_H0_eq_card_H1`).

This is exactly the arithmetic engine behind Proposition 5.1 of Suzuki, *Duality invariance of
Faltings heights, Hodge line bundles and global periods* (arXiv:2504.04993): the number of connected
components of `A(ℝ)` for an abelian variety over `ℝ` with period lattice `Λ` and conjugation `σ` is
`#Ĥ¹(σ)`, while that of the dual abelian variety is `#Ĥ¹(-σ) = #Ĥ⁰(σ)`; equality of the two is the
final step of the proof of duality invariance of real periods.

Neither Tate cohomology nor Herbrand quotients exist in mathlib, so everything here is built from
scratch.
-/

namespace GaloisForLFunctions.HTGeometry.InvolutionTate

open LinearMap Module Submodule

variable {Λ : Type*} [AddCommGroup Λ]

/-! ### The two structural maps of an involution -/

/-- The difference map `σ - 1` of an involution. -/
def dlt (σ : Λ →ₗ[ℤ] Λ) : Λ →ₗ[ℤ] Λ := σ - LinearMap.id

/-- The norm map `σ + 1` of an involution. -/
def nrm (σ : Λ →ₗ[ℤ] Λ) : Λ →ₗ[ℤ] Λ := σ + LinearMap.id

@[simp] theorem dlt_apply (σ : Λ →ₗ[ℤ] Λ) (x : Λ) : dlt σ x = σ x - x := rfl

@[simp] theorem nrm_apply (σ : Λ →ₗ[ℤ] Λ) (x : Λ) : nrm σ x = σ x + x := rfl

/-- The `+1`-eigenlattice `Λ^{σ = 1}`. -/
def plusPart (σ : Λ →ₗ[ℤ] Λ) : Submodule ℤ Λ := ker (dlt σ)

/-- The `-1`-eigenlattice `Λ^{σ = -1}`. -/
def minusPart (σ : Λ →ₗ[ℤ] Λ) : Submodule ℤ Λ := ker (nrm σ)

theorem mem_plusPart {σ : Λ →ₗ[ℤ] Λ} {x : Λ} : x ∈ plusPart σ ↔ σ x = x := by
  simp [plusPart, LinearMap.mem_ker, sub_eq_zero]

theorem mem_minusPart {σ : Λ →ₗ[ℤ] Λ} {x : Λ} : x ∈ minusPart σ ↔ σ x = -x := by
  simp [minusPart, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

/-! ### Behaviour under `σ ↦ -σ` -/

@[simp] theorem dlt_neg (σ : Λ →ₗ[ℤ] Λ) : dlt (-σ) = -nrm σ := by
  ext x; simp [dlt, nrm]; abel

@[simp] theorem nrm_neg (σ : Λ →ₗ[ℤ] Λ) : nrm (-σ) = -dlt σ := by
  ext x; simp [dlt, nrm]; abel

@[simp] theorem plusPart_neg (σ : Λ →ₗ[ℤ] Λ) : plusPart (-σ) = minusPart σ := by
  ext x; simp [plusPart, minusPart, LinearMap.mem_ker]

@[simp] theorem minusPart_neg (σ : Λ →ₗ[ℤ] Λ) : minusPart (-σ) = plusPart σ := by
  ext x; simp [plusPart, minusPart, LinearMap.mem_ker]

@[simp] theorem range_dlt_neg (σ : Λ →ₗ[ℤ] Λ) :
    range (dlt (-σ)) = range (nrm σ) := by
  rw [dlt_neg, LinearMap.range_neg]

@[simp] theorem range_nrm_neg (σ : Λ →ₗ[ℤ] Λ) :
    range (nrm (-σ)) = range (dlt σ) := by
  rw [nrm_neg, LinearMap.range_neg]

/-! ### Tate cohomology -/

/-- Tate `Ĥ¹` of the involution `σ`: `ker (σ + 1) / im (σ - 1)`. -/
abbrev H1 (σ : Λ →ₗ[ℤ] Λ) : Type _ :=
  (minusPart σ) ⧸ comap (minusPart σ).subtype (range (dlt σ))

/-- Tate `Ĥ⁰` of the involution `σ`: `ker (σ - 1) / im (σ + 1)`. -/
abbrev H0 (σ : Λ →ₗ[ℤ] Λ) : Type _ :=
  (plusPart σ) ⧸ comap (plusPart σ).subtype (range (nrm σ))

/-- The *defect* of the eigenlattice decomposition: `Λ / (Λ⁺ ⊕ Λ⁻)`. -/
abbrev defect (σ : Λ →ₗ[ℤ] Λ) : Type _ := Λ ⧸ (plusPart σ ⊔ minusPart σ)

/-- Cardinalities of subquotients only depend on the two submodules involved. -/
theorem card_subquot_congr {P P' Y Y' : Submodule ℤ Λ} (hP : P = P') (hY : Y = Y') :
    Nat.card ((P : Type _) ⧸ comap P.subtype Y)
      = Nat.card ((P' : Type _) ⧸ comap P'.subtype Y') := by
  subst hP; subst hY; rfl

/-! ### The exact sequence `0 → Λ/(Λ⁺ ⊕ Λ⁻) → Λ⁻/2Λ⁻ → Ĥ¹ → 0` -/

variable {σ : Λ →ₗ[ℤ] Λ}

theorem range_dlt_le_minusPart (hσ : ∀ x, σ (σ x) = x) :
    range (dlt σ) ≤ minusPart σ := by
  rintro _ ⟨x, rfl⟩
  rw [mem_minusPart]
  simp only [dlt_apply, map_sub, hσ]
  abel

theorem range_nrm_le_plusPart (hσ : ∀ x, σ (σ x) = x) :
    range (nrm σ) ≤ plusPart σ := by
  rintro _ ⟨x, rfl⟩
  rw [mem_plusPart]
  simp only [nrm_apply, map_add, hσ]
  abel

/-- The submodule `2 · Λ^{σ = -1}` of `Λ^{σ = -1}`. -/
def twoMinus (σ : Λ →ₗ[ℤ] Λ) : Submodule ℤ (minusPart σ) :=
  range ((2 : ℤ) • (LinearMap.id : (minusPart σ) →ₗ[ℤ] (minusPart σ)))

theorem twoMinus_le_dltComap (σ : Λ →ₗ[ℤ] Λ) :
    twoMinus σ ≤ comap (minusPart σ).subtype (range (dlt σ)) := by
  rintro _ ⟨b, rfl⟩
  refine ⟨-(b : Λ), ?_⟩
  have hb : σ (b : Λ) = -(b : Λ) := mem_minusPart.mp b.2
  simp only [dlt_apply, map_neg, hb, Submodule.coe_subtype, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.coe_smul]
  module

/-- `σ - 1` viewed as a map into the `-1`-eigenlattice. -/
def dltCod (hσ : ∀ x, σ (σ x) = x) : Λ →ₗ[ℤ] (minusPart σ) :=
  (dlt σ).codRestrict (minusPart σ) fun x => range_dlt_le_minusPart hσ ⟨x, rfl⟩

@[simp] theorem dltCod_coe (hσ : ∀ x, σ (σ x) = x) (x : Λ) :
    ((dltCod hσ x : (minusPart σ)) : Λ) = σ x - x := rfl

/-- The connecting map `Λ → Λ⁻ / 2Λ⁻`, `x ↦ (σ - 1) x`. -/
def psi (hσ : ∀ x, σ (σ x) = x) := (twoMinus σ).mkQ ∘ₗ dltCod hσ

theorem ker_psi (hσ : ∀ x, σ (σ x) = x) :
    ker (psi hσ) = plusPart σ ⊔ minusPart σ := by
  rw [psi, LinearMap.ker_comp, Submodule.ker_mkQ]
  ext x
  simp only [Submodule.mem_comap]
  constructor
  · rintro ⟨b, hb⟩
    -- `σ x - x = 2 • b` with `b ∈ Λ⁻`; then `x = (x + b) + (-b)` splits `x`.
    have hbval : σ x - x = (2 : ℤ) • (b : Λ) := by
      have := congrArg (fun y : (minusPart σ) => (y : Λ)) hb
      simpa using this.symm
    have hbmem : σ (b : Λ) = -(b : Λ) := mem_minusPart.mp b.2
    refine Submodule.mem_sup.mpr ⟨x + (b : Λ), ?_, -(b : Λ), (minusPart σ).neg_mem b.2, by abel⟩
    rw [mem_plusPart, map_add, hbmem]
    have hx : σ x = x + (2 : ℤ) • (b : Λ) := by rw [← hbval]; abel
    rw [hx]; module
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have hamem : σ a = a := mem_plusPart.mp ha
    have hbmem : σ b = -b := mem_minusPart.mp hb
    refine ⟨-(⟨b, hb⟩ : (minusPart σ)), ?_⟩
    apply Subtype.ext
    simp only [dltCod_coe, map_add, hamem, hbmem, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_smul, Submodule.coe_neg]
    module

theorem range_psi (hσ : ∀ x, σ (σ x) = x) :
    range (psi hσ) = map (twoMinus σ).mkQ (comap (minusPart σ).subtype (range (dlt σ))) := by
  rw [psi, LinearMap.range_comp, dltCod, LinearMap.range_codRestrict]
  rfl
