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
    have hb' := congrArg (Subtype.val) hb
    simp only [LinearMap.smul_apply, LinearMap.id_apply, SetLike.val_smul, dltCod_coe] at hb'
    have hbval : σ x - x = (2 : ℤ) • (b : Λ) := hb'.symm
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
    rw [dltCod_coe]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, SetLike.val_smul, Submodule.coe_neg,
      map_add, hamem, hbmem]
    module

theorem range_psi (hσ : ∀ x, σ (σ x) = x) :
    range (psi hσ) = map (twoMinus σ).mkQ (comap (minusPart σ).subtype (range (dlt σ))) := by
  rw [psi, LinearMap.range_comp, dltCod, LinearMap.range_codRestrict]

/-! ### The index of `n · M` in a finite free `ℤ`-module -/

/-- For a finite free `ℤ`-module `M` and `n ≠ 0`, the quotient `M / nM` has `|n| ^ rank M`
elements.  (mathlib has the determinant formula for the index of a full-rank sublattice, but not
this special case.) -/
theorem card_quotient_range_intSMul_id {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] {n : ℤ} (hn : n ≠ 0) :
    Nat.card (M ⧸ range (n • (LinearMap.id : M →ₗ[ℤ] M))) = n.natAbs ^ finrank ℤ M := by
  set f : M →ₗ[ℤ] M := n • (LinearMap.id : M →ₗ[ℤ] M) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    exact smul_right_injective M hn (by simpa [hf] using hab)
  let e : M ≃+ (range f) :=
    AddEquiv.ofBijective (f.rangeRestrict.toAddMonoidHom)
      ⟨fun a b h => hinj (congrArg Subtype.val h), f.surjective_rangeRestrict⟩
  have key := Submodule.natAbs_det_equiv (range f) e
  have hcomp :
      (range f).subtype ∘ₗ (AddMonoidHom.toIntLinearMap (e : M →+ (range f))) = f := by
    ext x; rfl
  rw [hcomp, hf, LinearMap.det_smul, LinearMap.det_id, mul_one, Int.natAbs_pow] at key
  exact key.symm

/-! ### The index formula -/

variable [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- **The defect–Tate index formula.**  For an involution `σ` of a finite free `ℤ`-module `Λ`,
```
#(Λ / (Λ⁺ ⊕ Λ⁻)) · #Ĥ¹(σ) = 2 ^ rank Λ⁻ .
```
This is the exact sequence `0 → Λ/(Λ⁺ ⊕ Λ⁻) → Λ⁻/2Λ⁻ → Ĥ¹(σ) → 0` in cardinality form. -/
theorem card_defect_mul_card_H1 (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (defect σ) * Nat.card (H1 σ) = 2 ^ finrank ℤ (minusPart σ) := by
  have htower :=
    Submodule.card_quotient_mul_card_quotient
      (comap (minusPart σ).subtype (range (dlt σ))) (twoMinus σ) (twoMinus_le_dltComap σ)
  have hdef : Nat.card (defect σ)
      = Nat.card (map (twoMinus σ).mkQ (comap (minusPart σ).subtype (range (dlt σ)))) := by
    have hker : (Λ ⧸ ker (psi hσ)) ≃ₗ[ℤ] (range (psi hσ)) := LinearMap.quotKerEquivRange _
    rw [ker_psi hσ] at hker
    rw [← range_psi hσ]
    exact Nat.card_congr hker.toEquiv
  have htwo : Nat.card ((minusPart σ) ⧸ twoMinus σ) = 2 ^ finrank ℤ (minusPart σ) :=
    card_quotient_range_intSMul_id (by norm_num)
  rw [hdef, htower, htwo]

/-! ### The `σ ↦ -σ` symmetry and the Herbrand quotient -/

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
theorem involutive_neg (hσ : ∀ x, σ (σ x) = x) : ∀ x, (-σ) ((-σ) x) = x := by
  intro x; simp [hσ]

/-- The same index formula for `Ĥ⁰`, obtained by replacing `σ` with `-σ`. -/
theorem card_defect_mul_card_H0 (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (defect σ) * Nat.card (H0 σ) = 2 ^ finrank ℤ (plusPart σ) := by
  have h := card_defect_mul_card_H1 (σ := -σ) (involutive_neg hσ)
  have hsup : plusPart (-σ) ⊔ minusPart (-σ) = plusPart σ ⊔ minusPart σ := by
    rw [plusPart_neg, minusPart_neg, sup_comm]
  have hdef : Nat.card (defect (-σ)) = Nat.card (defect σ) :=
    Nat.card_congr (Submodule.quotEquivOfEq _ _ hsup).toEquiv
  have hh : Nat.card (H1 (-σ)) = Nat.card (H0 σ) :=
    card_subquot_congr (minusPart_neg σ) (range_dlt_neg σ)
  have hr : finrank ℤ (minusPart (-σ)) = finrank ℤ (plusPart σ) := by rw [minusPart_neg]
  rw [hdef, hh, hr] at h
  exact h

/-- **The `ℤ/2` Herbrand quotient formula.**  For every involution `σ` of a finite free
`ℤ`-module `Λ`,
```
#Ĥ⁰(σ) · 2 ^ rank Λ⁻ = #Ĥ¹(σ) · 2 ^ rank Λ⁺ ,
```
i.e. the Herbrand quotient `#Ĥ⁰ / #Ĥ¹` equals `2 ^ (rank Λ⁺ - rank Λ⁻)`.  No hypothesis beyond
`σ ∘ σ = id` is needed. -/
theorem herbrand (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (H0 σ) * 2 ^ finrank ℤ (minusPart σ)
      = Nat.card (H1 σ) * 2 ^ finrank ℤ (plusPart σ) := by
  rw [← card_defect_mul_card_H1 hσ, ← card_defect_mul_card_H0 hσ]
  ring

/-- Both Tate cohomology groups are finite. -/
theorem card_H1_ne_zero (hσ : ∀ x, σ (σ x) = x) : Nat.card (H1 σ) ≠ 0 := by
  intro h
  have := card_defect_mul_card_H1 hσ
  rw [h, mul_zero] at this
  exact absurd this.symm (by positivity)

theorem card_H0_ne_zero (hσ : ∀ x, σ (σ x) = x) : Nat.card (H0 σ) ≠ 0 := by
  intro h
  have := card_defect_mul_card_H0 hσ
  rw [h, mul_zero] at this
  exact absurd this.symm (by positivity)

theorem card_defect_ne_zero (hσ : ∀ x, σ (σ x) = x) : Nat.card (defect σ) ≠ 0 := by
  intro h
  have := card_defect_mul_card_H1 hσ
  rw [h, zero_mul] at this
  exact absurd this.symm (by positivity)

theorem finite_H1 (hσ : ∀ x, σ (σ x) = x) : Finite (H1 σ) :=
  Nat.finite_of_card_ne_zero (card_H1_ne_zero hσ)

theorem finite_H0 (hσ : ∀ x, σ (σ x) = x) : Finite (H0 σ) :=
  Nat.finite_of_card_ne_zero (card_H0_ne_zero hσ)

theorem finite_defect (hσ : ∀ x, σ (σ x) = x) : Finite (defect σ) :=
  Nat.finite_of_card_ne_zero (card_defect_ne_zero hσ)

/-- **Equal Tate cohomology in the balanced case.**  If the two eigenlattices of the involution
have the same rank, then `Ĥ⁰(σ)` and `Ĥ¹(σ)` have the same (finite) cardinality. -/
theorem card_H0_eq_card_H1 (hσ : ∀ x, σ (σ x) = x)
    (hrank : finrank ℤ (plusPart σ) = finrank ℤ (minusPart σ)) :
    Nat.card (H0 σ) = Nat.card (H1 σ) := by
  have h := herbrand hσ
  rw [hrank] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

/-! ### Ranks of the two eigenlattices -/

omit [Module.Free ℤ Λ] [Module.Finite ℤ Λ] in
/-- The two eigenlattices of an involution meet only in `0` (there is no `2`-torsion). -/
theorem disjoint_plusPart_minusPart [Module.IsTorsionFree ℤ Λ] :
    Disjoint (plusPart σ) (minusPart σ) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have h1 : σ x = x := mem_plusPart.mp hx
  have h2 : σ x = -x := mem_minusPart.mp hx'
  have hx0 : x = -x := h1.symm.trans h2
  have h3 : (2 : ℤ) • x = 0 := by
    rw [two_smul, ← sub_neg_eq_add, ← hx0, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- Ranks of two disjoint submodules add up to the rank of their sum. -/
theorem finrank_add_finrank_of_disjoint {P Q : Submodule ℤ Λ} (h : Disjoint P Q) :
    finrank ℤ P + finrank ℤ Q = finrank ℤ (P ⊔ Q : Submodule ℤ Λ) := by
  set f := LinearMap.coprod P.subtype Q.subtype with hf
  have hker : LinearMap.ker f = ⊥ := by
    rw [hf, LinearMap.ker_coprod_of_disjoint_range, Submodule.ker_subtype, Submodule.ker_subtype]
    · simp
    · rwa [Submodule.range_subtype, Submodule.range_subtype]
  have hrange : LinearMap.range f = P ⊔ Q := by
    rw [hf, LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype]
  have e : (↥P × ↥Q) ≃ₗ[ℤ] (P ⊔ Q : Submodule ℤ Λ) :=
    (Submodule.quotEquivOfEqBot _ hker).symm ≪≫ₗ (LinearMap.quotKerEquivRange f) ≪≫ₗ
      (LinearEquiv.ofEq _ _ hrange)
  rw [← Module.finrank_prod (R := ℤ) (M := ↥P) (M' := ↥Q)]
  exact e.finrank_eq

/-- **Rank additivity for an involution.**  The `+1`- and `-1`-eigenlattices of an involution of a
finite free `ℤ`-module have ranks adding up to the rank of the whole module. -/
theorem finrank_plusPart_add_finrank_minusPart (hσ : ∀ x, σ (σ x) = x) :
    finrank ℤ (plusPart σ) + finrank ℤ (minusPart σ) = finrank ℤ Λ := by
  rw [finrank_add_finrank_of_disjoint (disjoint_plusPart_minusPart)]
  exact (Submodule.finiteQuotient_iff _).mp (finite_defect hσ)

/-- With rank additivity, the balanced hypothesis of `card_H0_eq_card_H1` becomes the statement
that the fixed lattice has half the total rank. -/
theorem card_H0_eq_card_H1_of_two_mul (hσ : ∀ x, σ (σ x) = x)
    (h : 2 * finrank ℤ (plusPart σ) = finrank ℤ Λ) :
    Nat.card (H0 σ) = Nat.card (H1 σ) := by
  refine card_H0_eq_card_H1 hσ ?_
  have := finrank_plusPart_add_finrank_minusPart hσ
  omega

/-! ### A balanced model

The hypotheses of `card_H0_eq_card_H1` and `card_H0_eq_card_H1_of_two_mul` are not vacuous: the
involution `(a, b) ↦ (a, -b)` of `ℤ × ℤ` realises them. -/

/-- The model involution `(a, b) ↦ (a, -b)` of `ℤ × ℤ`. -/
def modelInvolution : (ℤ × ℤ) →ₗ[ℤ] (ℤ × ℤ) :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).prodMap (-LinearMap.id : ℤ →ₗ[ℤ] ℤ)

theorem modelInvolution_apply (p : ℤ × ℤ) : modelInvolution p = (p.1, -p.2) := rfl

theorem modelInvolution_involutive : ∀ p, modelInvolution (modelInvolution p) = p := by
  intro p; simp [modelInvolution_apply]

theorem plusPart_modelInvolution :
    plusPart modelInvolution = LinearMap.range (LinearMap.inl ℤ ℤ ℤ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨-, h2⟩ := Prod.ext_iff.mp (mem_plusPart.mp hp)
    simp only [modelInvolution_apply] at h2
    refine ⟨p.1, Prod.ext rfl ?_⟩
    simp only [LinearMap.coe_inl]
    omega
  · rintro ⟨c, hc⟩
    rw [mem_plusPart, ← hc]
    simp [modelInvolution_apply]

theorem minusPart_modelInvolution :
    minusPart modelInvolution = LinearMap.range (LinearMap.inr ℤ ℤ ℤ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨h1, -⟩ := Prod.ext_iff.mp (mem_minusPart.mp hp)
    simp only [modelInvolution_apply, Prod.fst_neg] at h1
    refine ⟨p.2, Prod.ext ?_ rfl⟩
    simp only [LinearMap.coe_inr]
    omega
  · rintro ⟨c, hc⟩
    rw [mem_minusPart, ← hc]
    simp [modelInvolution_apply]

theorem finrank_plusPart_modelInvolution : finrank ℤ (plusPart modelInvolution) = 1 := by
  rw [plusPart_modelInvolution,
    (LinearEquiv.ofInjective (LinearMap.inl ℤ ℤ ℤ) LinearMap.inl_injective).finrank_eq.symm,
    finrank_self]

theorem finrank_minusPart_modelInvolution : finrank ℤ (minusPart modelInvolution) = 1 := by
  rw [minusPart_modelInvolution,
    (LinearEquiv.ofInjective (LinearMap.inr ℤ ℤ ℤ) LinearMap.inr_injective).finrank_eq.symm,
    finrank_self]

/-- The balanced hypothesis is satisfiable. -/
theorem modelInvolution_balanced :
    2 * finrank ℤ (plusPart modelInvolution) = finrank ℤ (ℤ × ℤ) := by
  rw [finrank_plusPart_modelInvolution, Module.finrank_prod, finrank_self]

theorem sup_eigenParts_modelInvolution :
    plusPart modelInvolution ⊔ minusPart modelInvolution = ⊤ := by
  rw [plusPart_modelInvolution, minusPart_modelInvolution]
  exact sup_range_inl_inr

theorem card_defect_modelInvolution : Nat.card (defect modelInvolution) = 1 := by
  rw [defect, sup_eigenParts_modelInvolution]
  exact Nat.card_unique

/-- In the model, both Tate groups have order `2`: the elliptic curve `ℂ / (ℤ + ℤ i)` has two
real connected components, and so does its dual.  In particular the theorems above are not
vacuous. -/
theorem card_H1_modelInvolution : Nat.card (H1 modelInvolution) = 2 := by
  have h := card_defect_mul_card_H1 modelInvolution_involutive
  rw [card_defect_modelInvolution, one_mul, finrank_minusPart_modelInvolution, pow_one] at h
  exact h

theorem card_H0_modelInvolution : Nat.card (H0 modelInvolution) = 2 := by
  have h := card_defect_mul_card_H0 modelInvolution_involutive
  rw [card_defect_modelInvolution, one_mul, finrank_plusPart_modelInvolution, pow_one] at h
  exact h

end GaloisForLFunctions.HTGeometry.InvolutionTate
