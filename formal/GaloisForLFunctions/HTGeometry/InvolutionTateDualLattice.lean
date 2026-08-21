import GaloisForLFunctions.HTGeometry.InvolutionTateCohomology
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tate cohomology of the dual lattice

Let `Λ` be a finite free `ℤ`-module with an involution `σ`, and let `Λ^∨ = Hom_ℤ(Λ, ℤ)` carry the
transposed involution `σ^∨ : f ↦ f ∘ σ`.  This file proves

```
#Ĥ⁰(σ^∨, Λ^∨) = #Ĥ⁰(σ, Λ)   and   #Ĥ¹(σ^∨, Λ^∨) = #Ĥ¹(σ, Λ) ,
```

the Tate duality for the group `ℤ/2` in the form needed by Suzuki, *Duality invariance of Faltings
heights, Hodge line bundles and global periods* (arXiv:2504.04993), Proposition 5.1: the period
lattice of the dual complex torus is `Λ^∨` with the involution `-σ^∨`, and the number of connected
components of its real points is `#Ĥ¹(-σ^∨, Λ^∨) = #Ĥ⁰(σ^∨, Λ^∨)`.

The proof is elementary and avoids the classification of `ℤ[ℤ/2]`-lattices:

* the *ranks* of the two eigenlattices are preserved, because restriction of functionals gives
  injections `Λ^∨_± ↪ (Λ_±)^∨` whose ranks must therefore add up to `rank Λ` on both sides
  (`InvolutionTate.finrank_plusPart_dual`);
* the *defect* `#(Λ / (Λ⁺ ⊕ Λ⁻))` is preserved, because the reduction mod `2` of the evaluation
  pairing identifies `Λ^∨ / 2Λ^∨` with the `𝔽₂`-dual of `Λ / 2Λ`, carrying the reduction of
  `σ^∨ - 1` to the transpose of the reduction of `σ - 1`, and a linear map and its transpose have
  equal rank (`InvolutionTate.card_defect_dual`).

Together with the index formula `#(Λ/(Λ⁺ ⊕ Λ⁻)) · #Ĥ¹(σ) = 2 ^ rank Λ⁻` of
`GaloisForLFunctions.HTGeometry.InvolutionTateCohomology` this gives the two displayed equalities.
-/

namespace GaloisForLFunctions.HTGeometry.InvolutionTate

open LinearMap Module Submodule

variable {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]

/-- The involution transposed to the dual lattice, `f ↦ f ∘ σ`. -/
def dualInvolution (σ : Λ →ₗ[ℤ] Λ) : Module.Dual ℤ Λ →ₗ[ℤ] Module.Dual ℤ Λ :=
  Module.Dual.transpose (R := ℤ) σ

@[simp] theorem dualInvolution_apply (σ : Λ →ₗ[ℤ] Λ) (f : Module.Dual ℤ Λ) (x : Λ) :
    dualInvolution σ f x = f (σ x) := rfl

theorem dualInvolution_involutive {σ : Λ →ₗ[ℤ] Λ} (hσ : ∀ x, σ (σ x) = x) :
    ∀ f, dualInvolution σ (dualInvolution σ f) = f := by
  intro f
  ext x
  simp [hσ]

/-! ### Step A: the eigenlattices have the same ranks -/

variable {σ : Λ →ₗ[ℤ] Λ}

/-- A functional fixed by `σ^∨` kills the `-1`-eigenlattice. -/
theorem plusPart_dual_apply_minusPart {f : Module.Dual ℤ Λ} (hf : f ∈ plusPart (dualInvolution σ))
    {x : Λ} (hx : x ∈ minusPart σ) : f x = 0 := by
  have h1 : f (σ x) = f x := congrFun (congrArg (fun g : Module.Dual ℤ Λ => (g : Λ → ℤ))
    (mem_plusPart.mp hf)) x
  rw [mem_minusPart.mp hx, map_neg] at h1
  omega

/-- A functional negated by `σ^∨` kills the `+1`-eigenlattice. -/
theorem minusPart_dual_apply_plusPart {f : Module.Dual ℤ Λ} (hf : f ∈ minusPart (dualInvolution σ))
    {x : Λ} (hx : x ∈ plusPart σ) : f x = 0 := by
  have h1 : f (σ x) = -f x := congrFun (congrArg (fun g : Module.Dual ℤ Λ => (g : Λ → ℤ))
    (mem_minusPart.mp hf)) x
  rw [mem_plusPart.mp hx] at h1
  omega

/-- Every element of `Λ` has `2 x` in `Λ⁺ ⊕ Λ⁻`. -/
theorem two_smul_mem_sup (hσ : ∀ x, σ (σ x) = x) (x : Λ) :
    (2 : ℤ) • x ∈ plusPart σ ⊔ minusPart σ := by
  refine Submodule.mem_sup.mpr ⟨x + σ x, ?_, x - σ x, ?_, by module⟩
  · rw [mem_plusPart, map_add, hσ]; abel
  · rw [mem_minusPart, map_sub, hσ]; abel

/-- Restriction of functionals, from the `+1`-eigenlattice of `Λ^∨` to the dual of the
`+1`-eigenlattice of `Λ`. -/
def restrictPlus (σ : Λ →ₗ[ℤ] Λ) :
    plusPart (dualInvolution σ) →ₗ[ℤ] Module.Dual ℤ (plusPart σ) where
  toFun f := (f : Module.Dual ℤ Λ).comp (plusPart σ).subtype
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

/-- Restriction of functionals, from the `-1`-eigenlattice of `Λ^∨` to the dual of the
`-1`-eigenlattice of `Λ`. -/
def restrictMinus (σ : Λ →ₗ[ℤ] Λ) :
    minusPart (dualInvolution σ) →ₗ[ℤ] Module.Dual ℤ (minusPart σ) where
  toFun f := (f : Module.Dual ℤ Λ).comp (minusPart σ).subtype
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

theorem injective_restrictPlus (hσ : ∀ x, σ (σ x) = x) :
    Function.Injective (restrictPlus σ) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply Subtype.ext
  ext x
  have hzero : ∀ y ∈ plusPart σ ⊔ minusPart σ, (f : Module.Dual ℤ Λ) y = 0 := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : (f : Module.Dual ℤ Λ) a = 0 := by
      have := congrArg (fun g : Module.Dual ℤ (plusPart σ) => g ⟨a, ha⟩) hf
      simpa [restrictPlus] using this
    have h2 : (f : Module.Dual ℤ Λ) b = 0 := plusPart_dual_apply_minusPart f.2 hb
    simp [h1, h2]
  have h2x := hzero _ (two_smul_mem_sup hσ x)
  rw [map_zsmul, smul_eq_mul] at h2x
  show (f : Module.Dual ℤ Λ) x = ((0 : plusPart (dualInvolution σ)) : Module.Dual ℤ Λ) x
  rw [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  omega

theorem injective_restrictMinus (hσ : ∀ x, σ (σ x) = x) :
    Function.Injective (restrictMinus σ) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply Subtype.ext
  ext x
  have hzero : ∀ y ∈ plusPart σ ⊔ minusPart σ, (f : Module.Dual ℤ Λ) y = 0 := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : (f : Module.Dual ℤ Λ) a = 0 := minusPart_dual_apply_plusPart f.2 ha
    have h2 : (f : Module.Dual ℤ Λ) b = 0 := by
      have := congrArg (fun g : Module.Dual ℤ (minusPart σ) => g ⟨b, hb⟩) hf
      simpa [restrictMinus] using this
    simp [h1, h2]
  have h2x := hzero _ (two_smul_mem_sup hσ x)
  rw [map_zsmul, smul_eq_mul] at h2x
  show (f : Module.Dual ℤ Λ) x = ((0 : minusPart (dualInvolution σ)) : Module.Dual ℤ Λ) x
  rw [ZeroMemClass.coe_zero, LinearMap.zero_apply]
  omega


/-- **The eigenlattices of `σ` and of `σ^∨` have the same ranks.** -/
theorem finrank_eigenParts_dual (hσ : ∀ x, σ (σ x) = x) :
    finrank ℤ (plusPart (dualInvolution σ)) = finrank ℤ (plusPart σ) ∧
      finrank ℤ (minusPart (dualInvolution σ)) = finrank ℤ (minusPart σ) := by
  have hp : finrank ℤ (plusPart (dualInvolution σ)) ≤ finrank ℤ (plusPart σ) := by
    refine le_trans (LinearMap.finrank_le_finrank_of_injective (injective_restrictPlus hσ)) ?_
    exact le_of_eq (Module.finrank_linearMap_self ℤ ℤ (plusPart σ))
  have hm : finrank ℤ (minusPart (dualInvolution σ)) ≤ finrank ℤ (minusPart σ) := by
    refine le_trans (LinearMap.finrank_le_finrank_of_injective (injective_restrictMinus hσ)) ?_
    exact le_of_eq (Module.finrank_linearMap_self ℤ ℤ (minusPart σ))
  have hsum : finrank ℤ (plusPart σ) + finrank ℤ (minusPart σ) = finrank ℤ Λ :=
    finrank_plusPart_add_finrank_minusPart hσ
  have hsumd : finrank ℤ (plusPart (dualInvolution σ)) + finrank ℤ (minusPart (dualInvolution σ))
      = finrank ℤ (Module.Dual ℤ Λ) :=
    finrank_plusPart_add_finrank_minusPart (dualInvolution_involutive hσ)
  rw [Module.finrank_linearMap_self ℤ ℤ Λ] at hsumd
  omega

theorem finrank_minusPart_dual (hσ : ∀ x, σ (σ x) = x) :
    finrank ℤ (minusPart (dualInvolution σ)) = finrank ℤ (minusPart σ) :=
  (finrank_eigenParts_dual hσ).2

theorem finrank_plusPart_dual (hσ : ∀ x, σ (σ x) = x) :
    finrank ℤ (plusPart (dualInvolution σ)) = finrank ℤ (plusPart σ) :=
  (finrank_eigenParts_dual hσ).1


/-! ### Step B: the defect is preserved

The defect `Λ / (Λ⁺ ⊕ Λ⁻)` is the image of `σ - 1` in `Λ / 2Λ`, and the evaluation pairing
identifies `Λ^∨ / 2Λ^∨` with the `𝔽₂`-dual of `Λ / 2Λ` in a way that carries the reduction of
`σ^∨ - 1` to the transpose of the reduction of `σ - 1`. -/

/-- `2 Λ`, written as in mathlib's `ModN`. -/
abbrev twoLat (Λ : Type*) [AddCommGroup Λ] : Submodule ℤ Λ :=
  LinearMap.range (LinearMap.lsmul ℤ Λ ((2 : ℕ) : ℤ))

theorem mem_twoLat {Λ : Type*} [AddCommGroup Λ] {v : Λ} :
    v ∈ twoLat Λ ↔ ∃ w : Λ, (2 : ℤ) • w = v := by
  simp [LinearMap.mem_range, LinearMap.lsmul_apply]

/-- `Λ⁺ ⊕ Λ⁻` is exactly the preimage of `2Λ` under `σ - 1`. -/
theorem sup_eq_comap_dlt_twoLat (hσ : ∀ x, σ (σ x) = x) :
    plusPart σ ⊔ minusPart σ = Submodule.comap (dlt σ) (twoLat Λ) := by
  ext x
  rw [Submodule.mem_comap, mem_twoLat]
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨-b, ?_⟩
    rw [dlt_apply, map_add, mem_plusPart.mp ha, mem_minusPart.mp hb]
    module
  · rintro ⟨y, hy⟩
    -- `(σ + 1)(σ - 1) x = 0` forces `y ∈ Λ⁻`
    have hzero : σ ((2 : ℤ) • y) + (2 : ℤ) • y = 0 := by
      rw [hy, dlt_apply, map_sub, hσ]
      abel
    have hy' : σ y + y = 0 := by
      have h2 : (2 : ℤ) • (σ y + y) = 0 := by
        rw [smul_add, ← map_zsmul]
        simpa using hzero
      rcases smul_eq_zero.mp h2 with h | h
      · exact absurd h (by norm_num)
      · exact h
    have hymem : y ∈ minusPart σ := by
      rw [mem_minusPart, ← add_eq_zero_iff_eq_neg]; exact hy'
    -- now use the description of `ker ψ`
    rw [← ker_psi hσ, LinearMap.mem_ker]
    have hmem : dltCod hσ x ∈ twoMinus σ := by
      refine ⟨(⟨y, hymem⟩ : minusPart σ), ?_⟩
      apply Subtype.ext
      simp only [LinearMap.smul_apply, LinearMap.id_apply, SetLike.val_smul, dltCod_coe]
      rw [← dlt_apply σ x, ← hy]
    rw [psi, LinearMap.coe_comp, Function.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-! #### The reduction of the lattice modulo 2 -/

theorem mem_twoLat_iff_forall_dual {v : Λ} :
    v ∈ twoLat Λ ↔ ∀ f : Module.Dual ℤ Λ, (2 : ℤ) ∣ f v := by
  classical
  constructor
  · intro hv f
    obtain ⟨w, rfl⟩ := mem_twoLat.mp hv
    exact ⟨f w, by rw [map_zsmul, smul_eq_mul]⟩
  · intro h
    let b := Module.Free.chooseBasis ℤ Λ
    choose m hm using fun i => h (b.coord i)
    rw [mem_twoLat]
    refine ⟨∑ i, m i • b i, ?_⟩
    rw [Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    have := hm i
    rw [Basis.coord_apply] at this
    omega

theorem mem_twoLat_dual_iff_forall {g : Module.Dual ℤ Λ} :
    g ∈ twoLat (Module.Dual ℤ Λ) ↔ ∀ x : Λ, (2 : ℤ) ∣ g x := by
  classical
  constructor
  · intro hg x
    obtain ⟨h, rfl⟩ := mem_twoLat.mp hg
    exact ⟨h x, by simp⟩
  · intro hdvd
    let b := Module.Free.chooseBasis ℤ Λ
    choose m hm using fun i => hdvd (b i)
    rw [mem_twoLat]
    refine ⟨∑ i, m i • b.coord i, ?_⟩
    apply b.ext
    intro j
    rw [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp only [LinearMap.smul_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one]
      have := hm j
      omega
    · intro i _ hij
      simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, Ne.symm hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj

theorem dlt_le_comap_twoLat (σ : Λ →ₗ[ℤ] Λ) :
    twoLat Λ ≤ Submodule.comap (dlt σ) (twoLat Λ) := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_twoLat.mp hv
  rw [Submodule.mem_comap, mem_twoLat]
  exact ⟨dlt σ w, by rw [map_zsmul]⟩

/-- `σ - 1` reduced modulo `2`, as an endomorphism of `Λ / 2Λ` over `ℤ`. -/
noncomputable def redDltZ (σ : Λ →ₗ[ℤ] Λ) : ModN Λ 2 →ₗ[ℤ] ModN Λ 2 :=
  Submodule.mapQ (twoLat Λ) (twoLat Λ) (dlt σ) (dlt_le_comap_twoLat σ)

/-- `σ - 1` reduced modulo `2`, as a `ZMod 2`-linear endomorphism of `Λ / 2Λ`. -/
noncomputable def redDlt (σ : Λ →ₗ[ℤ] Λ) : ModN Λ 2 →ₗ[ZMod 2] ModN Λ 2 :=
  ((redDltZ σ).toAddMonoidHom).toZModLinearMap 2

theorem redDlt_mkQ (σ : Λ →ₗ[ℤ] Λ) (x : Λ) :
    redDlt σ ((twoLat Λ).mkQ x) = (twoLat Λ).mkQ (dlt σ x) := rfl

theorem ker_redComp (hσ : ∀ x, σ (σ x) = x) :
    LinearMap.ker ((twoLat Λ).mkQ ∘ₗ dlt σ) = plusPart σ ⊔ minusPart σ := by
  rw [sup_eq_comap_dlt_twoLat hσ]
  ext x
  rw [LinearMap.mem_ker]
  show Submodule.Quotient.mk (dlt σ x) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem mem_range_redComp_iff (σ : Λ →ₗ[ℤ] Λ) (y : ModN Λ 2) :
    y ∈ LinearMap.range ((twoLat Λ).mkQ ∘ₗ dlt σ) ↔ y ∈ LinearMap.range (redDlt σ) := by
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(twoLat Λ).mkQ x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := (twoLat Λ).mkQ_surjective z
    exact ⟨x, rfl⟩

/-- **The defect is the image of `σ - 1` in `Λ / 2Λ`.** -/
theorem card_defect_eq_card_range_redDlt (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (defect σ) = Nat.card (LinearMap.range (redDlt σ)) := by
  have h1 : Nat.card (Λ ⧸ LinearMap.ker ((twoLat Λ).mkQ ∘ₗ dlt σ))
      = Nat.card (LinearMap.range ((twoLat Λ).mkQ ∘ₗ dlt σ)) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [ker_redComp hσ] at h1
  rw [h1]
  exact Nat.card_congr (Equiv.subtypeEquivRight (mem_range_redComp_iff σ))

/-! #### The evaluation pairing modulo 2 -/

theorem two_nsmul_zmod_two (a : ZMod 2) : (2 : ℕ) • a = 0 := CharTwo.two_nsmul a

/-- Reduction mod `2` of a functional, as an additive map on `Λ / 2Λ`. -/
noncomputable def evalOneHom (f : Module.Dual ℤ Λ) : ModN Λ 2 →+ ZMod 2 :=
  ModN.liftEquiv.symm
    ⟨(Int.castAddHom (ZMod 2)).comp (LinearMap.toAddMonoidHom f), fun _ => two_nsmul_zmod_two _⟩

/-- Reduction mod `2` of a functional, as an `𝔽₂`-functional on `Λ / 2Λ`. -/
noncomputable def evalOne (f : Module.Dual ℤ Λ) : Module.Dual (ZMod 2) (ModN Λ 2) :=
  (evalOneHom f).toZModLinearMap 2

@[simp] theorem evalOne_mkQ (f : Module.Dual ℤ Λ) (x : Λ) :
    evalOne f ((twoLat Λ).mkQ x) = ((f x : ℤ) : ZMod 2) := rfl

@[simp] theorem evalOne_mk (f : Module.Dual ℤ Λ) (x : Λ) :
    evalOne f (Submodule.Quotient.mk x : ModN Λ 2) = ((f x : ℤ) : ZMod 2) := rfl

theorem dual_modTwo_ext {F G : Module.Dual (ZMod 2) (ModN Λ 2)}
    (h : ∀ x : Λ, F ((twoLat Λ).mkQ x) = G ((twoLat Λ).mkQ x)) : F = G := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (twoLat Λ).mkQ_surjective y
  exact h x

/-- The assignment `f ↦ (f mod 2)` on functionals. -/
noncomputable def evalAddHom : Module.Dual ℤ Λ →+ Module.Dual (ZMod 2) (ModN Λ 2) where
  toFun := evalOne
  map_zero' := by
    refine dual_modTwo_ext fun x => ?_
    simp
  map_add' f g := by
    refine dual_modTwo_ext fun x => ?_
    simp

theorem two_nsmul_evalAddHom (f : Module.Dual ℤ Λ) :
    (2 : ℕ) • (evalAddHom f) = 0 := by
  refine dual_modTwo_ext fun x => ?_
  rw [LinearMap.zero_apply]
  show (2 : ℕ) • ((evalAddHom f) ((twoLat Λ).mkQ x)) = 0
  exact two_nsmul_zmod_two _

/-- **The evaluation pairing modulo `2`**: `Λ^∨ / 2Λ^∨ → Dual_{𝔽₂}(Λ / 2Λ)`. -/
noncomputable def modTwoEval :
    ModN (Module.Dual ℤ Λ) 2 →ₗ[ZMod 2] Module.Dual (ZMod 2) (ModN Λ 2) :=
  (ModN.liftEquiv.symm ⟨evalAddHom, two_nsmul_evalAddHom⟩).toZModLinearMap 2

@[simp] theorem modTwoEval_apply (f : Module.Dual ℤ Λ) (x : Λ) :
    modTwoEval ((twoLat (Module.Dual ℤ Λ)).mkQ f) ((twoLat Λ).mkQ x)
      = ((f x : ℤ) : ZMod 2) := rfl

theorem injective_modTwoEval : Function.Injective (modTwoEval (Λ := Λ)) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨f, rfl⟩ := (twoLat (Module.Dual ℤ Λ)).mkQ_surjective y
  refine (Submodule.Quotient.mk_eq_zero _).2 (mem_twoLat_dual_iff_forall.2 fun x => ?_)
  have hx : modTwoEval ((twoLat (Module.Dual ℤ Λ)).mkQ f) ((twoLat Λ).mkQ x) = 0 := by
    rw [hy]; rfl
  rw [modTwoEval_apply] at hx
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (f x) 2).1 hx

theorem finrank_modN_two : finrank (ZMod 2) (ModN Λ 2) = finrank ℤ Λ := by
  classical
  let b := Module.Free.chooseBasis ℤ Λ
  rw [Module.finrank_eq_card_basis (ModN.basis (n := 2) b), Module.finrank_eq_card_basis b]

theorem finrank_dual_modN_two :
    finrank (ZMod 2) (Module.Dual (ZMod 2) (ModN Λ 2)) = finrank ℤ Λ := by
  rw [Subspace.dual_finrank_eq (K := ZMod 2) (V := ModN Λ 2), finrank_modN_two]

theorem finrank_modN_dual_two :
    finrank (ZMod 2) (ModN (Module.Dual ℤ Λ) 2) = finrank ℤ Λ := by
  rw [finrank_modN_two (Λ := Module.Dual ℤ Λ), Module.finrank_linearMap_self ℤ ℤ Λ]

theorem bijective_modTwoEval : Function.Bijective (modTwoEval (Λ := Λ)) := by
  have hdim : finrank (ZMod 2) (ModN (Module.Dual ℤ Λ) 2)
      = finrank (ZMod 2) (Module.Dual (ZMod 2) (ModN Λ 2)) := by
    rw [finrank_modN_dual_two, finrank_dual_modN_two]
  exact ⟨injective_modTwoEval,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 injective_modTwoEval⟩

theorem modTwoEval_comp_redDlt (σ : Λ →ₗ[ℤ] Λ) :
    (modTwoEval (Λ := Λ)).comp (redDlt (dualInvolution σ))
      = (redDlt σ).dualMap.comp (modTwoEval (Λ := Λ)) := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨f, rfl⟩ := (twoLat (Module.Dual ℤ Λ)).mkQ_surjective y
  refine dual_modTwo_ext fun x => ?_
  show modTwoEval ((twoLat (Module.Dual ℤ Λ)).mkQ (dlt (dualInvolution σ) f))
      ((twoLat Λ).mkQ x)
    = modTwoEval ((twoLat (Module.Dual ℤ Λ)).mkQ f) ((twoLat Λ).mkQ (dlt σ x))
  rw [modTwoEval_apply, modTwoEval_apply]
  congr 1
  show (dualInvolution σ f - f) x = f (σ x - x)
  rw [map_sub, LinearMap.sub_apply]
  rfl

theorem finrank_range_redDlt_dual (σ : Λ →ₗ[ℤ] Λ) :
    finrank (ZMod 2) (LinearMap.range (redDlt (dualInvolution σ)))
      = finrank (ZMod 2) (LinearMap.range (redDlt σ)) := by
  have hbij := bijective_modTwoEval (Λ := Λ)
  have hsurj : LinearMap.range (modTwoEval (Λ := Λ)) = ⊤ := LinearMap.range_eq_top.2 hbij.2
  have hkey : LinearMap.range ((redDlt σ).dualMap)
      = Submodule.map (modTwoEval (Λ := Λ)) (LinearMap.range (redDlt (dualInvolution σ))) := by
    have h1 : LinearMap.range ((redDlt σ).dualMap ∘ₗ modTwoEval (Λ := Λ))
        = LinearMap.range ((redDlt σ).dualMap) := by
      rw [LinearMap.range_comp, hsurj, Submodule.map_top]
    rw [← h1, ← modTwoEval_comp_redDlt σ, LinearMap.range_comp]
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (redDlt σ), hkey]
  exact (Submodule.equivMapOfInjective _ hbij.1 _).finrank_eq

theorem card_eq_two_pow_finrank {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Nat.card W = 2 ^ finrank (ZMod 2) W := by
  haveI := Fintype.ofFinite W
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]

/-- **The defect is preserved by lattice duality.** -/
theorem card_defect_dual (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (defect (dualInvolution σ)) = Nat.card (defect σ) := by
  rw [card_defect_eq_card_range_redDlt (dualInvolution_involutive hσ),
    card_defect_eq_card_range_redDlt hσ, card_eq_two_pow_finrank, card_eq_two_pow_finrank,
    finrank_range_redDlt_dual σ]

/-- **Tate duality for `ℤ/2`, degree one.** -/
theorem card_H1_dual (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (H1 (dualInvolution σ)) = Nat.card (H1 σ) := by
  have h1 := card_defect_mul_card_H1 (σ := dualInvolution σ) (dualInvolution_involutive hσ)
  have h2 := card_defect_mul_card_H1 hσ
  rw [card_defect_dual hσ, finrank_minusPart_dual hσ] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (card_defect_ne_zero hσ)) (h1.trans h2.symm)

/-- **Tate duality for `ℤ/2`, degree zero.** -/
theorem card_H0_dual (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (H0 (dualInvolution σ)) = Nat.card (H0 σ) := by
  have h1 := card_defect_mul_card_H0 (σ := dualInvolution σ) (dualInvolution_involutive hσ)
  have h2 := card_defect_mul_card_H0 hσ
  rw [card_defect_dual hσ, finrank_plusPart_dual hσ] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (card_defect_ne_zero hσ)) (h1.trans h2.symm)

end GaloisForLFunctions.HTGeometry.InvolutionTate
