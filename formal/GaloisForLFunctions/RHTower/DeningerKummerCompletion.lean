import GaloisForLFunctions.RHTower.DeningerKummerSpace
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The Hilbert--Kummer Banach space

The Kummer space `𝒢 ⊗ ℚ` with the Weil height norm is a normed `ℚ`-vector space; its completion
is a Banach space over `ℚ`.  The Kummer class map sends a unit to its class, has the height as its
norm, and annihilates exactly the roots of unity.  Its image spans the whole of `𝒢 ⊗ ℚ` over `ℚ`,
so it is dense in the completion.

* `deningerKummerSpace_normedAddCommGroup`, `deningerKummerSpace_normedSpace` : the normed
  `ℚ`-vector space.
* `deningerKummerCompletion` : its completion.
* `deningerUnitKummerClass` : the Kummer class map, with `deningerUnitKummerClass_norm` and
  `deningerUnitKummerClass_eq_zero_iff_isOfFinOrder`.
* `deningerUnitKummerClass_span`, `deningerUnitKummerClass_dense_completion` : the classes span `𝒢 ⊗ ℚ`
  and are dense in the completion.
-/

namespace RHTower

open NumberField

section KummerBanach

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

noncomputable instance deningerKummerSpace_normedAddCommGroup :
    NormedAddCommGroup (deningerKummerSpace F) :=
  deningerKummerSpaceNorm.toNormedAddCommGroup

theorem deningerKummerSpace_norm_def (x : deningerKummerSpace F) :
    ‖x‖ = deningerKummerSpaceNorm x := rfl

noncomputable instance deningerKummerSpace_normedSpace :
    NormedSpace ℚ (deningerKummerSpace F) where
  norm_smul_le q x := by
    rw [deningerKummerSpace_norm_def, deningerKummerSpace_norm_def,
      deningerKummerSpaceNorm_qsmul, Rat.cast_abs, ← Real.norm_eq_abs, Rat.norm_cast_real]

/-- **The Hilbert--Kummer Banach space**: the completion of `𝒢 ⊗ ℚ` for the Weil height norm. -/
abbrev deningerKummerCompletion (F : Type*) [Field F] [Algebra ℚ F]
    [Algebra.IsAlgebraic ℚ F] : Type _ :=
  UniformSpace.Completion (deningerKummerSpace F)

/-- **The Kummer class of a unit.** -/
noncomputable def deningerUnitKummerClass (u : Fˣ) : deningerKummerSpace F :=
  DivisibleHull.coe (Additive.ofMul (QuotientGroup.mk u : deningerKummerGroup F))

/-- **The norm of a Kummer class is the height.** -/
theorem deningerUnitKummerClass_norm (u : Fˣ) :
    ‖deningerUnitKummerClass u‖ = deningerAbsHeight (u : F) := by
  rw [deningerKummerSpace_norm_def, deningerUnitKummerClass]
  show deningerKummerAddNorm (Additive.ofMul (QuotientGroup.mk u : deningerKummerGroup F))
      / ((1 : ℕ+) : ℕ) = _
  rw [PNat.one_coe, Nat.cast_one, div_one]
  exact deningerKummerNorm_mk u

/-- The class map is additive. -/
theorem deningerUnitKummerClass_mul (u v : Fˣ) :
    deningerUnitKummerClass (u * v) = deningerUnitKummerClass u + deningerUnitKummerClass v := by
  rw [deningerUnitKummerClass, deningerUnitKummerClass, deningerUnitKummerClass, ← DivisibleHull.coe_add]
  rfl

/-- **The class map annihilates exactly the roots of unity.** -/
theorem deningerUnitKummerClass_eq_zero_iff_isOfFinOrder (u : Fˣ) :
    deningerUnitKummerClass u = 0 ↔ IsOfFinOrder u := by
  constructor
  · intro h
    have hn : ‖deningerUnitKummerClass (F := F) u‖ = 0 := by rw [h, norm_zero]
    rw [deningerUnitKummerClass_norm] at hn
    exact deningerUnits_isOfFinOrder_iff.mp
      ((deningerAbsHeight_eq_zero_iff u.ne_zero).mp hn)
  · intro h
    have hn : ‖deningerUnitKummerClass (F := F) u‖ = 0 := by
      rw [deningerUnitKummerClass_norm,
        (deningerAbsHeight_eq_zero_iff u.ne_zero).mpr (deningerUnits_isOfFinOrder_iff.mpr h)]
    exact norm_eq_zero.mp hn

/-- Every element of the Kummer space is a rational multiple of a class. -/
theorem deningerKummerSpace_mk_eq_smul (m : deningerKummerAdd F) (s : ℕ+) :
    DivisibleHull.mk m s = (((s : ℕ) : ℚ))⁻¹ • (DivisibleHull.coe m : deningerKummerSpace F) := by
  have hs : (((s : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast s.ne_zero
  refine (eq_inv_smul_iff₀ hs).mpr ?_
  rw [DivisibleHull.qsmul_mk]
  refine DivisibleHull.mk_eq_mk_iff_smul_eq_smul.mpr ?_
  simp only [Rat.num_natCast, Rat.den_natCast, PNat.mul_coe]
  rw [natCast_zsmul]
  simp

/-- **The Kummer classes span the Kummer space over `ℚ`.** -/
theorem deningerUnitKummerClass_span :
    Submodule.span ℚ (Set.range (deningerUnitKummerClass (F := F))) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun x => ?_
  induction x using DivisibleHull.ind with
  | mk m s =>
    obtain ⟨u, hu⟩ : ∃ u : Fˣ, (QuotientGroup.mk u : deningerKummerGroup F) = Additive.toMul m :=
      QuotientGroup.mk_surjective _
    have hm : DivisibleHull.coe m = deningerUnitKummerClass (F := F) u := by
      rw [deningerUnitKummerClass, hu]
      rfl
    rw [deningerKummerSpace_mk_eq_smul, hm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

/-- **The Kummer classes are dense in the completion.** -/
theorem deningerUnitKummerClass_dense_completion :
    Dense ((Submodule.span ℚ (Set.range (fun u : Fˣ =>
        ((deningerUnitKummerClass (F := F) u : deningerKummerSpace F) :
          deningerKummerCompletion F)))) : Set (deningerKummerCompletion F)) := by
  refine Dense.mono ?_ UniformSpace.Completion.denseRange_coe
  rintro y ⟨x, rfl⟩
  have hx : x ∈ Submodule.span ℚ (Set.range (deningerUnitKummerClass (F := F))) := by
    rw [deningerUnitKummerClass_span]
    exact Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem
    (f := (UniformSpace.Completion.toComplL (𝕜 := ℚ)
      (E := deningerKummerSpace F)).toLinearMap) hx
  rwa [Submodule.map_span, ← Set.range_comp] at hmap

end KummerBanach

end RHTower
