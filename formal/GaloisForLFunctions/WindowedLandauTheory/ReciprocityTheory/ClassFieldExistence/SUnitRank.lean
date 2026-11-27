import GaloisForLFunctions.RHTower.Artin.TheHerbrandQuotientOfTheSUnits
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The divisor map on S-units has the ordinary unit group as kernel
and full-rank image in the lattice of finite places in S. -/

noncomputable section

open NumberField IsDedekindDomain Module

namespace GaloisForLFunctions

variable (K : Type*) [Field K] [NumberField K] (G : Type*) [Group G] [MulSemiringAction G K]
attribute [local instance] primeMulAction
variable (S : SubMulAction G (HeightOneSpectrum (𝓞 K)))

local notation "U" => (sUnits K G S)

private def restrictedDivisor : U →ₗ[ℤ] (S → ℤ) :=
  ((divMap K G S).comp (U).subtype).toIntLinearMap

private def unitsToDivisorKernel :
    Additive (𝓞 K)ˣ ≃ₗ[ℤ] (restrictedDivisor K G S).ker := by
  let d := restrictedDivisor K G S
  have hu (u : Additive (𝓞 K)ˣ) :
      unitsIncl K u ∈ U ⊓ (divMap K G S).ker := by
    rw [sUnits_inf_ker_divMap]
    exact ⟨u, rfl⟩
  let f : Additive (𝓞 K)ˣ →+ d.ker :=
    { toFun := fun u => ⟨⟨unitsIncl K u, (hu u).1⟩,
        LinearMap.mem_ker.mpr (AddMonoidHom.mem_ker.mp (hu u).2)⟩
      map_zero' := Subtype.ext (Subtype.ext (map_zero _))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add _ _ _)) }
  apply LinearEquiv.ofBijective f.toIntLinearMap
  constructor
  · intro x y hxy
    exact unitsIncl_injective K (congrArg (fun z : d.ker => z.val.val) hxy)
  · intro x
    have hx : x.val.val ∈ U ⊓ (divMap K G S).ker :=
      ⟨x.val.2, AddMonoidHom.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩
    rw [sUnits_inf_ker_divMap] at hx
    obtain ⟨u, he⟩ := hx
    exact ⟨u, Subtype.ext (Subtype.ext he)⟩

/-- The S-unit group of a finite set of places is finitely generated. -/
theorem finite_sUnits [Fintype S] : Module.Finite ℤ U := by
  let d := restrictedDivisor K G S
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker d (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq, ← Module.Finite.iff_fg]
  exact Module.Finite.equiv (unitsToDivisorKernel K G S)

private theorem finrank_range_restrictedDivisor [Fintype S] :
    finrank ℤ (restrictedDivisor K G S).range = Fintype.card S := by
  classical
  let d := restrictedDivisor K G S
  choose u hu hdiv using fun v : S => exists_mem_sUnits_divMap_eq K G S v
  let b := Pi.basisFun ℤ S
  let lift : (S → ℤ) →ₗ[ℤ] U := b.constr ℤ fun v => ⟨u v, hu v⟩
  have hcomp : d.comp lift = (classNumber K : ℤ) • LinearMap.id := by
    apply b.ext
    intro v
    simp only [LinearMap.comp_apply, lift, Basis.constr_basis, LinearMap.smul_apply, LinearMap.id_apply]
    change divMap K G S (u v) = (classNumber K : ℤ) • b v
    simpa only [b, Pi.basisFun_apply, natCast_zsmul] using hdiv v
  have hcompinj : Function.Injective (d.comp lift) := by
    rw [hcomp]
    intro x y he
    exact smul_right_injective (S → ℤ) (by exact_mod_cast classNumber_ne_zero K) he
  have hcard : finrank ℤ (S → ℤ) = Fintype.card S := Module.finrank_fintype_fun_eq_card ℤ
  refine le_antisymm ((Submodule.finrank_le _).trans hcard.le) ?_
  rw [← hcard, ← LinearMap.finrank_range_of_inj hcompinj]
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

/-- Each finite place in S contributes one free generator to the rank
of the S-unit group. -/
theorem finrank_sUnits [Fintype S] :
    finrank ℤ U = Units.rank K + Fintype.card S := by
  letI : Module.Finite ℤ U := finite_sUnits K G S
  let d := restrictedDivisor K G S
  rw [← Submodule.finrank_quotient_add_finrank d.ker,
    LinearEquiv.finrank_eq d.quotKerEquivRange, finrank_range_restrictedDivisor,
    ← LinearEquiv.finrank_eq (unitsToDivisorKernel K G S), Units.finrank_eq, add_comm]

/-- If a nonzero power has trivial divisor outside S, the original unit
has trivial divisor there too. -/
theorem nsmul_mem_sUnits_iff {n : ℕ} (hn : n ≠ 0) {x : Additive Kˣ} :
    n • x ∈ U ↔ x ∈ U := by
  constructor
  · intro h w hw
    have h0 := h w hw
    rw [map_nsmul, nsmul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast hn)
  · intro h
    exact (U).nsmul_mem h n

theorem range_nsmul_subgroupOf_sUnits {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := Additive Kˣ) n).range.addSubgroupOf U =
      (nsmulAddMonoidHom (α := U) n).range := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    change n • x = y.val at hx
    have hx' : n • x ∈ U := hx ▸ y.2
    exact ⟨⟨x, (nsmul_mem_sUnits_iff K G S hn).mp hx'⟩, Subtype.ext hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x.val, congrArg Subtype.val hx⟩

end GaloisForLFunctions
