import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionPowerIndex
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration

/-! Sufficiently deep units of a finite completion have integral roots.
If the exponent is a unit, the first principal units suffice. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero
open GaloisForLFunctions.HTGeometry.ABHN
open scoped ValuativeRel

namespace GlobalTheory.Reciprocity

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  (v : Valuation F ℤᵐ⁰) [v.Compatible]

private theorem valued_le_one_iff_mem_integer (x : F) : v x ≤ 1 ↔ x ∈ 𝒪[F] := by
  rw [← valuationSubring_eq_integer v]
  exact Iff.rfl

private theorem valued_integerUnit (x : 𝒪[F]ˣ) : v ((x : 𝒪[F]) : F) = 1 := by
  have hi : v.Integers 𝒪[F] := ⟨Subtype.val_injective,
    fun a => (valued_le_one_iff_mem_integer v a.val).mpr a.2,
    fun a ha => ⟨⟨a, (valued_le_one_iff_mem_integer v a).mp ha⟩, rfl⟩⟩
  exact hi.isUnit_iff_valuation_eq_one.mp x.isUnit

private def integerUnitOfValuedEqOne (x : Fˣ) (hx : v x.val = 1) : 𝒪[F]ˣ :=
  ⟨⟨x.val, (valued_le_one_iff_mem_integer v _).mp hx.le⟩,
    ⟨(x⁻¹ : Fˣ).val, (valued_le_one_iff_mem_integer v _).mp (by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])⟩,
    Subtype.ext x.mul_inv, Subtype.ext x.inv_mul⟩

theorem mem_principalUnits_of_valued_bound {π : 𝒪[F]}
    (hπ : Irreducible π) (hπv : v π.val = exp (-1 : ℤ)) (s : ℕ) (x : 𝒪[F]ˣ)
    (hx : v (((x : 𝒪[F]) : F) - 1) ≤ exp (-(s : ℤ))) :
    x ∈ nonarchimedeanLocalFieldPrincipalUnitFiltration F s := by
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff, mem_maximalIdeal_pow_iff hπ]
  have hπs : v (π.val ^ s) = exp (-(s : ℤ)) := by rw [map_pow, hπv, ← exp_nsmul]; simp
  have h0 : π.val ^ s ≠ 0 := pow_ne_zero _ (fun h => hπ.ne_zero (Subtype.ext h))
  let a : F := (((x : 𝒪[F]) : F) - 1) / π.val ^ s
  have ha : v a ≤ 1 := by
    change v (_ / _) ≤ 1
    have hp : 0 < v (π.val ^ s) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr h0)
    rw [map_div₀]
    apply (div_le_one₀ hp).mpr
    rwa [hπs]
  refine ⟨⟨a, (valued_le_one_iff_mem_integer v a).mp ha⟩, Subtype.ext ?_⟩
  change (((x : 𝒪[F]) : F) - 1) = π.val ^ s * a
  rw [mul_comm]
  exact (div_mul_cancel₀ _ h0).symm

private theorem exists_root_at_valuation_depth (hv : Function.Surjective v) (n : ℕ)
    (hn : (n : F) ≠ 0) :
    ∃ s : ℕ, 1 ≤ s ∧ (v (n : F) = 1 → s = 1) ∧ ∀ x : Fˣ,
      v x.val = 1 → v (x.val - 1) ≤ exp (-(s : ℤ)) →
      ∃ z : Fˣ, v z.val = 1 ∧ z ^ n = x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hn' : (n : 𝒪[F]) ≠ 0 := fun h => hn (congrArg Subtype.val h)
  obtain ⟨d, ε, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn' hπ
  have hπv := irreducible_intValuation_eq_exp_neg_one v hv hπ
  have hnv : v (n : F) = exp (-(d : ℤ)) := by
    change v ((n : 𝒪[F]).val) = _
    rw [he, Subring.coe_mul, Subring.coe_pow, map_mul, map_pow,
      valued_integerUnit v ε, one_mul, hπv, ← exp_nsmul]
    simp
  refine ⟨d + 1 + d, by omega, fun h => ?_, fun x hx hx' => ?_⟩
  · have hd := exp_inj.mp (hnv.symm.trans (h.trans exp_zero.symm))
    omega
  · let x' := integerUnitOfValuedEqOne v x hx
    have hxU : x' ∈ nonarchimedeanLocalFieldPrincipalUnitFiltration F (d + 1 + d) :=
      mem_principalUnits_of_valued_bound v hπ hπv _ x' hx'
    rw [← map_pow_principalUnitFiltration hπ he] at hxU
    obtain ⟨z, -, hz⟩ := hxU
    refine ⟨Units.map (𝒪[F]).subtype.toMonoidHom z, valued_integerUnit v z, ?_⟩
    apply Units.ext
    exact congrArg (fun b : 𝒪[F]ˣ => (b.val : F)) hz

end Local

variable {K : Type} [Field K] [NumberField K]

theorem exists_unitsLevel_pow_roots (p : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : n ≠ 0) :
    ∃ s : ℕ, 1 ≤ s ∧ (Valued.v (n : p.adicCompletion K) = 1 → s = 1) ∧
      ∀ x : (p.adicCompletion K)ˣ, x ∈ unitsLevel p s →
        ∃ z : (p.adicCompletion K)ˣ, z ∈ unitsLevel p 0 ∧ z ^ n = x := by
  obtain ⟨w, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := K)).surjective p
  let F := w.maximalIdeal.adicCompletion K
  let v : Valuation F ℤᵐ⁰ := Valued.v
  letI : ValuativeRel F := numberFieldAdicCompletionValuativeRel K w
  letI : v.Compatible := numberFieldAdicCompletionValuationCompatible K w
  letI : IsNonarchimedeanLocalField F := numberFieldAdicCompletionIsNonarchimedeanLocalField K w
  letI : T2Space F := inferInstanceAs (T2Space (w.maximalIdeal.adicCompletion K))
  have hnF : (n : F) ≠ 0 := by
    rw [← map_natCast (algebraMap K F), map_ne_zero_iff _ (algebraMap K F).injective]
    exact Nat.cast_ne_zero.mpr hn
  obtain ⟨s, hs, hunit, hroot⟩ :=
    exists_root_at_valuation_depth v (valuedAdicCompletion_surjective K w.maximalIdeal) n hnF
  refine ⟨s, hs, hunit, fun x hx => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hroot x hx.1 hx.2
  refine ⟨z, mem_unitsLevel.mpr ⟨hz, ?_⟩, hzx⟩
  change v (z.val - (1 : F)) ≤ exp (-(0 : ℤ))
  rw [neg_zero, exp_zero]
  exact v.map_sub_le hz.le (map_one v).le

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_unitsLevel_pow_roots
