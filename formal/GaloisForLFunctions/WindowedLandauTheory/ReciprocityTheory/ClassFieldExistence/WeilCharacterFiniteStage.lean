import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.CyclotomicStageWeilDegree

/-! A finite-exponent Weil character with open inertia kernel factors
through a finite Galois stage. The inertia topology gives the first
stage, and a cyclotomic stage detects the necessary Frobenius powers. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField Filter Topology
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}

theorem exists_finiteGaloisStage_in_weilCharacter_ker {H : Type*} [Group H]
    (h : IsPlaceOver A v) (ξ : Weil h →* H) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ σ, ξ σ ^ n = 1)
    (hop : IsOpen {s : Ine (F := K) A | ξ (ineIncl h s) = 1}) :
    ∃ (M : IntermediateField K Ω) (_ : FiniteDimensional K M) (hM : IsGalois K M),
      letI := hM
      ∀ σ : Weil h, AlgEquiv.restrictNormalHom M (σ : Gal(Ω/K)) = 1 → ξ σ = 1 := by
  have hU : {s : Ine (F := K) A | ξ (ineIncl h s) = 1} ∈ 𝓝 (1 : Ine (F := K) A) :=
    hop.mem_nhds (by simp only [Set.mem_setOf_eq, map_one])
  rw [IsEmbedding.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨U, hU, hsub⟩ := hU
  have hU' : U ∈ 𝓝 (1 : Gal(Ω/K)) := hU
  obtain ⟨L, hL, hnL, hLU⟩ := (krullTopology_mem_nhds_one_iff_of_normal K Ω U).mp hU'
  letI := hL
  letI := hnL
  letI : NumberField L := NumberField.of_module_finite K L
  letI : IsGalois K L := { to_normal := hnL }
  let φ := frob h
  let rL := (AlgEquiv.restrictNormalHom L).comp (Weil h).subtype
  let c := orderOf (rL φ) * n
  have hc : 0 < c := Nat.mul_pos (orderOf_pos _) hn
  obtain ⟨V, hVr, hV⟩ := exists_unramified_cyclotomicStage_frobenius_order K Ω h c hc
  let D := (V : IntermediateField K Ω)
  letI := V.2.1
  letI := V.2.2
  letI : NumberField D := NumberField.of_module_finite K D
  letI : Fintype Gal(D/K) := Fintype.ofFinite _
  letI : CommGroup Gal(D/K) :=
    { (inferInstance : Group Gal(D/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  let M := L ⊔ D
  letI : IsGalois K M := inferInstance
  refine ⟨M, inferInstance, inferInstance, fun σ hσ => ?_⟩
  have hfix : (σ : Gal(Ω/K)) ∈ M.fixingSubgroup := by
    rw [← M.restrictNormalHom_ker]
    exact MonoidHom.mem_ker.mpr hσ
  have hrest (B : IntermediateField K Ω) (hB : B ≤ M) :
      (σ : Gal(Ω/K)) ∈ B.fixingSubgroup := B.fixingSubgroup_antitone hB hfix
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
  let rD := (AlgEquiv.restrictNormalHom D).comp (Weil h).subtype
  let w := finitePlaceAtAbsoluteValuation (L := D) A h
  letI := w.isMaximal
  letI : w.asIdeal.LiesOver v.asIdeal := finitePlaceAtAbsoluteValuation_liesOver (L := D) A h
  have hτD : rD (ineIncl h τ) = 1 := by
    have hi : rD (ineIncl h τ) ∈ w.asIdeal.inertia Gal(D/K) :=
      restrictNormalHom_mem_inertia_of_mem_Ine A h τ.2
    rwa [hVr w.asIdeal inferInstance inferInstance, Subgroup.mem_bot] at hi
  have hD : rD σ = 1 := by
    have hh := hrest D le_sup_right
    rw [← D.restrictNormalHom_ker] at hh
    exact MonoidHom.mem_ker.mp hh
  have hDpow : rD φ ^ deg σ = 1 := by
    rw [hτ, map_mul, map_zpow, hτD, mul_one] at hD
    exact hD
  have hcd : (c : ℤ) ∣ deg σ := by
    have e : orderOf (rD φ) = c := hV
    rw [← e]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hDpow
  have hLpow : rL φ ^ deg σ = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp
      ((Int.natCast_dvd_natCast.mpr (dvd_mul_right (orderOf (rL φ)) n)).trans hcd)
  have hξpow : ξ φ ^ deg σ = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp ((Int.natCast_dvd_natCast.mpr
      ((orderOf_dvd_of_pow_eq_one (hpow φ)).trans (dvd_mul_left n (orderOf (rL φ))))).trans hcd)
  have hτL : rL (ineIncl h τ) = 1 := by
    have hh := hrest L le_sup_left
    rw [← L.restrictNormalHom_ker] at hh
    have hL0 : rL σ = 1 := MonoidHom.mem_ker.mp hh
    rwa [hτ, map_mul, map_zpow, hLpow, one_mul] at hL0
  have hτfix : τ.val ∈ L.fixingSubgroup := by
    rw [← L.restrictNormalHom_ker]
    exact hτL
  have hξτ : ξ (ineIncl h τ) = 1 := hsub (hLU hτfix)
  rw [hτ, map_mul, map_zpow, hξpow, hξτ, mul_one]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_finiteGaloisStage_in_weilCharacter_ker
