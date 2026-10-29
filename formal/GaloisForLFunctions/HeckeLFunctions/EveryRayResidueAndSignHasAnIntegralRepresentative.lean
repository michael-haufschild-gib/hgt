import GaloisForLFunctions.HeckeLFunctions.TheTrivialCharacterHasAPositiveResidue

/-!
# Finite residues and real signs can be prescribed independently

Positive ray-class density forces every signed fundamental norm ball to have positive
volume. Its translated lattice count has a smaller-order error, so every residue coset
meets a sufficiently large signed ball. This gives a nonzero integral representative of
any invertible finite residue and any real sign pattern, and proves `rayHom` surjective.
-/

noncomputable section

open MeasureTheory Filter Topology NumberField Module Set NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone
open scoped Classical Pointwise

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- Every sign sector of the fundamental norm ball has positive volume. -/
theorem signedNormBall_volume_pos (σ : 𝔪.inf → ℤˣ) :
    0 < volume.real (signedNormBall 𝔪.inf σ) := by
  rw [measureReal_signedNormBall_eq 𝔪.inf σ (1 : 𝔪.inf → ℤˣ)]
  have h := rayDensity_pos 𝔪
  by_contra hV
  have hzero : volume.real (signedNormBall 𝔪.inf (1 : 𝔪.inf → ℤˣ)) = 0 :=
    le_antisymm (not_lt.mp hV) measureReal_nonneg
  rw [rayDensity, hzero, mul_zero, zero_div] at h
  exact lt_irrefl 0 h

/-- Some positive dilate of a sign sector meets any given translate of a full lattice. -/
theorem exists_lattice_point_in_signedNormBall_coset
    (Λ : Submodule ℤ (mixedSpace K)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (σ : 𝔪.inf → ℤˣ) (v : mixedSpace K) :
    ∃ T : ℝ, 1 ≤ T ∧
      ((v +ᵥ (T ^ ((finrank ℚ K : ℝ)⁻¹)) • signedNormBall 𝔪.inf σ) ∩
        (Λ : Set (mixedSpace K))).Nonempty := by
  obtain ⟨C, hC⟩ := exists_abs_ncard_vadd_signedNormBall_sub_le Λ 𝔪.inf σ
  have hn : 0 < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast finrank_pos)
  have hV := signedNormBall_volume_pos 𝔪 σ
  have hlim : Tendsto (fun T : ℝ => C * T ^ (-(finrank ℚ K : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hn).const_mul C
  obtain ⟨T, hT, hsmall⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hlim.eventually (Iio_mem_nhds hV))).exists
  refine ⟨T, hT, ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  by_contra hempty
  have hbound := hC T hT v
  rw [not_nonempty_iff_eq_empty.mp hempty, ncard_empty, Nat.cast_zero, zero_mul,
    zero_sub, abs_neg, abs_of_pos (mul_pos hT0 hV)] at hbound
  rw [sub_eq_add_neg, Real.rpow_add hT0, Real.rpow_one, mul_left_comm C T] at hbound
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hsmall hT0)) hbound

/-- Every invertible residue and real sign pattern has a nonzero integral representative. -/
theorem exists_integral_residue_sign
    (g : (𝓞 K ⧸ 𝔪.fin)ˣ × (𝔪.inf → ℤˣ)) :
    ∃ γ : 𝓞 K, algebraMap (𝓞 K) K γ ≠ 0 ∧ Ideal.Quotient.mk 𝔪.fin γ = g.1 ∧
      ∀ w : 𝔪.inf, 0 < ((g.2 w : ℤ) : ℝ) *
        InfinitePlace.embedding_of_isReal w.1.2 (γ : K) := by
  have hI0 : (1 : Ideal (𝓞 K)) ≠ ⊥ := one_ne_zero
  have hI : (1 : Ideal (𝓞 K)) ⊔ 𝔪.fin = ⊤ := by simp only [Ideal.one_eq_top, top_sup_eq]
  let Λ := idealLattice K (idealUnit (mul_ne_zero 𝔪.fin_ne_bot hI0))
  obtain ⟨T, hT, hpoint⟩ := exists_lattice_point_in_signedNormBall_coset 𝔪 Λ g.2
    (-mixedEmbedding K (residueRep 𝔪 hI g.1 : K))
  have hcone : (conePoints 𝔪 1 g T).Nonempty := by
    rw [conePoints_eq_image hI0 hI (lt_of_lt_of_le zero_lt_one hT)]
    exact hpoint.image _
  obtain ⟨_, hcone, γ, rfl, _, hcond⟩ := hcone
  have hγ0 : algebraMap (𝓞 K) K γ ≠ 0 := by
    intro hzero
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have h := normAtPlace_pos_of_mem hcone w
    rw [show (γ : K) = algebraMap (𝓞 K) K γ from rfl, hzero] at h
    simp at h
  exact ⟨γ, hγ0, hcond.2.1, hcond.2.2⟩

/-- Finite residues and real signs can be prescribed independently in `K_𝔪`. -/
theorem rayHom_surjective : Function.Surjective (rayHom 𝔪) := by
  intro g
  obtain ⟨γ, hγ0, hres, hsign⟩ := exists_integral_residue_sign 𝔪 g
  have hunit : IsUnit (Ideal.Quotient.mk 𝔪.fin γ) := hres ▸ g.1.isUnit
  have hγ := fun v hv => not_mem_of_isUnit_mk 𝔪 hunit v hv
  refine ⟨⟨_, mk0_mem_primeToUnits 𝔪 hγ0 hγ⟩, ?_⟩
  rw [rayHom_algebraMap 𝔪 hγ0 hγ]
  refine Prod.ext (Units.ext ?_) ((signAtInf_eq_iff 𝔪 _ _).mpr hsign)
  rw [coe_unitMod, hres]

end GaloisForLFunctions.HeckeLFunctions

