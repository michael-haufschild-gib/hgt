import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.KrullTopology

/-!
# Compactness of the automorphism group of a normal algebraic extension

For a normal algebraic extension `E / F` the restriction map to the separable closure is a group
isomorphism onto `Gal (F^sep / F)`: it is surjective because `E / F` is normal, and injective
because `E / F^sep` is purely inseparable, so an automorphism fixing `F^sep` satisfies
`σ (a) ^ {q^n} = a ^ {q^n}` and hence `σ (a) = a`.  The inverse is continuous — a finite
subextension of `E` is fixed as soon as finitely many `q^n`-th powers in `F^sep` are — so the
automorphism group is the continuous image of a compact group, hence compact.  This removes the
`IsGalois` hypothesis from mathlib's compactness instance.
-/

namespace HTGeometry

open IntermediateField AlgEquiv

universe u v

theorem expChar_of_algebra (F : Type u) [Field F] {E : Type v} [Field E] [Algebra F E]
    (q : ℕ) [ExpChar F q] : ExpChar E q :=
  expChar_of_injective_algebraMap (algebraMap F E).injective q

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Normal F E]

/-- An automorphism fixing the separable closure pointwise is the identity. -/
theorem algEquiv_eq_one_of_fixes_separableClosure (q : ℕ) [ExpChar F q] (σ : E ≃ₐ[F] E)
    (h : ∀ a : ↥(separableClosure F E), σ (a : E) = (a : E)) : σ = 1 := by
  haveI := expChar_of_algebra F (E := E) q
  haveI : ExpChar ↥(separableClosure F E) q :=
    expChar_of_algebra F (E := ↥(separableClosure F E)) q
  refine AlgEquiv.ext fun a => ?_
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem ↥(separableClosure F E) q a
  have hfix : σ (a ^ q ^ n) = a ^ q ^ n := by
    rw [← hb]
    exact h b
  rw [map_pow] at hfix
  have hinj : Function.Injective (iterateFrobenius E q n) :=
    (iterateFrobenius E q n).injective
  refine hinj ?_
  rw [iterateFrobenius_def, iterateFrobenius_def]
  simpa using hfix

/-- Restriction to the separable closure is injective on automorphisms. -/
theorem restrictNormalHom_separableClosure_injective (q : ℕ) [ExpChar F q] :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) ↥(separableClosure F E)) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  refine algEquiv_eq_one_of_fixes_separableClosure q σ fun a => ?_
  have h := congrArg (fun τ : ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E) => τ a) hσ
  have hres : (AlgEquiv.restrictNormalHom (F := F) (K₁ := E)
      ↥(separableClosure F E) σ) a = a := h
  have hcomm := AlgEquiv.restrictNormal_commutes σ ↥(separableClosure F E) a
  have hres' : σ.restrictNormal ↥(separableClosure F E) a = a := hres
  rw [hres'] at hcomm
  exact hcomm.symm

/-- Restriction to the separable closure is a group isomorphism. -/
noncomputable def restrictNormalMulEquiv (q : ℕ) [ExpChar F q] :
    (E ≃ₐ[F] E) ≃* (↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E)) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom ↥(separableClosure F E))
    ⟨restrictNormalHom_separableClosure_injective q,
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥(separableClosure F E)) (E := E)⟩

/-- The inverse of restriction to the separable closure is continuous: a finite subextension
`K = F(t)` of `E` is fixed as soon as the finitely many separable powers `x ^ q ^ n` of the
generators `x ∈ t` are, and those powers generate a finite subextension of `F^sep`. -/
theorem continuous_restrictNormalMulEquiv_symm (q : ℕ) [ExpChar F q] :
    Continuous ⇑(restrictNormalMulEquiv (F := F) (E := E) q).symm := by
  haveI := expChar_of_algebra F (E := E) q
  have hrestrict : ∀ τ : ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E),
      AlgEquiv.restrictNormalHom (F := F) (K₁ := E) ↥(separableClosure F E)
        ((restrictNormalMulEquiv (F := F) (E := E) q).symm τ) = τ :=
    fun τ => (restrictNormalMulEquiv (F := F) (E := E) q).apply_symm_apply τ
  have hpow : ∀ x : E, ∃ (n : ℕ) (b : ↥(separableClosure F E)),
      algebraMap (↥(separableClosure F E)) E b = x ^ q ^ n := by
    intro x
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem ↥(separableClosure F E) q x
    exact ⟨n, hn⟩
  choose nn bb hbb using hpow
  have key : ∀ U ∈ nhds (1 : E ≃ₐ[F] E),
      (⇑(restrictNormalMulEquiv (F := F) (E := E) q).symm) ⁻¹' U ∈
        nhds (1 : ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E)) := by
    intro U hU
    rw [krullTopology_mem_nhds_one_iff] at hU ⊢
    obtain ⟨K, hKfd, hKsub⟩ := hU
    obtain ⟨t, htfin, htK⟩ : ∃ t : Set E, t.Finite ∧ IntermediateField.adjoin F t = K := by
      refine IntermediateField.fg_def.1 ?_
      refine IntermediateField.fg_of_fg_toSubalgebra K ?_
      rw [Subalgebra.fg_iff_finiteType]
      infer_instance
    haveI : Finite ↥(bb '' t) := (htfin.image bb).to_subtype
    refine ⟨IntermediateField.adjoin F (bb '' t), ?_, ?_⟩
    · exact IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
    · intro τ hτ
      rw [Set.mem_preimage]
      refine hKsub ?_
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
      rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ
      set σ := (restrictNormalMulEquiv (F := F) (E := E) q).symm τ with hσ
      have hgen : ∀ x ∈ t, σ x = x := by
        intro x hx
        have hy : bb x ∈ IntermediateField.adjoin F (bb '' t) :=
          IntermediateField.subset_adjoin F _ ⟨x, hx, rfl⟩
        have h1 := AlgEquiv.restrictNormal_commutes σ ↥(separableClosure F E) (bb x)
        have h2 : σ.restrictNormal ↥(separableClosure F E) (bb x) = τ (bb x) :=
          congrArg (fun f : ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E) => f (bb x))
            (hrestrict τ)
        rw [h2, hτ _ hy, hbb x, map_pow] at h1
        have hinj : Function.Injective (iterateFrobenius E q (nn x)) :=
          (iterateFrobenius E q (nn x)).injective
        refine hinj ?_
        rw [iterateFrobenius_def, iterateFrobenius_def]
        exact h1.symm
      intro x hx
      rw [← htK] at hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx => exact hgen x hx
      | algebraMap x => exact σ.commutes x
      | add x y _ _ hx hy => rw [map_add, hx, hy]
      | inv x _ hx => rw [map_inv₀, hx]
      | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  refine continuous_of_continuousAt_one _ ?_
  have hone : (restrictNormalMulEquiv (F := F) (E := E) q).symm 1 = 1 := map_one _
  have hmain : Filter.Tendsto (⇑(restrictNormalMulEquiv (F := F) (E := E) q).symm)
      (nhds 1) (nhds 1) := Filter.tendsto_def.2 key
  exact hmain.mono_right (le_of_eq (congrArg nhds hone.symm))

/-- **The automorphism group of a normal algebraic extension is compact.**  It is the continuous
image of the compact group `Gal (F^sep / F)` under the inverse of restriction. -/
theorem compactSpace_algEquiv_of_normal : CompactSpace (E ≃ₐ[F] E) := by
  obtain ⟨q, hq⟩ := ExpChar.exists F
  haveI := hq
  constructor
  have hc := isCompact_range (continuous_restrictNormalMulEquiv_symm (F := F) (E := E) q)
  rwa [(restrictNormalMulEquiv (F := F) (E := E) q).symm.surjective.range_eq] at hc

instance : CompactSpace (E ≃ₐ[F] E) := compactSpace_algEquiv_of_normal

end HTGeometry
