import GaloisForLFunctions.HTGeometry.AlgebraSpectrumProper
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumEquiv

/-!
# Properness of finite maps on complex algebra spectra

For a module-finite map of complex algebras, every element upstairs satisfies a monic relation over
the base.  Cauchy's root bound controls its value uniformly above a compact family of base points.
The complex-point space is closed in the full function space, so Tychonoff compactness makes the
preimage of every compact base set compact.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace AlgSpec

variable {A B : Type*} [CommRing A] [CommRing B] [Nontrivial A] [Nontrivial B]
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]

private abbrev towerMap : A →ₐ[ℂ] B := IsScalarTower.toAlgHom ℂ A B

/-- A monic relation over an arbitrary complex base algebra bounds an upstairs point coordinate in
terms of the values of its coefficients at the projected base point. -/
theorem norm_apply_le_of_monic_over {b : B} {r : Polynomial A} (hr : r.Monic)
    (hb : Polynomial.aeval b r = 0) (χ : AlgSpec B) :
    ‖χ b‖ ≤ max 1
      (∑ i ∈ Finset.range r.natDegree,
        ‖(precomp (towerMap (A := A) (B := B)) χ) (r.coeff i)‖) := by
  by_cases hd : r.natDegree = 0
  · exfalso
    have h1 : r = 1 := Polynomial.eq_one_of_monic_natDegree_zero hr hd
    rw [h1, map_one] at hb
    exact (one_ne_zero : (1 : B) ≠ 0) hb
  have hroot : (r.map (precomp (towerMap (A := A) (B := B)) χ)).eval (χ b) = 0 := by
    rw [Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ r (algebraMap A B) χ.toRingHom b
    rw [Polynomial.aeval_def] at hb
    rw [hb, map_zero] at h
    exact h.symm
  have h := Bottcher.norm_root_le_of_monic (hr.map _) hroot (by
    rw [hr.natDegree_map]
    exact Nat.pos_of_ne_zero hd)
  rw [hr.natDegree_map] at h
  simpa [Polynomial.coeff_map] using h

/-- **Compact-preimage theorem for finite complex-algebra maps.** -/
theorem isCompact_preimage_precomp_of_finite [Module.Finite A B]
    {K : Set (AlgSpec A)} (hK : IsCompact K) :
    IsCompact (precomp (towerMap (A := A) (B := B)) ⁻¹' K) := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · simp [hKe]
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have hint : ∀ b : B, IsIntegral A b := fun b => Algebra.IsIntegral.isIntegral b
  choose r hrm hrz using hint
  set F : B → AlgSpec A → ℝ := fun b ψ =>
    max 1 (∑ i ∈ Finset.range (r b).natDegree, ‖ψ ((r b).coeff i)‖)
  have hFcont : ∀ b, Continuous (F b) := by
    intro b
    refine continuous_const.max ?_
    exact continuous_finsetSum _ fun i _ => (continuous_eval ((r b).coeff i)).norm
  have hmax : ∀ b, ∃ C : ℝ, ∀ ψ ∈ K, F b ψ ≤ C := by
    intro b
    obtain ⟨ψ₀, _, hψ₀⟩ := hK.exists_isMaxOn hKne (hFcont b).continuousOn
    exact ⟨F b ψ₀, fun ψ hψ => hψ₀ hψ⟩
  set C : B → ℝ := fun b => (hmax b).choose
  have hCspec : ∀ b, ∀ ψ ∈ K, F b ψ ≤ C b := fun b => (hmax b).choose_spec
  let restrictFun : (B → ℂ) → (A → ℂ) := fun φ a => φ (algebraMap A B a)
  have hrestrict : Continuous restrictFun :=
    continuous_pi fun a => continuous_apply (algebraMap A B a)
  have hcoeA : Continuous (fun ψ : AlgSpec A => (ψ : A → ℂ)) :=
    isEmbedding_coe.continuous
  have hKfun : IsCompact ((fun ψ : AlgSpec A => (ψ : A → ℂ)) '' K) :=
    hK.image hcoeA
  have himg :
      (fun χ : AlgSpec B => (χ : B → ℂ)) ''
          (precomp (towerMap (A := A) (B := B)) ⁻¹' K) =
        (Set.range fun χ : AlgSpec B => (χ : B → ℂ)) ∩
          restrictFun ⁻¹' ((fun ψ : AlgSpec A => (ψ : A → ℂ)) '' K) := by
    ext φ
    constructor
    · rintro ⟨χ, hχ, rfl⟩
      refine ⟨⟨χ, rfl⟩, ?_⟩
      exact ⟨precomp (towerMap (A := A) (B := B)) χ, hχ, rfl⟩
    · rintro ⟨⟨χ, rfl⟩, ⟨ψ, hψ, hfun⟩⟩
      refine ⟨χ, ?_, rfl⟩
      have heq : precomp (towerMap (A := A) (B := B)) χ = ψ := by
        apply DFunLike.ext _ _
        intro a
        exact (congrFun hfun a).symm
      change precomp (towerMap (A := A) (B := B)) χ ∈ K
      rw [heq]
      exact hψ
  have hclosed : IsClosed ((fun χ : AlgSpec B => (χ : B → ℂ)) ''
      (precomp (towerMap (A := A) (B := B)) ⁻¹' K)) := by
    rw [himg]
    exact isClosed_range_algSpec_coe.inter (hKfun.isClosed.preimage hrestrict)
  have hsub : (fun χ : AlgSpec B => (χ : B → ℂ)) ''
      (precomp (towerMap (A := A) (B := B)) ⁻¹' K) ⊆
      Set.univ.pi fun b => Metric.closedBall (0 : ℂ) (C b) := by
    rintro _ ⟨χ, hχ, rfl⟩ b _
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_apply_le_of_monic_over (hrm b) (hrz b) χ).trans (hCspec b _ hχ)
  have hcomp : IsCompact ((fun χ : AlgSpec B => (χ : B → ℂ)) ''
      (precomp (towerMap (A := A) (B := B)) ⁻¹' K)) :=
    (isCompact_univ_pi fun b => isCompact_closedBall (0 : ℂ) (C b)).of_isClosed_subset
      hclosed hsub
  exact isInducing_coe.isCompact_iff.mpr hcomp

/-- **A module-finite complex-algebra map is proper on complex points.** -/
theorem isProperMap_precomp_of_finite [Module.Finite A B]
    [CompactlyCoherentSpace (AlgSpec A)] :
    IsProperMap (precomp (towerMap (A := A) (B := B))) := by
  rw [isProperMap_iff_isCompact_preimage]
  exact ⟨continuous_precomp _, fun _ hK => isCompact_preimage_precomp_of_finite hK⟩

end AlgSpec

end

end GaloisForLFunctions.HTGeometry
