import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! Inertia at a finite normal level lifts to absolute inertia. First correct an
extension so that it fixes the valuation, then cancel its action on the residue
field by an automorphism fixing the finite field extension. -/

noncomputable section

open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal NumberField
open scoped Pointwise

namespace GlobalTheory.InertiaLift

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

private theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, hst⟩ := exists_den F A hx
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr ((apply_mem_iff_of_mem_Dec hσ s).mpr
      (mem_of_isIntegral_int A hs))) ?_
    rw [← not_lt, valuation_apply_lt_one_iff hσ, hs1]
    exact lt_irrefl 1
  have hst' : σ s * σ x = σ t := by rw [← map_mul, hst]
  have hfactor : σ s * (σ x - x) = (σ t - t) + x * (s - σ s) := by
    rw [← hst', ← hst]
    ring
  have hmul : A.valuation (σ s * (σ x - x)) < 1 := by
    rw [hfactor]
    refine Valuation.map_add_lt _ (h t ht) ?_
    rw [map_mul, Valuation.map_sub_swap]
    exact (mul_le_of_le_one_left' hx).trans_lt (h s hs)
  rwa [map_mul, hσs, one_mul] at hmul

private theorem exists_valuation_conjugate {A B : ValuationSubring Ω}
    (h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ B.valuation (algebraMap F Ω x) < 1) :
    ∃ g : G F Ω, ∀ y, B.valuation (g y) < 1 ↔ A.valuation y < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  letI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  letI := continuousSMul_intCl F Ω
  letI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := G F Ω) (primeBelow (F := F) A) (primeBelow (F := F) B) (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      exact h x)
  have he : g • A = B := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) B
    rw [primeBelow_smul, hg]
  refine ⟨g, fun y => ?_⟩
  rw [← he, smul_valuation_lt_one_iff, show (g⁻¹ : G F Ω) (g y) = y from g.symm_apply_apply y]

private def integralRingEquiv (s : Ω ≃+* Ω) : IntCl F Ω ≃+* IntCl F Ω where
  toFun b := ⟨s b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.toRingHom.toIntAlgHom)⟩
  invFun b := ⟨s.symm b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_int_of_isIntegral b.2).map s.symm.toRingHom.toIntAlgHom)⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b)
  right_inv b := Subtype.ext (s.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul s (a : Ω) b)
  map_add' a b := Subtype.ext (map_add s (a : Ω) b)

private theorem exists_decomposition_congruent {A : ValuationSubring Ω} (s : Ω ≃+* Ω)
    (hs : ∀ y, A.valuation (s y) < 1 ↔ A.valuation y < 1)
    (h : ∀ x : 𝓞 F, A.valuation (s (algebraMap F Ω x) - algebraMap F Ω x) < 1) :
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (g b - s b) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  letI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  letI := continuousSMul_intCl F Ω
  letI := isInvariant_intCl F Ω
  let Q := primeBelow (F := F) A
  let s₀ : IntCl F Ω ≃+* IntCl F Ω := integralRingEquiv s
  have hmap : Q = Q.map (s₀ : IntCl F Ω →+* IntCl F Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    change b ∈ primeBelow (F := F) A ↔ s₀.symm b ∈ primeBelow (F := F) A
    rw [mem_primeBelow, mem_primeBelow, ← hs (s₀.symm b)]
    rw [show s (s₀.symm b : Ω) = (b : Ω) from s.apply_symm_apply b]
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (IntCl F Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q s₀ hmap) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk Q (s₀ (algebraMap _ _ x)) = Ideal.Quotient.mk Q (algebraMap _ _ x)
      rw [Ideal.Quotient.eq]
      exact h x)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := G F Ω) (Q.under (𝓞 F)) Q φ
  have hσQ' : σ • Q = Q := hσQ
  refine ⟨σ, ?_, fun b hb => ?_⟩
  · refine eq_of_valuation_lt_one_iff F fun z hz => ?_
    let z' : IntCl F Ω := ⟨z, hz.tower_top⟩
    change z' ∈ primeBelow (F := F) (σ • A) ↔ z' ∈ Q
    rw [primeBelow_smul, hσQ']
  · let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    have he : Ideal.Quotient.mk Q (σ • b') = Ideal.Quotient.mk Q (s₀ b') :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b')
    rw [Ideal.Quotient.eq] at he
    exact he

omit [IsAlgClosure F Ω] in
private theorem mem_Dec_of_lt {A : ValuationSubring Ω} {σ : G F Ω}
    (h : ∀ y, A.valuation (σ y) < 1 ↔ A.valuation y < 1) : σ ∈ Dec (F := F) A := by
  have hmem (y : Ω) : y ∈ A ↔ y = 0 ∨ ¬ A.valuation y⁻¹ < 1 := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
      rw [← A.valuation_le_one_iff, map_inv₀, inv_lt_one₀ h0, not_lt]
      simp [hy]
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hmem, hmem y,
    ← h, map_inv₀ σ, mul_inv_apply, map_eq_zero_iff _ (σ⁻¹ : G F Ω).injective]

/-- Every finite-level inertia automorphism lifts to one preserving the residue of
each element of the valuation ring of the algebraic closure. -/
theorem exists_mem_Ine_lift (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M]
    (τ : M ≃ₐ[F] M)
    (h : ∀ x : 𝓞 M,
      A.valuation (algebraMap M Ω (τ (x : M)) - algebraMap M Ω (x : M)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  letI : NumberField M := NumberField.of_module_finite F M
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  letI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  let σ₀ : G F Ω := τ.liftNormal Ω
  have h₀ (x : M) : σ₀ (algebraMap M Ω x) = algebraMap M Ω (τ x) := τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := exists_valuation_conjugate (F := M) (A := A) (B := σ₀⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔
      A.valuation (σ₀ (algebraMap M Ω (x : M))) < 1
    rw [h₀]
    have hx := h x
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₁ : G F Ω := σ₀ * g.restrictScalars F
  have h₁ (x : M) : σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
    rw [← h₀]
    exact congrArg σ₀ (g.commutes x)
  have hpres (y : Ω) : A.valuation (σ₁ y) < 1 ↔ A.valuation y < 1 := by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := exists_decomposition_congruent (F := M) (A := A) σ₁.toRingEquiv hpres (by
    intro x
    change A.valuation (σ₁ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₁]
    exact h x)
  have hinv (y : Ω) : A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₁, mem_Ine_of_integral (mem_Dec_of_lt fun y => ?_)
    (fun b hb => ?_), fun x => ?_⟩
  · change A.valuation (k.symm (σ₁ y)) < 1 ↔ A.valuation y < 1
    rw [hinv, hpres]
  · change A.valuation (k.symm (σ₁ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₁ (algebraMap M Ω x)) = _
    rw [h₁]
    exact k.symm.commutes (τ x)

end GlobalTheory.InertiaLift
