import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedDehomogenization
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! The specialized kernel of a graded presentation is finite on every finitely presented chart. -/

open MvPolynomial
open scoped Pointwise

namespace GlobalTheory

private theorem finite_specialized_kernel {S F G : Type*} [CommRing S]
    [AddCommGroup F] [Module S F] [AddCommGroup G] [Module S G] (u : S) (f : F →ₗ[S] G)
    [Module.Finite S F] [Module.FinitePresentation S (QuotSMulTop u G)]
    (hreg : ∀ z : G, u • z = 0 → z = 0)
    (hsurj : ∀ z : G, ∃ (y : F) (w : G), f y = z + u • w)
    (hker : ∀ (y : F) (w : G), f y = u • w → ∃ k v : F, f k = 0 ∧ y = k + u • v) :
    Module.Finite S (QuotSMulTop u (LinearMap.ker f)) := by
  let K := LinearMap.ker f
  let A : Submodule S F := u • ⊤
  let B : Submodule S G := u • ⊤
  let ψ := B.mkQ ∘ₗ f
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨z, rfl⟩ := B.mkQ_surjective q
    obtain ⟨y, w, hy⟩ := hsurj z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, map_add, add_eq_left]
    exact (Submodule.Quotient.mk_eq_zero B).2
      (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hsup : K ⊔ A = LinearMap.ker ψ := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro y hy
        rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.1 hy, map_zero]
      · intro y hy
        obtain ⟨v, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    · intro y hy
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      obtain ⟨k, v, hk, rfl⟩ := hker y w hw.symm
      exact Submodule.add_mem_sup (LinearMap.mem_ker.2 hk)
        (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hinf : (K ⊓ A).comap K.subtype = u • (⊤ : Submodule S K) := by
    ext x
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
    constructor
    · rintro ⟨_, hx⟩
      obtain ⟨v, _, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      have hvK : v ∈ K := LinearMap.mem_ker.2 (hreg _ (by
        rw [← map_smul, hv]
        exact LinearMap.mem_ker.1 x.2))
      have hx' : x = u • (⟨v, hvK⟩ : K) := Subtype.ext hv.symm
      rw [hx']
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    · intro hx
      obtain ⟨v, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact ⟨(u • v).2, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩
  haveI : Module.Finite S ↥(K ⊔ A) := by
    rw [hsup]
    exact Module.Finite.iff_fg.2 (Module.FinitePresentation.fg_ker ψ hψ)
  haveI : Module.Finite S (K ⧸ (K ⊓ A).comap K.subtype) :=
    Module.Finite.equiv (LinearMap.quotientInfEquivSupQuotient K A).symm
  exact Module.Finite.equiv (Submodule.quotEquivOfEq _ _ hinf)

section

variable {ι R F G : Type*} [CommRing R]
  [AddCommGroup F] [Module R F] [Module (MvPolynomial ι R) F] [IsScalarTower R (MvPolynomial ι R) F]
  [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G]
  {D : ℤ → Submodule R F} {E : ℤ → Submodule R G}
  [PolyGradedSMul ι D] [PolyGradedSMul ι E] [DirectSum.Decomposition D] [DirectSum.Decomposition E]
  {f : F →ₗ[MvPolynomial ι R] G} (hf : IsGradedMap D E f) (i : ι)

omit [Module R F] [Module R G] [IsScalarTower R (MvPolynomial ι R) F]
  [IsScalarTower R (MvPolynomial ι R) G] in
private theorem exists_preimage_add_X_sub_one
    (hsat : ∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range f)
    (z : G) : ∃ (y : F) (w : G), f y = z + (X i - 1 : MvPolynomial ι R) • w := by
  obtain ⟨k, y, hy⟩ := hsat z
  obtain ⟨w, hw⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k z
  exact ⟨y, w, hy.trans hw⟩

include hf in
omit [IsScalarTower R (MvPolynomial ι R) F] in
private theorem exists_kernel_add_X_sub_one (y : F) (w : G)
    (hw : f y = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ (k v : F), f k = 0 ∧ y = k + (X i - 1 : MvPolynomial ι R) • v := by
  obtain ⟨n, hn⟩ := exists_homogeneous_add_X_sub_one_smul D i y
  obtain ⟨a, ha, v, hv⟩ := hn n le_rfl
  have ha' : f a = (X i - 1 : MvPolynomial ι R) • (w - f v) := by
    rw [smul_sub, ← hw, hv, map_add, map_smul, add_sub_cancel_right]
  obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul E i (hf ha) ha'
  obtain ⟨v', hv'⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) k a
  refine ⟨(X i : MvPolynomial ι R) ^ k • a, v - v', by rw [map_smul, hk], ?_⟩
  rw [hv, hv', smul_sub]
  abel

include hf in
omit [IsScalarTower R (MvPolynomial ι R) F] in
theorem finite_quotSMulTop_ker_of_graded
    [Module.Finite (MvPolynomial ι R) F]
    [Module.FinitePresentation (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) G)]
    (hsat : ∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range f) :
    Module.Finite (MvPolynomial ι R) (QuotSMulTop (X i - 1 : MvPolynomial ι R) (LinearMap.ker f)) :=
  finite_specialized_kernel _ f (fun _ => eq_zero_of_X_sub_one_smul_eq_zero E i)
    (exists_preimage_add_X_sub_one i hsat) (exists_kernel_add_X_sub_one hf i)

include hf in
omit [IsScalarTower R (MvPolynomial ι R) F] in
/-- A graded map whose kernel and cokernel are killed elementwise by powers of a
coordinate becomes an isomorphism after setting that coordinate equal to one. -/
theorem bijective_specialization_of_saturating
    (hker : ∀ y : F, f y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0)
    (hsat : ∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range f) :
    Function.Bijective (QuotSMulTop.map (X i - 1 : MvPolynomial ι R) f) := by
  let u : MvPolynomial ι R := X i - 1
  let A : Submodule (MvPolynomial ι R) F := u • ⊤
  let B : Submodule (MvPolynomial ι R) G := u • ⊤
  have ha (v : F) : A.mkQ (u • v) = 0 := (Submodule.Quotient.mk_eq_zero A).2
    (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  have hb (w : G) : B.mkQ (u • w) = 0 := (Submodule.Quotient.mk_eq_zero B).2
    (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨y, rfl⟩ := A.mkQ_surjective q
    change B.mkQ (f y) = 0 at hq
    obtain ⟨w, _, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1
      ((Submodule.Quotient.mk_eq_zero B).1 hq)
    obtain ⟨k, v, hk, hy⟩ := exists_kernel_add_X_sub_one hf i y w hw.symm
    obtain ⟨n, hn⟩ := hker k hk
    obtain ⟨v', hv'⟩ := exists_pow_smul_eq_add_sub_one_smul (X i : MvPolynomial ι R) n k
    have h := congrArg A.mkQ (hn.symm.trans hv')
    rw [map_zero, map_add, ha, add_zero] at h
    change A.mkQ y = 0
    rw [hy, map_add, ha, add_zero, ← h]
  · intro z
    obtain ⟨z, rfl⟩ := B.mkQ_surjective z
    obtain ⟨y, w, hy⟩ := exists_preimage_add_X_sub_one i hsat z
    refine ⟨A.mkQ y, ?_⟩
    change B.mkQ (f y) = B.mkQ z
    rw [hy, map_add, hb, add_zero]

end

end GlobalTheory
