import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedCotangentMatrix
import Mathlib.RingTheory.Etale.Kaehler

/-! Cotangent coordinates at an evaluation are unchanged by
localizing at elements invertible there or by an algebra isomorphism. -/

noncomputable section

open KaehlerDifferential

namespace GlobalTheory.W1.HasCotangentRows

variable {k A B : Type} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {d : ℕ} {u v : Fin d → A} {M : Matrix (Fin d) (Fin d) k}

/-- Localize both parameter families and the cotangent value map at
an evaluation extending to the localization. -/
theorem localization [Algebra A B] [IsScalarTower k A B]
    (S : Submonoid A) [IsLocalization S B]
    {e : A →ₐ[k] k} {e' : B →ₐ[k] k} (he : ∀ b, e' (algebraMap A B b) = e b)
    (h : HasCotangentRows e u v M) :
    HasCotangentRows e' (fun l => algebraMap A B (u l)) (fun l => algebraMap A B (v l)) M := by
  obtain ⟨φ, hφ, hu, hv, hker⟩ := h
  let P := Fin d → k
  letI : Module B P := Module.compHom P e'.toRingHom
  letI : Module A P := Module.compHom P e.toRingHom
  have hA (a : A) (z : P) : a • z = e a • z := rfl
  have hB (b : B) (z : P) : b • z = e' b • z := rfl
  letI : IsScalarTower A B P := ⟨fun a b z => by
    rw [Algebra.smul_def, hB, hB, hA, map_mul, he, mul_smul]⟩
  letI : IsScalarTower k B P := ⟨fun a b z => by
    rw [Algebra.smul_def, hB, hB, map_mul, e'.commutes, mul_smul]
    simp⟩
  let φ₀ : Ω[A⁄k] →ₗ[A] P := ⟨⟨φ, φ.map_add⟩, hφ⟩
  let f := KaehlerDifferential.map k k A B
  letI : IsLocalizedModule S f := KaehlerDifferential.isLocalizedModule_map k A B S
  let hl := IsLocalizedModule.isBaseChange S B f
  let ψ : Ω[B⁄k] →ₗ[B] P := hl.lift φ₀
  have hψ (ω : Ω[A⁄k]) : ψ (f ω) = φ ω := hl.lift_eq φ₀ ω
  have hD (a : A) : ψ (D k B (algebraMap A B a)) = φ (D k A a) := by
    rw [← hψ, show f (D k A a) = D k B (algebraMap A B a) by
      simp only [f, KaehlerDifferential.map_D]]
  refine ⟨ψ.restrictScalars k, fun b ω => ψ.map_smul b ω,
    fun l => (hD _).trans (hu l), fun l => (hD _).trans (hv l), ?_⟩
  intro ω hω
  have hω' : ψ ω = 0 := hω
  obtain ⟨⟨ω₀, a⟩, ha⟩ := IsLocalizedModule.surj S f ω
  have ha' : algebraMap A B (a : A) • ω = f ω₀ := by
    rw [algebraMap_smul]
    exact ha
  have h₀ : φ ω₀ = 0 := by rw [← hψ, ← ha', map_smul, hω', smul_zero]
  obtain ⟨n, b, w, hb, rfl⟩ := hker ω₀ h₀
  obtain ⟨c, hc⟩ := (IsLocalization.map_units B a).exists_left_inv
  refine ⟨n, fun j => algebraMap A B (b j), fun j => c • f (w j), fun j => (he _).trans (hb j), ?_⟩
  have hw : ω = c • (algebraMap A B (a : A) • ω) := by rw [smul_smul, hc, one_smul]
  rw [hw, ha', map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← algebraMap_smul B (b j), smul_comm]

/-- An algebra isomorphism carrying one evaluation to the other
carries the two families of differential values with it. -/
theorem algEquiv (ρ : A ≃ₐ[k] B) {e : A →ₐ[k] k} {e' : B →ₐ[k] k}
    (he : ∀ a, e' (ρ a) = e a) (h : HasCotangentRows e u v M) :
    HasCotangentRows e' (fun j => ρ (u j)) (fun j => ρ (v j)) M := by
  letI : Algebra A B := ρ.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun a => (ρ.commutes a).symm
  letI : IsLocalization (⊥ : Submonoid A) B := by
    refine IsLocalization.of_le_isUnit_of_bijective ?_ ρ.bijective
    simp [Algebra.algebraMapSubmonoid]
  have he' (a : A) : e' (algebraMap A B a) = e a := he a
  exact localization (⊥ : Submonoid A) he' h

end GlobalTheory.W1.HasCotangentRows
