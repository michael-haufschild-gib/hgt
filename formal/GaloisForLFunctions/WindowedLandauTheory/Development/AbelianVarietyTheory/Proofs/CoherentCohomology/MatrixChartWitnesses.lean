import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveCokernelMatrix
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FinitePresentation

/-! A projective module on a smooth chart supplies finite equations for its presentation. -/

namespace GlobalTheory.SmoothDescent

/-- Relations for a smooth coefficient quotient, its scalar specialization and
a projective module on it all admit finite matrix witnesses. -/
theorem exists_chart_witnesses {R S B P : Type} [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Algebra.FinitePresentation R S] [Algebra.Smooth R B]
    [AddCommGroup P] [Module B P] [Module.Projective B P]
    {a b : ℕ} (Φ : Matrix (Fin a) (Fin b) S) (u : S) (π : S →ₐ[R] B)
    (hπ : Function.Surjective π) (hu : π u = 0) (ε : (Fin a → S) →ₛₗ[π.toRingHom] P)
    (hε : Function.Surjective ε)
    (hkerε : ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w') :
    ∃ (r : ℕ) (g : Fin r → S), Algebra.FormallySmooth R (S ⧸ Ideal.span (Set.range g)) ∧
      (∃ c : Fin r → S, u = ∑ k, c k * g k) ∧
      (∀ k, ∃ (C : Matrix (Fin b) (Fin a) S) (C' : Matrix (Fin a) (Fin a) S),
        g k • (1 : Matrix (Fin a) (Fin a) S) = Φ * C + u • C') ∧
      (∃ (Ψ : Matrix (Fin b) (Fin a) S) (E : Fin r → Matrix (Fin a) (Fin b) S),
        Φ * Ψ * Φ = Φ + ∑ k, g k • E k) := by
  classical
  have hfg := Algebra.FinitePresentation.ker_fG_of_surjective π hπ
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hker : RingHom.ker π.toRingHom = Ideal.span (Set.range g) := hg.symm
  refine ⟨r, g, ?_, ?_, ?_, ?_⟩
  · have e : (S ⧸ RingHom.ker π.toRingHom) ≃ₐ[R] B :=
      Ideal.quotientKerAlgEquivOfSurjective hπ
    have hs : Algebra.FormallySmooth R (S ⧸ RingHom.ker π.toRingHom) :=
      Algebra.FormallySmooth.of_equiv e.symm
    rwa [hker] at hs
  · have hmem : u ∈ Ideal.span (Set.range g) := hker ▸ (RingHom.mem_ker.2 hu)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hmem
    exact ⟨c, by simpa only [smul_eq_mul] using hc.symm⟩
  · intro k
    have hgk : π (g k) = 0 :=
      RingHom.mem_ker.1 (hker.symm ▸ Ideal.subset_span ⟨k, rfl⟩)
    have hcol (m : Fin a) : ∃ w w',
        g k • (Pi.single m 1 : Fin a → S) = Φ.mulVec w + u • w' := by
      apply (hkerε _).1
      rw [LinearMap.map_smulₛₗ]
      change π (g k) • ε (Pi.single m 1) = 0
      rw [hgk, zero_smul]
    choose w w' hw using hcol
    refine ⟨Matrix.of fun j m => w m j, Matrix.of fun l m => w' m l, ?_⟩
    ext l m
    have h := congrFun (hw m) l
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply] at h
    simp only [Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.of_apply, smul_eq_mul]
    rw [h]
    simp only [Matrix.mulVec, dotProduct]
  · exact exists_generalizedInverse_mod_generators Φ π.toRingHom hπ g hker
      (projective_cokernel_of_semilinear_presentation Φ u π.toRingHom hπ hu ε hε hkerε)

end GlobalTheory.SmoothDescent
