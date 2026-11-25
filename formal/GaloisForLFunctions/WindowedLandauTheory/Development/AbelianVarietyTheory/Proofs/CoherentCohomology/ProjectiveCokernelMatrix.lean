import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveCokernelSplitting
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span

/-! Matrix equations express projectivity of a cokernel after a coefficient quotient. -/

namespace GlobalTheory.SmoothDescent

/-- A finite matrix has projective cokernel if and only if it has a generalized inverse. -/
theorem projective_matrix_cokernel_iff {R : Type*} [CommRing R] {a b : ℕ}
    (Φ : Matrix (Fin a) (Fin b) R) :
    Module.Projective R ((Fin a → R) ⧸ LinearMap.range Φ.mulVecLin) ↔
      ∃ Ψ : Matrix (Fin b) (Fin a) R, Φ * Ψ * Φ = Φ := by
  rw [projective_cokernel_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
    have he : Matrix.toLin' Φ ∘ₗ g ∘ₗ Matrix.toLin' Φ = Matrix.toLin' Φ := hg
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_assoc] using he
  · rintro ⟨Ψ, hΨ⟩
    refine ⟨Ψ.mulVecLin, ?_⟩
    simpa only [Matrix.mulVecLin_mul, LinearMap.comp_assoc] using
      congrArg (fun M : Matrix (Fin a) (Fin b) R => M.mulVecLin) hΨ

/-- A semilinear presentation whose extra scalar relation vanishes over the
coefficient quotient presents the original projective module there. -/
theorem projective_cokernel_of_semilinear_presentation {R S P : Type*}
    [CommRing R] [CommRing S] [AddCommGroup P] [Module S P] [Module.Projective S P]
    {a b : ℕ} (Φ : Matrix (Fin a) (Fin b) R) (u : R) (π : R →+* S)
    (hπ : Function.Surjective π) (hu : π u = 0) (ε : (Fin a → R) →ₛₗ[π] P)
    (hε : Function.Surjective ε)
    (hkerε : ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w') :
    Module.Projective S ((Fin a → S) ⧸ LinearMap.range (Φ.map π).mulVecLin) := by
  let liftVec (n : ℕ) (x : Fin n → R) : Fin n → S := π ∘ x
  have hVec (n : ℕ) : Function.Surjective (liftVec n) := by
    intro x
    choose y hy using fun i => hπ (x i)
    exact ⟨y, funext hy⟩
  let p (i : Fin a) := ε (Pi.single i 1)
  let F := Fintype.linearCombination S p
  have hF (y : Fin a → R) : F (liftVec a y) = ε y := by
    rw [Fintype.linearCombination_apply]
    conv_rhs => rw [show y = ∑ i, y i • Pi.single i 1 from by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]]
    simp only [map_sum, map_smulₛₗ, liftVec, Function.comp_apply, p]
  have hFsurj : Function.Surjective F := by
    intro x
    obtain ⟨y, rfl⟩ := hε x
    exact ⟨liftVec a y, hF y⟩
  have hmul (w : Fin b → R) : liftVec a (Φ.mulVec w) = (Φ.map π).mulVecLin (liftVec b w) :=
    funext (RingHom.map_mulVec π Φ w)
  have hker : LinearMap.ker F = LinearMap.range (Φ.map π).mulVecLin := by
    ext x
    constructor
    · obtain ⟨y, rfl⟩ := hVec a x
      intro h
      change F (liftVec a y) = 0 at h
      obtain ⟨w, w', hy⟩ := (hkerε y).1 ((hF y).symm.trans h)
      refine ⟨liftVec b w, (hmul w).symm.trans ?_⟩
      rw [hy]
      funext i
      simp [liftVec, Pi.smul_apply, smul_eq_mul, hu]
    · rintro ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := hVec b v
      change F ((Φ.map π).mulVecLin (liftVec b w)) = 0
      rw [← hmul, hF]
      exact (hkerε _).2 ⟨w, 0, by simp⟩
  rw [← hker]
  exact Module.Projective.of_equiv' (LinearMap.quotKerEquivOfSurjective F hFsurj).symm

/-- A projective cokernel over a quotient gives a generalized inverse modulo
the generators of its defining ideal. -/
theorem exists_generalizedInverse_mod_generators {R S : Type*} [CommRing R] [CommRing S]
    {a b r : ℕ} (Φ : Matrix (Fin a) (Fin b) R) (π : R →+* S) (hπ : Function.Surjective π)
    (g : Fin r → R) (hker : RingHom.ker π = Ideal.span (Set.range g))
    (hp : Module.Projective S ((Fin a → S) ⧸ LinearMap.range (Φ.map π).mulVecLin)) :
    ∃ (Ψ : Matrix (Fin b) (Fin a) R) (E : Fin r → Matrix (Fin a) (Fin b) R),
      Φ * Ψ * Φ = Φ + ∑ k, g k • E k := by
  classical
  obtain ⟨Ψₛ, hΨₛ⟩ := (projective_matrix_cokernel_iff (Φ.map π)).1 hp
  choose ψ hψ using fun i j => hπ (Ψₛ i j)
  let Ψ : Matrix (Fin b) (Fin a) R := Matrix.of ψ
  have hmap : Ψ.map π = Ψₛ := Matrix.ext hψ
  have hprod : (Φ * Ψ * Φ).map π = Φ.map π := by
    simp only [Matrix.map_mul, hmap, hΨₛ]
  have hk (i : Fin a) (j : Fin b) : (Φ * Ψ * Φ - Φ) i j ∈ Ideal.span (Set.range g) := by
    rw [← hker, RingHom.mem_ker, Matrix.sub_apply, map_sub]
    exact sub_eq_zero.2 (congrArg (fun M : Matrix (Fin a) (Fin b) S => M i j) hprod)
  choose c hc using fun i j => (Submodule.mem_span_range_iff_exists_fun R).1 (hk i j)
  refine ⟨Ψ, fun k => Matrix.of fun i j => c i j k, ?_⟩
  ext i j
  have h := hc i j
  simp only [smul_eq_mul] at h
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [show ∑ k, g k * c i j k = ∑ k, c i j k * g k from
    Finset.sum_congr rfl fun _ _ => mul_comm _ _, h]
  exact (sub_add_cancel _ _).symm.trans (add_comm _ _)

end GlobalTheory.SmoothDescent
