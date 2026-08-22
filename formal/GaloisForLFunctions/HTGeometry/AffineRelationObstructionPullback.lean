import GaloisForLFunctions.HTGeometry.AffineSpectralRelationOrbitPolynomial
import GaloisForLFunctions.HTGeometry.RealRelationRootPacketBridge

/-!
# Pulling the affine labeling-orbit obstruction through a characteristic-coefficient family

`LinearRelationObstructionPullback` and `RealRelationRootPacketBridge` do this for a homogeneous
relation.  A relation that is merely *constant* on a parameter chart is affine, and its obstruction
is symmetric for exactly the same reason, so the same pullback works verbatim with the constant
carried along.

## Main results

* `affineRelationObstructionPullback`, `eval_affineRelationObstructionPullback_value`.
* `not_affineRelation_on_open_of_escape` — **(L2') for a characteristic-coefficient family.**
* `not_affineRelation_on_open_of_rootPacket_escape` — **(L2') for a polynomial matrix family.**
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pull the affine relation obstruction through a complex characteristic-coefficient family. -/
def affineRelationObstructionPullback {θ I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) (target : ℝ) :
    MvPolynomial θ ℂ :=
  MvPolynomial.aeval coefficient ((affineRelationCoefficient c target).map Complex.ofRealHom)

theorem eval_affineRelationObstructionPullback {θ I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) (target : ℝ) (z : θ → ℂ) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (affineRelationObstructionPullback coefficient c target)
      = MvPolynomial.eval₂ Complex.ofRealHom
          (fun i => MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient i))
          (affineRelationCoefficient c target) := by
  unfold affineRelationObstructionPullback
  change
    (MvPolynomial.aeval z)
        (MvPolynomial.aeval coefficient
          ((affineRelationCoefficient c target).map Complex.ofRealHom)) = _
  rw [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

/-- **The value of the parameter obstruction is the labeling-orbit obstruction of the spectrum.** -/
theorem eval_affineRelationObstructionPullback_value {θ I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) (target : ℝ)
    (z : θ → ℂ) (energy : I → ℝ)
    (hcoeff : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient j)
        = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ)) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (affineRelationObstructionPullback coefficient c target)
      = ((affineRelationOrbitValue c target energy : ℝ) : ℂ) := by
  have hval := eval_affineRelationObstructionPullback coefficient c target z
  rw [funext hcoeff, eval₂_ofRealHom_eq, eval_affineRelationCoefficient_esymm] at hval
  exact hval

/-- Wherever the affine relation itself holds, the obstruction vanishes: the identity relabeling is
one of its factors. -/
theorem eval_affineRelationObstructionPullback_eq_zero {θ I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) (target : ℝ)
    (z : θ → ℂ) (energy : I → ℝ)
    (hcoeff : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient j)
        = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hrel : ∑ i, c i * energy i = target) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z
      (affineRelationObstructionPullback coefficient c target) = 0 := by
  classical
  have hval := eval_affineRelationObstructionPullback_value coefficient c target z energy hcoeff
  have hzero : affineRelationOrbitValue c target energy = 0 := by
    have hfac : ¬ ∀ σ : Equiv.Perm I, ∑ i, c i * energy (σ i) ≠ target := by
      intro hall
      exact hall (Equiv.refl I) (by simpa using hrel)
    by_contra hne
    exact hfac ((affineRelationOrbitValue_ne_zero_iff c target energy).mp hne)
  rw [hval, hzero]
  simp

open Set in
/-- **(L2'), for a characteristic-coefficient family.**  If one parameter value carries a spectrum on
which every relabeling of the relation misses the target, then the relation cannot take that
constant value throughout any nonempty open set of parameters. -/
theorem not_affineRelation_on_open_of_escape {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ) {c : I → ℝ} {target : ℝ}
    (z₀ : Fin m → ℝ) (energy₀ : I → ℝ)
    (hcoeff₀ : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (z₀ i : ℂ)) (coefficient j)
        = ((MvPolynomial.eval energy₀ (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hesc : ∀ σ : Equiv.Perm I, ∑ i, c i * energy₀ (σ i) ≠ target)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hspec : ∀ q ∈ U, ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (q i : ℂ)) (coefficient j)
        = ((MvPolynomial.eval (spec q) (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = target) : False := by
  classical
  set P : MvPolynomial (Fin m) ℂ := affineRelationObstructionPullback coefficient c target with hP
  have hwitness : ∀ _ : ℕ, ∃ x : Fin m → ℝ,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (x i : ℂ)) P ≠ 0 := by
    intro _
    refine ⟨z₀, ?_⟩
    rw [hP, eval_affineRelationObstructionPullback_value coefficient c target
      (fun i => (z₀ i : ℂ)) energy₀ hcoeff₀]
    have hne : affineRelationOrbitValue c target energy₀ ≠ 0 :=
      (affineRelationOrbitValue_ne_zero_iff c target energy₀).mpr hesc
    exact_mod_cast hne
  obtain ⟨hdense, -, -⟩ :=
    complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure (fun _ : ℕ => P) hwitness
  obtain ⟨q, hqavoid, hqU⟩ := hdense.exists_mem_open hU hUne
  exact hqavoid 0 (eval_affineRelationObstructionPullback_eq_zero coefficient c target
    (fun i => (q i : ℂ)) (spec q) (hspec q hqU) (hrel q hqU))

/-- **(L2') for a polynomial matrix family.**  If one real parameter carries a simple root packet on
which every relabeling of the relation misses the target, then the relation cannot take that
constant value throughout any nonempty open set of parameters. -/
theorem not_affineRelation_on_open_of_rootPacket_escape
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) {c : I → ℝ} {target : ℝ}
    (p₀ : Fin m → ℝ) (energy₀ : I → ℝ)
    (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p₀ t : ℂ))),
          ((energy₀ i : ℝ) : ℂ)) = 0)
    (hesc : ∀ σ : Equiv.Perm I, ∑ i, c i * energy₀ (σ i) ≠ target)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hrootq : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))),
          ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = target) : False := by
  classical
  have hbridge : ∀ (q : Fin m → ℝ) (e : I → ℝ),
      Function.Injective e →
      (∀ i, matrixCharpolyRelation
        (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (q t : ℂ))),
          ((e i : ℝ) : ℂ)) = 0) →
      ∀ j : Fin (Fintype.card I),
        MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (q i : ℂ))
            (matrixCharacteristicElementaryPolynomial M j)
          = ((MvPolynomial.eval e (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ) := by
    intro q e he hr j
    rw [eval_matrixCharacteristicElementaryPolynomial]
    rw [matrixCharacteristicElementaryCoefficient_eq_rootPacket _ (fun i => ((e i : ℝ) : ℂ))
      (fun a b h => he (Complex.ofReal_injective h)) hr j]
    exact esymm_eval₂_cast e (j.1 + 1)
  exact not_affineRelation_on_open_of_escape (matrixCharacteristicElementaryPolynomial M) p₀ energy₀
    (hbridge p₀ energy₀ hinj₀ hroot₀) hesc hU hUne spec
    (fun q hq => hbridge q (spec q) (hinj q hq) (hrootq q hq)) hrel

end

end GaloisForLFunctions.HTGeometry
