import GaloisForLFunctions.HTGeometry.LinearSpectralRelationOrbitPolynomial
import GaloisForLFunctions.HTGeometry.ComplexSpectralCoefficientPolynomialGenericity
import GaloisForLFunctions.HTGeometry.ComplexPolynomialRealParameterGenericity

/-!
# Pulling the linear-relation obstruction through a characteristic-coefficient family

The labeling-orbit obstruction of a real linear spectral relation is a polynomial in the elementary
symmetric functions of the spectrum.  Composing it with the signed characteristic coefficients of a
polynomial matrix family turns it into a polynomial in the *parameters*.  One spectrum escaping
every relabeling of the relation therefore certifies that this parameter polynomial is nonzero —
which is what makes "no identical real relation" a global statement, with no connectedness of the
simple-spectrum locus and no monodromy.

This mirrors `complexSpectralCoefficientObstructionPullback` for balanced *integer* characters.

## Main results

* `linearRelationObstructionPullback` — the pullback.
* `eval_linearRelationObstructionPullback` — evaluation of the pullback.
* `linearRelationObstructionPullback_ne_zero` — one escaping spectrum makes it nonzero.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pull the real linear-relation obstruction through a complex characteristic-coefficient
family. -/
def linearRelationObstructionPullback {θ I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) :
    MvPolynomial θ ℂ :=
  MvPolynomial.aeval coefficient ((linearRelationCoefficient c).map Complex.ofRealHom)

theorem eval_linearRelationObstructionPullback {θ I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ) (z : θ → ℂ) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (linearRelationObstructionPullback coefficient c)
      = MvPolynomial.eval₂ Complex.ofRealHom
          (fun i => MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient i))
          (linearRelationCoefficient c) := by
  unfold linearRelationObstructionPullback
  change
    (MvPolynomial.aeval z)
        (MvPolynomial.aeval coefficient
          ((linearRelationCoefficient c).map Complex.ofRealHom)) = _
  rw [MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

/-- Evaluating a real polynomial through the real-to-complex cast is the cast of its real
evaluation. -/
theorem eval₂_ofRealHom_eq {θ : Type*} (g : θ → ℝ) (P : MvPolynomial θ ℝ) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun i => ((g i : ℝ) : ℂ)) P
      = ((MvPolynomial.eval g P : ℝ) : ℂ) := by
  have h := MvPolynomial.hom_eval₂ P (RingHom.id ℝ) Complex.ofRealHom g
  rw [MvPolynomial.eval₂_id, RingHom.comp_id] at h
  exact h.symm

/-- **The value of the parameter obstruction is the labeling-orbit obstruction of the spectrum.** -/
theorem eval_linearRelationObstructionPullback_value {θ I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ)
    (z : θ → ℂ) (energy : I → ℝ)
    (hcoeff : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient j)
        = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ)) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (linearRelationObstructionPullback coefficient c)
      = ((linearRelationOrbitValue c energy : ℝ) : ℂ) := by
  have hval := eval_linearRelationObstructionPullback coefficient c z
  rw [funext hcoeff, eval₂_ofRealHom_eq, eval_linearRelationCoefficient_esymm] at hval
  exact hval

/-- **One escaping spectrum makes the parameter obstruction a nonzero polynomial.** -/
theorem linearRelationObstructionPullback_ne_zero {θ I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) {c : I → ℝ}
    (z₀ : θ → ℂ) (energy : I → ℝ)
    (hcoeff : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z₀ (coefficient j)
        = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hesc : ∀ σ : Equiv.Perm I, ∑ i, c i * energy (σ i) ≠ 0) :
    linearRelationObstructionPullback coefficient c ≠ 0 := by
  intro h0
  have hval := eval_linearRelationObstructionPullback_value coefficient c z₀ energy hcoeff
  rw [h0, MvPolynomial.eval₂_zero] at hval
  have hne : linearRelationOrbitValue c energy ≠ 0 :=
    (linearRelationOrbitValue_ne_zero_iff c energy).mpr hesc
  exact hne (by exact_mod_cast hval.symm)

/-- Conversely, at any parameter where the relation itself vanishes the pullback obstruction
vanishes: the identity relabeling is one of its factors. -/
theorem eval_linearRelationObstructionPullback_eq_zero {θ I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial θ ℂ) (c : I → ℝ)
    (z : θ → ℂ) (energy : I → ℝ)
    (hcoeff : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z (coefficient j)
        = ((MvPolynomial.eval energy (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hrel : ∑ i, c i * energy i = 0) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (linearRelationObstructionPullback coefficient c) = 0 := by
  classical
  have hval := eval_linearRelationObstructionPullback_value coefficient c z energy hcoeff
  have hzero : linearRelationOrbitValue c energy = 0 := by
    have hfac : ¬ ∀ σ : Equiv.Perm I, ∑ i, c i * energy (σ i) ≠ 0 := by
      intro hall
      exact hall (Equiv.refl I) (by simpa using hrel)
    by_contra hne
    exact hfac ((linearRelationOrbitValue_ne_zero_iff c energy).mp hne)
  rw [hval, hzero]
  simp

open Set in
/-- **(L2), in the form the metric-recurrence card needs.**  If one parameter value carries a
spectrum escaping every relabeling of the real relation `c`, then `c` cannot annihilate the
spectrum throughout *any* nonempty open set of parameters.

No connectedness of the simple-spectrum locus is used: the obstruction is a genuine polynomial in
the parameters, so vanishing on a nonempty open set would force it to vanish everywhere. -/
theorem not_relation_on_open_of_escape {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ) {c : I → ℝ}
    (z₀ : Fin m → ℝ) (energy₀ : I → ℝ)
    (hcoeff₀ : ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (z₀ i : ℂ)) (coefficient j)
        = ((MvPolynomial.eval energy₀ (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hesc : ∀ σ : Equiv.Perm I, ∑ i, c i * energy₀ (σ i) ≠ 0)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hspec : ∀ q ∈ U, ∀ j : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (q i : ℂ)) (coefficient j)
        = ((MvPolynomial.eval (spec q) (MvPolynomial.esymm I ℝ (j.1 + 1)) : ℝ) : ℂ))
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = 0) : False := by
  classical
  set P : MvPolynomial (Fin m) ℂ := linearRelationObstructionPullback coefficient c with hP
  have hwitness : ∀ _ : ℕ, ∃ x : Fin m → ℝ,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun i => (x i : ℂ)) P ≠ 0 := by
    intro _
    refine ⟨z₀, ?_⟩
    rw [hP, eval_linearRelationObstructionPullback_value coefficient c
      (fun i => (z₀ i : ℂ)) energy₀ hcoeff₀]
    have hne : linearRelationOrbitValue c energy₀ ≠ 0 :=
      (linearRelationOrbitValue_ne_zero_iff c energy₀).mpr hesc
    exact_mod_cast hne
  obtain ⟨hdense, -, -⟩ :=
    complexPolynomialRealAvoidanceSet_dense_residual_fullMeasure (fun _ : ℕ => P) hwitness
  obtain ⟨q, hqavoid, hqU⟩ := hdense.exists_mem_open hU hUne
  exact hqavoid 0 (eval_linearRelationObstructionPullback_eq_zero coefficient c
    (fun i => (q i : ℂ)) (spec q) (hspec q hqU) (hrel q hqU))

end

end GaloisForLFunctions.HTGeometry
