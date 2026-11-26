import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedCohomologyRetractions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GradedTensorContraction

/-! Degree-preserving contractions identify each cohomology group with its
projected cocycle representatives. -/

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.CechDR.FiniteGradedComplex

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- The homogeneous term is the range of its degree projection. -/
abbrev term (G : FiniteGradedComplex K V) (n : ℕ) := LinearMap.range (G.π n)

theorem π_apply_term (G : FiniteGradedComplex K V) (n : ℕ) (x : G.term n) :
    G.π n x.1 = x.1 := by
  obtain ⟨_, z, rfl⟩ := x
  exact G.idem n z

/-- The differential carries each homogeneous term to the next. -/
def termMap (G : FiniteGradedComplex K V) (n : ℕ) : G.term n →ₗ[K] G.term (n + 1) :=
  (G.d ∘ₗ (G.term n).subtype).codRestrict _ fun x =>
    ⟨G.d x.1, (G.dπ n x.1).symm.trans (congrArg G.d (G.π_apply_term n x))⟩

/-- The three consecutive terms compute cohomology in degree `n + 1`. -/
def degreeShort (G : FiniteGradedComplex K V) (n : ℕ) : ShortComplex (ModuleCat K) :=
  ShortComplex.mk (ModuleCat.ofHom (G.termMap n)) (ModuleCat.ofHom (G.termMap (n + 1))) (by
    ext x
    exact Subtype.ext (G.dd x.1))

/-- Squaring the representative map of a contraction makes it a projection.
The additional homotopy is the original homotopy applied to those representatives. -/
theorem exists_idempotent_contraction (G : FiniteGradedComplex K V) :
    ∃ e h : V →ₗ[K] V,
      (∀ x, G.d (e x) = 0) ∧ (∀ x, e (G.d x) = 0) ∧ (∀ x, e (e x) = e x) ∧
      (∀ x, G.d (h x) + h (G.d x) + e x = x) ∧
      (∀ n x, h (G.π (n + 1) x) = G.π n (h x)) ∧
      (∀ n x, e (G.π n x) = G.π n (e x)) := by
  obtain ⟨e, h, hde, hed, he, hh, hπ⟩ := G.exists_contraction
  let p := e ∘ₗ e
  let H := h + h ∘ₗ e
  have hp (y : V) (hy : G.d y = 0) : e (e y) = e y := by
    simpa only [map_add, hed, hy, map_zero, zero_add] using congrArg e (he y)
  refine ⟨p, H, fun x => hde (e x), fun x => ?_, fun x => ?_, ?_, ?_, ?_⟩
  · change e (e (G.d x)) = 0
    rw [hed, map_zero]
  · change e (e (e (e x))) = e (e x)
    exact (hp (e (e x)) (hde (e x))).trans (hp (e x) (hde x))
  · intro x
    have he' : G.d (h (e x)) + e (e x) = e x := by
      simpa only [hde, map_zero, add_zero] using he (e x)
    calc
      G.d (H x) + H (G.d x) + p x =
          G.d (h x) + h (G.d x) + (G.d (h (e x)) + e (e x)) := by
            simp only [H, p, LinearMap.comp_apply, LinearMap.add_apply, map_add, hed, map_zero, add_zero]
            abel
      _ = x := (congrArg (G.d (h x) + h (G.d x) + ·) he').trans (he x)
  · intro n x
    simp only [H, LinearMap.comp_apply, LinearMap.add_apply, hπ, hh, map_add]
  · intro n x
    simp only [p, LinearMap.comp_apply, hπ]

/-- Pulling the representative projection back to one degree gives a linear model
for cohomology since on cycles its kernel consists exactly of boundaries. -/
theorem nonempty_homology_equiv_termRange (G : FiniteGradedComplex K V) (e h : V →ₗ[K] V)
    (hde : ∀ x, G.d (e x) = 0) (hed : ∀ x, e (G.d x) = 0)
    (hee : ∀ x, e (e x) = e x)
    (he : ∀ x, G.d (h x) + h (G.d x) + e x = x)
    (hh : ∀ n x, h (G.π (n + 1) x) = G.π n (h x))
    (hπ : ∀ n x, e (G.π n x) = G.π n (e x)) (n : ℕ) :
    Nonempty ((G.degreeShort n).homology ≃ₗ[K] LinearMap.range (e ∘ₗ G.π (n + 1))) := by
  let P := LinearMap.range (e ∘ₗ G.π (n + 1))
  let M := G.term (n + 1)
  let I : P →ₗ[K] M := P.subtype.codRestrict M fun x => by
    obtain ⟨_, y, rfl⟩ := x
    exact ⟨e y, (hπ (n + 1) y).symm⟩
  let Q : M →ₗ[K] P := (e ∘ₗ G.π (n + 1)).rangeRestrict ∘ₗ M.subtype
  have hQ (x : M) : (Q x).1 = e x.1 := congrArg e (G.π_apply_term (n + 1) x)
  have hI (x : P) : (I x).1 = x.1 := rfl
  refine nonempty_homology_equiv_of_retract (G.degreeShort n) I Q ?_ ?_ ?_ ?_
  · rintro ⟨_, y, rfl⟩
    exact Subtype.ext (hde (G.π (n + 1) y))
  · intro y
    apply Subtype.ext
    have hy : (G.termMap n y).1 = G.d y.1 := rfl
    exact (hQ (G.termMap n y)).trans ((congrArg e hy).trans (hed y.1))
  · rintro ⟨_, y, rfl⟩
    exact Subtype.ext ((hQ _).trans ((congrArg e (hI _)).trans (hee (G.π (n + 1) y))))
  · intro x hx hx'
    have hx₀ : G.d x.1 = 0 := congrArg Subtype.val hx
    have hx₁ : e x.1 = 0 := (hQ x).symm.trans (congrArg Subtype.val hx')
    have hy : G.π n (h x.1) = h x.1 :=
      (hh n x.1).symm.trans (congrArg h (G.π_apply_term (n + 1) x))
    refine ⟨⟨h x.1, ⟨h x.1, hy⟩⟩, Subtype.ext ?_⟩
    simpa only [hx₀, hx₁, map_zero, add_zero] using he x.1

end GlobalTheory.CechDR.FiniteGradedComplex
