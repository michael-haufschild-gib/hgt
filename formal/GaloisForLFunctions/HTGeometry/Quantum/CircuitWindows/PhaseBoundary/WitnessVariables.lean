import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Projection
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Simultaneous elimination of finitely many real incidence variables -/
open Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

private def move_head (A : Type*) [CommRing A] (n : ℕ) :
    MvPolynomial (Fin (n+1)) A →+* MvPolynomial (Fin n) (Polynomial A) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Polynomial.C)
    (Fin.cases (MvPolynomial.C Polynomial.X) MvPolynomial.X)

private theorem eval_move_head {A : Type*} [CommRing A] {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) A) (φ : A →+* ℝ) (y : ℝ) (w : Fin n → ℝ) :
    MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom φ y) w (move_head A n p) =
      MvPolynomial.eval₂Hom φ (Fin.cases y w) p := by
  have he : (MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom φ y) w).comp (move_head A n) =
      MvPolynomial.eval₂Hom φ (Fin.cases y w) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [move_head]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [move_head]
  exact DFunLike.congr_fun he p

private theorem exists_move_head {A X : Type*} [CommRing A] (ρ : X → A →+* ℝ) {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) A) :
    Prod.fst '' {z : X × ℝ | ∃ w : Fin n → ℝ,
      MvPolynomial.eval₂Hom (appendEval ρ z) w (move_head A n p) = 0} =
      {x | ∃ w : Fin (n+1) → ℝ, MvPolynomial.eval₂Hom (ρ x) w p = 0} := by
  apply Set.ext
  intro x
  constructor
  · intro h
    obtain ⟨⟨a,y⟩,hw,hx⟩ := h
    change a = x at hx
    subst a
    obtain ⟨w,hw⟩ := hw
    change MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom (ρ x) y) w (move_head A n p) = 0 at hw
    refine ⟨Fin.cases y w,?_⟩
    rw [←eval_move_head p (ρ x) y w]
    exact hw
  · rintro ⟨w,hw⟩
    let v : Fin n → ℝ := fun j => w j.succ
    have he : Fin.cases (w 0) v = w := funext fun i => Fin.cases rfl (fun _ => rfl) i
    refine ⟨(x,w 0),?_,rfl⟩
    refine ⟨v,?_⟩
    change MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom (ρ x) (w 0)) v (move_head A n p) = 0
    rw [eval_move_head,he]
    exact hw

/-- An existential real algebraic incidence over any finite list of
witness coordinates is locally certified over the original base ring. -/
theorem certified_exists_fin (n : ℕ) {A X : Type*} [CommRing A] [TopologicalSpace X]
    (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a) (p : MvPolynomial (Fin n) A) :
    LocallyCertified ρ {x | ∃ w : Fin n → ℝ, MvPolynomial.eval₂Hom (ρ x) w p = 0} := by
  induction n generalizing X A with
  | zero =>
    let a := MvPolynomial.eval (fun i : Fin 0 => i.elim0) p
    have hv (x : X) (w : Fin 0 → ℝ) : ρ x a = MvPolynomial.eval₂Hom (ρ x) w p := by
      have he : (ρ x).comp (MvPolynomial.eval (fun i : Fin 0 => i.elim0)) =
          MvPolynomial.eval₂Hom (ρ x) w := by
        apply MvPolynomial.ringHom_ext
        · intro r; simp
        · intro i; exact i.elim0
      exact DFunLike.congr_fun he p
    rintro x ⟨w,hw⟩
    exact ⟨a,(hv x w).trans hw,Eventually.of_forall fun z hz => ⟨w,(hv z w).symm.trans hz⟩⟩
  | succ n ih =>
    let S := {z : X × ℝ | ∃ w : Fin n → ℝ, MvPolynomial.eval₂Hom (appendEval ρ z) w (move_head A n p) = 0}
    have hcert : LocallyCertified (appendEval ρ) S :=
      ih (appendEval ρ) (continuous_appendEval ρ hc) (move_head A n p)
    rw [←exists_move_head ρ p]
    exact hcert.fst_image hc

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
