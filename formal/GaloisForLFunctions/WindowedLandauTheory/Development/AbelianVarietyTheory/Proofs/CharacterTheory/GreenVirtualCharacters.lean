import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerCharacters
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParabolicInduction

/-! The characteristic-polynomial Möbius inverse gives a virtual character. -/

open Polynomial Module GaloisForLFunctions

namespace GlobalTheory.CuspGL

private lemma finsum_proper_invariant_eq_sum_range_finrank {F : Type} [Field F] [Finite F] (d : ℕ)
    (g : Module.End F (Fin d → F)) (Ψ : ∀ W : Submodule F (Fin d → F), (∀ v ∈ W, g v ∈ W) → ℂ) :
    (∑ᶠ (W : { W : Submodule F (Fin d → F) // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W }), Ψ W.1 W.2.2) =
    ∑ a ∈ Finset.range d, ∑ᶠ (W : { W : Submodule F (Fin d → F) //
      Module.finrank F W = a ∧ ∀ v ∈ W, g v ∈ W }), Ψ W.1 W.2.2 := by
  classical
  letI : Finite (Fin d → F) := Module.finite_of_finite F
  letI : Finite (Submodule F (Fin d → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin d → F) => (W : Set (Fin d → F)))
      SetLike.coe_injective
  letI : Fintype (Submodule F (Fin d → F)) := Fintype.ofFinite _
  let Fn : Submodule F (Fin d → F) → ℂ := fun W => if h : ∀ v ∈ W, g v ∈ W then Ψ W h else 0
  have hsub : ∀ (p : Submodule F (Fin d → F) → Prop) [DecidablePred p], (∀ W, p W → ∀ v ∈ W, g v ∈ W) →
      ∀ (hp : ∀ W : { W // p W }, ∀ v ∈ W.1, g v ∈ W.1),
      (∑ᶠ (W : { W // p W }), Ψ W.1 (hp W)) = ∑ W, if p W then Fn W else 0 := by
    intro p _ hpi hp
    rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter,
      Finset.sum_subtype (p := p) (Finset.univ.filter p) (fun W => by simp) Fn]
    exact Finset.sum_congr rfl fun W _ => (dif_pos (hp W)).symm
  rw [hsub (fun W => W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W) (fun W h => h.2) (fun W => W.2.2)]
  rw [Finset.sum_congr rfl fun a _ => hsub (fun W => Module.finrank F W = a ∧ ∀ v ∈ W, g v ∈ W)
    (fun W h => h.2) (fun W => W.2.2)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases hinv : ∀ v ∈ W, g v ∈ W
  · simp only [and_iff_left hinv]
    rw [Finset.sum_ite_eq]
    have hd : Module.finrank F (Fin d → F) = d := Module.finrank_fin_fun F
    have hiff : W ≠ ⊤ ↔ Module.finrank F W < d := by
      constructor
      · intro h
        have h' := Submodule.finrank_lt h
        rwa [hd] at h'
      · rintro h rfl
        rw [finrank_top, hd] at h
        exact lt_irrefl _ h
    simp only [Finset.mem_range, hiff]
  · simp [hinv]

/-- Inverting the root-sum weight subtracts parabolic inductions of lower-dimensional terms. -/
theorem psi_rootSum_charpoly_mem_virtual (F : Type) [Field F] [Finite F]
    (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (k : ℕ) (d : ℕ) :
    (fun x : GL (Fin d) F => psi (rootSum θ k)
      (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∈
      virtualCharacterGroup (GL (Fin d) F) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have hconj : ∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
        [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V),
        psi (rootSum θ k) V' (e.conj g) =
          psi (rootSum θ k) V g :=
      fun V V' _ _ _ _ _ _ e g =>
        psi_conj _ V V' e g
    have heq : (fun x : GL (Fin d) F => psi
        (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) =
        (fun x : GL (Fin d) F => rootSum θ k (x : Matrix (Fin d) (Fin d) F).charpoly) -
        ∑ a ∈ Finset.range d, (fun x : GL (Fin d) F =>
          ∑ᶠ (W : { W : Submodule F (Fin d → F) // Module.finrank F W = a ∧
            ∀ v ∈ W, (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) v ∈ W }),
            psi (rootSum θ k) (↥(W : Submodule F (Fin d → F)))
              ((Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)).restrict W.2.2)) := by
      funext x
      rw [psi_eq, Matrix.charpoly_toLin',
        finsum_proper_invariant_eq_sum_range_finrank d (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))
          (fun W h => psi (rootSum θ k) (↥W)
            ((Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)).restrict h))]
      simp [Finset.sum_apply]
    rw [heq]
    refine sub_mem (rootSum_charpoly_mem_virtual F θ hθ d k)
      (AddSubgroup.sum_mem _ fun a ha => ?_)
    exact parabolic_sum_mem_virtual
      (fun V _ _ _ g => psi (rootSum θ k) V g)
      hconj a d (Nat.le_of_lt (Finset.mem_range.mp ha)) (ih a (Finset.mem_range.mp ha))

end GlobalTheory.CuspGL
