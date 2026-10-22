import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysCompletedTriple
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization

/-!
# The completed points over a one-point scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §14.

At a point specialising to itself the local ring of the closure is the residue field, so both
evaluation maps used in Proposition 14.11 are bijective; on a scheme with a single point — for
instance `Spec` of a field — this makes the two hypotheses of that proposition hold.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry Perfection

noncomputable section

universe u

variable {X : Scheme.{u}} {x : X}

theorem deningerClosureToResidue_refl_surjective (h : x ⤳ x) :
    Function.Surjective (deningerClosureToResidue h) := by
  intro t
  obtain ⟨a, rfl⟩ := X.residue_surjective x t
  refine ⟨DeningerClosureLocalRing.mk h a, ?_⟩
  rw [deningerClosureToResidue_mk, stalkValue_def]
  have hid : X.presheaf.stalkSpecializes h = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl X.presheaf x
  rw [hid]
  rfl

theorem deningerClosureResidue_refl_eq (h : x ⤳ x) (a : X.presheaf.stalk x) :
    deningerClosureResidue h (DeningerClosureLocalRing.mk h a)
      = deningerClosureToResidue h (DeningerClosureLocalRing.mk h a) := by
  rw [deningerClosureResidue_mk, deningerClosureToResidue_mk, stalkValue_def]
  have hid : X.presheaf.stalkSpecializes h = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl X.presheaf x
  rw [hid]
  rfl

theorem deningerClosureResidue_refl_surjective (h : x ⤳ x) :
    Function.Surjective (deningerClosureResidue h) := by
  intro t
  obtain ⟨d, hd⟩ := deningerClosureToResidue_refl_surjective h t
  obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective h d
  exact ⟨_, (deningerClosureResidue_refl_eq h a).trans hd⟩

variable {p : ℕ} [NeZero p]

theorem deningerPerfEvalGen_refl_surjective (h : x ⤳ x) :
    Function.Surjective (deningerPerfEvalGen (p := p) h) := by
  intro t
  have hsur := deningerClosureToResidue_refl_surjective h
  refine ⟨⟨fun n => Function.surjInv hsur (coeffMonoidHom _ p n t), fun n => ?_⟩, ?_⟩
  · refine (deningerClosureToResidue_injective h) ?_
    have e1 := Function.surjInv_eq hsur (coeffMonoidHom _ p (n + 1) t)
    have e2 := Function.surjInv_eq hsur (coeffMonoidHom _ p n t)
    rw [map_pow, e1, e2]
    exact t.2 n
  · refine Subtype.ext (funext fun n => ?_)
    exact Function.surjInv_eq hsur (coeffMonoidHom _ p n t)

theorem deningerPerfEvalSpec_refl_surjective (h : x ⤳ x) :
    Function.Surjective (deningerPerfEvalSpec (p := p) h) := by
  intro t
  obtain ⟨f, hf⟩ := deningerPerfEvalGen_refl_surjective (p := p) h t
  refine ⟨f, ?_⟩
  refine Subtype.ext (funext fun n => ?_)
  have hn : deningerClosureResidue h (coeffMonoidHom _ p n f)
      = deningerClosureToResidue h (coeffMonoidHom _ p n f) := by
    obtain ⟨a, ha⟩ := DeningerClosureLocalRing.mk_surjective h (coeffMonoidHom _ p n f)
    rw [← ha]
    exact deningerClosureResidue_refl_eq h a
  show deningerClosureResidue h (coeffMonoidHom _ p n f) = _
  rw [hn]
  exact congrArg (fun z => coeffMonoidHom _ p n z) hf

theorem deningerPerfRatio_of_surjective {a b : X} (h : a ⤳ b)
    (hsurj : Function.Surjective (deningerPerfEvalGen (p := p) h))
    (t : Perfection (X.residueField a) p) :
    ∃ fs : Perfection (DeningerClosureLocalRing h) p × Perfection (DeningerClosureLocalRing h) p,
      fs.2 ≠ 0 ∧ t * deningerPerfEvalGen h p fs.2 = deningerPerfEvalGen h p fs.1 := by
  obtain ⟨f, hf⟩ := hsurj t
  exact ⟨(f, 1), one_ne_zero, by rw [map_one, mul_one, hf]⟩

variable (X p)

/-- On a scheme with a single point both hypotheses of Proposition 14.11 hold. -/
theorem deningerPerfEvalSpec_surjective_of_subsingleton [Subsingleton X] :
    ∀ (a b : X) (h : a ⤳ b), Function.Surjective (deningerPerfEvalSpec (p := p) h) := by
  intro a b h
  have hab : a = b := Subsingleton.elim a b
  subst hab
  exact deningerPerfEvalSpec_refl_surjective h

theorem deningerPerfRatio_of_subsingleton [Subsingleton X] :
    ∀ (a b : X) (h : a ⤳ b) (t : Perfection (X.residueField a) p),
      ∃ fs : Perfection (DeningerClosureLocalRing h) p × Perfection (DeningerClosureLocalRing h) p,
        fs.2 ≠ 0 ∧ t * deningerPerfEvalGen h p fs.2 = deningerPerfEvalGen h p fs.1 := by
  intro a b h t
  have hab : a = b := Subsingleton.elim a b
  subst hab
  exact deningerPerfRatio_of_surjective h (deningerPerfEvalGen_refl_surjective h) t

/-- **Deninger, Proposition 14.11 (`t1213nn`), over a one-point scheme.**  The hypotheses of the
proposition are satisfiable: over `Spec` of a field they hold, so the completed `𝒪`-valued points
really are the continuous pointed multiplicative maps `P̂_y` with conditions 1) and 2). -/
theorem deningerCompletedTripleEquiv_of_subsingleton [Subsingleton X]
    (O : Type u) [CommRing O] [IsDomain O] [IsLocalRing O] [TopologicalSpace O] :
    Nonempty (DeningerCompletedCharTriple X O p ≃ DeningerCompletedHatTriple X O p) :=
  ⟨deningerCompletedTripleEquiv (deningerPerfRatio_of_subsingleton X p)
    (deningerPerfEvalSpec_surjective_of_subsingleton X p)⟩

end

end RHTower