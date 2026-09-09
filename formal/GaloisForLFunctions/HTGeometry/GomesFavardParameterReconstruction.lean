import GaloisForLFunctions.HTGeometry.GomesMomentMassScale

/-!
Exact source reconstruction and the mass forgotten by monic recurrence frames.
This applies the reconstruction and missing-observation viewpoint of Gomes,
arXiv:2607.24901v1 and arXiv:2509.25276v7, to the corpus Favard realization.
These are corpus applications, not transcriptions of numbered paper results.
-/

open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- The generated monic family retains the prescribed recurrence shape and forgets its mass. -/
theorem gomesFavardMoment_monicOrtho (r : ℝ) (a q : ℕ → ℝ) (n : ℕ) :
    monicOrtho (gomesFavardMoment r a q) n = favardPoly a (gomesFavardLower q) n := by
  change monicOrtho (gomesMomentMassScale r (favardMoment a (gomesFavardLower q))) n = _
  rw [gomesMomentMassScale_monicOrtho]
  exact monicOrtho_favardMoment a _ (fun k => Real.exp_pos (q k)) n

/-- Generated diagonal coefficients recover all prescribed diagonal data. -/
theorem gomesFavardMoment_alpha (r : ℝ) (a q : ℕ → ℝ) (n : ℕ) :
    monicOrthoAlpha (gomesFavardMoment r a q) n = a n := by
  change monicOrthoAlpha (gomesMomentMassScale r (favardMoment a (gomesFavardLower q))) n = _
  rw [gomesMomentMassScale_alpha]
  exact monicOrthoAlpha_favardMoment a _ (fun k => Real.exp_pos (q k)) n

/-- Generated lower coefficients recover all exponentiated lower data. -/
theorem gomesFavardMoment_beta_succ (r : ℝ) (a q : ℕ → ℝ) (n : ℕ) :
    monicOrthoBeta (gomesFavardMoment r a q) (n+1) = Real.exp (q n) := by
  change monicOrthoBeta (gomesMomentMassScale r (favardMoment a (gomesFavardLower q))) (n+1) = _
  rw [gomesMomentMassScale_beta]
  exact monicOrthoBeta_favardMoment a _ (fun k => Real.exp_pos (q k)) (Nat.succ_pos n)

/-- The exact squared norms retain both initial mass and the running product of lower coefficients. -/
theorem gomesFavardMoment_normSq (r : ℝ) (a q : ℕ → ℝ) (n : ℕ) :
    monicOrthoNormSq (gomesFavardMoment r a q) n = Real.exp r*∏ k ∈ Finset.range n, Real.exp (q k) := by
  change monicOrthoNormSq (gomesMomentMassScale r (favardMoment a (gomesFavardLower q))) n = _
  rw [gomesMomentMassScale_normSq,monicOrthoNormSq_favardMoment a _ (fun k => Real.exp_pos (q k))]
  rfl

/-- Full moment data reconstruct all three input coordinates exactly. -/
theorem gomesFavardMoment_injective_data (r t : ℝ) (a b q p : ℕ → ℝ) :
    gomesFavardMoment r a q = gomesFavardMoment t b p ↔ r = t ∧ a = b ∧ q = p := by
  constructor
  · intro h
    have hm := congrFun h 0
    rw [gomesFavardMoment_zero,gomesFavardMoment_zero] at hm
    have ha : a = b := by
      funext n
      have hh := congrArg (fun s => monicOrthoAlpha s n) h
      simpa only [gomesFavardMoment_alpha] using hh
    have hq : q = p := by
      funext n
      have hh := congrArg (fun s => monicOrthoBeta s (n+1)) h
      rw [gomesFavardMoment_beta_succ,gomesFavardMoment_beta_succ] at hh
      exact Real.exp_injective hh
    exact ⟨Real.exp_injective hm,ha,hq⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

/-- The complete real frame, at every level and spectral point, is insensitive to arbitrary positive mass. -/
theorem gomesFavardMoment_frame_mass_invariant (r t : ℝ) (a q : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    gomesMomentFrame (gomesFavardMoment r a q) n x = gomesMomentFrame (gomesFavardMoment t a q) n x := by
  change gomesMomentFrame (gomesMomentMassScale r (favardMoment a (gomesFavardLower q))) n x =
    gomesMomentFrame (gomesMomentMassScale t (favardMoment a (gomesFavardLower q))) n x
  rw [gomesMomentMassScale_frame,gomesMomentMassScale_frame]

/-- Exact reconstruction obstruction: even every monic frame fails to distinguish two different positive moment masses. -/
theorem gomesFavardMoment_full_frame_incomplete (r : ℝ) (a q : ℕ → ℝ) :
    (∀ n : ℕ, ∀ x : ℝ, gomesMomentFrame (gomesFavardMoment r a q) n x =
      gomesMomentFrame (gomesFavardMoment (r+1) a q) n x) ∧
    gomesFavardMoment r a q ≠ gomesFavardMoment (r+1) a q := by
  refine ⟨fun n x => gomesFavardMoment_frame_mass_invariant r (r+1) a q n x,?_⟩
  intro h
  have hr := ((gomesFavardMoment_injective_data r (r+1) a a q q).mp h).1
  linarith

end GaloisForLFunctions.HTGeometry
