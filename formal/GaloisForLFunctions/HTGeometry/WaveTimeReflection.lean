import GaloisForLFunctions.HTGeometry.WaveCauchyUniqueness

/-!
# Time reflection

The clock equation is invariant under reversing time: only the *second* time derivative enters, so
reflecting an event across the initial slice carries a solution to a solution of the reflected
potential, and carries the energy of a slice to the energy of the reflected slice. Uniqueness for
positive times therefore gives uniqueness for negative times as well.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Reflect

variable {d : ℕ} {u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

/-- Reflection of an event across the initial slice. -/
noncomputable def timeReflect (d : ℕ) : (ℝ × (Fin d → ℝ)) →L[ℝ] (ℝ × (Fin d → ℝ)) :=
  (-(ContinuousLinearMap.fst ℝ ℝ (Fin d → ℝ))).prod (ContinuousLinearMap.snd ℝ ℝ (Fin d → ℝ))

@[simp] theorem timeReflect_apply (p : ℝ × (Fin d → ℝ)) :
    timeReflect d p = (-p.1, p.2) := rfl

theorem contDiff_comp_timeReflect (hu : ContDiff ℝ ∞ u₁) :
    ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => u₁ (timeReflect d q) :=
  hu.comp (timeReflect d).contDiff

/-- The chain rule for a reflected field. -/
theorem dirDeriv_comp_timeReflect (hu : ContDiff ℝ ∞ u₁) (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv v (fun q => u₁ (timeReflect d q)) p
      = dirDeriv (timeReflect d v) u₁ (timeReflect d p) := by
  have hcomp : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => u₁ (timeReflect d q))
      ((fderiv ℝ u₁ (timeReflect d p)).comp (timeReflect d)) p :=
    (differentiableAt_of_contDiff_infty' hu (timeReflect d p)).hasFDerivAt.comp p
      (timeReflect d).hasFDerivAt
  rw [dirDeriv, hcomp.fderiv]
  rfl

theorem timeReflect_timeDir : timeReflect d (timeDir d) = -(timeDir d) := by
  refine Prod.ext ?_ ?_ <;> simp [timeDir]

theorem timeReflect_spaceDir (i : Fin d) : timeReflect d (spaceDir d i) = spaceDir d i := by
  refine Prod.ext ?_ ?_ <;> simp [spaceDir]

theorem dirDeriv_neg_dir (v p : ℝ × (Fin d → ℝ)) :
    dirDeriv (-v) u₁ p = -dirDeriv v u₁ p := by
  rw [dirDeriv, dirDeriv, map_neg]

theorem dirDeriv_timeDir_comp_timeReflect (hu : ContDiff ℝ ∞ u₁) (p : ℝ × (Fin d → ℝ)) :
    dirDeriv (timeDir d) (fun q => u₁ (timeReflect d q)) p
      = -dirDeriv (timeDir d) u₁ (timeReflect d p) := by
  rw [dirDeriv_comp_timeReflect hu, timeReflect_timeDir, dirDeriv_neg_dir]

theorem dirDeriv_spaceDir_comp_timeReflect (hu : ContDiff ℝ ∞ u₁) (i : Fin d)
    (p : ℝ × (Fin d → ℝ)) :
    dirDeriv (spaceDir d i) (fun q => u₁ (timeReflect d q)) p
      = dirDeriv (spaceDir d i) u₁ (timeReflect d p) := by
  rw [dirDeriv_comp_timeReflect hu, timeReflect_spaceDir]

/-- **The clock equation is invariant under time reflection.** -/
theorem solvesWaveEq_comp_timeReflect (hu : ContDiff ℝ ∞ u₁) (h : SolvesWaveEq u₁ V) :
    SolvesWaveEq (fun q => u₁ (timeReflect d q)) (fun q => V (timeReflect d q)) := by
  intro p
  have hsecond : dirDeriv (timeDir d) (dirDeriv (timeDir d) fun q => u₁ (timeReflect d q)) p
      = dirDeriv (timeDir d) (dirDeriv (timeDir d) u₁) (timeReflect d p) := by
    have hfirst : (dirDeriv (timeDir d) fun q => u₁ (timeReflect d q))
        = fun q => -dirDeriv (timeDir d) u₁ (timeReflect d q) := by
      funext q
      exact dirDeriv_timeDir_comp_timeReflect hu q
    rw [hfirst]
    have hneg : (fun q : ℝ × (Fin d → ℝ) => -dirDeriv (timeDir d) u₁ (timeReflect d q))
        = fun q => (fun r => -dirDeriv (timeDir d) u₁ r) (timeReflect d q) := rfl
    rw [hneg, dirDeriv_comp_timeReflect ((contDiff_dirDeriv hu _).neg), timeReflect_timeDir,
      dirDeriv_neg_dir]
    have hnegfun : dirDeriv (timeDir d) (fun r : ℝ × (Fin d → ℝ) =>
        -dirDeriv (timeDir d) u₁ r) (timeReflect d p)
        = -dirDeriv (timeDir d) (dirDeriv (timeDir d) u₁) (timeReflect d p) := by
      have hfd : HasFDerivAt (fun r : ℝ × (Fin d → ℝ) => -dirDeriv (timeDir d) u₁ r)
          (-(fderiv ℝ (dirDeriv (timeDir d) u₁) (timeReflect d p))) (timeReflect d p) :=
        (differentiableAt_of_contDiff_infty' (contDiff_dirDeriv hu _)
          (timeReflect d p)).hasFDerivAt.neg
      rw [dirDeriv, dirDeriv, hfd.fderiv]
      rfl
    rw [hnegfun, neg_neg]
  have hspace : ∀ i : Fin d,
      dirDeriv (spaceDir d i) (dirDeriv (spaceDir d i) fun q => u₁ (timeReflect d q)) p
        = dirDeriv (spaceDir d i) (dirDeriv (spaceDir d i) u₁) (timeReflect d p) := by
    intro i
    have hfirst : (dirDeriv (spaceDir d i) fun q => u₁ (timeReflect d q))
        = fun q => dirDeriv (spaceDir d i) u₁ (timeReflect d q) := by
      funext q
      exact dirDeriv_spaceDir_comp_timeReflect hu i q
    rw [hfirst]
    exact dirDeriv_spaceDir_comp_timeReflect (contDiff_dirDeriv hu _) i p
  show dirDeriv (timeDir d) (dirDeriv (timeDir d) fun q => u₁ (timeReflect d q)) p
    = (∑ i : Fin d, dirDeriv (spaceDir d i)
        (dirDeriv (spaceDir d i) fun q => u₁ (timeReflect d q)) p)
      + V (timeReflect d p) * u₁ (timeReflect d p)
  rw [hsecond, Finset.sum_congr rfl fun i _ => hspace i]
  exact h (timeReflect d p)

/-- **Uniqueness for the Cauchy problem, at every time.** -/
theorem eq_of_solvesWaveEq_of_data_eq_all (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (hV : Continuous V) (hK : IsCompact K)
    (hzero₁ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₁ p = 0)
    (hzero₂ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₂ p = 0)
    (h₁ : SolvesWaveEq u₁ V) (h₂ : SolvesWaveEq u₂ V) {M : ℝ} (hM : ∀ p, |V p| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u₁ (0, x) = u₂ (0, x))
    (hder : ∀ x : Fin d → ℝ,
      dirDeriv (timeDir d) u₁ (0, x) = dirDeriv (timeDir d) u₂ (0, x))
    (t : ℝ) (x : Fin d → ℝ) : u₁ (t, x) = u₂ (t, x) := by
  rcases le_total 0 t with ht | ht
  · exact eq_of_solvesWaveEq_of_data_eq hu₁ hu₂ hV hK hzero₁ hzero₂ h₁ h₂ hM hval hder ht x
  · have hrefl := eq_of_solvesWaveEq_of_data_eq
      (u₁ := fun q => u₁ (timeReflect d q)) (u₂ := fun q => u₂ (timeReflect d q))
      (V := fun q => V (timeReflect d q))
      (contDiff_comp_timeReflect hu₁) (contDiff_comp_timeReflect hu₂)
      (hV.comp (timeReflect d).continuous) hK
      (fun p hp => hzero₁ (timeReflect d p) hp) (fun p hp => hzero₂ (timeReflect d p) hp)
      (solvesWaveEq_comp_timeReflect hu₁ h₁) (solvesWaveEq_comp_timeReflect hu₂ h₂)
      (fun p => hM (timeReflect d p))
      (fun y => by simpa using hval y)
      (fun y => by
        rw [dirDeriv_timeDir_comp_timeReflect hu₁, dirDeriv_timeDir_comp_timeReflect hu₂]
        simpa using congrArg Neg.neg (hder y))
      (t := -t) (by linarith) x
    simpa using hrefl

end Reflect

end GaloisForLFunctions.HTGeometry
