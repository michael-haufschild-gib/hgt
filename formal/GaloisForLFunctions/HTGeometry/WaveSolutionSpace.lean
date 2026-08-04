import GaloisForLFunctions.HTGeometry.WaveCauchyUniqueness

/-!
# The solutions of a fixed clock equation form a vector space

The clock equation is linear in the field, so its solutions are closed under sums and scalar
multiples as well as differences. This is what superposition arguments — and any later construction
of a solution as a limit of finite combinations — consume.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContDiff

section Linear

variable {d : ℕ} {u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ}

theorem waveDirDeriv_const_smul {f : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (v p : ℝ × (Fin d → ℝ)) : waveDirDeriv v (fun q => c * f q) p = c * waveDirDeriv v f p := by
  have hd : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => c * f q) (c • fderiv ℝ f p) p :=
    ((differentiableAt_of_contDiff_infty' hf p).hasFDerivAt).const_mul c
  rw [waveDirDeriv, hd.fderiv]
  simp [waveDirDeriv]

theorem waveDirDeriv_const_smul_fun {f : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ)
    (v : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun q => c * f q) = fun p => c * waveDirDeriv v f p := by
  funext p
  exact waveDirDeriv_const_smul hf c v p

theorem waveDirDeriv_add_fun {f g : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun q => f q + g q) = fun p => waveDirDeriv v f p + waveDirDeriv v g p := by
  funext p
  exact waveDirDeriv_add hf hg v p

/-- **The sum of two solutions is a solution.** -/
theorem solvesWaveEq_add (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (h₁ : SolvesWaveEq u₁ V) (h₂ : SolvesWaveEq u₂ V) :
    SolvesWaveEq (fun q => u₁ q + u₂ q) V := by
  intro p
  have hsecondTime : waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) (fun q => u₁ q + u₂ q)) p
      = waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₁) p
        + waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₂) p := by
    rw [waveDirDeriv_add_fun hu₁ hu₂]
    exact waveDirDeriv_add (contDiff_dirDeriv hu₁ _) (contDiff_dirDeriv hu₂ _) _ p
  have hsecondSpace : ∀ i : Fin d,
      waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) (fun q => u₁ q + u₂ q)) p
        = waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u₁) p
          + waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u₂) p := by
    intro i
    rw [waveDirDeriv_add_fun hu₁ hu₂]
    exact waveDirDeriv_add (contDiff_dirDeriv hu₁ _) (contDiff_dirDeriv hu₂ _) _ p
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun q => u₁ q + u₂ q) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) fun q => u₁ q + u₂ q) p)
      + V p * (u₁ p + u₂ p)
  rw [hsecondTime, Finset.sum_congr rfl fun i _ => hsecondSpace i, Finset.sum_add_distrib,
    h₁ p, h₂ p]
  ring

/-- **A scalar multiple of a solution is a solution.** -/
theorem solvesWaveEq_const_smul (hu₁ : ContDiff ℝ ∞ u₁) (h₁ : SolvesWaveEq u₁ V) (c : ℝ) :
    SolvesWaveEq (fun q => c * u₁ q) V := by
  intro p
  have hsecondTime : waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) (fun q => c * u₁ q)) p
      = c * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₁) p := by
    rw [waveDirDeriv_const_smul_fun hu₁]
    exact waveDirDeriv_const_smul (contDiff_dirDeriv hu₁ _) c _ p
  have hsecondSpace : ∀ i : Fin d,
      waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) (fun q => c * u₁ q)) p
        = c * waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u₁) p := by
    intro i
    rw [waveDirDeriv_const_smul_fun hu₁]
    exact waveDirDeriv_const_smul (contDiff_dirDeriv hu₁ _) c _ p
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun q => c * u₁ q) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) fun q => c * u₁ q) p)
      + V p * (c * u₁ p)
  rw [hsecondTime, Finset.sum_congr rfl fun i _ => hsecondSpace i, ← Finset.mul_sum, h₁ p]
  ring

/-- The zero field solves every clock equation. -/
theorem solvesWaveEq_zero : SolvesWaveEq (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) V := by
  intro p
  have hz : ∀ v : ℝ × (Fin d → ℝ),
      waveDirDeriv v (fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) = fun _ => (0 : ℝ) := by
    intro v
    funext q
    rw [waveDirDeriv, fderiv_fun_const]
    rfl
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i)
        (waveDirDeriv (spaceDir d i) fun _ : ℝ × (Fin d → ℝ) => (0 : ℝ)) p) + V p * 0
  rw [hz (timeDir d), hz (timeDir d), Finset.sum_congr rfl fun i _ => by
    rw [hz (spaceDir d i), hz (spaceDir d i)]]
  simp

end Linear

end GaloisForLFunctions.HTGeometry
