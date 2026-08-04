import GaloisForLFunctions.HTGeometry.WaveEnergyDerivative

/-!
# Uniqueness for the Cauchy problem

The energy estimate is stated for one solution and its own energy. What an inverse problem uses is
the difference of two solutions: the clock equation is linear, so that difference solves it again,
and if the two solutions carry the same Cauchy data then the difference has vanishing energy at time
zero. The estimate then forces it to vanish afterwards.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Uniqueness

variable {d : ℕ} {u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

theorem waveDirDeriv_sub {f g : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v p : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun q => f q - g q) p = waveDirDeriv v f p - waveDirDeriv v g p := by
  have hd : HasFDerivAt (fun q : ℝ × (Fin d → ℝ) => f q - g q)
      (fderiv ℝ f p - fderiv ℝ g p) p :=
    (differentiableAt_of_contDiff_infty' hf p).hasFDerivAt.sub
      (differentiableAt_of_contDiff_infty' hg p).hasFDerivAt
  rw [waveDirDeriv, hd.fderiv]
  simp [waveDirDeriv]

theorem waveDirDeriv_sub_fun {f g : ℝ × (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (v : ℝ × (Fin d → ℝ)) :
    waveDirDeriv v (fun q => f q - g q) = fun p => waveDirDeriv v f p - waveDirDeriv v g p := by
  funext p
  exact waveDirDeriv_sub hf hg v p

/-- **The clock equation is linear:** the difference of two solutions with the same potential is
again a solution. -/
theorem solvesWaveEq_sub (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (h₁ : SolvesWaveEq u₁ V) (h₂ : SolvesWaveEq u₂ V) :
    SolvesWaveEq (fun q => u₁ q - u₂ q) V := by
  intro p
  have htime := waveDirDeriv_sub_fun hu₁ hu₂ (timeDir d)
  have hspace : ∀ i : Fin d, waveDirDeriv (spaceDir d i) (fun q => u₁ q - u₂ q)
      = fun q => waveDirDeriv (spaceDir d i) u₁ q - waveDirDeriv (spaceDir d i) u₂ q :=
    fun i => waveDirDeriv_sub_fun hu₁ hu₂ (spaceDir d i)
  have hsecondTime : waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) (fun q => u₁ q - u₂ q)) p
      = waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₁) p
        - waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u₂) p := by
    rw [htime]
    exact waveDirDeriv_sub (contDiff_dirDeriv hu₁ _) (contDiff_dirDeriv hu₂ _) _ p
  have hsecondSpace : ∀ i : Fin d,
      waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) (fun q => u₁ q - u₂ q)) p
        = waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u₁) p
          - waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) u₂) p := by
    intro i
    rw [hspace i]
    exact waveDirDeriv_sub (contDiff_dirDeriv hu₁ _) (contDiff_dirDeriv hu₂ _) _ p
  show waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) fun q => u₁ q - u₂ q) p
    = (∑ i : Fin d, waveDirDeriv (spaceDir d i) (waveDirDeriv (spaceDir d i) fun q => u₁ q - u₂ q) p)
      + V p * (u₁ p - u₂ p)
  rw [hsecondTime, Finset.sum_congr rfl fun i _ => hsecondSpace i, Finset.sum_sub_distrib,
    h₁ p, h₂ p]
  ring

/-- A field vanishing on a whole slice, together with its time derivative there, has zero energy on
that slice. -/
theorem waveEnergy_eq_zero_of_slice_zero {w : ℝ × (Fin d → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w)
    (hval : ∀ x : Fin d → ℝ, w (0, x) = 0)
    (hder : ∀ x : Fin d → ℝ, waveDirDeriv (timeDir d) w (0, x) = 0) : waveEnergy w 0 = 0 := by
  have hslice : (fun y : Fin d → ℝ => w (0, y)) = fun _ : Fin d → ℝ => (0 : ℝ) := by
    funext y
    exact hval y
  have hspace : ∀ (i : Fin d) (x : Fin d → ℝ), waveDirDeriv (spaceDir d i) w (0, x) = 0 := by
    intro i x
    rw [waveDirDeriv_spaceDir_eq hw i 0 x, hslice, coordPartial_const]
  have hdens : ∀ x : Fin d → ℝ, energyDensity w (0, x) = 0 := by
    intro x
    rw [energyDensity, hder x, Finset.sum_congr rfl fun i _ => by rw [hspace i x], hval x]
    simp
  rw [waveEnergy, integral_congr_ae (Filter.Eventually.of_forall hdens)]
  simp

/-- **Uniqueness for the Cauchy problem.** Two classical solutions with spatially compact support,
the same bounded potential and the same Cauchy data agree at every later time. -/
theorem eq_of_solvesWaveEq_of_data_eq (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (hV : Continuous V) (hK : IsCompact K)
    (hzero₁ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₁ p = 0)
    (hzero₂ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₂ p = 0)
    (h₁ : SolvesWaveEq u₁ V) (h₂ : SolvesWaveEq u₂ V) {M : ℝ} (hM : ∀ p, |V p| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u₁ (0, x) = u₂ (0, x))
    (hder : ∀ x : Fin d → ℝ,
      waveDirDeriv (timeDir d) u₁ (0, x) = waveDirDeriv (timeDir d) u₂ (0, x))
    {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) : u₁ (t, x) = u₂ (t, x) := by
  have hwcd : ContDiff ℝ ∞ fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q := hu₁.sub hu₂
  have hwzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → (fun q => u₁ q - u₂ q) p = 0 := by
    intro p hp
    show u₁ p - u₂ p = 0
    rw [hzero₁ p hp, hzero₂ p hp, sub_zero]
  have hwsolve : SolvesWaveEq (fun q => u₁ q - u₂ q) V := solvesWaveEq_sub hu₁ hu₂ h₁ h₂
  have hwval : ∀ y : Fin d → ℝ, (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) (0, y) = 0 := by
    intro y
    show u₁ (0, y) - u₂ (0, y) = 0
    rw [hval y, sub_self]
  have hwder : ∀ y : Fin d → ℝ,
      waveDirDeriv (timeDir d) (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) (0, y) = 0 := by
    intro y
    rw [waveDirDeriv_sub hu₁ hu₂, hder y, sub_self]
  have h0 : waveEnergy (fun q : ℝ × (Fin d → ℝ) => u₁ q - u₂ q) 0 = 0 :=
    waveEnergy_eq_zero_of_slice_zero hwcd hwval hwder
  have hvanish := eq_zero_of_waveEnergy_zero hwcd hV hK hwzero hwsolve hM h0 ht x
  have : u₁ (t, x) - u₂ (t, x) = 0 := hvanish
  linarith

end Uniqueness

end GaloisForLFunctions.HTGeometry
