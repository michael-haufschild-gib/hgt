import GaloisForLFunctions.HTGeometry.WaveTimeReflection

/-!
# The estimate on both sides of the initial slice, and continuous dependence

Time reflection turns the forward energy estimate into the backward one, because the energy density
is even in the time derivative. What comes out is the estimate in its symmetric form,
`E(t) ≤ E(0)·exp((M+1)|t|)`, and — applied to the difference of two solutions, which solves the same
equation — the quantitative form of uniqueness: the energy of the difference at any time is
controlled by the energy of the difference of the Cauchy data.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section TwoSided

variable {d : ℕ} {u u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ} {K : Set (Fin d → ℝ)}

theorem energyDensity_comp_timeReflect (hu : ContDiff ℝ ∞ u) (p : ℝ × (Fin d → ℝ)) :
    energyDensity (fun q => u (timeReflect d q)) p = energyDensity u (timeReflect d p) := by
  have htime : (dirDeriv (timeDir d) (fun q => u (timeReflect d q)) p) ^ 2
      = (dirDeriv (timeDir d) u (timeReflect d p)) ^ 2 := by
    rw [dirDeriv_timeDir_comp_timeReflect hu]
    ring
  have hspace : ∀ i : Fin d,
      (dirDeriv (spaceDir d i) (fun q => u (timeReflect d q)) p) ^ 2
        = (dirDeriv (spaceDir d i) u (timeReflect d p)) ^ 2 := by
    intro i
    rw [dirDeriv_spaceDir_comp_timeReflect hu]
  rw [energyDensity, energyDensity, htime, Finset.sum_congr rfl fun i _ => hspace i]

theorem waveEnergy_comp_timeReflect (hu : ContDiff ℝ ∞ u) (t : ℝ) :
    waveEnergy (fun q => u (timeReflect d q)) t = waveEnergy u (-t) := by
  rw [waveEnergy, waveEnergy]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact energyDensity_comp_timeReflect hu (t, x)

/-- **The energy estimate on both sides of the initial slice.** -/
theorem waveEnergy_le_exp_abs (hu : ContDiff ℝ ∞ u) (hV : Continuous V) (hK : IsCompact K)
    (hzero : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u p = 0) (hsolve : SolvesWaveEq u V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    waveEnergy u t ≤ waveEnergy u 0 * Real.exp ((M + 1) * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact waveEnergy_le_exp hu hV hK hzero hsolve hM ht
  · have hrefl := waveEnergy_le_exp
      (u := fun q => u (timeReflect d q)) (V := fun q => V (timeReflect d q))
      (contDiff_comp_timeReflect hu) (hV.comp (timeReflect d).continuous) hK
      (fun p hp => hzero (timeReflect d p) hp)
      (solvesWaveEq_comp_timeReflect hu hsolve) (fun p => hM (timeReflect d p))
      (t := -t) (by linarith)
    rw [waveEnergy_comp_timeReflect hu, waveEnergy_comp_timeReflect hu, neg_neg, neg_zero] at hrefl
    rw [abs_of_nonpos ht]
    exact hrefl

/-- **Continuous dependence on the Cauchy data.** The energy of the difference of two solutions is
controlled at every time by its value on the initial slice — the quantitative form of uniqueness. -/
theorem waveEnergy_sub_le_exp_abs (hu₁ : ContDiff ℝ ∞ u₁) (hu₂ : ContDiff ℝ ∞ u₂)
    (hV : Continuous V) (hK : IsCompact K)
    (hzero₁ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₁ p = 0)
    (hzero₂ : ∀ p : ℝ × (Fin d → ℝ), p.2 ∉ K → u₂ p = 0)
    (h₁ : SolvesWaveEq u₁ V) (h₂ : SolvesWaveEq u₂ V) {M : ℝ} (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    waveEnergy (fun q => u₁ q - u₂ q) t
      ≤ waveEnergy (fun q => u₁ q - u₂ q) 0 * Real.exp ((M + 1) * |t|) := by
  refine waveEnergy_le_exp_abs (hu₁.sub hu₂) hV hK ?_ (solvesWaveEq_sub hu₁ hu₂ h₁ h₂) hM t
  intro p hp
  show u₁ p - u₂ p = 0
  rw [hzero₁ p hp, hzero₂ p hp, sub_zero]

end TwoSided

end GaloisForLFunctions.HTGeometry
