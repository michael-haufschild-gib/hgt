import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.Laplace

/-! # The zero set of the spectral rate and norm-preserving composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Filter Topology MeasureTheory Endpoints

/-- Cost of observing an admissible ordered spectrum at inverse temperature β. -/
def rate (c d : ℝ) {k : ℕ} (β : ℝ) (v : Fin k → ℝ) := pressure c d k β-(1-β)*∑ i, v i

/-- The variational expression is the largest reward after subtracting its spectral cost. -/
theorem laplace_rate {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (hk : 0 < k)
    {F : (Fin k → ℝ) → ℝ} (hF : ContinuousOn F (orderedBand c d k)) :
    Tendsto (fun h : Ioi (0:ℝ) => h.val*Real.log (∫ v, Real.exp (F v/h.val) ∂(thermalLaw c d h β k : Measure _)))
      criticalApproach (𝓝 (peak c d (fun v => F v-rate c d β v))) := by
  obtain ⟨v,hv,he,hm⟩ := peak_attained hcd.le (tiltedObservable_continuousOn (β := β) hF)
  let G (w : Fin k → ℝ) := F w-rate c d β w
  have hG (w) : G w = tiltedObservable β F w-pressure c d k β := by
    unfold G rate tiltedObservable
    ring
  have H : IsGreatest (G '' orderedBand c d k) (G v) := ⟨mem_image_of_mem _ hv,by
    rintro _ ⟨w,hw,rfl⟩
    rw [hG,hG]
    exact sub_le_sub_right (hm w hw) _⟩
  change Tendsto _ _ (𝓝 (sSup (G '' orderedBand c d k)))
  rw [H.csSup_eq,hG,he]
  exact laplace_principle hc hcd β hk hF

theorem rate_above {β : ℝ} (hβ : 1 < β) (c d : ℝ) {k : ℕ} (v : Fin k → ℝ) :
    rate c d β v = (β-1)*∑ i, (v i-c) := by
  rw [rate,pressure,if_neg hβ.not_ge,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem rate_below {β : ℝ} (hβ : β < 1) (c d : ℝ) {k : ℕ} (v : Fin k → ℝ) :
    rate c d β v = (1-β)*∑ i, (d-v i) := by
  rw [rate,pressure,if_pos hβ.le,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem rate_one (c d : ℝ) {k : ℕ} (v : Fin k → ℝ) : rate c d 1 v = 0 := by simp [rate,pressure]

theorem rate_nonneg {c d β : ℝ} {k : ℕ} {v : Fin k → ℝ} (hv : v ∈ orderedBand c d k) : 0 ≤ rate c d β v := by
  rcases lt_trichotomy β 1 with hh | rfl | hh
  · rw [rate_below hh]
    exact mul_nonneg (sub_nonneg.mpr hh.le) (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hv.2 i).2)
  · exact (rate_one _ _ _).ge
  · rw [rate_above hh]
    exact mul_nonneg (sub_nonneg.mpr hh.le) (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hv.2 i).1)

/-- Cooling imposes a strictly positive cost unless every coordinate equals the lower endpoint. -/
theorem rate_zero_above {c d β : ℝ} (hβ : 1 < β) {k : ℕ} {v : Fin k → ℝ} (hv : v ∈ orderedBand c d k) :
    rate c d β v = 0 ↔ v = fun _ => c := by
  rw [rate_above hβ,mul_eq_zero,or_iff_right (sub_pos.mpr hβ).ne',
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hv.2 i).1)]
  exact ⟨fun h => funext fun i => sub_eq_zero.mp (h i (Finset.mem_univ _)),
    fun h i _ => sub_eq_zero.mpr (congrFun h i)⟩

/-- Heating imposes a strictly positive cost unless every coordinate equals the upper endpoint. -/
theorem rate_zero_below {c d β : ℝ} (hβ : β < 1) {k : ℕ} {v : Fin k → ℝ} (hv : v ∈ orderedBand c d k) :
    rate c d β v = 0 ↔ v = fun _ => d := by
  rw [rate_below hβ,mul_eq_zero,or_iff_right (sub_pos.mpr hβ).ne',
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hv.2 i).2)]
  exact ⟨fun h => funext fun i => (sub_eq_zero.mp (h i (Finset.mem_univ _))).symm,
    fun h i _ => sub_eq_zero.mpr (congrFun h i).symm⟩

/-- All ordered spectra carry zero exponential cost precisely when divisor splitting is isometric. -/
theorem split_isometric_iff_zero_rate {c d : ℝ} (hcd : c < d) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
    ∀ v ∈ orderedBand c d k, rate c d (2*s.re) v = 0 := by
  rw [split_isometric_iff]
  constructor
  · intro hs v _
    rw [show 2*s.re = 1 by rw [hs]; ring]
    exact rate_one _ _ _
  · intro H
    let i : Fin k := ⟨0,hk⟩
    rcases lt_trichotomy (2*s.re) 1 with hh | hh | hh
    · have hv := constant_mem (x := c) ⟨le_rfl,hcd.le⟩ k
      exact False.elim (hcd.ne (congrFun ((rate_zero_below hh hv).mp (H _ hv)) i))
    · linarith only [hh]
    · have hv := constant_mem (x := d) ⟨hcd.le,le_rfl⟩ k
      exact False.elim (hcd.ne' (congrFun ((rate_zero_above hh hv).mp (H _ hv)) i))

#print axioms laplace_rate
#print axioms rate_nonneg
#print axioms rate_zero_above
#print axioms rate_zero_below
#print axioms split_isometric_iff_zero_rate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
