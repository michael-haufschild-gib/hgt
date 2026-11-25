import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.Deviations

/-! # Recovering the spectral rate from probabilities of neighborhoods -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Filter Topology Set MeasureTheory Endpoints

/-- Exponents r for which every neighborhood of v eventually has probability at least exp(−r/h). -/
def neighborhoodExponents (c d β : ℝ) {k : ℕ} (v : Fin k → ℝ) : Set ℝ :=
  {r | ∀ G : Set (Fin k → ℝ), IsOpen G → v ∈ G →
    ∀ᶠ h in criticalApproach, Real.exp (-r/h.val) ≤ (thermalLaw c d h β k G : ℝ)}

/-- The greatest lower bound of physically observable neighborhood exponents is the spectral cost. -/
theorem local_rate {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (hk : 0 < k)
    {v : Fin k → ℝ} (hv : v ∈ orderedBand c d k) :
    IsGLB (neighborhoodExponents c d β v) (rate c d β v) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  have habove {r : ℝ} (h : rate c d β v < r) : r ∈ neighborhoodExponents c d β v :=
    fun _ hG hvG => open_lower hc hcd β hk hG hv hvG r h
  constructor
  · intro r hr
    by_contra! h
    obtain ⟨t,hrt,htv⟩ := exists_between h
    obtain ⟨q,hrq,hqt⟩ := exists_between hrt
    let G := rate c d (k := k) β ⁻¹' Ioi t
    let C := rate c d (k := k) β ⁻¹' Ici t
    have hG : IsOpen G := isOpen_Ioi.preimage (continuous_rate c d β k)
    have hC : IsClosed C := isClosed_Ici.preimage (continuous_rate c d β k)
    have hu := closed_upper hc hcd β hk hC q (fun w hw => hqt.trans_le (show t ≤ rate c d β w from hw.2))
    obtain ⟨h,hl,hu'⟩ := ((hr G hG htv).and hu).exists
    have hGC : G ⊆ C := fun w hw => (show t < rate c d β w from hw).le
    have hm := measureReal_mono (μ := (thermalLaw c d h β k : Measure _)) hGC
    simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn] at hm
    exact (Real.exp_lt_exp.mpr (div_lt_div_of_pos_right (neg_lt_neg hrq) h.property)).not_ge ((hl.trans hm).trans hu')
  · intro t ht
    by_contra! h
    obtain ⟨r,hvr,hrt⟩ := exists_between h
    exact hrt.not_ge (ht (habove hvr))

/-- No finite lower exponent is observed outside the closed ordered band. -/
theorem no_exponents_outside {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ}
    {v : Fin k → ℝ} (hv : v ∉ orderedBand c d k) :
    neighborhoodExponents c d β v = ∅ := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  apply eq_empty_iff_forall_notMem.mpr
  intro r hr
  let U := (orderedBand c d k)ᶜ
  have hU : IsOpen U := (orderedBand_compact c d k).isClosed.isOpen_compl
  obtain ⟨h,hl,hp⟩ := ((hr U hU hv).and (eventually_positive hc hcd β (fun _ : Fin k → ℝ => (0:ℝ)))).exists
  have hz : eventWeight (added c d h) β h k U = 0 := by
    unfold eventWeight
    exact Finset.sum_eq_zero fun R _ => if_neg (show spectrum h R ∉ U from fun hr => hr (spectrum_mem_band h R))
  have he := thermalLaw_event h k hU.measurableSet hp.1
  rw [hz,zero_div] at he
  exact (Real.exp_pos _).not_ge (hl.trans_eq he)

/-- Neighborhood probabilities alone detect norm-preserving composition. -/
theorem split_isometric_iff_zero_local_cost {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
    ∀ v ∈ orderedBand c d k, IsGLB (neighborhoodExponents c d (2*s.re) v) 0 := by
  rw [split_isometric_iff_zero_rate hcd hk]
  constructor
  · intro H v hv
    simpa only [H v hv] using local_rate hc hcd (2*s.re) hk hv
  · intro H v hv
    exact (local_rate hc hcd (2*s.re) hk hv).unique (H v hv)

#print axioms local_rate
#print axioms no_exponents_outside
#print axioms split_isometric_iff_zero_local_cost

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
