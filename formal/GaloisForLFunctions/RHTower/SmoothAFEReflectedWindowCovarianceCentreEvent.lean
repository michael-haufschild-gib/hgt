import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowConditionalEnergy
import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowBoundedCentreEvent
import GaloisForLFunctions.RHTower.SteinhausFrozenWindowLocalTarget
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCovarianceEvent

open MeasureTheory Filter Finset Complex
open scoped Topology ENNReal
noncomputable section
namespace RHTower
open SteinhausModel

/-- One retained event of fixed positive mass supports the actual enlarged-cutoff Gram floor
and bounded centres, inside any requested refinement of the prescribed character cell. -/
theorem exists_reflectedPrimalWindow_covariance_boundedCentre_subcell_event
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (ω : Omega) (B₀ : ℕ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {H : ℝ} (hH : 0 < H) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ K B D : ℕ, ∃ δ m : ℝ,
        B₀ ≤ B ∧ δ ≤ δ₀ ∧ 0 < K ∧ 0 < δ ∧ 0 < m ∧
        ∀ᶠ N : ℕ in atTop, B ≤ N / (2 * K) ∧
          ∀ L : ℕ, N ≤ L → N * D ≤ L →
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
            ∃ E : Set Omega, MeasurableSet E ∧ m ≤ steinhausMeasure.real E ∧
              E ⊆ steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ ∧
              (∀ η ξ : Omega, (∀ p ∈ steinhausWindowRetainedPrimes L N (N / (2 * K)), η p = ξ p) →
                (η ∈ E ↔ ξ ∈ E)) ∧
              ∀ η ∈ E,
                (∀ j, ‖reflectedPrimalRetainedBackground (d j) (tau + b j) N L
                  (steinhausWindowRetainedPrimes L N (N / (2 * K))) η‖ ≤ 1) ∧
                ∀ u : Fin J → ℂ,
                  H / Real.log N * ‖u‖ ^ 2 ≤
                    ∑ p ∈ largePrimes N (N / (2 * K)),
                      ‖∑ j, steinhausLargePrimeChannel
                        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) 1 N)
                          L p η * u j‖ ^ 2 := by
  obtain ⟨ω', hprefix, K, Bc, D, δc, hK, hδc, hcov⟩ :=
    exists_reflectedPrimalWindowConditional_energy_cell_lower hJ d b hd hdhalf hinj S ω hH
  let B := max Bc B₀
  let δ := min δc δ₀
  have hδ : 0 < δ := lt_min hδc hδ₀
  let m := steinhausMeasure (steinhausCharacterCell B ω' δ)
  have hm : 0 < m := steinhausMeasure_characterCell_pos B ω' hδ
  have hcell (tau : ℝ) : MeasurableSet
      (steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ) ∧
      steinhausMeasure (steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ) = m := by
    refine ⟨(isOpen_steinhausCharacterCell B _ δ).measurableSet, ?_⟩
    exact steinhausMeasure_characterCell_add_phase B ω'
      (fun p => (-tau) * Real.log p / (2 * Real.pi)) δ
  have hsub (tau : ℝ) : steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ ⊆
      steinhausCharacterCell Bc (steinhausLogPhaseShift ω' (-tau)) δc := by
    intro η hη n hn
    exact (hη n (mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
      (mem_Icc.mp hn).2.trans (le_max_left _ _)⟩)).trans_le (min_le_left _ _)
  have hmtop : m ≠ ∞ := measure_ne_top _ _
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm.ne' hmtop
  refine ⟨ω', hprefix, K, B, D, δ, m.toReal / 2,
    le_max_right _ _, min_le_right _ _, hK, hδ, half_pos hmR, ?_⟩
  have hoffset : ∀ᶠ N : ℕ in atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  filter_upwards [hcov, hoffset, eventually_ge_atTop (B * (2 * K)),
    eventually_reflectedPrimalWindowBoundedCentreEvent_inter_mass d b hd hdhalf hmR]
    with N hcovN hbN hNB hgoodN
  have hBcut : B ≤ N / (2 * K) := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * K)).mpr hNB
  refine ⟨hBcut, ?_⟩
  intro L hNL hLD tau htau
  have ht (j : Fin J) : (N : ℝ) ≤ tau + b j := by
    have h := hbN j
    have hab := neg_abs_le (b j)
    linarith [htau.1]
  let T := steinhausWindowRetainedPrimes L N (N / (2 * K))
  let C : Set Omega := steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ
  let G : Set Omega := reflectedPrimalWindowBoundedCentreEvent d b tau N L T
  have hC : MeasurableSet C := (hcell tau).1
  have hG : MeasurableSet G := measurableSet_reflectedPrimalWindowBoundedCentreEvent _ _ _ _ _ _
  have hmass : m.toReal ≤ steinhausMeasure.real C := by
    change m.toReal ≤ (steinhausMeasure C).toReal
    rw [(hcell tau).2]
  refine ⟨C ∩ G, hC.inter hG, hgoodN L T tau ht C hmass, Set.inter_subset_left, ?_, ?_⟩
  · intro η ξ hphase
    have hsmall : ∀ p ∈ Nat.primesLE B, η p = ξ p := fun p hp =>
      hphase p (primesLE_subset_steinhausWindowRetainedPrimes hBcut (Nat.div_le_self _ _) hNL hp)
    have hcellEq := steinhausCharacterCell_congr_smallPrimes B
      (steinhausLogPhaseShift ω' (-tau)) δ hsmall
    have hgoodEq := reflectedPrimalWindowBoundedCentreEvent_congr_retained d b tau N L T hphase
    exact and_congr hcellEq hgoodEq
  · intro η hη
    refine ⟨hη.2, ?_⟩
    intro u
    have hcancel : ∀ omega : Omega, ∀ t : ℝ,
        steinhausLogPhaseShift (steinhausLogPhaseShift omega (-t)) t = omega := by
      intro omega t
      ext p
      simp only [steinhausLogPhaseShift]
      ring
    have hshift : steinhausLogPhaseShift η tau ∈ steinhausCharacterCell Bc ω' δc := by
      intro n hn
      have hnorm := norm_steinhausCharacter_sub_add_phase n
        (steinhausLogPhaseShift ω' (-tau)) η (fun p => tau * Real.log p / (2 * Real.pi))
      change ‖X n (steinhausLogPhaseShift η tau) -
        X n (steinhausLogPhaseShift (steinhausLogPhaseShift ω' (-tau)) tau)‖ = _ at hnorm
      rw [hcancel] at hnorm
      rw [hnorm]
      exact hsub tau hη.1 n hn
    have h := hcovN.2 L hLD (steinhausLogPhaseShift η tau) hshift tau htau u
    have heq : steinhausLogPhaseShift (steinhausLogPhaseShift η tau) (-tau) = η := by
      simpa only [neg_neg] using hcancel η (-tau)
    simpa only [heq] using h

end RHTower
