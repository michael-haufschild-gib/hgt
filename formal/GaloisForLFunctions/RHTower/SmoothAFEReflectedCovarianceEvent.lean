import GaloisForLFunctions.RHTower.SmoothAFEReflectedConditionalEnergy
import GaloisForLFunctions.RHTower.SteinhausFiniteCharacterCellRotation

/-!
# A fixed positive-mass conditional covariance event

For every prescribed positive covariance constant and every finite set of distinct right-strip
nodes, one finite-character cell supports the reflected-primal channel energy lower bound
`H / log N` in every direction. Its mass is strictly positive and exactly independent of the
common height. Its character prefix lies below the conditioning threshold for all sufficiently
large cutoffs. Every sufficiently small positive smoothing scale uses the same event.

The event centres retain any prescribed finite phase prefix before the common-height rotation.
This proves a covariance producer component. It supplies neither simultaneous background/target
control nor transfer to the deterministic vertical prime flow, and does not prove recurrence.
-/

noncomputable section
open MeasureTheory Filter Topology Finset Complex
namespace RHTower

/-- A character cell reads only the prime coordinates below its fixed prefix bound. -/
theorem steinhausCharacterCell_congr_smallPrimes (B : ℕ) (omega : SteinhausModel.Omega)
    (δ : ℝ) {eta eta' : SteinhausModel.Omega}
    (h : ∀ p ∈ Nat.primesLE B, eta p = eta' p) :
    eta ∈ steinhausCharacterCell B omega δ ↔ eta' ∈ steinhausCharacterCell B omega δ := by
  have hX : ∀ n ∈ Icc 1 B, SteinhausModel.X n eta = SteinhausModel.X n eta' := by
    intro n hn
    apply X_congr_of_eqOn_primeFactors
    intro p hp
    apply h p
    rw [Nat.mem_primesLE]
    refine ⟨?_, Nat.prime_of_mem_primeFactors hp⟩
    exact (Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; omega)
      (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hn).2
  constructor
  · intro he n hn
    rw [← hX n hn]
    exact he n hn
  · intro he n hn
    rw [hX n hn]
    exact he n hn

/-- A fixed positive probability, uniform in the common height and cutoff, supports
arbitrarily large `H / log N` reflected-primal conditional covariance in every direction. -/
theorem exists_reflectedPrimalConditional_covariance_event
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (omega : SteinhausModel.Omega) {H : ℝ} (hH : 0 < H) :
    ∃ omega' : SteinhausModel.Omega, (∀ p ∈ S, omega' p = omega p) ∧
      ∃ r₀ : ℝ, ∃ K B : ℕ, ∃ δ : ℝ, ∃ m : ENNReal,
        0 < r₀ ∧ 0 < K ∧ 0 < δ ∧ 0 < m ∧
        (∀ tau : ℝ, MeasurableSet
          (steinhausCharacterCell B (steinhausLogPhaseShift omega' (-tau)) δ) ∧
          SteinhausModel.steinhausMeasure
            (steinhausCharacterCell B (steinhausLogPhaseShift omega' (-tau)) δ) = m) ∧
        ∀ᶠ N : ℕ in atTop,
          N < (N / (2 * K)) * (N / (2 * K)) ∧ B ≤ N / (2 * K) ∧
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
            ∀ eta ∈ steinhausCharacterCell B (steinhausLogPhaseShift omega' (-tau)) δ,
              ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ u : Fin J → ℂ,
                H / Real.log N * ‖u‖ ^ 2 ≤
                  ∑ p ∈ largePrimes N (N / (2 * K)),
                    ‖∑ j, steinhausLargePrimeChannel
                        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
                        N p eta * u j‖ ^ 2 := by
  obtain ⟨omega', hp, r₀, K, B, δ, hr₀, hK, hδ, hcell⟩ :=
    exists_reflectedPrimalConditional_energy_cell_lower hJ d b hd hdhalf hinj S omega hH
  refine ⟨omega', hp, r₀, K, B, δ,
    SteinhausModel.steinhausMeasure (steinhausCharacterCell B omega' δ),
    hr₀, hK, hδ, steinhausMeasure_characterCell_pos B omega' hδ, ?_, ?_⟩
  · intro tau
    refine ⟨(isOpen_steinhausCharacterCell B _ δ).measurableSet, ?_⟩
    exact steinhausMeasure_characterCell_add_phase B omega'
      (fun p => (-tau) * Real.log p / (2 * Real.pi)) δ
  · filter_upwards [hcell, eventually_ge_atTop (B * (2 * K))] with N hN hNB
    refine ⟨hN.1, (Nat.le_div_iff_mul_le (by omega : 0 < 2 * K)).mpr hNB, ?_⟩
    intro tau htau eta heta r hr hrle u
    have hcancel : ∀ omega : SteinhausModel.Omega, ∀ t : ℝ,
        steinhausLogPhaseShift (steinhausLogPhaseShift omega (-t)) t = omega := by
      intro omega t
      ext p
      simp only [steinhausLogPhaseShift]
      ring
    have hshift : steinhausLogPhaseShift eta tau ∈ steinhausCharacterCell B omega' δ := by
      intro n hn
      have hnorm := norm_steinhausCharacter_sub_add_phase n
        (steinhausLogPhaseShift omega' (-tau)) eta (fun p => tau * Real.log p / (2 * Real.pi))
      change ‖SteinhausModel.X n (steinhausLogPhaseShift eta tau) -
        SteinhausModel.X n (steinhausLogPhaseShift (steinhausLogPhaseShift omega' (-tau)) tau)‖ = _
        at hnorm
      rw [hcancel] at hnorm
      rw [hnorm]
      exact heta n hn
    have h := hN.2 (steinhausLogPhaseShift eta tau) hshift tau htau r hr hrle u
    have heq : steinhausLogPhaseShift (steinhausLogPhaseShift eta tau) (-tau) = eta := by
      simpa only [neg_neg] using hcancel eta (-tau)
    simpa only [heq] using h

end RHTower
