import GaloisForLFunctions.RHTower.SmoothAFEReflectedBoundedCentreEvent
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCovarianceEvent

open MeasureTheory Filter Finset Complex
open scoped Topology ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- One event of fixed positive mass supports both the actual covariance lower bound and bounded centres. -/
theorem exists_reflectedPrimalConditional_covariance_boundedCentre_event
    {J : ℕ} (hJ : 0 < J) (d b : Fin J → ℝ)
    (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    (hinj : Function.Injective (fun j => rightDisplacedLinePt (d j) (b j)))
    (S : Finset ℕ) (ω : Omega) {H : ℝ} (hH : 0 < H) :
    ∃ ω' : Omega, (∀ p ∈ S, ω' p = ω p) ∧
      ∃ r₀ : ℝ, ∃ K B : ℕ, ∃ δ m : ℝ,
        0 < r₀ ∧ 0 < K ∧ 0 < δ ∧ 0 < m ∧
        ∀ᶠ N : ℕ in atTop,
          N < (N / (2 * K)) * (N / (2 * K)) ∧ B ≤ N / (2 * K) ∧
          ∀ tau ∈ Set.Icc ((5 / 4 : ℝ) * N) ((7 / 4 : ℝ) * N),
            ∀ r : ℝ, 0 < r → r ≤ r₀ →
              ∃ E : Set Omega, MeasurableSet E ∧ m ≤ steinhausMeasure.real E ∧
                E ⊆ steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ ∧
                (∀ η ξ : Omega, (∀ p ∈ Nat.primesLE (N / (2 * K)), η p = ξ p) →
                  (η ∈ E ↔ ξ ∈ E)) ∧
                ∀ η ∈ E,
                  (∀ j, ‖steinhausSmoothCarrier
                    (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
                      N (N / (2 * K)) η‖ ≤ 1) ∧
                  ∀ u : Fin J → ℂ,
                    H / Real.log N * ‖u‖ ^ 2 ≤
                      ∑ p ∈ largePrimes N (N / (2 * K)),
                        ‖∑ j, steinhausLargePrimeChannel
                          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
                            N p η * u j‖ ^ 2 := by
  obtain ⟨ω', hprefix, r₀, K, B, δ, m, hr₀, hK, hδ, hm, hcell, hcov⟩ :=
    exists_reflectedPrimalConditional_covariance_event hJ d b hd hdhalf hinj S ω hH
  have hmtop : m ≠ ∞ := by
    rw [← (hcell 0).2]
    exact measure_ne_top _ _
  have hmR : 0 < m.toReal := ENNReal.toReal_pos hm.ne' hmtop
  refine ⟨ω', hprefix, r₀, K, B, δ, m.toReal / 2, hr₀, hK, hδ, half_pos hmR, ?_⟩
  have hoffset : ∀ᶠ N : ℕ in atTop, ∀ j, 4 * |b j| ≤ (N : ℝ) := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (4 * |b j|))
  filter_upwards [hcov, hoffset,
    eventually_reflectedPrimalBoundedCentreEvent_inter_mass d b hd hdhalf hmR] with N hcovN hbN hgoodN
  refine ⟨hcovN.1, hcovN.2.1, ?_⟩
  intro tau htau r hr hrle
  have ht (j : Fin J) : (N : ℝ) ≤ tau + b j := by
    have h := hbN j
    have hab := neg_abs_le (b j)
    linarith [htau.1]
  let C : Set Omega := steinhausCharacterCell B (steinhausLogPhaseShift ω' (-tau)) δ
  let G : Set Omega := reflectedPrimalBoundedCentreEvent d b tau r N (N / (2 * K))
  have hC : MeasurableSet C := (hcell tau).1
  have hG : MeasurableSet G := measurableSet_reflectedPrimalBoundedCentreEvent _ _ _ _ _ _
  have hmass : m.toReal ≤ steinhausMeasure.real C := by
    change m.toReal ≤ (steinhausMeasure C).toReal
    rw [(hcell tau).2]
  refine ⟨C ∩ G, hC.inter hG, hgoodN tau ht r hr _ C hmass, Set.inter_subset_left, ?_, ?_⟩
  · intro η ξ hphase
    have hsmall : ∀ p ∈ Nat.primesLE B, η p = ξ p := by
      intro p hp
      apply hphase p
      obtain ⟨hpB, hprime⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨hpB.trans hcovN.2.1, hprime⟩
    have hcellEq := steinhausCharacterCell_congr_smallPrimes B
      (steinhausLogPhaseShift ω' (-tau)) δ hsmall
    have hgoodEq := reflectedPrimalBoundedCentreEvent_congr_smallPrimes d b tau r N
      (N / (2 * K)) hphase
    exact and_congr hcellEq hgoodEq
  · intro η hη
    exact ⟨hη.2, fun u => hcovN.2.2 tau htau η hη.1 r hr hrle u⟩

end RHTower
