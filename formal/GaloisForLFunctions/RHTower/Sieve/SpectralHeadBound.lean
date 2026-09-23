import GaloisForLFunctions.RHTower.Sieve.LadderPrimeMajorant
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedAnnulusBound
import GaloisForLFunctions.RHTower.Sieve.OmegaBudgetFromAnnulus
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange

/-!
# The head of the Gallagher split, in closed form

Feeding the annulus bound `V_j ≤ ρ·Q_j` and the disc bound `U_j ≤ s·B₀/Q_j` into the two-weight cut
window estimate turns the frequencies below the Gallagher cut into a single explicit expression: a
geometric sum for the annulus and the ladder's counting sum for the disc.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The designated primes of a ladder lie in the ladder's range. -/
theorem primesRange_ladder_bounds {z₀ z L : ℕ} {Q η : ℝ} (hQ : Q = (z₀ : ℝ)) (hη : 0 ≤ η)
    (hQ0 : 0 ≤ Q) (hz : z = ⌊Q * (1 + η) ^ L⌋₊) :
    ∀ p ∈ primesRange z₀ z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L := by
  intro p hp
  rw [mem_primesRange] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  constructor
  · rw [hQ]
    exact_mod_cast hlo
  · have : (p : ℝ) ≤ ((⌊Q * (1 + η) ^ L⌋₊ : ℕ) : ℝ) := by
      rw [← hz]
      exact_mod_cast hhi
    refine this.trans (Nat.floor_le ?_)
    positivity

/-- **The head of the Gallagher split, in closed form.** -/
theorem integral_normSq_omegaWeighted_head_closed {z₀ z L : ℕ} {B₀ : ℕ} {Q η w₀ G ρ s : ℝ}
    (hQ : Q = (z₀ : ℝ)) (hQ1 : 1 < Q) (hη : 0 < η) (hG : 1 ≤ G) (hw₀ : 0 ≤ w₀) (hwG : w₀ ≤ G)
    (hL : 1 ≤ L) (hρ : 0 < ρ) (hs : 0 ≤ s) (hz : z = ⌊Q * (1 + η) ^ L⌋₊)
    (hGle : ∀ j ∈ Finset.range L, G ≤ (B₀ : ℝ) / (Q * (1 + η) ^ j))
    (hV : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-G) G \ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ ρ * (Q * (1 + η) ^ j))
    (hU : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖logPoly moebiusCoeff (geomCofactorBlockAt 1 B₀ Q η j) w‖
        ≤ s * ((B₀ : ℝ) / (Q * (1 + η) ^ j))) :
    (∫ w in Set.Icc (-G) G,
        ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (Finset.Icc 1 B₀) w‖ ^ (2 : ℕ))
      ≤ 2 * ((ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2)
              * ((L : ℝ) * (B₀ : ℝ) + Q * (((1 + η) ^ L - 1) / η))) ^ (2 : ℕ)
            + (∑ j ∈ Finset.range L,
                discMajorant (primesRange z₀ z) B₀ Q η s w₀ j) ^ (2 : ℕ))
        + 2 * ((5 * Real.pi / 2 * G
              + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
            * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
              * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                  * ((1 + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                    + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ)))) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ1
  have hη0 : (0 : ℝ) ≤ η := hη.le
  have hG0 : (0 : ℝ) < G := lt_of_lt_of_le zero_lt_one hG
  have hPprime : ∀ q ∈ primesRange z₀ z, q.Prime := fun q hq => (mem_primesRange.1 hq).1
  have hPbd := primesRange_ladder_bounds (z := z) (L := L) hQ hη0 hQ0.le hz
  have hPge : ∀ p ∈ primesRange z₀ z, Q ≤ (p : ℝ) := fun p hp => (hPbd p hp).1.le
  set c : ℕ → ℝ := fun j => primeStepMajorant B₀ Q η ρ j with hc
  set d : ℕ → ℝ := fun j => discMajorant (primesRange z₀ z) B₀ Q η s w₀ j with hd
  set V : ℕ → ℝ := fun j => ρ * (Q * (1 + η) ^ j) with hV'
  set U : ℕ → ℝ := fun j => s * ((B₀ : ℝ) / (Q * (1 + η) ^ j)) with hU'
  set Vlow : ℕ → ℝ := fun j => ((geomBlock (primesRange z₀ z) Q (1 + η) j).card : ℝ) with hVlow
  have hVpos : ∀ j, 0 ≤ V j := by
    intro j
    rw [hV']
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hUpos : ∀ j, 0 ≤ U j := by
    intro j
    rw [hU']
    have : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
    positivity
  have hVlowpos : ∀ j, 0 ≤ Vlow j := fun j => Nat.cast_nonneg _
  have hcpos : ∀ j ∈ Finset.range L, 0 < c j := fun j _ =>
    primeStepMajorant_pos hQ0 hη0 hρ j
  have hdpos : ∀ j ∈ Finset.range L, 0 < d j := fun j _ =>
    discMajorant_pos hQ0 hη0 hs j
  have hcT : ∀ j ∈ Finset.range L, V j ^ (2 : ℕ) * ladderStepMVT B₀ Q η G j ≤ c j ^ (2 : ℕ) := by
    intro j hj
    exact primeStepMajorant_sq_ge hQ0 hη0 hG0.le j (hGle j hj) (hVpos j) le_rfl
  have hdT : ∀ j ∈ Finset.range L, Vlow j ^ (2 : ℕ) * U j ^ (2 : ℕ) * (2 * w₀) ≤ d j ^ (2 : ℕ) := by
    intro j _
    exact discMajorant_sq_ge hQ0 hη0 hs hw₀ j (hUpos j) (hVlowpos j) le_rfl le_rfl
  have hlowP : ∀ j ∈ Finset.range L, ∀ w ∈ Set.Icc (-w₀) w₀,
      ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1 + η) j) w‖ ≤ Vlow j := by
    intro j _ w _
    exact norm_primeBlockPoly_le_card _ w
  have hmain := integral_normSq_omegaWeighted_annulus_optimal_two_le (P := primesRange z₀ z)
    (A₀ := 1) (B₀ := B₀) (by omega) hQ1 hη0 hG hw₀ hwG hL hPprime hPge hPbd
    c d V U Vlow hcpos hdpos hVpos hUpos hVlowpos hcT hdT hV hlowP hU
  have hcsum : (∑ j ∈ Finset.range L, c j)
      = ρ * Real.sqrt (5 * Real.pi / 2 + 5 * Real.exp 1 / 2)
        * ((L : ℝ) * (B₀ : ℝ) + Q * (((1 + η) ^ L - 1) / η)) :=
    sum_primeStepMajorant_eq hη L
  rw [hcsum] at hmain
  simpa [hd] using hmain

end

end RHTower.Sieve
