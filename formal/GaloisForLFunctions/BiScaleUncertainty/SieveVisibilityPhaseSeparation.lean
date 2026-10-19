import GaloisForLFunctions.BiScaleUncertainty.SieveVisibilityPerturbations
import GaloisForLFunctions.BiScaleUncertainty.SieveHighestModeStability

/-! Uniform translation separation for missing-coordinate and radial perturbations. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
open ValuationPhase ParityNeighborhood
set_option autoImplicit false

/-- A lower-depth mode has a fixed odd-power phase relation with the highest dyadic mode. -/
theorem top_phase_relation (N : ℕ) (hN : 2 ≤ N) (q : ℕ) (hq : q ∈ Icc 1 N)
    (hne : q ≠ TopAnchor.topOrder N) :
    ∃ p u : ℕ, Odd u ∧ ∀ h : ℕ,
      (translationPhase N (TopAnchor.topOrder N) h)^p = (translationPhase N q h)^u := by
  obtain ⟨j, hqeq⟩ := order_odd_decomposition (mem_Icc.mp hq).1
  let p : ℕ := 2^(Nat.log 2 N-q.factorization 2)
  let u : ℕ := 2*j+1
  have hv := TopAnchor.depth_lt_top hq hne
  have hH : TopAnchor.topOrder N = 2^(q.factorization 2)*p := by
    dsimp [TopAnchor.topOrder, p]
    rw [← pow_add]
    congr 1
    omega
  have hq' : q = 2^(q.factorization 2)*u := hqeq
  have hdH : TopAnchor.topOrder N ∣ N.factorial :=
    Nat.dvd_factorial (mem_Icc.mp (TopAnchor.topOrder_mem N hN)).1
      (mem_Icc.mp (TopAnchor.topOrder_mem N hN)).2
  have hdq : q ∣ N.factorial := Nat.dvd_factorial (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
  have he : p*(N.factorial/TopAnchor.topOrder N) = u*(N.factorial/q) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < (2 : ℕ)) (q.factorization 2))
    calc
      2^(q.factorization 2)*(p*(N.factorial/TopAnchor.topOrder N)) =
          TopAnchor.topOrder N*(N.factorial/TopAnchor.topOrder N) := by rw [hH]; ring
      _ = N.factorial := Nat.mul_div_cancel' hdH
      _ = q*(N.factorial/q) := (Nat.mul_div_cancel' hdq).symm
      _ = (2^(q.factorization 2)*u)*(N.factorial/q) :=
        congrArg (fun a => a*(N.factorial/q)) hq'
      _ = 2^(q.factorization 2)*(u*(N.factorial/q)) := Nat.mul_assoc _ _ _
  refine ⟨p, u, ⟨j, by dsimp [u]⟩, ?_⟩
  intro h
  exact translationPhase_relation N _ q h p u he

/-- A retained top coordinate prevents any translation from hiding the signed missing mode. -/
theorem spike_separation_of_relation (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (q : ℕ)
    (hq : q ∈ Icc 1 N) (hne : q ≠ TopAnchor.topOrder N)
    (hA : 1 ≤ |selbergMultiplesCoord N b (TopAnchor.topOrder N)|)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (h p u : ℕ) (hu : Odd u)
    (hphase : (translationPhase N (TopAnchor.topOrder N) h)^p = (translationPhase N q h)^u)
    (D : ℝ)
    (herr : ∀ n, |sieveSeq N (spikeWeights N b q (-t)) n-
      sieveSeq N (spikeWeights N b q t) (n+h)| ≤ D) :
    2*t ≤ ((p : ℝ)+u)*D := by
  let A : ℝ := selbergMultiplesCoord N b (TopAnchor.topOrder N)
  let z : ℂ := translationPhase N (TopAnchor.topOrder N) h
  let w : ℂ := translationPhase N q h
  have hstrong := translated_coordinate_error N (spikeWeights N b q t)
    (spikeWeights N b q (-t)) h D herr
    ((N.factorial/TopAnchor.topOrder N : ℕ) : ZMod N.factorial)
  rw [frequency_order (TopAnchor.topOrder_mem N hN),
    coordinate_spikeWeights N b q (-t) hq, coordinate_spikeWeights N b q t hq] at hstrong
  simp only [spikeProfile, if_neg hne.symm] at hstrong
  change ‖(A : ℂ)-z*(A : ℂ)‖ ≤ D at hstrong
  rw [show (A : ℂ)-z*(A : ℂ) = (A : ℂ)*(1-z) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs] at hstrong
  have hz : ‖1-z‖ ≤ D :=
    (le_mul_of_one_le_left (norm_nonneg _) hA).trans hstrong
  have hweak := translated_coordinate_error N (spikeWeights N b q t)
    (spikeWeights N b q (-t)) h D herr ((N.factorial/q : ℕ) : ZMod N.factorial)
  rw [frequency_order hq, coordinate_spikeWeights N b q (-t) hq,
    coordinate_spikeWeights N b q t hq] at hweak
  simp only [spikeProfile, if_true, Complex.ofReal_neg] at hweak
  change ‖-(t : ℂ)-w*(t : ℂ)‖ ≤ D at hweak
  rw [show -(t : ℂ)-w*(t : ℂ) = -(t : ℂ)*(1+w) by ring,
    norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] at hweak
  have hzsmall : t*‖1-z‖ ≤ D := by
    have hh := mul_le_mul_of_nonneg_right ht1 (norm_nonneg (1-z))
    exact (show t*‖1-z‖ ≤ ‖1-z‖ by simpa only [one_mul] using hh).trans hz
  have hp := phase_incompatibility z w p u
    (translationPhase_norm N _ h).le (translationPhase_norm N q h).le hu hphase
  calc
    _ ≤ (p : ℝ)*(t*‖1-z‖)+(u : ℝ)*(t*‖1+w‖) := by
      nlinarith only [mul_le_mul_of_nonneg_left hp ht]
    _ ≤ (p : ℝ)*D+(u : ℝ)*D :=
      add_le_add (mul_le_mul_of_nonneg_left hzsmall (Nat.cast_nonneg p))
        (mul_le_mul_of_nonneg_left hweak (Nat.cast_nonneg u))
    _ = _ := by ring

/-- Radial scaling leaves a linear Fourier error under every natural translation. -/
theorem radial_separation (N : ℕ) (b : ℕ → ℝ) (q : ℕ) (hq : q ∈ Icc 1 N)
    (hA : 2 ≤ |selbergMultiplesCoord N b q|) (t : ℝ) (ht : 0 ≤ t) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N (fun d => (1+t)*b d) n-sieveSeq N b (n+h)| ≤ D) :
    2*t ≤ D := by
  let A : ℝ := selbergMultiplesCoord N b q
  let z : ℂ := translationPhase N q h
  have he := translated_coordinate_error N b (fun d => (1+t)*b d) h D herr
    ((N.factorial/q : ℕ) : ZMod N.factorial)
  rw [frequency_order hq, coordinate_scale] at he
  change ‖(((1+t)*A : ℝ) : ℂ)-z*(A : ℂ)‖ ≤ D at he
  have hl := (norm_sub_norm_le (((1+t)*A : ℝ) : ℂ) (z*(A : ℂ))).trans he
  have hz : ‖z‖ = 1 := translationPhase_norm N q h
  simp only [norm_mul, hz, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1+t)] at hl
  have htA : 2*t ≤ |A| * t := mul_le_mul_of_nonneg_right hA ht
  nlinarith only [hl, htA]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.LinearVisibility
