import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.BoundedVariationDilationEnergy
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.DilationPacketOperator
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMixedMoments
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLiouvilleGaugeFlipsThePolarDivergence

/-!
# Norm costs for the neutral complete form

The prime Schur bound and the two-moment complete remainder give a
polynomial overlap bound on the neutral hyperplane. Polarization then
transports energies across projections whose norms decay polynomially
in the horizon parameter.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- Ordinary square mass is bounded by the horizon times harmonic square mass. -/
theorem packet_ordinary_square_le_horizon (N : ℕ) (F : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, F n ^ 2) ≤ (N : ℝ) * ‖packetVector F N‖ ^ 2 := by
  rw [packetVector_norm_sq, mul_sum]
  apply sum_le_sum
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
  calc
    _ = (n : ℝ) * (F n ^ 2 / n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hnN (by positivity)

/-- The prime dilation form has a logarithmic norm bound at every horizon. -/
theorem abs_jumpEnergy_le_log_norm (N : ℕ) (F : ℕ → ℝ) :
    |jumpEnergy N F| ≤
      (2 * (Real.log 8 + 5)) * (Real.log N + 1) * ‖packetVector F N‖ ^ 2 := by
  have hH : 0 ≤ ∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ) :=
    sum_nonneg fun n _ => by positivity
  have hL := Real.log_natCast_nonneg N
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have h48 : Real.log 4 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  have hp : |primeDilationForm N F| ≤
      (Real.log N + (Real.log 4 + 4)) * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) := by
    have h := abs_atomicWeilForm_le N (atomAmplitude F)
    rw [atomicWeilForm_atomAmplitude] at h
    convert h using 1
    congr 1
    exact sum_congr rfl fun n hn => (atomAmplitude_sq (mem_Icc.mp hn).1 F).symm
  have hd : |mertensDiagonal N F| ≤
      (Real.log 8 + 4 + Real.log N) * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) := by
    calc
      _ = |(mertensDiagonal N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))) +
          Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))| := by rw [sub_add_cancel]
      _ ≤ |mertensDiagonal N F - Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))| +
          |Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ))| := abs_add_le _ _
      _ ≤ (Real.log 8 + 4) * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
          Real.log N * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) := by
        rw [abs_of_nonneg (mul_nonneg hL hH)]
        exact add_le_add (abs_mertensDiagonal_sub_log_mass_le N F) le_rfl
      _ = _ := by ring
  have he : jumpEnergy N F = mertensDiagonal N F - primeDilationForm N F := by
    rw [primeDilationForm_eq]
    ring
  rw [he, packetVector_norm_sq]
  refine ((abs_sub _ _).trans (add_le_add hd hp)).trans ?_
  have hco : Real.log 8 + 4 + Real.log N + (Real.log N + (Real.log 4 + 4)) ≤
      2 * (Real.log 8 + 5) * (Real.log N + 1) := by
    nlinarith only [hL, h8, h48, mul_nonneg hL h8]
  convert mul_le_mul_of_nonneg_right hco hH using 1; ring

/-- On the neutral hyperplane the complete form costs only a polynomial overlap times a logarithm. -/
theorem exists_complete_packet_neutral_norm_cost {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (c : ℝ),
      1 ≤ N → 1 ≤ c → c / N ≤ 1 / 3 → ∀ F : ℕ → ℝ,
      (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      |completeWeilEnergy φ c N (packetVector F N)| ≤
        C * c ^ 3 * (Real.log N + 1) * ‖packetVector F N‖ ^ 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  refine ⟨A + B + 2 * (Real.log 8 + 5), by positivity, ?_⟩
  intro N c hN hc hw F hF
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hc23 : c ^ 2 ≤ c ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hc (sq_nonneg c)
    nlinarith only [h]
  have hc3 : 1 ≤ c ^ 3 := (show 1 ≤ c ^ 2 by nlinarith only [hc]).trans hc23
  have herr : |completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F| ≤
      (A + B) * c ^ 3 * (Real.log N + 1) * ‖packetVector F N‖ ^ 2 := by
    have h := hbound c N hc hN hw F hF
    rw [← packetVector_norm_sq] at h
    refine h.trans ?_
    calc
      _ ≤ A * c ^ 2 * ‖packetVector F N‖ ^ 2 +
          (B * c ^ 3 * (Real.log N + 1) / N) * ((N : ℝ) * ‖packetVector F N‖ ^ 2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (packet_ordinary_square_le_horizon N F) (by positivity))
      _ = (A * c ^ 2 + B * c ^ 3 * (Real.log N + 1)) * ‖packetVector F N‖ ^ 2 := by
        field_simp [hN0.ne']
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hterm : A * c ^ 2 ≤ A * c ^ 3 * (Real.log N + 1) :=
          (mul_le_mul_of_nonneg_left hc23 hA).trans
            (le_mul_of_one_le_right (by positivity) (by linarith only [hL]))
        nlinarith only [hterm]
  have hj : |jumpEnergy N F| ≤
      (2 * (Real.log 8 + 5)) * c ^ 3 * (Real.log N + 1) * ‖packetVector F N‖ ^ 2 := by
    refine (abs_jumpEnergy_le_log_norm N F).trans ?_
    have h := mul_le_mul_of_nonneg_left hc3
      (show 0 ≤ (2 * (Real.log 8 + 5)) * (Real.log N + 1) * ‖packetVector F N‖ ^ 2 by positivity)
    simpa only [mul_one] using h.trans_eq (by ring)
  calc
    _ = |(completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F) + jumpEnergy N F| :=
      by rw [sub_add_cancel]
    _ ≤ |completeWeilEnergy φ c N (packetVector F N) - jumpEnergy N F| + |jumpEnergy N F| :=
      abs_add_le _ _
    _ ≤ _ := (add_le_add herr hj).trans_eq (by ring)

/-- Polarization of the literal complete packet form. -/
theorem completePacketPairing_polarization (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (F G : ℕ → ℝ) (s : ℝ) :
    completeWeilEnergy φ c N (packetVector (fun n => F n + s * G n) N) -
      completeWeilEnergy φ c N (packetVector (fun n => F n - s * G n) N) =
        4 * s * completePacketPairing φ c N F G := by
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hcross :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector G N), packetVector F N⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ := by
    rw [hs, real_inner_comm]
  have hminus : (fun n => F n - s * G n) = (fun n => F n + (-s) * G n) := by
    funext n
    ring
  rw [hminus]
  simp only [packetVector_add, packetVector_const_mul, completeWeilEnergy, completePacketPairing,
    map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hcross]
  ring

/-- The neutral norm cost controls mixed pairings against every unit neutral receiver. -/
theorem completePacketPairing_sq_le_of_neutral_norm_cost
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ F : ℕ → ℝ, (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      |completeWeilEnergy φ c N (packetVector F N)| ≤ D * ‖packetVector F N‖ ^ 2)
    (F G : ℕ → ℝ) (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0)
    (hG : ∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) (hunit : ‖packetVector G N‖ ≤ 1) :
    completePacketPairing φ c N F G ^ 2 ≤ D ^ 2 * ‖packetVector F N‖ ^ 2 := by
  have hGsq : ‖packetVector G N‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hunit 2
  have h (s : ℝ) : |4 * s * completePacketPairing φ c N F G| ≤
      2 * D * ‖packetVector F N‖ ^ 2 + 2 * s ^ 2 * D := by
    have hp : ∑ n ∈ Icc 1 N, (F n + s * G n) / (n : ℝ) = 0 := by
      simp only [add_div, mul_div_assoc, sum_add_distrib, ← mul_sum, hF, hG, mul_zero, add_zero]
    have hm : ∑ n ∈ Icc 1 N, (F n - s * G n) / (n : ℝ) = 0 := by
      simp only [sub_div, mul_div_assoc, sum_sub_distrib, ← mul_sum, hF, hG, mul_zero, sub_zero]
    have hpar : ‖packetVector (fun n => F n + s * G n) N‖ ^ 2 +
        ‖packetVector (fun n => F n - s * G n) N‖ ^ 2 =
          2 * ‖packetVector F N‖ ^ 2 + 2 * s ^ 2 * ‖packetVector G N‖ ^ 2 := by
      simp only [packetVector_norm_sq, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun n _ => by ring
    rw [← completePacketPairing_polarization]
    calc
      _ ≤ D * ‖packetVector (fun n => F n + s * G n) N‖ ^ 2 +
          D * ‖packetVector (fun n => F n - s * G n) N‖ ^ 2 :=
        (abs_sub _ _).trans (add_le_add (hbound _ hp) (hbound _ hm))
      _ = 2 * D * ‖packetVector F N‖ ^ 2 + 2 * s ^ 2 * D * ‖packetVector G N‖ ^ 2 := by
        rw [← mul_add, hpar]
        ring
      _ ≤ _ := add_le_add le_rfl (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hGsq (by positivity : 0 ≤ 2 * s ^ 2 * D))
  let b := completePacketPairing φ c N F G
  have hh := mul_le_mul_of_nonneg_right ((le_abs_self (4 * (b / D) * b)).trans (h (b / D))) hD.le
  have hl : 4 * (b / D) * b * D = 4 * b ^ 2 := by field_simp [hD.ne']
  have hr : (2 * D * ‖packetVector F N‖ ^ 2 + 2 * (b / D) ^ 2 * D) * D =
      2 * D ^ 2 * ‖packetVector F N‖ ^ 2 + 2 * b ^ 2 := by field_simp [hD.ne']
  rw [hl, hr] at hh
  change b ^ 2 ≤ _
  linarith only [hh]

/-- Removing a small neutral profile changes complete energy by its norm and its square. -/
theorem abs_complete_packet_energy_sub_le_of_neutral_norm_cost
    (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ F : ℕ → ℝ, (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
      |completeWeilEnergy φ c N (packetVector F N)| ≤ D * ‖packetVector F N‖ ^ 2)
    (F G : ℕ → ℝ) (hF : ∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0)
    (hG : ∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) (hunit : ‖packetVector F N‖ ≤ 1) :
    |completeWeilEnergy φ c N (packetVector (fun n => F n - G n) N) -
      completeWeilEnergy φ c N (packetVector F N)| ≤
        D * (‖packetVector G N‖ ^ 2 + 2 * ‖packetVector G N‖) := by
  have hsq := completePacketPairing_sq_le_of_neutral_norm_cost φ c N hD hbound G F hG hF hunit
  have hpair : |completePacketPairing φ c N G F| ≤ D * ‖packetVector G N‖ := by
    have hnonneg := mul_nonneg hD.le (norm_nonneg (packetVector G N))
    nlinarith only [hsq, sq_abs (completePacketPairing φ c N G F),
      abs_nonneg (completePacketPairing φ c N G F), hnonneg]
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr (completeWeilMatrix_isHermitian φ c N)
  have hcross :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector G N), packetVector F N⟫ := by
    rw [hs, real_inner_comm]
  have he : completeWeilEnergy φ c N (packetVector (fun n => F n - G n) N) -
      completeWeilEnergy φ c N (packetVector F N) =
        completeWeilEnergy φ c N (packetVector G N) - 2 * completePacketPairing φ c N G F := by
    have hminus : (fun n => F n - G n) = (fun n => F n + (-1 : ℝ) * G n) := by
      funext n
      ring
    rw [hminus]
    simp only [packetVector_add, packetVector_const_mul, completeWeilEnergy, completePacketPairing,
      map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hcross]
    ring
  rw [he]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (add_le_add (hbound G hG) (mul_le_mul_of_nonneg_left hpair (by norm_num))).trans_eq (by ring)

#print axioms exists_complete_packet_neutral_norm_cost
#print axioms completePacketPairing_sq_le_of_neutral_norm_cost
#print axioms abs_complete_packet_energy_sub_le_of_neutral_norm_cost

end GaloisForLFunctions.ArithmeticCouplingTheory
