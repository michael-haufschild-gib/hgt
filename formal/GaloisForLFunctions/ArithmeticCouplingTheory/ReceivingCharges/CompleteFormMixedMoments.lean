import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.CompleteFormMoments
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceDilationPairing

/-!
# The mixed complete-form error on the neutral hyperplane

Polarizing the two-moment remainder controls its pairing with every unit
neutral vector. The ordinary moment of a unit vector is at most the horizon,
so the same estimate applies to a growing orthogonal complement.
-/

noncomputable section

open Finset MeasureTheory
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCouplingTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- Literal polarized complete energy in packet coordinates. -/
def completePacketPairing (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (F G : ℕ → ℝ) : ℝ :=
  ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫

private theorem packet_add_mul (N : ℕ) (F G : ℕ → ℝ) (s : ℝ) :
    packetVector (fun n => F n + s * G n) N = packetVector F N + s • packetVector G N := by
  ext n
  change (F n + s * G n) / Real.sqrt (n : ℕ) =
    F n / Real.sqrt (n : ℕ) + s * (G n / Real.sqrt (n : ℕ))
  ring

private theorem complete_polarization (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    (F G : ℕ → ℝ) (s : ℝ) :
    completeWeilEnergy φ c N (packetVector (fun n => F n + s * G n) N) -
      completeWeilEnergy φ c N (packetVector (fun n => F n - s * G n) N) =
        4 * s * completePacketPairing φ c N F G := by
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c N)
  have hcross :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector G N), packetVector F N⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (packetVector F N), packetVector G N⟫ := by
    rw [hsym, real_inner_comm]
  have hminus : (fun n => F n - s * G n) = (fun n => F n + (-s) * G n) := by
    funext n
    ring
  rw [hminus, packet_add_mul, packet_add_mul]
  simp only [completeWeilEnergy, completePacketPairing, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hcross]
  ring

private theorem jump_polarization (N : ℕ) (F G : ℕ → ℝ) (s : ℝ) :
    jumpEnergy N (fun n => F n + s * G n) -
      jumpEnergy N (fun n => F n - s * G n) = 4 * s * jumpPairing N F G := by
  simp only [jumpEnergy, jumpPairing, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun kn _ => by ring

private def momentMajorant (N : ℕ) (u v : ℝ) (F : ℕ → ℝ) : ℝ :=
  u * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) + v * ∑ n ∈ Icc 1 N, F n ^ 2

private theorem moment_parallelogram (N : ℕ) (u v s : ℝ) (F G : ℕ → ℝ) :
    momentMajorant N u v (fun n => F n + s * G n) +
      momentMajorant N u v (fun n => F n - s * G n) =
        2 * momentMajorant N u v F + 2 * s ^ 2 * momentMajorant N u v G := by
  simp only [momentMajorant, mul_add, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

private theorem moment_of_unit_le {N : ℕ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (G : ℕ → ℝ) (hG : ‖packetVector G N‖ ≤ 1) :
    momentMajorant N u v G ≤ u + v * N := by
  have hh : (∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ)) ≤ 1 := by
    rw [← packetVector_norm_sq]
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hG 2
  have ho : (∑ n ∈ Icc 1 N, G n ^ 2) ≤
      (N : ℝ) * ∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    calc
      G n ^ 2 = (n : ℝ) * (G n ^ 2 / n) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hnN (by positivity)
  have ho' : (∑ n ∈ Icc 1 N, G n ^ 2) ≤ N :=
    ho.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N))
  exact (add_le_add (mul_le_mul_of_nonneg_left hh hu)
    (mul_le_mul_of_nonneg_left ho' hv)).trans_eq (by ring)

private theorem scalar_polarization_bound {a b d : ℝ} (hd : 0 < d)
    (h : ∀ s : ℝ, |4 * s * b| ≤ 2 * a + 2 * s ^ 2 * d) : b ^ 2 ≤ d * a := by
  have h' := (le_abs_self (4 * (b / d) * b)).trans (h (b / d))
  have hh := mul_le_mul_of_nonneg_right h' hd.le
  have hleft : 4 * (b / d) * b * d = 4 * b ^ 2 := by field_simp [hd.ne']
  have hright : (2 * a + 2 * (b / d) ^ 2 * d) * d = 2 * a * d + 2 * b ^ 2 := by
    field_simp [hd.ne']
  rw [hleft, hright] at hh
  linarith only [hh]

/-- Two packets with small complete-form moment costs also have small mixed remainder. -/
theorem exists_complete_packet_bilinear_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ F G : ℕ → ℝ,
        (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
        (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) →
        |completePacketPairing φ c N F G - jumpPairing N F G| ≤
          (A * c ^ 2 * ((∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
              ∑ n ∈ Icc 1 N, G n ^ 2 / (n : ℝ)) +
            (B * c ^ 3 * (Real.log N + 1) / N) *
              ((∑ n ∈ Icc 1 N, F n ^ 2) + ∑ n ∈ Icc 1 N, G n ^ 2)) / 2 := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  refine ⟨A, B, hA, hB, ?_⟩
  intro c N hc hN hw F G hF hG
  let u := A * c ^ 2
  let v := B * c ^ 3 * (Real.log N + 1) / N
  have hpneutral : ∑ n ∈ Icc 1 N, (F n + G n) / (n : ℝ) = 0 := by
    simp only [add_div, sum_add_distrib, hF, hG, add_zero]
  have hmneutral : ∑ n ∈ Icc 1 N, (F n - G n) / (n : ℝ) = 0 := by
    simp only [sub_div, sum_sub_distrib, hF, hG, sub_self]
  have hp := hbound c N hc hN hw (fun n => F n + G n) hpneutral
  have hm := hbound c N hc hN hw (fun n => F n - G n) hmneutral
  have he := complete_polarization φ c N F G 1
  have hj := jump_polarization N F G 1
  simp only [one_mul, mul_one] at he hj
  have hid : 4 * (completePacketPairing φ c N F G - jumpPairing N F G) =
      (completeWeilEnergy φ c N (packetVector (fun n => F n + G n) N) -
        jumpEnergy N (fun n => F n + G n)) -
      (completeWeilEnergy φ c N (packetVector (fun n => F n - G n) N) -
        jumpEnergy N (fun n => F n - G n)) := by linarith only [he, hj]
  have h : |4 * (completePacketPairing φ c N F G - jumpPairing N F G)| ≤
      2 * momentMajorant N u v F + 2 * momentMajorant N u v G := by
    rw [hid]
    calc
      _ ≤ momentMajorant N u v (fun n => F n + G n) +
          momentMajorant N u v (fun n => F n - G n) :=
        (abs_sub _ _).trans (add_le_add hp hm)
      _ = _ := by simpa only [one_mul, one_pow, mul_one] using moment_parallelogram N u v 1 F G
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
  dsimp only [momentMajorant, u, v] at h
  linarith only [h]

/-- Uniform mixed control on the harmonic-neutral hyperplane, including all complete-form terms. -/
theorem exists_complete_packet_mixed_moment_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφ0 : ∀ u, 0 ≤ φ u)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (c : ℝ) (N : ℕ), 1 ≤ c → 1 ≤ N → c / N ≤ 1 / 3 →
      ∀ F G : ℕ → ℝ,
        (∑ n ∈ Icc 1 N, F n / (n : ℝ) = 0) →
        (∑ n ∈ Icc 1 N, G n / (n : ℝ) = 0) → ‖packetVector G N‖ ≤ 1 →
        (completePacketPairing φ c N F G - jumpPairing N F G) ^ 2 ≤
          (1 + A * c ^ 2 + B * c ^ 3 * (Real.log N + 1)) *
            (A * c ^ 2 * (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) +
              (B * c ^ 3 * (Real.log N + 1) / N) * ∑ n ∈ Icc 1 N, F n ^ 2) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_complete_packet_two_moment_bound hφ hφ0 hsupp hM
  refine ⟨A, B, hA, hB, ?_⟩
  intro c N hc hN hw F G hF hG hunit
  let u := A * c ^ 2
  let v := B * c ^ 3 * (Real.log N + 1) / N
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : 0 ≤ u := mul_nonneg hA (sq_nonneg c)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hD : 0 < 1 + u + v * N := by positivity
  have hGbound := moment_of_unit_le hu hv G hunit
  have hGbound' : momentMajorant N u v G ≤ 1 + u + v * N := by linarith only [hGbound]
  have hneutral (s : ℝ) : ∑ n ∈ Icc 1 N, (F n + s * G n) / (n : ℝ) = 0 := by
    simp only [add_div, mul_div_assoc, sum_add_distrib, ← mul_sum, hF, hG, mul_zero, add_zero]
  have hmixed := scalar_polarization_bound hD (a := momentMajorant N u v F)
    (b := completePacketPairing φ c N F G - jumpPairing N F G) (by
      intro s
      have hp := hbound c N hc hN hw (fun n => F n + s * G n) (hneutral s)
      have hmneutral : ∑ n ∈ Icc 1 N, (F n - s * G n) / (n : ℝ) = 0 := by
        simpa only [neg_mul, ← sub_eq_add_neg] using hneutral (-s)
      have hm := hbound c N hc hN hw (fun n => F n - s * G n) hmneutral
      have hid : 4 * s * (completePacketPairing φ c N F G - jumpPairing N F G) =
          (completeWeilEnergy φ c N (packetVector (fun n => F n + s * G n) N) -
            jumpEnergy N (fun n => F n + s * G n)) -
          (completeWeilEnergy φ c N (packetVector (fun n => F n - s * G n) N) -
            jumpEnergy N (fun n => F n - s * G n)) := by
        have he := complete_polarization φ c N F G s
        have hj := jump_polarization N F G s
        linarith only [he, hj]
      rw [hid]
      calc
        _ ≤ momentMajorant N u v (fun n => F n + s * G n) +
            momentMajorant N u v (fun n => F n - s * G n) :=
          (abs_sub _ _).trans (add_le_add hp hm)
        _ = _ := moment_parallelogram N u v s F G
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
          hGbound' (by positivity : 0 ≤ 2 * s ^ 2)))
  have hcancel : v * N = B * c ^ 3 * (Real.log N + 1) := by
    dsimp only [v]
    rw [div_mul_cancel₀ _ hN0.ne']
  simpa only [momentMajorant, hcancel, u, v] using hmixed

#print axioms exists_complete_packet_mixed_moment_bound
#print axioms exists_complete_packet_bilinear_moment_bound

end GaloisForLFunctions.ArithmeticCouplingTheory
