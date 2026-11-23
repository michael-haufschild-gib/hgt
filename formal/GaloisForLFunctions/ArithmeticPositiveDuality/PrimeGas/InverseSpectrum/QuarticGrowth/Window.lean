import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.HalfTurn
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.FiniteVariation

/-! # A block of independently attenuated half turns forces quartic growth -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

private theorem reciprocal_next (k : ℕ) :
    occupationWeight k*(1-occupationWeight (k+1)) = occupationWeight (k+1) := by
  simp only [occupationWeight_eq,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

private theorem window_fraction_admissible {z : ℂ} (ht : 0 < z.im) (N j : ℕ) (hj : j < N)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) :
    occupationWeight (N+j)*(halfTurnFraction ht.ne').val ∈ Icc (occupationWeight (N+j+1)) (occupationWeight (N+j)) := by
  let u := halfTurnFraction ht.ne'
  have ha : Real.pi/z.im ≤ occupationWeight (2*N) := by
    rw [occupationWeight_eq,← one_div,Nat.cast_mul,Nat.cast_ofNat]
    apply (div_le_div_iff₀ ht (show 0 < 2*(N:ℝ)+1 by positivity)).mpr
    simpa only [one_mul,mul_comm Real.pi] using hsize
  have hcost := ((halfTurn_fraction_loss ht).trans ha).trans (occupationWeight_antitone (show N+j+1 ≤ 2*N by omega))
  have hret : 1-occupationWeight (N+j+1) ≤ u.val := by change 1-u.val ≤ _ at hcost; linarith only [hcost]
  exact ⟨(reciprocal_next (N+j)).symm.trans_le (mul_le_mul_of_nonneg_left hret (occupationWeight_pos _).le),
    mul_le_of_le_one_right (occupationWeight_pos _).le u.property.2.le⟩

private theorem window_deficit (N : ℕ) {S : Finset ℕ} (hS : S ⊆ range N) (x : ℕ → ℝ)
    (hx : ∀ j ∈ S, occupationWeight (N+j+1) ≤ x (N+j)) :
    (∑ j ∈ S, (occupationWeight (N+j)^2-x (N+j)^2)) ≤ occupationWeight N^2 := by
  have he := sum_range_sub' (fun j => occupationWeight (N+j)^2) N
  simp only [Nat.add_zero,← Nat.add_assoc] at he
  calc
    _ ≤ ∑ j ∈ S, (occupationWeight (N+j)^2-occupationWeight (N+j+1)^2) := sum_le_sum (fun j hj =>
      sub_le_sub_left (pow_le_pow_left₀ (occupationWeight_pos _).le (hx j hj) 2) _)
    _ ≤ ∑ j ∈ range N, (occupationWeight (N+j)^2-occupationWeight (N+j+1)^2) :=
      sum_le_sum_of_subset_of_nonneg hS (fun j _ _ => sub_nonneg.mpr
        (pow_le_pow_left₀ (occupationWeight_pos _).le (occupationWeight_antitone (Nat.le_succ _)) 2))
    _ ≤ _ := he.trans_le (sub_le_self _ (sq_nonneg _))

/-- A single omitted direction can test any coherent subset of the half turns in the clock-scale block. -/
theorem window_quartic_test {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) (N : ℕ)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) {K : ℝ} (h : traceControlsAt 1 z 4 K) :
    ((N:ℝ)*occupationWeight (2*N)^z.re)^4 ≤ 4^4*(K*occupationWeight N^2) := by
  let u := halfTurnFraction ht.ne'
  let x (k : ℕ) := occupationWeight k*u.val
  let v (j : ℕ) := (occupationWeight (N+j):ℂ)^z-(x (N+j):ℂ)^z
  have hx (j : ℕ) (hj : j ∈ range N) := window_fraction_admissible ht N j (mem_range.mp hj) hsize
  have hlen (j : ℕ) (hj : j ∈ range N) : occupationWeight (2*N)^z.re ≤ ‖v j‖ := by
    change _ ≤ ‖(occupationWeight (N+j):ℂ)^z-((occupationWeight (N+j)*u.val:ℝ):ℂ)^z‖
    rw [norm_scaled_occupation_chord z (occupationWeight_pos _) u.property.1]
    have hj' := mem_range.mp hj
    exact (Real.rpow_le_rpow (occupationWeight_pos _).le (occupationWeight_antitone (show N+j ≤ 2*N by omega)) hz.le).trans
      (le_mul_of_one_le_right (Real.rpow_nonneg (occupationWeight_pos _).le _) (halfTurn_chord_one_le ht))
  obtain ⟨S,hS,hsel⟩ := exists_complex_subset (range N) v
  have hsum := sum_le_sum hlen
  simp only [sum_const,card_range,nsmul_eq_mul] at hsum
  have hj : Function.Injective (fun j : ℕ => N+j) := fun _ _ he => Nat.add_left_cancel he
  have hmem (k : ℕ) (hk : k ∈ S.image (fun j => N+j)) : x k ∈ Icc (occupationWeight (k+1)) (occupationWeight k) := by
    obtain ⟨j,hj',rfl⟩ := mem_image.mp hk
    exact hx j (hS hj')
  have hfinite := (rank_one_trace_finite_iff hz (by norm_num : (0:ℝ)<4)).mp h (S.image (fun j => N+j)) x hmem
  simp only [sum_image hj.injOn] at hfinite
  change ‖∑ j ∈ S, v j‖^(4:ℝ) ≤ _ at hfinite
  rw [show ‖∑ j ∈ S, v j‖^(4:ℝ) = ‖∑ j ∈ S, v j‖^4 from Real.rpow_natCast _ 4] at hfinite
  have hcost := window_deficit N hS x (fun j hj' => (hx j (hS hj')).1)
  have hK := trace_coefficient_nonneg 0 hz (by norm_num : (0:ℝ)≤4) h
  have he := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (occupationWeight_pos _).le _)) (hsum.trans hsel) 4
  rw [mul_pow] at he
  exact he.trans (mul_le_mul_of_nonneg_left (hfinite.trans (mul_le_mul_of_nonneg_left hcost hK)) (by norm_num))

#print axioms window_quartic_test

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
