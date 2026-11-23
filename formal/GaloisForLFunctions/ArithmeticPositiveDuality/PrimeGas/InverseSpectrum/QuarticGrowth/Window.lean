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

/-- Independent half turns in one block leave a coherent complex sum with a telescoping quadratic deficit. -/
theorem exists_window_profile {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) (N : ℕ)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) :
    ∃ b : SpectralBand 1, (N:ℝ)*occupationWeight (2*N)^z.re ≤ 4*‖relativePartition b z‖ ∧
      relativeReading quadraticResponse b ≤ occupationWeight N^2 := by
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
  refine ⟨finiteProfile (S.image (fun j => N+j)) x hmem,?_,?_⟩
  · rw [finiteProfile_partition,sum_image hj.injOn]
    exact hsum.trans hsel
  · rw [finiteProfile_quadratic,sum_image hj.injOn]
    exact window_deficit N hS x (fun j hj' => (hx j (hS hj')).1)

private theorem window_mem_closure (b : SpectralBand 1) : b ∈ closure (physicalSpectra 1) := by
  rw [closure_rank_one_spectra]
  exact mem_univ _

/-- An actual conserving omission witnesses a large clock amplitude and small fourth-trace loss simultaneously. -/
theorem physical_window_witness {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) (N : ℕ) (hN : 0 < N)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) :
    ∃ (P : Projection) (hd : MissingDimension P 1) (hc : Conserving (projected P)),
      (N:ℝ)*occupationWeight (2*N)^z.re/8 < ‖relativePartition (physicalSpectrum P hd hc) z‖ ∧
      traceLoss (projected P) < 2*occupationWeight N^2 := by
  let A := (N:ℝ)*occupationWeight (2*N)^z.re
  let U := {c : SpectralBand 1 | A/8 < ‖relativePartition c z‖ ∧ relativeReading quadraticResponse c < 2*occupationWeight N^2}
  have hA : 0 < A := mul_pos (Nat.cast_pos.mpr hN) (Real.rpow_pos_of_pos (occupationWeight_pos _) _)
  have hopen : IsOpen U := (isOpen_lt continuous_const (continuous_relativePartition_spectrum hz 1).norm).inter
    (isOpen_lt (continuous_relativeReading quadraticResponse 1) continuous_const)
  obtain ⟨b,hb,hd⟩ := exists_window_profile hz ht N hsize
  change A ≤ 4*‖relativePartition b z‖ at hb
  have hin : b ∈ U := ⟨by linarith only [hA,hb],by linarith only [hd,sq_pos_of_pos (occupationWeight_pos N)]⟩
  obtain ⟨c,hc,P,hp,hq,rfl⟩ := mem_closure_iff.mp (window_mem_closure b) U hopen hin
  exact ⟨P,hp,hq,hc.1,(quadratic_physicalReading P hp hq) ▸ hc.2⟩

/-- Every nonnegative physical trace power is tested by the same coherent block. -/
theorem window_power_test {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) (N : ℕ)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) {p K : ℝ} (hp : 0 ≤ p) (h : traceControlsAt 1 z p K) :
    ((N:ℝ)*occupationWeight (2*N)^z.re)^p ≤ (4:ℝ)^p*(K*occupationWeight N^2) := by
  obtain ⟨b,hl,hd⟩ := exists_window_profile hz ht N hsize
  have hf := trace_control_on_closure hz hp h (window_mem_closure b)
  have hK := trace_coefficient_nonneg 0 hz hp h
  have he := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (occupationWeight_pos _).le _)) hl hp
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) (norm_nonneg _)] at he
  exact he.trans (mul_le_mul_of_nonneg_left (hf.trans (mul_le_mul_of_nonneg_left hd hK)) (Real.rpow_nonneg (by norm_num) _))

theorem window_quartic_test {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) (N : ℕ)
    (hsize : (2*(N:ℝ)+1)*Real.pi ≤ z.im) {K : ℝ} (h : traceControlsAt 1 z 4 K) :
    ((N:ℝ)*occupationWeight (2*N)^z.re)^4 ≤ 4^4*(K*occupationWeight N^2) := by
  simpa only [show ∀ x : ℝ, x^(4:ℝ) = x^4 from fun x => Real.rpow_natCast x 4] using
    window_power_test hz ht N hsize (by norm_num : (0:ℝ)≤4) h

#print axioms exists_window_profile
#print axioms physical_window_witness
#print axioms window_power_test
#print axioms window_quartic_test

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
