import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.QuarticGrowth.Window

/-! # Physical witnesses for simultaneous bounds on amplitude and trace loss -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

/-- Strict amplitude and deficit inequalities at a limiting spectrum hold together in an actual system. -/
theorem physical_readout_neighborhood {r : ℕ} {z : ℂ} (hz : 0 < z.re) {b : SpectralBand r}
    (hb : b ∈ closure (physicalSpectra r)) {A B : ℝ} (ha : A < ‖relativePartition b z‖)
    (hd : relativeReading quadraticResponse b < B) :
    ∃ (P : Projection) (dim : MissingDimension P r) (hc : Conserving (projected P)),
      A < ‖relativePartition (physicalSpectrum P dim hc) z‖ ∧ traceLoss (projected P) < B := by
  let U := {c : SpectralBand r | A < ‖relativePartition c z‖ ∧ relativeReading quadraticResponse c < B}
  have hopen : IsOpen U := (isOpen_lt continuous_const (continuous_relativePartition_spectrum hz r).norm).inter
    (isOpen_lt (continuous_relativeReading quadraticResponse r) continuous_const)
  obtain ⟨c,hin,P,dim,hc,rfl⟩ := mem_closure_iff.mp hb U hopen (show b ∈ U from ⟨ha,hd⟩)
  exact ⟨P,dim,hc,hin.1,(quadratic_physicalReading P dim hc) ▸ hin.2⟩

/-- A scalar ground chord and its quadratic deficit can be measured simultaneously to arbitrary strict tolerances. -/
theorem physical_ground_chord (r : ℕ) {z : ℂ} (hz : 0 < z.re) (u : Ioc (0:ℝ) 1) {A B : ℝ}
    (ha : A < ‖1-(u.val:ℂ)^z‖) (hd : 1-u.val^2 < B) :
    ∃ (P : Projection) (dim : MissingDimension P (r+1)) (hc : Conserving (projected P)),
      A < ‖relativePartition (physicalSpectrum P dim hc) z‖ ∧ traceLoss (projected P) < B := by
  obtain ⟨b,hb,he⟩ := exists_ground_attenuation r u
  have hD := he (z := 2) (by norm_num)
  have hp : (u.val:ℂ)^(2:ℂ) = ((u.val^2:ℝ):ℂ) := by rw [Complex.ofReal_pow,← Complex.cpow_natCast]; rfl
  rw [partition_at_two,hp,← Complex.ofReal_one,← Complex.ofReal_sub] at hD
  exact physical_readout_neighborhood hz hb (by rwa [he hz]) ((Complex.ofReal_inj.mp hD).trans_lt hd)

/-- Each admissible clock chord in a finite occupation block can be selected independently at rank one. -/
theorem physical_coherent_block {z : ℂ} (hz : 0 < z.re) (N : ℕ) (hN : 0 < N) (x : ℕ → ℝ) {A : ℝ} (hA : 0 < A)
    (hx : ∀ j ∈ range N, x (N+j) ∈ Icc (occupationWeight (N+j+1)) (occupationWeight (N+j)))
    (hlen : ∀ j ∈ range N, A ≤ ‖(occupationWeight (N+j):ℂ)^z-(x (N+j):ℂ)^z‖) :
    ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      (N:ℝ)*A/8 < ‖relativePartition (physicalSpectrum P dim hc) z‖ ∧ traceLoss (projected P) < 2*occupationWeight N^2 := by
  let v (j : ℕ) := (occupationWeight (N+j):ℂ)^z-(x (N+j):ℂ)^z
  obtain ⟨S,hS,hsel⟩ := exists_complex_subset (range N) v
  have hsum := sum_le_sum hlen
  simp only [sum_const,card_range,nsmul_eq_mul] at hsum
  have hj : Function.Injective (fun j : ℕ => N+j) := fun _ _ he => Nat.add_left_cancel he
  let F := S.image (fun j => N+j)
  have hmem (k : ℕ) (hk : k ∈ F) : x k ∈ Icc (occupationWeight (k+1)) (occupationWeight k) := by
    obtain ⟨j,hj',rfl⟩ := mem_image.mp hk
    exact hx j (hS hj')
  let b := finiteProfile F x hmem
  have hb : b ∈ closure (physicalSpectra 1) := by rw [closure_rank_one_spectra]; exact mem_univ _
  have hL : (N:ℝ)*A ≤ 4*‖relativePartition b z‖ := by
    rw [finiteProfile_partition]
    simp only [F,sum_image hj.injOn]
    exact hsum.trans hsel
  have hD : relativeReading quadraticResponse b ≤ occupationWeight N^2 := by
    rw [finiteProfile_quadratic]
    simp only [F,sum_image hj.injOn]
    have hgap (j : ℕ) : 0 ≤ occupationWeight (N+j)^2-occupationWeight (N+j+1)^2 := sub_nonneg.mpr
      (pow_le_pow_left₀ (occupationWeight_pos _).le (occupationWeight_antitone (Nat.le_succ _)) 2)
    have he := sum_range_sub' (fun j => occupationWeight (N+j)^2) N
    simp only [Nat.add_zero,← Nat.add_assoc] at he
    refine (sum_le_sum (fun j hj' => sub_le_sub_left (pow_le_pow_left₀ (occupationWeight_pos _).le (hx j (hS hj')).1 2) _)).trans ?_
    exact (sum_le_sum_of_subset_of_nonneg hS (fun j _ _ => hgap j)).trans (he.trans_le (sub_le_self _ (sq_nonneg _)))
  apply physical_readout_neighborhood hz hb
  · linarith only [hL,mul_pos (Nat.cast_pos.mpr hN) hA]
  · linarith only [hD,sq_pos_of_pos (occupationWeight_pos N)]

#print axioms physical_ground_chord
#print axioms physical_coherent_block

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
