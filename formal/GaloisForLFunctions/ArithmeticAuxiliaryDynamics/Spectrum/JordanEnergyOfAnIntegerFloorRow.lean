import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheHalfScaleOfTheRate
import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy

/-!
# Jordan energy and the integer multiplicities of a floor row

Fourier integration of a periodic interval indicator, as in El Kaouni
(arXiv:2610.42022, §3), divides its nonconstant modes by a discrete
derivative. For a balanced floor row the primitive is its centered
multiplicity. The Jordan-weighted squared divisor coordinates therefore
have a sharp ceiling. Its defect measures every intermediate multiplicity.
-/

noncomputable section
open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

/-- Jordan-weighted energy of the multiples coordinates above the mean mode. -/
def jordanEnergy (K : ℕ) (c : ℕ →₀ ℤ) : ℝ :=
  ∑ q ∈ Icc 2 K, jordanTotient2 q * selbergMultiplesCoord K (fun k => (c k : ℝ)) q ^ 2

variable {c : ℕ →₀ ℤ} {m B K : ℕ}

private theorem support_le (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    c.support ⊆ Icc 1 K := fun k hk => mem_Icc.mpr ⟨Nat.pos_of_ne_zero
      (fun h => Finsupp.mem_support_iff.mp hk (h ▸ hP.zero)), hK k hk⟩

/-- The centered floor multiplicity is the zero-mean primitive of its divisor jumps. -/
theorem centered_floor (hP : IsProducer c m B) (hK : AlphabetLE c K) (r : ℕ) :
    weightedCenteredSawtoothSum K (fun k => (c k : ℝ)) r =
      (stepWeight c r : ℝ) - (peak c : ℝ)/2 := by
  rw [stepWeight_eq_mean_add hP.zero hP.balanced, add_sub_cancel_left,
    weightedCenteredSawtoothSum, ← sum_neg_distrib]
  rw [← sum_subset (support_le hP hK) (fun k _ hk => by
    simp only [Finsupp.notMem_support_iff.mp hk, Int.cast_zero, zero_mul, neg_zero])]
  apply sum_congr rfl
  intro k hk
  rw [centeredDiscreteSawtooth_eq_mod_sub_half (mem_Icc.mp (support_le hP hK hk)).1]
  unfold residue
  ring

private theorem factorial_step (hP : IsProducer c m B) (hK : AlphabetLE c K) (r : ℕ) :
    stepWeight c r = stepWeight c (r % K.factorial) := by
  conv_lhs => rw [← Nat.div_add_mod r K.factorial, Nat.mul_comm K.factorial]
  exact stepWeight_periodic hP.zero hP.balanced
    (fun k hk => Nat.dvd_factorial (mem_Icc.mp (support_le hP hK hk)).1 (hK k hk)) _ _

/-- Exact defect below the Jordan ceiling. A phase of intermediate height
pays its multiplicity times its distance from the peak. -/
theorem jordan_defect (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    3*(peak c : ℝ)^2-jordanEnergy K c = 12/(K.factorial : ℝ) *
      ∑ r ∈ range K.factorial, (stepWeight c r : ℝ)*((peak c : ℝ)-stepWeight c r) := by
  have hP0 : (K.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  rw [jordanEnergy, ← twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal, sievePrimitiveEnergy]
  simp_rw [centered_floor hP hK]
  field_simp [hP0]
  have he : ∑ r ∈ range K.factorial,
        (((stepWeight c r : ℝ)-(peak c : ℝ)/2)^2 +
          (stepWeight c r : ℝ)*((peak c : ℝ)-stepWeight c r)) =
      K.factorial*((peak c : ℝ)^2/4) := by
    simp_rw [show ∀ a w : ℝ, (a-w/2)^2+a*(w-a)=w^2/4 by intros; ring]
    rw [sum_const, card_range, nsmul_eq_mul]
  rw [sum_add_distrib] at he
  linarith only [he]

private theorem defectTerm_nonneg (hP : IsProducer c m B) (r : ℕ) :
    0 ≤ (stepWeight c r : ℝ)*((peak c : ℝ)-stepWeight c r) :=
  mul_nonneg (by exact_mod_cast hP.nonneg r) (sub_nonneg.mpr (by exact_mod_cast hP.stepWeight_le_peak r))

/-- Every admissible integer row obeys the same quadratic ceiling. -/
theorem jordan_ceiling (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    jordanEnergy K c ≤ 3*(peak c : ℝ)^2 := by
  apply sub_nonneg.mp
  rw [jordan_defect hP hK]
  exact mul_nonneg (by positivity) (sum_nonneg fun r _ => defectTerm_nonneg hP r)

/-- The ceiling is saturated exactly by rows taking only zero and peak height. -/
theorem jordan_ceiling_eq_iff (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    jordanEnergy K c = 3*(peak c : ℝ)^2 ↔ ∀ r, stepWeight c r = 0 ∨ stepWeight c r = peak c := by
  have he := jordan_defect hP hK
  have hfac : 12/(K.factorial : ℝ) ≠ 0 := ne_of_gt (by positivity)
  constructor
  · intro hh r
    rw [hh, sub_self] at he
    have hz := (mul_eq_zero.mp he.symm).resolve_left hfac
    have hterm := (sum_eq_zero_iff_of_nonneg (fun j _ => defectTerm_nonneg hP j)).mp hz
      (r % K.factorial) (mem_range.mpr (Nat.mod_lt _ (Nat.factorial_pos K)))
    rw [← factorial_step hP hK r] at hterm
    rcases mul_eq_zero.mp hterm with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast (sub_eq_zero.mp h).symm)
  · intro hh
    have hz : ∑ r ∈ range K.factorial, (stepWeight c r : ℝ)*((peak c : ℝ)-stepWeight c r) = 0 := by
      apply sum_eq_zero
      intro r _
      rcases hh r with h | h <;> simp [h]
    rw [hz, mul_zero] at he
    linarith only [he]

/-- For integer rows the spectral equality is an arithmetic divisibility
test on the letters alone. Dividing an extremizer by its peak leaves a
row with multiplicities zero and one. -/
theorem saturation_iff_peak_dvd_letters (hP : IsProducer c m B) (hK : AlphabetLE c K) :
    jordanEnergy K c = 3*(peak c : ℝ)^2 ↔ ∀ k, peak c ∣ c k := by
  rw [jordan_ceiling_eq_iff hP hK]
  constructor
  · intro hh
    have hd (r : ℕ) : peak c ∣ stepWeight c r := by
      rcases hh r with h | h <;> simp [h]
    have hi (n : ℕ) (hn : 0 < n) : peak c ∣ increment c n := by
      obtain ⟨r,rfl⟩ : ∃ r, n = r+1 := ⟨n-1, by omega⟩
      have he := stepWeight_succ c r
      rw [show increment c (r+1) = stepWeight c (r+1)-stepWeight c r by linarith only [he]]
      exact dvd_sub (hd _) (hd _)
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hP.zero]
    rw [coeff_eq_moebius_increment c hk]
    exact Finset.dvd_sum fun x hx => dvd_mul_of_dvd_right
      (hi x.2 (Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx))) _
  · intro hh r
    have hd : peak c ∣ stepWeight c r := Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (hh k) _
    rcases eq_or_lt_of_le (hP.nonneg r) with h | h
    · exact Or.inl h.symm
    · exact Or.inr ((hP.stepWeight_le_peak r).antisymm (Int.le_of_dvd h hd))

/-- A long initial producer window constrains its full Jordan spectrum
through its slope excess. Every sample uses the actual multiplicity. -/
theorem window_energy_le_excess (hP : IsProducer c m B) (hK : AlphabetLE c K) (hK2 : 2 ≤ K)
    (L : ℕ) (hL : L < B) :
    ((L:ℝ)-(2*(K:ℝ)^2-1)) * jordanEnergy K c ≤
      12*((L:ℝ)*((m:ℝ)-(peak c : ℝ)/2)^2 + m*(1+(L:ℝ))^2*excess c m B) := by
  let E := sievePrimitiveEnergy K (fun k => (c k : ℝ))
  have hwin := abs_window_sum_sq_weightedCenteredSawtoothSum_sub_le hK2
    (fun k => (c k : ℝ)) 0 L
  simp only [Nat.zero_add, centered_floor hP hK] at hwin
  have hlow := (abs_le.mp hwin).1
  have hloc (r : ℕ) (hr : r ∈ Icc 1 L) :
      ((stepWeight c r : ℝ)-(peak c : ℝ)/2)^2 ≤
      ((m : ℝ)-(peak c : ℝ)/2)^2 + m*((stepWeight c r : ℝ)-m) := by
    have hm : (m : ℝ) ≤ stepWeight c r := by
      exact_mod_cast hP.window r (mem_Ico.mpr ⟨(mem_Icc.mp hr).1, (mem_Icc.mp hr).2.trans_lt hL⟩)
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm)
      (sub_nonneg.mpr (show (stepWeight c r : ℝ) ≤ peak c by exact_mod_cast hP.stepWeight_le_peak r))]
  have hc := sum_le_sum hloc
  rw [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, ← mul_sum] at hc
  have hshift : ∑ r ∈ Icc 1 L, ((stepWeight c r : ℝ)-m) =
      ∑ j ∈ range L, ((stepWeight c (1+j) : ℝ)-m) := by
    apply sum_nbij' (fun r => r-1) (fun j => 1+j)
    · intro r hr; simp only [mem_Icc] at hr; simp only [mem_range]; omega
    · intro j hj; simp only [mem_range] at hj; simp only [mem_Icc]; omega
    · intro r hr; simp only [mem_Icc] at hr; omega
    · intro j _; omega
    · intro r hr; rw [show 1+(r-1)=r by have := (mem_Icc.mp hr).1; omega]
  rw [hshift] at hc
  have hb := hP.sum_sub_le_excess (n := 1) le_rfl L
  simp only [Nat.cast_one] at hb
  have hbudget := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg m (α := ℝ))
  rw [jordanEnergy, ← twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
  linarith only [hlow, hc, hbudget]

#print axioms centered_floor
#print axioms jordan_defect
#print axioms jordan_ceiling
#print axioms jordan_ceiling_eq_iff
#print axioms saturation_iff_peak_dvd_letters
#print axioms window_energy_le_excess
end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
