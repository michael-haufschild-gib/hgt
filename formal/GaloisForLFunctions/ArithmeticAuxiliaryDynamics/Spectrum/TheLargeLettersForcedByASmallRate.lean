import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.Spectrum.TheSquareRootFloorOfEveryIntegerAlphabet

/-!
# Large letters forced by a small producer rate

At width H the sinc sampler annihilates every centered sawtooth of
period at most H. The loss from the remaining letters is bounded by their
total coefficient mass. Combined with uncertainty at a zeta zero this
forces mass of order m/ε beyond letters of size comparable to ε⁻².
Consequently every positive moment of the coefficient mass has a rate cost.
-/

open Finset GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.TransThresholdPairCorrelation
namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum

noncomputable section

/-- Coefficient mass carried strictly above the cutoff. -/
def largeLetterMass (c : ℕ →₀ ℤ) (H : ℕ) :=
  ∑ k ∈ c.support.filter (H < ·), |(c k : ℝ)|

private def saw (c : ℕ →₀ ℤ) (k : ℕ) (z : ℤ) : ℝ :=
  (-(c k : ℝ)/k)*residue k (z : ZMod (IsProducer.period c)).val

private theorem saw_bound {c : ℕ →₀ ℤ} {k : ℕ} (hk : 0 < k) (z : ℤ) :
    |saw c k z| ≤ |(c k : ℝ)| := by
  have hkr : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  rw [saw, abs_mul,abs_div,abs_neg,abs_of_pos hkr]
  exact (mul_le_mul_of_nonneg_left (abs_residue_le hk _) (by positivity)).trans_eq
    (div_mul_cancel₀ _ hkr.ne')

private theorem short_saw_mean {c : ℕ →₀ ℤ} {m B H k : ℕ} (hP : IsProducer c m B)
    (hk : k ∈ c.support) (hshort : k ≤ H) (s : ℤ) :
    HasSum (fun z : ℤ => gridSincWeight H (z-s)*saw c k z) 0 := by
  let L := IsProducer.period c
  letI : NeZero L := ⟨hP.period_pos.ne'⟩
  letI : NeZero k := ⟨fun he => Finsupp.mem_support_iff.mp hk (he ▸ hP.zero)⟩
  have h := hasSum_gridSinc_periodic_mean hshort (fun j : ZMod k => residue k j.val) s
  rw [residue_class_mean,zero_div] at h
  have h' := h.mul_left (-(c k : ℝ)/k)
  rw [mul_zero] at h'
  apply h'.congr_fun
  intro z
  have Hcast := congrArg (ZMod.castHom (IsProducer.dvd_period k hk) (ZMod k))
    (ZMod.natCast_zmod_val (z : ZMod L))
  have hh : (((z : ZMod L).val : ℕ) : ZMod k) = (z : ZMod k) := by
    simpa only [map_natCast,map_intCast] using Hcast
  have he : (z : ZMod L).val % k = (z : ZMod k).val := by
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hh
  change gridSincWeight H (z-s)*((-(c k : ℝ)/k)*residue k (z : ZMod L).val) = _
  simp only [residue,he,Nat.mod_eq_of_lt (ZMod.val_lt _)]
  ring

/-- Each omitted letter costs at most its coefficient mass in reconstructing
the mean, uniformly in the center of the sampling window. -/
theorem short_sinc_height_error {c : ℕ →₀ ℤ} {m B H : ℕ} (hP : IsProducer c m B)
    (hH : 0 < H) (s : ℤ) :
    |(∑' z : ℤ, gridSincWeight H (z-s)*periodicFloorHeight c z)-(peak c : ℝ)/2| ≤ largeLetterMass c H := by
  let W (z : ℤ) := gridSincWeight H (z-s)
  have hW : HasSum W 1 := (Equiv.subRight s).hasSum_iff.mpr
    ((summable_gridSincWeight hH).hasSum_iff.mpr (tsum_gridSincWeight hH))
  let S := c.support.filter (· ≤ H)
  let R := c.support.filter (H < ·)
  let T := largeLetterMass c H
  have hpart (z : ℤ) : periodicFloorHeight c z =
      (peak c : ℝ)/2 + ∑ k ∈ S, saw c k z + ∑ k ∈ R, saw c k z := by
    rw [periodicFloorHeight,stepWeight_eq_mean_add hP.zero hP.balanced,add_assoc]
    congr 1
    exact (by simpa only [S,R,not_le,saw] using
      (sum_filter_add_sum_filter_not c.support (· ≤ H) (fun k => saw c k z)).symm)
  have htail (z : ℤ) : |∑ k ∈ R, saw c k z| ≤ T := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => saw_bound ?_ z)
    exact Nat.pos_of_ne_zero fun he =>
      Finsupp.mem_support_iff.mp (mem_filter.mp hk).1 (he ▸ hP.zero)
  have hs := (hW.mul_right ((peak c : ℝ)/2)).add
    (hasSum_sum (s := S) fun k hk => short_saw_mean hP (mem_filter.mp hk).1 (mem_filter.mp hk).2 s)
  simp only [one_mul,sum_const_zero,add_zero] at hs
  have hu : Summable (fun z : ℤ => W z*periodicFloorHeight c z) := by
    apply (hW.summable.mul_right (peak c : ℝ)).of_nonneg_of_le
    · intro z
      exact mul_nonneg (gridSincWeight_nonneg _ _)
        (by exact_mod_cast hP.nonneg (z : ZMod (IsProducer.period c)).val)
    · intro z
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hP.stepWeight_le_peak (z : ZMod (IsProducer.period c)).val)
        (gridSincWeight_nonneg _ _)
  have ht := hu.hasSum.sub hs
  have hdom (z : ℤ) : |W z*periodicFloorHeight c z -
      (W z*((peak c : ℝ)/2)+∑ k ∈ S, W z*saw c k z)| ≤ W z*T := by
    rw [hpart,←mul_sum,←mul_add,mul_add,add_sub_cancel_left,abs_mul,abs_of_nonneg (gridSincWeight_nonneg _ _)]
    exact mul_le_mul_of_nonneg_left (htail z) (gridSincWeight_nonneg _ _)
  have hmajor := hW.mul_right T
  rw [one_mul] at hmajor
  have hh := hasSum_le (fun z => (le_abs_self _).trans (hdom z)) ht hmajor
  have hl := hasSum_le (fun z => (neg_le_abs _).trans (hdom z)) ht.neg hmajor
  exact abs_le.mpr ⟨neg_le.mp hl,hh⟩

/-- A two-scale peak bound. No bound on the largest letter is needed. -/
theorem peak_le_short_sinc_and_large_letters {c : ℕ →₀ ℤ} {m B H : ℕ}
    (hP : IsProducer c m B) (hH : 0 < H) :
    (peak c : ℝ) ≤ 4*m+272*H*excess c m B+4*largeLetterMass c H := by
  have hu := sinc_floor_height_budget hP hH
  have hl := (abs_le.mp (short_sinc_height_error hP hH (4*H))).1
  linarith only [hu,hl]

/-- Every sufficiently accurate producer has coefficient mass of order m/ε
on letters larger than a constant times ε⁻². -/
theorem exists_mass_beyond_inverse_square :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B →
      ∀ H : ℕ, 0 < H → rate c m B ≤ η → (H : ℝ)*(rate c m B)^2 ≤ η →
        η*m ≤ rate c m B*largeLetterMass c H := by
  obtain ⟨δ,hδ,hδ₁,hlaw⟩ := exists_uncertainty_constant
  refine ⟨δ/300,by positivity,by linarith only [hδ₁],fun c m B hP H hH he hscale => ?_⟩
  have h := hlaw c m B hP (by linarith only [he,hδ₁])
  rw [IsProducer.peakRatio,←mul_div_assoc,le_div_iff₀ hP.m_pos] at h
  have hpeak := peak_le_short_sinc_and_large_letters hP hH
  have hT := mul_le_mul_of_nonneg_left hP.excess_le (by positivity : 0 ≤ 272*(H:ℝ))
  have hbound : (peak c : ℝ) ≤ 4*m+272*H*((m:ℝ)*rate c m B)+4*largeLetterMass c H := by
    linarith only [hpeak,hT]
  have h₁ := mul_le_mul_of_nonneg_left hbound hP.rate_pos.le
  have h₂ := mul_le_mul_of_nonneg_right he hP.m_pos.le
  have h₃ := mul_le_mul_of_nonneg_right hscale hP.m_pos.le
  linarith only [h,h₁,h₂,h₃,mul_nonneg hδ.le hP.m_pos.le]

/-- Every nonnegative real moment of the coefficient mass pays the full power of
the forced letter scale. At moment s the cost grows as m ε^(-(2s+1)). -/
theorem exists_letter_moment_rate_cost :
    ∃ η : ℝ, 0 < η ∧ ∀ (c : ℕ →₀ ℤ) (m B : ℕ), IsProducer c m B → rate c m B ≤ η →
      ∀ s : ℝ, 0 ≤ s → (η/(rate c m B)^2)^s*(η*m) ≤
        rate c m B*(∑ k ∈ c.support, (k:ℝ)^s*|(c k : ℝ)|) := by
  obtain ⟨η,hη,hη₁,H⟩ := exists_mass_beyond_inverse_square
  refine ⟨η,hη,fun c m B hP he s hs => ?_⟩
  let e := rate c m B
  let t := η/e^2
  have he₀ : 0 < e := hP.rate_pos
  have hsq : e^2 ≤ η := by
    have he₁ : e ≤ 1 := he.trans hη₁
    nlinarith only [he,mul_le_mul_of_nonneg_left he₁ he₀.le]
  have ht : 1 ≤ t := (one_le_div (sq_pos_of_pos he₀)).mpr hsq
  have hf : 0 < ⌊t⌋₊ := Nat.floor_pos.mpr ht
  have hcut : (⌊t⌋₊ : ℝ)*e^2 ≤ η := (le_div_iff₀ (sq_pos_of_pos he₀)).mp
    (Nat.floor_le (zero_le_one.trans ht))
  have hm := H c m B hP ⌊t⌋₊ hf he hcut
  have hcost : t^s*largeLetterMass c ⌊t⌋₊ ≤ ∑ k ∈ c.support, (k:ℝ)^s*|(c k : ℝ)| := by
    rw [largeLetterMass,mul_sum]
    apply (sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (zero_le_one.trans ht) ((Nat.lt_of_floor_lt (mem_filter.mp hk).2).le) hs)
      (abs_nonneg _)).trans
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun k _ _ =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _)
  have h := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (zero_le_one.trans ht) s)
  have hh := mul_le_mul_of_nonneg_left hcost he₀.le
  change t^s*(η*m) ≤ e*_
  calc _ ≤ t^s*(e*largeLetterMass c ⌊t⌋₊) := h
       _ = e*(t^s*largeLetterMass c ⌊t⌋₊) := by ring
       _ ≤ _ := hh

#print axioms short_sinc_height_error
#print axioms exists_mass_beyond_inverse_square
#print axioms exists_letter_moment_rate_cost

end

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics.FloorSpectrum
