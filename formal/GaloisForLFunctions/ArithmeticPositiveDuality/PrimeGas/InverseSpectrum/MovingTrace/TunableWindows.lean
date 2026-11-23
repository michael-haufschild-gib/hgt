import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.PhysicalTest
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MovingTrace.ShortChord

/-! # Tunable ground and high-occupation witnesses -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

/-- A single attenuated ground mode gives order t/R amplitude at order 1/R trace loss. -/
theorem ground_scale_witness {σ t R : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      (shortChordFactor σ/2)*(t/R) < ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ ∧
      traceLoss (projected P) < 2/R := by
  have ht' := zero_lt_one.trans_le ht
  have hR' := ht'.trans_le hR
  let u : Ioc (0:ℝ) 1 := ⟨Real.exp (-(shortStep/R)),Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_pos shortStep_pos hR').le)⟩
  apply physical_ground_chord 0 (z := ⟨σ,t⟩) hσ u
  · exact (mul_lt_mul_of_pos_right (half_lt_self (shortChordFactor_pos σ)) (div_pos ht' hR')).trans_le
      (short_chord_lower hσ.le ht'.le (ht.trans hR) hR)
  · have h := short_retention_loss (R := R)
    change 1-u.val ≤ shortStep/R at h
    have hs : shortStep < 1 := (min_le_left _ _).trans_lt (by norm_num : (1/4:ℝ)<1)
    have hsmall := div_lt_div_of_pos_right hs hR'
    nlinarith only [h,hsmall,sq_nonneg (1-u.val),show 2/R=2*(1/R) by ring]

private theorem retention_in_gap (N j : ℕ) (hN : 0 < N) (hj : j < N) :
    occupationWeight (N+j)*Real.exp (-(shortStep/(N:ℝ))) ∈ Icc (occupationWeight (N+j+1)) (occupationWeight (N+j)) := by
  have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have he : occupationWeight (N+j)*(1-occupationWeight (N+j+1)) = occupationWeight (N+j+1) := by
    simp only [occupationWeight_eq,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  have hsmall : shortStep/(N:ℝ) ≤ occupationWeight (2*N) := by
    rw [occupationWeight_eq,← one_div,Nat.cast_mul,Nat.cast_ofNat]
    apply (div_le_div_iff₀ hNp (show 0 < 2*(N:ℝ)+1 by positivity)).mpr
    have hb := mul_le_mul_of_nonneg_right (show shortStep ≤ 1/4 from min_le_left _ _) (show 0 ≤ 2*(N:ℝ)+1 by positivity)
    linarith only [hb,h1]
  have hcost := ((short_retention_loss (R := (N:ℝ))).trans hsmall).trans
    (occupationWeight_antitone (show N+j+1 ≤ 2*N by omega))
  have hr : 1-occupationWeight (N+j+1) ≤ Real.exp (-(shortStep/(N:ℝ))) := by linarith only [hcost]
  exact ⟨he.symm.trans_le (mul_le_mul_of_nonneg_left hr (occupationWeight_pos _).le),
    mul_le_of_le_one_right (occupationWeight_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_pos shortStep_pos hNp).le))⟩

/-- A block at level N pays a quadratic cost even when the clock rotates by only order t/N per level. -/
private theorem short_block_witness {σ t : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (N : ℕ) (hN : t ≤ (N:ℝ)) :
    ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      (shortChordFactor σ/8)*t*occupationWeight (2*N)^σ < ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ ∧
      traceLoss (projected P) < 2*occupationWeight N^2 := by
  let z : ℂ := ⟨σ,t⟩
  let u := Real.exp (-(shortStep/(N:ℝ)))
  let A := occupationWeight (2*N)^σ*(shortChordFactor σ*(t/(N:ℝ)))
  have ht' := zero_lt_one.trans_le ht
  have hNp := ht'.trans_le hN
  have hNat : 0 < N := Nat.cast_pos.mp hNp
  have hA : 0 < A := mul_pos (Real.rpow_pos_of_pos (occupationWeight_pos _) _) (mul_pos (shortChordFactor_pos σ) (div_pos ht' hNp))
  have hv (j : ℕ) (hj : j ∈ range N) : A ≤ ‖(occupationWeight (N+j):ℂ)^z-((occupationWeight (N+j)*u:ℝ):ℂ)^z‖ := by
    rw [norm_scaled_occupation_chord z (occupationWeight_pos _) (Real.exp_pos _)]
    have hj' := mem_range.mp hj
    exact mul_le_mul (Real.rpow_le_rpow (occupationWeight_pos _).le
      (occupationWeight_antitone (show N+j ≤ 2*N by omega)) hσ.le)
      (short_chord_lower hσ.le ht'.le (ht.trans hN) hN) (mul_pos (shortChordFactor_pos σ) (div_pos ht' hNp)).le
      (Real.rpow_nonneg (occupationWeight_pos _).le _)
  obtain ⟨P,dim,hc,hL,hD⟩ := physical_coherent_block (z := z) hσ N hNat (fun k => occupationWeight k*u) hA
    (fun j hj => retention_in_gap N j hNat (mem_range.mp hj)) hv
  have he : (N:ℝ)*A/8 = (shortChordFactor σ/8)*t*occupationWeight (2*N)^σ := by
    dsimp only [A]
    field_simp [hNp.ne']
  exact ⟨P,dim,hc,he ▸ hL,hD⟩

def highWindowFactor (σ : ℝ) : ℝ := (shortChordFactor σ/8)*(1/5:ℝ)^σ

theorem highWindowFactor_pos (σ : ℝ) : 0 < highWindowFactor σ :=
  mul_pos (div_pos (shortChordFactor_pos σ) (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)

/-- At any real occupation scale R at least t, one conserving omission gives amplitude at least a constant times t/R^σ at cost below 2/R². -/
theorem high_scale_witness {σ t R : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    ∃ (P : Projection) (dim : MissingDimension P 1) (hc : Conserving (projected P)),
      highWindowFactor σ*(t/R^σ) < ‖relativePartition (physicalSpectrum P dim hc) (⟨σ,t⟩:ℂ)‖ ∧
      traceLoss (projected P) < 2/R^2 := by
  let N := ⌈R⌉₊
  have h1 := ht.trans hR
  have hRp := zero_lt_one.trans_le h1
  have hN : R ≤ (N:ℝ) := Nat.le_ceil _
  have hNu : (N:ℝ) < R+1 := Nat.ceil_lt_add_one hRp.le
  obtain ⟨P,dim,hc,hL,hD⟩ := short_block_witness hσ ht N (hR.trans hN)
  have ha : (1/5:ℝ)*(1/R) ≤ occupationWeight (2*N) := by
    rw [occupationWeight_eq,← one_div,Nat.cast_mul,Nat.cast_ofNat,show (1/5:ℝ)*(1/R)=1/(5*R) by ring]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hRp) (show 0<2*(N:ℝ)+1 by positivity)).mpr
    linarith only [hNu,h1]
  have hb : occupationWeight N ≤ 1/R := by
    rw [occupationWeight_eq,← one_div]
    exact one_div_le_one_div_of_le hRp (hN.trans (le_add_of_nonneg_right zero_le_one))
  have hp := Real.rpow_le_rpow (mul_nonneg (by norm_num : (0:ℝ)≤1/5) (one_div_pos.mpr hRp).le) ha hσ.le
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/5) (one_div_pos.mpr hRp).le,one_div R,Real.inv_rpow hRp.le] at hp
  have hAmp := mul_le_mul_of_nonneg_left hp (mul_pos (div_pos (shortChordFactor_pos σ) (by norm_num : (0:ℝ)<8)) (zero_lt_one.trans_le ht)).le
  have hLoss := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (occupationWeight_pos _).le hb 2) (by norm_num : (0:ℝ)≤2)
  refine ⟨P,dim,hc,?_,hD.trans_le (hLoss.trans_eq (by rw [div_pow,one_pow]; ring))⟩
  exact (show highWindowFactor σ*(t/R^σ) = (shortChordFactor σ/8*t)*((1/5:ℝ)^σ*(R^σ)⁻¹) by unfold highWindowFactor; ring).trans_lt (hAmp.trans_lt hL)

#print axioms ground_scale_witness
#print axioms high_scale_witness

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
