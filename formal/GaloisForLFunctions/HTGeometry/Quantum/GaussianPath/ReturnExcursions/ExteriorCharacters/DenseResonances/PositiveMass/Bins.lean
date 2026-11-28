import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.PhaseMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.AbsoluteWindow

/-! # Positive real mass on inverse-width macroscopic detunings -/

open Finset Complex
open scoped ComplexConjugate symmDiff
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Positive real part restricted to inverse-width detunings with large
support. The complex amplitudes already include the midpoint phases. -/
def positiveWindow (F : Finset (Finset I)) (a : Finset I → ℂ) (x : Finset I → ℝ)
    (r : ℕ) (w : ℝ) : ℝ :=
  ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card ∧ |w*(x S-x T)|≤1),
    max 0 ((a S*conj (a T)).re*Real.sinc (w*(x S-x T)/2))

/-- A short detuning preserves at least half the positive real part. -/
private theorem positive_sinc {d : ℝ} (hd : |d|≤1) (v : ℝ) :
    max 0 v ≤ 2*max 0 (v*Real.sinc (d/2)) := by
  have hs : 1/2≤Real.sinc (d/2) := sinc_half (by
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right hd (by norm_num))
  rcases le_total 0 v with h|h
  · rw [max_eq_right h]
    nlinarith only [mul_le_mul_of_nonneg_left hs h,le_max_right 0 (v*Real.sinc (d/2))]
  · rw [max_eq_left h]
    positivity

/-- The bin price applies to arbitrary complex starting amplitudes. It
keeps both the real sign and the inverse-width cutoff. -/
theorem positive_bin_bound (F : Finset (Finset I)) (a : Finset I → ℂ) (x : Finset I → ℝ)
    (r : ℕ) (lo hi w : ℝ) (hw : 0≤w) (hx : ∀ S∈F, x S∈Set.Icc lo hi)
    (ha : ∀ S∈F, ‖a S‖≤1) :
    (∑ S ∈ F, ‖a S‖)^2 ≤ ((⌊w*(hi-lo)⌋₊+1:ℕ):ℝ)*4*
      (F.card*(2^r*(3/2)^Fintype.card I)+2*positiveWindow F a x r w) := by
  classical
  obtain ⟨j,hj⟩ := frequency_bins F x lo hi w hw hx
  let U (b) := F.filter fun S => j S=b
  let M (S T : Finset I) := max 0 (a S*conj (a T)).re
  let V (S : Finset I) := F.filter fun T => r<(S ∆ T).card ∧ |w*(x S-x T)|≤1
  let k (S T : Finset I) := max 0 ((a S*conj (a T)).re*Real.sinc (w*(x S-x T)/2))
  let A : ℝ := 2^r*(3/2)^Fintype.card I
  have hrow (b) (S) (hS : S∈U b) :
      (∑ T ∈ U b, M S T)≤A+2*∑ T ∈ V S, k S T := by
    let near := (U b).filter fun T => (S ∆ T).card≤r
    let far := (U b).filter fun T => r<(S ∆ T).card
    have hsF := (mem_filter.mp hS).1
    have hd (T) (hT : T∈U b) : |w*(x S-x T)|≤1 :=
      hj S hsF T (mem_filter.mp hT).1 ((mem_filter.mp hS).2.trans (mem_filter.mp hT).2.symm)
    have hn : (∑ T ∈ near, M S T)≤A := by
      apply le_trans _ (small_support_count (U b) S r)
      calc
        _ ≤ ∑ _T ∈ near, (1:ℝ) := by
          apply sum_le_sum
          intro T hT
          apply max_le zero_le_one
          apply (Complex.re_le_norm _).trans
          rw [norm_mul,Complex.norm_conj]
          exact mul_le_one₀ (ha S hsF) (norm_nonneg _) (ha T (mem_filter.mp (mem_filter.mp hT).1).1)
        _ = (near.card:ℝ) := by simp
    have hsub : far⊆V S := by
      intro T hT
      obtain ⟨hT,hr⟩ := mem_filter.mp hT
      exact mem_filter.mpr ⟨(mem_filter.mp hT).1,hr,hd T hT⟩
    have hf : (∑ T ∈ far, M S T)≤2*∑ T ∈ V S, k S T := by
      rw [mul_sum]
      calc
        _ ≤ ∑ T ∈ far, 2*k S T := sum_le_sum fun T hT => positive_sinc (hd T (mem_filter.mp hT).1) _
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ => mul_nonneg (by norm_num) (le_max_left ..))
    have ht := sum_filter_add_sum_filter_not (U b) (fun T => (S ∆ T).card≤r) (M S)
    simp only [not_le] at ht
    exact ht ▸ add_le_add hn hf
  let R (b) := ∑ S ∈ U b, ‖a S‖
  have hfib (b) : (R b)^2 ≤ 4*∑ S ∈ U b, (A+2*∑ T ∈ V S, k S T) := by
    exact (positive_amplitude_mass (U b) a).trans (mul_le_mul_of_nonneg_left (sum_le_sum (hrow b)) (by norm_num))
  have hmap : (F : Set (Finset I)).MapsTo j (univ : Finset (Fin (⌊w*(hi-lo)⌋₊+1))) :=
    fun _ _ => mem_univ _
  have hR : (∑ b, R b)=∑ S ∈ F, ‖a S‖ := sum_fiberwise_of_maps_to hmap _
  have hc := sq_sum_le_card_mul_sum_sq (s:=univ) (f:=R)
  rw [hR,card_univ,Fintype.card_fin] at hc
  have ht := sum_le_sum (fun b (_ : b∈(univ:Finset _)) => hfib b)
  dsimp only [U] at ht
  rw [←mul_sum,sum_fiberwise_of_maps_to hmap,sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at ht
  rw [mul_assoc]
  exact hc.trans (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _))

#print axioms positive_bin_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
