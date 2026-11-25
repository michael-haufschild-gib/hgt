import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.EventWeights
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.TotalEnergy

/-! # Distance of an ordered spectrum from either endpoint of its energy band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Filter Topology Set MeasureTheory _root_.RHTower
open GaloisForLFunctions.HTGeometry

/-- Each sorted coordinate still belongs to the original half-open prime band. -/
theorem spectrum_mem {c d : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) (i : Fin k) :
    spectrum h R i ∈ Ioc c d := by
  letI : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective
  let v (j : Fin k) := location h ((R.val.orderIsoOfFin R.property j).val).val
  let p := (R.val.orderIsoOfFin R.property (Tuple.sort v i)).val
  exact (mem_added c d h p.val).mp p.property

theorem sum_spectrum {S : Finset Nat.Primes} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥S) :
    ∑ i, spectrum h R i = h.val*energyOf R := by
  have H := total_spectrum h R
  change (∑ i, spectrum h R i) = _ at H
  rwa [packetEnergy,energyOf_eq] at H

private theorem dist_le_sum {k : ℕ} (v : Fin k → ℝ) (z : ℝ) :
    dist v (fun _ => z) ≤ ∑ i, |v i-z| := by
  apply (dist_pi_le_iff (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr
  intro i
  rw [Real.dist_eq]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (v j-z)) (Finset.mem_univ i)

/-- Every coordinate's distance from the lower endpoint is paid for in total excess energy. -/
theorem lower_distance {c d : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) :
    dist (spectrum h R) (fun _ => c) ≤ h.val*energyOf R-k*c := by
  calc _ ≤ ∑ i, |spectrum h R i-c| := dist_le_sum _ _
       _ = ∑ i, (spectrum h R i-c) := Finset.sum_congr rfl fun i _ =>
         abs_of_nonneg (sub_nonneg.mpr (spectrum_mem h R i).1.le)
       _ = _ := by rw [Finset.sum_sub_distrib,sum_spectrum]; simp [nsmul_eq_mul]

/-- The upper energy deficit bounds the joint distance from the upper endpoint. -/
theorem upper_distance {c d : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) :
    dist (spectrum h R) (fun _ => d) ≤ k*d-h.val*energyOf R := by
  calc _ ≤ ∑ i, |spectrum h R i-d| := dist_le_sum _ _
       _ = ∑ i, (d-spectrum h R i) := Finset.sum_congr rfl fun i _ => by
         rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (spectrum_mem h R i).2)]
       _ = _ := by rw [Finset.sum_sub_distrib,sum_spectrum]; simp [nsmul_eq_mul]

theorem subband {c b e d : ℝ} (hcb : c ≤ b) (hed : e ≤ d) (h : Ioi (0:ℝ)) : added b e h ⊆ added c d h := by
  intro p hp
  have hm := (mem_added b e h p).mp hp
  exact (mem_added c d h p).mpr ⟨hcb.trans_lt hm.1,hm.2.trans hed⟩

/-- Critical coefficients stay positive even when conditioning later becomes a rare event. -/
theorem critical_limit_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) (k : ℕ) :
    0 < Real.log (d/c)^k/k.factorial :=
  div_pos (pow_pos (Real.log_pos ((one_lt_div hc).mpr hcd)) k) (Nat.cast_pos.mpr (Nat.factorial_pos k))

theorem inner_width {c d ε : ℝ} (hcd : c < d) (hε : 0 < ε) {k : ℕ} (hk : 0 < k) :
    ∃ w : ℝ, 0 < w ∧ w < d-c ∧ k*w < ε := by
  have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  obtain ⟨w,hw,hW⟩ := exists_between (lt_min (sub_pos.mpr hcd) (div_pos hε hk'))
  refine ⟨w,hw,hW.trans_le (min_le_left _ _),?_⟩
  rw [mul_comm]
  exact (lt_div_iff₀ hk').mp (hW.trans_le (min_le_right _ _))

/-- Moving the inverse temperature up by u h penalizes each occupied energy by exp(−u v). -/
theorem cooling_bounds (c d : ℝ) (h : Ioi (0:ℝ)) {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    Real.exp (u*(-(k*d)))*coefficient (added c d h) 1 k ≤ coefficient (added c d h) (1+u*h.val) k ∧
    coefficient (added c d h) (1+u*h.val) k ≤ Real.exp (u*(-(k*c)))*coefficient (added c d h) 1 k := by
  have he (v : ℝ) : -u*h.val*(k*v/h.val) = u*(-(k*v)) := by field_simp [(show 0 < h.val from h.property).ne']
  have H := coefficient_tilt_neg c d h (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) h.property.le) k
  rwa [show 1-(-u*h.val) = 1+u*h.val by ring,he,he] at H

/-- Moving the inverse temperature down by u h favors larger energies. -/
theorem heating_bounds (c d : ℝ) (h : Ioi (0:ℝ)) {u : ℝ} (hu : 0 ≤ u) (k : ℕ) :
    Real.exp (u*(k*c))*coefficient (added c d h) 1 k ≤ coefficient (added c d h) (1-u*h.val) k ∧
    coefficient (added c d h) (1-u*h.val) k ≤ Real.exp (u*(k*d))*coefficient (added c d h) 1 k := by
  have he (v : ℝ) : u*h.val*(k*v/h.val) = u*(k*v) := by field_simp [(show 0 < h.val from h.property).ne']
  have H := coefficient_tilt_pos c d h (mul_nonneg hu h.property.le) k
  rwa [he,he] at H

#print axioms spectrum_mem
#print axioms lower_distance
#print axioms upper_distance

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
