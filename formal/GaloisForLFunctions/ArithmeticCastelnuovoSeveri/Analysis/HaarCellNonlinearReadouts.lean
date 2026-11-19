import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellProfiles

/-!
# Nonlinear readouts of logarithmic Haar details

Gaussian moment matching retains the squared detail. Higher-order readout,
as in the cubic polarization of Kumar–Senapati–Vashisth, retains its sign.
The left logarithmic half-cell is longer than the right one. Consequently
the centered third moment has a nonzero signed coefficient on every pair.
-/

noncomputable section
open MeasureTheory Set
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

/-- Integrated response above the zero-detail baseline on a single open pair. -/
def detailReadout (f : ℝ → ℝ) (d : ℕ → ℝ) (X a : ℕ) : ℝ :=
  ∫ x in Ioo (Real.log ((2*a : ℕ) : ℝ)) (Real.log ((2*a+2 : ℕ) : ℝ)),
    f (haarSectionProfile d X x) - f 0

private theorem test_two_cells (f : ℝ → ℝ) (b : ℝ) (a : ℕ) (x : ℝ) :
    f (b*haarProfile a x) - f 0 =
      (f (b*haarLeftCoeff a)-f 0)*rawCell (2*a) x +
      (f (-(b*haarRightCoeff a))-f 0)*rawCell (2*a+1) x := by
  unfold haarProfile rawCell
  simp only [indicator_apply]
  split_ifs with hl hr hr
  · exact False.elim (hl.2.not_ge hr.1)
  all_goals simp

private theorem readout_on_pair (f : ℝ → ℝ) (d : ℕ → ℝ) {X a : ℕ} (ha : 1 ≤ a) (hX : a ≤ X) :
    detailReadout f d X a =
      (f (d a*haarLeftCoeff a)-f 0)*logCellWidth (2*a) +
      (f (-(d a*haarRightCoeff a))-f 0)*logCellWidth (2*a+1) := by
  let l := Real.log ((2*a : ℕ) : ℝ)
  let u := Real.log ((2*a+2 : ℕ) : ℝ)
  have he : (Ioo l u).indicator (fun x => f (haarSectionProfile d X x)-f 0) =ᵐ[volume]
      fun x => f (d a*haarProfile a x)-f 0 := by
    filter_upwards [Measure.ae_ne volume l] with x hne
    by_cases hx : x ∈ Ioo l u
    · rw [indicator_of_mem hx,haarSectionProfile_on_pair d ha hX hx]
    · rw [indicator_of_notMem hx, haarProfile_zero_outside_pair ha (fun hi =>
        hx ⟨lt_of_le_of_ne hi.1 hne.symm,hi.2⟩),mul_zero,sub_self]
  unfold detailReadout
  rw [← integral_indicator measurableSet_Ioo, integral_congr_ae he]
  simp_rw [test_two_cells]
  rw [integral_add ((integrable_rawCell _).const_mul _) ((integrable_rawCell _).const_mul _),
    integral_const_mul,integral_const_mul,integral_rawCell (a := 2*a) (by omega),
    integral_rawCell (a := 2*a+1) (by omega)]

/-- Every test function on the physical detail reduces to the two point
values, with the original logarithmic lengths as weights. -/
theorem detailReadout_law (f : ℝ → ℝ) (d : ℕ → ℝ) (i k : ℕ) :
    let a := i+1
    detailReadout f d (a+k) a =
      (f (d a*haarLeftCoeff a)-f 0)*logCellWidth (2*a) +
      (f (-(d a*haarRightCoeff a))-f 0)*logCellWidth (2*a+1) :=
  readout_on_pair f d (by omega) (by omega)

private theorem width_shrinks {n : ℕ} (h : 1 ≤ n) : logCellWidth (n+1) < logCellWidth n := by
  have h0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 0 < (n:ℝ)+1 := by linarith
  have h2 : 0 < (n:ℝ)+1+1 := by linarith
  simp only [logCellWidth,Nat.cast_add,Nat.cast_one]
  rw [← Real.log_div h2.ne' h1.ne',← Real.log_div h1.ne' h0.ne']
  apply Real.log_lt_log (div_pos h2 h1)
  exact (div_lt_div_iff₀ h1 h0).mpr (by nlinarith only [])

/-- The imbalance of the two logarithmic lengths has a fixed strict sign. -/
theorem detail_skew_negative (i : ℕ) :
    haarMass (i+1)*(haarLeftCoeff (i+1)-haarRightCoeff (i+1)) < 0 := by
  let a := i+1
  have ha : 1 ≤ a := by omega
  have hleft := logCellWidth_pos (show 1 ≤ 2*a by omega)
  have hright := logCellWidth_pos (show 1 ≤ 2*a+1 by omega)
  have hdec := width_shrinks (show 1 ≤ 2*a by omega)
  apply mul_neg_of_pos_of_neg (haarMass_pos ha)
  exact sub_neg.mpr ((div_lt_div_iff_of_pos_right (add_pos hleft hright)).mpr hdec)

/-- Centered third moment reads the signed cube of the physical detail. -/
theorem detail_cubic_moment (d : ℕ → ℝ) (i k : ℕ) :
    let a := i+1
    detailReadout (fun t => t^3) d (a+k) a =
      (haarMass a*(haarLeftCoeff a-haarRightCoeff a))*(d a)^3 := by
  let a := i+1
  have hl := (haarCoeff_mass a).1
  have hr := (haarCoeff_mass a).2
  have hs := haarCoeff_sum (show 1 ≤ a by omega)
  change detailReadout _ d (a+k) a = _
  rw [readout_on_pair _ d (show 1 ≤ a by omega) (by omega)]
  calc
    _ = (d a)^3 * (haarLeftCoeff a^2*(haarLeftCoeff a*logCellWidth (2*a)) -
        haarRightCoeff a^2*(haarRightCoeff a*logCellWidth (2*a+1))) := by ring
    _ = _ := by
      rw [hl,hr]
      linear_combination (d a)^3 * haarMass a * (haarLeftCoeff a-haarRightCoeff a) * hs

/-- One cubic reading distinguishes both signs and all magnitudes. -/
theorem cubic_readout_identifies (d e : ℕ → ℝ) (i k : ℕ) :
    let a := i+1
    detailReadout (fun t => t^3) d (a+k) a = detailReadout (fun t => t^3) e (a+k) a ↔ d a = e a := by
  dsimp only
  rw [detail_cubic_moment,detail_cubic_moment,mul_right_inj' (detail_skew_negative i).ne]
  exact (show Odd (3 : ℕ) from ⟨1,rfl⟩).pow_inj

/-- Polarized third-order responses read the product of three independent
detail coefficients even when the remaining cells carry arbitrary values. -/
theorem mixed_cubic_readout (d e f : ℕ → ℝ) (i k : ℕ) :
    let a := i+1
    let T := fun h => detailReadout (fun t => t^3) h (a+k) a
    T (d+e+f)-T (d+e)-T (d+f)-T (e+f)+T d+T e+T f =
      6*haarMass a*(haarLeftCoeff a-haarRightCoeff a)*d a*e a*f a := by
  dsimp only
  simp only [detail_cubic_moment,Pi.add_apply]
  ring

#print axioms detailReadout_law
#print axioms detail_skew_negative
#print axioms detail_cubic_moment
#print axioms cubic_readout_identifies
#print axioms mixed_cubic_readout
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
