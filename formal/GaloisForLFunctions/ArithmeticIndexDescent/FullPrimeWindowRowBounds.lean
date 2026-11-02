import GaloisForLFunctions.ArithmeticIndexDescent.FullPrimeWindowHaarDecay

/-!
# Summable normalized rows of the literal prime–pole source

The trace support bound and both balanced pole moments give an a^(-3/2)
row estimate. Its square divided by the Haar mass has a telescoping tail.
-/

noncomputable section
open MeasureTheory Finset Filter Topology Set
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
namespace GaloisForLFunctions.ArithmeticIndexDescent

lemma coarseProfile_exp_neg_abs_le_two {b : ℕ} (hb : 1 ≤ b) :
    |∫ u, coarseProfile b u * Real.exp (-u/2)| ≤ 2 := by
  simp_rw [coarseProfile,add_mul]
  rw [integral_add (integrable_rawCell_mul_exp _) (integrable_rawCell_mul_exp _)]
  change |cellExpMass (2*b)+cellExpMass (2*b+1)| ≤ 2
  rw [cellExpMass_eq (by omega),cellExpMass_eq (by omega),
    show 2*b+1+1=2*b+2 by omega]
  have hlo : 0 ≤ Real.log (((2*b:ℕ):ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤2*b by omega))
  have horder : Real.log (((2*b:ℕ):ℝ)) ≤ Real.log (((2*b+2:ℕ):ℝ)) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (show 2*b≤2*b+2 by omega))
  have he1 : Real.exp (-Real.log (((2*b:ℕ):ℝ))/2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith only [hlo])
  have he2 : Real.exp (-Real.log (((2*b+2:ℕ):ℝ))/2) ≤
      Real.exp (-Real.log (((2*b:ℕ):ℝ))/2) :=
    Real.exp_le_exp.mpr (by linarith only [horder])
  rw [abs_of_nonneg (by linarith only [he2])]
  have he0 := (Real.exp_pos (-Real.log (((2*b+2:ℕ):ℝ))/2)).le
  linarith only [he1,he0]

/-- Both exact poles preserve the summable row scale of the full prime trace. -/
theorem abs_fullPrimeWindowRemainder_le_haar_mass {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |fullPrimeWindowRemainder Y a b| ≤
      ((4*RHTower.FreeLagTrace.chebyshevConst+8)*Real.sqrt ((2:ℝ)*b+2)) *
        (2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ)) := by
  let H := 2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ)
  let S := Real.sqrt ((2:ℝ)*b+2)
  have hH : 0 ≤ H := div_nonneg (mul_nonneg (by norm_num) (haarMass_pos ha).le)
    (Real.sqrt_nonneg _)
  have hS : 1 ≤ S := by
    rw [Real.le_sqrt zero_le_one (by positivity)]
    norm_num only [one_pow]
    have hb0 := Nat.cast_nonneg (α := ℝ) b
    linarith only [hb0]
  have hY1 : (1:ℝ) ≤ Y := by exact_mod_cast hY
  have hY0 : (0:ℝ) < Y := zero_lt_one.trans_le hY1
  have hp := abs_haarProfile_exp_pos_le ha
  have hm := abs_haarProfile_exp_neg_le ha
  have hc := coarseProfile_exp_neg_abs_le_two hb
  have hk : |4*(S-Real.sqrt ((2:ℝ)*b))| ≤ 4*S := by
    have hs : Real.sqrt ((2:ℝ)*b) ≤ S := Real.sqrt_le_sqrt (by linarith)
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hs))]
    have hnn := Real.sqrt_nonneg ((2:ℝ)*b)
    linarith only [hnn]
  have hsecond : |(2*(∫ u,haarProfile a u*Real.exp (u/2))*
      (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ)| ≤ 4*H := by
    rw [abs_div,abs_of_pos hY0,div_le_iff₀ hY0,abs_mul,abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    have ht := mul_le_mul (mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤2 by norm_num)) hc
      (abs_nonneg _) (mul_nonneg (show (0:ℝ)≤2 by norm_num) hH)
    have hy := mul_le_mul_of_nonneg_left hY1 (show 0≤4*H by positivity)
    dsimp only [H] at ht hy ⊢
    nlinarith only [ht,hy]
  have heq : fullPrimeWindowRemainder Y a b =
      fullPrimeWindowCoupling (haarProfile a) Y b/Real.sqrt Y -
      (4*(S-Real.sqrt ((2:ℝ)*b)))*(∫ u,haarProfile a u*Real.exp (-u/2)) -
      (2*(∫ u,haarProfile a u*Real.exp (u/2))*
        (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ) := by
    rw [fullPrimeWindowRemainder,
      ← fullPrimeWindowCoupling_eq_tsum_euler (X := a+(b+1)*Y)
        hY ha hb (by omega) (by nlinarith only [Nat.zero_le a]),
      sub_div,fullPrimeWindowMixedPole_div_sqrt hY hb]
    dsimp only [S]
    ring
  rw [heq]
  calc
    _ ≤ |fullPrimeWindowCoupling (haarProfile a) Y b/Real.sqrt Y| +
        |(4*(S-Real.sqrt ((2:ℝ)*b)))*(∫ u,haarProfile a u*Real.exp (-u/2))| +
        |(2*(∫ u,haarProfile a u*Real.exp (u/2))*
          (∫ u,coarseProfile b u*Real.exp (-u/2)))/(Y:ℝ)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (4*RHTower.FreeLagTrace.chebyshevConst*S)*H+(4*S)*H+4*H := by
      apply add_le_add (add_le_add (abs_fullPrimeWindowCoupling_div_sqrt_le hY ha hb) ?_) hsecond
      rw [abs_mul]
      exact mul_le_mul hk hm (abs_nonneg _) (by positivity)
    _ ≤ _ := by
      change _ ≤ ((4*RHTower.FreeLagTrace.chebyshevConst+8)*S)*H
      nlinarith only [mul_nonneg hH (sub_nonneg.mpr hS)]

lemma haar_root_mass_sq_le_pronic {a : ℕ} (ha : 1 ≤ a) :
    (2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ))^2 ≤
      haarMass a/((a:ℝ)*((a:ℝ)+1)) := by
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0:ℝ) < a := zero_lt_one.trans_le ha1
  have hm := (haarMass_pos ha).le
  have he : (2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ))^2 = 2*haarMass a^2/(a:ℝ) := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
    push_cast
    field_simp [ha0.ne']
  have hb : 2*haarMass a ≤ 1/((a:ℝ)+1) := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ)<4*(a:ℝ)+1)).mp (haarMass_bounds ha).2
    rw [le_div_iff₀ (by positivity : (0:ℝ)<(a:ℝ)+1)]
    nlinarith only [h,mul_nonneg hm (show 0≤2*(a:ℝ)-1 by linarith only [ha1])]
  rw [he]
  calc
    _ = (haarMass a/(a:ℝ))*(2*haarMass a) := by ring
    _ ≤ (haarMass a/(a:ℝ))*(1/((a:ℝ)+1)) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hm ha0.le)
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev];ring

/-- The normalized squared rows have a telescoping arithmetic majorant. -/
theorem exists_fullPrimeWindowRemainder_square_row_bound :
    ∃ C : ℝ, 0<C ∧ ∀ Y a b : ℕ, 1≤Y → 1≤a → 1≤b →
      (fullPrimeWindowRemainder Y a b)^2 ≤
        C*((b:ℝ)+1)*(haarMass a/((a:ℝ)*((a:ℝ)+1))) := by
  let L := 4*RHTower.FreeLagTrace.chebyshevConst+8
  have hL : 0<L := by
    have h := RHTower.FreeLagTrace.chebyshevConst_pos
    dsimp only [L]
    linarith only [h]
  refine ⟨2*L^2,by positivity,?_⟩
  intro Y a b hY ha hb
  have h := abs_fullPrimeWindowRemainder_le_haar_mass hY ha hb
  have hs : (fullPrimeWindowRemainder Y a b)^2 ≤
      ((L*Real.sqrt ((2:ℝ)*b+2))*(2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ)))^2 :=
    sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  calc
    _ ≤ _ := hs
    _ = (L*Real.sqrt ((2:ℝ)*b+2))^2*(2*haarMass a/Real.sqrt ((2*a:ℕ):ℝ))^2 := mul_pow _ _ _
    _ ≤ (L*Real.sqrt ((2:ℝ)*b+2))^2*(haarMass a/((a:ℝ)*((a:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left (haar_root_mass_sq_le_pronic ha) (sq_nonneg _)
    _ = _ := by rw [mul_pow,Real.sq_sqrt (by positivity)];ring

#print axioms coarseProfile_exp_neg_abs_le_two
#print axioms abs_fullPrimeWindowRemainder_le_haar_mass
#print axioms haar_root_mass_sq_le_pronic
#print axioms exists_fullPrimeWindowRemainder_square_row_bound
end GaloisForLFunctions.ArithmeticIndexDescent
