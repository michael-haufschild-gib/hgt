import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FourCofactorCapsAtAZetaZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SeventhDifferencesAcrossTheSignedCofactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSignOfTheFirstQuotientCell
import GaloisForLFunctions.BiScaleUncertainty.InteriorOfBoxSplines

/-!
# The last two quotient cells of the signed spline

The first and second positive quotients share their middle sample. Near
half the last spline endpoint the cells have opposite signs, and their
sum stays strictly positive.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticWeightTheory
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private abbrev R : ℝ := 4*Real.exp 8
/-- Left endpoint in the first prime divided by the conductor square. -/
def upperFirstPrimeBandLeft : ℝ := 3*(4*Real.exp 8)/8

/-- Right endpoint in the first prime divided by the conductor square. -/
def upperFirstPrimeBandRight : ℝ := 2*(4*Real.exp 8)/5

private theorem upper_mesh_first_cell {b : ℕ} (hb : 2 ≤ b) {x : ℝ} (hx : 0<x) (hx2 : R<2*x) :
    quotientMeshProfile b x - quotientMeshProfile 1 x = centeredPrimeWeight 1 1*dyadicSpline x := by
  let F (j : ℕ) := (dyadicSpline (j*x)-dyadicSpline ((j+1:ℕ)*x))*centeredPrimeWeight 1 j
  have hz (j : ℕ) (hj : 2≤j) : dyadicSpline (j*x)=0 :=
    dyadicSpline_eq_zero_outside (fun h => (hx2.trans_le
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (2:ℝ)≤j) hx.le)).not_ge h.2)
  have htail : ∑ j ∈ range (b-2), F (2+j)=0 := by
    apply sum_eq_zero
    intro j _
    simp only [F,hz (2+j) (by omega),hz (2+j+1) (by omega),sub_self,zero_mul]
  change (∑ j ∈ range b, F j)-(∑ j ∈ range 1, F j)=_
  calc _ = (∑ j ∈ range 2, F j)-(∑ j ∈ range 1, F j) := by
         conv_lhs => lhs; rw [show b=2+(b-2) by omega,sum_range_add]
         rw [htail,add_zero]
       _ = F 1 := by rw [show 2=1+1 by decide,Finset.sum_range_succ F 1]; ring
       _ = _ := by
         have h2 : dyadicSpline (2*x)=0 := by simpa only [Nat.cast_ofNat] using hz 2 le_rfl
         simp only [F,show (1+1:ℕ)=2 by decide,Nat.cast_one,Nat.cast_ofNat,one_mul,h2,sub_zero]
         ring

/-- Once the third cofactor passes the support, the complete cofactor and
quotient sum reduces to one spline sample, uniformly in both far endpoints. -/
theorem last_first_prime_cofactor {b m : ℕ} (hb : 2≤b) (hm : 2 ≤ m) {h : ℝ}
    (h3 : 4*Real.exp 8 < 3*h) :
    (∑ v ∈ Ioc 0 m, innerJump 1 v*positiveCofactorProfile b h v) =
      (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*dyadicSpline (2*h) := by
  change R<3*h at h3
  have hR : 0<R := by positivity
  have hh : 0<h := by linarith only [hR,h3]
  have h4 : R < 2*(2*h) := by linarith only [h3,hh]
  rw [sum_eq_single_of_mem 2 (mem_Ioc.mpr ⟨by decide,hm⟩) (by
    intro v hv hv2
    by_cases hv1 : v=1
    · subst v; rw [innerJump_small le_rfl,zero_mul]
    have hv3 : 3≤v := by have := (mem_Ioc.mp hv).1; omega
    have hbig := h3.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hv3 : (3:ℝ)≤v) hh.le)
    rw [positiveCofactorProfile,quotient_mesh_after_support b hbig,quotient_mesh_after_support 1 hbig,
      sub_self,mul_zero])]
  have hg : innerJump 1 2=1-cofactorDyadicCoefficient := by simpa using (innerJump_dyadic_pair 0).2
  rw [hg,positiveCofactorProfile]
  norm_num only [Nat.cast_ofNat]
  rw [upper_mesh_first_cell hb (mul_pos two_pos hh) h4]
  ring

private theorem spline_negative_on_last_dilate {x : ℝ} (hl : Real.exp 8 < x) (hu : x<R) :
    dyadicSpline x<0 := by
  have hx := (Real.exp_pos 8).trans hl
  have hlog := Real.log_lt_log (Real.exp_pos _) hl
  rw [Real.log_exp] at hlog
  have h4 : Real.exp (8+Real.log 4)=R := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]; dsimp only [R]; ring
  have ht : Real.log x < 8+Real.log 4 := (Real.log_lt_iff_lt_exp hx).mpr (by rwa [h4])
  have h4log : Real.log 4<4 := (Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<4) (by norm_num)).trans (by norm_num)
  have hshift : |Real.log x-Real.log 4|<8 := abs_lt.mpr ⟨by linarith only [hlog,h4log], by linarith only [ht]⟩
  have hcorr : 0<splineAutoCorr (Real.log x-Real.log 4) := by
    rw [splineAutoCorr_eq_eight_boxes]
    exact GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.upow_unit_pos 7 (by norm_num; exact hshift)
  have hzero := splineAutoCorr_zero_outside (hlog.trans_le (le_abs_self (Real.log x)))
  simp only [dyadicSpline,if_pos hx,squarePrimeWeight,Complex.ofReal_re,squareLogProfile,hzero,mul_zero,zero_sub]
  exact mul_neg_of_pos_of_neg two_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) (neg_neg_of_pos hcorr))

private theorem spline_negative_on_upper_first_primes {h : ℝ} (hl : upperFirstPrimeBandLeft≤h) (hu : h≤upperFirstPrimeBandRight) :
    dyadicSpline (2*h)<0 := by
  have he := Real.exp_pos 8
  apply spline_negative_on_last_dilate
  · dsimp only [upperFirstPrimeBandLeft] at hl; linarith only [he,hl]
  · dsimp only [upperFirstPrimeBandRight,R] at hu ⊢; linarith only [he,hu]

/-- The two adjacent positive quotients share the middle spline sample
with coefficient W(2)-W(1). The first excluded sample is at 3x. -/
theorem last_two_quotient_cells {b : ℕ} (hb : 3≤b) {x : ℝ} (hx : 0<x) (h3 : 4*Real.exp 8<3*x) :
    quotientMeshProfile b x-quotientMeshProfile 1 x =
      centeredPrimeWeight 1 1*(dyadicSpline x-dyadicSpline (2*x))+dyadicSpline (2*x) := by
  let F (j : ℕ) := (dyadicSpline (j*x)-dyadicSpline ((j+1:ℕ)*x))*centeredPrimeWeight 1 j
  have hz (j : ℕ) (hj : 3≤j) : dyadicSpline (j*x)=0 :=
    dyadicSpline_eq_zero_outside fun h => (h3.trans_le
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (3:ℝ)≤j) hx.le)).not_ge h.2
  have htail : ∑ j ∈ range (b-3), F (3+j)=0 := sum_eq_zero fun j _ => by
    simp only [F,hz (3+j) (by omega),hz (3+j+1) (by omega),sub_self,zero_mul]
  change (∑ j ∈ range b, F j)-(∑ j ∈ range 1, F j)=_
  calc _ = (∑ j ∈ range 3, F j)-(∑ j ∈ range 1, F j) := by
         conv_lhs => lhs; rw [show b=3+(b-3) by omega,sum_range_add]
         rw [htail,add_zero]
       _ = F 1+F 2 := by
         rw [show 3=2+1 by decide,Finset.sum_range_succ F 2,show 2=1+1 by decide,Finset.sum_range_succ F 1]
         ring
       _ = _ := by
         have h3' : dyadicSpline (3*x)=0 := by simpa only [Nat.cast_ofNat] using hz 3 le_rfl
         simp only [F,show (1+1:ℕ)=2 by decide,show (2+1:ℕ)=3 by decide,
           Nat.cast_one,Nat.cast_ofNat,one_mul,h3',sub_zero,second_centered_quotient_unit,mul_one]
         ring

/-- Immediately below half the last spline endpoint the two adjacent cells
have opposite signs. Their signed sum remains bounded below by a positive
constant on a full interval, uniformly in the far quotient endpoint. -/
theorem last_two_quotient_cells_opposite_signs :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ {x : ℝ}, (4*Real.exp 8)/2-δ<x → x<(4*Real.exp 8)/2 → ∀ {b : ℕ}, 3≤b →
      0<centeredPrimeWeight 1 1*(dyadicSpline x-dyadicSpline (2*x)) ∧
      dyadicSpline (2*x)<0 ∧ c≤quotientMeshProfile b x-quotientMeshProfile 1 x := by
  let F (x : ℝ) := centeredPrimeWeight 1 1*(dyadicSpline x-dyadicSpline (2*x))+dyadicSpline (2*x)
  have hR : 0<R := by positivity
  have hf := contDiff_six_dyadicSpline.continuous
  have hzero : dyadicSpline R=0 := by
    have hcl : IsClosed {x : ℝ | dyadicSpline x=0} := isClosed_eq hf continuous_const
    have hoff : Set.Ioi R ⊆ {x : ℝ | dyadicSpline x=0} := fun _ hx =>
      dyadicSpline_eq_zero_outside (fun h => hx.not_ge h.2)
    have hc := closure_minimal hoff hcl
    rw [closure_Ioi] at hc
    exact hc (Set.mem_Ici.mpr (le_refl R))
  have hneg : dyadicSpline (R/2)<0 := spline_negative_on_last_dilate
    (by dsimp only [R]; linarith only [Real.exp_pos 8]) (half_lt_self hR)
  have hpos : 0<F (R/2) := by
    dsimp only [F]
    rw [show 2*(R/2)=R by ring,hzero,sub_zero,add_zero]
    exact mul_pos_of_neg_of_neg first_centered_quotient_negative hneg
  have hcont : Continuous F := by dsimp only [F]; fun_prop
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp
    (hcont.continuousAt.eventually (lt_mem_nhds (half_lt_self hpos)))
  refine ⟨min r (R/12), F (R/2)/2,lt_min hr (by positivity),half_pos hpos,?_⟩
  intro x hl hu b hb
  have hxa : R/2-R/12<x := (sub_le_sub_left (min_le_right r (R/12)) _).trans_lt hl
  have hrx : R/2-r<x := (sub_le_sub_left (min_le_left r (R/12)) _).trans_lt hl
  have hx : x∈Metric.ball (R/2) r := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]; constructor <;> linarith only [hrx,hu,hr]
  have hsum : F (R/2)/2 < F x := hs hx
  have h2 : dyadicSpline (2*x)<0 := spline_negative_on_last_dilate
    (by dsimp only [R] at hxa; linarith only [hxa,Real.exp_pos 8]) (by linarith only [hu])
  have hrow := last_two_quotient_cells hb (by linarith only [hxa,hR] : 0<x)
    (by linarith only [hxa,hR] : R<3*x)
  change quotientMeshProfile b x-quotientMeshProfile 1 x=F x at hrow
  refine ⟨?_,h2,hsum.le.trans_eq hrow.symm⟩
  have hxsum := (half_pos hpos).trans hsum
  dsimp only [F] at hxsum
  linarith only [hxsum,h2]

/-- Every prime in the closed rescaled band sees a spline bounded away
from zero on the negative side. -/
theorem last_first_prime_spline_margin :
    ∃ c : ℝ, 0<c ∧ ∀ {h : ℝ}, upperFirstPrimeBandLeft≤h → h≤upperFirstPrimeBandRight → c ≤ -dyadicSpline (2*h) := by
  have hR : 0<R := by positivity
  have hLH : upperFirstPrimeBandLeft≤upperFirstPrimeBandRight := by dsimp only [upperFirstPrimeBandLeft,upperFirstPrimeBandRight]; linarith only [hR]
  have hc : Continuous (fun h : ℝ => -dyadicSpline (2*h)) :=
    (contDiff_six_dyadicSpline.continuous.comp (continuous_const.mul continuous_id)).neg
  obtain ⟨t,ht,htmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hLH) hc.continuousOn
  exact ⟨_,neg_pos.mpr (spline_negative_on_upper_first_primes ht.1 ht.2),fun hl hu => htmin ⟨hl,hu⟩⟩

/-- The weight of the first nonzero cofactor is positive. -/
theorem first_even_cofactor_positive : 0 < 1-cofactorDyadicCoefficient := by
  have h := cofactor_density_normalization
  have hlog : 2/3 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
  by_contra! hc
  have hl : 3/2 ≤ 1+cofactorDyadicCoefficient/2 := by linarith only [hc]
  have hh := (mul_lt_mul_of_pos_left hlog (by norm_num : (0:ℝ)<3/2)).trans_le
    (mul_le_mul_of_nonneg_right hl (Real.log_pos (by norm_num : (1:ℝ)<2)).le)
  linarith only [h,hh]

#print axioms last_two_quotient_cells_opposite_signs
#print axioms last_first_prime_cofactor
#print axioms last_first_prime_spline_margin
#print axioms first_even_cofactor_positive

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
