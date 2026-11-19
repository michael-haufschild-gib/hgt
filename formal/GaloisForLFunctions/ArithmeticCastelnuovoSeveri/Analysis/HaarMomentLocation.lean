import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.HaarCellNonlinearReadouts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.EveryHaarCellHasPositiveWeilEnergy
import GaloisForLFunctions.RHTower.Chebyshev.OrbitCubicTraceMoments

/-!
# Locating a complete logarithmic Haar pair from its moments

The ratio of adjacent logarithmic widths decreases strictly. Hence the
squared standardized skewness identifies the cell index, independently of
the detail magnitude or sign. Its signed third moment then recovers the
detail. The fourth moment obeys the rank-two Hankel relation.
-/

noncomputable section
open Set
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open BiarithmeticGaugeGeometry

private def widthAt (x : ℝ) := Real.log (x+1)-Real.log x

private theorem width_bounds {x : ℝ} (hx : 0 < x) :
    1/(x+1) ≤ widthAt x ∧ widthAt x < 1/x := by
  have h1 : 0 < x+1 := by linarith only [hx]
  have h := Real.log_le_sub_one_of_pos (div_pos hx h1)
  have g := Real.log_lt_sub_one_of_pos (div_pos h1 hx) (show (x+1)/x ≠ 1 by
    intro e
    linarith only [(div_eq_iff hx.ne').mp e])
  rw [Real.log_div hx.ne' h1.ne'] at h
  rw [Real.log_div h1.ne' hx.ne'] at g
  have he : x/(x+1)-1 = -(1/(x+1)) := by field_simp; ring
  have he' : (x+1)/x-1 = 1/x := by field_simp; ring
  rw [he] at h
  exact ⟨by unfold widthAt; linarith only [h],g.trans_eq he'⟩

private theorem width_pos {x : ℝ} (hx : 0 < x) : 0 < widthAt x :=
  (by positivity : 0 < 1/(x+1)).trans_le (width_bounds hx).1

private theorem width_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt widthAt (-1/(x*(x+1))) x := by
  have h1 : 0 < x+1 := by linarith only [hx]
  have raw : HasDerivAt widthAt (1/(x+1)-x⁻¹) x :=
    (((hasDerivAt_id x).add_const 1).log h1.ne').sub (Real.hasDerivAt_log hx.ne')
  convert raw using 1
  field_simp [hx.ne',h1.ne']
  ring

private theorem adjacent_ratio_strict :
    StrictAntiOn (fun x : ℝ => widthAt x / widthAt (x+1)) (Ioi 0) := by
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt (fun y => widthAt y/widthAt (y+1))
      ((-1/(x*(x+1))*widthAt (x+1)-widthAt x*(-1/((x+1)*(x+1+1))*1))/(widthAt (x+1))^2) x := by
    have hx1 : 0<x+1 := by linarith only [hx]
    have inner : HasDerivAt (fun y : ℝ => y+1) 1 x := (hasDerivAt_id x).add_const 1
    have shift : HasDerivAt (fun y : ℝ => widthAt (y+1)) (-1/((x+1)*(x+1+1))*1) x := by
      simpa only [Function.comp_def] using HasDerivAt.comp (h₂:=widthAt) (h:=fun y : ℝ => y+1) x
        (width_derivative hx1) inner
    exact (width_derivative hx).div shift (width_pos hx1).ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    change 0 < x at hx
    have hx1 : 0 < x+1 := by linarith
    have hx2 : 0 < x+1+1 := by linarith
    rw [(hder x hx).deriv]
    refine div_neg_of_neg_of_pos ?_ (sq_pos_of_pos (width_pos hx1))
    have hi := (lt_div_iff₀ hx).mp (width_bounds hx).2
    have hj := (div_le_iff₀ hx2).mp (width_bounds hx1).1
    have he : -1/(x*(x+1))*widthAt (x+1)-widthAt x*(-1/((x+1)*(x+1+1))*1) =
        (widthAt x*x-widthAt (x+1)*(x+1+1))/(x*(x+1)*(x+1+1)) := by
      field_simp [hx.ne',hx1.ne',hx2.ne']
      ring
    rw [he]
    exact div_neg_of_neg_of_pos (by linarith only [hi,hj]) (mul_pos (mul_pos hx hx1) hx2)

private def widthRatio (i : ℕ) : ℝ :=
  logCellWidth (2*(i+1))/logCellWidth (2*(i+1)+1)

private theorem ratio_real (i : ℕ) : widthRatio i =
    widthAt (2*((i:ℝ)+1)) / widthAt (2*((i:ℝ)+1)+1) := by
  simp only [widthRatio,logCellWidth,widthAt,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]

/-- Ratios of successive left and right cell lengths separate the positions. -/
theorem haar_width_ratio_strict : StrictAnti (fun i : ℕ =>
    logCellWidth (2*(i+1))/logCellWidth (2*(i+1)+1)) := by
  intro i j hij
  change widthRatio j < widthRatio i
  rw [ratio_real,ratio_real]
  have hij' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
  apply adjacent_ratio_strict
  · show 0<2*((i:ℝ)+1)
    positivity
  · show 0<2*((j:ℝ)+1)
    positivity
  · linarith only [hij']

private theorem ratio_gt_one (i : ℕ) : 1 < widthRatio i := by
  rw [ratio_real]
  let x : ℝ := 2*((i:ℝ)+1)
  have hx : 0 < x := by dsimp [x]; positivity
  have h1 : 0 < x+1 := by positivity
  exact (one_lt_div (width_pos h1)).mpr ((width_bounds h1).2.trans_le (width_bounds hx).1)

/-- Squared standardized skewness, expressed in terms of the width ratio. -/
def skewSignature (i : ℕ) := widthRatio i+(widthRatio i)⁻¹-2

theorem skewSignature_strictAnti : StrictAnti skewSignature := by
  intro i j hij
  have hlt : widthRatio j < widthRatio i := haar_width_ratio_strict hij
  have hi := ratio_gt_one i
  have hj := ratio_gt_one j
  have hp : 1 < widthRatio i * widthRatio j := by
    nlinarith only [hi,hj,mul_pos (sub_pos.mpr hi) (sub_pos.mpr hj)]
  have he : skewSignature i-skewSignature j =
      ((widthRatio i-widthRatio j)*(widthRatio i*widthRatio j-1))/(widthRatio i*widthRatio j) := by
    unfold skewSignature
    field_simp [(by linarith only [hi] : widthRatio i ≠ 0),
      (by linarith only [hj] : widthRatio j ≠ 0)]
    ring
  apply sub_pos.mp
  rw [he]
  exact div_pos (mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hp)) (by linarith only [hp])

/-- Centered moments under normalized length on the given complete pair. -/
def detailMoment (k : ℕ) (d : ℕ → ℝ) (i : ℕ) : ℝ :=
  detailReadout (fun x => x^k) d (i+1) (i+1)/logCellWidth (i+1)

private theorem moment_values (d : ℕ → ℝ) (i : ℕ) :
    let a := i+1
    let p := haarRightCoeff a
    let q := haarLeftCoeff a
    let v := d a
    detailMoment 2 d i = p*q*v^2 ∧ detailMoment 3 d i = p*q*(q-p)*v^3 ∧
      detailMoment 4 d i = p*q*(q^3+p^3)*v^4 := by
  let a := i+1
  let L := logCellWidth (2*a)
  let R := logCellWidth (2*a+1)
  have hL : 0 < L := logCellWidth_pos (by dsimp [a]; omega)
  have hR : 0 < R := logCellWidth_pos (by dsimp [a]; omega)
  have hs := logCellWidth_pair_sum (show 1 ≤ a by omega)
  have h (k : ℕ) : detailMoment k d i =
      (((d a*(R/(L+R)))^k-0^k)*L+((-(d a*(L/(L+R))))^k-0^k)*R)/(L+R) := by
    have hw := detailReadout_law (fun x => x^k) d i 0
    simp only [Nat.add_zero] at hw
    unfold detailMoment
    rw [hw,← hs]
    rfl
  refine ⟨?_,?_,?_⟩ <;> rw [h] <;>
    simp only [haarRightCoeff,haarLeftCoeff,zero_pow (by norm_num : 2 ≠ 0),
      zero_pow (by norm_num : 3 ≠ 0),zero_pow (by norm_num : 4 ≠ 0),sub_zero] <;>
    dsimp only [a,L,R] at * <;>
    field_simp [(add_pos hL hR).ne'] <;> ring

/-- The index is an amplitude-independent invariant of the second and third
moments. The formula remains valid at zero amplitude without division. -/
theorem skewSignature_identity (d : ℕ → ℝ) (i : ℕ) :
    (detailMoment 3 d i)^2 = skewSignature i*(detailMoment 2 d i)^3 := by
  obtain ⟨h2,h3,_⟩ := moment_values d i
  rw [h2,h3]
  unfold skewSignature widthRatio haarRightCoeff haarLeftCoeff
  have hL := logCellWidth_pos (show 1 ≤ 2*(i+1) by omega)
  have hR := logCellWidth_pos (show 1 ≤ 2*(i+1)+1 by omega)
  field_simp [hL.ne',hR.ne',(add_pos hL hR).ne']
  ring

/-- The fourth centered moment is forced by the first three moments on
every complete Haar pair, by vanishing of the order-three Hankel determinant. -/
theorem haar_fourth_moment_rigidity (d : ℕ → ℝ) (i : ℕ) :
    detailMoment 2 d i*detailMoment 4 d i-(detailMoment 3 d i)^2-(detailMoment 2 d i)^3 = 0 := by
  obtain ⟨h2,h3,h4⟩ := moment_values d i
  rw [h2,h3,h4]
  have hs := haarCoeff_sum (show 1 ≤ i+1 by omega)
  let p := haarRightCoeff (i+1)
  let q := haarLeftCoeff (i+1)
  have he : p+q = 1 := by dsimp only [p,q]; linarith only [hs]
  change (p*q*_)*(p*q*(q^3+p^3)*_) - (p*q*(q-p)*_)^2 - (p*q*_)^3 = 0
  rw [show q = 1-p by linarith only [he]]
  ring

/-- Two nonzero details on unknown cells have identical second and third
moments precisely when their locations and signed amplitudes agree. The
only cross-cell ambiguity is the zero signal. -/
theorem haar_moments_identify_location (d e : ℕ → ℝ) (i j : ℕ) :
    (detailMoment 2 d i = detailMoment 2 e j ∧ detailMoment 3 d i = detailMoment 3 e j) ↔
      (d (i+1) = 0 ∧ e (j+1) = 0) ∨ (i = j ∧ d (i+1) = e (j+1)) := by
  have van (f : ℕ → ℝ) (a : ℕ) : detailMoment 2 f a = 0 ↔ f (a+1) = 0 := by
    obtain ⟨h,_,_⟩ := moment_values f a
    have hl := logCellWidth_pos (show 1 ≤ 2*(a+1) by omega)
    have hr := logCellWidth_pos (show 1 ≤ 2*(a+1)+1 by omega)
    rw [h]
    simp [haarRightCoeff,haarLeftCoeff,hl.ne',hr.ne',(add_pos hl hr).ne']
  constructor
  · rintro ⟨hv,hs⟩
    by_cases hz : detailMoment 2 d i = 0
    · exact Or.inl ⟨(van d i).mp hz,(van e j).mp (hv ▸ hz)⟩
    have h1 := skewSignature_identity d i
    rw [hs,hv,skewSignature_identity e j] at h1
    have hij := skewSignature_strictAnti.injective
      (mul_right_cancel₀ (pow_ne_zero _ (hv ▸ hz)) h1.symm)
    subst j
    right
    refine ⟨rfl,?_⟩
    have h3 (f : ℕ → ℝ) : detailMoment 3 f i =
        (haarMass (i+1)*(haarLeftCoeff (i+1)-haarRightCoeff (i+1)))*f (i+1)^3/logCellWidth (i+1) := by
      unfold detailMoment
      simpa only [Nat.add_zero] using congrArg (fun z : ℝ => z/logCellWidth (i+1)) (detail_cubic_moment f i 0)
    rw [h3,h3,div_left_inj' (logCellWidth_pos (show 1 ≤ i+1 by omega)).ne',
      mul_right_inj' (detail_skew_negative i).ne] at hs
    exact (show Odd (3:ℕ) from ⟨1,rfl⟩).pow_inj.mp hs
  · rintro (⟨hd,he⟩|⟨hij,he⟩)
    · obtain ⟨dv,ds,_⟩ := moment_values d i
      obtain ⟨ev,es,_⟩ := moment_values e j
      simp [dv,ds,ev,es,hd,he]
    · subst j
      obtain ⟨dv,ds,_⟩ := moment_values d i
      obtain ⟨ev,es,_⟩ := moment_values e i
      simp only [dv,ds,ev,es,he,and_self]

open _root_.RHTower.OrbitCubic

/-- At each cell there is a positive amplitude and a cubic trace law with
the same centered variance and third moment. The fourth moment of the
three-root law exceeds the two-cell reading by exactly one half. -/
theorem haar_orbit_fourth_gap (i : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ q a b c : ℝ, binary q a 1 = 0 ∧ binary q b 1 = 0 ∧ binary q c 1 = 0 ∧
      let H := fun k => detailMoment k (fun _ => D) i
      let M := moment a b c (q+1/2)
      H 2 = 2 ∧ M 2 = H 2 ∧ M 3 = H 3 ∧ M 4 = H 4+1/2 := by
  let L := haarLeftCoeff (i+1)
  let R := haarRightCoeff (i+1)
  have hl := logCellWidth_pos (show 1 ≤ 2*(i+1) by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2*(i+1)+1 by omega)
  have hp : 0 < R*L := mul_pos (div_pos hl (add_pos hl hr)) (div_pos hr (add_pos hl hr))
  let D := Real.sqrt (2/(R*L))
  let H := fun k => detailMoment k (fun _ => D) i
  have h2 : H 2 = 2 := by
    change detailMoment 2 _ i = 2
    rw [(moment_values (fun _ => D) i).1]
    change R*L*(Real.sqrt (2/(R*L)))^2 = 2
    rw [Real.sq_sqrt (div_pos (by norm_num) hp).le]
    rw [mul_comm (R*L),div_mul_cancel₀ _ hp.ne']
  let q := -H 3/2
  obtain ⟨a,b,c,ha,hb,hc,_,_,_,_,_,m2,m3,_,hdet⟩ := centered_trace_invariants q
  have h3 : moment a b c (q+1/2) 3 = H 3 := by rw [m3]; dsimp only [q]; ring
  have hh := haar_fourth_moment_rigidity (fun _ => D) i
  change H 2*H 4-H 3^2-H 2^3 = 0 at hh
  rw [m2,h3] at hdet
  rw [h2] at hh
  exact ⟨D,Real.sqrt_pos.mpr (div_pos (by norm_num) hp),q,a,b,c,ha,hb,hc,
    h2,m2.trans h2.symm,h3,by linarith only [hh,hdet]⟩

#print axioms haar_width_ratio_strict
#print axioms skewSignature_strictAnti
#print axioms skewSignature_identity
#print axioms haar_fourth_moment_rigidity
#print axioms haar_moments_identify_location
#print axioms haar_orbit_fourth_gap
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
