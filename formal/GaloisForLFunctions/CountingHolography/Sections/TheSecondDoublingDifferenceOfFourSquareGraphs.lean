import GaloisForLFunctions.CountingHolography.Sections.FourSquareGraphsWithBothPoleDegreesZero
import GaloisForLFunctions.CountingHolography.Sections.UnitMultiplicityOnThePoleHyperplane
import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityOnThePoleHyperplane

/-!
# The second doubling difference on the reciprocal four-graph divisor

Its two long-lag displacements converge to log four with inverse-linear
error. The spline trace increment estimate makes the error in the degree
bounded. A second forward doubling difference then reads the zero width.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SquareRootThreshold SurfaceOfSpecZ ArithmeticOrientationGeometry
open ArithmeticScatteringHolography RenormalizedIntersectionTheory Zeta23

private def X (n : ℕ) : ℝ := (n:ℝ)+1
private def f (n : ℕ) := realSplineTrace (2*Real.log (X n))
private def U (n : ℕ) := 2*n+1

private theorem X_step (n : ℕ) : X (U n) = 2*X n := by
  unfold X U
  push_cast
  ring

private theorem X_one (n : ℕ) : 1 ≤ X n := by dsimp only [X]; linarith only [Nat.cast_nonneg (α := ℝ) n]

private theorem square_bound {s : ℝ} (hs : 0 ≤ s) (hw : zetaZeroWidth ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |f n| ≤ C*(X n)^(2*s) := by
  obtain ⟨C,hC⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hs).mpr hw
  refine ⟨|C|,abs_nonneg _,fun n => ?_⟩
  have hx := zero_lt_one.trans_le (X_one n)
  have ht := hC (2*Real.log (X n)) (mul_nonneg two_pos.le (Real.log_nonneg (X_one n)))
  rw [orbitCorr_splineCycle_eq] at ht
  have he : Real.exp (s*(2*Real.log (X n))) = (X n)^(2*s) := by
    rw [Real.rpow_def_of_pos hx]; congr 1; ring
  rw [he] at ht
  exact ht.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx.le _))

private theorem f_sublinear : Tendsto (fun n : ℕ => f n/X n) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := square_bound zetaZeroWidth_nonneg le_rfl
  have hw : 0 < 1-2*zetaZeroWidth := by linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]
  have hx : Tendsto X atTop atTop := tendsto_atTop_mono (f := fun n : ℕ => (n:ℝ))
    (fun _ => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have ht := ((tendsto_rpow_neg_atTop hw).comp hx).const_mul C
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using ht)
  refine Eventually.of_forall fun n => ?_
  have hx' := zero_lt_one.trans_le (X_one n)
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hx']
  change |f n|/X n ≤ C*(X n)^(-(1-2*zetaZeroWidth))
  rw [show -(1-2*zetaZeroWidth)=2*zetaZeroWidth-1 by ring,Real.rpow_sub hx',Real.rpow_one,← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h n) hx'.le

private theorem four_lag_error : ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 0 < n →
    |integerProbe _ (fourSquareDivisor n)-2*(4*f n-4*f (U n)+f (U (U n)))| ≤ D := by
  obtain ⟨L,hL,hincr⟩ := realSplineTrace_increment
  obtain ⟨C,hC⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le zetaZeroWidth_nonneg).mpr le_rfl
  let w := zetaZeroWidth
  let H := Real.log 4
  let K := |C| * Real.exp (w*(2*H))
  have hK : 0 ≤ K := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨10*|realSplineTrace 0|+8*K+240*L,by positivity,fun n hn => ?_⟩
  let s := 2*X n
  let r := (4*(n:ℝ)+3)/(2*n)
  let t := 2*Real.log s
  let h := 2*Real.log r
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp := zero_lt_one.trans_le hn'
  have hs : 4 ≤ s := by dsimp only [s,X]; linarith only [hn']
  have hs' : 0 < s := by linarith only [hs]
  have hs4 : s ≤ 4*n := by dsimp only [s,X]; linarith only [hn']
  have hr : 2 ≤ r := (le_div_iff₀ (mul_pos two_pos hnp)).mpr (by linarith)
  have hr4 : r ≤ 4 := (div_le_iff₀ (mul_pos two_pos hnp)).mpr (by linarith only [hn'])
  have hr' : 0 < r := by linarith only [hr]
  have hH : H = 2*Real.log 2 := by unfold H; rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hH0 : 0 ≤ H := Real.log_nonneg (by norm_num)
  have hHh : H ≤ h := by rw [hH]; exact mul_le_mul_of_nonneg_left (Real.log_le_log two_pos hr) two_pos.le
  have hht : h ≤ t := mul_le_mul_of_nonneg_left (Real.log_le_log hr' (hr4.trans hs)) two_pos.le
  have hh2 : h ≤ 2*H := mul_le_mul_of_nonneg_left (Real.log_le_log hr' hr4) two_pos.le
  have hshort : |realSplineTrace h| ≤ K := by
    have hh := hC h (hH0.trans hHh)
    rw [orbitCorr_splineCycle_eq] at hh
    exact hh.trans (mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hh2 zetaZeroWidth_nonneg)) (Real.exp_pos _).le (abs_nonneg _))
  have hdiff : h-H ≤ 3/(2*n) := by
    rw [hH]
    have hx := Real.log_le_sub_one_of_pos (div_pos hr' two_pos)
    rw [Real.log_div hr'.ne' two_ne_zero] at hx
    have he : 2*(r/2-1) = 3/(2*n) := by dsimp only [r]; field_simp; ring
    unfold h
    linarith only [hx,he]
  have hcap : Real.exp (w*(t+h)) ≤ 16*n := by
    have hx : 0 ≤ t+h := add_nonneg (hH0.trans (hHh.trans hht)) (hH0.trans hHh)
    have hw : w ≤ 1/2 := ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans (by norm_num)
    calc _ ≤ Real.exp ((1/2)*(t+h)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw hx)
      _ = s*r := by
        rw [show (1/2)*(t+h) = Real.log s+Real.log r by dsimp only [t,h]; ring,
          Real.exp_add,Real.exp_log hs',Real.exp_log hr']
      _ ≤ _ := (mul_le_mul hs4 hr4 hr'.le (by positivity)).trans_eq (by ring)
  have hprice {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ t+h) (hgap : y-x = h-H) :
      |realSplineTrace y-realSplineTrace x| ≤ 24*L := by
    have he := hincr x y hx hxy
    rw [hgap] at he
    have hcap' := (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy zetaZeroWidth_nonneg)).trans hcap
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hdiff hL) hcap'
      (Real.exp_pos _).le (mul_nonneg hL (by positivity))
    exact he.trans (hh.trans_eq (by field_simp; ring))
  have hplus := hprice (x := t+H) (y := t+h) (by linarith only [hH0,hHh,hht])
    (by linarith only [hHh]) le_rfl (by ring)
  have hminus := hprice (x := t-h) (y := t-H) (sub_nonneg.mpr hht)
    (by linarith only [hHh]) (by linarith only [hHh,hH0]) (by ring)
  have hu : f (U n) = realSplineTrace t := by simp only [f,X_step,t,s]
  have hlo : f n = realSplineTrace (t-H) := by
    unfold f t s
    rw [hH,Real.log_mul two_ne_zero (zero_lt_one.trans_le (X_one n)).ne']
    congr 1; ring
  have hhi : f (U (U n)) = realSplineTrace (t+H) := by
    unfold f t s
    rw [X_step,X_step,hH,Real.log_mul two_ne_zero (mul_pos two_pos (zero_lt_one.trans_le (X_one n))).ne',
      Real.log_mul two_ne_zero (zero_lt_one.trans_le (X_one n)).ne']
    congr 1; ring
  rw [integerProbe_fourSquareDivisor hn,hu,hlo,hhi]
  change |(10*realSplineTrace 0-8*realSplineTrace h+2*(realSplineTrace (t+h)-4*realSplineTrace t+
    4*realSplineTrace (t-h)))-2*(4*realSplineTrace (t-H)-4*realSplineTrace t+realSplineTrace (t+H))| ≤ _
  rw [abs_le]
  constructor <;> linarith only [(abs_le.mp hplus).1,(abs_le.mp hplus).2,
    (abs_le.mp hminus).1,(abs_le.mp hminus).2,(abs_le.mp hshort).1,(abs_le.mp hshort).2,
    le_abs_self (realSplineTrace 0),neg_le_abs (realSplineTrace 0)]

/-- The one-sided growth exponent of the reciprocal four-graph degrees
recovers the actual zero width. -/
theorem zetaZeroWidth_le_iff_fourSquare_degree {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      -(A*((n:ℝ)+1)^(2*s)) ≤ integerProbe _ (fourSquareDivisor n) := by
  obtain ⟨D,hD,hd⟩ := four_lag_error
  have hr := mul_nonneg two_pos.le hs
  have slack (n : ℕ) : D ≤ D*(X n)^(2*s) := le_mul_of_one_le_right hD (Real.one_le_rpow (X_one n) hr)
  constructor
  · intro hw
    obtain ⟨C,hC,h⟩ := square_bound hs hw
    let b := (2:ℝ)^(2*s)
    have hstep (n : ℕ) : (X (U n))^(2*s) = b*(X n)^(2*s) := by
      rw [X_step,Real.mul_rpow two_pos.le (zero_le_one.trans (X_one n))]
    refine ⟨8*C+8*C*b+2*C*b^2+D,fun n hn => ?_⟩
    have h1 := (abs_le.mp (h (U n))).2
    have h2 := (abs_le.mp (h (U (U n)))).1
    rw [hstep] at h1
    rw [hstep,hstep] at h2
    change -(_*(X n)^(2*s)) ≤ _
    linarith only [(abs_le.mp (h n)).1,h1,h2,(abs_le.mp (hd n hn)).1,slack n]
  · rintro ⟨A,hA⟩
    obtain ⟨B,hB⟩ := lower_of_second_doubling_difference (F := f) (C := (A+D)/2)
      (show 2*s<1 by linarith only [hs']) f_sublinear (fun n hn => by
        change -((A+D)/2*(X n)^(2*s)) ≤ 4*f n-4*f (U n)+f (U (U n))
        have hh := hA n hn
        change -(A*(X n)^(2*s)) ≤ _ at hh
        linarith only [hh,(abs_le.mp (hd n hn)).2,slack n])
    apply (zetaZeroWidth_le_iff_bddBelow_of_powGaps hs hs' (by norm_num)
      (powGaps_kthPrimePowers (k := 2) (by norm_num))).mpr
    refine ⟨2*B,?_⟩
    rintro d ⟨p,hp,rfl⟩
    have hsub : X (p-1) = p := by dsimp only [X]; rw [Nat.cast_sub hp.pos,Nat.cast_one,sub_add_cancel]
    have h := hB (p-1) (by have := hp.two_le; omega)
    change -(B*(X (p-1))^(2*s)) ≤ realSplineTrace (2*Real.log (X (p-1))) at h
    rw [hsub] at h
    have he : ((p^2:ℕ):ℝ)^s = (p:ℝ)^(2*s) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Real.rpow_natCast_mul (Nat.cast_nonneg (α := ℝ) p) 2 s).symm
    rw [he,← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq,Nat.cast_pow,Real.log_pow]
    change -(2*B*(p:ℝ)^(2*s)) ≤ 2*realSplineTrace (2*Real.log p)
    linarith only [h]

/-- One rational comparison per member of a six-unit four-graph family
annihilating both poles suffices for the Riemann hypothesis. -/
theorem riemannHypothesis_iff_fourSquare_horizon_power :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ n : ℕ, 0 < n →
      let m := horizonMultiplicity (fourSquareHorizon n)
      ordinaryPrimeGenerator (m • fourSquareDivisor n) ≤ (B:ℚ)^(m^2) := by
  have hrh : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 :=
    riemannHypothesis_iff_zetaZeroWidth_eq_zero.trans ⟨fun h => h.le,fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [hrh,zetaZeroWidth_le_iff_fourSquare_degree le_rfl (by norm_num)]
  simp only [mul_zero,Real.rpow_zero,mul_one]
  have he := lower_degree_iff_horizon_power (ι := ℕ+) (fun n => fourSquareHorizon n)
    (fun n => fourSquareDivisor n) (M := 6) (by norm_num)
    (fun n => (fourSquareDivisor_degrees n.property).1) (fun n => fourSquareDivisor_mass n)
  constructor
  · rintro ⟨A,hA⟩
    obtain ⟨B,hB,h⟩ := he.mp ⟨A,fun n => hA n n.property⟩
    exact ⟨B,hB,fun n hn => h ⟨n,hn⟩⟩
  · rintro ⟨B,hB,h⟩
    obtain ⟨A,hA⟩ := he.mpr ⟨B,hB,fun n => h n n.property⟩
    exact ⟨A,fun n hn => hA ⟨n,hn⟩⟩

#print axioms zetaZeroWidth_le_iff_fourSquare_degree
#print axioms riemannHypothesis_iff_fourSquare_horizon_power

end GaloisForLFunctions.CountingHolography.Sections
