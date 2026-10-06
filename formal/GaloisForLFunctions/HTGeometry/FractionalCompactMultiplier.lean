import GaloisForLFunctions.HTGeometry.DirectionalGagliardoFourier

/-!
# Compact multipliers for directional fractional energy

The exact product difference splits into an input difference and a coefficient
increment. Compact C1 data supply both a supremum bound and a Lipschitz constant.
The increment has an admitted scalar majorant at zero and infinity for every
fractional order in `(0,1)`. Nonnegative integration and translation invariance
then prove the full energy estimate without a prior integrability assumption.

Joint compactness in parameter and physical variables yields one constant for
all parameter values. The Schwartz corollary gives finite energy controlled by
physical mass and weighted Fourier energy. This is the multiplier step toward
BAG's weighted logarithmic transfer; actual Mellin coefficients and first Euler
derivative attachment remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped FourierTransform Topology ContDiff ENNReal
namespace GaloisForLFunctions.HTGeometry

private def multiplierRemainder (s M L h : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun t => L^2*t^(1-2*s)) h+
    (Ioi (1 : ℝ)).indicator (fun t => 4*M^2*t^(-(1+2*s))) h

private theorem multiplier_remainder_nonneg (s M L h : ℝ) :
    0 ≤ multiplierRemainder s M L h := by
  apply add_nonneg
  · exact Set.indicator_nonneg (fun t ht =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht.1.le _)) _
  · exact Set.indicator_nonneg (fun t ht =>
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (Real.rpow_nonneg (zero_lt_one.trans ht).le _)) _

private theorem multiplier_remainder_integrable
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1}) (M L : ℝ) :
    Integrable (multiplierRemainder s.1 M L) := by
  have hi : IntegrableOn (fun h : ℝ => h^(1-2*s.1)) (Ioc (0 : ℝ) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by linarith [s.2.2])
  have hj := integrableOn_Ioi_rpow_of_lt (by linarith [s.2.1] : -(1+2*s.1) < -1)
    (by norm_num : (0 : ℝ)<1)
  exact (IntegrableOn.integrable_indicator (hi.const_mul (L^2)) measurableSet_Ioc).add
    (IntegrableOn.integrable_indicator (hj.const_mul (4*M^2)) measurableSet_Ioi)

private theorem product_difference_sq (a b c d : ℂ) :
    ‖a*b-c*d‖^2 ≤ 2*‖a‖^2*‖b-d‖^2+2*‖a-c‖^2*‖d‖^2 := by
  have he : a*b-c*d=a*(b-d)+(a-c)*d := by ring
  rw [he]
  have hn := pow_le_pow_left₀ (norm_nonneg (a*(b-d)+(a-c)*d)) (norm_add_le _ _) 2
  have hs := sq_nonneg (‖a*(b-d)‖-‖(a-c)*d‖)
  rw [norm_mul,norm_mul] at hn hs
  nlinarith only [hn,hs]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem multiplier_increment_kernel (s : ℝ) (A : E→ℂ) (M L : ℝ)
    (hM : ∀x, ‖A x‖ ≤ M) (hL : ∀x y, ‖A x-A y‖ ≤ L*‖x-y‖)
    (v x : E) (h : {r : ℝ // 0<r}) :
    ‖A x-A (x+h.1 • v)‖^2*h.1^(-(1+2*s)) ≤
      multiplierRemainder s M (L*‖v‖) h.1 := by
  have hpow : 0 ≤ h.1^(-(1+2*s)) := (Real.rpow_pos_of_pos h.2 _).le
  by_cases hh : h.1 ≤ 1
  · have hbound : ‖A x-A (x+h.1 • v)‖ ≤ (L*‖v‖)*h.1 := by
      have hx := hL x (x+h.1 • v)
      simpa only [sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
        abs_of_pos h.2,mul_assoc,mul_comm,mul_left_comm] using hx
    have hb := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hbound 2) hpow
    have he : h.1^2*h.1^(-(1+2*s))=h.1^(1-2*s) := by
      rw [←Real.rpow_two,←Real.rpow_add h.2]
      congr 1
      ring
    simpa only [multiplierRemainder,indicator_of_mem (show h.1∈Ioc (0 : ℝ) 1 from ⟨h.2,hh⟩),
      indicator_of_notMem (show h.1∉Ioi (1 : ℝ) from not_lt.mpr hh),add_zero,
      mul_pow,mul_assoc,he] using hb
  · have hbound : ‖A x-A (x+h.1 • v)‖ ≤ 2*M := by
      calc ‖A x-A (x+h.1 • v)‖ ≤ ‖A x‖+‖A (x+h.1 • v)‖ := norm_sub_le _ _
        _ ≤ M+M := add_le_add (hM _) (hM _)
        _ = 2*M := (two_mul _).symm
    have hb := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hbound 2) hpow
    simpa only [multiplierRemainder,indicator_of_notMem (show h.1∉Ioc (0 : ℝ) 1 from fun ht => hh ht.2),
      indicator_of_mem (show h.1∈Ioi (1 : ℝ) from lt_of_not_ge hh),zero_add,
      mul_pow,show (2 : ℝ)^2=4 by norm_num] using hb

private theorem multiplier_remainder_measurable (s M L : ℝ) :
    Measurable (multiplierRemainder s M L) := by
  have h1 : Measurable (fun h : ℝ => L^2*h^(1-2*s)) := by fun_prop
  have h2 : Measurable (fun h : ℝ => 4*M^2*h^(-(1+2*s))) := by fun_prop
  exact (h1.indicator measurableSet_Ioc).add (h2.indicator measurableSet_Ioi)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem multiplier_difference_kernel (s : ℝ) (A f : E→ℂ) (M L : ℝ)
    (hM : ∀x, ‖A x‖ ≤ M) (hL : ∀x y, ‖A x-A y‖ ≤ L*‖x-y‖)
    (v x : E) (h : {r : ℝ // 0<r}) :
    ‖A x*f x-A (x+h.1 • v)*f (x+h.1 • v)‖^2*h.1^(-(1+2*s)) ≤
      (2*M^2)*(‖f x-f (x+h.1 • v)‖^2*h.1^(-(1+2*s)))+
        (2*multiplierRemainder s M (L*‖v‖) h.1)*‖f (x+h.1 • v)‖^2 := by
  have hp : 0 ≤ h.1^(-(1+2*s)) := (Real.rpow_pos_of_pos h.2 _).le
  have hm2 := pow_le_pow_left₀ (norm_nonneg (A x)) (hM x) 2
  have hi := multiplier_increment_kernel s A M L hM hL v x h
  calc ‖A x*f x-A (x+h.1 • v)*f (x+h.1 • v)‖^2*h.1^(-(1+2*s))
      ≤ (2*‖A x‖^2*‖f x-f (x+h.1 • v)‖^2+
        2*‖A x-A (x+h.1 • v)‖^2*‖f (x+h.1 • v)‖^2)*h.1^(-(1+2*s)) :=
          mul_le_mul_of_nonneg_right (product_difference_sq _ _ _ _) hp
    _ = (2*‖A x‖^2)*(‖f x-f (x+h.1 • v)‖^2*h.1^(-(1+2*s)))+
        (2*(‖A x-A (x+h.1 • v)‖^2*h.1^(-(1+2*s))))*‖f (x+h.1 • v)‖^2 := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by norm_num))
        (mul_nonneg (sq_nonneg _) hp))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) (sq_nonneg _))

private theorem multiplier_energy_bound (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (A f : E→ℂ) (hf : Continuous f) (M L : ℝ)
    (hM : ∀x, ‖A x‖ ≤ M) (hL : ∀x y, ‖A x-A y‖ ≤ L*‖x-y‖) (v : E) :
    (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      ENNReal.ofReal (‖A x*f x-A (x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1)))) ≤
      ENNReal.ofReal (2*M^2)*(∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1))))+
      ENNReal.ofReal (∫h in Ioi (0 : ℝ), 2*multiplierRemainder s.1 M (L*‖v‖) h)*
        ∫⁻ x : E, ENNReal.ofReal (‖f x‖^2) := by
  have hfm := hf.measurable
  have hrm := multiplier_remainder_measurable s.1 M (L*‖v‖)
  have hri := (multiplier_remainder_integrable s M (L*‖v‖)).const_mul 2
  have hstep (h : ℝ) (hh : h∈Ioi (0 : ℝ)) :
      (∫⁻ x : E, ENNReal.ofReal (‖A x*f x-A (x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal (2*M^2)*(∫⁻ x : E,
          ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1))))+
          ENNReal.ofReal (2*multiplierRemainder s.1 M (L*‖v‖) h)*
            ∫⁻ x : E, ENNReal.ofReal (‖f x‖^2) := by
    have hnon : 0 ≤ 2*multiplierRemainder s.1 M (L*‖v‖) h :=
      mul_nonneg (by norm_num) (multiplier_remainder_nonneg _ _ _ _)
    calc (∫⁻ x : E, ENNReal.ofReal (‖A x*f x-A (x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1))))
        ≤ ∫⁻ x : E,
          ENNReal.ofReal (2*M^2)*ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1)))+
          ENNReal.ofReal (2*multiplierRemainder s.1 M (L*‖v‖) h)*ENNReal.ofReal (‖f (x+h • v)‖^2) := by
            apply lintegral_mono
            intro x
            change ENNReal.ofReal _ ≤ ENNReal.ofReal _*ENNReal.ofReal _+ENNReal.ofReal _*ENNReal.ofReal _
            rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*M^2),←ENNReal.ofReal_mul hnon,
              ←ENNReal.ofReal_add
                (mul_nonneg (by positivity : 0 ≤ 2*M^2)
                  (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (show 0<h from hh) _).le))
                (mul_nonneg hnon (sq_nonneg _))]
            exact ENNReal.ofReal_le_ofReal (multiplier_difference_kernel s.1 A f M L hM hL v x ⟨h,hh⟩)
      _ = _ := by
        rw [lintegral_add_left (by fun_prop)]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_add_right_eq_self (fun x : E => ENNReal.ofReal (‖f x‖^2)) (h • v)]
  have hem : Measurable (fun z : ℝ×E =>
      ENNReal.ofReal (‖f z.2-f (z.2+z.1 • v)‖^2*z.1^(-(1+2*s.1)))) := by fun_prop
  refine (setLIntegral_mono' measurableSet_Ioi hstep).trans_eq ?_
  have hEm : Measurable (fun h : ℝ => ENNReal.ofReal (2*M^2)*
      ∫⁻ x : E, ENNReal.ofReal (‖f x-f (x+h • v)‖^2*h^(-(1+2*s.1)))) :=
    measurable_const.mul hem.lintegral_prod_right'
  rw [lintegral_add_left hEm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_mul_const _ (by fun_prop)]
  rw [←ofReal_integral_eq_lintegral_ofReal hri.integrableOn
    (Eventually.of_forall (fun h => mul_nonneg (by norm_num) (multiplier_remainder_nonneg _ _ _ _)))]

/-- Every compact C1 multiplier acts boundedly on directional fractional energy.
The coefficient bound and Lipschitz constant are derived from the compact C1
function. The estimate is uniform over all continuous input functions. -/
theorem compact_multiplier_fractional_energy (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (A : {a : E→ℂ // ContDiff ℝ 1 a ∧ HasCompactSupport a}) (v : E) :
    ∃ C : ℝ, 0<C ∧ ∀f : {g : E→ℂ // Continuous g},
      (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖A.1 x*f.1 x-A.1 (x+h • v)*f.1 (x+h • v)‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal C*((∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
          ENNReal.ofReal (‖f.1 x-f.1 (x+h • v)‖^2*h^(-(1+2*s.1))))+
            ∫⁻ x : E, ENNReal.ofReal (‖f.1 x‖^2)) := by
  obtain ⟨M0,hM0⟩ := A.2.2.exists_bound_of_continuous A.2.1.continuous
  let M := |M0|+1
  have hM (x : E) : ‖A.1 x‖ ≤ M := (hM0 x).trans (by dsimp [M]; linarith [le_abs_self M0])
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport A.2.2 A.2.1 (by norm_num)
  have hLn (x y : E) : ‖A.1 x-A.1 y‖ ≤ (L : ℝ)*‖x-y‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul x y
  let B := ∫h in Ioi (0 : ℝ), 2*multiplierRemainder s.1 M ((L : ℝ)*‖v‖) h
  have hB : 0 ≤ B := integral_nonneg (fun h =>
    mul_nonneg (by norm_num) (multiplier_remainder_nonneg _ _ _ _))
  refine ⟨2*M^2+B+1,by positivity,fun f => ?_⟩
  refine (multiplier_energy_bound s A.1 f.1 f.2 M L hM hLn v).trans ?_
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show 2*M^2 ≤ 2*M^2+B+1 by linarith)) _)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show B ≤ 2*M^2+B+1 by nlinarith [sq_nonneg M])) _)

/-- Compact C1 data in parameter and physical variables give one fractional
multiplier bound for every parameter value. This derives uniformity directly
from joint compactness, without an assumed family of analytic norm bounds. -/
theorem compact_parameter_multiplier_fractional_energy
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (A : {a : P×E→ℂ // ContDiff ℝ 1 a ∧ HasCompactSupport a}) (v : E) :
    ∃ C : ℝ, 0<C ∧ ∀(p : P) (f : {g : E→ℂ // Continuous g}),
      (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖A.1 (p,x)*f.1 x-A.1 (p,x+h • v)*f.1 (x+h • v)‖^2*h^(-(1+2*s.1)))) ≤
        ENNReal.ofReal C*((∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
          ENNReal.ofReal (‖f.1 x-f.1 (x+h • v)‖^2*h^(-(1+2*s.1))))+
            ∫⁻ x : E, ENNReal.ofReal (‖f.1 x‖^2)) := by
  obtain ⟨M0,hM0⟩ := A.2.2.exists_bound_of_continuous A.2.1.continuous
  let M := |M0|+1
  have hM (p : P) (x : E) : ‖A.1 (p,x)‖ ≤ M :=
    (hM0 (p,x)).trans (by dsimp [M]; linarith [le_abs_self M0])
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport A.2.2 A.2.1 (by norm_num)
  have hLn (p : P) (x y : E) : ‖A.1 (p,x)-A.1 (p,y)‖ ≤ (L : ℝ)*‖x-y‖ := by
    have he : ‖(p,x)-(p,y)‖=‖x-y‖ := by
      change max ‖p-p‖ ‖x-y‖=‖x-y‖
      rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
    simpa only [dist_eq_norm,he] using hL.dist_le_mul (p,x) (p,y)
  let B := ∫h in Ioi (0 : ℝ), 2*multiplierRemainder s.1 M ((L : ℝ)*‖v‖) h
  have hB : 0 ≤ B := integral_nonneg (fun h =>
    mul_nonneg (by norm_num) (multiplier_remainder_nonneg _ _ _ _))
  refine ⟨2*M^2+B+1,by positivity,fun p f => ?_⟩
  refine (multiplier_energy_bound s (fun x => A.1 (p,x)) f.1 f.2 M L (hM p) (hLn p) v).trans ?_
  rw [mul_add]
  exact add_le_add
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show 2*M^2 ≤ 2*M^2+B+1 by linarith)) _)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (show B ≤ 2*M^2+B+1 by nlinarith [sq_nonneg M])) _)

/-- Uniform compact-parameter multiplication has admitted fractional energy
on every Schwartz input, controlled by its physical mass and Fourier energy. -/
theorem compact_parameter_multiplier_fractional_schwartz
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : {r : ℝ // r∈Ioo (0 : ℝ) 1})
    (A : {a : P×E→ℂ // ContDiff ℝ 1 a ∧ HasCompactSupport a}) (v : E) :
    ∃ C : ℝ, 0<C ∧ ∀(p : P) (f : SchwartzMap E ℂ),
      let L := ∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
        ENNReal.ofReal (‖A.1 (p,x)*f x-A.1 (p,x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1)))
      L < (∞ : ℝ≥0∞) ∧ L ≤ ENNReal.ofReal C*
        (ENNReal.ofReal (∫ξ : E, |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2)+
          ENNReal.ofReal (∫x : E, ‖f x‖^2)) := by
  obtain ⟨B,hB,hBb⟩ := compact_parameter_multiplier_fractional_energy s A v
  obtain ⟨D,hD,hDb⟩ := directional_gagliardo_fourier (E := E) s
  refine ⟨B*(D+1),mul_pos hB (by linarith),fun p f => ?_⟩
  dsimp only
  have hb := hBb p ⟨f,f.continuous⟩
  have he := (hDb f v).2
  have him : Integrable (fun x : E => ‖f x‖^2) :=
    (f.memLp 2).integrable_norm_pow (by norm_num : 2≠0)
  have hmass := ofReal_integral_eq_lintegral_ofReal him
    (Eventually.of_forall (fun x : E => sq_nonneg ‖f x‖))
  simp only [he,←hmass] at hb
  have hbound : (∫⁻ h in Ioi (0 : ℝ), ∫⁻ x : E,
      ENNReal.ofReal (‖A.1 (p,x)*f x-A.1 (p,x+h • v)*f (x+h • v)‖^2*h^(-(1+2*s.1)))) ≤
      ENNReal.ofReal (B*(D+1))*
        (ENNReal.ofReal (∫ξ : E, |inner ℝ v ξ|^(2*s.1)*‖(𝓕 f) ξ‖^2)+
          ENNReal.ofReal (∫x : E, ‖f x‖^2)) := by
    refine hb.trans ?_
    rw [ENNReal.ofReal_mul hB.le,mul_assoc]
    apply mul_le_mul_right
    rw [mul_add]
    apply add_le_add
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith : D ≤ D+1)) _
    · calc ENNReal.ofReal (∫x : E, ‖f x‖^2)
          = 1*ENNReal.ofReal (∫x : E, ‖f x‖^2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_left (by
          simpa only [←ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ D+1 by linarith)) _
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,ENNReal.ofReal_lt_top⟩)),hbound⟩

end GaloisForLFunctions.HTGeometry
