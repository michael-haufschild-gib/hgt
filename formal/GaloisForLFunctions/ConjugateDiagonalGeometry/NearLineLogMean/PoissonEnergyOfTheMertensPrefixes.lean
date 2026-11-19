import GaloisForLFunctions.ArithmeticInnerFunctionTheory.MollifiedLogDilationBridge
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.LongMoebiusSecondMomentRigidity
import GaloisForLFunctions.RHTower.MobiusReciprocalPrimitiveRatio

/-!
# A fixed Poisson measurement of long Möbius polynomials

At the critical line the Poisson weight of height one half gives the
matrix 1/max(m,n). Abel summation, as in Pain (arXiv:2603.08959, §4),
writes its energy as a positive sum of squared Mertens prefixes. A sharp
time cutoff through T costs only a factor of order T² against this single
weight. Sparse polynomial bounds on the finite arithmetic form therefore
constrain the zero width.
-/

noncomputable section
open Complex MeasureTheory Filter Finset
open scoped Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open _root_.RHTower ArithmeticInnerFunctionTheory
open GaloisForLFunctions.SquareRootThreshold (zetaZeroWidth zetaZeroWidth_nonneg)

def mertensPoissonGram (N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
    mobiusRealCoefficient m * mobiusRealCoefficient n / (max m n : ℝ)

private def criticalSection (N : ℕ) (t : ℝ) : ℂ :=
  edPoly mobCoeff (Icc 1 N) (((1/2:ℝ):ℂ) + t*I)

private theorem section_continuous (N : ℕ) : Continuous (criticalSection N) :=
  (differentiable_edPoly mobCoeff (fun _ hn => (mem_Icc.mp hn).1)).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => ((1/2:ℝ):ℂ) + t*I))

theorem mertens_gram_poisson_integral (N : ℕ) :
    mobiusWeightedLineEnergy (halfPlanePoissonKernel 1) (1/2) N = mertensPoissonGram N := by
  have he (t : ℝ) : realDirichletPoly N mobiusRealCoefficient ((1/2:ℂ)+t*I) = criticalSection N t := by
    simp [criticalSection, realDirichletPoly, edPoly, mobCoeff, mobiusRealCoefficient]
  have h := integral_dirichletPoly_norm_sq_poisson N mobiusRealCoefficient 0
  simpa only [Complex.ofReal_zero, add_zero, neg_zero, Real.rpow_zero, mul_one, he,
    mobiusWeightedLineEnergy, mertensPoissonGram, criticalSection] using h

private theorem prefix_complex (k : ℕ) :
    ((∑ m ∈ Icc 1 k, mobiusRealCoefficient m : ℝ) : ℂ) = mobiusMertensPartialSum k := by
  rw [←sum_range_mobCoeff_succ_eq_mobiusMertensPartialSum]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le k)), Complex.ofReal_add,
      sum_range_succ, ih]
    simp [mobiusRealCoefficient,mobCoeff]

/-- The fixed time-weighted measurement is an arithmetic sum of nonnegative
terms. Its first term is the terminal Mertens value. -/
theorem mertens_gram_prefix_squares {N : ℕ} (hN : 1 ≤ N) :
    mertensPoissonGram N = ‖mobiusMertensPartialSum N‖^2/(N:ℝ) +
      ∑ k ∈ Icc 1 (N-1), ((k:ℝ)⁻¹ - ((k:ℝ)+1)⁻¹) * ‖mobiusMertensPartialSum k‖^2 := by
  have hp (k : ℕ) : (∑ m ∈ Icc 1 k, mobiusRealCoefficient m)^2 = ‖mobiusMertensPartialSum k‖^2 := by
    rw [←prefix_complex, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [mertensPoissonGram, hp, Nat.cast_succ] using
    dirichletGram_eq_abel_squares hN mobiusRealCoefficient

private theorem kernel_half : halfPlanePoissonKernel 1 = HTGeometry.halfPlanePoisson (1/2) := by
  ext t
  rw [halfPlanePoissonKernel_one, HTGeometry.halfPlanePoisson]
  have h : 0 < (1/4:ℝ)+t^2 := by positivity
  norm_num only [show (1/2:ℝ)^2 = 1/4 by norm_num]
  field_simp [Real.pi_ne_zero, h.ne'] <;> ring

private theorem integrable_section (N : ℕ) :
    Integrable (fun t => ‖criticalSection N t‖^2 * halfPlanePoissonKernel 1 t) := by
  rw [kernel_half]
  have hp := HTGeometry.integrable_halfPlanePoisson (by norm_num : (0:ℝ) < 1/2)
  refine (hp.const_mul ((N:ℝ)^2)).mono' (((section_continuous N).norm.pow 2).aestronglyMeasurable.mul
    (HTGeometry.continuous_halfPlanePoisson (by norm_num : (0:ℝ)<1/2)).aestronglyMeasurable) ?_
  filter_upwards with t
  have hk := (HTGeometry.halfPlanePoisson_pos (by norm_num : (0:ℝ)<1/2) t).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hk)]
  apply mul_le_mul_of_nonneg_right _ hk
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_edPoly_mobCoeff_le N (by norm_num)) 2

/-- The Poisson weight dominates the sharp moment through height T after
multiplication by 4πT², uniformly in the polynomial length N. -/
theorem sharp_moebius_moment_le_mertens_gram (N : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (1:ℝ)..T, ‖edPoly moebiusMollifierCoeff (Icc 1 N)
      (((1/2:ℝ):ℂ)+t*I)‖^2) ≤ (4*Real.pi*T^2)*mertensPoissonGram N := by
  let C := 4*Real.pi*T^2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hk (t : ℝ) : 0 ≤ halfPlanePoissonKernel 1 t := (halfPlanePoissonKernel_pos (by norm_num) t).le
  have hl (t : ℝ) (ht : t ∈ Set.Ioc 1 T) : 1 ≤ C*halfPlanePoissonKernel 1 t := by
    have htpos := zero_lt_one.trans ht.1
    have hsq := pow_le_pow_left₀ htpos.le ht.2 2
    have hbig := one_le_pow₀ hT (n := 2)
    have hden : 0 < 1/4+t^2 := by positivity
    dsimp only [C]
    rw [halfPlanePoissonKernel_one]
    field_simp [Real.pi_pos.ne',hden.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hbig Real.pi_pos.le, Real.pi_pos]
  have hi := integrable_section N
  change (∫ t in (1:ℝ)..T, ‖criticalSection N t‖^2) ≤ C*mertensPoissonGram N
  rw [intervalIntegral.integral_of_le hT, ←mertens_gram_poisson_integral, mobiusWeightedLineEnergy]
  change _ ≤ C*(∫ t : ℝ, ‖criticalSection N t‖^2 * halfPlanePoissonKernel 1 t)
  calc _ ≤ ∫ t in Set.Ioc 1 T, C*(‖criticalSection N t‖^2 * halfPlanePoissonKernel 1 t) := by
         apply setIntegral_mono_on (section_continuous N |>.norm.pow 2 |>.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
           ((hi.const_mul C).integrableOn) measurableSet_Ioc
         intro t ht
         have hh := mul_le_mul_of_nonneg_left (hl t ht) (sq_nonneg ‖criticalSection N t‖)
         linarith only [hh]
       _ ≤ ∫ t : ℝ, C*(‖criticalSection N t‖^2 * halfPlanePoissonKernel 1 t) :=
         setIntegral_le_integral (hi.const_mul C) (Eventually.of_forall fun t => mul_nonneg hC
           (mul_nonneg (sq_nonneg _) (hk t)))
       _ = _ := integral_const_mul ..

/-- A bound for the arithmetic form at arbitrarily large integer lengths
transfers to the actual zero width. No height parameter enters the bound. -/
theorem width_le_of_cofinal_mertens_gram {b : ℝ} (hb : 0 ≤ b)
    (hgram : ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ N : ℕ in atTop, mertensPoissonGram N ≤ C*(N:ℝ)^(2*b)) :
    zetaZeroWidth ≤ b := by
  obtain ⟨C,hC,hN⟩ := hgram
  apply zetaZeroWidth_le_of_cofinal_pure_moebius_slope hb (by norm_num : (0:ℝ) ≤ 2)
  intro θ hθ
  refine ⟨θ,le_rfl,4*Real.pi*C,by positivity,?_⟩
  apply frequently_atTop.mpr
  intro A
  have hi : Tendsto (fun n : ℕ => (n:ℝ)^(1/θ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 1/θ)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hn,hlarge,hN₁⟩ := (hN.and_eventually ((hi.eventually_ge_atTop A).and
    (eventually_ge_atTop 1))).exists
  let T := (N:ℝ)^(1/θ)
  have hnr : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN₁
  have hT : 1 ≤ T := Real.one_le_rpow hnr (by positivity)
  have he : T^θ = (N:ℝ) := by
    dsimp only [T]; rw [←Real.rpow_mul (Nat.cast_nonneg _), one_div_mul_cancel hθ.ne', Real.rpow_one]
  refine ⟨T,hlarge,?_⟩
  rw [he,Nat.floor_natCast]
  have hh := (sharp_moebius_moment_le_mertens_gram N hT).trans
    (mul_le_mul_of_nonneg_left hn (by positivity))
  refine hh.trans_eq ?_
  rw [←he, ←Real.rpow_mul (zero_le_one.trans hT), Real.rpow_add (zero_lt_one.trans_le hT)]
  rw [Real.rpow_two, show θ * (2*b) = 2*b*θ by ring]
  ring

/-- Every power strictly above twice the zero width bounds the Poisson
measurement at every polynomial length. -/
theorem mertens_gram_upper_power {b : ℝ} (hb : zetaZeroWidth < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, mertensPoissonGram N ≤ B*(N:ℝ)^(2*b) := by
  have hb₀ := zetaZeroWidth_nonneg.trans_lt hb
  let a := 1/2+b
  have ha : zetaZeroAbscissa < a := by
    rw [GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half] at hb
    dsimp only [a]; linarith only [hb]
  have ha₀ : 0 ≤ a := by dsimp only [a]; linarith only [hb₀]
  obtain ⟨C,hC,h⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
  let A := (C*2^a)^2
  have hA : 0 ≤ A := sq_nonneg _
  have hterm (k : ℕ) (hk : 1 ≤ k) :
      ‖mobiusMertensPartialSum k‖^2/(k:ℝ) ≤ A*(k:ℝ)^(2*b) := by
    have hk₁ : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
    have hk₀ := zero_lt_one.trans_le hk₁
    have h₁ := h k
    rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa) = a by ring] at h₁
    have hpow := Real.rpow_le_rpow (show (0:ℝ) ≤ k+1 by positivity)
      (show (k:ℝ)+1 ≤ 2*k by linarith only [hk₁]) ha₀
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hk₀.le] at hpow
    have hh := pow_le_pow_left₀ (norm_nonneg _)
      (h₁.trans (mul_le_mul_of_nonneg_left hpow hC)) 2
    apply (div_le_iff₀ hk₀).mpr
    refine hh.trans_eq ?_
    rw [←mul_assoc C, mul_pow, ← Real.rpow_natCast ((k:ℝ)^a) 2, ← Real.rpow_mul hk₀.le,
      show a*((2:ℕ):ℝ) = 2*b+1 by dsimp only [a]; push_cast; ring, Real.rpow_add_one hk₀.ne']
    dsimp only [A]; ring
  have hrow (k : ℕ) (hk : 1 ≤ k) :
      ((k:ℝ)⁻¹-((k:ℝ)+1)⁻¹)*‖mobiusMertensPartialSum k‖^2 ≤ A*(k:ℝ)^(2*b-1) := by
    have hk₀ : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
    have hw : (k:ℝ)⁻¹-((k:ℝ)+1)⁻¹ ≤ (k:ℝ)⁻¹*(k:ℝ)⁻¹ := by
      have hk₁ : 0 < (k:ℝ)+1 := by positivity
      field_simp
      nlinarith only [hk₀]
    calc _ ≤ ((k:ℝ)⁻¹*(k:ℝ)⁻¹)*‖mobiusMertensPartialSum k‖^2 :=
           mul_le_mul_of_nonneg_right hw (sq_nonneg _)
         _ = (‖mobiusMertensPartialSum k‖^2/(k:ℝ))/(k:ℝ) := by ring
         _ ≤ (A*(k:ℝ)^(2*b))/(k:ℝ) := div_le_div_of_nonneg_right (hterm k hk) hk₀.le
         _ = _ := by rw [Real.rpow_sub_one hk₀.ne']; ring
  have hb₂ : 0 < 2*b := by positivity
  refine ⟨A+A*(1+1/(2*b)),by positivity,fun N => ?_⟩
  cases N with
  | zero => simp [mertensPoissonGram]
  | succ n =>
    have hs := sum_le_sum (s := Icc 1 n) fun i hi => hrow i (mem_Icc.mp hi).1
    rw [←mul_sum, _root_.RHTower.sum_Icc_eq_sum_range_shift] at hs
    simp only [Nat.cast_succ] at hs
    have hsum := hs.trans (mul_le_mul_of_nonneg_left
      (ArithmeticGaugeTheory.sum_rpow_sub_one_le hb₂ n) hA)
    rw [mertens_gram_prefix_squares (Nat.succ_pos n),Nat.succ_sub_one]
    have ht := hterm (n+1) (Nat.succ_pos n)
    rw [Nat.cast_succ] at ht ⊢
    linarith only [ht,hsum]

/-- Off the boundary, an arbitrarily late small Poisson measurement is
equivalent to the same exponent bounding every measurement. -/
theorem cofinal_mertens_gram_iff {b : ℝ} (hb : 0 ≤ b) (hoff : b ≠ zetaZeroWidth) :
    (∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ N : ℕ in atTop, mertensPoissonGram N ≤ C*(N:ℝ)^(2*b)) ↔
      zetaZeroWidth < b := by
  constructor
  · intro h
    exact lt_of_le_of_ne (width_le_of_cofinal_mertens_gram hb h) hoff.symm
  · intro h
    obtain ⟨B,hB,h⟩ := mertens_gram_upper_power h
    exact ⟨B,hB,(Eventually.of_forall h).frequently⟩

#print axioms mertens_gram_upper_power
#print axioms cofinal_mertens_gram_iff
#print axioms mertens_gram_prefix_squares
#print axioms sharp_moebius_moment_le_mertens_gram
#print axioms width_le_of_cofinal_mertens_gram

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
