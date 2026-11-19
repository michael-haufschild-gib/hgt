import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedIntegerWeightsBelowTheTestAbscissa
import GaloisForLFunctions.RHTower.VonMangoldtRpowTail
import GaloisForLFunctions.RHTower.MertensVonMangoldtEulerConstant
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The reciprocal term above the test abscissa

The linear part of the fractional kernel gives a signed reciprocal Mangoldt
tail. Its floor correction samples only the far left of the state's eighth
exponential square mass.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri

/-- Square norm of the exponentially weighted profile to the left of b. -/
def leftEighthNorm (Φ : ℝ → ℝ) (b : ℝ) : ℝ :=
  Real.sqrt (∫ v in Iic b, Φ v ^ 2 * Real.exp (-(8*v)))

/-- The left eighth exponential norm vanishes at the negative endpoint. -/
theorem leftEighthNorm_atBot {Φ : ℝ → ℝ}
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v))) :
    Tendsto (leftEighthNorm Φ) atBot (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := volume) (s := fun t : ℝ => Iic (-t))
    (fun _ => measurableSet_Iic) (fun _ _ hab => Iic_subset_Iic.2 (neg_le_neg hab))
    ⟨0,hi.integrableOn⟩
  have he : (⋂ t : ℝ, Iic (-t)) = (∅ : Set ℝ) := by
    ext y
    simp only [mem_iInter,mem_Iic,mem_empty_iff_false,iff_false,not_forall,not_le]
    exact ⟨1-y,by linarith⟩
  rw [he,Measure.restrict_empty,integral_zero_measure] at h
  change Tendsto (fun b : ℝ => Real.sqrt (∫ v in Iic b, Φ v ^ 2 * Real.exp (-(8*v)))) atBot (𝓝 0)
  simpa only [Function.comp_def,neg_neg,Real.sqrt_zero] using
    (h.comp tendsto_neg_atBot_atTop).sqrt

private theorem left_tilt_bound {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v))) (b : ℝ) :
    (∫ v in Iic b, |Φ v| * Real.exp (-v/2)) ≤ leftEighthNorm Φ b * Real.exp (7*b/2) := by
  let f := fun v : ℝ => |Φ v| * Real.exp (-4*v)
  let g := fun v : ℝ => Real.exp (7*v/2)
  have hf (v : ℝ) : f v ^ 2 = Φ v ^ 2 * Real.exp (-(8*v)) := by
    simp only [f,mul_pow,sq_abs,sq (Real.exp _),← Real.exp_add]
    congr 2; ring
  have hg (v : ℝ) : g v ^ 2 = Real.exp (7*v) := by
    dsimp only [g]; rw [sq,← Real.exp_add]; congr 1; ring
  have hfg (v : ℝ) : f v * g v = |Φ v| * Real.exp (-v/2) := by
    dsimp only [f,g]; rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hf2 : IntegrableOn (fun v => f v ^ 2) (Iic b) := by simpa only [hf] using hi.integrableOn
  have hg2 : IntegrableOn (fun v => g v ^ 2) (Iic b) := by
    simpa only [hg] using integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<7) b
  have h := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Iic b)) (f := f) (g := g)
    (hc.abs.mul (by fun_prop)).aestronglyMeasurable
    (by fun_prop : Continuous g).aestronglyMeasurable hf2 hg2
  simp only [hfg,hf,hg,integral_exp_mul_Iic (by norm_num : (0:ℝ)<7)] at h
  have hE : 0 ≤ ∫ v in Iic b, Φ v ^ 2 * Real.exp (-(8*v)) :=
    integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hsq : (leftEighthNorm Φ b * Real.exp (7*b/2)) ^ 2 =
      (∫ v in Iic b, Φ v ^ 2 * Real.exp (-(8*v))) * Real.exp (7*b) := by
    rw [mul_pow,leftEighthNorm,Real.sq_sqrt hE,show Real.exp (7*b/2)^2=Real.exp (7*b) from hg b]
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
  change _ ≤ (leftEighthNorm Φ b * Real.exp (7*b/2))^2
  rw [hsq]
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [Real.exp_pos (7*b)] :
    Real.exp (7*b)/7 ≤ Real.exp (7*b)) hE)

/-- The upper atom differs from its reciprocal main term only at particles
v ≤ T-p. The eighth exponential norm on that set gives a vanishing coefficient. -/
theorem testedIntegerWeight_upper_atom {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)))
    (ht : Integrable fun v => Real.exp (-v/2)*Φ v) (T p : ℝ) :
    |testedIntegerWeight Φ T p -
        (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2-p)| ≤
      |∫ v, Φ v| * leftEighthNorm Φ (T-p) * Real.exp (4*T-9*p/2) := by
  let b := T-p
  let y := Real.exp b
  let z := fun v : ℝ => y * Real.exp (-v)
  let f := fun v : ℝ => Real.exp (v/2)*Φ v*Int.fract (z v)
  let g := fun v : ℝ => y*(Real.exp (-v/2)*Φ v)
  have hz (v : ℝ) : 0 ≤ z v := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hle (v : ℝ) : Int.fract (z v) ≤ z v := by
    rw [Int.fract]; apply sub_le_self; exact_mod_cast (Int.floor_nonneg.mpr (hz v))
  have hlin (v : ℝ) : Real.exp (v/2)*Φ v*z v = g v := by
    have hx : Real.exp (v/2)*Real.exp (-v)=Real.exp (-v/2) := by
      rw [← Real.exp_add]; congr 1; ring
    dsimp only [z,g]; linear_combination y*Φ v*hx
  have hfa (v : ℝ) : |f v| ≤ |g v| := by
    rw [← hlin]; dsimp only [f]
    simp only [abs_mul,abs_of_nonneg (Int.fract_nonneg (z v)),abs_of_nonneg (hz v)]
    exact mul_le_mul_of_nonneg_left (hle v) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hgi : Integrable g := ht.const_mul _
  have hfm : Measurable f := ((by fun_prop : Continuous (fun v : ℝ => Real.exp (v/2)*Φ v)).measurable).mul
    (measurable_fract.comp (by fun_prop : Continuous z).measurable)
  have hfi := hgi.abs.mono' hfm.aestronglyMeasurable (Eventually.of_forall hfa)
  have heg (v : ℝ) (hb : b < v) : f v = g v := by
    have hz1 : z v < 1 := by
      dsimp only [z,y]; rw [← Real.exp_add,Real.exp_lt_one_iff]; linarith
    rw [← hlin v]; dsimp only [f]; rw [Int.fract_eq_self.mpr ⟨hz v,hz1⟩]
  have hdiff (v : ℝ) : |f v-g v| ≤ y*(|Φ v| *Real.exp (-v/2)) := by
    rw [← hlin v]; dsimp only [f]; rw [← mul_sub,abs_mul,abs_of_nonpos (sub_nonpos.mpr (hle v))]
    calc _ ≤ |Real.exp (v/2)*Φ v| * z v := mul_le_mul_of_nonneg_left
           (by linarith only [Int.fract_nonneg (z v)]) (abs_nonneg _)
         _ = |g v| := by rw [← hlin v,abs_mul (Real.exp (v/2)*Φ v),abs_of_nonneg (hz v)]
         _ = _ := by
           dsimp only [g]
           rw [abs_mul y,abs_mul (Real.exp (-v/2)),abs_of_pos (Real.exp_pos (-v/2)),
             show |y|=y from abs_of_pos (Real.exp_pos b)]; ring
  have habsi : Integrable (fun v : ℝ => |Φ v| *Real.exp (-v/2)) := by
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _),mul_comm] using ht.abs
  have hprice : |(∫ v, f v)-(∫ v, g v)| ≤ y*(leftEighthNorm Φ b*Real.exp (7*b/2)) := by
    rw [← integral_sub hfi hgi]
    calc _ ≤ ∫ v, |f v-g v| := by
           simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v => f v-g v)
         _ = ∫ v in Iic b, |f v-g v| := by
           symm
           apply setIntegral_eq_integral_of_forall_compl_eq_zero
           intro v hv
           rw [heg v (lt_of_not_ge hv),sub_self,abs_zero]
         _ ≤ ∫ v in Iic b, y*(|Φ v| *Real.exp (-v/2)) :=
           integral_mono (hfi.sub hgi).abs.integrableOn (habsi.const_mul y).integrableOn hdiff
         _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left
                       (left_tilt_bound hc hi b) (Real.exp_pos _).le
  let m := ∫ v, Φ v
  have hmain : Real.exp (-T/2)*y=Real.exp (T/2-p) := by
    dsimp only [y,b]; rw [← Real.exp_add]; congr 1; ring
  have hw : testedIntegerWeight Φ T p = Real.exp (-T/2)*m*(∫ v, f v) := by
    have h := scaled_testedIntegerWeight_eq_fractional_reading Φ T p
    change Real.exp (T/2)*testedIntegerWeight Φ T p=m*(∫ v, f v) at h
    rw [mul_assoc,← h,← mul_assoc,← Real.exp_add,show -T/2+T/2=0 by ring,Real.exp_zero,one_mul]
  have heq : testedIntegerWeight Φ T p-m*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2-p) =
      (Real.exp (-T/2)*m)*((∫ v, f v)-(∫ v, g v)) := by
    rw [hw,show (∫ v, g v) = y*(∫ v, Real.exp (-v/2)*Φ v) from integral_const_mul ..,← hmain]; ring
  have hex : Real.exp (-T/2)*y*Real.exp (7*b/2)=Real.exp (4*T-9*p/2) := by
    dsimp only [y,b]; rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
  change |testedIntegerWeight Φ T p-m*_ * _| ≤ _
  rw [heq,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left hprice (mul_nonneg (Real.exp_pos _).le (abs_nonneg m))).trans_eq
  rw [← hex]; ring

/-- The natural-order tail of the centred reciprocal Mangoldt measure. -/
def reciprocalPrimeRemainder (k : ℕ) : ℝ :=
  -2*Real.eulerMascheroniConstant - ∑ n ∈ Finset.Ioc 0 k, (vonMangoldt n-1)/(n:ℝ)

theorem tendsto_reciprocalPrimeBand (k : ℕ) :
    Tendsto (fun L => ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ))
      atTop (𝓝 (reciprocalPrimeRemainder k)) := by
  let c := fun n : ℕ => (vonMangoldt n-1)/(n:ℝ)
  have hψ := _root_.RHTower.tendsto_real_sum_vonMangoldt_div_sub_log.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hst := hψ.sub Real.tendsto_harmonic_sub_log
  have hp (L : ℕ) : (∑ n ∈ Finset.Icc 0 L, vonMangoldt n/(n:ℝ)) -
      (harmonic L : ℝ) = ∑ n ∈ Finset.Ioc 0 L, c n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le L),Finset.sum_cons]
    simp only [Nat.cast_zero,div_zero,zero_add,harmonic_eq_sum_Icc,Rat.cast_sum,
      Rat.cast_inv,Rat.cast_natCast]
    have hsets : Finset.Icc 1 L=Finset.Ioc 0 L := by ext n; simp; omega
    rw [hsets,← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by simp only [c,sub_div,one_div]
  have hpref : Tendsto (fun L => ∑ n ∈ Finset.Ioc 0 L, c n) atTop
      (𝓝 (-2*Real.eulerMascheroniConstant)) := by
    convert hst using 1
    · funext L
      simp only [Function.comp_apply,Nat.floor_natCast,sub_sub_sub_cancel_right,hp]
    · congr 1; ring
  apply (hpref.sub_const (∑ n ∈ Finset.Ioc 0 k, c n)).congr'
  filter_upwards [eventually_ge_atTop k] with L hL
  have h := Finset.sum_Ioc_consecutive c (Nat.zero_le k) hL
  linarith only [h]

private theorem leftEighthNorm_mono {Φ : ℝ → ℝ}
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v))) : Monotone (leftEighthNorm Φ) := by
  intro x y h
  apply Real.sqrt_le_sqrt
  exact integral_mono_measure (Measure.restrict_mono_set _ (Iic_subset_Iic.2 h))
    (Eventually.of_forall fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hi.integrableOn

private def upperTailConstant : ℝ :=
  2 ^ (7/2 : ℝ)*_root_.RHTower.vonMangoldtRpowTailConstant (7/2)+1

private theorem abs_prime_power_band (k L : ℕ) (hk : 1 ≤ k) :
    ∑ n ∈ Finset.Ioc k L, |vonMangoldt n-1| *(n:ℝ)^(-(9/2:ℝ)) ≤
      upperTailConstant*(k:ℝ)^(-(7/2:ℝ)) := by
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hfilter : (Finset.Icc 1 L).filter (fun n : ℕ => (k:ℝ)<n)=Finset.Ioc k L := by
    ext n
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc,Nat.cast_lt]
    omega
  have hm := _root_.RHTower.sum_vonMangoldt_rpow_tail_le (δ := 7/2) (by norm_num)
    (show (1:ℝ) ≤ k by exact_mod_cast hk) L
  rw [hfilter,show -(1+(7/2:ℝ)) = -(9/2:ℝ) by norm_num] at hm
  let g := fun x : ℝ => x ^ (-(9/2:ℝ))
  have ha : AntitoneOn g (Icc (k:ℝ) L) := fun x hx _ _ h =>
    Real.rpow_le_rpow_of_nonpos (hk0.trans_le hx.1) h (by norm_num)
  have ho := ha.sum_Ico_le_integral (integrableOn_Ioi_rpow_of_lt (by norm_num) hk0)
    (fun x hx => Real.rpow_nonneg (hk0.le.trans (le_of_lt hx)) _)
  change (∑ n ∈ Finset.Ico k L, g ↑(n+1)) ≤ _ at ho
  rw [Finset.sum_Ico_add' (fun n : ℕ => g n),Finset.Ico_add_one_add_one_eq_Ioc] at ho
  change (∑ n ∈ Finset.Ioc k L, (n:ℝ)^(-(9/2:ℝ))) ≤ ∫ x in Ioi (k:ℝ), x^(-(9/2:ℝ)) at ho
  rw [integral_Ioi_rpow_of_lt (by norm_num) hk0] at ho
  have hpow := Real.rpow_nonneg hk0.le (-(7/2:ℝ))
  calc _ ≤ ∑ n ∈ Finset.Ioc k L, (vonMangoldt n+1)*(n:ℝ)^(-(9/2:ℝ)) :=
           Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (by
             simpa only [abs_of_nonneg vonMangoldt_nonneg,abs_one] using abs_sub (vonMangoldt n) (1:ℝ))
             (Real.rpow_nonneg (Nat.cast_nonneg _) _)
       _ ≤ _ := by
           simp only [add_mul,one_mul,Finset.sum_add_distrib,upperTailConstant]
           rw [show -(9/2:ℝ)+1 = -(7/2:ℝ) by norm_num] at ho
           linarith only [hm,ho,hpow]

private def upperReciprocalCoefficient (Φ : ℝ → ℝ) (T : ℝ) : ℝ :=
  (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2)

private def upperWeightError (Φ : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  (vonMangoldt n-1)*(testedIntegerWeight Φ T (Real.log n)-upperReciprocalCoefficient Φ T/n)

private theorem abs_upperWeightError_band {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)))
    (ht : Integrable fun v => Real.exp (-v/2)*Φ v) (T : ℝ) {k : ℕ} (hk : 1 ≤ k) (L : ℕ) :
    (∑ n ∈ Finset.Ioc k L, |upperWeightError Φ T n|) ≤
      (|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T))*
        (upperTailConstant*(k:ℝ)^(-(7/2:ℝ))) := by
  let D := |∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  have hb (n : ℕ) (hn : n ∈ Finset.Ioc k L) : |upperWeightError Φ T n| ≤
      D*(|vonMangoldt n-1| *(n:ℝ)^(-(9/2:ℝ))) := by
    have hkn := (Finset.mem_Ioc.mp hn).1
    have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hkn)
    have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
    have hw := testedIntegerWeight_upper_atom hc hi ht T (Real.log n)
    have hmain : upperReciprocalCoefficient Φ T / n =
        (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2-Real.log n) := by
      rw [upperReciprocalCoefficient,Real.exp_sub,Real.exp_log hn0,mul_div_assoc]
    have hp : Real.exp (4*T-9*Real.log n/2)=Real.exp (4*T)*(n:ℝ)^(-(9/2:ℝ)) := by
      rw [Real.rpow_def_of_pos hn0,← Real.exp_add]; congr 1; ring
    have hnorm := leftEighthNorm_mono hi (sub_le_sub_left
      (Real.log_le_log hk0 (Nat.cast_le.mpr hkn.le)) T)
    rw [hp] at hw
    rw [upperWeightError,abs_mul,hmain]
    calc _ ≤ |vonMangoldt n-1| *((|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log n))*
           (Real.exp (4*T)*(n:ℝ)^(-(9/2:ℝ)))) := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
         _ ≤ |vonMangoldt n-1| *((|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k))*
           (Real.exp (4*T)*(n:ℝ)^(-(9/2:ℝ)))) := by
             exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
               (mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)) (mul_nonneg
                 (Real.exp_pos _).le (Real.rpow_nonneg hn0.le _))) (abs_nonneg _)
         _ = _ := by dsimp only [D]; ring
  calc _ ≤ ∑ n ∈ Finset.Ioc k L, D*(|vonMangoldt n-1| *(n:ℝ)^(-(9/2:ℝ))) := Finset.sum_le_sum hb
       _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (abs_prime_power_band k L hk) hD


/-- Finite endpoints retain the difference of the same two reciprocal tails. -/
theorem upper_finite_reciprocal_difference {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)))
    (ht : Integrable fun v => Real.exp (-v/2)*Φ v) (T : ℝ) {k L : ℕ} (hk : 1 ≤ k) (hkL : k ≤ L) :
    |(∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n))-
      (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2)*
        (reciprocalPrimeRemainder k-reciprocalPrimeRemainder L)| ≤
        (|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T))*
          ((2 ^ (7/2:ℝ)*_root_.RHTower.vonMangoldtRpowTailConstant (7/2)+1)*(k:ℝ)^(-(7/2:ℝ))) := by
  let c := fun n : ℕ => (vonMangoldt n-1)/(n:ℝ)
  have hR : reciprocalPrimeRemainder k-reciprocalPrimeRemainder L=∑ n ∈ Finset.Ioc k L, c n := by
    change (-2*Real.eulerMascheroniConstant-∑ n ∈ Finset.Ioc 0 k, c n)-
      (-2*Real.eulerMascheroniConstant-∑ n ∈ Finset.Ioc 0 L, c n)=_
    rw [← Finset.sum_Ioc_consecutive c (Nat.zero_le k) hkL]; ring
  rw [hR,Finset.mul_sum,← Finset.sum_sub_distrib]
  have heq (n : ℕ) : (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)-
      (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2)*c n=upperWeightError Φ T n := by
    dsimp only [upperWeightError,upperReciprocalCoefficient,c]; ring
  simp only [heq]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (abs_upperWeightError_band hc hi ht T hk L)

private theorem sum_cut_range (a : ℕ → ℝ) (k L : ℕ) :
    ∑ n ∈ Finset.range (L+1), (if k<n then a n else 0) = ∑ n ∈ Finset.Ioc k L, a n := by
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc]
  omega

/-- At any upper cutoff the fractional test has a naturally ordered infinite
signed tail. Its difference from the reciprocal Mangoldt term is absolutely
summable and is controlled by the left eighth exponential mass. -/
theorem criticalState_upper_reciprocal_tail {W₀ : ℝ} {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    (T : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ w : ℝ, Tendsto (fun L => ∑ n ∈ Finset.Ioc k L,
        (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) atTop (𝓝 w) ∧
      |w-(∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*Real.exp (T/2)*reciprocalPrimeRemainder k| ≤
        (|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T))*
          ((2 ^ (7/2:ℝ)*_root_.RHTower.vonMangoldtRpowTailConstant (7/2)+1)*(k:ℝ)^(-(7/2:ℝ))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)) :=
    hd.exponential.congr (he.mono fun v hv => congrArg (fun x : ℝ => x^2*Real.exp (-(8*v))) hv)
  have ht : Integrable fun v => Real.exp (-v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hd (by norm_num : (-4:ℝ)< -1/2)).congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]; congr 2; ring
  let a := fun n : ℕ => if k<n then upperWeightError Φ T n else 0
  let B := (|∫ v, Φ v| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T))*
    (upperTailConstant*(k:ℝ)^(-(7/2:ℝ)))
  have hb := abs_upperWeightError_band hc hi ht T hk
  have hnorm (n : ℕ) : ‖a n‖ = if k<n then |upperWeightError Φ T n| else 0 := by
    by_cases h : k<n <;> simp [a,h,Real.norm_eq_abs]
  have hs : Summable a := by
    apply Summable.of_norm
    apply summable_of_sum_range_le (c := B) (fun _ => norm_nonneg _)
    intro L
    cases L with
    | zero => simpa [B] using hb 0
    | succ L => simpa only [Nat.succ_eq_add_one,hnorm,sum_cut_range] using (show
        ∑ n ∈ Finset.Ioc k L, |upperWeightError Φ T n| ≤ B from hb L)
  have herr := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun L => ∑ n ∈ Finset.Ioc k L, upperWeightError Φ T n)
      atTop (𝓝 (∑' n, a n)) := by
    apply herr.congr
    intro L
    exact sum_cut_range (upperWeightError Φ T) k L
  let C := upperReciprocalCoefficient Φ T
  refine ⟨(∑' n, a n)+C*reciprocalPrimeRemainder k,?_,?_⟩
  · apply (hlim.add ((tendsto_reciprocalPrimeBand k).const_mul C)).congr
    intro L
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [upperWeightError,C]; ring
  · change |(∑' n, a n)+C*reciprocalPrimeRemainder k-C*reciprocalPrimeRemainder k| ≤ B
    rw [add_sub_cancel_right]
    apply le_of_tendsto hlim.abs
    exact Eventually.of_forall fun L => (Finset.abs_sum_le_sum_abs _ _).trans (hb L)

/-- With X = k^(7/8), the entire signed upper tail of the original whole
weights is its reciprocal term plus o(1), including the growing lower endpoint. -/
theorem riemannHypothesis_or_upper_reciprocal_asymptotic : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (w : ℕ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ k : ℕ, 1 ≤ k → Tendsto (fun L => ∑ n ∈ Finset.Ioc k L,
        (vonMangoldt n-1)*testedIntegerWeight Φ ((7/8)*Real.log k) (Real.log n)) atTop (𝓝 (w k))) ∧
      Tendsto (fun k : ℕ => w k-(∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)*
        (k:ℝ)^(7/16:ℝ)*reciprocalPrimeRemainder k) atTop (𝓝 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  obtain ⟨_,_,Φ,hc,he,_⟩ := criticalState_exists_continuous_representative hW ht hF
  let T := fun k : ℕ => (7/8)*Real.log k
  let C := (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)
  let cost := fun k : ℕ => (|∫ v, Φ v| *leftEighthNorm Φ (T k-Real.log k)*Real.exp (4*T k))*
    (upperTailConstant*(k:ℝ)^(-(7/2:ℝ)))
  have hw (k : ℕ) : ∃ w : ℝ, 1 ≤ k → Tendsto (fun L => ∑ n ∈ Finset.Ioc k L,
      (vonMangoldt n-1)*testedIntegerWeight Φ (T k) (Real.log n)) atTop (𝓝 w) ∧
      |w-C*Real.exp (T k/2)*reciprocalPrimeRemainder k| ≤ cost k := by
    by_cases hk : 1 ≤ k
    · obtain ⟨w,hw⟩ := criticalState_upper_reciprocal_tail hF hc he (T k) hk
      exact ⟨w,fun _ => hw⟩
    · exact ⟨0,fun hk' => (hk hk').elim⟩
  choose w hw using hw
  refine Or.inr ⟨W₀,F,Φ,w,hW,ht,hF,hc,he,fun k hk => (hw k hk).1,?_⟩
  have hi : Integrable fun v => Φ v ^ 2 * Real.exp (-(8*v)) :=
    (criticalHalfLineEnergyDomain_of_groundState hF).exponential.congr (he.mono fun v hv => congrArg (fun x : ℝ => x^2*Real.exp (-(8*v))) hv)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hleft : Tendsto (fun k : ℕ => T k-Real.log k) atTop atBot := by
    apply (hlog.const_mul_atTop_of_neg (by norm_num : (-1/8:ℝ)<0)).congr
    intro k; dsimp only [Function.comp_apply,T]; ring
  have hlim := ((leftEighthNorm_atBot hi).comp hleft).const_mul (|∫ v, Φ v| *upperTailConstant)
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hp : Real.exp (4*T k)*(k:ℝ)^(-(7/2:ℝ))=1 := by
    rw [Real.rpow_def_of_pos hk0,← Real.exp_add,show 4*T k + Real.log k * -(7/2:ℝ)=0 by dsimp [T]; ring,
      Real.exp_zero]
  have hq : (k:ℝ)^(7/16:ℝ)=Real.exp (T k/2) := by
    rw [Real.rpow_def_of_pos hk0]; congr 1; dsimp [T]; ring
  rw [Real.norm_eq_abs,hq]
  apply (hw k hk).2.trans_eq
  dsimp only [cost,Function.comp_apply]
  linear_combination (|∫ v, Φ v| *leftEighthNorm Φ (T k-Real.log k)*upperTailConstant)*hp

#print axioms tendsto_reciprocalPrimeBand
#print axioms criticalState_upper_reciprocal_tail
#print axioms riemannHypothesis_or_upper_reciprocal_asymptotic
end GaloisForLFunctions.ExclusionOfTheCriticalState
