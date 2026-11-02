import GaloisForLFunctions.ArithmeticIndexDescent.FullPrimeWindowTraceDecay
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPoleBound

/-!
# Uniform row tails for the full prime source

Exponential spatial decay pairs with the exact Haar mass at order a^(-3/2).
This gives summable squared rows after normalization by their Hilbert mass.
-/

noncomputable section
open MeasureTheory Finset Filter Topology Set
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The unsigned contracting moment has the same useful mass scale as the signed poles. -/
theorem integral_abs_haarProfile_exp_neg_le {a : ℕ} (ha : 1 ≤ a) :
    (∫ u, |haarProfile a u| * Real.exp (-u/2)) ≤
      2 * haarMass a / Real.sqrt ((2*a:ℕ):ℝ) := by
  have hi : Integrable (fun u => |haarProfile a u| * Real.exp (-u/2)) := by
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a)
        (show Continuous (fun u : ℝ => Real.exp (-u/2)) by fun_prop)).abs
  have hbound (u : ℝ) : |haarProfile a u| * Real.exp (-u/2) ≤
      |haarProfile a u| / Real.sqrt ((2*a:ℕ):ℝ) := by
    by_cases hu : u ∈ Ico (Real.log ((2*a:ℕ):ℝ)) (Real.log ((2*a+2:ℕ):ℝ))
    · have hp : (0:ℝ) < ((2*a:ℕ):ℝ) := by exact_mod_cast (show 0<2*a by omega)
      have he : Real.exp (-u/2) ≤ 1 / Real.sqrt ((2*a:ℕ):ℝ) := by
        calc
          _ ≤ Real.exp (-Real.log ((2*a:ℕ):ℝ)/2) :=
            Real.exp_le_exp.mpr (by linarith only [hu.1])
          _ = _ := by rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log hp,one_div]
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he (abs_nonneg _)
    · rw [haarProfile_zero_outside_pair ha hu,abs_zero,zero_mul,zero_div]
  calc
    _ ≤ ∫ u, |haarProfile a u| / Real.sqrt ((2*a:ℕ):ℝ) :=
      integral_mono hi ((integrable_haarProfile a).abs.div_const _) hbound
    _ = _ := by rw [integral_div,integral_abs_haarProfile ha]

/-- A spatially decaying trace pairs uniformly with each complete Haar detail. -/
theorem abs_integral_haarProfile_mul_le_of_exp_decay {a : ℕ} (ha : 1 ≤ a)
    {g : ℝ → ℝ} (hg : Measurable g) {L : ℝ} (hL : 0 ≤ L)
    (hb : ∀ u : ℝ, |g u| ≤ L * Real.exp (-u/2)) :
    |∫ u, haarProfile a u * g u| ≤
      L * (2 * haarMass a / Real.sqrt ((2*a:ℕ):ℝ)) := by
  have hi : Integrable (fun u => |haarProfile a u| * Real.exp (-u/2)) := by
    simpa only [abs_mul,abs_of_pos (Real.exp_pos _)] using
      (integrable_compact_bv_mul (haarProfile_bv a) (haarProfile_compact a)
        (show Continuous (fun u : ℝ => Real.exp (-u/2)) by fun_prop)).abs
  have hh (u : ℝ) : |haarProfile a u * g u| ≤
      L * (|haarProfile a u| * Real.exp (-u/2)) := by
    rw [abs_mul]
    calc
      _ ≤ |haarProfile a u| * (L * Real.exp (-u/2)) :=
        mul_le_mul_of_nonneg_left (hb u) (abs_nonneg _)
      _ = _ := by ring
  have hip : Integrable (fun u => haarProfile a u * g u) :=
    (hi.const_mul L).mono' ((measurable_haarProfile a).mul hg).aestronglyMeasurable
      (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using hh u)
  calc
    _ ≤ ∫ u, |haarProfile a u * g u| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun u => haarProfile a u * g u)
    _ ≤ ∫ u, L * (|haarProfile a u| * Real.exp (-u/2)) :=
      integral_mono hip.abs (hi.const_mul L) hh
    _ = L * ∫ u, |haarProfile a u| * Real.exp (-u/2) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_abs_haarProfile_exp_neg_le ha) hL

/-- The literal full prime window has a horizon-independent normalized row bound. -/
theorem abs_fullPrimeWindowCoupling_div_sqrt_le {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |fullPrimeWindowCoupling (haarProfile a) Y b / Real.sqrt Y| ≤
      (4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt ((2:ℝ)*b+2)) *
        (2 * haarMass a / Real.sqrt ((2*a:ℕ):ℝ)) := by
  have hm : Measurable (fun u => fullPrimeWindowTrace Y b u / Real.sqrt Y) :=
    (((measurable_headTrace ((b+1)*Y) b).comp (measurable_add_const _)).div_const _)
  have h := abs_integral_haarProfile_mul_le_of_exp_decay ha hm
    (show 0 ≤ 4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt ((2:ℝ)*b+2) by
      exact mul_nonneg (mul_nonneg (by norm_num)
        RHTower.FreeLagTrace.chebyshevConst_pos.le) (Real.sqrt_nonneg _))
    (fun u => by rw [abs_of_nonneg (fullPrimeWindowTrace_div_sqrt_le_exp hY hb u).1]
                 exact (fullPrimeWindowTrace_div_sqrt_le_exp hY hb u).2)
  rw [fullPrimeWindowCoupling,← integral_div]
  simpa only [mul_div_assoc] using h

#print axioms integral_abs_haarProfile_exp_neg_le
#print axioms abs_integral_haarProfile_mul_le_of_exp_decay
#print axioms abs_fullPrimeWindowCoupling_div_sqrt_le
end GaloisForLFunctions.ArithmeticIndexDescent
