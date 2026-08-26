import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeReciprocalMass
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusOneRate

/-!
# Quantitative head bound in the smooth-prime coprime expansion

The modulus-one two-logarithm rate is summed over the part of the smooth-prime semigroup below a
cutoff.  Exact total mass gives the sharp squarefree factor `r / φ(r)`.
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset Filter
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

/-- Uniform logarithmic-square bound for the head of the smooth-prime coprime expansion. -/
theorem exists_abs_smoothPrimeCoprimeLogHead_log_sq_rate
    {r : ℕ} (hr : Squarefree r) :
    ∃ C K : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ K ∧
      ∀ (Y : ℝ) (D : ℕ), 1 ≤ D → K ≤ Y / (D : ℝ) →
        |∑ d ∈ primeSupportedIcc r D,
            (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| ≤
          C * ((r : ℝ) / (Nat.totient r : ℝ)) /
            (Real.log (Y / (D : ℝ))) ^ 2 := by
  classical
  obtain ⟨C, hC, hrate⟩ :=
    exists_abs_coprimeLogMoebius_one_sub_one_log_sq_rate
  rw [Filter.eventually_atTop] at hrate
  obtain ⟨K₀, hK₀⟩ := hrate
  refine ⟨C, max K₀ (Real.exp 1), hC, le_max_right _ _, ?_⟩
  intro Y D hD hscale
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  have hbaseExp : Real.exp 1 ≤ Y / (D : ℝ) :=
    le_trans (le_max_right K₀ (Real.exp 1)) hscale
  have hbasePos : 0 < Y / (D : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 1) hbaseExp
  have hYpos : 0 < Y := by
    rcases div_pos_iff.mp hbasePos with h | h
    · exact h.1
    · linarith [h.2, hDpos]
  have hlogBase : 1 ≤ Real.log (Y / (D : ℝ)) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hbaseExp
  have hlogBasePos : 0 < Real.log (Y / (D : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hlogBase
  have hpoint : ∀ d ∈ primeSupportedIcc r D,
      |(1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| ≤
        (C / (Real.log (Y / (D : ℝ))) ^ 2) * (1 / (d : ℝ)) := by
    intro d hd
    have hdmem : d ∈ Finset.Icc 1 D := (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
    have hdD : d ≤ D := (Finset.mem_Icc.mp hdmem).2
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
    have hquot : Y / (D : ℝ) ≤ Y / (d : ℝ) := by
      exact div_le_div_of_nonneg_left hYpos.le hdpos (by exact_mod_cast hdD)
    have hKarg : K₀ ≤ Y / (d : ℝ) :=
      le_trans (le_max_left K₀ (Real.exp 1)) (le_trans hscale hquot)
    have hrateArg := hK₀ (Y / (d : ℝ)) hKarg
    have hlogMono : Real.log (Y / (D : ℝ)) ≤ Real.log (Y / (d : ℝ)) :=
      Real.log_le_log hbasePos hquot
    have hlogArgPos : 0 < Real.log (Y / (d : ℝ)) :=
      lt_of_lt_of_le hlogBasePos hlogMono
    have hsquares : (Real.log (Y / (D : ℝ))) ^ 2 ≤
        (Real.log (Y / (d : ℝ))) ^ 2 := by nlinarith
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hdpos)]
    calc
      (1 / (d : ℝ)) * |coprimeLogMoebius 1 (Y / (d : ℝ)) - 1| ≤
          (1 / (d : ℝ)) * (C / (Real.log (Y / (d : ℝ))) ^ 2) :=
        mul_le_mul_of_nonneg_left hrateArg (one_div_nonneg.mpr hdpos.le)
      _ ≤ (1 / (d : ℝ)) * (C / (Real.log (Y / (D : ℝ))) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hdpos.le)
        exact div_le_div_of_nonneg_left hC (pow_pos hlogBasePos 2) hsquares
      _ = (C / (Real.log (Y / (D : ℝ))) ^ 2) * (1 / (d : ℝ)) := by ring
  have hsumMass :
      ∑ d ∈ primeSupportedIcc r D, (1 / (d : ℝ)) =
        ∑ d ∈ primeSupportedIcc r D, primeSupportedReciprocal r d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdmem : d ∈ Finset.Icc 1 D := (Finset.mem_filter.mp hd).1
    have hsupp : primeSupportedOn r d := (Finset.mem_filter.mp hd).2
    have hd0 : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp hdmem).1)
    rw [primeSupportedReciprocal_apply_of_supported hsupp,
      reciprocalNatArithmetic_apply hd0]
  have hmass :
      ∑ d ∈ primeSupportedIcc r D, (1 / (d : ℝ)) ≤
        ∑' d : ℕ, primeSupportedReciprocal r d := by
    rw [hsumMass]
    exact (summable_primeSupportedReciprocal
      (Nat.pos_of_ne_zero hr.ne_zero)).sum_le_tsum
        (primeSupportedIcc r D) (fun d _ => primeSupportedReciprocal_nonneg r d)
  have hfactor : 0 ≤ C / (Real.log (Y / (D : ℝ))) ^ 2 := by positivity
  calc
    |∑ d ∈ primeSupportedIcc r D,
        (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| ≤
        ∑ d ∈ primeSupportedIcc r D,
          |(1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ primeSupportedIcc r D,
        (C / (Real.log (Y / (D : ℝ))) ^ 2) * (1 / (d : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = (C / (Real.log (Y / (D : ℝ))) ^ 2) *
        ∑ d ∈ primeSupportedIcc r D, (1 / (d : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (C / (Real.log (Y / (D : ℝ))) ^ 2) *
        (∑' d : ℕ, primeSupportedReciprocal r d) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = C * ((r : ℝ) / (Nat.totient r : ℝ)) /
        (Real.log (Y / (D : ℝ))) ^ 2 := by
      rw [tsum_primeSupportedReciprocal_eq_totientRatio hr]
      ring

end

end RHTower.Sieve
