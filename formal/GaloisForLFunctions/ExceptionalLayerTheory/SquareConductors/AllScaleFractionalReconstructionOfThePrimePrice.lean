import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGreenSeriesOfThePrimeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FractionalDiscrepancyAtThePrimeMidpoint

/-!
# Recovering centered prime mass from fractional fields at all scales

The fractional inversion at real thresholds counts the actual integer
atoms. Its centering is therefore θ(x)−⌊x⌋. The floor correction has
geometric terminal decay. The Green reconstruction allows a different
fractional order at each depth and each observation scale.
-/

noncomputable section
open Finset Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
open GaloisForLFunctions.ExclusionOfTheCriticalState (ordinaryPrimeExcessCoeff)
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def discretePrimeExcess (x : ℝ) := Chebyshev.theta x-(⌊x⌋₊:ℝ)

/-- Signed fractional test at real cutoffs a and b, using every integer
atom in (a,c], including composites of weight −1. -/
def realPrimeIntervalProbe (a b c β : ℝ) : ℝ :=
  ∫ t, (cutPower (-β) (t-a)-2*cutPower (-β) (t-b))*
    field (Ioc ⌊a⌋₊ ⌊c⌋₊) Nat.cast ordinaryPrimeExcessCoeff (β-1) t

private theorem sum_prime_excess (a b : ℝ) (hab : a ≤ b) :
    (∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, ordinaryPrimeExcessCoeff p)=discretePrimeExcess b-discretePrimeExcess a := by
  have prefix (y : ℝ) : (∑ p ∈ Ioc 0 ⌊y⌋₊, ordinaryPrimeExcessCoeff p)=discretePrimeExcess y := by
    simp only [ordinaryPrimeExcessCoeff,discretePrimeExcess,Chebyshev.theta,sum_sub_distrib,
      sum_filter,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
  have h := sum_Ioc_consecutive ordinaryPrimeExcessCoeff (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
  rw [prefix,prefix] at h
  linarith only [h]

theorem real_prime_interval_inversion {a b c β : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hβ : β ∈ Set.Ioo (0:ℝ) 1) :
    realPrimeIntervalProbe a b c β=ProbabilityTheory.beta (1-β) β*
      (2*discretePrimeExcess b-discretePrimeExcess a-discretePrimeExcess c) := by
  let S := Ioc ⌊a⌋₊ ⌊c⌋₊
  let f := field S Nat.cast ordinaryPrimeExcessCoeff (β-1)
  have he (y : ℝ) (hy : a ≤ y) :
      (∫ t, cutPower (-β) (t-y)*f t)=ProbabilityTheory.beta (1-β) β*
        ∑ i ∈ Ioc ⌊y⌋₊ ⌊c⌋₊, ordinaryPrimeExcessCoeff i := by
    have hfilter : S.filter (fun i => y < (i:ℝ))=Ioc ⌊y⌋₊ ⌊c⌋₊ := by
      ext i
      simp only [S,mem_filter,mem_Ioc,←Nat.floor_lt (ha.trans hy)]
      have hA := Nat.floor_mono hy
      omega
    simpa only [←sum_filter,hfilter,f] using complementary_tail S Nat.cast ordinaryPrimeExcessCoeff hβ y
  have hi (y : ℝ) : Integrable (fun t => cutPower (-β) (t-y)*f t) := by
    simpa only [f,show 1-β-1= -β by ring] using
      integrable_pairing S Nat.cast ordinaryPrimeExcessCoeff (sub_pos.mpr hβ.2) hβ.1 y
  change (∫ t, (cutPower (-β) (t-a)-2*cutPower (-β) (t-b))*f t)=_
  simp only [sub_mul,mul_assoc]
  rw [integral_sub (hi a) ((hi b).const_mul 2),integral_const_mul,he a le_rfl,he b hab,
    sum_prime_excess a c (hab.trans hbc),sum_prime_excess b c hbc]
  ring

private def floorError (t : ℝ) := ((⌊Real.exp t⌋₊:ℝ)-Real.exp t)/Real.exp t

private theorem floor_error_bound (t : ℝ) : |floorError t| ≤ 1*Real.exp (-t/2) := by
  have he := Real.exp_pos t
  rw [floorError,abs_div,abs_of_pos he,abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le he.le)),neg_sub,one_mul]
  rcases le_total t 0 with ht | ht
  · apply le_trans ((div_le_one he).mpr (sub_le_self _ (Nat.cast_nonneg _)))
    exact Real.one_le_exp_iff.mpr (by linarith only [ht])
  · have h := Nat.lt_floor_add_one (Real.exp t)
    calc (Real.exp t-(⌊Real.exp t⌋₊:ℝ))/Real.exp t ≤ 1/Real.exp t :=
          div_le_div_of_nonneg_right (by linarith only [h]) he.le
      _ = Real.exp (-t) := by rw [Real.exp_neg,one_div]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [ht])

private def discreteLogPrice (t : ℝ) := discretePrimeExcess (Real.exp t)/Real.exp t

private theorem discrete_log_terminal (t : ℝ) :
    Summable (fun n => midpointLogWalk n (fun u => |discreteLogPrice u|) t) := by
  have hf : Summable (fun n => midpointLogWalk n (fun u => |floorError u|) t) := by
    simpa only [pow_zero,one_mul] using half_power_terminal_moments floorError floor_error_bound 0 t
  have he : Summable (fun n => midpointLogWalk n (fun u => |normalizedPrimeError u|) t) := by
    simpa only [pow_zero,one_mul] using all_prime_midpoint_terminal_moments 0 t
  have hprice (x : ℝ) : discreteLogPrice x=normalizedPrimeError x-floorError x := by
    unfold discreteLogPrice discretePrimeExcess normalizedPrimeError floorError
    ring
  have hbound (x : ℝ) : |discreteLogPrice x| ≤ |normalizedPrimeError x|+|floorError x| := by
    rw [hprice]
    exact abs_sub _ _
  apply (he.add hf).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (midpointLogWalk_abs_nonneg n discreteLogPrice t)]
  exact midpointLogWalk_le_add hbound n t

/-- Beta-normalization exactly removes the chosen fractional order from
each local price. -/
def normalizedFractionalProbe (β t : ℝ) := realPrimeIntervalProbe (Real.exp t*(2/3)) (Real.exp t)
  (Real.exp t*(4/3)) β/(ProbabilityTheory.beta (1-β) β*(2*Real.exp t))

private theorem probe_defect {β : ℝ} (hb : β ∈ Set.Ioo (0:ℝ) 1) (t : ℝ) :
    normalizedFractionalProbe β t=logWalkDefect discreteLogPrice t := by
  have ht := Real.exp_pos t
  have hB := ProbabilityTheory.beta_pos (sub_pos.mpr hb.2) hb.1
  rw [normalizedFractionalProbe,real_prime_interval_inversion (by positivity)
    (by linarith only [ht] : Real.exp t*(2/3) ≤ Real.exp t)
    (by linarith only [ht] : Real.exp t ≤ Real.exp t*(4/3)) hb,logWalkDefect,midpointLogWalk_one]
  simp only [discreteLogPrice,Real.exp_add,Real.exp_log (by norm_num : 0<(2/3:ℝ)),
    Real.exp_log (by norm_num : 0<(4/3:ℝ))]
  field_simp [hB.ne',ht.ne'] <;> ring

/-- The order may vary by depth and scale, arbitrarily close to either
endpoint. Every such family reconstructs the same centered prime mass. -/
theorem variable_order_prime_green_series (order : ℕ → ℝ → Set.Ioo (0:ℝ) 1) (t : ℝ) :
    HasSum (fun n => midpointLogWalk n (fun u => normalizedFractionalProbe (order n u) u) t)
      (discretePrimeExcess (Real.exp t)/Real.exp t) := by
  have he (n : ℕ) : (fun u => normalizedFractionalProbe (order n u) u)=logWalkDefect discreteLogPrice :=
    funext fun u => probe_defect (order n u).2 u
  simp_rw [he]
  exact midpoint_green_of_terminal discreteLogPrice t (discrete_log_terminal t)

#print axioms real_prime_interval_inversion
#print axioms variable_order_prime_green_series

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
