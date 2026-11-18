import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.MoebiusInversionOfTheIntegerQuadrature
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SubcriticalMeanSquareOfTheIntegerQuadrature
import GaloisForLFunctions.RHTower.ZetaFisherVariance
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Absolute control of the moving small divisors

The range log d ≤ αt absorbs one factor of d from a stronger time tilt.
The remaining translates have summable L² costs for every fixed logarithmic
moment. The cutoff may therefore grow exponentially in time.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The positive uniform bound for all signed divisor coefficients of a fixed
logarithmic order. The sum is finite at each time because of the cutoff. -/
def smallDivisorEnvelope (Φ : ℝ → ℝ) (A α : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑' d : ℕ, if Real.log d ≤ α*t then (Real.log d)^k*|centredMultipleRow Φ A d t| else 0

private theorem memLp_tsum_of_summable_costs {u : ℕ → ℝ → ℝ} (hm : ∀ d, Measurable (u d))
    {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hs : Summable c) {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (hb : ∀ d, eLpNorm (u d) 2 volume ≤ ENNReal.ofReal (c d)*B) :
    MemLp (fun t => ∑' d, u d t) 2 := by
  let K := (∑' d, ENNReal.ofReal (c d))*B
  have hK : K < ⊤ := by
    dsimp only [K]
    rw [← ENNReal.ofReal_tsum_of_nonneg hc hs]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top
  have hsum : (∑' d, eLpNorm (u d) 2 volume) ≤ K := by
    apply (ENNReal.tsum_le_tsum hb).trans_eq
    exact ENNReal.tsum_mul_right
  have hconv := MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num)
    (fun d => (hm d).aestronglyMeasurable) (hsum.trans_lt hK).ne
  let S := fun N : ℕ => ∑ d ∈ Finset.range N, u d
  have hS (N : ℕ) : eLpNorm (S N) 2 volume ≤ K :=
    (eLpNorm_sum_le (fun d _ => (hm d).aestronglyMeasurable) (by norm_num)).trans
      ((ENNReal.sum_le_tsum (Finset.range N)).trans hsum)
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable,(Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := S)
    (Eventually.of_forall hS) (fun N => Finset.aestronglyMeasurable_sum _ fun d _ =>
      (hm d).aestronglyMeasurable) ?_).trans_lt hK⟩
  filter_upwards [hconv] with t ht
  simpa only [S,Finset.sum_apply] using ht.of_norm.hasSum.tendsto_sum_nat

/-- The absolute envelope of all centered multiples through exp(αt) has
finite exponentially weighted square integral below α+b = 1/2. -/
theorem criticalState_smallDivisorEnvelope {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {α b : ℝ} (hα : 0 < α) (hb0 : 0 ≤ b) (hroom : b+α < 1/2) (k : ℕ) :
    let A := ∫ u, Real.exp (-u/2)*Φ u
    MemLp (fun t => Real.exp (b*t)*smallDivisorEnvelope Φ A α k t) 2 := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let D := fun t : ℝ => integerReferenceWave Φ t-Real.exp (t/2)*A
  obtain ⟨β,hβ,hβ'⟩ := exists_between hroom
  let f := fun t : ℝ => Real.exp (β*t)*D t
  have hf : MemLp f 2 := criticalState_subcritical_integer_error hW ht hF hc he hC hb
    ((add_nonneg hb0 hα.le).trans hβ.le) hβ'
  have hN := continuous_integerReferenceWave hc hC hb
  have hD : Continuous D := by dsimp only [D]; fun_prop
  let L := fun d : ℕ => Real.log d
  let c := fun d : ℕ => (L d)^k*(d:ℝ)^(-(3/2-β))
  have hcost : Summable c := _root_.RHTower.summable_log_natCast_pow_mul_rpow_neg k
    (by linarith only [hβ'] : 1 < 3/2-β)
  have hlog (d : ℕ) : 0 ≤ L d := Real.log_natCast_nonneg d
  have hcn (d : ℕ) : 0 ≤ c d := mul_nonneg (pow_nonneg (hlog d) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let u := fun (d : ℕ) (t : ℝ) => if L d ≤ α*t then
    Real.exp (b*t)*(L d)^k*|centredMultipleRow Φ A d t| else 0
  have humeas (d : ℕ) : Measurable (u d) := by
    dsimp only [u,centredMultipleRow]
    exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) (by fun_prop) measurable_const
  have heq : (fun t : ℝ => Real.exp (b*t)*smallDivisorEnvelope Φ A α k t) = (fun t => ∑' d, u d t) := by
    funext t
    rw [smallDivisorEnvelope,← tsum_mul_left]
    apply tsum_congr fun d => ?_
    by_cases h : L d ≤ α*t
    · change Real.exp (b*t)*(if L d ≤ α*t then _ else 0) = u d t
      simp only [u,if_pos h,mul_assoc,L]
    · change Real.exp (b*t)*(if L d ≤ α*t then _ else 0) = u d t
      simp only [u,if_neg h,mul_zero]
  change MemLp (fun t => Real.exp (b*t)*smallDivisorEnvelope Φ A α k t) 2
  rw [heq]
  refine memLp_tsum_of_summable_costs humeas hcn hcost hf.2.ne (fun d => ?_)
  let g := fun t : ℝ => f (t-L d)
  have hp := measurePreserving_sub_right volume (L d)
  have heLp : eLpNorm g 2 volume=eLpNorm f 2 volume := eLpNorm_comp_measurePreserving (p := 2) (g := f) hf.1 hp
  have hcmp (t : ℝ) : ‖u d t‖ ≤ ‖(c d • g) t‖ := by
    rw [Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hcn d)]
    by_cases hs : L d ≤ α*t
    · rw [show u d t=Real.exp (b*t)*(L d)^k*|centredMultipleRow Φ A d t| from if_pos hs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg (hlog d) _)) (abs_nonneg _))]
      rcases Nat.eq_zero_or_pos d with rfl | hd
      · simp only [centredMultipleRow, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, abs_zero, mul_zero]
        exact mul_nonneg (hcn 0) (abs_nonneg _)
      have hd' : (0:ℝ) < d := by exact_mod_cast hd
      have ht0 : 0 ≤ t := nonneg_of_mul_nonneg_right ((hlog d).trans hs) hα
      have hlt : L d ≤ (β-b)*t := hs.trans (mul_le_mul_of_nonneg_right (by linarith only [hβ]) ht0)
      have hroot : (Real.sqrt d)⁻¹=Real.exp (-(L d/2)) := by rw [Real.exp_neg,Real.exp_half,Real.exp_log hd']
      have hratio : Real.exp (b*t)*Real.exp (-(L d/2)) ≤ (d:ℝ)^(-(3/2-β))*Real.exp (β*(t-L d)) := by
        rw [Real.rpow_def_of_pos hd',← Real.exp_add,← Real.exp_add]
        apply Real.exp_le_exp.2
        change b*t + -(L d/2) ≤ L d*(-(3/2-β))+β*(t-L d)
        linarith only [hlt]
      change Real.exp (b*t)*(L d)^k*|(Real.sqrt d)⁻¹*D (t-L d)| ≤
        ((L d)^k*(d:ℝ)^(-(3/2-β)))*|Real.exp (β*(t-L d))*D (t-L d)|
      rw [hroot,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
      calc _ = ((L d)^k*(Real.exp (b*t)*Real.exp (-(L d/2))))*|D (t-L d)| := by ring
        _ ≤ ((L d)^k*((d:ℝ)^(-(3/2-β))*Real.exp (β*(t-L d))))*|D (t-L d)| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (pow_nonneg (hlog d) _)) (abs_nonneg _)
        _ = _ := by ring
    · rw [show u d t=0 from if_neg hs,abs_zero]
      exact mul_nonneg (hcn d) (abs_nonneg _)
  apply (eLpNorm_mono hcmp).trans_eq
  rw [eLpNorm_const_smul,heLp,Real.enorm_eq_ofReal_abs,abs_of_nonneg (hcn d)]

#print axioms criticalState_smallDivisorEnvelope
end GaloisForLFunctions.ExclusionOfTheCriticalState
