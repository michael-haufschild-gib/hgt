import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Scaling
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.VacuumCalibration.Profile

/-! # Gibbs temperature shifts and a normalized vacuum reading -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace
open scoped ENNReal

/-- Probability of the empty configuration in the admitted band at inverse temperature s. -/
def vacuum (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) :=
  finiteSquarefreeBornWeight (added c d h) s 0

theorem vacuum_eq (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) :
    vacuum c d h s = (finiteSquarefreePartition (added c d h) s)⁻¹ := by
  simp [vacuum,finiteSquarefreeBornWeight_eq,finiteSquarefreeHamiltonian,squarefreeBitEnergy,one_div]

theorem vacuum_mem (c d : ℝ) (h : Ioi (0:ℝ)) (s : ℝ) : vacuum c d h s ∈ Icc (0:ℝ) 1 := by
  refine ⟨(weight_pos _ _ _).le,?_⟩
  calc vacuum c d h s ≤ ∑ x, finiteSquarefreeBornWeight (added c d h) s x :=
         Finset.single_le_sum (fun x _ => (weight_pos _ _ x).le) (Finset.mem_univ 0)
       _ = 1 := sum_squarefreeBitWeight ..

theorem vacuum_mono (c d : ℝ) (h : Ioi (0:ℝ)) : Monotone (vacuum c d h) := by
  intro s t hst
  rw [vacuum_eq,vacuum_eq]
  apply (inv_le_inv₀ (finiteSquarefreePartition_pos _ _) (finiteSquarefreePartition_pos _ _)).mpr
  apply Finset.prod_le_prod
  · intro p _
    exact (add_pos_of_pos_of_nonneg zero_lt_one (Real.exp_pos _).le).le
  · intro p _
    change 1+Real.exp (-t*Real.log (p.val:ℝ)) ≤ 1+Real.exp (-s*Real.log (p.val:ℝ))
    exact add_le_add_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hst)
      (Real.log_nonneg (by exact_mod_cast p.val.property.one_le)))) _

private theorem real_moment (S : Finset Nat.Primes) (h : Ioi (0:ℝ)) (r : ℝ) :
    packetMoment S h (r:ℂ) = ((finiteSquarefreePartition S (1+(1-r)*h.val)/
      finiteSquarefreePartition S (1+h.val):ℝ):ℂ) := by
  let s := 1+h.val
  let t := 1+(1-r)*h.val
  have he (x : SquarefreeBitConfig S) : finiteSquarefreeBornWeight S s x*Real.exp (r*packetEnergy S h x) =
      (finiteSquarefreePartition S t/finiteSquarefreePartition S s)*finiteSquarefreeBornWeight S t x := by
    rw [finiteSquarefreeBornWeight_eq,finiteSquarefreeBornWeight_eq,div_mul_eq_mul_div,← Real.exp_add]
    have harg : -s*finiteSquarefreeHamiltonian S x+r*packetEnergy S h x = -t*finiteSquarefreeHamiltonian S x := by
      dsimp [s,t,packetEnergy]
      ring
    rw [harg]
    field_simp [(finiteSquarefreePartition_pos S s).ne',(finiteSquarefreePartition_pos S t).ne']
  have hr : packetMoment S h (r:ℂ) = ((∑ x, finiteSquarefreeBornWeight S s x*Real.exp (r*packetEnergy S h x):ℝ):ℂ) := by
    simp only [packetMoment,s,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [hr,Finset.sum_congr rfl (fun x _ => he x),← Finset.mul_sum,
    show (∑ x, finiteSquarefreeBornWeight S t x) = 1 from sum_squarefreeBitWeight ..,mul_one]

theorem vacuum_tilt (c d : ℝ) (h : Ioi (0:ℝ)) (a : ℝ) :
    vacuum c d h (1+a*h.val) = vacuum c d h (1+h.val)/(packetMoment (added c d h) h ((1-a:ℝ):ℂ)).re := by
  rw [real_moment,Complex.ofReal_re,sub_sub_cancel,vacuum_eq,vacuum_eq]
  field_simp [(finiteSquarefreePartition_pos (added c d h) (1+h.val)).ne',
    (finiteSquarefreePartition_pos (added c d h) (1+a*h.val)).ne']

private def realExponent (c d r : ℝ) := ∫ v in c..d, density v*(Real.exp (r*v)-1)

private theorem real_cast (c d r : ℝ) : bandExponent c d (r:ℂ) = (realExponent c d r:ℂ) := by
  rw [bandExponent,realExponent,← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro v _
  push_cast
  rfl

private theorem mass_split {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    rate c d+realExponent c d (1-a) = mass c d a := by
  have hD : IntervalIntegrable density volume c d := intervalIntegrable_exp_neg_div hc hcd.le
  have hf : Continuous (fun v : ℝ => Real.exp ((1-a)*v)-1) := by fun_prop
  have hW : IntervalIntegrable (fun v => density v*(Real.exp ((1-a)*v)-1)) volume c d :=
    hD.mul_continuousOn hf.continuousOn
  rw [rate_integral hc hcd.le,← intervalIntegral.integral_of_le hcd.le,realExponent,
    ← intervalIntegral.integral_add hD hW,mass]
  apply intervalIntegral.integral_congr
  intro v _
  change Real.exp (-v)/v+(Real.exp (-v)/v)*(Real.exp ((1-a)*v)-1) = Real.exp (-a*v)/v
  rw [show -a*v = -v+(1-a)*v by ring,Real.exp_add]
  ring

/-- At drift a, a finite raw vacuum reading tends to exp(-∫ exp(-av)dv/v). -/
theorem drift_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (a : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => vacuum c d h (1+a*h.val)) criticalApproach (𝓝 (response c d a)) := by
  have hV := vacuum_limit hc hcd
  have hM := band_transform_limit hc hcd ((1-a:ℝ):ℂ)
  rw [increment_mgf,real_cast,← Complex.ofReal_exp] at hM
  have hR := (Complex.continuous_re.tendsto _).comp hM
  simp only [Function.comp_def,Complex.ofReal_re] at hR
  have H := hV.div hR (Real.exp_pos _).ne'
  have hv : Real.exp (expIntegralOne d-expIntegralOne c)/Real.exp (realExponent c d (1-a)) =
      response c d a := by
    rw [← Real.exp_sub,response,← mass_split hc hcd a]
    congr 1
    unfold rate
    ring
  rw [hv] at H
  apply H.congr
  intro h
  change ((packetLaw (added c d h) h : Measure ℝ) {0}).toReal / (packetMoment (added c d h) h ((1-a:ℝ):ℂ)).re = _
  rw [vacuum_tilt,packet_zero_mass,ENNReal.toReal_ofReal (inv_pos.mpr (finiteSquarefreePartition_pos _ _)).le,
    vacuum_eq]

#print axioms vacuum_eq
#print axioms vacuum_mem
#print axioms vacuum_mono
#print axioms vacuum_tilt
#print axioms drift_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.VacuumCalibration
