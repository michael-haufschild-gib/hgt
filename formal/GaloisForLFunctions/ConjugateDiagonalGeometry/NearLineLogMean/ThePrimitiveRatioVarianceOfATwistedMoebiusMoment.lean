import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheTimeAveragedDyadicMaximumOfAPrimeTwist
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimitiveSpectrumOfTheMoebiusGram
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheConstantTermOfTheSquarefreeHarmonicDiagonal
import GaloisForLFunctions.ArithmeticCorrelationGeometry.SuccessorCorrelationsArePureGaugeCharge
import GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers

/-!
# The exact prime-twist variance of a time-averaged Möbius polynomial

At the Plancherel endpoint used by Wu and Yang (arXiv:2611.05863),
distinct reduced ratios are orthogonal characters of the prime torus.
All dilations of one ratio must be collected before squaring. The
variance pairs the squared Möbius atom with the squared Fourier
transform of the height measure at its log ratio.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
open Finset Complex MeasureTheory
open scoped ComplexConjugate
open _root_.RHTower _root_.RHTower.Sieve
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open MoebiusGram
noncomputable section

private abbrev amplitude (n : ℕ) : ℂ := coeff n

/-- The unitary time character in angular-frequency normalization. -/
def timePhase (u t : ℝ) := Complex.exp (((t*u:ℝ):ℂ)*Complex.I)

/-- Fourier transform of a finite measure on heights at an angular frequency. -/
def timeTransform (ν : Measure ℝ) (u : ℝ) := ∫ t, timePhase u t ∂ν

theorem norm_timePhase (u t : ℝ) : ‖timePhase u t‖=1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem integrable_timePhase (ν : Measure ℝ) [IsFiniteMeasure ν] (u : ℝ) :
    Integrable (timePhase u) ν := by
  apply Integrable.of_bound (f:=timePhase u) (by unfold timePhase; fun_prop) 1
  exact .of_forall fun t => (norm_timePhase u t).le

/-- Angular frequency of the directed off-diagonal pair. -/
abbrev ratioFrequency (m n : ℕ) := Real.log n-Real.log m
private abbrev charge (x : GaugeTorus) (m n : ℕ) := twist x m * conj (twist x n)

private theorem vertical_product (t : ℝ) (m n : ℕ) :
    verticalCoeff amplitude t m * conj (verticalCoeff amplitude t n) =
      ((coeff m*coeff n:ℝ):ℂ)*timePhase (ratioFrequency m n) t := by
  simp only [verticalCoeff,map_mul,amplitude,Complex.conj_ofReal,←Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_mul,timePhase]
  calc
    _ = ((coeff m:ℂ)*(coeff n:ℂ)) *
        (Complex.exp (((-t*Real.log m:ℝ):ℂ)*Complex.I) * Complex.exp (((-t*Real.log n:ℝ):ℂ)*(-Complex.I))) := by push_cast; ring
    _ = _ := by
      rw [←Complex.exp_add]
      congr 2
      push_cast
      ring

private def entry (x : GaugeTorus) (t : ℝ) (m n : ℕ) :=
  ((coeff m*coeff n:ℝ):ℂ) * (timePhase (ratioFrequency m n) t * charge x m n)

private theorem diagonal_entry (x : GaugeTorus) (t : ℝ) (n : ℕ) :
    entry x t n n = ((mobiusRealCoefficient n^2/n:ℝ):ℂ) := by
  simp only [entry,ratioFrequency,sub_self,timePhase,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,
    charge,twist_mul_conj_self,mul_one]
  rw [←sq,coeff,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem reduced_entries (x : GaugeTorus) (t : ℝ) (N : ℕ) :
    (∑ p ∈ offDiagPairs N, entry x t p.1 p.2) =
      ∑ q ∈ primitiveRatioPairs N, (atom N q.1 q.2:ℂ) *
        (timePhase (ratioFrequency q.1 q.2) t * charge x q.1 q.2) := by
  rw [sum_offDiagPairs_eq_sum_ratio]
  apply sum_congr rfl
  intro q hq
  obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp hq).1
  have ha' := (Nat.ne_of_gt (mem_Icc.mp ha).1)
  have hb' := (Nat.ne_of_gt (mem_Icc.mp hb).1)
  rw [←scale_correlation,Complex.ofReal_sum,sum_mul]
  apply sum_congr rfl
  intro d hd
  have hd' := Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hd).1).1
  have hg : ratioFrequency (d*q.1) (d*q.2) = ratioFrequency q.1 q.2 := by
    simp only [ratioFrequency,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr hd') (Nat.cast_ne_zero.mpr ha'),
      Real.log_mul (Nat.cast_ne_zero.mpr hd') (Nat.cast_ne_zero.mpr hb'),add_sub_add_left_eq_sub]
  have hc : charge x (d*q.1) (d*q.2) = charge x q.1 q.2 := by
    rw [charge,twist_mul x hd' ha',twist_mul x hd' hb',map_mul,mul_mul_mul_comm,twist_mul_conj_self,one_mul]
  rw [entry,hg,hc]

private theorem power_spectrum (x : GaugeTorus) (N : ℕ) (t : ℝ) :
    (power amplitude (Icc 1 N) x t : ℂ) = (harmonicMoebiusDiagonal N:ℂ) +
      ∑ q ∈ primitiveRatioPairs N, (atom N q.1 q.2:ℂ) *
        (timePhase (ratioFrequency q.1 q.2) t * charge x q.1 q.2) := by
  let s := Icc 1 N
  let a := verticalCoeff amplitude t
  have h := twistSum_mul_conj s s a a x
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq] at h
  change ((‖twistSum s a x‖^2:ℝ):ℂ) = _
  rw [h,←reduced_entries,sum_offDiagPairs_eq_double,harmonicMoebiusDiagonal,Nat.floor_natCast,
    Complex.ofReal_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have hrow : (∑ n ∈ s, a m * conj (a n) * charge x m n) = ∑ n ∈ s, entry x t m n :=
    sum_congr rfl fun n _ => by rw [vertical_product]; unfold entry; ring
  rw [hrow]
  change ∑ n ∈ s, entry x t m n =
    ((mobiusRealCoefficient m^2/m : ℝ) : ℂ) + ∑ n ∈ s.erase m, entry x t m n
  rw [←diagonal_entry x t m,add_comm,sum_erase_add _ _ hm]

/-- The sharp critical Möbius section measured against an arbitrary finite
height distribution, with its Haar mean removed. -/
def centeredMoment (ν : Measure ℝ) (N : ℕ) (x : GaugeTorus) :=
  moment ν amplitude (Icc 1 N) x - ν.real Set.univ*harmonicMoebiusDiagonal N

/-- The centered time measurement is the Fourier polynomial on reduced
rational characters with the windowed primitive atoms as coefficients. -/
theorem centered_moment_eq_pairForm (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) (x : GaugeTorus) :
    (centeredMoment ν N x:ℂ) = pairForm (primitiveRatioPairs N)
      (fun q => (atom N q.1 q.2:ℂ)*timeTransform ν (ratioFrequency q.1 q.2)) x := by
  let c (q : ℕ × ℕ) := (atom N q.1 q.2:ℂ)*charge x q.1 q.2
  have he (t : ℝ) : (power amplitude (Icc 1 N) x t:ℂ) = (harmonicMoebiusDiagonal N:ℂ) +
      ∑ q ∈ primitiveRatioPairs N, c q*timePhase (ratioFrequency q.1 q.2) t := by
    rw [power_spectrum]
    congr 1
    exact sum_congr rfl fun q _ => by dsimp only [c]; ring
  have hi (q : ℕ × ℕ) := (integrable_timePhase ν (ratioFrequency q.1 q.2)).const_mul (c q)
  rw [centeredMoment,Complex.ofReal_sub,moment,←integral_complex_ofReal]
  simp_rw [he]
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun q _ => hi q),integral_const,
    integral_finsetSum _ (fun q _ => hi q)]
  simp only [pairForm,integral_const_mul,timeTransform,Complex.real_smul,Complex.ofReal_mul,add_sub_cancel_left]
  exact sum_congr rfl fun q _ => by dsimp only [c,charge]; ring

/-- Time integration leaves a continuous observable on the prime torus. -/
theorem continuous_centeredMoment (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    Continuous (centeredMoment ν N) := by
  let w (q : ℕ × ℕ) := (atom N q.1 q.2:ℂ)*timeTransform ν (ratioFrequency q.1 q.2)
  have he : centeredMoment ν N = fun x => (pairForm (primitiveRatioPairs N) w x).re := by
    funext x
    exact congrArg Complex.re (centered_moment_eq_pairForm ν N x)
  rw [he]
  exact Complex.continuous_re.comp (continuous_pairForm _ w)

private theorem charge_parseval (N : ℕ) (w : ℕ × ℕ → ℂ) :
    ∫ x, ‖pairForm (primitiveRatioPairs N) w x‖^2 ∂gaugeHaar =
      ∑ q ∈ primitiveRatioPairs N, ‖w q‖^2 := by
  have hn (q : ℕ × ℕ) (hq : q ∈ primitiveRatioPairs N) : 0 < q.1 ∧ 0 < q.2 := by
    have h := mem_product.mp (mem_filter.mp hq).1
    exact ⟨(mem_Icc.mp h.1).1,(mem_Icc.mp h.2).1⟩
  have h := integral_pairForm_mul_conj (fun q hq => ⟨(hn q hq).1.ne',(hn q hq).2.ne'⟩) w
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,integral_complex_ofReal] at h
  apply Complex.ofReal_injective
  rw [h,Complex.ofReal_sum]
  apply sum_congr rfl
  intro q hq
  rw [sum_eq_single q,if_pos (Nat.mul_comm _ _),Complex.mul_conj,Complex.normSq_eq_norm_sq]
  · intro p hp hpq
    apply if_neg
    intro hcross
    obtain ⟨ha,hb⟩ := VerticalAP.eq_of_coprime_of_mul_eq (mem_filter.mp hq).2.1
      (mem_filter.mp hp).2.1 (hn p hp).1 hcross
    exact hpq (Prod.ext ha hb).symm
  · exact fun hnot => (hnot hq).elim

/-- Exact Haar variance for every finite height measure, including atomic
sampling and sharp or smoothed time intervals. -/
theorem integral_centered_moment_sq (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    ∫ x, (centeredMoment ν N x)^2 ∂gaugeHaar =
      ∑ q ∈ primitiveRatioPairs N, (atom N q.1 q.2)^2*‖timeTransform ν (ratioFrequency q.1 q.2)‖^2 := by
  have he (x : GaugeTorus) : (centeredMoment ν N x)^2 =
      ‖pairForm (primitiveRatioPairs N) (fun q => (atom N q.1 q.2:ℂ)*timeTransform ν (ratioFrequency q.1 q.2)) x‖^2 := by
    rw [←centered_moment_eq_pairForm,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  simp_rw [he]
  rw [charge_parseval]
  apply sum_congr rfl
  intro q _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]

#print axioms centered_moment_eq_pairForm
#print axioms integral_centered_moment_sq
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.PrimeTwistedMoments
