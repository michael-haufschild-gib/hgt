import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum.Calibration
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac

/-! # Reciprocal integer spectrum of the whole-gas detector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum

open Finset Filter MeasureTheory InverseSpectrum.ShellMixing

def weight (k : ℕ) := occupationWeight k^2

def spectrum : Measure ℝ := _root_.HTGeometry.countableWeightedDirac weight occupationWeight

theorem weight_pos (k : ℕ) : 0 < weight k := pow_pos (occupationWeight_pos k) 2

theorem moment_series (k : ℕ) :
    HasSum (fun i => weight i * occupationWeight i^k) (riemannZeta ((k+2:ℕ):ℂ)).re := by
  have greater : (1:ℝ)<((k+2:ℕ):ℝ) := by exact_mod_cast (show 1<k+2 by omega)
  let β : GibbsExponent := ⟨((k+2:ℕ):ℝ),zero_lt_one.trans greater⟩
  have hb : 1<β.val := greater
  have eqn (i : ℕ) : weight i * occupationWeight i^k = shellPower β i := by
    rw [←occupation_rpow_eq_shellPower]
    change occupationWeight i^2 * occupationWeight i^k = occupationWeight i^((k+2:ℕ):ℝ)
    rw [Real.rpow_natCast,←pow_add,Nat.add_comm 2 k]
  simpa only [β,Complex.ofReal_natCast] using (hasSum_shellPower hb).congr_fun eqn

theorem positive_moment (k : ℕ) : 0 < (riemannZeta ((k+2:ℕ):ℂ)).re := by
  have h := (moment_series k).summable.sum_le_tsum ({0}:Finset ℕ)
    (fun i _ => mul_nonneg (weight_pos i).le (pow_nonneg (occupationWeight_pos i).le k))
  rw [sum_singleton,(moment_series k).tsum_eq] at h
  exact (mul_pos (weight_pos 0) (pow_pos (occupationWeight_pos 0) k)).trans_le h

private theorem weight_summable : Summable weight := by
  simpa only [pow_zero,mul_one] using (moment_series 0).summable

instance : IsFiniteMeasure spectrum := ⟨by
  rw [spectrum,_root_.HTGeometry.countableWeightedDirac_univ_ofReal (fun k => (weight_pos k).le) weight_summable]
  exact ENNReal.ofReal_lt_top⟩

theorem carried : spectrum (Set.Icc (-1:ℝ) 1)ᶜ=0 := by
  have off (k : ℕ) : (Set.Icc (-1:ℝ) 1)ᶜ.indicator (1 : ℝ → ENNReal) (occupationWeight k)=0 := by
    apply Set.indicator_of_notMem
    intro h
    exact h ⟨(by linarith only [occupationWeight_pos k]),
      (occupationWeight_antitone (Nat.zero_le k)).trans_eq occupationWeight_zero⟩
  rw [spectrum,_root_.HTGeometry.countableWeightedDirac_apply _ _ measurableSet_Icc.compl]
  simp only [off,mul_zero,tsum_zero]

theorem integrable_moment (k : ℕ) : Integrable (fun x : ℝ => x^k) spectrum := by
  apply _root_.HTGeometry.integrable_countableWeightedDirac (fun i => (weight_pos i).le)
    ((continuous_id.pow k).aestronglyMeasurable)
  refine (moment_series k).summable.congr fun i => ?_
  change weight i * occupationWeight i^k = weight i * |occupationWeight i^k|
  rw [abs_of_nonneg (pow_nonneg (occupationWeight_pos i).le k)]

theorem moment (k : ℕ) : (∫ x,(x:ℝ)^k ∂spectrum)=(riemannZeta ((k+2:ℕ):ℂ)).re := by
  rw [spectrum,_root_.HTGeometry.integral_countableWeightedDirac (fun i => (weight_pos i).le) (integrable_moment k)]
  exact (moment_series k).tsum_eq

theorem atom (k : ℕ) : spectrum.real {occupationWeight k}=weight k :=
  _root_.HTGeometry.countableWeightedDirac_real_singleton weight occupationWeight_strictAnti.injective
    (fun i => (weight_pos i).le) k

theorem atoms (x : ℝ) : 0 < spectrum.real {x} ↔ ∃ k, x=occupationWeight k := by
  constructor
  · intro hx
    by_contra off
    have vanish (i : ℕ) : ({x} : Set ℝ).indicator (1 : ℝ → ENNReal) (occupationWeight i)=0 := by
      apply Set.indicator_of_notMem
      exact fun h => off ⟨i,(Set.mem_singleton_iff.mp h).symm⟩
    rw [Measure.real,spectrum,_root_.HTGeometry.countableWeightedDirac_apply _ _ (measurableSet_singleton x)] at hx
    simp only [vanish,mul_zero,tsum_zero,ENNReal.toReal_zero,lt_self_iff_false] at hx
  · rintro ⟨k,rfl⟩
    rw [atom]
    exact weight_pos k

#print axioms moment_series
#print axioms moment
#print axioms atom
#print axioms atoms

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Vacuum.WholeSpectrum
