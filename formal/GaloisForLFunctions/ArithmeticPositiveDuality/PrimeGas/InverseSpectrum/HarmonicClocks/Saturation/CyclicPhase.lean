import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.PhaseLaw
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # The discrete extremal law on a rotation cycle -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open MeasureTheory
open scoped ENNReal

/-- Positive unit rotation through one r-th of a turn. -/
def clockRoot (r : ℕ+) := Circle.exp (2*Real.pi/(r.val:ℝ))

theorem clockRoot_primitive (r : ℕ+) : IsPrimitiveRoot (clockRoot r:ℂ) r.val := by
  have h : (((2*Real.pi/(r.val:ℝ)):ℝ):ℂ)*Complex.I = 2*(Real.pi:ℂ)*Complex.I/(r.val:ℂ) := by
    push_cast
    ring
  rw [clockRoot,Circle.coe_exp,h]
  exact Complex.isPrimitiveRoot_exp _ r.ne_zero

/-- Uniform mass contributed by the cyclic part to each root. -/
def rootShare (r : ℕ+) (δ : ℝ) := (1-δ)/(r.val:ℝ)

private theorem share_total (r : ℕ+) (δ : ℝ) : (r.val:ℝ)*rootShare r δ = 1-δ := by
  unfold rootShare
  field_simp [show (r.val:ℝ) ≠ 0 by exact_mod_cast r.ne_zero]

private def rootWeight (r : ℕ+) (δ : ℝ) (k : ℕ) := rootShare r δ+(if k = 0 then δ else 0)

private theorem rootWeight_nonneg (r : ℕ+) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (k : ℕ) :
    0 ≤ rootWeight r δ k := by
  unfold rootWeight rootShare
  exact add_nonneg (div_nonneg (sub_nonneg.mpr h₁) (Nat.cast_nonneg _)) (by split <;> positivity)

private theorem rootWeight_sum (r : ℕ+) (δ : ℝ) : ∑ k ∈ Finset.range r.val, rootWeight r δ k = 1 := by
  simp only [rootWeight,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,share_total,
    Finset.sum_ite_eq',if_pos (Finset.mem_range.mpr r.pos),sub_add_cancel]

/-- Mass δ at the trivial phase plus mass 1−δ uniformly distributed around the cycle. -/
def cyclicPhaseLaw (r : ℕ+) (δ : ℝ) (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) : ProbabilityMeasure Circle :=
  ⟨∑ k ∈ Finset.range r.val, ENNReal.ofReal (rootWeight r δ k) • Measure.dirac (clockRoot r^k),⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one,
      ← ENNReal.ofReal_sum_of_nonneg (fun k _ => rootWeight_nonneg r h₀ h₁ k),rootWeight_sum,ENNReal.ofReal_one]⟩⟩

theorem cyclicPhaseLaw_integral (r : ℕ+) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (f : Circle → ℂ) :
    (∫ z, f z ∂(cyclicPhaseLaw r δ h₀ h₁ : Measure Circle)) =
      (δ:ℂ)*f 1+(rootShare r δ:ℂ)*∑ k ∈ Finset.range r.val, f (clockRoot r^k) := by
  change (∫ z, f z ∂(∑ k ∈ Finset.range r.val, ENNReal.ofReal (rootWeight r δ k) •
    Measure.dirac (clockRoot r^k))) = _
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  have hw (k : ℕ) : (ENNReal.ofReal (rootWeight r δ k)).toReal = rootWeight r δ k :=
    ENNReal.toReal_ofReal (rootWeight_nonneg r h₀ h₁ k)
  simp only [integral_smul_measure,integral_dirac,hw,Complex.real_smul]
  simp only [rootWeight,Complex.ofReal_add,add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  have he (k : ℕ) : ((if k = 0 then δ else 0 : ℝ):ℂ)*f (clockRoot r^k) =
      if k = 0 then (δ:ℂ)*f 1 else 0 := by
    by_cases hk : k = 0 <;> simp [hk]
  rw [Finset.sum_congr rfl (fun k _ => he k),Finset.sum_ite_eq',if_pos (Finset.mem_range.mpr r.pos),add_comm]

theorem cyclicPhaseLaw_moment (r : ℕ+) {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1) (k : ℕ) :
    (∫ z : Circle, (z:ℂ)^k ∂(cyclicPhaseLaw r δ h₀ h₁ : Measure Circle)) =
      if r.val ∣ k then (1:ℂ) else (δ:ℂ) := by
  have hr := clockRoot_primitive r
  rw [cyclicPhaseLaw_integral]
  simp only [Circle.coe_one,one_pow,mul_one,Circle.coe_pow]
  have he (l : ℕ) : ((clockRoot r:ℂ)^l)^k = ((clockRoot r:ℂ)^k)^l := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  rw [Finset.sum_congr rfl (fun l _ => he l)]
  by_cases hk : r.val ∣ k
  · rw [if_pos hk,(hr.pow_eq_one_iff_dvd k).mpr hk]
    simp only [one_pow,Finset.sum_const,Finset.card_range,nsmul_one]
    rw [mul_comm,← Complex.ofReal_natCast,← Complex.ofReal_mul,share_total,← Complex.ofReal_add]
    simp
  · have hn : (clockRoot r:ℂ)^k ≠ 1 := fun h => hk ((hr.pow_eq_one_iff_dvd k).mp h)
    have hp : ((clockRoot r:ℂ)^k)^r.val = 1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,hr.pow_eq_one,one_pow]
    rw [if_neg hk,geom_sum_eq hn,hp,sub_self,zero_div,mul_zero,add_zero]

#print axioms clockRoot_primitive
#print axioms cyclicPhaseLaw_integral
#print axioms cyclicPhaseLaw_moment

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
