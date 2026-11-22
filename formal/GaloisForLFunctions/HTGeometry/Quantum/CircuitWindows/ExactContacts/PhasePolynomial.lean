import GaloisForLFunctions.HTGeometry.FiniteSpectralHaarRecurrenceLaw
import GaloisForLFunctions.HTGeometry.EscapingRealSequenceCover
import GaloisForLFunctions.RHTower.ExponentialSumMeanSquareLower
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Zeros of a polynomial along independent phase clocks -/
open Filter Set MvPolynomial
namespace GaloisForLFunctions.HTGeometry.ExactContacts
noncomputable section
variable {I : Type*} [Fintype I]

/-- The temporal frequency of one phase monomial. -/
def monomialFrequency (w : I→ℝ) (d : I →₀ ℕ) : ℝ := ∑ i, (d i:ℝ)*w i

theorem injective_monomialFrequency {w : I→ℝ} (hw : RationallyIndependentFrequency w) :
    Function.Injective (monomialFrequency w) := by
  intro d e h
  let m (i : I) : ℤ := (d i:ℤ)-(e i:ℤ)
  have hd : finiteTorusCharacterDetuning m w=0 := by
    simp only [finiteTorusCharacterDetuning,m,Int.cast_sub,Int.cast_natCast,sub_mul,Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have hm := hw m hd
  ext i
  have he := congrFun hm i
  change (d i:ℤ)-(e i:ℤ)=0 at he
  omega

def energyPhase (w t : ℝ) : ℂ := Complex.exp (-Complex.I*(w:ℂ)*(t:ℂ))

/-- Evaluation on the torus groups the polynomial into distinct physical
frequencies, one for each nonzero coefficient. -/
theorem eval_phase_expansion (w : I→ℝ) (F : MvPolynomial I ℂ) (t : ℝ) :
    aeval (fun i => energyPhase (w i) t) F =
      RHTower.expSum_exponentialSumMeanSquareLower F.support (fun d => F.coeff d) (monomialFrequency w) t := by
  classical
  rw [aeval_def,eval₂_eq']
  apply Finset.sum_congr rfl
  intro d _
  change F.coeff d*(∏ i, (energyPhase (w i) t)^(d i))=F.coeff d*energyPhase (monomialFrequency w d) t
  congr 1
  simp only [energyPhase,←Complex.exp_nat_mul,←Complex.exp_sum]
  congr 1
  dsimp only [monomialFrequency]
  push_cast
  simp only [Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A nonzero polynomial in rationally independent phases has only finitely
many real zeros in any compact interval. -/
theorem finite_phase_zeros {w : I→ℝ} (hw : RationallyIndependentFrequency w) {F : MvPolynomial I ℂ}
    (hF : F≠0) (a b : ℝ) :
    {t ∈ Icc a b | aeval (fun i => energyPhase (w i) t) F=0}.Finite := by
  classical
  let f := RHTower.expSum_exponentialSumMeanSquareLower F.support (fun d => F.coeff d) (monomialFrequency w)
  have hs : F.support.Nonempty := MvPolynomial.support_nonempty.mpr hF
  have hn : (0:ℝ)^2 < ∑ d ∈ F.support, ‖F.coeff d‖^2 := by
    rw [zero_pow (by decide : 2≠0)]
    exact Finset.sum_pos (fun d hd => sq_pos_of_pos (norm_pos_iff.mpr (MvPolynomial.mem_support_iff.mp hd))) hs
  obtain ⟨t,ht⟩ := (RHTower.frequently_lt_norm_expSum F.support (fun d => F.coeff d) (monomialFrequency w)
    (injective_monomialFrequency hw).injOn hn).exists
  have hne : f t≠0 := norm_pos_iff.mp ht
  have ha (x : ℝ) : AnalyticAt ℝ f x := by
    apply Finset.analyticAt_fun_sum
    intro d _
    apply analyticAt_const.mul
    have hc : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-Complex.I*(monomialFrequency w d:ℂ)*z)) (x:ℂ) := by fun_prop
    exact analyticAt_comp_ofReal hc
  have hfin := finite_zeros_of_analyticOnNhd_complex isPreconnected_univ (fun x _ => ha x)
    (mem_univ t) hne (isCompact_Icc (a:=a) (b:=b)) (subset_univ _)
  exact hfin.subset fun t ht => ⟨ht.1,(eval_phase_expansion w F t).symm.trans ht.2⟩

#print axioms finite_phase_zeros
end
end GaloisForLFunctions.HTGeometry.ExactContacts
