import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.SplitAbscissae.PrimeTower
import GaloisForLFunctions.U0.U0NaturalBoundary

/-! # Transporting the unit-circle obstruction to the composition line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology U0 U0NaturalBoundary
open _root_.RHTower.PrimeCoShift

def compositionRight := {s : ℂ | 1/2 < s.re}

/-- The exponential of twice the displacement from the isometry line in units of one prime energy. -/
def compositionClock (p : Nat.Primes) (s : ℂ) :=
  Complex.exp ((2*s-1)*(energy (primePNat p):ℂ))

theorem compositionClock_heat (p : Nat.Primes) (s : ℂ) :
    (heat (2*s-1) (primePNat p))⁻¹ = compositionClock p s := by
  rw [heat,← Complex.exp_neg,compositionClock,neg_mul,neg_neg]

theorem compositionClock_norm (p : Nat.Primes) (s : ℂ) :
    ‖compositionClock p s‖ = Real.exp ((2*s.re-1)*energy (primePNat p)) := by
  rw [compositionClock,Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,two_mul,
    Complex.sub_re,Complex.add_re,Complex.one_re]

theorem compositionClock_exterior (p : Nat.Primes) (s : ℂ) :
    compositionClock p s ∈ U0NaturalBoundary.Ext ↔ s ∈ compositionRight := by
  change 1 < ‖compositionClock p s‖ ↔ 1/2 < s.re
  rw [compositionClock_norm,Real.one_lt_exp_iff]
  constructor
  · intro h
    by_contra! hh
    exact h.not_ge (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hh]) (prime_energy_pos p).le)
  · intro h
    exact mul_pos (by linarith only [h]) (prime_energy_pos p)

theorem compositionClock_analytic (p : Nat.Primes) (s : ℂ) : AnalyticAt ℂ (compositionClock p) s := by
  unfold compositionClock
  fun_prop

private def inverseAt (p : Nat.Primes) (s : ℂ) (w : ℂ) :=
  s + Complex.log (w/compositionClock p s)/(2*(energy (primePNat p):ℂ))

private theorem inverse_center (p : Nat.Primes) (s : ℂ) : inverseAt p s (compositionClock p s) = s := by
  simp only [inverseAt,div_self (show compositionClock p s ≠ 0 from Complex.exp_ne_zero _),
    Complex.log_one,zero_div,add_zero]

private theorem inverse_analytic (p : Nat.Primes) (s : ℂ) :
    AnalyticAt ℂ (inverseAt p s) (compositionClock p s) := by
  have hq : AnalyticAt ℂ (fun w => w/compositionClock p s) (compositionClock p s) := by fun_prop
  have hl := hq.clog (show compositionClock p s/compositionClock p s ∈ Complex.slitPlane by
    rw [div_self (show compositionClock p s ≠ 0 from Complex.exp_ne_zero _)]; exact Complex.one_mem_slitPlane)
  unfold inverseAt
  exact analyticAt_const.add hl.div_const

private theorem clock_inverse (p : Nat.Primes) (s : ℂ) {w : ℂ} (hw : w ≠ 0) :
    compositionClock p (inverseAt p s w) = w := by
  have hL : (energy (primePNat p):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (prime_energy_pos p).ne'
  have hC : compositionClock p s ≠ 0 := Complex.exp_ne_zero _
  have he : (2*inverseAt p s w-1)*(energy (primePNat p):ℂ) =
      (2*s-1)*(energy (primePNat p):ℂ)+Complex.log (w/compositionClock p s) := by
    unfold inverseAt
    field_simp [hL]
    ring
  change Complex.exp ((2*inverseAt p s w-1)*(energy (primePNat p):ℂ)) = w
  rw [he,Complex.exp_add,Complex.exp_log (div_ne_zero hw hC)]
  change compositionClock p s*(w/compositionClock p s) = w
  field_simp [hC]

/-- A genuine continuation of the pulled-back function would continue the companion through the unit circle. -/
theorem clock_natural_boundary (p : Nat.Primes) (s : ℂ) (hs : s.re = 1/2) :
    ¬ ContinuesAcross (fun z => u0 (compositionClock p z)) compositionRight s := by
  rintro ⟨g,hg,he⟩
  let C := compositionClock p s
  let I := inverseAt p s
  have hn : ‖C‖ = 1 := by rw [show C = compositionClock p s from rfl,compositionClock_norm,hs]; norm_num
  have hIC : I C = s := inverse_center p s
  have ha : AnalyticAt ℂ I C := inverse_analytic p s
  have ht : Tendsto I (𝓝[U0NaturalBoundary.Ext] C) (𝓝[compositionRight] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hIC ▸ ha.continuousAt.continuousWithinAt,?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    apply (compositionClock_exterior p _).mp
    change compositionClock p (inverseAt p s w) ∈ U0NaturalBoundary.Ext
    rw [clock_inverse p s (ne_zero_of_Ext hw)]
    exact hw
  apply u0_natural_boundary C hn
  have hg' : AnalyticAt ℂ g (I C) := hIC.symm ▸ hg
  refine ⟨g ∘ I,hg'.comp ha,?_⟩
  filter_upwards [ht.eventually he,self_mem_nhdsWithin] with w hw hExt
  change g (I w) = u0 w
  change g (I w) = u0 (compositionClock p (inverseAt p s w)) at hw
  rw [hw,clock_inverse p s (ne_zero_of_Ext hExt)]

#print axioms compositionClock_heat
#print axioms compositionClock_norm
#print axioms compositionClock_exterior
#print axioms compositionClock_analytic
#print axioms clock_natural_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
