import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.BornLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Characters
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Powers
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Partition

/-! # A continuous coherent response has a unique critical-line exponent -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Set CoherentRay ModeCapacities
open scoped NNReal

/-- Divide out the attenuation in positive logarithmic time to obtain a
unit character, then put that phase back into the amplitude. -/
theorem critical_power {A : ℝ → ℂ} (hc : ContinuousOn A Shares) (seq : sequential A) (h : born A) :
    ∃ s : Conserving, ∀ x ∈ Shares, A x=power s.val x := by
  let B (t : ℝ≥0) := Real.exp (-(t:ℝ))
  let D (t : ℝ≥0) := Real.exp (-(t:ℝ)/2)
  have inside (t : ℝ≥0) : B t∈Shares := ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.property)⟩
  have dc (t : ℝ≥0) : 0<D t := Real.exp_pos _
  have bp (a b : ℝ≥0) : B (a+b)=B a*B b := by simp only [B,NNReal.coe_add,neg_add,Real.exp_add]
  have dp (a b : ℝ≥0) : D (a+b)=D a*D b := by simp only [D,NNReal.coe_add,neg_add,add_div,Real.exp_add]
  have normA (t : ℝ≥0) : ‖A (B t)‖=D t := by
    apply (sq_eq_sq₀ (norm_nonneg _) (dc t).le).mp
    rw [h _ (inside t)]
    dsimp only [D,B]
    rw [sq,←Real.exp_add]
    congr 1
    ring
  let C (t : ℝ≥0) := A (B t)/(D t:ℂ)
  have bc : Continuous B := by unfold B; fun_prop
  have dc' : Continuous (fun t : ℝ≥0 => (D t:ℂ)) := by unfold D; fun_prop
  have cc : Continuous C := (hc.comp_continuous bc inside).div dc' (fun t => Complex.ofReal_ne_zero.mpr (dc t).ne')
  have cm (a b : ℝ≥0) : C (a+b)=C a*C b := by
    dsimp only [C]
    rw [bp,seq _ (inside a) _ (inside b),dp,Complex.ofReal_mul,div_mul_div_comm]
  have unit (t : ℝ≥0) : ‖C t‖=1 := by
    dsimp only [C]
    rw [norm_div,normA,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (dc t),div_self (dc t).ne']
  obtain ⟨freq,phase⟩ := forward_character cc cm unit
  let s : Conserving := ⟨(1/2:ℂ)-(freq:ℂ)*Complex.I,by
    simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re,Complex.mul_I_re,Complex.ofReal_im,
      neg_zero,sub_zero]⟩
  refine ⟨s,?_⟩
  intro x hx
  let t : ℝ≥0 := ⟨-Real.log x,neg_nonneg.mpr (Real.log_nonpos hx.1.le hx.2)⟩
  have xt : B t=x := by change Real.exp (- -Real.log x)=x; rw [neg_neg,Real.exp_log hx.1]
  have H : A (B t)/(D t:ℂ)=Complex.exp ((freq*(t:ℝ):ℝ)*Complex.I) := phase t
  rw [xt] at H
  calc
    A x = Complex.exp ((freq*(t:ℝ):ℝ)*Complex.I)*(D t:ℂ) :=
      (div_eq_iff (Complex.ofReal_ne_zero.mpr (dc t).ne')).mp H
    _ = power s.val x := by
      dsimp only [D]
      rw [Complex.ofReal_exp,←Complex.exp_add,power]
      congr 1
      change ((freq*(-Real.log x):ℝ):ℂ)*Complex.I + ((- -Real.log x/2:ℝ):ℂ) =
        ((1/2:ℂ)-(freq:ℂ)*Complex.I)*(Real.log x:ℂ)
      push_cast
      ring

theorem unique_power {z w : ℂ} (same : ∀ x ∈ Shares, power z x=power w x) : z=w := by
  have ref (s : ℂ) (n : ℕ+) : power s (1/(n.val:ℝ))=heat s n := by
    simp only [power,one_div,Real.log_inv,Complex.ofReal_neg,heat,energy,mul_neg,neg_mul]
  have atInteger (n : ℕ+) : heat z n=heat w n := by
    have pos : (0:ℝ)<n.val := Nat.cast_pos.mpr n.pos
    have one : (1:ℝ)≤n.val := by exact_mod_cast (show 1≤n.val from n.pos)
    have share : 1/(n.val:ℝ)∈Shares := ⟨one_div_pos.mpr pos,(div_le_one pos).mpr one⟩
    exact (ref z n).symm.trans ((same _ share).trans (ref w n))
  exact two_prime_heat_injective (Prod.ext (atInteger 2) (atInteger 3))

#print axioms critical_power
#print axioms unique_power

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
