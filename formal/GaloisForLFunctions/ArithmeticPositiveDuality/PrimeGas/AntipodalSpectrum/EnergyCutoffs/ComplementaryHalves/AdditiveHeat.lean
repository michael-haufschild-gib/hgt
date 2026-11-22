import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.ComplementaryHalves.SpectralRigidity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Reflection of the paired additive heat

The geometric heat of the complete integer tiling gives a closed two-copy
trace. Its reflection detects the common translation at any positive time.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves

def entry (C : Radix) (a v : ℝ) (x : Half C) := Real.exp (-v*((x.val:ℝ)+a))

def singleHeat (C : Radix) (a v : ℝ) := ∑' x : Half C, entry C a v x

def kernel (C : Radix) (a v : ℝ) := Real.exp (-v*(((C.val:ℝ)+1)*a))/(1-Real.exp (-v))

private theorem geometric (v : {x : ℝ // 0 < x}) : Real.exp (-v.val) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos v.property)

theorem entry_summable (C : Radix) (a : ℝ) (v : {u : ℝ // 0 < u}) : Summable (entry C a v.val) := by
  have h := (summable_geometric_of_lt_one (Real.exp_pos (-v.val)).le (geometric v)).comp_injective
    (Subtype.val_injective (p := fun x : ℕ => ∀ d ∈ (C.val^2).digits x, d < C.val))
  apply (h.mul_left (Real.exp (-v.val*a))).congr
  intro x
  change Real.exp (-v.val*a)*Real.exp (-v.val)^x.val = _
  rw [← Real.exp_nat_mul,← Real.exp_add,entry]
  congr 1
  ring

/-- Complementary copies at times v and Cv give the geometric heat of all translated integers. -/
theorem heat_product (C : Radix) (a : ℝ) (v : {u : ℝ // 0 < u}) :
    singleHeat C a v.val*singleHeat C a ((C.val:ℝ)*v.val) = kernel C a v.val := by
  let h := ((C.val:ℝ)+1)*a
  have hv : 0 < (C.val:ℝ)*v.val := mul_pos (by exact_mod_cast zero_lt_one.trans C.property) v.property
  have hX := entry_summable C a v
  have hY := entry_summable C a ⟨_,hv⟩
  have hp := hX.mul_of_nonneg hY (fun x => (Real.exp_pos _).le) (fun y => (Real.exp_pos _).le)
  rw [singleHeat,singleHeat,hX.tsum_mul_tsum hY hp]
  calc
    _ = ∑' p : Half C × Half C, Real.exp (-v.val*h)*Real.exp (-v.val)^(interleave C p) := by
      apply tsum_congr
      intro p
      simp only [entry,← Real.exp_nat_mul,← Real.exp_add,interleave_apply,Nat.cast_add,Nat.cast_mul,h]
      congr 1
      ring
    _ = ∑' n : ℕ, Real.exp (-v.val*h)*Real.exp (-v.val)^n :=
      (interleave C).tsum_eq (fun n : ℕ => Real.exp (-v.val*h)*Real.exp (-v.val)^n)
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.exp_pos _).le (geometric v)]; rfl

private theorem sinh_factor (v : ℝ) :
    2*Real.sinh (v/2) = Real.exp (v/2)*(1-Real.exp (-v)) := by
  rw [Real.sinh_eq,mul_sub,mul_one,← Real.exp_add,show v/2 + -v = -(v/2) by ring]
  ring

theorem kernel_sinh (C : Radix) (a v : ℝ) :
    kernel C a v = Real.exp ((1/2-((C.val:ℝ)+1)*a)*v)/(2*Real.sinh (v/2)) := by
  let h := ((C.val:ℝ)+1)*a
  change Real.exp (-v*h)/(1-Real.exp (-v)) = Real.exp ((1/2-h)*v)/_
  rw [sinh_factor,show (1/2-h)*v = v/2 + -v*h by ring,Real.exp_add,
    mul_div_mul_left _ _ (Real.exp_ne_zero _)]

theorem centered_heat_product (C : Radix) (v : {u : ℝ // 0 < u}) :
    singleHeat C (midpoint C) v.val*singleHeat C (midpoint C) ((C.val:ℝ)*v.val) =
      1/(2*Real.sinh (v.val/2)) := by
  rw [heat_product,kernel_sinh,midpoint_eq,sub_self,zero_mul,Real.exp_zero]

/-- One reflected pair of nonzero times determines the unique centered spectrum. -/
theorem reflection_iff (C : Radix) (a : ℝ) (v : {u : ℝ // 0 < u}) :
    kernel C a (-v.val) = -kernel C a v.val ↔ a = midpoint C := by
  let d := 1/2-((C.val:ℝ)+1)*a
  have hD : 2*Real.sinh (v.val/2) ≠ 0 := by
    rw [sinh_factor]
    exact mul_ne_zero (Real.exp_ne_zero _) (sub_pos.mpr (geometric v)).ne'
  rw [kernel_sinh,kernel_sinh,neg_div,Real.sinh_neg,mul_neg (2:ℝ) _,div_neg,neg_inj]
  change Real.exp (d*(-v.val))/(2*Real.sinh (v.val/2)) = Real.exp (d*v.val)/(2*Real.sinh (v.val/2)) ↔ _
  constructor
  · intro H
    have he := congrArg (fun x : ℝ => x*(2*Real.sinh (v.val/2))) H
    simp only [div_mul_cancel₀ _ hD] at he
    have hx := Real.exp_injective he
    have hd : d*v.val = 0 := by linarith only [hx]
    have hd₀ := (mul_eq_zero.mp hd).resolve_right v.property.ne'
    apply mul_left_cancel₀ (show (C.val:ℝ)+1 ≠ 0 by positivity)
    rw [midpoint_eq]
    exact (sub_eq_zero.mp hd₀).symm
  · rintro rfl
    simp only [d,midpoint_eq,sub_self,zero_mul]

#print axioms heat_product
#print axioms centered_heat_product
#print axioms reflection_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.ComplementaryHalves
