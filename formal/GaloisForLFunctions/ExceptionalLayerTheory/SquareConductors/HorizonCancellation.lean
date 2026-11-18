import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import GaloisForLFunctions.HTGeometry.CenteredModularAbel

/-!
# Horizon cancellation of the factorial prime weight

At a fixed product q the divisor tests have periods dq. Their discrete
means differ from their continuous means by a reciprocal divisor
weight. Both parity corrections and the factorial stencil kill that
weight, so only two incomplete periods survive on any horizon interval.
-/

noncomputable section
open Finset HTGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def correctedStencil (R : ℕ) (f : ℕ → ℝ) : ℝ :=
  stencil R f - momentRatio R * parityFunctional R f +
    (2/63)*primeWeightMean R * parityFunctional (128*R^2+1) f

private theorem stencil_diff (R : ℕ) (f g : ℕ → ℝ) :
    correctedStencil R (fun d => f d-g d) = correctedStencil R f-correctedStencil R g := by
  simp only [correctedStencil,stencil_sub,parityFunctional]
  ring

private theorem stencil_recip {R : ℕ} (hR : 1 ≤ R) (x : ℝ) :
    correctedStencil R (fun d => x/d) = 0 := by
  have h (a : ℕ) : parityFunctional a (fun d => x/d) = 0 := by
    simp only [parityFunctional,Nat.cast_mul,Nat.cast_ofNat,div_mul_eq_div_div]
    ring
  simp only [correctedStencil,stencil_linear_quotient hR,h,mul_zero,sub_zero,add_zero]

private theorem corrected_bound {R : ℕ} (hR : 1 ≤ R) (f : ℕ → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ d ∈ Icc 1 (128*(128*R^2+1)), |f d| ≤ M) :
    |correctedStencil R f| ≤ 1000*(1+mass R)*M := by
  let a := 128*R^2+1
  have hra : R ≤ a := by
    have hsq : R ≤ R^2 := by simpa only [sq,one_mul] using Nat.mul_le_mul_right R hR
    dsimp [a]; omega
  have h₁ := abs_stencil_le hR f fun d hd =>
    hf d (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,by have := (mem_Icc.mp hd).2; change d ≤ 128*a; omega⟩)
  have h₂ := parityFunctional_bound (R := R) (f := f) fun d hd =>
    hf d (mem_Icc.mpr ⟨hR.trans (mem_Icc.mp hd).1,by have := (mem_Icc.mp hd).2; change d ≤ 128*a; omega⟩)
  have h₃ := parityFunctional_bound (R := a) (f := f) fun d hd =>
    hf d (mem_Icc.mpr ⟨(hR.trans hra).trans (mem_Icc.mp hd).1,(mem_Icc.mp hd).2⟩)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  unfold correctedStencil
  apply (abs_add_le _ _).trans ((add_le_add (abs_sub _ _) le_rfl).trans ?_)
  rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/63)]
  have h₂' := mul_le_mul (ratio_bound hR) h₂ (abs_nonneg _) (by positivity)
  have h₃' := mul_le_mul (mul_le_mul_of_nonneg_left (mean_bound hR) (by norm_num : (0:ℝ) ≤ 2/63))
    h₃ (abs_nonneg _) (by positivity)
  linarith only [h₁,h₂',h₃',mul_nonneg hm hM,hM]

private theorem corrected_sum {ι : Type*} (R : ℕ) (S : Finset ι) (f : ι → ℕ → ℝ) :
    ∑ i ∈ S, correctedStencil R (f i) = correctedStencil R (fun d => ∑ i ∈ S, f i d) := by
  have st := stencil_weighted_sum R S (fun _ => (1:ℝ)) f
  have par (a : ℕ) := commute_functional S (fun _ => (1:ℝ)) f a
  simp only [one_mul] at st par
  simp only [correctedStencil,sum_add_distrib,sum_sub_distrib,←mul_sum,st,par]

private theorem ramp_shift {d q : ℕ} (hd : 0 < d) (hq : 0 < q) (k : ℕ) :
    centeredQuotient k q d = centeredModularRamp (d*q) k - ((1/2 : ℝ)/q)/d := by
  unfold centeredQuotient centeredModularRamp
  rw [div_div,←Nat.cast_mul,Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp
  ring

private theorem weight_ramps {R q : ℕ} (hR : 1 ≤ R) (hq : 0 < q) (k : ℕ) :
    centeredPrimeWeight R (k/q) = correctedStencil R (fun d => centeredModularRamp (d*q) k) := by
  let f := centeredQuotient k q
  let g := fun d : ℕ => centeredModularRamp (d*q) k - ((1/2 : ℝ)/q)/d
  have hz := corrected_bound hR (fun d => f d-g d) (M := 0) le_rfl
    (fun d hd => by simp only [f,g,ramp_shift (mem_Icc.mp hd).1 hq,sub_self,abs_zero,le_refl])
  rw [stencil_diff,mul_zero,abs_nonpos_iff,sub_eq_zero] at hz
  rw [centeredPrimeWeight_expansion hR]
  change correctedStencil R f=_
  rw [hz]
  dsimp only [g]
  rw [stencil_diff,stencil_recip hR,sub_zero]

/-- The prefix discrepancy of a fixed product grows linearly in the product,
even for sharp and independently moving horizon endpoints. -/
theorem centeredPrimeWeight_horizon_interval {R q : ℕ} (hR : 1 ≤ R) (hq : 0 < q) (L U : ℕ) :
    |∑ k ∈ Ico L U, centeredPrimeWeight R (k/q)| ≤
      125*(1+mass R)*(128*(128*(R:ℝ)^2+1))*q := by
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  by_cases hLU : L ≤ U
  swap
  · rw [Ico_eq_empty (by omega),sum_empty,abs_zero]; positivity
  simp only [weight_ramps hR hq,corrected_sum]
  let J := 128*(128*R^2+1)
  have hb := corrected_bound hR (fun d => ∑ k ∈ Ico L U, centeredModularRamp (d*q) k)
    (M := (J:ℝ)*q/8) (by positivity) fun d hd => by
      rw [sum_Ico_eq_sub _ hLU,sum_centeredModularRamp,sum_centeredModularRamp,abs_le]
      have hu := centeredModularPrimitive_bounds (d*q) U
      have hl := centeredModularPrimitive_bounds (d*q) L
      have hle : ((d*q:ℕ):ℝ) ≤ (J:ℝ)*q := by exact_mod_cast Nat.mul_le_mul_right q (mem_Icc.mp hd).2
      constructor <;> linarith only [hu.1,hu.2,hl.1,hl.2,hle]
  apply hb.trans_eq
  dsimp only [J]
  push_cast
  ring

#print axioms centeredPrimeWeight_horizon_interval
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
