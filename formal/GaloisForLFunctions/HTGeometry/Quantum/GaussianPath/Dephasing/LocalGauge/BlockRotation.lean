import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.CircuitProfile

/-! # A straight tangent to onsite conjugation is an exact quadratic field change -/
open Matrix Complex
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.LocalGauge
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private abbrev M := Matrix ι ι ℂ

/-- Part of H that exchanges the two sectors of the specified bit. -/
def exchange (b : ι→Bool) (H : M) : M := fun i j => if b i=b j then 0 else H i j

/-- Derivative of conjugation by the phase exp(ih) on the true sector. -/
def tangent (b : ι→Bool) (H : M) : M := fun i j =>
  if b i=b j then 0 else if b i then I*H i j else -(I*H i j)

/-- On opposite sectors the factors 1±ih have the common magnitude
√(1+h²). Their phases are exactly removed by one diagonal basis change. -/
theorem tangent_conjugation (b : ι→Bool) (H : M) (h : ℝ) :
    ∃ V : Matrix.unitaryGroup ι ℂ, H+h • tangent b H=
      V.val*(H+(Real.sqrt (1+h^2)-1) • exchange b H)*star V.val := by
  let a := Real.sqrt (1+h^2)
  have ha : 0<a := Real.sqrt_pos.mpr (by positivity)
  let w := (1+(h:ℂ)*I)/(a:ℂ)
  have hw₀ : ‖1+(h:ℂ)*I‖=a := by
    rw [Complex.norm_def,Complex.normSq_apply]
    simp [a,sq]
  have hw : ‖w‖=1 := by
    rw [show ‖w‖=‖1+(h:ℂ)*I‖/‖(a:ℂ)‖ from norm_div ..,hw₀,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,div_self ha.ne']
  let f (i : ι) : ℂ := if b i then w else 1
  have hunit (i : ι) : f i*star (f i)=1 := by
    have hn : ‖f i‖=1 := by dsimp only [f]; split <;> simp [hw]
    rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one]
  have hV : diagonal f∈Matrix.unitaryGroup ι ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,diagonal_conjTranspose,diagonal_mul_diagonal,←Matrix.diagonal_one]
    exact congrArg diagonal (funext hunit)
  refine ⟨⟨diagonal f,hV⟩,?_⟩
  change H+h • tangent b H=diagonal f*(H+(a-1) • exchange b H)*star (diagonal f)
  rw [Matrix.star_eq_conjTranspose,diagonal_conjTranspose]
  have hwc : w*star w=1 := by rw [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hw,one_pow,Complex.ofReal_one]
  have hwa : w*(a:ℂ)=1+(h:ℂ)*I := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr ha.ne')
  have hwb : star w*(a:ℂ)=1-(h:ℂ)*I := by
    have he := congrArg (star : ℂ→ℂ) hwa
    simpa only [star_mul',map_add,star_one,Complex.star_def,Complex.conj_ofReal,Complex.conj_I,mul_neg,←sub_eq_add_neg] using he
  ext i j
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.add_apply,Matrix.smul_apply,Complex.real_smul,
    smul_eq_mul,Pi.star_apply,Complex.ofReal_sub,Complex.ofReal_one]
  cases hi : b i <;> cases hj : b j <;> simp only [exchange,tangent,f,hi,hj,if_true,if_false,Bool.false_ne_true,
    Bool.true_ne_false,Bool.false_eq_true,ite_self,star_one,mul_zero,mul_one,one_mul,add_zero]
  all_goals first | linear_combination (norm := ring) H i j*hwa | linear_combination (norm := ring) H i j*hwb |
    linear_combination (norm := ring) -(H i j)*hwc | ring

#print axioms tangent_conjugation
end
end GaloisForLFunctions.HTGeometry.Dephasing.LocalGauge
