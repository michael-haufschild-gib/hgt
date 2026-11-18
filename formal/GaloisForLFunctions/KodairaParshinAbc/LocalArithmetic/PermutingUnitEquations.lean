import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.DyadicUnitEquationHeights

/-!
# Permutation of signed projective S-unit equations

The invariance of solution counts in Ziegler (arXiv:2609.15487, §1)
uses a sign when the target moves to the left of the equation. Fixing
the last homogeneous coordinate at -1 supplies that sign canonically.
Changing the distinguished coordinate and permuting a finite list of
coefficients then give exact equivalences of solution types.
-/

noncomputable section
namespace GaloisForLFunctions.KodairaParshinAbc
open GaloisForLFunctions.RHTower IsDedekindDomain
variable (S : Finset (HeightOneSpectrum ℤ))
local notation "U" => fieldOneSUnitSubgroup S

/-- The distinguished coordinate of a homogeneous signed unit presentation. -/
def unitEquationSign : U := ⟨-1,fieldOne_negOne_mem_sUnitSubgroup _⟩
local notation "ε" => unitEquationSign S

/-- A linear unit equation with one coordinate normalized to minus one. -/
def SignedUnitChart {ι : Type*} [Fintype ι] (a : ι → ℚ) (j : ι) :=
  {z : ι → U // z j = ε ∧ ∑ i, a i * ((z i).val:ℚ) = 0}

/-- Ordinary two-term unit solutions are the last-coordinate chart of a homogeneous ternary equation. -/
def ternaryUnitChart (A B C : ℚ) :
    RationalUnitSolutions S A B C ≃ SignedUnitChart S ![A,B,C] (2 : Fin 3) where
  toFun z := ⟨![z.val.1,z.val.2,ε],rfl,by
    simp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    change A*(z.val.1.val:ℚ)+B*(z.val.2.val:ℚ)+C*(-1) = 0
    rw [z.property]; ring⟩
  invFun z := ⟨(z.val 0,z.val 1),by
    have h := z.property.2
    rw [Fin.sum_univ_three,z.property.1] at h
    change A*((z.val 0).val:ℚ)+B*((z.val 1).val:ℚ)+C*(-1)=0 at h
    linear_combination h⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext; funext i
    fin_cases i
    · rfl
    · rfl
    · exact z.property.1.symm

private def chartTransport {ι κ : Type*} [Fintype ι] [Fintype κ] {a : ι → ℚ}
    {j : ι} (e : κ ≃ ι) (k : κ) (z : SignedUnitChart S a j) : SignedUnitChart S (a ∘ e) k :=
  ⟨fun i => z.val (e i) * (ε / z.val (e k)), by simp, by
    let t := ε / z.val (e k)
    change ∑ i, a (e i) * (((z.val (e i) * t).val):ℚ) = 0
    simp only [Subgroup.coe_mul,Units.val_mul,← mul_assoc,← Finset.sum_mul]
    rw [e.sum_comp (fun i => a i*((z.val i).val:ℚ)),z.property.2,zero_mul]⟩

/-- Arbitrary permutations and changes of affine chart preserve the full solution fiber. -/
def signedUnitChartEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℚ) (j : ι)
    (e : κ ≃ ι) (k : κ) : SignedUnitChart S a j ≃ SignedUnitChart S (a ∘ e) k where
  toFun := chartTransport S e k
  invFun z := ⟨(chartTransport S e.symm j z).val,(chartTransport S e.symm j z).property.1,
    by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using (chartTransport S e.symm j z).property.2⟩
  left_inv z := by
    apply Subtype.ext; funext i
    change (z.val (e (e.symm i))*(ε/z.val (e k)))*(ε/(z.val (e (e.symm j))*(ε/z.val (e k))))=z.val i
    rw [e.apply_symm_apply,e.apply_symm_apply,z.property.1]
    rw [div_mul_cancel_left,mul_inv_cancel_right]
  right_inv z := by
    apply Subtype.ext; funext i
    change (z.val (e.symm (e i))*(ε/z.val (e.symm j)))*(ε/(z.val (e.symm (e k))*(ε/z.val (e.symm j))))=z.val i
    rw [e.symm_apply_apply,e.symm_apply_apply,z.property.1]
    rw [div_mul_cancel_left,mul_inv_cancel_right]

/-- All six permutations of the three unsigned coefficients preserve the signed S-unit solution fiber. -/
def rationalUnitSolutionsPermute (a : Fin 3 → ℚ) (e : Equiv.Perm (Fin 3)) :
    RationalUnitSolutions S (a 0) (a 1) (a 2) ≃
      RationalUnitSolutions S (a (e 0)) (a (e 1)) (a (e 2)) := by
  have h (b : Fin 3 → ℚ) : ![b 0,b 1,b 2] = b := by funext i; fin_cases i <;> rfl
  let toChart (b : Fin 3 → ℚ) : RationalUnitSolutions S (b 0) (b 1) (b 2) ≃ SignedUnitChart S b 2 :=
    (ternaryUnitChart S _ _ _).trans (Equiv.cast (congrArg (fun c => SignedUnitChart S c 2) (h b)))
  exact (toChart a).trans ((signedUnitChartEquiv S a 2 e 2).trans (toChart (a ∘ e)).symm)

/-- Swapping first coefficient and target requires the sign on the second unit.
The unsigned substitution works precisely if that coefficient is zero. -/
theorem unsigned_target_swap_iff {K : Type*} [Field K] [CharZero K] (a b c : K) (x y : Kˣ)
    (h : a*(x:K)+b*(y:K)=c) : c/(x:K)+b*((y:K)/x)=a ↔ b=0 := by
  constructor
  · intro hu
    field_simp [x.ne_zero] at hu
    have he : (2:K)*b*(y:K)=0 := by linear_combination hu + h
    exact ((mul_eq_zero.mp he).resolve_right y.ne_zero |> mul_eq_zero.mp).resolve_left two_ne_zero
  · rintro rfl
    rw [zero_mul,add_zero] at h ⊢
    rw [← h,mul_div_cancel_right₀ _ x.ne_zero]

/-- The signed reciprocal substitution works for every solution over every field. -/
theorem signed_target_swap {K : Type*} [Field K] (a b c : K) (x y : Kˣ)
    (h : a*(x:K)+b*(y:K)=c) : c/(x:K)+b*(-(y:K)/x)=a := by
  field_simp [x.ne_zero]
  linear_combination -h

#print axioms ternaryUnitChart
#print axioms signedUnitChartEquiv
#print axioms rationalUnitSolutionsPermute
#print axioms unsigned_target_swap_iff
#print axioms signed_target_swap

end GaloisForLFunctions.KodairaParshinAbc
