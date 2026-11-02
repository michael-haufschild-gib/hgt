import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
/-!
# Explicit parameters for sparse spline correction

A single positive radius controls displacement, spatial variation, and the
nonlinear remainder. A quadratic sampling threshold and continuous endpoint
bounds determine the node count. An explicit height threshold controls both
exact denominator errors.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Explicit choices keep sampling, nonlinear, spatial, and denominator
errors small while retaining polynomial dependence on finite scalar data. -/
theorem exists_sparse_spline_parameters {δ m P Q I J M₀ C B G : ℝ}
    (hδ : 0 < δ) (hm : 0 ≤ m) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hM : 0 ≤ M₀)
    (hB : 0 ≤ B) (hG : 0 ≤ G) :
    ∃ ρ ε H₀ : ℝ, ∃ n : ℕ, 0 < ρ ∧ 0 < ε ∧ 0 < H₀ ∧ 0 < n ∧
      ρ=1/(8*(1+P+2*m*I+Q*P^2)) ∧ ε=ρ/(16*(m+1)) ∧
      P*ρ ≤ 1/4 ∧ (2*m*I)*ρ ≤ 1/2 ∧ Q*P^2*ρ ≤ 1/8 ∧
      C^2 ≤ (n:ℝ)*ε^2 ∧ J/(n:ℝ)+2*m*ε ≤ 1/4 ∧ ε+M₀/(n:ℝ) ≤ ρ/8 ∧
      (n:ℝ) ≤ 2+(C/ε)^2+16*J+16*M₀/ρ ∧
      H₀=1+64*((((n:ℝ)+2)+δ)*G+B)*P+64*(((n:ℝ)+2)+δ)*B/ρ ∧
      ∀ H : ℝ, H₀ ≤ H →
        8*((((n:ℝ)+2)+δ)*G+B)*P/H ≤ 1/8 ∧
        8*(((n:ℝ)+2)+δ)*B/H ≤ ρ/8 := by
  let D := 1+P+2*m*I+Q*P^2
  have hD : 0 < D := by dsimp only [D]; positivity
  have hMI : 0 ≤ 2*m*I := by positivity
  have hQP : 0 ≤ Q*P^2 := by positivity
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith only [hP,hMI,hQP]
  have hPD : P ≤ D := by dsimp only [D]; linarith only [hMI,hQP]
  have hMID : 2*m*I ≤ D := by dsimp only [D]; linarith only [hP,hQP]
  have hQPD : Q*P^2 ≤ D := by dsimp only [D]; linarith only [hP,hMI]
  let ρ := 1/(8*D)
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hDρ : D*ρ=1/8 := by dsimp only [ρ]; field_simp [hD.ne']
  have hρ1 : ρ ≤ 1/8 := by
    have hh := mul_le_mul_of_nonneg_right hD1 hρ.le
    rw [one_mul,hDρ] at hh
    exact hh
  have hprod : ∀ V : ℝ, V ≤ D → V*ρ ≤ 1/8 := by
    intro V hV
    exact (mul_le_mul_of_nonneg_right hV hρ.le).trans_eq hDρ
  have hdisp : P*ρ ≤ 1/4 := (hprod P hPD).trans (by norm_num)
  have hspace : (2*m*I)*ρ ≤ 1/2 :=
    (hprod (2*m*I) hMID).trans (by norm_num)
  have hquad : Q*P^2*ρ ≤ 1/8 := hprod (Q*P^2) hQPD
  let ε := ρ/(16*(m+1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have heps : 16*(m+1)*ε=ρ := by dsimp only [ε]; field_simp [show m+1 ≠ 0 by positivity]
  have hεsmall : ε ≤ ρ/16 := by
    have hh := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤16) hm) hε.le
    nlinarith only [heps,hh]
  have hmeps : 2*m*ε ≤ 1/8 := by nlinarith only [heps,hε,hρ1]
  let n := ⌊1+(C/ε)^2+16*J+16*M₀/ρ⌋₊+1
  have hnLower : 1+(C/ε)^2+16*J+16*M₀/ρ < (n:ℝ) := by
    simpa only [n,Nat.cast_add,Nat.cast_one] using
      Nat.lt_floor_add_one (1+(C/ε)^2+16*J+16*M₀/ρ)
  have hnUpper : (n:ℝ) ≤ 2+(C/ε)^2+16*J+16*M₀/ρ := by
    have hh := Nat.floor_le (show 0 ≤ 1+(C/ε)^2+16*J+16*M₀/ρ by positivity)
    dsimp only [n]
    rw [Nat.cast_add,Nat.cast_one]
    linarith only [hh]
  have hc0 : 0 ≤ (C/ε)^2 := sq_nonneg _
  have hj0 : 0 ≤ 16*J := by positivity
  have hm0 : 0 ≤ 16*M₀/ρ := by positivity
  have hnR : (0:ℝ)<n := by linarith only [hnLower,hc0,hj0,hm0]
  have hn : 0 < n := by exact_mod_cast hnR
  have hcost : C^2 ≤ (n:ℝ)*ε^2 := by
    have hh : (C/ε)^2 ≤ (n:ℝ) := by linarith only [hnLower,hj0,hm0]
    rw [div_pow] at hh
    exact (div_le_iff₀ (pow_pos hε 2)).mp hh
  have hJn : J/(n:ℝ) ≤ 1/16 := by
    apply (div_le_iff₀ hnR).2
    linarith only [hnLower,hc0,hm0]
  have hMn : M₀/(n:ℝ) ≤ ρ/16 := by
    apply (div_le_iff₀ hnR).2
    have hh : 16*M₀/ρ ≤ (n:ℝ) := by linarith only [hnLower,hc0,hj0]
    have hh' := (div_le_iff₀ hρ).mp hh
    nlinarith only [hh']
  have hrow : J/(n:ℝ)+2*m*ε ≤ 1/4 := by linarith only [hJn,hmeps]
  have hbase : ε+M₀/(n:ℝ) ≤ ρ/8 := by linarith only [hεsmall,hMn]
  let H₀ := 1+64*((((n:ℝ)+2)+δ)*G+B)*P+64*(((n:ℝ)+2)+δ)*B/ρ
  have hH₀ : 0 < H₀ := by dsimp only [H₀]; positivity
  refine ⟨ρ,ε,H₀,n,hρ,hε,hH₀,hn,rfl,rfl,hdisp,hspace,hquad,hcost,hrow,hbase,hnUpper,rfl,?_⟩
  intro H hH
  have hHp := hH₀.trans_le hH
  have he0 : 0 ≤ 64*((((n:ℝ)+2)+δ)*G+B)*P := by positivity
  have hb0 : 0 ≤ 64*(((n:ℝ)+2)+δ)*B/ρ := by positivity
  constructor
  · apply (div_le_iff₀ hHp).2
    change 1+64*((((n:ℝ)+2)+δ)*G+B)*P+64*(((n:ℝ)+2)+δ)*B/ρ ≤ H at hH
    nlinarith only [hH,hb0]
  · apply (div_le_iff₀ hHp).2
    have hh : 64*(((n:ℝ)+2)+δ)*B/ρ ≤ H := by
      change 1+64*((((n:ℝ)+2)+δ)*G+B)*P+64*(((n:ℝ)+2)+δ)*B/ρ ≤ H at hH
      linarith only [hH,he0]
    have hh' := (div_le_iff₀ hρ).mp hh
    nlinarith only [hh']

#print axioms exists_sparse_spline_parameters
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
