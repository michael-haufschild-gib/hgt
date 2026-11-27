import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.ShellPhases
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Commensurable.Stabilization

/-! # Algebraic coordinates of energy differences -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Finset Real Set
open scoped Polynomial

/-- Exponential coordinate of the energy difference of two integer shells. -/
def relativePower (s : ℝ) (a b : ℕ+) := shellPower s a/shellPower s b

theorem relativePower_exp (s : ℝ) (a b : ℕ+) :
    relativePower s a b=exp (s*(energy a-energy b)) := by
  rw [relativePower,shellPower_exp,shellPower_exp,mul_sub,exp_sub]

/-- Homogenizing in the two shell monomials clears every denominator. -/
private def cleared (P : ℤ[X]) (a b : ℕ+) : PolynomialRing :=
  ∑ i ∈ range (P.natDegree+1), (P.coeff i : PolynomialRing)*(atom a)^i*(atom b)^(P.natDegree-i)

private theorem eval_cleared {K : Type} [Field K] [CharZero K] (e : PolynomialRing →ₐ[ℤ] K)
    (P : ℤ[X]) (a b : ℕ+) (nz : e (atom b) ≠ 0) :
    e (cleared P a b)=(e (atom b))^P.natDegree * Polynomial.aeval (e (atom a)/e (atom b)) P := by
  rw [cleared,map_sum,Polynomial.aeval_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ P.natDegree := Nat.le_of_lt_succ (mem_range.mp hi)
  have split : (e (atom b))^P.natDegree=(e (atom b))^(P.natDegree-i)*(e (atom b))^i :=
    (congrArg ((e (atom b))^·) (Nat.sub_add_cancel hi').symm).trans (pow_add _ _ _)
  rw [split]
  simp only [map_mul,map_intCast,map_pow,zsmul_eq_mul,div_pow]
  field_simp

/-- The quotient of the two twisted coordinates is a root of every original
polynomial for the relative coordinate. Its modulus records the signed order. -/
theorem relative_root {t v : ℝ} {m : ℕ} (hm : 0 < m) (spec : TorsionSpecialization m t v)
    (a b : ℕ+) (P : ℤ[X]) (root : Polynomial.aeval (relativePower t a b) P=0) :
    ∃ z : ℂ, Polynomial.aeval z P=0 ∧ ‖z‖=relativePower v a b := by
  obtain ⟨e,ω,phase,atomEq,keep⟩ := twisted_evaluation spec
  have mag (n : ℕ+) : ‖e (atom n)‖=shellPower v n := by
    rw [atomEq,norm_mul,phase_norm hm (phase n),one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (shellPower_pos _ _)]
  have nonzero : e (atom b) ≠ 0 := norm_pos_iff.mp (by rw [mag]; exact shellPower_pos v b)
  have src (n : ℕ+) : value t (atom n)=shellPower t n := (value_atom n t).trans (shellPower_exp t n).symm
  have hp : value t (cleared P a b)=0 := by
    rw [eval_cleared (value t) P a b (by rw [src]; exact (shellPower_pos t b).ne'),src,src]
    exact mul_eq_zero_of_right _ root
  have target := keep _ hp
  rw [eval_cleared e P a b nonzero] at target
  exact ⟨_,(mul_eq_zero.mp target).resolve_left (pow_ne_zero _ nonzero),by rw [norm_div,mag,mag,relativePower]⟩

/-- One fixed integral polynomial on an energy gap bounds all forced target
orders across all rational dilations. -/
theorem relative_candidates (a b : ℕ+) (gap : energy b<energy a) {t : ℝ} (ht : 0<t)
    (P : ℤ[X]) (ne : P ≠ 0) (root : Polynomial.aeval (relativePower t a b) P=0) :
    accumulated t ⊆ (P.map (algebraMap ℤ ℂ)).roots.toFinset.image
      (fun z => |log ‖z‖|/(energy a-energy b)) := by
  classical
  rintro u ⟨hu,m,hm,force⟩
  have signed (v : ℝ) (s : TorsionSpecialization m t v) :
      ∃ z ∈ (P.map (algebraMap ℤ ℂ)).roots, |log ‖z‖|/(energy a-energy b)=|v| := by
    obtain ⟨z,hz,mag⟩ := relative_root hm s a b P root
    refine ⟨z,(Polynomial.mem_roots_map_of_injective (Int.cast_injective (α := ℂ)) ne).mpr hz,?_⟩
    rw [mag,relativePower_exp,log_exp,abs_mul,abs_of_pos (sub_pos.mpr gap),
      mul_div_cancel_right₀ _ (sub_pos.mpr gap).ne']
  have existsRoot : ∃ z ∈ (P.map (algebraMap ℤ ℂ)).roots, |log ‖z‖|/(energy a-energy b)=u := by
    rcases (scaled_forcing_iff ht hu hm).mp force with pos | neg
    · simpa only [abs_of_pos hu] using signed u pos
    · simpa only [abs_neg,abs_of_pos hu] using signed (-u) neg
  obtain ⟨z,mem,eq⟩ := existsRoot
  exact Finset.mem_image.mpr ⟨z,Multiset.mem_toFinset.mpr mem,eq⟩

theorem algebraic_gap_finite (a b : ℕ+) (gap : energy b<energy a) {t : ℝ} (ht : 0<t)
    (alg : IsAlgebraic ℚ (relativePower t a b)) : (accumulated t).Finite := by
  obtain ⟨P,ne,root⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr alg
  exact Finset.finite_toSet _ |>.subset (relative_candidates a b gap ht P ne root)

#print axioms relative_root
#print axioms relative_candidates
#print axioms algebraic_gap_finite

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
