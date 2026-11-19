import GaloisForLFunctions.HTGeometry.StokesWeylFourierSource
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Polynomial momentum jumps in the Weyl algebra

A jump depending on momentum differentiates once against its conjugate coordinate.
Consequently the highest nonzero commutator on the nth coordinate power is a
factorial times the nth power of the jump derivative. For a position square
this gives the heating symbol in Donadi–Lobo–Fadel, equations (9)–(17).
-/

noncomputable section
namespace GaloisForLFunctions.PolynomialJump

open Polynomial
variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Commutator with the polynomial jump or conjugate coordinate. -/
def bracket (F B : A) : A := F*B-B*F

theorem bracket_add (F a b : A) :
    bracket F (a+b) = bracket F a + bracket F b := by
  unfold bracket
  noncomm_ring

theorem bracket_mul (F a b : A) :
    bracket F (a*b) = bracket F a*b+a*bracket F b := by
  unfold bracket
  noncomm_ring

private theorem bracket_nsmul (F a : A) (n : ℕ) :
    bracket F (n • a) = n • bracket F a := by
  simp [bracket,mul_smul_comm,smul_mul_assoc,smul_sub]

private theorem bracket_vanishes {F B : A} (h : Commute F B) : bracket F B = 0 :=
  sub_eq_zero.mpr h

private theorem eval_commute (P : A) (f g : ℂ[X]) : Commute (aeval P f) (aeval P g) :=
  (Commute.all f g).map (aeval P).toRingHom

/-- A central canonical commutator differentiates the full polynomial functional calculus. -/
theorem conjugate_polynomial {Q P : A} {k : ℂ} (h : bracket Q P = k • (1:A))
    (f : ℂ[X]) : bracket Q (aeval P f) = k • aeval P f.derivative := by
  induction f using Polynomial.induction_on with
  | C c =>
    rw [aeval_C,derivative_C,map_zero,smul_zero]
    exact bracket_vanishes (Algebra.commutes c Q).symm
  | add f g hf hg => simp only [map_add,bracket_add,hf,hg,smul_add]
  | monomial n c ih =>
    rw [pow_succ,← mul_assoc,derivative_mul,derivative_X,mul_one,map_add,map_mul,aeval_X,
      bracket_mul,ih,h]
    simp only [map_mul,aeval_X,smul_add,smul_mul_assoc,mul_smul_comm,mul_one]

/-- A nonzero scalar commutator precludes every nonzero polynomial relation on momentum. -/
theorem canonical_aeval_injective [Nontrivial A] {Q P : A} {k : ℂ}
    (hk : k ≠ 0) (h : bracket Q P = k • (1:A)) :
    Function.Injective (aeval P : ℂ[X] →ₐ[ℂ] A) := by
  have ker (f : ℂ[X]) (hf : aeval P f = 0) : f = 0 := by
    induction d : f.natDegree using Nat.strong_induction_on generalizing f with
    | h d ih =>
      have hc : f = C (f.coeff 0) := by
        by_cases hz : f.natDegree = 0
        · exact eq_C_of_natDegree_eq_zero hz
        apply eq_C_of_derivative_eq_zero
        have hd := conjugate_polynomial h f
        rw [hf] at hd
        have hzero : k • aeval P f.derivative = 0 := by simpa [bracket] using hd.symm
        have hlt := natDegree_derivative_lt hz
        exact ih _ (by omega) _ ((smul_eq_zero.mp hzero).resolve_left hk) rfl
      have ha : algebraMap ℂ A (f.coeff 0) = 0 := by
        rw [← aeval_C P,← hc,hf]
      exact hc.trans (by rw [(algebraMap ℂ A).injective (ha.trans (map_zero _).symm),map_zero])
  intro f g hfg
  exact sub_eq_zero.mp (ker (f-g) (by rw [map_sub,hfg,sub_self]))

/-- If the commutator of F with Q is fixed, the iterated Leibniz rule on BQ
has only the two terms in which Q is differentiated zero or one times. -/
private theorem iterate_product (F Q : A) (h : bracket F (bracket F Q) = 0) (B : A) (n : ℕ) :
    (bracket F)^[n+1] (B*Q) = (bracket F)^[n+1] B*Q +
      (n+1) • ((bracket F)^[n] B * bracket F Q) := by
  induction n with
  | zero => simpa using bracket_mul F B Q
  | succ n ih =>
    rw [Function.iterate_succ_apply' _ (n+1),ih,bracket_add,bracket_mul,bracket_nsmul,
      bracket_mul,h,mul_zero,add_zero,← Function.iterate_succ_apply',
      ← Function.iterate_succ_apply']
    rw [succ_nsmul]
    abel

/-- The factorial commutator of a coordinate power and annihilation at the next order. -/
theorem highest_commutator {F Q : A} (h : Commute F (bracket F Q)) (n : ℕ) :
    (bracket F)^[n] (Q^n) = n.factorial • (bracket F Q)^n ∧
    (bracket F)^[n+1] (Q^n) = 0 := by
  have top (j : ℕ) (ht : (bracket F)^[j] (Q^j) = j.factorial • (bracket F Q)^j) :
      (bracket F)^[j+1] (Q^j) = 0 := by
    rw [Function.iterate_succ_apply',ht,bracket_nsmul,bracket_vanishes (h.pow_right j),smul_zero]
  induction n with
  | zero =>
    have hz : (bracket F)^[0] (Q^0) = Nat.factorial 0 • (bracket F Q)^0 := by simp
    exact ⟨hz,top _ hz⟩
  | succ n ih =>
    have hs : (bracket F)^[n+1] (Q^(n+1)) =
        (n+1).factorial • (bracket F Q)^(n+1) := by
      rw [pow_succ,iterate_product F Q (bracket_vanishes h),ih.2,ih.1,zero_mul,zero_add,
        smul_mul_assoc,← pow_succ,Nat.factorial_succ,mul_smul]
    exact ⟨hs,top _ hs⟩

/-- Degree-n endpoint for a momentum-dependent jump, including constant jumps. -/
theorem polynomial_highest {Q P : A} {k : ℂ} (h : bracket Q P = k • (1:A))
    (f : ℂ[X]) (n : ℕ) :
    (bracket (aeval P f))^[n] (Q^n) =
      n.factorial • (aeval P (C (-k) * f.derivative))^n ∧
    (bracket (aeval P f))^[n+1] (Q^n) = 0 := by
  have hk : bracket (aeval P f) Q = aeval P (C (-k)*f.derivative) := by
    rw [map_mul,aeval_C,← Algebra.smul_def,neg_smul,← conjugate_polynomial h]
    unfold bracket
    exact (neg_sub _ _).symm
  have hc : Commute (aeval P f) (bracket (aeval P f) Q) := by
    rw [hk]
    exact eval_commute P _ _
  simpa only [hk] using highest_commutator hc n

open IrregularStokes.WeylFourier

private theorem weyl_relation : bracket D X = (1:ℂ) • (1:WeylAlgebra) := by
  simpa [bracket] using D_mul_X_sub_X_mul_D

/-- In the presented Weyl algebra the top commutator and its cutoff hold for all orders. -/
theorem weyl_top (f : ℂ[X]) (n : ℕ) :
    (bracket (aeval X f))^[n] (D^n) = n.factorial • (aeval X (-f.derivative))^n ∧
    (bracket (aeval X f))^[n+1] (D^n) = 0 := by
  simpa using polynomial_highest weyl_relation f n

/-- The unique polynomial giving the double commutator on D² has degree
2(deg f − 1). A quadratic momentum observable suffices exactly up to degree two. -/
theorem weyl_square_closure (f : ℂ[X]) :
    (∃ g : ℂ[X], g.natDegree ≤ 2 ∧
      (bracket (aeval X f))^[2] (D^2) = aeval X g) ↔ f.natDegree ≤ 2 := by
  have he : (bracket (aeval X f))^[2] (D^2) = aeval X (2 * f.derivative^2) := by
    have he := (weyl_top f 2).1
    simpa [Nat.factorial_succ,two_nsmul,pow_two,two_mul] using he
  have hd : (2 * f.derivative^2).natDegree = 2*(f.natDegree-1) := by
    rw [show (2 : ℂ[X]) = C 2 by simp, natDegree_C_mul (by norm_num : (2:ℂ) ≠ 0),
      natDegree_pow,natDegree_derivative]
  rw [he]
  constructor
  · rintro ⟨g,hg,h⟩
    have hpoly := canonical_aeval_injective one_ne_zero weyl_relation h
    rw [← hpoly,hd] at hg
    omega
  · intro hf
    exact ⟨_,by rw [hd]; omega,rfl⟩

end GaloisForLFunctions.PolynomialJump
