import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell.Gibbs

/-! # Binary thermometry on the vacuum, one prime and its square -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell

open Finset Real
open _root_.HTGeometry (finiteGibbsStateWeight)

/-- A probe using only occupations zero, one and two of a single prime. -/
abbrev SquareStates (A B : ℕ) := Fin (A+3*B) ⊕ (Fin (3*A+4*B) ⊕ Fin B)

def squareOccupation (A B : ℕ) : SquareStates A B → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 2))

private def quarters (A B : ℕ) : SquareStates A B → ℝ :=
  Sum.elim (fun _ => -3) (Sum.elim (fun _ => 1) (fun _ => 5))

private theorem square_center (A B : ℕ) :
    centered (levels (squareOccupation A B))=fun i => (1/4 : ℝ)*quarters A B i := by
  have zero : (∑ i, quarters A B i)=0 := by
    simp only [quarters,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have shift : levels (squareOccupation A B)=fun i => (1/4 : ℝ)*quarters A B i+3/4 := by
    funext i
    rcases i with i | (i | i) <;> norm_num [levels,squareOccupation,quarters]
  rw [shift,centered_affine,centered_eq_of_sum_zero zero]

def squareResponse (p : Nat.Primes) (A B : ℕ) (t : ℝ) :=
  oddTrace (centered (primeModes p (squareOccupation A B))) t

private theorem step_two (x k : ℝ) : coordinate (2*x)*oddTerm x k=
    oddTerm x (k+2)+oddTerm x (k-2) := by
  simp only [coordinate,oddTerm,sub_eq_add_neg,mul_add,mul_neg,neg_neg,mul_comm x 2,
    mul_comm (-x) 2,neg_mul,exp_add]
  ring

/-- The nearest three shells give the same rational threshold as the
0, 3, 5 packet at half the damping, times a strictly positive factor. -/
theorem square_response_identity (p : Nat.Primes) (A B : ℕ) (t : ℝ) :
    coordinate (t*log p.val/4)*squareResponse p A B t=response p A B (t/2) := by
  let x := t*log p.val/4
  let Y := coordinate (2*x)
  have first : oddTerm x 1=exp x-exp (-x) := by simp only [oddTerm,mul_one]
  have rev (k : ℝ) : oddTerm x (-k)= -oddTerm x k := by simp only [oddTerm,mul_neg,neg_mul,neg_neg,neg_sub]
  have h₁ : Y*oddTerm x 1=oddTerm x 3-oddTerm x 1 := by
    simpa only [Y,show (1 : ℝ)+2=3 from by ring,show (1 : ℝ)-2= -1 from by ring,rev,sub_eq_add_neg]
      using step_two x 1
  have h₃ : Y*oddTerm x 3=oddTerm x 5+oddTerm x 1 := by
    simpa only [Y,show (3 : ℝ)+2=5 from by ring,show (3 : ℝ)-2=1 from by ring] using step_two x 3
  have triple : oddTerm x 3=(Y+1)*oddTerm x 1 := by linear_combination -h₁
  have five : oddTerm x 5=(Y*(Y+1)-1)*oddTerm x 1 := by
    rw [triple] at h₃; linear_combination -h₃
  have half : t/2*log (p.val : ℝ)=2*x := by dsimp only [x]; ring
  have scale (z : ℝ) : oddTerm t (log p.val*((1/4 : ℝ)*z))=oddTerm x z := by
    unfold oddTerm; congr 2 <;> dsimp only [x] <;> ring
  have double : coordinate x*oddTerm x 1=exp (2*x)-exp (-(2*x)) := by
    rw [coordinate,first,two_mul,neg_add,exp_add,exp_add]; ring
  rw [squareResponse,Sparse.mode_grid,centered_affine,square_center,response_eq,half]
  simp only [oddTrace,scale,quarters,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_const,
    card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,rev,triple,five]
  change coordinate x*_=(exp (2*x)-exp (-(2*x)))*(Y-2)*((B : ℝ)*Y-(A : ℝ))
  rw [← double]
  ring

theorem square_positive_iff (p : Nat.Primes) (A B : ℕ) (t : ℝ) :
    0<squareResponse p A B t ↔ 0<response p A B (t/2) := by
  have pos : 0<coordinate (t*log p.val/4) := add_pos (exp_pos _) (exp_pos _)
  rw [← square_response_identity,mul_pos_iff_of_pos_left pos]

/-- The complete binary response profile of vacuum, prime and square
determines the signed temperature. -/
theorem square_readings_iff (p : Nat.Primes) (t u : ℝ) :
    (∀ A B : ℕ, 0<B → (0<squareResponse p A B t ↔ 0<squareResponse p A B u)) ↔ t=u := by
  simp only [square_positive_iff]
  rw [readings_iff]
  constructor <;> intro h <;> linarith only [h]

def squareLaw (p : Nat.Primes) (A B : ℕ) (s : ℂ) :=
  finiteGibbsStateWeight (2*s.re-1) (primeModes p (squareOccupation A B))

private theorem square_bit (p : Nat.Primes) (A B : ℕ) (s : ℂ) :
    positiveBit (squareLaw p A B s) ↔ 0<squareResponse p A B (2*s.re-1) := by
  let E := primeModes p (squareOccupation A B)
  let d := 2*s.re-1
  have eq := funext (Observation.gibbs_information E d)
  change 0<oddTrace (centered (Observation.information (finiteGibbsStateWeight d E))) 1 ↔
    0<oddTrace (centered E) d
  rw [eq,centered_affine]
  simp only [oddTrace,oddTerm,one_mul,neg_mul]

theorem square_real_part_iff (p : Nat.Primes) (s w : ℂ) :
    (∀ A B : ℕ, 0<B → (positiveBit (squareLaw p A B s) ↔ positiveBit (squareLaw p A B w))) ↔ s.re=w.re := by
  simp only [square_bit]
  rw [square_readings_iff]
  constructor <;> intro h <;> linarith only [h]

theorem square_isometric_iff (p : Nat.Primes) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x=split s f x) ↔
      ∀ A B : ℕ, 0<B → ¬positiveBit (squareLaw p A B s) := by
  rw [split_isometric_iff]
  have test := square_readings_iff p (2*s.re-1) 0
  have zero (A B : ℕ) : squareResponse p A B 0=0 := odd_zero _
  simp only [zero,lt_irrefl,iff_false] at test
  simp only [square_bit]
  rw [test]
  constructor <;> intro h <;> linarith only [h]

#print axioms square_response_identity
#print axioms square_readings_iff
#print axioms square_real_part_iff
#print axioms square_isometric_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ThreeShell
