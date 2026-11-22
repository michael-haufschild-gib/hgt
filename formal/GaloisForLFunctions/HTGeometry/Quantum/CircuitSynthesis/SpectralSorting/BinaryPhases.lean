import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.TwoWirePhases
import GaloisForLFunctions.QuantumAlg.Util.FinPow
import Batteries.Data.Fin.OfBits

/-! # Linear and controlled linear phases on the binary register -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralSorting
noncomputable section
open DiagonalSynthesis

/-- The binary integer whose least significant bit is at site zero. -/
def binaryIndex (n : ℕ) : (Fin n→Bool) ≃ Fin (2^n) where
  toFun := Fin.ofBits
  invFun y i := y.val.testBit i
  left_inv x := funext fun i => Nat.testBit_ofBits_lt x i.val i.isLt
  right_inv y := Fin.ext ((Nat.ofBits_testBit ..).trans (Nat.mod_eq_of_lt y.isLt))

theorem binary_sum {n : ℕ} (x : Fin n→Bool) :
    Nat.ofBits x=∑ i : Fin n, 2^i.val*(x i).toNat := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [QuantumAlg.nat_ofBits_succ_last,Fin.sum_univ_castSucc,ih]
    rfl

/-- A binary-angle phase is a product of one phase per bit. The
parameter can be an arbitrary real number. -/
theorem realizes_binary_phase {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) (p : Equiv.Perm (Fin n)) :
    Realizes n (diagonal (fun x : Fin n→Bool => Complex.exp
      (Complex.I*(θ:ℂ)*(Nat.ofBits (x ∘ p):ℂ)))) := by
  let f (i : Fin n) (b : Bool) := Complex.exp (Complex.I*(θ:ℂ)*2^i.val*(b.toNat:ℂ))
  have h := realizes_phase_product Finset.univ (fun i (x : Fin n→Bool) => f i (x (p i)))
    (fun i _ => realizes_single_phase hn (p i) (f i) (fun b => by simp [f,Complex.norm_exp]))
  have he (x : Fin n→Bool) : (∏ i, f i (x (p i))) =
      Complex.exp (Complex.I*(θ:ℂ)*(Nat.ofBits (x ∘ p):ℂ)) := by
    rw [binary_sum]
    push_cast
    simp only [Finset.mul_sum,Function.comp_apply,f,←Complex.exp_sum,mul_assoc]
  simpa only [Finset.card_univ,Fintype.card_fin,he] using h

/-- Applying the binary phase to the low n bits conditional on the high
bit needs n ordinary two-qubit gates. -/
theorem realizes_twiddle (n : ℕ) (θ : ℝ) :
    Realizes n (diagonal (fun x : Fin (n+1)→Bool => Complex.exp (Complex.I*(θ:ℂ)*
      ((x (Fin.last n)).toNat:ℂ)*(Nat.ofBits (x ∘ Fin.castSucc):ℂ)))) := by
  let f (i : Fin n) (p : Bool×Bool) := Complex.exp (Complex.I*(θ:ℂ)*(p.2.toNat:ℂ)*2^i.val*(p.1.toNat:ℂ))
  have h := realizes_phase_product Finset.univ (fun i (x : Fin (n+1)→Bool) => f i (x i.castSucc,x (Fin.last n)))
    (fun i _ => realizes_pair_phase i.castSucc (Fin.last n) (Fin.castSucc_ne_last i)
      (f i) (fun p => by simp [f,Complex.norm_exp]))
  have he (x : Fin (n+1)→Bool) : (∏ i, f i (x i.castSucc,x (Fin.last n))) =
      Complex.exp (Complex.I*(θ:ℂ)*((x (Fin.last n)).toNat:ℂ)*(Nat.ofBits (x ∘ Fin.castSucc):ℂ)) := by
    rw [binary_sum]
    push_cast
    simp only [Finset.mul_sum,Function.comp_apply,f,←Complex.exp_sum,mul_assoc]
  simpa only [Finset.card_univ,Fintype.card_fin,he] using h

#print axioms realizes_twiddle
end
end GaloisForLFunctions.HTGeometry.SpectralSorting
