import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.SpectralSorting.BinaryPhases
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Repeated spectral clocks from disjoint pairs of wires -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.ClockSpectrum
open DiagonalSynthesis SpectralSorting
noncomputable section

/-- Order the register first by the active binary word, then by the
unused word. Each active word labels a consecutive block of size 2^k. -/
def clockOrder (q k : ℕ) : (Fin ((q+q)+k)→Bool) ≃ Fin (2^(q+q)*2^k) :=
  ((Fin.appendEquiv (α:=Bool) (q+q) k).symm.trans
    ((binaryIndex (q+q)).prodCongr (binaryIndex k))).trans finProdFinEquiv

private theorem clock_digit (q k : ℕ) (x : Fin ((q+q)+k)→Bool) :
    (clockOrder q k x).val/2^k=Nat.ofBits (fun i : Fin (q+q) => x (i.castAdd k)) := by
  let p := ((binaryIndex (q+q)).prodCongr (binaryIndex k)) ((Fin.appendEquiv (q+q) k).symm x)
  change (p.2.val+2^k*p.1.val)/2^k=p.1.val
  rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt p.2.isLt,zero_add]

/-- Exactly q two-qubit phase gates suffice to realize a clock with
4^q phases, each repeated 2^k times. The angular step is arbitrary. -/
theorem realizes_repeated_clock (q k : ℕ) (θ : ℝ) :
    Realizes q (diagonal (fun x : Fin ((q+q)+k)→Bool =>
      Complex.exp (Complex.I*(θ:ℂ)*(((clockOrder q k x).val/2^k:ℕ):ℂ)))) := by
  let a (i : Fin q) := (i.castAdd q).castAdd k
  let b (i : Fin q) := (Fin.natAdd q i).castAdd k
  let G (i : Fin q) (p : Bool×Bool) := Complex.exp
    (Complex.I*(θ:ℂ)*(2^i.val*(p.1.toNat:ℂ)+2^(q+i.val)*(p.2.toNat:ℂ)))
  have hd (i : Fin q) : a i≠b i := by
    intro h
    have e := congrArg Fin.val h
    change i.val=q+i.val at e
    have := i.isLt
    omega
  have hf := realizes_phase_product Finset.univ (fun i (x : Fin ((q+q)+k)→Bool) => G i (x (a i),x (b i)))
    (fun i _ => realizes_pair_phase (a i) (b i) (hd i) (G i) (fun p => by simp [G,Complex.norm_exp,binary_weight_im]))
  have he (x : Fin ((q+q)+k)→Bool) : (∏ i : Fin q, G i (x (a i),x (b i))) =
      Complex.exp (Complex.I*(θ:ℂ)*(((clockOrder q k x).val/2^k:ℕ):ℂ)) := by
    rw [clock_digit,binary_sum,Fin.sum_univ_add]
    push_cast
    simp only [G,a,b,←Complex.exp_sum,←Finset.mul_sum,Finset.sum_add_distrib,Fin.val_castAdd,Fin.val_natAdd]
  simpa only [Finset.card_univ,Fintype.card_fin,he] using hf

#print axioms realizes_repeated_clock
end
end GaloisForLFunctions.HTGeometry.ClockSpectrum
