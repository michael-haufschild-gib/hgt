import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.SquareWords
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.AllOrders
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.LocalError

/-! # High-order short pulses for a sparse spectral generator -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
open private compile_word from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.WordStep
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

/-- Each increase in contact order triples the length of a sparse Pauli
pulse. The constants in its short-time error depend on the generator
and contact order alone. -/
theorem high_order_words {n : ℕ} (hn : 2 ≤ n) {I : Type*} [Fintype I]
    (P : I → Fin n → Option (Fin 3)) (a : I → ℝ) (k j : ℕ) (hk : ∀ i, pauliWeight (P i) ≤ k) :
    let H := ∑ i, a i • finitePauliMatrix (P i)
    ∃ B>0, ∃ δ>0, ∀ t : ℝ, |t| ≤ δ → HasProjectiveCircuitApproximation n (B*|t|^(j+2))
      (3^j*Fintype.card I*(2*k+1)) (unitaryEvolution H t) := by
  classical
  intro H
  let X (i : I) := a i • ((-Complex.I) • finitePauliMatrix (P i))
  let e := (Fintype.equivFin I).symm
  let Z := List.ofFn (fun l => X (e l))
  have hZ : Z.sum=(-Complex.I) • H := by
    dsimp only [Z,H]
    rw [List.sum_ofFn,Equiv.sum_comp e X,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  obtain ⟨w,hcont,huses,hlen,_⟩ := ProductFormula.exists_word Z j
  let K := 1+ProductFormula.mass w+‖Z.sum‖
  have hmass := ProductFormula.mass_nonneg w
  have hnorm := norm_nonneg Z.sum
  have hK : 0 < K := by dsimp only [K]; linarith only [hmass,hnorm]
  refine ⟨6*K^(j+2),by positivity,1/K,one_div_pos.mpr hK,?_⟩
  intro t ht
  have htime : ‖(t:ℂ)‖*K ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact (le_div_iff₀ hK).mp ht
  have herr := ProductFormula.contact_error hcont hK
    (show ProductFormula.mass w ≤ K by dsimp only [K]; linarith only [hnorm])
    (show ‖Z.sum‖ ≤ K by dsimp only [K]; linarith only [hmass]) htime
  have hc (y : Reg n) (hy : y ∈ w) : ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount ≤ 2*k+1 ∧ exp (t • y)=c • (C.eval : Reg n) := by
    obtain ⟨x,hx,b,rfl⟩ := huses y hy
    obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hx
    let i := e l
    obtain ⟨c,hc,C,hC,he⟩ := exists_projective_pauli_rotation_circuit hn (P i) ((t*b)*a i)
    refine ⟨c,hc,C,hC.trans (by have h := hk i; omega),?_⟩
    change exp (t • ((b:ℂ) • (a i • ((-Complex.I) • finitePauliMatrix (P i)))))=_
    rwa [Complex.coe_smul,smul_smul,smul_smul]
  obtain ⟨c,hc,C,hgate,hword⟩ := compile_word w t (2*k+1) hc
  rw [hlen,show Z.length=Fintype.card I from List.length_ofFn] at hgate
  simp only [ProductFormula.word,Complex.coe_smul,hword,hZ,Complex.norm_real,Real.norm_eq_abs] at herr
  refine ⟨c,hc,C,hgate,(norm_sub_rev ..).le.trans (herr.trans_eq ?_)⟩
  rw [mul_pow]
  ring

/-- The degree-two control preserves a quadratic gate budget at every
fixed contact order, including order three and above. -/
theorem high_order_square {n : ℕ} (u : PathShell n) (a : ℝ) (j : ℕ) :
    ∃ B>0, ∃ δ>0, ∀ t : ℝ, |t| ≤ δ → HasProjectiveCircuitApproximation (n+2) (B*|t|^(j+2))
      (3^j*(Fintype.card (PathLabel n)+1)^2*9)
      (unitaryEvolution ((pathHamiltonian u-(a:ℂ) • (1:Reg (n+2)))^2) t) := by
  obtain ⟨P,c,hp,he⟩ := shifted_square_words u a
  have h := high_order_words (by omega : 2 ≤ n+2) P c 4 j hp
  rw [←he] at h
  simpa only [Fintype.card_prod,Fintype.card_option,sq] using h

#print axioms high_order_square
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
