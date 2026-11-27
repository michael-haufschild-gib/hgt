import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.LocalCommutator
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.PhysicalEcho
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.OnsiteOperatorDistance
import GaloisForLFunctions.HTGeometry.FinitePauliConjugationLaw

/-! # Onsite fields reversed by a Pauli word reached on the orbit -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section

private def sign {n : ℕ} (Q : Fin (n+2) → Option (Fin 3)) (l : PathLabel n) : ℝ :=
  if finitePauliConjugationSign Q (pathWord l)=1 then 1 else -1

private theorem cast_sign {n : ℕ} (Q : Fin (n+2) → Option (Fin 3)) (l : PathLabel n) :
    (sign Q l:ℂ)=finitePauliConjugationSign Q (pathWord l) := by
  have h := finitePauliConjugationSign_sq Q (pathWord l)
  rcases sq_eq_one_iff.mp (by rwa [pow_two] : finitePauliConjugationSign Q (pathWord l)^2=1)
    with h'|h' <;> norm_num [sign,h']

private def signedShell {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3)) : PathShell n :=
  WithLp.toLp 2 (fun l => u l*sign Q l)

private theorem signed_norm {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3)) :
    ‖signedShell u Q‖^2=‖u‖^2 := by
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  apply sum_congr rfl
  intro l _
  change ‖u l*sign Q l‖^2=‖u l‖^2
  unfold sign
  split <;> simp

private theorem signed_matrix {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3)) :
    finitePauliMatrix Q*pathHamiltonian u*star (finitePauliMatrix Q)=pathHamiltonian (signedShell u Q) := by
  rw [(finitePauliMatrix_isHermitian Q).isSelfAdjoint.star_eq,pathHamiltonian_eq_sum u,
    pathHamiltonian_eq_sum (signedShell u Q),Finset.mul_sum,Finset.sum_mul]
  refine sum_congr rfl fun l _ => ?_
  change _=(((u l*sign Q l:ℝ):ℂ)) • finitePauliMatrix (pathWord l)
  rw [Matrix.mul_smul,Matrix.smul_mul,finitePauliMatrix_conj,smul_smul,Complex.ofReal_mul,cast_sign]

private theorem onsite_sign {n : ℕ} (Q : Fin (n+2) → Option (Fin 3)) (s : Fin (n+2)) (j : Fin 3)
    (hQ : Q s ≠ none) (hj : Q s ≠ some j) : sign Q (.inl (s,j))= -1 := by
  have he : finitePauliConjugationSign Q (onsiteWord s j)= -1 := by
    unfold finitePauliConjugationSign
    rw [prod_eq_single s]
    · simp [onsiteWord,boolPauliConjugationSign,hQ,hj]
    · intro i _ hi
      simp [onsiteWord,hi,boolPauliConjugationSign]
    · simp
  norm_num [sign,pathWord,he]

/-- Locality bounds the commutator of a Pauli conjugate, while opposite
product-spin readings measure the field components reversed by the word. -/
theorem transverse_of_rotation {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3))
    (S : Finset (Fin (n+2))) (j : Fin (n+2) → Fin 3)
    (ha : ∀ s ∈ S, Q s ≠ none ∧ Q s ≠ some (j s)) {f : ℝ}
    (h : let H := pathHamiltonian u
         let B := finitePauliMatrix Q*H*star (finitePauliMatrix Q)
         4*f*‖H-B‖^2 ≤ π^2*‖H*B-B*H‖) :
    16*f*(∑ s ∈ S, |u (.inl (s,j s))|)^2 ≤ 84*π^2*‖u‖^2 := by
  let v := signedShell u Q
  let H := pathHamiltonian u
  let B := pathHamiltonian v
  change 4*f*‖H-(finitePauliMatrix Q*H*star (finitePauliMatrix Q))‖^2 ≤ _ at h
  rw [show finitePauliMatrix Q*H*star (finitePauliMatrix Q)=B from signed_matrix u Q] at h
  have hc := path_pair_commutator u v
  rw [show ‖v‖^2=‖u‖^2 from signed_norm u Q] at hc
  have hfield := signed_onsite_sum_le_pathHamiltonian_dist u v j
  have he (s) (hs : s ∈ S) :
      |u (.inl (s,j s))-v (.inl (s,j s))|=2*|u (.inl (s,j s))| := by
    change |u _-u _*sign Q _|=_
    rw [onsite_sign Q s (j s) (ha s hs).1 (ha s hs).2,mul_neg_one,sub_neg_eq_add,←two_mul,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hl : 2*(∑ s ∈ S, |u (.inl (s,j s))|) ≤ ‖H-B‖ := by
    rw [mul_sum]
    exact (sum_congr rfl fun s hs => (he s hs).symm).le.trans
      ((sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => abs_nonneg _)).trans hfield)
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num) (sum_nonneg fun _ _ => abs_nonneg _)) hl 2
  by_cases hd : 0 ≤ f
  · have hsmall := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hd)
    have hright := (hsmall.trans h).trans (mul_le_mul_of_nonneg_left hc (sq_nonneg π))
    linarith only [hright]
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
      (by norm_num) (le_of_not_ge hd)) (sq_nonneg _)).trans (by positivity)

/-- Reversing a large total transverse field forces a Pauli word far from
all physical dates. Either transverse component can be chosen at each site. -/
theorem pauli_transverse_price {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3))
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (S : Finset (Fin (n+2))) (j : Fin (n+2) → Fin 3)
    (ha : ∀ s ∈ S, Q s ≠ none ∧ Q s ≠ some (j s)) :
    16*(1-‖unitaryEvolution (pathHamiltonian u) t-z • finitePauliMatrix Q‖)*(∑ s ∈ S, |u (.inl (s,j s))|)^2 ≤ 84*π^2*‖u‖^2 := by
  let V : unitaryGroup (Fin (n+2) → Bool) ℂ := ⟨finitePauliMatrix Q,finitePauliMatrix_mem_unitary Q⟩
  exact transverse_of_rotation u Q S j ha
    (physical_energy_rotation ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ V t z hz)

/-- Every Pauli word fitted at error 1/4 reverses only a small total
onsite field. At each active site one may choose either transverse
component after observing the entire chain and the proposed word. -/
theorem pauli_transverse_fields {n : ℕ} (u : PathShell n) (Q : Fin (n+2) → Option (Fin 3))
    (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    (hfit : ‖unitaryEvolution (pathHamiltonian u) t-z • finitePauliMatrix Q‖ ≤ 1/4)
    (S : Finset (Fin (n+2))) (j : Fin (n+2) → Fin 3)
    (ha : ∀ s ∈ S, Q s ≠ none ∧ Q s ≠ some (j s)) :
    12*(∑ s ∈ S, |u (.inl (s,j s))|)^2 ≤ 84*π^2*‖u‖^2 := by
  have h := pauli_transverse_price u Q t z hz S j ha
  exact (mul_le_mul_of_nonneg_right (by linarith only [hfit] :
    (12:ℝ) ≤ 16*(1-‖unitaryEvolution (pathHamiltonian u) t-z • finitePauliMatrix Q‖)) (sq_nonneg _)).trans h

#print axioms pauli_transverse_fields
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
