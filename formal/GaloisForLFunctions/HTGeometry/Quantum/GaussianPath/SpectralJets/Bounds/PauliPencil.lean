import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ClearedRows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.PauliDetector
import GaloisForLFunctions.HTGeometry.DirectionalVandermondeQuantitativePhaseJet

/-! # Explicit modulus bounds for the path Pauli characteristic pencil -/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- Characteristic-polynomial bound on the joint polydisc of root and couplings. -/
theorem characteristic_box_bound {n D : ℕ} {S : Type*} [CommRing S]
    (A : Fin n → Matrix (Fin D) (Fin D) S) (φ : S →+* ℂ)
    (hA : ∀ a i j, ‖φ (A a i j)‖ ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    BoxBound (MvPolynomial.map φ (characteristic A)) R (D.factorial*((n+1)*R)^D) := by
  intro x hx
  let z (i : Fin n) := x (some i)
  have hchar := eval_characteristic A φ z (x none)
  have hx' : (fun o : Option (Fin n) => o.elim (x none) z) = x := funext fun o => by cases o <;> rfl
  rw [hx'] at hchar
  rw [eval_map]
  change ‖eval₂Hom φ x (characteristic A)‖ ≤ _
  rw [hchar,matrixCharpolyRelation]
  apply norm_det_le_factorial_mul_pow _ (by positivity)
  intro i j
  rw [Matrix.sub_apply]
  have hd : ‖Matrix.scalar (Fin D) (x none) i j‖ ≤ R := by
    by_cases h : i=j <;> simp [Matrix.scalar_apply,h,hR,hx]
  have he (a : Fin n) : ‖(z a • (A a).map φ) i j‖ ≤ R := by
    simp only [Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,norm_mul]
    exact (mul_le_mul (hx (some a)) (hA a i j) (norm_nonneg _) hR).trans_eq (mul_one R)
  have hsum : ‖(∑ a, z a • (A a).map φ) i j‖ ≤ n*R := by
    rw [Matrix.sum_apply]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => he a).trans_eq (by simp [nsmul_eq_mul]))
  exact (norm_sub_le _ _).trans ((add_le_add hd hsum).trans_eq (by ring))

private theorem pauli_local_entry_le_one (p : Option (Fin 3)) (x y : Bool) :
    ‖boolPauliOptionEntry p (x,y)‖ ≤ 1 := by
  change ‖boolPauliOption p x y‖ ≤ 1
  cases p with
  | none => cases x <;> cases y <;> simp [boolPauliOption]
  | some j => fin_cases j <;> cases x <;> cases y <;> simp [boolPauliOption,finiteQubitPauli]

/-- All entries in a numbered path generator have modulus at most one. -/
theorem path_entry_le_one (N : ℕ) (a : Coordinates N) (i j : Fin (2^N)) :
    ‖chainPauliFin N a i j‖ ≤ 1 := by
  unfold chainPauliFin
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply,finitePauliMatrix,norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => pauli_local_entry_le_one _ _ _)

/-- Characteristic-polynomial cap on the enlarged box used in the Cauchy argument. -/
def pencilCap (N : ℕ) (R : ℝ) : ℝ :=
  (2^N).factorial * (((Fintype.card (ChainLabel N) : ℝ)+1)*R)^(2^N)

theorem one_le_pencilCap (N : ℕ) {R : ℝ} (hR : 1 ≤ R) : 1 ≤ pencilCap N R := by
  apply one_le_mul_of_one_le_of_one_le
  · exact_mod_cast Nat.factorial_pos (2^N)
  · apply one_le_pow₀
    exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hR

theorem path_characteristic_box_bound (N : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    BoxBound (MvPolynomial.map GaussianInt.toComplex (characteristic (integralGenerators N))) R (pencilCap N R) := by
  apply characteristic_box_bound (integralGenerators N) GaussianInt.toComplex _ hR
  intro a i j
  change ‖(integralGenerators N a).map GaussianInt.toComplex i j‖ ≤ 1
  rw [generators_map]
  exact path_entry_le_one N a i j

/-- Uniform cap for every cleared row of the specified order budget. -/
theorem path_jetRow_box_bound (N L : ℕ) {r R : ℝ} (hR : 1 ≤ R) (hm : r+(L:ℝ)+2 ≤ R)
    (w : Option (List (Coordinates N))) (hw : ∀ v ∈ w, v.length ≤ L) :
    BoxBound (jetRow (MvPolynomial.map GaussianInt.toComplex (characteristic (integralGenerators N))) L w)
      r (R*(2+4*(L:ℝ))^L*(pencilCap N R)^(2*L)) :=
  jetRow_box_bound _ (path_characteristic_box_bound N (zero_le_one.trans hR)) hR (one_le_pencilCap N hR) L hm w hw

#print axioms path_jetRow_box_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets
