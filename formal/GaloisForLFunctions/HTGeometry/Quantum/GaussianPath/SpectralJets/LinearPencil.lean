import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.TraceGram
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Numerators
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-! # Characteristic polynomials and cleared derivative rows of a linear matrix family -/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι R : Type*} [Fintype ι] [CommRing R] {D : ℕ}

/-- The matrix of the linear family in the coupling indeterminates. -/
def pencil (A : ι → Matrix (Fin D) (Fin D) R) : Matrix (Fin D) (Fin D) (MvPolynomial ι R) :=
  fun i j => ∑ a, X a * C (A a i j)

/-- The joint characteristic determinant in the root and the couplings. -/
def characteristic (A : ι → Matrix (Fin D) (Fin D) R) : MvPolynomial (Option ι) R :=
  (Matrix.of fun i j => (if i=j then X none else 0) - ∑ a, X (some a) * C (A a i j)).det

theorem pencil_degree [Nontrivial R] (A : ι → Matrix (Fin D) (Fin D) R) (i j) :
    (pencil A i j).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro a _
  simpa only [totalDegree_X,totalDegree_C,add_zero] using totalDegree_mul (X a) (C (A a i j))

theorem characteristic_degree [Nontrivial R] (A : ι → Matrix (Fin D) (Fin D) R) :
    (characteristic A).totalDegree ≤ D := by
  apply le_trans (determinant_degree _ 1 ?_) (Nat.mul_one _).le
  intro i j
  change ((_ - _) : MvPolynomial (Option ι) R).totalDegree ≤ 1
  apply (totalDegree_sub _ _).trans
  apply max_le
  · split <;> simp
  · apply totalDegree_finsetSum_le
    intro a _
    simpa only [totalDegree_X,totalDegree_C,add_zero] using totalDegree_mul (X (some a)) (C (A a i j))

theorem eval_pencil {S : Type*} [CommRing S] (A : ι → Matrix (Fin D) (Fin D) R)
    (φ : R →+* S) (z : ι → S) :
    (eval₂Hom φ z).mapMatrix (pencil A) = ∑ a, z a • (A a).map φ := by
  ext i j
  simp [RingHom.mapMatrix_apply,pencil,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]

theorem eval_characteristic (A : ι → Matrix (Fin D) (Fin D) R)
    (φ : R →+* ℂ) (z : ι → ℂ) (y : ℂ) :
    eval₂Hom φ (fun o : Option ι => o.elim y z) (characteristic A) =
      matrixCharpolyRelation (∑ a, z a • (A a).map φ,y) := by
  rw [characteristic,RingHom.map_det,matrixCharpolyRelation]
  apply congrArg Matrix.det
  ext i j
  by_cases hij : i=j <;> simp [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.scalar_apply,
    Matrix.sum_apply,Matrix.smul_apply,hij]

/-- An absent word denotes the constant row. A present word, including the
empty word, denotes the corresponding derivative of the root. -/
def jetRow (p : MvPolynomial (Option ι) R) (L : ℕ) :
    Option (List ι) → MvPolynomial (Option ι) R
  | none => (pderiv none p)^(2*L)
  | some w => cleared p L w

omit [Fintype ι] in
theorem jetRow_degree [Nontrivial R] (p : MvPolynomial (Option ι) R) (L : ℕ)
    (w : Option (List ι)) (hw : ∀ v ∈ w, v.length ≤ L) :
    (jetRow p L w).totalDegree ≤ 1+2*L*p.totalDegree := by
  cases w with
  | none =>
    exact ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (totalDegree_partial_le none p))).trans (Nat.le_add_left ..)
  | some w => exact cleared_degree p L w (hw w rfl)

/-- The integral polynomial whose value is the squared cleared determinant. -/
def jetGram (A : ι → Matrix (Fin D) (Fin D) R) (L : ℕ) (rows : Fin D → Option (List ι)) :=
  gram (pencil A) (fun j => jetRow (characteristic A) L (rows j))

theorem jetGram_degree [Nontrivial R] (A : ι → Matrix (Fin D) (Fin D) R) (L : ℕ)
    (rows : Fin D → Option (List ι)) (hw : ∀ j v, v ∈ rows j → v.length ≤ L) :
    (jetGram A L rows).totalDegree ≤ D*(2*(1+2*L*D)) := by
  apply gram_degree _ (pencil_degree A)
  intro j
  exact (jetRow_degree _ _ _ (hw j)).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (characteristic_degree A)) 1)

omit [Fintype ι] in
/-- Formal differential numerators commute with extension of scalars. -/
private theorem numerator_map {S : Type*} [CommRing S] (φ : R →+* S)
    (p : MvPolynomial (Option ι) R) (w : List ι) :
    map φ (numerator p w) = numerator (map φ p) w := by
  induction w with
  | nil => simp [numerator]
  | cons i w ih =>
    simp only [numerator,tangent,map_sub,map_mul,map_nsmul,pderiv_map,← ih]

omit [Fintype ι] in
theorem jetRow_map {S : Type*} [CommRing S] (φ : R →+* S)
    (p : MvPolynomial (Option ι) R) (L : ℕ) (w : Option (List ι)) :
    map φ (jetRow p L w) = jetRow (map φ p) L w := by
  cases w <;> simp only [jetRow,cleared,map_mul,map_pow,pderiv_map,numerator_map]

#print axioms jetGram_degree
end
end GaloisForLFunctions.HTGeometry.SpectralJets
