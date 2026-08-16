import GaloisForLFunctions.HTGeometry.StabilizerPauliProduct

/-!
# The stabilizer projector of a commuting family and its Pauli expansion

The sign-weighted local projectors of a commuting family of Pauli matrices commute, so their product
is again a projector.  Expanding the product over subsets exhibits it as the average over the
subset-sum Pauli matrices weighted by the subset sign and the product sign.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ} {b : Fin n → PauliSymp n}

/-- The sign-weighted local projector attached to one member of the family. -/
def stabFactor (b : Fin n → PauliSymp n) (ε : Fin n → ZMod 2) (i : Fin n) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  (2 : ℂ)⁻¹ • (1 + signOf (ε i) • pauliMat (b i))

theorem commute_stabFactor (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    (i j : Fin n) : Commute (stabFactor b ε i) (stabFactor b ε j) := by
  have hQ : Commute (pauliMat (b i)) (pauliMat (b j)) := commute_pauliMat (hb i j)
  have h1 : Commute (signOf (ε i) • pauliMat (b i)) (signOf (ε j) • pauliMat (b j)) :=
    (hQ.smul_left _).smul_right _
  have h2 : Commute ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε i) • pauliMat (b i))
      ((1 : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) + signOf (ε j) • pauliMat (b j)) :=
    Commute.add_left (Commute.one_left _) (Commute.add_right (Commute.one_right _) h1)
  exact (h2.smul_left _).smul_right _

/-- The subset expansion of the stabilizer projector. -/
def stabExpansion (b : Fin n → PauliSymp n) (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) (T : Finset (Fin n)) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  ∑ S ∈ T.powerset, signOf (∑ i ∈ S, ε i) • stabProd b hb S

/-- The product of the local projectors over a subset. -/
def stabProjectorOn (b : Fin n → PauliSymp n) (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) (T : Finset (Fin n)) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  T.noncommProd (stabFactor b ε) fun i _ j _ _ => commute_stabFactor hb ε i j

theorem stabProjectorOn_empty (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2) :
    stabProjectorOn b hb ε ∅ = 1 :=
  Finset.noncommProd_empty _ _

theorem stabProjectorOn_insert (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    {a : Fin n} {T : Finset (Fin n)} (ha : a ∉ T) :
    stabProjectorOn b hb ε (insert a T) = stabFactor b ε a * stabProjectorOn b hb ε T := by
  classical
  rw [stabProjectorOn, stabProjectorOn]
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ ha

theorem stabExpansion_insert (hb : ∀ i j, symForm (b i) (b j) = 0) (ε : Fin n → ZMod 2)
    {a : Fin n} {T : Finset (Fin n)} (ha : a ∉ T) :
    stabExpansion b hb ε (insert a T) = stabExpansion b hb ε T +
      ∑ S ∈ T.powerset, signOf (∑ i ∈ insert a S, ε i) • stabProd b hb (insert a S) := by
  classical
  rw [stabExpansion, stabExpansion, Finset.powerset_insert, Finset.sum_union, Finset.sum_image]
  · intro S hS S' hS' hSS'
    have hSa : a ∉ S := fun hc => ha (Finset.mem_powerset.mp hS hc)
    have hS'a : a ∉ S' := fun hc => ha (Finset.mem_powerset.mp hS' hc)
    have hcongr := congrArg (fun U : Finset (Fin n) => U.erase a) hSS'
    simpa [Finset.erase_insert hSa, Finset.erase_insert hS'a] using hcongr
  · refine Finset.disjoint_left.mpr fun S hS hS' => ?_
    obtain ⟨S', _, rfl⟩ := Finset.mem_image.mp hS'
    exact ha (Finset.mem_powerset.mp hS (Finset.mem_insert_self a S'))

/-- **The subset expansion of the product of local projectors.** -/
theorem stabProjectorOn_eq_smul_expansion (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) (T : Finset (Fin n)) :
    stabProjectorOn b hb ε T = ((2 : ℂ) ^ T.card)⁻¹ • stabExpansion b hb ε T := by
  classical
  induction T using Finset.induction with
  | empty =>
      rw [stabProjectorOn_empty, stabExpansion, Finset.powerset_empty, Finset.card_empty]
      simp [signOf, stabProd_empty]
  | insert a T ha ih =>
      have hQE : ∀ S ∈ T.powerset,
          signOf (ε a) • (pauliMat (b a) * (signOf (∑ i ∈ S, ε i) • stabProd b hb S)) =
            signOf (∑ i ∈ insert a S, ε i) • stabProd b hb (insert a S) := by
        intro S hS
        have haS : a ∉ S := fun hc => ha (Finset.mem_powerset.mp hS hc)
        rw [Matrix.mul_smul, smul_smul, ← stabProd_insert hb haS, Finset.sum_insert haS,
          signOf_add]
      have hkey : (1 + signOf (ε a) • pauliMat (b a)) * stabExpansion b hb ε T =
          stabExpansion b hb ε (insert a T) := by
        rw [stabExpansion_insert hb ε ha, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
        congr 1
        calc signOf (ε a) • (pauliMat (b a) * stabExpansion b hb ε T)
            = signOf (ε a) • ∑ S ∈ T.powerset,
                pauliMat (b a) * (signOf (∑ i ∈ S, ε i) • stabProd b hb S) := by
              rw [stabExpansion, Finset.mul_sum]
          _ = ∑ S ∈ T.powerset, signOf (ε a) •
                (pauliMat (b a) * (signOf (∑ i ∈ S, ε i) • stabProd b hb S)) := Finset.smul_sum
          _ = ∑ S ∈ T.powerset, signOf (∑ i ∈ insert a S, ε i) • stabProd b hb (insert a S) :=
              Finset.sum_congr rfl hQE
      rw [stabProjectorOn_insert hb ε ha, ih, stabFactor, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, hkey, Finset.card_insert_of_notMem ha]
      congr 1
      rw [pow_succ, mul_inv]
      ring

/-- The stabilizer projector of a commuting family with a sign pattern. -/
def stabProjector (b : Fin n → PauliSymp n) (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) :
    Matrix (FiniteQubitConfiguration (Fin n)) (FiniteQubitConfiguration (Fin n)) ℂ :=
  stabProjectorOn b hb ε Finset.univ

theorem stabProjector_eq_smul_expansion (hb : ∀ i j, symForm (b i) (b j) = 0)
    (ε : Fin n → ZMod 2) :
    stabProjector b hb ε =
      ((2 : ℂ) ^ n)⁻¹ • ∑ S : Finset (Fin n), signOf (∑ i ∈ S, ε i) • stabProd b hb S := by
  classical
  rw [stabProjector, stabProjectorOn_eq_smul_expansion, stabExpansion, Finset.card_univ,
    Fintype.card_fin, Finset.powerset_univ]

end GaloisForLFunctions.HTGeometry
