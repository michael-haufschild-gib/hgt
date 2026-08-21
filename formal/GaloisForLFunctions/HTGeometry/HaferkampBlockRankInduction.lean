import GaloisForLFunctions.HTGeometry.HaferkampLiftedCliffordAction
import GaloisForLFunctions.HTGeometry.HaferkampDerivativeRank
import GaloisForLFunctions.HTGeometry.HaferkampPauliDirectionSelection

/-!
# Fresh Pauli families for the Haferkamp block-rank induction

Appendix B requires one nonidentity Pauli direction per light-cone block in
the strict range `T < 4^n - 1`.  The finite Pauli basis allows choosing the
entire family injectively at once; hence its matrices are linearly
independent before the block-specific Clifford transports are applied.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix

/-- In the strict pre-saturation range there are `T` distinct nonidentity
`n`-qubit Pauli labels. -/
theorem exists_injective_haferkampNonidentityPauliFamily
    {n T : ℕ} (hT : T < 4 ^ n - 1) :
    ∃ P : Fin T → HaferkampPauliLabel n,
      (∀ i, P i ≠ fun _ => none) ∧ Function.Injective P := by
  let S := haferkampNonidentityPauliLabels n
  let e := Fintype.equivFin {P : HaferkampPauliLabel n // P ∈ S}
  have hcard : T ≤ Fintype.card {P : HaferkampPauliLabel n // P ∈ S} := by
    rw [Fintype.card_coe, card_haferkampNonidentityPauliLabels]
    exact Nat.le_of_lt hT
  let f : Fin T → {P : HaferkampPauliLabel n // P ∈ S} :=
    fun i => e.symm (Fin.castLE hcard i)
  refine ⟨fun i => (f i).1, ?_, ?_⟩
  · intro i
    exact (Finset.mem_filter.mp (f i).2).2
  · intro i j hij
    apply Fin.castLE_injective hcard
    have hf : f i = f j := Subtype.ext hij
    simpa [f] using congrArg e hf

/-- The selected finite Pauli matrices form an independent complex family. -/
theorem exists_linearIndependent_haferkampNonidentityPauliFamily
    {n T : ℕ} (hT : T < 4 ^ n - 1) :
    ∃ P : Fin T → HaferkampPauliLabel n,
      (∀ i, P i ≠ fun _ => none) ∧
      LinearIndependent ℂ (fun i => finitePauliMatrix (P i)) := by
  obtain ⟨P, hP, hPinj⟩ := exists_injective_haferkampNonidentityPauliFamily hT
  exact ⟨P, hP,
    (finitePauliMatrix_linearIndependent (σ := Fin n)).comp P hPinj⟩

/-- A common left matrix factor may be stripped from a family once its
images are nonzero scalar multiples of independent finite Pauli matrices.
This is the linear-algebraic end of the Appendix-B block induction. -/
theorem linearIndependent_of_left_smul_finitePauli
    {Q : Type*} [Fintype Q] [DecidableEq Q] {T : Type*}
    (P : T → Q → Option (Fin 3))
    (hP : LinearIndependent ℂ (fun i => finitePauliMatrix (P i)))
    (V : T → Matrix (Q → Bool) (Q → Bool) ℂ)
    (U : Matrix (Q → Bool) (Q → Bool) ℂ)
    (c : T → ℂ) (hc : ∀ i, c i ≠ 0)
    (hstrip : ∀ i, U * V i = c i • finitePauliMatrix (P i)) :
    LinearIndependent ℂ V := by
  apply LinearIndependent.of_comp (LinearMap.mulLeft ℂ U)
  simpa [Function.comp_def, hstrip] using
    (linearIndependent_smul_of_ne_zero (fun i => finitePauliMatrix (P i)) hP c hc)

/-- Factor a reverse-chronological finite word at one gate location. -/
theorem haferkamp_reverse_prod_split
    {G : Type*} [Group G] (gates : List G) (i : Fin gates.length) :
    gates.reverse.prod = (gates.drop (i.1 + 1)).reverse.prod * gates.get i *
      (gates.take i.1).reverse.prod := by
  have hsplit : gates = gates.take i.1 ++ gates.get i :: gates.drop (i.1 + 1) := by
    calc
      gates = gates.take i.1 ++ gates.drop i.1 := (List.take_append_drop i.1 gates).symm
      _ = gates.take i.1 ++ gates.get i :: gates.drop (i.1 + 1) := by
        rw [← List.getElem_cons_drop (as := gates) (i := i.1) i.2]
        simp only [List.get_eq_getElem]
  calc
    gates.reverse.prod =
        (gates.take i.1 ++ gates.get i :: gates.drop (i.1 + 1)).reverse.prod :=
      congrArg (fun word : List G => word.reverse.prod) hsplit
    _ = (gates.drop (i.1 + 1)).reverse.prod * gates.get i *
        (gates.take i.1).reverse.prod := by
      rw [List.reverse_append, List.reverse_cons, List.prod_append, List.prod_append]
      simp only [List.prod_cons, List.prod_nil, mul_one]

/-- Stripping the total unitary from a coordinate variation leaves the
prefix-conjugated local variation. -/
theorem haferkamp_unitary_reverse_coordinate_strip
    {I : Type*} [Fintype I] [DecidableEq I]
    (gates : List (Matrix.unitaryGroup I ℂ)) (i : Fin gates.length)
    (Z : Matrix I I ℂ) :
    Matrix.conjTranspose
        ((gates.reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) *
      (((gates.drop (i.1 + 1)).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) *
        (Z * (gates.get i : Matrix I I ℂ)) *
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) =
      Matrix.conjTranspose
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) *
        Matrix.conjTranspose (gates.get i : Matrix I I ℂ) * Z *
          (gates.get i : Matrix I I ℂ) *
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) := by
  let later : Matrix.unitaryGroup I ℂ := (gates.drop (i.1 + 1)).reverse.prod
  let front : Matrix.unitaryGroup I ℂ := (gates.take i.1).reverse.prod
  have htotalG := haferkamp_reverse_prod_split gates i
  have htotal : (gates.reverse.prod : Matrix I I ℂ) =
      ((later * gates.get i * front : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) := by
    simpa only [later, front] using
      congrArg (fun U : Matrix.unitaryGroup I ℂ => (U : Matrix I I ℂ)) htotalG
  have hlater : Matrix.conjTranspose (later : Matrix I I ℂ) *
      (later : Matrix I I ℂ) = 1 := by
    rw [← star_eq_conjTranspose]
    exact mul_eq_one_comm.mp (Matrix.mem_unitaryGroup_iff.mp later.2)
  have coe_mul (U V : Matrix.unitaryGroup I ℂ) :
      ((U * V : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) =
        (U : Matrix I I ℂ) * (V : Matrix I I ℂ) := rfl
  rw [htotal]
  calc
    Matrix.conjTranspose
          ((later * gates.get i * front : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) *
        (later : Matrix I I ℂ) * (Z * (gates.get i : Matrix I I ℂ)) *
          (front : Matrix I I ℂ) =
      (Matrix.conjTranspose (front : Matrix I I ℂ) *
        Matrix.conjTranspose (gates.get i : Matrix I I ℂ) *
        (Matrix.conjTranspose (later : Matrix I I ℂ) * (later : Matrix I I ℂ))) *
          (Z * (gates.get i : Matrix I I ℂ)) * (front : Matrix I I ℂ) := by
        simp only [coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.conjTranspose (front : Matrix I I ℂ) *
        Matrix.conjTranspose (gates.get i : Matrix I I ℂ) * Z *
          (gates.get i : Matrix I I ℂ) * (front : Matrix I I ℂ) := by
      rw [hlater]
      simp only [Matrix.one_mul, Matrix.mul_assoc]

/-- Ambient coordinate variation obtained from a local Hermitian Pauli
direction immediately after its unitary gate. -/
def haferkampUnitaryListCoordinateOutput
    {I : Type*} [Fintype I] [DecidableEq I]
    (gates : List (Matrix.unitaryGroup I ℂ)) (i : Fin gates.length)
    (Z : Matrix I I ℂ) : Matrix I I ℂ :=
  (((gates.drop (i.1 + 1)).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ) *
    (Z * (gates.get i : Matrix I I ℂ)) *
      (((gates.take i.1).reverse.prod : Matrix.unitaryGroup I ℂ) : Matrix I I ℂ)

/-- The total unitary strips a coordinate variation to the supplied
prefix-conjugated local Pauli identity. -/
theorem haferkampUnitaryListCoordinateOutput_strip
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (gates : List (Matrix.unitaryGroup (Q → Bool) ℂ))
    (i : Fin gates.length) (Z : Matrix (Q → Bool) (Q → Bool) ℂ)
    (P : Q → Option (Fin 3)) (c : ℂ)
    (hprefix :
      Matrix.conjTranspose
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
            Matrix (Q → Bool) (Q → Bool) ℂ) *
        Matrix.conjTranspose (gates.get i : Matrix (Q → Bool) (Q → Bool) ℂ) * Z *
          (gates.get i : Matrix (Q → Bool) (Q → Bool) ℂ) *
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
            Matrix (Q → Bool) (Q → Bool) ℂ) = c • finitePauliMatrix P) :
    Matrix.conjTranspose
        ((gates.reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
          Matrix (Q → Bool) (Q → Bool) ℂ) *
      haferkampUnitaryListCoordinateOutput gates i Z = c • finitePauliMatrix P := by
  unfold haferkampUnitaryListCoordinateOutput
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [haferkamp_unitary_reverse_coordinate_strip]
  exact hprefix

/-- Independent prefix-conjugated Pauli directions yield independent ambient
coordinate variations of the full reverse-chronological circuit word. -/
theorem linearIndependent_haferkampUnitaryListCoordinateOutputs
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (gates : List (Matrix.unitaryGroup (Q → Bool) ℂ))
    (P : Fin gates.length → Q → Option (Fin 3))
    (hP : LinearIndependent ℂ (fun i => finitePauliMatrix (P i)))
    (Z : Fin gates.length → Matrix (Q → Bool) (Q → Bool) ℂ)
    (c : Fin gates.length → ℂ) (hc : ∀ i, c i ≠ 0)
    (hprefix : ∀ i,
      Matrix.conjTranspose
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
            Matrix (Q → Bool) (Q → Bool) ℂ) *
        Matrix.conjTranspose (gates.get i : Matrix (Q → Bool) (Q → Bool) ℂ) * Z i *
          (gates.get i : Matrix (Q → Bool) (Q → Bool) ℂ) *
          (((gates.take i.1).reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
            Matrix (Q → Bool) (Q → Bool) ℂ) = c i • finitePauliMatrix (P i)) :
    LinearIndependent ℂ (fun i =>
      haferkampUnitaryListCoordinateOutput gates i (Z i)) := by
  apply linearIndependent_of_left_smul_finitePauli P hP
    (fun i => haferkampUnitaryListCoordinateOutput gates i (Z i))
    (Matrix.conjTranspose
      ((gates.reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
        Matrix (Q → Bool) (Q → Bool) ℂ)) c hc
  intro i
  exact haferkampUnitaryListCoordinateOutput_strip gates i (Z i) (P i) (c i) (hprefix i)

/-- The preceding independence argument applies to any selected family of
coordinates of a longer physical gate word.  The selected terminal gates of
the BLC block assembly are such a family. -/
theorem linearIndependent_haferkampSelectedUnitaryListCoordinateOutputs
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (gates : List (Matrix.unitaryGroup (Q → Bool) ℂ)) {T : ℕ}
    (indices : Fin T → Fin gates.length)
    (P : Fin T → Q → Option (Fin 3))
    (hP : LinearIndependent ℂ (fun i => finitePauliMatrix (P i)))
    (Z : Fin T → Matrix (Q → Bool) (Q → Bool) ℂ)
    (c : Fin T → ℂ) (hc : ∀ i, c i ≠ 0)
    (hprefix : ∀ i,
      Matrix.conjTranspose
          (((gates.take (indices i).1).reverse.prod :
            Matrix.unitaryGroup (Q → Bool) ℂ) : Matrix (Q → Bool) (Q → Bool) ℂ) *
        Matrix.conjTranspose (gates.get (indices i) : Matrix (Q → Bool) (Q → Bool) ℂ) *
          Z i * (gates.get (indices i) : Matrix (Q → Bool) (Q → Bool) ℂ) *
        (((gates.take (indices i).1).reverse.prod :
          Matrix.unitaryGroup (Q → Bool) ℂ) : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c i • finitePauliMatrix (P i)) :
    LinearIndependent ℂ (fun i =>
      haferkampUnitaryListCoordinateOutput gates (indices i) (Z i)) := by
  apply linearIndependent_of_left_smul_finitePauli P hP
    (fun i => haferkampUnitaryListCoordinateOutput gates (indices i) (Z i))
    (Matrix.conjTranspose
      ((gates.reverse.prod : Matrix.unitaryGroup (Q → Bool) ℂ) :
        Matrix (Q → Bool) (Q → Bool) ℂ)) c hc
  intro i
  exact haferkampUnitaryListCoordinateOutput_strip gates (indices i) (Z i)
    (P i) (c i) (hprefix i)

end

end GaloisForLFunctions.HTGeometry
