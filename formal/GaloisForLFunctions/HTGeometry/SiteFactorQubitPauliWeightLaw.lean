import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.FiniteQubitPauliBasisLaw
import GaloisForLFunctions.HTGeometry.PauliWeightWitnesses
import GaloisForLFunctions.HTGeometry.SiteFactorInteractionCoordinates
import GaloisForLFunctions.HTGeometry.HypergraphComponentWitness

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extend a Pauli word on a site packet by identities on spectator sites. -/
def extendPacketPauliLabel (S : Finset V)
    (P : S → Option (Fin 3)) : V → Option (Fin 3) :=
  fun v => if hv : v ∈ S then P ⟨v, hv⟩ else none

@[simp] theorem extendPacketPauliLabel_mem (S : Finset V)
    (P : S → Option (Fin 3)) {v : V} (hv : v ∈ S) :
    extendPacketPauliLabel S P v = P ⟨v, hv⟩ := by
  simp [extendPacketPauliLabel, hv]

@[simp] theorem extendPacketPauliLabel_notMem (S : Finset V)
    (P : S → Option (Fin 3)) {v : V} (hv : v ∉ S) :
    extendPacketPauliLabel S P v = none := by
  simp [extendPacketPauliLabel, hv]

/-- Lifting a packet Pauli word is extension by identity labels. -/
theorem liftLocalMatrix_finitePauliMatrix (S : Finset V)
    (P : S → Option (Fin 3)) :
    liftLocalMatrix (A := fun _ : V => Bool) S (finitePauliMatrix P) =
      finitePauliMatrix (extendPacketPauliLabel S P) := by
  ext x y
  rw [liftLocalMatrix]
  by_cases hout : restrictOutsideConfiguration S x =
      restrictOutsideConfiguration S y
  · rw [if_pos hout]
    rw [finitePauliMatrix, finitePauliMatrix]
    let f : V → ℂ := fun v =>
      boolPauliOptionEntry (extendPacketPauliLabel S P v) (x v, y v)
    have houtside : ∀ v ∈ (Finset.univ : Finset V), v ∉ S → f v = 1 := by
      intro v _ hv
      have hxy : x v = y v := congrFun hout ⟨v, hv⟩
      simp [f, extendPacketPauliLabel, hv, boolPauliOptionEntry,
        boolPauliOption, Matrix.one_apply, hxy]
    have hprod : ∏ v ∈ S, f v = ∏ v : V, f v := by
      simpa using (Finset.prod_subset (s₁ := S) (s₂ := Finset.univ)
        (Finset.subset_univ S) houtside)
    rw [← hprod]
    rw [Finset.prod_subtype S (fun v => Iff.rfl)]
    apply Finset.prod_congr rfl
    intro v _
    simp [f, extendPacketPauliLabel, restrictLocalConfiguration]
  · rw [if_neg hout]
    rw [finitePauliMatrix]
    obtain ⟨v, hv⟩ : ∃ v : {v : V // v ∉ S}, x v.1 ≠ y v.1 := by
      simpa only [Function.ne_iff, restrictOutsideConfiguration] using hout
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v.1)
    simp [extendPacketPauliLabel, v.2, boolPauliOptionEntry,
      boolPauliOption, Matrix.one_apply, hv]

/-- A packet extension has support weight at most the packet cardinality. -/
theorem finitePauliWeight_extendPacketPauliLabel_le (S : Finset V)
    (P : S → Option (Fin 3)) :
    finitePauliWeight (extendPacketPauliLabel S P) ≤ S.card := by
  rw [finitePauliWeight]
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  by_contra hvS
  exact hv (extendPacketPauliLabel_notMem S P hvS)

/-- Every Hermitian operator supported on a packet is a real combination of Pauli words whose
nonidentity letters remain inside that packet. -/
theorem exists_real_pauli_expansion_of_isSiteSupported
    (S : Finset V)
    {H : Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ}
    (hH : H.IsHermitian) (hsupp : IsSiteSupported S H) :
    ∃ c : (S → Option (Fin 3)) → ℝ,
      H = ∑ P, c P • finitePauliMatrix (extendPacketPauliLabel S P) := by
  classical
  obtain ⟨B, hB⟩ := exists_liftLocalMatrix_of_isSiteSupported hsupp
  have hBherm : B.IsHermitian := by
    apply isHermitian_of_isHermitian_liftLocalMatrix S
    rwa [← hB]
  let Bsa : selfAdjoint
      (Matrix (FiniteQubitConfiguration S) (FiniteQubitConfiguration S) ℂ) :=
    ⟨B, hBherm⟩
  let c : (S → Option (Fin 3)) → ℝ :=
    (finitePauliSelfAdjointBasis S).repr Bsa
  have hexp := (finitePauliSelfAdjointBasis S).sum_repr Bsa
  have hBexp : B = ∑ P, c P • finitePauliMatrix P := by
    have hcoe := congrArg
      (fun X : selfAdjoint
        (Matrix (FiniteQubitConfiguration S) (FiniteQubitConfiguration S) ℂ) =>
          (X : Matrix (FiniteQubitConfiguration S) (FiniteQubitConfiguration S) ℂ))
      hexp
    simpa [Bsa, c, finitePauliSelfAdjointBasis_apply,
      finitePauliSelfAdjoint] using hcoe.symm
  refine ⟨c, ?_⟩
  rw [hB, hBexp]
  change liftLocalMatrixLinear (fun _ : V => Bool) S
      (∑ P, c P • finitePauliMatrix P) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [map_smul, liftLocalMatrixLinear_apply,
    liftLocalMatrix_finitePauliMatrix]

/-- Packet support bounds every Pauli coefficient by packet cardinality. -/
theorem hasPauliWeightAtMost_of_isSiteSupported
    (S : Finset V)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ))
    (hsupp : IsSiteSupported S
      (H : Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ)) :
    HasPauliWeightAtMost V S.card H := by
  classical
  obtain ⟨c, hexp⟩ :=
    exists_real_pauli_expansion_of_isSiteSupported S H.prop hsupp
  have hsa : H = ∑ P, c P • finitePauliSelfAdjoint
      (extendPacketPauliLabel S P) := by
    apply Subtype.ext
    simpa [finitePauliSelfAdjoint] using hexp
  intro Q hQ
  rw [hsa, map_sum]
  simp only [map_smul]
  simp only [Finsupp.coe_finsetSum, Finsupp.coe_smul]
  rw [Fintype.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro P _
  have hne : extendPacketPauliLabel S P ≠ Q := by
    intro heq
    have hle := finitePauliWeight_extendPacketPauliLabel_le S P
    rw [heq] at hle
    omega
  rw [show finitePauliSelfAdjoint (extendPacketPauliLabel S P) =
      finitePauliSelfAdjointBasis V (extendPacketPauliLabel S P) by
        rw [finitePauliSelfAdjointBasis_apply],
    Module.Basis.repr_self, Finsupp.single_apply]
  simp [hne]

/-- Bounded Pauli weight is closed under real scalar multiplication. -/
theorem HasPauliWeightAtMost.smul {q : ℕ}
    {H : selfAdjoint
      (Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ)}
    (hH : HasPauliWeightAtMost V q H) (c : ℝ) :
    HasPauliWeightAtMost V q (c • H) := by
  intro P hP
  simp [hH P hP]

/-- Every ordinary onsite-plus-edge qubit Hamiltonian has Pauli weight at most two. -/
theorem hasPauliWeightAtMost_two_of_mem_siteFactorLocalSubmodule
    (G : SimpleGraph V)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration V) (FiniteQubitConfiguration V) ℂ))
    (hmem : (H : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ) ∈
        siteFactorLocalSubmodule (fun _ : V => Bool) G) :
    HasPauliWeightAtMost V 2 H := by
  let Good := fun X : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ =>
    ∃ hX : X.IsHermitian, HasPauliWeightAtMost V 2 ⟨X, hX⟩
  have hspan : ∀ X : Matrix (FiniteQubitConfiguration V)
      (FiniteQubitConfiguration V) ℂ,
      X ∈ siteFactorLocalSubmodule (fun _ : V => Bool) G → Good X := by
    intro X hXmem
    induction hXmem using Submodule.span_induction with
    | mem X hX =>
        rcases hX with ⟨hXherm, ⟨v, hsupp⟩ | ⟨u, v, huv, hsupp⟩⟩
        · refine ⟨hXherm, ?_⟩
          exact (hasPauliWeightAtMost_of_isSiteSupported {v}
            ⟨X, hXherm⟩ hsupp).mono (by simp)
        · refine ⟨hXherm, ?_⟩
          exact (hasPauliWeightAtMost_of_isSiteSupported {u, v}
            ⟨X, hXherm⟩ hsupp).mono (by
              calc
                ({u, v} : Finset V).card ≤ ({v} : Finset V).card + 1 :=
                  Finset.card_insert_le u {v}
                _ = 2 := by simp)
    | zero =>
        exact ⟨Matrix.isHermitian_zero, hasPauliWeightAtMost_zero 2⟩
    | add X Y _ _ hX hY =>
        obtain ⟨hXherm, hXlocal⟩ := hX
        obtain ⟨hYherm, hYlocal⟩ := hY
        refine ⟨hXherm.add hYherm, ?_⟩
        convert hXlocal.add hYlocal using 1
        apply Subtype.ext
        rfl
    | smul c X _ hX =>
        obtain ⟨hXherm, hXlocal⟩ := hX
        refine ⟨hXherm.smul (star_trivial c), ?_⟩
        convert hXlocal.smul c using 1
        apply Subtype.ext
        rfl
  obtain ⟨hHherm, hHlocal⟩ := hspan H hmem
  convert hHlocal using 1

end

end GaloisForLFunctions.HTGeometry
