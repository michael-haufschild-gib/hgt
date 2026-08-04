import GaloisForLFunctions.HTGeometry.InvolutiveSubspaceParityDecomposition

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def submoduleListSup
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X] :
    List (Submodule K X) → Submodule K X
  | [] => ⊥
  | U :: Us => U ⊔ submoduleListSup Us

theorem submoduleListSup_append
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (Us Vs : List (Submodule K X)) :
    submoduleListSup (Us ++ Vs) =
      submoduleListSup Us ⊔ submoduleListSup Vs := by
  induction Us with
  | nil => simp [submoduleListSup]
  | cons U Us ih =>
      simp only [List.cons_append, submoduleListSup, ih]
      rw [sup_assoc]

/-- Binary parity leaves obtained by successively splitting a subspace under
a finite list of involutions. -/
def simultaneousParityPieces
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X] :
    List (X ≃ₗ[K] X) → Submodule K X → List (Submodule K X)
  | [], U => [U]
  | C :: Cs, U =>
      simultaneousParityPieces Cs (U ⊓ involutiveEvenSubspace C) ++
        simultaneousParityPieces Cs (U ⊓ involutiveOddSubspace C)

/-- A subspace stable under a finite commuting list of involutions is the
sum of all of its simultaneous parity pieces. -/
theorem invariantSubspace_eq_simultaneousParityPieces_sup
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    (h2 : (2 : K) ≠ 0)
    (Cs : List (X ≃ₗ[K] X))
    (hinvolutive : ∀ C ∈ Cs, ∀ x, C (C x) = x)
    (hcomm : Cs.Pairwise fun C D => ∀ x, C (D x) = D (C x))
    (U : Submodule K X)
    (hstable : ∀ C ∈ Cs, U.map (C : X →ₗ[K] X) ≤ U) :
    U = submoduleListSup (simultaneousParityPieces Cs U) := by
  induction Cs generalizing U with
  | nil => simp [simultaneousParityPieces, submoduleListSup]
  | cons C Cs ih =>
      have hCinv : ∀ x, C (C x) = x := hinvolutive C (by simp)
      have hCstable : U.map (C : X →ₗ[K] X) ≤ U := hstable C (by simp)
      have htailInv : ∀ D ∈ Cs, ∀ x, D (D x) = x := by
        intro D hD
        exact hinvolutive D (by simp [hD])
      have htailPair : Cs.Pairwise fun D E => ∀ x, D (E x) = E (D x) :=
        List.pairwise_cons.mp hcomm |>.2
      have hheadComm : ∀ D ∈ Cs, ∀ x, C (D x) = D (C x) := by
        intro D hD
        exact (List.pairwise_cons.mp hcomm).1 D hD
      have htailStable : ∀ D ∈ Cs, U.map (D : X →ₗ[K] X) ≤ U := by
        intro D hD
        exact hstable D (by simp [hD])
      let E := U ⊓ involutiveEvenSubspace C
      let O := U ⊓ involutiveOddSubspace C
      have hEstable : ∀ D ∈ Cs, E.map (D : X →ₗ[K] X) ≤ E := by
        intro D hD
        exact evenPart_map_le_of_commuting_involutions C D
          (hheadComm D hD) U (htailStable D hD)
      have hOstable : ∀ D ∈ Cs, O.map (D : X →ₗ[K] X) ≤ O := by
        intro D hD
        exact oddPart_map_le_of_commuting_involutions C D
          (hheadComm D hD) U (htailStable D hD)
      have hsplit : U = E ⊔ O :=
        invariantSubspace_eq_even_sup_odd C hCinv h2 U hCstable
      have hE := ih htailInv htailPair E hEstable
      have hO := ih htailInv htailPair O hOstable
      rw [simultaneousParityPieces, submoduleListSup_append, ← hE, ← hO]
      exact hsplit

/-- In finite dimension the finranks of all simultaneous parity pieces add
exactly to the finrank of the invariant subspace. -/
theorem invariantSubspace_finrank_eq_simultaneousParityPieces_sum
    {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
    [FiniteDimensional K X]
    (h2 : (2 : K) ≠ 0)
    (Cs : List (X ≃ₗ[K] X))
    (hinvolutive : ∀ C ∈ Cs, ∀ x, C (C x) = x)
    (hcomm : Cs.Pairwise fun C D => ∀ x, C (D x) = D (C x))
    (U : Submodule K X)
    (hstable : ∀ C ∈ Cs, U.map (C : X →ₗ[K] X) ≤ U) :
    Module.finrank K U =
      ((simultaneousParityPieces Cs U).map
        (fun V : Submodule K X => Module.finrank K V)).sum := by
  induction Cs generalizing U with
  | nil => simp [simultaneousParityPieces]
  | cons C Cs ih =>
      have hCinv : ∀ x, C (C x) = x := hinvolutive C (by simp)
      have hCstable : U.map (C : X →ₗ[K] X) ≤ U := hstable C (by simp)
      have htailInv : ∀ D ∈ Cs, ∀ x, D (D x) = x := by
        intro D hD
        exact hinvolutive D (by simp [hD])
      have htailPair : Cs.Pairwise fun D E => ∀ x, D (E x) = E (D x) :=
        List.pairwise_cons.mp hcomm |>.2
      have hheadComm : ∀ D ∈ Cs, ∀ x, C (D x) = D (C x) := by
        intro D hD
        exact (List.pairwise_cons.mp hcomm).1 D hD
      have htailStable : ∀ D ∈ Cs, U.map (D : X →ₗ[K] X) ≤ U := by
        intro D hD
        exact hstable D (by simp [hD])
      let E := U ⊓ involutiveEvenSubspace C
      let O := U ⊓ involutiveOddSubspace C
      have hEstable : ∀ D ∈ Cs, E.map (D : X →ₗ[K] X) ≤ E := by
        intro D hD
        exact evenPart_map_le_of_commuting_involutions C D
          (hheadComm D hD) U (htailStable D hD)
      have hOstable : ∀ D ∈ Cs, O.map (D : X →ₗ[K] X) ≤ O := by
        intro D hD
        exact oddPart_map_le_of_commuting_involutions C D
          (hheadComm D hD) U (htailStable D hD)
      have hsplit :=
        invariantSubspace_finrank_eq_even_add_odd C hCinv h2 U hCstable
      have hE := ih htailInv htailPair E hEstable
      have hO := ih htailInv htailPair O hOstable
      simp only [simultaneousParityPieces, List.map_append, List.sum_append]
      dsimp [E, O] at hsplit hE hO
      omega

end

end GaloisForLFunctions.HTGeometry
