import GaloisForLFunctions.HTGeometry.GraphLocalPauliConjugation
import GaloisForLFunctions.HTGeometry.CommutingInvolutionCharacterExtraction

/-!
# Character resolution of the edge images on singlet input

On a sitewise singlet, the collective commutator of a physical Pauli word is an eigenvector of
every all-replica Pauli conjugation, with eigenvalue the single-site conjugation sign at the
conjugating site.  Distinct words carry distinct sign patterns, because the single-qubit symplectic
pairing already separates letters.  A subspace stable under all these conjugations therefore
contains every edge image whose sum it contains, and every edge image on singlet input is
orthogonal to the singlet sector.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-! ## Single-qubit conjugation signs -/

theorem boolPauliConjugationSign_some_none (c : Fin 3) :
    boolPauliConjugationSign (some c) none = 1 := by
  rw [boolPauliConjugationSign, if_pos (Or.inr (Or.inl rfl))]

theorem boolPauliConjugationSign_some_self (c : Fin 3) :
    boolPauliConjugationSign (some c) (some c) = 1 := by
  rw [boolPauliConjugationSign, if_pos (Or.inr (Or.inr rfl))]

theorem boolPauliConjugationSign_some_some_of_ne {c b : Fin 3} (h : c ≠ b) :
    boolPauliConjugationSign (some c) (some b) = -1 := by
  rw [boolPauliConjugationSign, if_neg]
  rintro (h1 | h1 | h1)
  · exact absurd h1 (Option.some_ne_none c)
  · exact absurd h1 (Option.some_ne_none b)
  · exact h (Option.some.inj h1)

theorem boolPauliConjugationSign_mul_self (q p : Option (Fin 3)) :
    boolPauliConjugationSign q p * boolPauliConjugationSign q p = 1 := by
  rw [boolPauliConjugationSign]
  split <;> norm_num

/-- **The single-qubit conjugation characters separate letters.** -/
theorem exists_boolPauliConjugationSign_mul_eq_neg_one {p q : Option (Fin 3)} (h : p ≠ q) :
    ∃ c : Fin 3,
      boolPauliConjugationSign (some c) p * boolPauliConjugationSign (some c) q = -1 := by
  have hne : ∀ b : Fin 3, b + 1 ≠ b := by decide
  rcases p with _ | a
  · rcases q with _ | b
    · exact absurd rfl h
    · exact ⟨b + 1, by
        rw [boolPauliConjugationSign_some_none,
          boolPauliConjugationSign_some_some_of_ne (hne b), one_mul]⟩
  · rcases q with _ | b
    · exact ⟨a + 1, by
        rw [boolPauliConjugationSign_some_some_of_ne (hne a),
          boolPauliConjugationSign_some_none, mul_one]⟩
    · have hab : a ≠ b := fun hc => h (by rw [hc])
      exact ⟨a, by
        rw [boolPauliConjugationSign_some_self,
          boolPauliConjugationSign_some_some_of_ne hab, one_mul]⟩

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- **Every collective commutator of singlet input is a conjugation eigenvector.** -/
theorem siteConjEquiv_commutator_singlet (v : I) (c : Fin 3) (p : I → Option (Fin 3))
    {x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    siteConjEquiv I R v c
        ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x) =
      boolPauliConjugationSign (some c) (p v) •
        (matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x := by
  obtain ⟨X, rfl⟩ := (vecLinearEquiv (FiniteQubitConfiguration (I × R))).surjective x
  have hfix : siteConjString I R v c * X * siteConjString I R v c = X := by
    have h := siteConjEquiv_apply_of_mem_singlet v c hx
    rw [siteConjEquiv_apply_vec] at h
    exact (vecLinearEquiv (FiniteQubitConfiguration (I × R))).injective h
  rw [toEuclideanLin_commutatorRep_vec, siteConjEquiv_apply_vec,
    siteConjString_conj_commutator_general p X, hfix, map_smul]

theorem graphLocalGenerator_inr_apply (G : SimpleGraph I)
    (p : {p : I → Option (Fin 3) // IsEdgeWord G p})
    (x : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)) :
    graphLocalGenerator I R G (Sum.inr p) x =
      (matrixCommutatorRepresentation (collectivePauliString I R p.1)).toEuclideanLin x := rfl

/-- **Character extraction: a conjugation-stable subspace containing the total edge image of a
singlet contains every edge image separately.** -/
theorem edgeImage_mem_of_sum_mem (G : SimpleGraph I)
    {U : Submodule ℂ (EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R))}
    (hUinv : ∀ v : I, ∀ c : Fin 3, ∀ u ∈ U, siteConjEquiv I R v c u ∈ U)
    {s : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hs : s ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hsum : (∑ p : {p : I → Option (Fin 3) // IsEdgeWord G p},
      graphLocalGenerator I R G (Sum.inr p) s) ∈ U)
    (p₀ : {p : I → Option (Fin 3) // IsEdgeWord G p}) :
    graphLocalGenerator I R G (Sum.inr p₀) s ∈ U := by
  classical
  refine mem_of_sum_mem_of_separating (𝕜 := ℂ) two_ne_zero U
    (fun k : I × Fin 3 =>
      (siteConjEquiv I R k.1 k.2 :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _))
    (fun k u hu => hUinv k.1 k.2 u hu)
    (fun p => graphLocalGenerator I R G (Sum.inr p) s)
    (fun p k => boolPauliConjugationSign (some k.2) (p.1 k.1))
    (fun p k => siteConjEquiv_commutator_singlet k.1 k.2 p.1 hs)
    (fun p k => boolPauliConjugationSign_mul_self _ _)
    (fun p q hpq => ?_) hsum p₀
  have hne : p.1 ≠ q.1 := fun hc => hpq (Subtype.ext hc)
  obtain ⟨v, hv⟩ := Function.ne_iff.mp hne
  obtain ⟨c, hc⟩ := exists_boolPauliConjugationSign_mul_eq_neg_one hv
  exact ⟨(v, c), hc⟩

/-! ## Edge images of singlets are orthogonal to the singlet sector -/

/-- **Every collective commutator of a nontrivial word sends singlets off the singlet sector.** -/
theorem inner_commutator_singlet_eq_zero {p : I → Option (Fin 3)} {v : I}
    (hv : p v ≠ none)
    {x y : EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R)}
    (hx : x ∈ finiteAllReplicaCollectiveSingletSubspace I R)
    (hy : y ∈ finiteAllReplicaCollectiveSingletSubspace I R) :
    (inner ℂ y
      ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x) : ℂ) =
      0 := by
  classical
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hv
  have hne : ∀ b : Fin 3, b + 1 ≠ b := by decide
  have hsign : boolPauliConjugationSign (some (a + 1)) (p v) = -1 := by
    rw [ha]
    exact boolPauliConjugationSign_some_some_of_ne (hne a)
  have hmove : (inner ℂ y
      ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x) : ℂ) =
      inner ℂ y (siteConjEquiv I R v (a + 1)
        ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x)) := by
    conv_lhs => rw [← siteConjEquiv_apply_of_mem_singlet v (a + 1) hy]
    rw [show ((siteConjEquiv I R v (a + 1)) y) =
      (siteConjEquiv I R v (a + 1) :
        EuclideanSpace ℂ (FiniteAllReplicaOperatorIndex I R) →ₗ[ℂ] _) y from rfl,
      ← adjoint_siteConjEquiv (I := I) (R := R) v (a + 1), LinearMap.adjoint_inner_left]
    rfl
  rw [siteConjEquiv_commutator_singlet v (a + 1) p hx, hsign, inner_smul_right] at hmove
  have h2 : (2 : ℂ) * (inner ℂ y
      ((matrixCommutatorRepresentation (collectivePauliString I R p)).toEuclideanLin x) : ℂ) = 0 := by
    linear_combination hmove
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

end GaloisForLFunctions.HTGeometry
