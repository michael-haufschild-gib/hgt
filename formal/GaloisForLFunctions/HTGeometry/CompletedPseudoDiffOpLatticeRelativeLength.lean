import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCoweightIntervalLength
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCartanUniqueness
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpProjectiveRelativePosition
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingStandardApartment

/-!
# Relative lengths of included completed lattices

An included completed lattice is viewed as a submodule of its ambient lattice carrier.  Quotient
length is invariant under every completed-skew change of frame.  Cartan reduction then identifies
the quotient length of any included finite-rank pair with the sum of the nonnegative canonical
relative-position coordinates in the reverse ordered pair.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- An included completed lattice viewed inside the carrier of the larger lattice. -/
def completedPseudoDiffOpLatticeSubmoduleOf (L M : CompletedPseudoDiffOpLattice K ι)
    (_h : L.carrier ≤ M.carrier) : Submodule (CompletedPseudoDiffOpInteger (K := K)) M.carrier :=
  Submodule.comap M.carrier.subtype L.carrier

/-- Completed-skew transport restricts to an integral linear equivalence of lattice carriers. -/
def completedPseudoDiffOpLatticeCarrierMapLinearEquiv
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L : CompletedPseudoDiffOpLattice K ι) :
    L.carrier ≃ₗ[CompletedPseudoDiffOpInteger (K := K)] (mapCompletedPseudoDiffOpLatticeLinear e L).carrier where
  toFun x := ⟨e x.1,
    (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L _).2 ⟨x.1, x.2, rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1
  map_smul' c x := by
    apply Subtype.ext
    exact (restrictCompletedPseudoVecLinearEquiv e).map_smul c x.1
  invFun y := ⟨e.symm y.1, by
    obtain ⟨x, hx, hxy⟩ :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L y.1).1 y.2
    have : x = e.symm y.1 := by
      apply e.injective
      simpa using hxy
    rwa [← this]⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- Carrier transport maps an included lattice submodule to the transported included lattice. -/
theorem map_completedPseudoDiffOpLatticeSubmoduleOf
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) (h : L.carrier ≤ M.carrier) :
    Submodule.map (completedPseudoDiffOpLatticeCarrierMapLinearEquiv e M).toLinearMap
        (completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      completedPseudoDiffOpLatticeSubmoduleOf
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M)
        ((mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff e L M).2 h) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e x.1 ∈ (mapCompletedPseudoDiffOpLatticeLinear e L).carrier
    exact (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L _).2
      ⟨x.1, hx, rfl⟩
  · intro hy
    change y.1 ∈ (mapCompletedPseudoDiffOpLatticeLinear e L).carrier at hy
    obtain ⟨x, hx, hxy⟩ :=
      (mem_mapCompletedPseudoDiffOpLatticeLinear_iff e L y.1).1 hy
    let z : M.carrier := ⟨x, h hx⟩
    refine ⟨z, hx, ?_⟩
    apply Subtype.ext
    exact hxy

/-- Simultaneous completed-skew transport induces an equivalence of lattice quotients. -/
def completedPseudoDiffOpLatticeQuotientMapLinearEquiv
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) (h : L.carrier ≤ M.carrier) :
    (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      ((mapCompletedPseudoDiffOpLatticeLinear e M).carrier ⧸
        completedPseudoDiffOpLatticeSubmoduleOf
          (mapCompletedPseudoDiffOpLatticeLinear e L)
          (mapCompletedPseudoDiffOpLatticeLinear e M)
          ((mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff e L M).2 h)) :=
  Submodule.Quotient.equiv _ _ (completedPseudoDiffOpLatticeCarrierMapLinearEquiv e M)
    (map_completedPseudoDiffOpLatticeSubmoduleOf e L M h)

/-- Relative lattice quotient length is invariant under completed-skew frame changes. -/
theorem completedPseudoDiffOpLatticeQuotient_length_mapLinear
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) (h : L.carrier ≤ M.carrier) :
    Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      Module.length (CompletedPseudoDiffOpInteger (K := K))
        ((mapCompletedPseudoDiffOpLatticeLinear e M).carrier ⧸
          completedPseudoDiffOpLatticeSubmoduleOf
            (mapCompletedPseudoDiffOpLatticeLinear e L)
            (mapCompletedPseudoDiffOpLatticeLinear e M)
            ((mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff e L M).2 h)) :=
  (completedPseudoDiffOpLatticeQuotientMapLinearEquiv e L M h).length_eq

/-- Equal included lattice pairs have equal quotient lengths, independent of inclusion proofs. -/
theorem completedPseudoDiffOpLatticeQuotient_length_congr
    (L M L' M' : CompletedPseudoDiffOpLattice K ι)
    (h : L.carrier ≤ M.carrier) (h' : L'.carrier ≤ M'.carrier)
    (hL : L = L') (hM : M = M') :
    Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      Module.length (CompletedPseudoDiffOpInteger (K := K)) (M'.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L' M' h') := by
  subst L'
  subst M'
  rfl

variable {r : ℕ}

/-- Reversing an included lattice pair gives a coordinatewise nonnegative Cartan vector. -/
theorem completedPseudoDiffOpDominantRelativePosition_nonneg_of_carrier_le
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) (h : L.carrier ≤ M.carrier) (i : Fin r) :
    0 ≤ completedPseudoDiffOpDominantRelativePosition M L i := by
  let d := completedPseudoDiffOpDominantCartanData M L
  change 0 ≤ d.coweight i
  have hmap : (mapCompletedPseudoDiffOpLatticeLinear d.frame L).carrier ≤
      (mapCompletedPseudoDiffOpLatticeLinear d.frame M).carrier :=
    (mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame L M).2 h
  rw [d.map_left, d.map_right] at hmap
  rw [← standardCompletedPseudoDiffOpLatticeAtCoweight_zero] at hmap
  have hi :=
    (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      d.coweight (fun _ : Fin r => 0)).1 hmap i
  exact hi

/-- Quotient length of an included pair is the sum of its reverse Cartan coordinates. -/
theorem completedPseudoDiffOpLatticeQuotient_length_eq_sum_relativePosition
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) (h : L.carrier ≤ M.carrier) :
    Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      ∑ i, Int.toNat (completedPseudoDiffOpDominantRelativePosition M L i) := by
  let d := completedPseudoDiffOpDominantCartanData M L
  change Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
    ∑ i, Int.toNat (d.coweight i)
  let w : Fin r → ℕ := fun i => Int.toNat (d.coweight i)
  have hw : (fun i : Fin r => (0 : ℤ) + (w i : ℤ)) = d.coweight := by
    funext i
    simp only [zero_add, w]
    rw [Int.toNat_of_nonneg]
    exact completedPseudoDiffOpDominantRelativePosition_nonneg_of_carrier_le L M h i
  have hlen := completedPseudoDiffOpLatticeQuotient_length_mapLinear d.frame L M h
  have hzero : standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
      (fun _ : Fin r => 0) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) :=
    standardCompletedPseudoDiffOpLatticeAtCoweight_zero
  have hinside :
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight).carrier ≤
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => 0)).carrier :=
    (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      d.coweight (fun _ : Fin r => 0)).2 fun i => by
        exact completedPseudoDiffOpDominantRelativePosition_nonneg_of_carrier_le L M h i
  have hlen' : Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      Module.length (CompletedPseudoDiffOpInteger (K := K))
        ((standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
            (fun _ : Fin r => 0)).carrier ⧸
          standardCompletedPseudoDiffOpCoweightIntervalInside
            (K := K) d.coweight (fun _ => 0)) := by
    exact hlen.trans (completedPseudoDiffOpLatticeQuotient_length_congr
      (mapCompletedPseudoDiffOpLatticeLinear d.frame L)
      (mapCompletedPseudoDiffOpLatticeLinear d.frame M)
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight)
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => 0))
      ((mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame L M).2 h)
      hinside d.map_right (d.map_left.trans hzero.symm))
  have hinterval := standardCompletedPseudoDiffOpCoweightIntervalQuotient_length
    (K := K) (n := fun _ : Fin r => 0) w
  rw [hw] at hinterval
  rw [hlen']
  exact hinterval

end

end GaloisForLFunctions.HTGeometry.DiffOp
