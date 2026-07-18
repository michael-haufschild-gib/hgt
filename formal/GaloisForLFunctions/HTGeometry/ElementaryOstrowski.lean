import GaloisForLFunctions.HTGeometry.AlgebraicPrimitiveDescent
import GaloisForLFunctions.HTGeometry.KaehlerKernel
import GaloisForLFunctions.HTGeometry.SemilinearKaehlerDescent

/-!
# The elementary several-automorphism Ostrowski circuit

Combine three unconditional ingredients:

1. algebraic dependence gives a nonzero Kähler circuit;
2. additive base-field shifts make its relation space semilinearly stable;
3. a least-support relation descends its coefficients to the joint fixed
   field.

The result is a nonzero constant-coefficient algebraic relation among the
dependent additive primitives.  The characteristic-zero identification of
the kernel of the universal derivation with the relative algebraic closure
then supplies the simultaneous telescoping conclusion.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The universal relative derivation of a constant-coefficient linear
combination is the same constant-coefficient combination of the universal
differentials. -/
theorem kaehlerD_constantCoefficient_linearCombination
    {kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    (x : kappa → L) (c : kappa →₀ C) :
    KaehlerDifferential.D K L
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) =
      Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  simp only [smul_eq_mul]
  rw [IsScalarTower.algebraMap_apply C K L]
  rw [← Algebra.smul_def, Derivation.map_smul]
  simp

/-- Algebraically dependent additive primitives admit a nonzero Kähler
relation with coefficients in the declared joint constant field. -/
theorem exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      Finsupp.linearCombination L
        (fun k ↦ KaehlerDifferential.D K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) = 0 := by
  classical
  let W : Submodule L (kappa →₀ L) :=
    LinearMap.ker (Finsupp.linearCombination L
      (fun k ↦ KaehlerDifferential.D K L (x k)))
  obtain ⟨u, hu0, hurel⟩ :=
    exists_nonzero_kaehler_relation_of_not_algebraicIndependent x hdep
  have huW : u ∈ W := by
    exact LinearMap.mem_ker.mpr hurel
  have hW0 : W ≠ ⊥ := by
    intro hbot
    have : u ∈ (⊥ : Submodule L (kappa →₀ L)) := by
      simpa [hbot] using huW
    exact hu0 (by simpa using this)
  have hWstable : ∀ i v, v ∈ W →
      finsuppMapRangeRingEquiv SL.aut i v ∈ W := by
    intro i v hv
    exact kaehler_relationSpace_stable_of_base_shifts
      SK.aut SL.aut hcomp x b hshift i v hv
  have hfixed' : ∀ z : L, (∀ i, SL.aut i z = z) →
      ∃ c : C, algebraMap C L c = z := by
    intro z hz
    exact hfixed z hz
  obtain ⟨c, hc0, hcW⟩ :=
    stable_finsupp_submodule_exists_nonzero_constant_vector
      SL.aut hfixed' W hWstable hW0
  exact ⟨c, hc0, LinearMap.mem_ker.mp hcW⟩

/-- Equivalent differential form of the preceding circuit: a nonzero
constant-coefficient linear combination of the dependent primitives lies in
the kernel of the universal relative derivation. -/
theorem exists_nonzero_constant_linearCombination_kaehlerD_eq_zero
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      KaehlerDifferential.D K L
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) = 0 := by
  obtain ⟨c, hc0, hrel⟩ :=
    exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
      SK SL hcomp hfixed x b hshift hdep
  refine ⟨c, hc0, ?_⟩
  rw [kaehlerD_constantCoefficient_linearCombination]
  exact hrel

/-- Algebraically dependent additive primitives admit a nonzero
constant-coefficient linear combination algebraic over the base field. -/
theorem exists_nonzero_constant_algebraic_linearCombination_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      IsAlgebraic K
        (Finsupp.linearCombination L x
          (Finsupp.mapRange (algebraMap C L)
            (map_zero (algebraMap C L)) c)) := by
  obtain ⟨c, hc0, hD⟩ :=
    exists_nonzero_constant_linearCombination_kaehlerD_eq_zero
      SK SL hcomp hfixed x b hshift hdep
  exact ⟨c, hc0, isAlgebraic_of_kaehlerD_eq_zero hD⟩

/-- A finitely supported linear combination distributes over pointwise
addition of the underlying family. -/
theorem finsupp_linearCombination_add_family
    {kappa L : Type*} [Field L]
    (x y : kappa → L) (c : kappa →₀ L) :
    Finsupp.linearCombination L (fun k ↦ x k + y k) c =
      Finsupp.linearCombination L x c +
        Finsupp.linearCombination L y c := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]

/-- Base extension commutes with a constant-coefficient finitely supported
linear combination. -/
theorem algebraMap_constant_finsupp_linearCombination
    {kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    (x : kappa → K) (c : kappa →₀ C) :
    algebraMap K L
        (Finsupp.linearCombination K x
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) =
      Finsupp.linearCombination L (fun k ↦ algebraMap K L (x k))
        (Finsupp.mapRange (algebraMap C L)
          (map_zero (algebraMap C L)) c) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [Finsupp.sum_mapRange_index (fun _ ↦ by simp)]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  simp only [smul_eq_mul, map_mul]
  rw [IsScalarTower.algebraMap_apply C K L]

/-- Full elementary Ostrowski descent: a dependent family of additive
primitives has a nonzero constant-coefficient linear combination equal to a
base-field element plus a joint constant. -/
theorem exists_nonzero_constant_linearCombination_eq_base_add_constant_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      ∃ k : K, ∃ c0 : C,
        Finsupp.linearCombination L x
            (Finsupp.mapRange (algebraMap C L)
              (map_zero (algebraMap C L)) c) =
          algebraMap K L k + algebraMap C L c0 := by
  classical
  obtain ⟨c, hc0, hcalg⟩ :=
    exists_nonzero_constant_algebraic_linearCombination_of_dependent_base_shifts
      SK SL hcomp hfixed x b hshift hdep
  let cL : kappa →₀ L := Finsupp.mapRange (algebraMap C L)
    (map_zero (algebraMap C L)) c
  let cK : kappa →₀ K := Finsupp.mapRange (algebraMap C K)
    (map_zero (algebraMap C K)) c
  let g : L := Finsupp.linearCombination L x cL
  let bsum : I → K := fun i ↦ Finsupp.linearCombination K (b i) cK
  have hshiftg : ∀ i, SL.aut i g = g + algebraMap K L (bsum i) := by
    intro i
    dsimp only [g]
    rw [ringEquiv_linearCombination]
    have hcmap :
        Finsupp.mapRange (SL.aut i) (map_zero (SL.aut i)) cL = cL := by
      ext j
      simp [cL, SL.aut_algebraMap]
    rw [hcmap]
    simp_rw [hshift]
    rw [finsupp_linearCombination_add_family]
    rw [algebraMap_constant_finsupp_linearCombination]
  have hgint : IsIntegral K g := hcalg.isIntegral
  obtain ⟨k, c0, hg⟩ :=
    algebraic_additive_primitive_eq_base_add_constant
      SK SL hcomp hfixed hgint bsum hshiftg
  exact ⟨c, hc0, k, c0, hg⟩

/-- **Unconditional several-automorphism Ostrowski theorem.** Algebraic
dependence of additive primitives forces one nonzero joint-constant linear
combination of all increment cocycles to be the coboundary of the same base
element in every automorphism direction. -/
theorem exists_nonzero_constant_simultaneous_telescoping_of_dependent_base_shifts
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hdep : ¬ AlgebraicIndependent K x) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧ ∃ k : K, ∀ i,
      SK.defect i k =
        Finsupp.linearCombination K (b i)
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c) := by
  classical
  obtain ⟨c, hc0, k, c0, hg⟩ :=
    exists_nonzero_constant_linearCombination_eq_base_add_constant_of_dependent_base_shifts
      SK SL hcomp hfixed x b hshift hdep
  let cL : kappa →₀ L := Finsupp.mapRange (algebraMap C L)
    (map_zero (algebraMap C L)) c
  let cK : kappa →₀ K := Finsupp.mapRange (algebraMap C K)
    (map_zero (algebraMap C K)) c
  let g : L := Finsupp.linearCombination L x cL
  let bsum : I → K := fun i ↦ Finsupp.linearCombination K (b i) cK
  have hg' : g = algebraMap K L k + algebraMap C L c0 := hg
  have hshiftg : ∀ i, SL.aut i g = g + algebraMap K L (bsum i) := by
    intro i
    dsimp only [g]
    rw [ringEquiv_linearCombination]
    have hcmap :
        Finsupp.mapRange (SL.aut i) (map_zero (SL.aut i)) cL = cL := by
      ext j
      simp [cL, SL.aut_algebraMap]
    rw [hcmap]
    simp_rw [hshift]
    rw [finsupp_linearCombination_add_family]
    rw [algebraMap_constant_finsupp_linearCombination]
  refine ⟨c, hc0, k, ?_⟩
  intro i
  apply (algebraMap K L).injective
  have hleft : SL.defect i g = algebraMap K L (bsum i) := by
    rw [CommutingDifferenceDifferentialField.defect, hshiftg i]
    abel
  have hright : SL.defect i g = algebraMap K L (SK.defect i k) := by
    rw [CommutingDifferenceDifferentialField.defect, hg', map_add,
      hcomp, SL.aut_algebraMap]
    simp only [CommutingDifferenceDifferentialField.defect, map_sub]
    abel
  rw [← hright, hleft]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

noncomputable section

/-- Contrapositive form of the unconditional several-automorphism Ostrowski
criterion. If no nonzero joint-constant linear combination of the increment
cocycles is the simultaneous coboundary of one base-field element, then the
additive primitives are algebraically independent. -/
theorem algebraicIndependent_of_no_constant_simultaneous_telescoping
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hnot : ∀ c : kappa →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      SK.defect i k ≠
        Finsupp.linearCombination K (b i)
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    AlgebraicIndependent K x := by
  by_contra hdep
  obtain ⟨c, hc0, k, hall⟩ :=
    exists_nonzero_constant_simultaneous_telescoping_of_dependent_base_shifts
      SK SL hcomp hfixed x b hshift hdep
  obtain ⟨i, hi⟩ := hnot c hc0 k
  exact hi (hall i)

/-- Differential jets commute with a differential-algebra structure map. -/
theorem differentialJet_algebraMap_of_differentialAlgebra
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (n : ℕ) (x : K) :
    differentialJet n (algebraMap K L x) =
      algebraMap K L (differentialJet n x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, ih,
        DifferentialAlgebra.deriv_algebraMap]

/-- Constant-coefficient differential operators commute with every differential-algebra
structure map. -/
theorem differentialOperatorApply_algebraMap_of_differentialAlgebra
    {C K L : Type*} [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    (hscalar : ∀ c : C,
      algebraMap K L (algebraMap C K c) = algebraMap C L c)
    (P : Polynomial C) (x : K) :
    algebraMap K L (differentialOperatorApply P x) =
      differentialOperatorApply P (algebraMap K L x) := by
  classical
  let phi : K →+* L := algebraMap K L
  unfold differentialOperatorApply
  rw [Polynomial.sum_def, Polynomial.sum_def]
  change phi (∑ n ∈ P.support,
    algebraMap C K (P.coeff n) * differentialJet n x) = _
  rw [map_sum phi]
  apply Finset.sum_congr rfl
  intro n hn
  change phi (algebraMap C K (P.coeff n) * differentialJet n x) = _
  rw [map_mul phi, differentialJet_algebraMap_of_differentialAlgebra]
  change algebraMap K L (algebraMap C K (P.coeff n)) *
      algebraMap K L (differentialJet n x) = _
  exact congrArg
    (fun c : L => c * algebraMap K L (differentialJet n x))
    (hscalar (P.coeff n))

/-- Every differential jet is additive. -/
theorem differentialJet_additive
    {L : Type*} [Field L] [Differential L] (n : ℕ) (x y : L) :
    differentialJet n (x + y) = differentialJet n x + differentialJet n y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, differentialJet_succ, differentialJet_succ, ih, map_add]

/-- **Unconditional differential Ostrowski criterion.** Suppose a family of
additive primitives has base-field increments for several commuting
automorphisms. If no nonzero finitely supported joint-constant linear
combination of any orders of the increment jets is the simultaneous
coboundary of one base-field element, then the primitive family is
differentially algebraically independent over the base field.

This is an all-orders statement: the finite support of `c` selects an
arbitrary finite collection of coordinates and derivative orders. -/
theorem differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    {I kappa C K L : Type*}
    [Field C] [Field K] [Field L]
    [Algebra C K] [Algebra C L] [Algebra K L]
    [IsScalarTower C K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L] [CharZero K]
    (SK : CommutingDifferenceDifferentialField I C K)
    (SL : CommutingDifferenceDifferentialField I C L)
    (hcomp : ∀ i k, SL.aut i (algebraMap K L k) =
      algebraMap K L (SK.aut i k))
    (hfixed : ∀ z : L, JointFixed SL z →
      ∃ c : C, algebraMap C L c = z)
    (x : kappa → L) (b : I → kappa → K)
    (hshift : ∀ i k, SL.aut i (x k) =
      x k + algebraMap K L (b i k))
    (hnot : ∀ c : (kappa × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
      SK.defect i k ≠
        Finsupp.linearCombination K
          (fun p ↦ differentialJet p.2 (b i p.1))
          (Finsupp.mapRange (algebraMap C K)
            (map_zero (algebraMap C K)) c)) :
    DifferentialIndependent K x := by
  let xJet : kappa × ℕ → L := fun p ↦ differentialJet p.2 (x p.1)
  let bJet : I → kappa × ℕ → K :=
    fun i p ↦ differentialJet p.2 (b i p.1)
  have hshiftJet : ∀ i p, SL.aut i (xJet p) =
      xJet p + algebraMap K L (bJet i p) := by
    intro i p
    dsimp only [xJet, bJet]
    rw [SL.aut_differentialJet, hshift]
    rw [differentialJet_additive,
      differentialJet_algebraMap_of_differentialAlgebra]
  have hAI : AlgebraicIndependent K xJet :=
    algebraicIndependent_of_no_constant_simultaneous_telescoping
      SK SL hcomp hfixed xJet bJet hshiftJet (by
        intro c hc0 k
        simpa only [bJet] using hnot c hc0 k)
  exact hAI

end

end GaloisForLFunctions
