import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.IntegerGluingCounts
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Arithmetic divisor lattices and transverse gluing height

The non-pole divisor columns generate a saturated integral lattice. Integral
inversion gives its actual basis, whose Gram determinant is the squarefree
count. Integer unit changes identify its squarefree Gram block and its
orthogonal unit directions.

The real span has an explicit Euclidean nearest-point projection. The
independent gluing count factors into the Gram volume of the integral
basis and the transverse distance of the arithmetic gluing column. Its
finite product-formula height splits into the corresponding logarithms.
-/

noncomputable section
open Finset Matrix ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory

/-- The actual non-pole divisor columns generate the arithmetic relation lattice. -/
def divisorRelationLattice (N : ℕ) (hN : 1 ≤ N) : Submodule ℤ (Vertex N → ℤ) :=
  (LinearMap.ker (LinearMap.proj (poleVertex N hN))).map
    (integerDivisibilityMatrix N).mulVecLin

/-- Pole coordinate after the inverse of the integral divisibility matrix. -/
def divisorNormal (N : ℕ) (hN : 1 ≤ N) : (Vertex N → ℤ) →ₗ[ℤ] ℤ :=
  (LinearMap.proj (poleVertex N hN)).comp (integerMoebiusMatrix N).mulVecLin

theorem divisorRelationLattice_eq_ker (N : ℕ) (hN : 1 ≤ N) :
    divisorRelationLattice N hN = LinearMap.ker (divisorNormal N hN) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (integerMoebiusMatrix N *ᵥ (integerDivisibilityMatrix N *ᵥ x))
      (poleVertex N hN) = 0
    rw [mulVec_mulVec, integerMoebius_mul_divisibility, one_mulVec]
    exact hx
  · intro hv
    refine ⟨integerMoebiusMatrix N *ᵥ v, hv, ?_⟩
    change integerDivisibilityMatrix N *ᵥ (integerMoebiusMatrix N *ᵥ v) = v
    rw [mulVec_mulVec, integerDivisibility_mul_moebius, one_mulVec]

theorem divisorNormal_apply (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℤ) :
    divisorNormal N hN v = ∑ i, moebius i.val * v i := by
  simp [divisorNormal, Matrix.mulVec, dotProduct, integerMoebiusMatrix, poleVertex]

theorem divisorNormal_single (N : ℕ) (hN : 1 ≤ N) (i : Vertex N) (a : ℤ) :
    divisorNormal N hN (Pi.single i a) = moebius i.val * a := by
  rw [divisorNormal_apply]
  simp [Pi.single_apply, mul_ite]

theorem divisorNormal_pole (N : ℕ) (hN : 1 ≤ N) (a : ℤ) :
    divisorNormal N hN (Pi.single (poleVertex N hN) a) = a := by
  rw [divisorNormal_single]
  simp [poleVertex]

/-- Arithmetic labels other than the unit label. -/
abbrev NonPoleVertex (N : ℕ) (hN : 1 ≤ N) := {i : Vertex N // i ≠ poleVertex N hN}

/-- Extend non-pole coordinates by zero at the unit label. -/
def nonPoleExtension (N : ℕ) (hN : 1 ≤ N) :
    (NonPoleVertex N hN → ℤ) →ₗ[ℤ] (Vertex N → ℤ) where
  toFun c i := if hi : i = poleVertex N hN then 0 else c ⟨i, hi⟩
  map_add' c d := by ext i; by_cases hi : i = poleVertex N hN <;> simp [hi]
  map_smul' a c := by ext i; by_cases hi : i = poleVertex N hN <;> simp [hi]

/-- Correct the pole coordinate so the integral normal vanishes. -/
def divisorGraphMap (N : ℕ) (hN : 1 ≤ N) :
    (NonPoleVertex N hN → ℤ) →ₗ[ℤ] (Vertex N → ℤ) :=
  nonPoleExtension N hN -
    (LinearMap.single ℤ (fun _ : Vertex N => ℤ) (poleVertex N hN)).comp
      ((divisorNormal N hN).comp (nonPoleExtension N hN))

theorem divisorGraphMap_apply (N : ℕ) (hN : 1 ≤ N) (c : NonPoleVertex N hN → ℤ) :
    divisorGraphMap N hN c = nonPoleExtension N hN c -
      Pi.single (poleVertex N hN) (divisorNormal N hN (nonPoleExtension N hN c)) := rfl

theorem divisorGraphMap_mem (N : ℕ) (hN : 1 ≤ N) (c : NonPoleVertex N hN → ℤ) :
    divisorGraphMap N hN c ∈ divisorRelationLattice N hN := by
  rw [divisorRelationLattice_eq_ker, LinearMap.mem_ker, divisorGraphMap_apply,
    map_sub, divisorNormal_pole, sub_self]

/-- Restriction to non-pole coordinates is an integral equivalence for the actual lattice. -/
def divisorRelationCoordinates (N : ℕ) (hN : 1 ≤ N) :
    (NonPoleVertex N hN → ℤ) ≃ₗ[ℤ] divisorRelationLattice N hN where
  toFun c := ⟨divisorGraphMap N hN c, divisorGraphMap_mem N hN c⟩
  invFun v j := v.val j.val
  left_inv c := by
    funext j
    change divisorGraphMap N hN c j.val = c j
    rw [divisorGraphMap_apply]
    simp [nonPoleExtension, j.property]
  right_inv v := by
    apply Subtype.ext
    have hv : divisorNormal N hN v.val = 0 := by
      exact (divisorRelationLattice_eq_ker N hN).le v.property
    have he : nonPoleExtension N hN (fun j => v.val j.val) =
        v.val - Pi.single (poleVertex N hN) (v.val (poleVertex N hN)) := by
      funext i
      by_cases hi : i = poleVertex N hN
      · subst i
        simp [nonPoleExtension]
      · simp [nonPoleExtension, hi]
    change divisorGraphMap N hN (fun j => v.val j.val) = v.val
    rw [divisorGraphMap_apply, he, map_sub, hv, divisorNormal_pole, zero_sub]
    simp only [Pi.single_neg]
    abel
  map_add' c d := by apply Subtype.ext; exact (divisorGraphMap N hN).map_add c d
  map_smul' a c := by apply Subtype.ext; exact (divisorGraphMap N hN).map_smul a c

theorem nonPoleExtension_single (N : ℕ) (hN : 1 ≤ N) (j : NonPoleVertex N hN) :
    nonPoleExtension N hN (Pi.single j 1) = Pi.single j.val 1 := by
  funext i
  by_cases hi : i = poleVertex N hN
  · subst i
    simp [nonPoleExtension, Pi.single_eq_of_ne j.property.symm]
  · by_cases hij : i = j.val
    · subst i
      simp [nonPoleExtension, j.property]
    · have hsub : (⟨i, hi⟩ : NonPoleVertex N hN) ≠ j :=
        fun h => hij (congrArg Subtype.val h)
      simp [nonPoleExtension, hi, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hsub]

/-- The integral basis transported through the explicit coordinate equivalence. -/
def divisorRelationBasis (N : ℕ) (hN : 1 ≤ N) :
    Module.Basis (NonPoleVertex N hN) ℤ (divisorRelationLattice N hN) :=
  (Pi.basisFun ℤ (NonPoleVertex N hN)).map (divisorRelationCoordinates N hN)

theorem divisorRelationBasis_coe (N : ℕ) (hN : 1 ≤ N) (j : NonPoleVertex N hN) :
    (divisorRelationBasis N hN j : Vertex N → ℤ) =
      Pi.single j.val 1 - Pi.single (poleVertex N hN) (moebius j.val.val) := by
  simp only [divisorRelationBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change divisorGraphMap N hN (Pi.single j 1) = _
  rw [divisorGraphMap_apply, nonPoleExtension_single, divisorNormal_single, mul_one]

/-- Integer dot products of the actual integral basis vectors. -/
def divisorRelationGram (N : ℕ) (hN : 1 ≤ N) :
    Matrix (NonPoleVertex N hN) (NonPoleVertex N hN) ℤ :=
  fun j k => (divisorRelationBasis N hN j : Vertex N → ℤ) ⬝ᵥ
    (divisorRelationBasis N hN k : Vertex N → ℤ)

theorem divisorRelationGram_apply (N : ℕ) (hN : 1 ≤ N) (j k : NonPoleVertex N hN) :
    divisorRelationGram N hN j k =
      (if j = k then 1 else 0) + moebius j.val.val * moebius k.val.val := by
  unfold divisorRelationGram
  rw [divisorRelationBasis_coe, divisorRelationBasis_coe,
    sub_dotProduct, dotProduct_sub, dotProduct_sub]
  rw [single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  rw [Pi.single_eq_of_ne j.property, Pi.single_eq_of_ne k.property.symm,
    Pi.single_eq_same]
  have he : (j.val = k.val) ↔ j = k := Subtype.ext_iff.symm
  simp only [Pi.single_apply, he, one_mul, mul_zero, sub_zero, zero_sub, sub_neg_eq_add]

theorem divisorRelationGram_eq (N : ℕ) (hN : 1 ≤ N) :
    divisorRelationGram N hN = 1 + vecMulVec
      (fun j => moebius j.val.val) (fun j => moebius j.val.val) := by
  ext j k
  rw [divisorRelationGram_apply]
  rfl

theorem divisorRelationGram_det (N : ℕ) (hN : 1 ≤ N) :
    (divisorRelationGram N hN).det = 1 + ∑ j : NonPoleVertex N hN, moebius j.val.val ^ 2 := by
  rw [divisorRelationGram_eq]
  have he : vecMulVec (fun j : NonPoleVertex N hN => moebius j.val.val)
      (fun j : NonPoleVertex N hN => moebius j.val.val) =
      replicateCol Unit (fun j : NonPoleVertex N hN => moebius j.val.val) *
        replicateRow Unit (fun j : NonPoleVertex N hN => moebius j.val.val) := by
    ext j k
    simp [Matrix.mul_apply, vecMulVec, replicateCol, replicateRow]
  rw [he, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, pow_two]

private theorem sum_nonPole_add_pole {R : Type*} [AddCommMonoid R]
    (N : ℕ) (hN : 1 ≤ N) (f : Vertex N → R) :
    (∑ j : NonPoleVertex N hN, f j.val) + f (poleVertex N hN) = ∑ i, f i := by
  have hs : (∑ j : NonPoleVertex N hN, f j.val) =
      ∑ i ∈ univ.erase (poleVertex N hN), f i :=
    (Finset.sum_subtype _ (fun i => by simp) f).symm
  rw [hs]
  exact Finset.sum_erase_add univ f (mem_univ _)

/-- The independent count of squarefree arithmetic labels through the cutoff. -/
def divisorSquarefreeCount (N : ℕ) : ℕ := ((Icc 1 N).filter Squarefree).card

theorem divisorNormal_square_sum (N : ℕ) :
    (∑ i : Vertex N, moebius i.val ^ 2) = (divisorSquarefreeCount N : ℤ) := by
  rw [← Finset.sum_subtype (Icc 1 N) (fun _ => Iff.rfl) (fun n => moebius n ^ 2)]
  simp_rw [ArithmeticFunction.moebius_sq]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rfl

theorem divisorRelationGram_det_eq_squarefreeCount (N : ℕ) (hN : 1 ≤ N) :
    (divisorRelationGram N hN).det = (divisorSquarefreeCount N : ℤ) := by
  rw [divisorRelationGram_det]
  have hs := sum_nonPole_add_pole N hN (fun i => moebius i.val ^ 2)
  simp only [poleVertex, moebius_apply_one, one_pow] at hs
  rw [divisorNormal_square_sum] at hs
  linarith only [hs]

#print axioms divisorRelationCoordinates
#print axioms divisorRelationBasis_coe
#print axioms divisorRelationGram_det_eq_squarefreeCount

#print axioms divisorRelationLattice_eq_ker


theorem divisorSquarefreeCount_pos (N : ℕ) (hN : 1 ≤ N) : 0 < divisorSquarefreeCount N := by
  apply Finset.card_pos.mpr
  exact ⟨1, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hN⟩, by simp⟩⟩

theorem divisorSquarefreeCount_le (N : ℕ) : divisorSquarefreeCount N ≤ N := by
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Euclidean Gram volume of the constructed integral basis. -/
def divisorRelationVolume (N : ℕ) (hN : 1 ≤ N) : ℝ :=
  Real.sqrt ((divisorRelationGram N hN).det : ℝ)

theorem divisorRelationVolume_eq (N : ℕ) (hN : 1 ≤ N) :
    divisorRelationVolume N hN = Real.sqrt (divisorSquarefreeCount N) := by
  rw [divisorRelationVolume, divisorRelationGram_det_eq_squarefreeCount]
  norm_cast

theorem divisorRelationVolume_pos (N : ℕ) (hN : 1 ≤ N) : 0 < divisorRelationVolume N hN := by
  rw [divisorRelationVolume_eq]
  exact Real.sqrt_pos.mpr (by exact_mod_cast divisorSquarefreeCount_pos N hN)

theorem divisorRelationVolume_le_sqrt (N : ℕ) (hN : 1 ≤ N) :
    divisorRelationVolume N hN ≤ Real.sqrt N := by
  rw [divisorRelationVolume_eq]
  exact Real.sqrt_le_sqrt (by exact_mod_cast divisorSquarefreeCount_le N)

/-- The actual integral basis embedded in real coordinate space. -/
def divisorRelationRealBasis (N : ℕ) (hN : 1 ≤ N) (j : NonPoleVertex N hN) :
    Vertex N → ℝ := fun i => (divisorRelationBasis N hN j : Vertex N → ℤ) i

/-- Real span of the embedded divisor-relation basis. -/
def divisorRelationRealSpace (N : ℕ) (hN : 1 ≤ N) : Submodule ℝ (Vertex N → ℝ) :=
  Submodule.span ℝ (Set.range (divisorRelationRealBasis N hN))

/-- The real normal functional obtained from the integral inverse row. -/
def divisorRealNormal (N : ℕ) : (Vertex N → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, (moebius i.val : ℝ) * v i
  map_add' v w := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm, mul_sum]

/-- The Euclidean normal vector to the divisor-relation span. -/
def divisorNormalVector (N : ℕ) : Vertex N → ℝ := fun i => moebius i.val

theorem divisorRelationRealBasis_apply (N : ℕ) (hN : 1 ≤ N)
    (j : NonPoleVertex N hN) (i : Vertex N) :
    divisorRelationRealBasis N hN j i =
      (if i = j.val then 1 else 0) -
        (if i = poleVertex N hN then (moebius j.val.val : ℝ) else 0) := by
  rw [divisorRelationRealBasis, divisorRelationBasis_coe]
  simp only [Pi.sub_apply, Int.cast_sub, Pi.single_apply]
  split_ifs <;> simp

theorem divisorRealNormal_basis (N : ℕ) (hN : 1 ≤ N) (j : NonPoleVertex N hN) :
    divisorRealNormal N (divisorRelationRealBasis N hN j) = 0 := by
  change (∑ i, (moebius i.val : ℝ) * divisorRelationRealBasis N hN j i) = 0
  simp_rw [divisorRelationRealBasis_apply, mul_sub, mul_ite, mul_one, mul_zero]
  rw [sum_sub_distrib]
  simp [poleVertex]

theorem mem_divisorRelationRealSpace_iff (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℝ) :
    v ∈ divisorRelationRealSpace N hN ↔ divisorRealNormal N v = 0 := by
  constructor
  · intro hv
    have hle : divisorRelationRealSpace N hN ≤ LinearMap.ker (divisorRealNormal N) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact divisorRealNormal_basis N hN j
    exact hle hv
  · intro hv
    have hs := sum_nonPole_add_pole N hN (fun i => (moebius i.val : ℝ) * v i)
    have hs0 : (∑ j : NonPoleVertex N hN, (moebius j.val.val : ℝ) * v j.val) +
        v (poleVertex N hN) = 0 := by
      simpa only [poleVertex, moebius_apply_one, Int.cast_one, one_mul] using hs.trans hv
    have he : v = ∑ j : NonPoleVertex N hN, v j.val • divisorRelationRealBasis N hN j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = poleVertex N hN
      · subst i
        have ht (j : NonPoleVertex N hN) :
            v j.val * divisorRelationRealBasis N hN j (poleVertex N hN) =
              -((moebius j.val.val : ℝ) * v j.val) := by
          rw [divisorRelationRealBasis_apply, if_neg j.property.symm, if_pos rfl]
          ring
        rw [sum_congr rfl (fun j _ => ht j), sum_neg_distrib]
        linarith only [hs0]
      · rw [sum_eq_single (⟨i, hi⟩ : NonPoleVertex N hN)]
        · rw [divisorRelationRealBasis_apply, if_pos rfl, if_neg hi]
          ring
        · intro j _ hj
          have hij : i ≠ j.val := fun h => hj (Subtype.ext h.symm)
          rw [divisorRelationRealBasis_apply, if_neg hij, if_neg hi]
          ring
        · intro h
          exact (h (mem_univ _)).elim
    rw [he]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Squared Euclidean coordinate length, independently of the default function-space norm. -/
def divisorEuclideanSq (N : ℕ) (v : Vertex N → ℝ) : ℝ := ∑ i, (v i)^2

theorem divisorEuclideanSq_nonneg (N : ℕ) (v : Vertex N → ℝ) :
    0 ≤ divisorEuclideanSq N v := sum_nonneg (fun i _ => sq_nonneg (v i))

theorem divisorNormalVector_square_sum (N : ℕ) :
    divisorEuclideanSq N (divisorNormalVector N) = (divisorSquarefreeCount N : ℝ) := by
  have h := divisorNormal_square_sum N
  change (∑ i : Vertex N, (moebius i.val : ℝ)^2) = (divisorSquarefreeCount N : ℝ)
  exact_mod_cast h

theorem divisorRealNormal_vector (N : ℕ) :
    divisorRealNormal N (divisorNormalVector N) = (divisorSquarefreeCount N : ℝ) := by
  change (∑ i : Vertex N, (moebius i.val : ℝ) * (moebius i.val : ℝ)) = _
  simpa only [divisorNormalVector, divisorEuclideanSq, pow_two]
    using divisorNormalVector_square_sum N

/-- Subtract the Euclidean normal component of a real arithmetic vector. -/
def divisorRelationProjection (N : ℕ) (v : Vertex N → ℝ) : Vertex N → ℝ :=
  v - (divisorRealNormal N v / divisorSquarefreeCount N) • divisorNormalVector N

theorem divisorRelationProjection_mem (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℝ) :
    divisorRelationProjection N v ∈ divisorRelationRealSpace N hN := by
  rw [mem_divisorRelationRealSpace_iff, divisorRelationProjection, map_sub, map_smul,
    divisorRealNormal_vector, smul_eq_mul, div_mul_cancel₀, sub_self]
  exact (by exact_mod_cast (divisorSquarefreeCount_pos N hN).ne' :
    (divisorSquarefreeCount N : ℝ) ≠ 0)

/-- Orthogonality separates the normal component from every displacement within the actual span. -/
theorem divisorRelation_pythagorean (N : ℕ) (hN : 1 ≤ N) (v y : Vertex N → ℝ)
    (hy : y ∈ divisorRelationRealSpace N hN) :
    divisorEuclideanSq N (v-y) = (divisorRealNormal N v)^2 / divisorSquarefreeCount N +
      divisorEuclideanSq N (divisorRelationProjection N v-y) := by
  let a := divisorRealNormal N v / divisorSquarefreeCount N
  let t := divisorRelationProjection N v
  have hQ : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  have ht : divisorRealNormal N (t-y) = 0 := by
    rw [map_sub, (mem_divisorRelationRealSpace_iff N hN _).mp
      (divisorRelationProjection_mem N hN v), (mem_divisorRelationRealSpace_iff N hN y).mp hy,
      sub_self]
  have hcross : (∑ i, (t i-y i) * (a*divisorNormalVector N i)) = 0 := by
    calc
      _ = a * divisorRealNormal N (t-y) := by
        change _ = a * ∑ i, (moebius i.val : ℝ) * (t i-y i)
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        dsimp only [divisorNormalVector]
        ring
      _ = 0 := by rw [ht, mul_zero]
  have hexpand : divisorEuclideanSq N (v-y) = divisorEuclideanSq N (t-y) +
      2 * (∑ i, (t i-y i)*(a*divisorNormalVector N i)) +
        a^2 * divisorEuclideanSq N (divisorNormalVector N) := by
    simp only [divisorEuclideanSq, Pi.sub_apply, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    dsimp [t, divisorRelationProjection, a]
    ring
  rw [hexpand, hcross, mul_zero, add_zero, divisorNormalVector_square_sum]
  dsimp only [a, t]
  field_simp [hQ]
  ring

theorem divisorRelationProjection_minimizes (N : ℕ) (hN : 1 ≤ N) (v y : Vertex N → ℝ)
    (hy : y ∈ divisorRelationRealSpace N hN) :
    divisorEuclideanSq N (v-divisorRelationProjection N v) ≤ divisorEuclideanSq N (v-y) := by
  rw [divisorRelation_pythagorean N hN v _ (divisorRelationProjection_mem N hN v),
    divisorRelation_pythagorean N hN v y hy]
  simp only [sub_self, divisorEuclideanSq, Pi.zero_apply, zero_pow (by omega : 2 ≠ 0),
    sum_const_zero, add_zero]
  exact le_add_of_nonneg_right (sum_nonneg (fun i _ => sq_nonneg _))

/-- Euclidean distance to the explicitly proved minimizing projection. -/
def divisorTransverseDistance (N : ℕ) (v : Vertex N → ℝ) : ℝ :=
  Real.sqrt (divisorEuclideanSq N (v-divisorRelationProjection N v))

theorem divisorTransverseDistance_formula (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℝ) :
    divisorTransverseDistance N v =
      Real.sqrt ((divisorRealNormal N v)^2 / divisorSquarefreeCount N) := by
  rw [divisorTransverseDistance, divisorRelation_pythagorean N hN v _
    (divisorRelationProjection_mem N hN v)]
  simp [divisorEuclideanSq]

theorem divisorRelationVolume_mul_distance (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℝ) :
    divisorRelationVolume N hN * divisorTransverseDistance N v = |divisorRealNormal N v| := by
  rw [divisorRelationVolume_eq, divisorTransverseDistance_formula N hN,
    ← Real.sqrt_mul (Nat.cast_nonneg (divisorSquarefreeCount N))]
  have hQ : (divisorSquarefreeCount N : ℝ) ≠ 0 := by
    exact_mod_cast (divisorSquarefreeCount_pos N hN).ne'
  have he : (divisorSquarefreeCount N : ℝ) *
      ((divisorRealNormal N v)^2 / divisorSquarefreeCount N) = (divisorRealNormal N v)^2 := by
    field_simp [hQ]
  rw [he, Real.sqrt_sq_eq_abs]

/-- The independently defined integral gluing column embedded in real coordinates. -/
def integerGluingRealColumn (N : ℕ) : Vertex N → ℝ := fun i => integerGluingColumn N i

theorem divisorRealNormal_gluing (N : ℕ) (hN : 1 ≤ N) :
    divisorRealNormal N (integerGluingRealColumn N) = (integerGluingCharge N : ℝ) := by
  have h : divisorNormal N hN (integerGluingColumn N) = integerGluingCharge N :=
    integerMoebius_pole_row N hN
  rw [divisorNormal_apply] at h
  change (∑ i : Vertex N, (moebius i.val : ℝ) * (integerGluingColumn N i : ℝ)) = _
  exact_mod_cast h

theorem integerGluingCount_volume_distance (N : ℕ) (hN : 1 ≤ N) :
    (integerGluingCount N : ℝ) = divisorRelationVolume N hN *
      divisorTransverseDistance N (integerGluingRealColumn N) := by
  rw [divisorRelationVolume_mul_distance N hN, divisorRealNormal_gluing N hN,
    integerGluingCount_eq N hN, Nat.cast_natAbs, Int.cast_abs]

theorem integerGluingCount_le_sqrt_mul_distance (N : ℕ) (hN : 1 ≤ N) :
    (integerGluingCount N : ℝ) ≤ Real.sqrt N *
      divisorTransverseDistance N (integerGluingRealColumn N) := by
  rw [integerGluingCount_volume_distance N hN]
  exact mul_le_mul_of_nonneg_right (divisorRelationVolume_le_sqrt N hN) (Real.sqrt_nonneg _)

#print axioms divisorRelationVolume_le_sqrt
#print axioms mem_divisorRelationRealSpace_iff
#print axioms divisorRelation_pythagorean
#print axioms divisorRelationProjection_minimizes
#print axioms integerGluingCount_volume_distance
#print axioms integerGluingCount_le_sqrt_mul_distance

/-- A sign making each nonzero Möbius coefficient positive. -/
def divisorOrientationSign (n : ℕ) : ℤ := if moebius n = -1 then -1 else 1

theorem divisorOrientationSign_sq (n : ℕ) : divisorOrientationSign n ^ 2 = 1 := by
  unfold divisorOrientationSign
  split_ifs <;> norm_num

theorem divisorOrientationSign_mul (n : ℕ) :
    divisorOrientationSign n * moebius n = moebius n ^ 2 := by
  by_cases hz : moebius n = 0
  · simp [hz]
  · rcases moebius_ne_zero_iff_eq_or.mp hz with h | h <;>
      simp [divisorOrientationSign, h]

/-- The sign correction as an actual integer unit. -/
def divisorOrientationUnit (n : ℕ) : ℤˣ :=
  Units.mkOfMulEqOne (divisorOrientationSign n) (divisorOrientationSign n)
    (by rw [← pow_two, divisorOrientationSign_sq])

/-- Rescale the actual integral basis by the arithmetic sign units. -/
def divisorUnsignedBasis (N : ℕ) (hN : 1 ≤ N) :
    Module.Basis (NonPoleVertex N hN) ℤ (divisorRelationLattice N hN) :=
  (divisorRelationBasis N hN).unitsSMul (fun j => divisorOrientationUnit j.val.val)

theorem divisorUnsignedBasis_coe (N : ℕ) (hN : 1 ≤ N) (j : NonPoleVertex N hN) :
    (divisorUnsignedBasis N hN j : Vertex N → ℤ) =
      divisorOrientationSign j.val.val • (divisorRelationBasis N hN j : Vertex N → ℤ) := by
  simp only [divisorUnsignedBasis, Module.Basis.unitsSMul_apply, Units.smul_def,
    Submodule.coe_smul, divisorOrientationUnit, Units.val_mkOfMulEqOne]

/-- Unit changes of the actual integral basis leave a squarefree root block and free directions. -/
theorem divisorUnsignedBasis_gram (N : ℕ) (hN : 1 ≤ N) (j k : NonPoleVertex N hN) :
    (divisorUnsignedBasis N hN j : Vertex N → ℤ) ⬝ᵥ
      (divisorUnsignedBasis N hN k : Vertex N → ℤ) =
        (if j = k then 1 else 0) +
          (if Squarefree j.val.val then 1 else 0) * (if Squarefree k.val.val then 1 else 0) := by
  rw [divisorUnsignedBasis_coe, divisorUnsignedBasis_coe]
  have he : (divisorOrientationSign j.val.val • (divisorRelationBasis N hN j : Vertex N → ℤ)) ⬝ᵥ
      (divisorOrientationSign k.val.val • (divisorRelationBasis N hN k : Vertex N → ℤ)) =
        divisorOrientationSign j.val.val * divisorOrientationSign k.val.val *
          divisorRelationGram N hN j k := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, divisorRelationGram, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [he, divisorRelationGram_apply]
  have hd : divisorOrientationSign j.val.val * divisorOrientationSign k.val.val *
      (if j = k then 1 else 0) = (if j = k then 1 else 0) := by
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl, mul_one, ← pow_two, divisorOrientationSign_sq]
    · rw [if_neg hjk, mul_zero]
  calc
    _ = divisorOrientationSign j.val.val * divisorOrientationSign k.val.val *
          (if j = k then 1 else 0) +
        (divisorOrientationSign j.val.val * moebius j.val.val) *
          (divisorOrientationSign k.val.val * moebius k.val.val) := by ring
    _ = _ := by rw [hd, divisorOrientationSign_mul, divisorOrientationSign_mul,
      ArithmeticFunction.moebius_sq, ArithmeticFunction.moebius_sq]

#print axioms divisorUnsignedBasis
#print axioms divisorUnsignedBasis_gram


/-- Actual local indices factor into arithmetic Gram volume and Euclidean displacement. -/
theorem localIndices_volume_distance (N : ℕ) (hN : 1 ≤ N) :
    |((∑ p, primeVertexRelativeIndex N N p : ℤ) : ℝ)| =
      divisorRelationVolume N hN * divisorTransverseDistance N (integerGluingRealColumn N) := by
  have h := integerGluingCount_volume_distance N hN
  rw [integerGluingCount_eq_localIndices N hN, Nat.cast_natAbs, Int.cast_abs] at h
  exact h

/-- The height splits into half the squarefree logarithm and transverse displacement;
the infinite cyclic case retains the cardinality convention `Nat.card = 0`. -/
theorem integerGluingHeight_volume_distance (N : ℕ) (hN : 1 ≤ N) :
    integerGluingHeight N = if integerGluingCharge N = 0 then 0 else
      Real.log (divisorSquarefreeCount N) / 2 +
        Real.log (divisorTransverseDistance N (integerGluingRealColumn N)) := by
  by_cases hz : integerGluingCharge N = 0
  · simp [integerGluingHeight, integerGluingCount_eq N hN, hz]
  · have hc : (integerGluingCount N : ℝ) ≠ 0 := by
      have hc : integerGluingCount N ≠ 0 := by
        rw [integerGluingCount_eq N hN]
        exact Int.natAbs_ne_zero.mpr hz
      exact_mod_cast hc
    have hd : divisorTransverseDistance N (integerGluingRealColumn N) ≠ 0 := by
      intro hd
      have he := integerGluingCount_volume_distance N hN
      rw [hd, mul_zero] at he
      exact hc he
    rw [if_neg hz, integerGluingHeight, integerGluingCount_volume_distance N hN,
      Real.log_mul (divisorRelationVolume_pos N hN).ne' hd, divisorRelationVolume_eq,
      Real.log_sqrt (Nat.cast_nonneg _)]

#print axioms localIndices_volume_distance
#print axioms integerGluingHeight_volume_distance

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
