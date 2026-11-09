import GaloisForLFunctions.ArithmeticDegenerationTheory.TheMertensFunctionIsAGluingDeterminant
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeVertexSignedLocalization
import Mathlib.Data.ZMod.QuotientRing

/-!
# Integral residue counts for signed prime-vertex localization

The relation lattice is defined by divisor-sum columns and the negative sum
of all non-pole basis vectors. Neither its quotient nor its count uses a
Möbius sum. Integral Möbius inversion reduces the actual presentation to
identity with one replaced column. An explicit residue map and kernel
calculation identify the quotient as cyclic, including its infinite case.
The oriented determinant is the sum of the actual local singular indices;
cardinality and the prime-primary decomposition give its arithmetic height.
-/

noncomputable section
open Finset Matrix ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory

/-- Integral incidence of divisibility on the labels `1,…,N`. -/
def integerDivisibilityMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℤ :=
  fun i j => if i.val ∣ j.val then 1 else 0

/-- Integral inverse coordinates, used in the proof of the arithmetic presentation. -/
def integerMoebiusMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℤ :=
  fun i j => if i.val ∣ j.val then moebius (j.val / i.val) else 0

/-- The oriented relation is the negative sum of the non-pole generators. -/
def integerGluingColumn (N : ℕ) : Vertex N → ℤ :=
  fun i => if i.val = 1 then 0 else -1

/-- Divisor-sum relations for non-pole labels, and the reduced gluing relation at one. -/
def integerGluingMatrix (N : ℕ) : Matrix (Vertex N) (Vertex N) ℤ :=
  fun i j => if j.val = 1 then integerGluingColumn N i else
    if i.val ∣ j.val then 1 else 0

/-- The actual integral relation map. -/
def integerGluingMap (N : ℕ) : (Vertex N → ℤ) →ₗ[ℤ] (Vertex N → ℤ) :=
  (integerGluingMatrix N).mulVecLin

/-- Integral residue classes defined solely by arithmetic divisibility and gluing. -/
abbrev IntegerGluingQuotient (N : ℕ) :=
  (Vertex N → ℤ) ⧸ LinearMap.range (integerGluingMap N)

/-- The real inversion identity descends through the injective integer embedding. -/
theorem integerDivisibility_mul_moebius (N : ℕ) :
    integerDivisibilityMatrix N * integerMoebiusMatrix N = 1 := by
  ext i j
  have h := congrArg (fun A : Matrix (Vertex N) (Vertex N) ℝ => A i j)
    (divisibilityMatrix_mul_moebiusMatrix N)
  simp only [Matrix.mul_apply, divisibilityMatrix, moebiusMatrix, Matrix.one_apply] at h
  simp only [Matrix.mul_apply, integerDivisibilityMatrix, integerMoebiusMatrix, Matrix.one_apply]
  exact_mod_cast h

theorem integerMoebius_mul_divisibility (N : ℕ) :
    integerMoebiusMatrix N * integerDivisibilityMatrix N = 1 :=
  mul_eq_one_comm.mp (integerDivisibility_mul_moebius N)

theorem integerGluing_eq_updateCol (N : ℕ) (hN : 1 ≤ N) :
    integerGluingMatrix N =
      (integerDivisibilityMatrix N).updateCol (poleVertex N hN) (integerGluingColumn N) := by
  ext i j
  simp only [integerGluingMatrix, integerDivisibilityMatrix, Matrix.updateCol_apply]
  by_cases hj : j = poleVertex N hN
  · subst j
    simp [poleVertex]
  · rw [if_neg hj]
    have hj1 : j.val ≠ 1 := fun h => hj (Subtype.ext h)
    simp [hj1]

/-- The arithmetic charge to which the independent quotient is compared. -/
def integerGluingCharge (N : ℕ) : ℤ := 1 - ∑ n ∈ Icc 1 N, moebius n

theorem integerMoebius_ones_pole (N : ℕ) (hN : 1 ≤ N) :
    (integerMoebiusMatrix N *ᵥ (fun _ => 1)) (poleVertex N hN) =
      ∑ n ∈ Icc 1 N, moebius n := by
  simp only [Matrix.mulVec, dotProduct, integerMoebiusMatrix, poleVertex,
    one_dvd, if_true, Nat.div_one, mul_one]
  exact (Finset.sum_subtype (Icc 1 N) (fun _ => Iff.rfl) (fun n => moebius n)).symm

theorem integerMoebius_pole_row (N : ℕ) (hN : 1 ≤ N) :
    (integerMoebiusMatrix N *ᵥ integerGluingColumn N) (poleVertex N hN) =
      integerGluingCharge N := by
  have hc : integerGluingColumn N = Pi.single (poleVertex N hN) 1 - (fun _ => 1) := by
    funext i
    by_cases hi : i = poleVertex N hN
    · subst i
      simp [integerGluingColumn, poleVertex]
    · have hi1 : i.val ≠ 1 := fun h => hi (Subtype.ext h)
      simp [integerGluingColumn, hi1, Pi.single_eq_of_ne hi]
  rw [hc, Matrix.mulVec_sub, Pi.sub_apply]
  have hs : (integerMoebiusMatrix N *ᵥ Pi.single (poleVertex N hN) 1)
      (poleVertex N hN) = 1 := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
      integerMoebiusMatrix, poleVertex]
  rw [hs, integerMoebius_ones_pole]
  rfl

#print axioms integerDivisibility_mul_moebius
#print axioms integerGluing_eq_updateCol

private theorem one_updateCol_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι) (w x : ι → ℤ) (i : ι) :
    ((1 : Matrix ι ι ℤ).updateCol p w *ᵥ x) i =
      if i = p then w i * x p else x i + w i * x p := by
  change (∑ j, (1 : Matrix ι ι ℤ).updateCol p w i j * x j) = _
  rw [← sum_erase_add univ (f := fun j => (1 : Matrix ι ι ℤ).updateCol p w i j * x j)
    (mem_univ p)]
  simp only [Matrix.updateCol_self]
  by_cases hi : i = p
  · subst i
    rw [if_pos rfl]
    have hz : ∑ j ∈ univ.erase p, (1 : Matrix ι ι ℤ).updateCol p w p j * x j = 0 := by
      apply sum_eq_zero
      intro j hj
      have h := (mem_erase.mp hj).1
      simp only [Matrix.updateCol_ne h, Matrix.one_apply, if_neg h.symm, zero_mul]
    rw [hz, zero_add]
  · rw [if_neg hi]
    congr 1
    rw [sum_eq_single i]
    · simp [Matrix.updateCol_ne hi]
    · intro j hj hji
      simp only [Matrix.updateCol_ne (mem_erase.mp hj).1, Matrix.one_apply,
        if_neg hji.symm, zero_mul]
    · intro h
      exact (h (mem_erase.mpr ⟨hi, mem_univ i⟩)).elim

/-- Integral inversion leaves exactly one nontrivial relation column. -/
theorem integerMoebius_mul_gluing (N : ℕ) (hN : 1 ≤ N) :
    integerMoebiusMatrix N * integerGluingMatrix N =
      (1 : Matrix (Vertex N) (Vertex N) ℤ).updateCol (poleVertex N hN)
        (integerMoebiusMatrix N *ᵥ integerGluingColumn N) := by
  rw [integerGluing_eq_updateCol N hN, Matrix.mul_updateCol,
    integerMoebius_mul_divisibility]

/-- Residue of the pole coordinate after integral inversion. -/
def integerGluingResidue (N : ℕ) (hN : 1 ≤ N) :
    (Vertex N → ℤ) →ₗ[ℤ] ZMod (integerGluingCharge N).natAbs :=
  (Int.castAddHom (ZMod (integerGluingCharge N).natAbs)).toIntLinearMap.comp
    ((LinearMap.proj (poleVertex N hN)).comp (integerMoebiusMatrix N).mulVecLin)

theorem integerGluingResidue_surjective (N : ℕ) (hN : 1 ≤ N) :
    Function.Surjective (integerGluingResidue N hN) := by
  intro y
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective y
  refine ⟨integerDivisibilityMatrix N *ᵥ Pi.single (poleVertex N hN) a, ?_⟩
  change (((integerMoebiusMatrix N *ᵥ
    (integerDivisibilityMatrix N *ᵥ Pi.single (poleVertex N hN) a)) (poleVertex N hN) : ℤ) :
      ZMod (integerGluingCharge N).natAbs) = _
  rw [mulVec_mulVec, integerMoebius_mul_divisibility, one_mulVec, Pi.single_eq_same]

/-- Divisibility of the pole coordinate explicitly reconstructs an integral relation preimage. -/
theorem integerGluingResidue_kernel (N : ℕ) (hN : 1 ≤ N) :
    LinearMap.ker (integerGluingResidue N hN) = LinearMap.range (integerGluingMap N) := by
  ext v
  rw [LinearMap.mem_ker]
  change (((integerMoebiusMatrix N *ᵥ v) (poleVertex N hN) : ℤ) :
      ZMod (integerGluingCharge N).natAbs) = 0 ↔ _
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd]
  constructor
  · rintro ⟨k, hk⟩
    let p := poleVertex N hN
    let z := integerMoebiusMatrix N *ᵥ v
    let w := integerMoebiusMatrix N *ᵥ integerGluingColumn N
    let x := Function.update (fun i => z i - w i * k) p k
    refine ⟨x, ?_⟩
    have hT : (1 : Matrix (Vertex N) (Vertex N) ℤ).updateCol p w *ᵥ x = z := by
      funext i
      rw [one_updateCol_mulVec_apply]
      by_cases hi : i = p
      · subst i
        rw [if_pos rfl]
        change w p * k = z p
        exact (integerMoebius_pole_row N hN ▸ hk).symm
      · rw [if_neg hi]
        dsimp only [x]
        rw [Function.update_of_ne hi, Function.update_self]
        ring
    have hU : integerMoebiusMatrix N *ᵥ (integerGluingMatrix N *ᵥ x) =
        integerMoebiusMatrix N *ᵥ v := by
      rw [mulVec_mulVec, integerMoebius_mul_gluing N hN]
      exact hT
    have hZ := congrArg (fun u => integerDivisibilityMatrix N *ᵥ u) hU
    simpa only [mulVec_mulVec, ← mul_assoc, integerDivisibility_mul_moebius, one_mul, one_mulVec,
      integerGluingMap, Matrix.mulVecLin_apply] using hZ
  · rintro ⟨x, rfl⟩
    change integerGluingCharge N ∣
      (integerMoebiusMatrix N *ᵥ (integerGluingMatrix N *ᵥ x)) (poleVertex N hN)
    rw [mulVec_mulVec, integerMoebius_mul_gluing N hN, one_updateCol_mulVec_apply,
      if_pos rfl, integerMoebius_pole_row]
    exact dvd_mul_right _ _

/-- The actual relation quotient is cyclic, even when its modulus is zero. -/
def integerGluingQuotientEquiv (N : ℕ) (hN : 1 ≤ N) :
    IntegerGluingQuotient N ≃ₗ[ℤ] ZMod (integerGluingCharge N).natAbs := by
  change ((Vertex N → ℤ) ⧸ LinearMap.range (integerGluingMap N)) ≃ₗ[ℤ] _
  rw [← integerGluingResidue_kernel N hN]
  exact (integerGluingResidue N hN).quotKerEquivOfSurjective
    (integerGluingResidue_surjective N hN)

#print axioms integerGluingQuotientEquiv


/-- The integral divisibility presentation is unimodular. -/
theorem integerDivisibilityMatrix_det (N : ℕ) : (integerDivisibilityMatrix N).det = 1 := by
  have htri : (integerDivisibilityMatrix N).BlockTriangular id := by
    intro i j hji
    apply if_neg
    intro hd
    exact (Nat.not_le_of_gt hji)
      (Nat.le_of_dvd (mem_Icc.mp j.property).1 hd)
  rw [Matrix.det_of_upperTriangular htri]
  simp [integerDivisibilityMatrix]

/-- The oriented integral gluing determinant equals the arithmetic signed charge. -/
theorem integerGluingMatrix_det (N : ℕ) (hN : 1 ≤ N) :
    (integerGluingMatrix N).det = integerGluingCharge N := by
  rw [integerGluing_eq_updateCol N hN, ← Matrix.cramer_apply]
  have hc : Matrix.cramer (integerDivisibilityMatrix N) (integerGluingColumn N) =
      integerMoebiusMatrix N *ᵥ integerGluingColumn N := by
    have h1 : integerDivisibilityMatrix N *ᵥ
        Matrix.cramer (integerDivisibilityMatrix N) (integerGluingColumn N) =
        integerGluingColumn N := by
      rw [Matrix.mulVec_cramer, integerDivisibilityMatrix_det, one_smul]
    calc
      _ = (integerMoebiusMatrix N * integerDivisibilityMatrix N) *ᵥ
          Matrix.cramer (integerDivisibilityMatrix N) (integerGluingColumn N) := by
        rw [integerMoebius_mul_divisibility, Matrix.one_mulVec]
      _ = _ := by rw [← Matrix.mulVec_mulVec, h1]
  rw [hc, integerMoebius_pole_row]

/-- The determinant retains the orientation of the actual local indices. -/
theorem integerGluingMatrix_det_localIndices (N : ℕ) (hN : 1 ≤ N) :
    (integerGluingMatrix N).det = ∑ p, primeVertexRelativeIndex N N p := by
  rw [integerGluingMatrix_det N hN, primeVertexRelativeIndex_sum_mertens N N le_rfl hN]
  rfl

/-- Number of actual integral relation classes; zero denotes an infinite quotient. -/
def integerGluingCount (N : ℕ) : ℕ := Nat.card (IntegerGluingQuotient N)

/-- The independently defined integral quotient counts the absolute arithmetic charge. -/
theorem integerGluingCount_eq (N : ℕ) (hN : 1 ≤ N) :
    integerGluingCount N = (integerGluingCharge N).natAbs := by
  rw [integerGluingCount, Nat.card_congr (integerGluingQuotientEquiv N hN).toEquiv,
    Nat.card_zmod]

/-- Finiteness is proved exactly; vanishing charge is not treated as an empty finite set. -/
theorem integerGluingQuotient_finite_iff (N : ℕ) (hN : 1 ≤ N) :
    Finite (IntegerGluingQuotient N) ↔ integerGluingCharge N ≠ 0 := by
  constructor
  · intro h
    letI := h
    have hc : 0 < integerGluingCount N := Nat.card_pos
    rw [integerGluingCount_eq N hN] at hc
    exact Int.natAbs_ne_zero.mp hc.ne'
  · intro h
    apply Nat.finite_of_card_ne_zero
    change integerGluingCount N ≠ 0
    rw [integerGluingCount_eq N hN]
    exact Int.natAbs_ne_zero.mpr h

/-- Zero arithmetic charge leaves an infinite cyclic relation quotient. -/
def integerGluingQuotient_zeroEquiv (N : ℕ) (hN : 1 ≤ N)
    (h : integerGluingCharge N = 0) : IntegerGluingQuotient N ≃ₗ[ℤ] ℤ := by
  have e := integerGluingQuotientEquiv N hN
  rw [h, Int.natAbs_zero] at e
  exact e

/-- The independent integral count is exactly the absolute sum of actual local indices. -/
theorem integerGluingCount_eq_localIndices (N : ℕ) (hN : 1 ≤ N) :
    integerGluingCount N = (∑ p, primeVertexRelativeIndex N N p).natAbs := by
  rw [integerGluingCount_eq N hN, primeVertexRelativeIndex_sum_mertens N N le_rfl hN]
  rfl

/-- The canonical cyclic presentation can be indexed by the count itself. -/
def integerGluingCyclicEquiv (N : ℕ) (hN : 1 ≤ N) :
    IntegerGluingQuotient N ≃ₗ[ℤ] ZMod (integerGluingCount N) := by
  rw [integerGluingCount_eq N hN]
  exact integerGluingQuotientEquiv N hN

/-- Actual prime-primary decomposition of every finite integral gluing quotient. -/
def integerGluingPrimaryEquiv (N : ℕ) (hN : 1 ≤ N) (h : integerGluingCount N ≠ 0) :
    IntegerGluingQuotient N ≃+
      Π p : (integerGluingCount N).primeFactors,
        ZMod ((p : ℕ) ^ (integerGluingCount N).factorization p) :=
  (integerGluingCyclicEquiv N hN).toAddEquiv.trans
    (ZMod.equivPi (integerGluingCount N) h).toAddEquiv

/-- Prime-local order multiplicity of the independently presented integral group. -/
def integerGluingOrder (N p : ℕ) : ℕ := (integerGluingCount N).factorization p

/-- Each actual primary factor has exactly the cardinality prescribed by its local multiplicity. -/
theorem integerGluingPrimary_card (N p : ℕ) :
    Nat.card (ZMod (p ^ integerGluingOrder N p)) = p ^ integerGluingOrder N p :=
  Nat.card_zmod _

/-- Logarithmic height of the actual residue-class count. -/
def integerGluingHeight (N : ℕ) : ℝ := Real.log (integerGluingCount N)

/-- The product formula for the independently constructed finite arithmetic count. -/
theorem integerGluingHeight_prime_sum (N : ℕ) (hN : 1 ≤ N)
    (h : integerGluingCharge N ≠ 0) :
    0 < integerGluingCount N ∧
      integerGluingHeight N = (integerGluingCount N).factorization.sum
        (fun p k => (k : ℝ) * Real.log p) := by
  refine ⟨?_, Real.log_nat_eq_sum_factorization _⟩
  rw [integerGluingCount_eq N hN]
  exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr h)

/-- Its archimedean value is the logarithm of the absolute actual local-index sum. -/
theorem integerGluingHeight_localIndices (N : ℕ) (hN : 1 ≤ N) :
    integerGluingHeight N =
      Real.log |((∑ p, primeVertexRelativeIndex N N p : ℤ) : ℝ)| := by
  rw [integerGluingHeight, integerGluingCount_eq_localIndices N hN,
    Nat.cast_natAbs, Int.cast_abs]

#print axioms integerGluingCount_eq
#print axioms integerGluingMatrix_det_localIndices
#print axioms integerGluingQuotient_finite_iff
#print axioms integerGluingQuotient_zeroEquiv
#print axioms integerGluingCount_eq_localIndices
#print axioms integerGluingPrimaryEquiv
#print axioms integerGluingHeight_prime_sum
#print axioms integerGluingHeight_localIndices

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
