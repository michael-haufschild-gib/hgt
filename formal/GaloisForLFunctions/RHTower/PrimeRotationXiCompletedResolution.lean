import GaloisForLFunctions.RHTower.PrimeRotationXiRationalTraceDefect
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Ring.GeomSum

/-!
# Completion of the literal prime-rotation Xi relation

The full arithmetic jet relation has an explicit inverse in the closed rotation algebra away
from the critical line. A finite strictly triangular series retains every nilpotent jet; no
small-norm hypothesis on the flow matrix is needed. On the line, density of the native phases
precludes even a left inverse. The actual inverse has the previously observed boundary trace.

Completion therefore contracts off-line packet resolutions. This is not a charged projective
realization of the original Poisson source: that source cannot be identified with this cokernel.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

private theorem strictUpper_power {R : Type*} [Ring R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (hN : ∀ i j, j ≤ i → N i j = 0)
    (k : ℕ) (i j : Fin n) (hij : j.val < i.val + k) : (N ^ k) i j = 0 := by
  induction k generalizing i j with
  | zero =>
    have hne : i ≠ j := by intro h; subst j; omega
    simp [hne]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases h : l.val < i.val + k
    · rw [ih i l h, zero_mul]
    · rw [hN l j (by change j.val ≤ l.val; omega), mul_zero]

private theorem strictUpper_nilpotent {R : Type*} [Ring R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (hN : ∀ i j, j ≤ i → N i j = 0) : N ^ n = 0 := by
  ext i j
  exact strictUpper_power N hN n i j (by have := j.isLt; omega)

private theorem strictUpper_series_diag {R : Type*} [Ring R] {n : ℕ}
    (hn : 0 < n) (N : Matrix (Fin n) (Fin n) R)
    (hN : ∀ i j, j ≤ i → N i j = 0) (i : Fin n) :
    (∑ k ∈ Finset.range n, N ^ k) i i = 1 := by
  simp only [Matrix.sum_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    exact strictUpper_power N hN k i i (by omega)
  · simp [hn]

private def nativeCompletedModulation (p : Nat.Primes) (q : ℕ) :
    paperRotationAlgebra (paperPrimeRotationFrequency p (q + 1)) :=
  ⟨paperRotationModulation (paperPrimeRotationFrequency p (q + 1)), by
    simpa using paperRotationModulation_mem_algebra (paperPrimeRotationFrequency p (q + 1)) 1⟩

/-- The literal right relation matrix on row coefficients, with the entire source flow block. -/
def deningerMeyerXiCompletedRelationMatrix (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) :
    Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho))
      (paperRotationAlgebra (paperPrimeRotationFrequency p (q + 1))) :=
  Matrix.scalar (Fin (xiSupportMultiplicity rho)) (nativeCompletedModulation p q) -
    Matrix.of (fun i j => deningerMeyerSingleXiFlowMatrix rho (-Real.log p) j i •
      (1 : paperRotationAlgebra (paperPrimeRotationFrequency p (q + 1))))

private theorem completedRelation_below (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport)
    (i j : Fin (xiSupportMultiplicity rho)) (hij : j < i) :
    deningerMeyerXiCompletedRelationMatrix p q rho i j = 0 := by
  simp only [deningerMeyerXiCompletedRelationMatrix, Matrix.sub_apply, Matrix.of_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij.ne',
    deningerMeyerSingleXiFlowMatrix_lower rho (-Real.log p) j i hij, zero_smul, sub_zero]

private theorem completedRelation_diag (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport)
    (i : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerXiCompletedRelationMatrix p q rho i i =
      nativeCompletedModulation p q - deningerMeyerPrimeMellinCoordinate p rho • 1 := by
  simp only [deningerMeyerXiCompletedRelationMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq, deningerMeyerSingleXiFlowMatrix_diag,
    deningerMeyerPrimeMellinCoordinate, Complex.ofReal_neg]

private def xiCompletedScalarInverse (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) :
    paperRotationAlgebra (paperPrimeRotationFrequency p (q + 1)) :=
  if 1 / 2 < (rho : ℂ).re then
    ⟨paperRotationInsideResolvent (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho), paperRotationInsideResolvent_mem_algebra _ _⟩
  else
    ⟨paperRotationOutsideResolvent (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho), paperRotationOutsideResolvent_mem_algebra _ _⟩

private theorem xiCompletedScalarInverse_left (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    xiCompletedScalarInverse p q rho *
      (nativeCompletedModulation p q - deningerMeyerPrimeMellinCoordinate p rho • 1) = 1 := by
  unfold xiCompletedScalarInverse
  split_ifs with h
  · apply Subtype.ext
    exact paperRotationInsideResolvent_mul_reverse (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho)
      (deningerMeyerPrimeMellinCoordinate_norm_lt_one p rho h)
  · apply Subtype.ext
    exact paperRotationOutsideResolvent_mul_reverse (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho)
      (deningerMeyerPrimeMellinCoordinate_one_lt_norm p rho
        ((lt_or_gt_of_ne hrho).resolve_right h))

private theorem xiCompletedScalarInverse_right (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    (nativeCompletedModulation p q - deningerMeyerPrimeMellinCoordinate p rho • 1) *
      xiCompletedScalarInverse p q rho = 1 := by
  unfold xiCompletedScalarInverse
  split_ifs with h
  · apply Subtype.ext
    exact paperRotationInsideResolvent_mul (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho)
      (deningerMeyerPrimeMellinCoordinate_norm_lt_one p rho h)
  · apply Subtype.ext
    exact paperRotationOutsideResolvent_mul (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerPrimeMellinCoordinate p rho)
      (deningerMeyerPrimeMellinCoordinate_one_lt_norm p rho
        ((lt_or_gt_of_ne hrho).resolve_right h))

private def xiCompletedNilpotent (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) :=
  1 - Matrix.scalar _ (xiCompletedScalarInverse p q rho) *
    deningerMeyerXiCompletedRelationMatrix p q rho

private theorem xiCompletedNilpotent_strictUpper (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2)
    (i j : Fin (xiSupportMultiplicity rho)) (hij : j ≤ i) :
    xiCompletedNilpotent p q rho i j = 0 := by
  rcases hij.eq_or_lt with h | h
  · subst j
    simp only [xiCompletedNilpotent, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_mul, Matrix.one_apply, ite_true, completedRelation_diag,
      xiCompletedScalarInverse_left p q rho hrho, sub_self]
  · simp only [xiCompletedNilpotent, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_mul, Matrix.one_apply, if_neg h.ne',
      completedRelation_below p q rho i j h, mul_zero, sub_zero]

/-- A finite triangular inverse built from actual analytic scalar resolvents. -/
def deningerMeyerXiCompletedRelationInverse (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) :=
  (∑ k ∈ Finset.range (xiSupportMultiplicity rho), xiCompletedNilpotent p q rho ^ k) *
    Matrix.scalar _ (xiCompletedScalarInverse p q rho)

/-- The full source relation contracts in the closed algebra off the critical line. -/
theorem deningerMeyerXiCompletedRelationInverse_mul (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerXiCompletedRelationInverse p q rho *
      deningerMeyerXiCompletedRelationMatrix p q rho = 1 := by
  have hn := strictUpper_nilpotent (xiCompletedNilpotent p q rho)
    (xiCompletedNilpotent_strictUpper p q rho hrho)
  have he : Matrix.scalar _ (xiCompletedScalarInverse p q rho) *
      deningerMeyerXiCompletedRelationMatrix p q rho = 1 - xiCompletedNilpotent p q rho := by
    simp only [xiCompletedNilpotent, sub_sub_cancel]
  rw [deningerMeyerXiCompletedRelationInverse, mul_assoc, he, geom_sum_mul_neg, hn, sub_zero]

/-- Both inverse identities hold inside the actual closed rotation algebra. -/
theorem deningerMeyerXiCompletedRelationMatrix_mul_inverse (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerXiCompletedRelationMatrix p q rho *
      deningerMeyerXiCompletedRelationInverse p q rho = 1 := by
  let D := Matrix.scalar (Fin (xiSupportMultiplicity rho))
    (nativeCompletedModulation p q - deningerMeyerPrimeMellinCoordinate p rho • 1)
  have hDR : D * Matrix.scalar _ (xiCompletedScalarInverse p q rho) = 1 := by
    dsimp only [D]
    rw [← map_mul, xiCompletedScalarInverse_right p q rho hrho, map_one]
  have hn := strictUpper_nilpotent (xiCompletedNilpotent p q rho)
    (xiCompletedNilpotent_strictUpper p q rho hrho)
  have hB : deningerMeyerXiCompletedRelationMatrix p q rho =
      D * (1 - xiCompletedNilpotent p q rho) := by
    simp only [xiCompletedNilpotent, sub_sub_cancel, ← mul_assoc, hDR, one_mul]
  rw [deningerMeyerXiCompletedRelationInverse, hB, mul_assoc, ← mul_assoc (1 - _),
    mul_neg_geom_sum, hn, sub_zero, one_mul, hDR]

/-- Every inverse diagonal is the actual scalar resolvent, despite arbitrary multiplicity. -/
theorem deningerMeyerXiCompletedRelationInverse_diag (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2)
    (i : Fin (xiSupportMultiplicity rho)) :
    (deningerMeyerXiCompletedRelationInverse p q rho i i).val =
      if 1 / 2 < (rho : ℂ).re then
        paperRotationInsideResolvent (paperPrimeRotationFrequency p (q + 1))
          (deningerMeyerPrimeMellinCoordinate p rho)
      else paperRotationOutsideResolvent (paperPrimeRotationFrequency p (q + 1))
          (deningerMeyerPrimeMellinCoordinate p rho) := by
  simp only [deningerMeyerXiCompletedRelationInverse, Matrix.scalar_apply, Matrix.mul_diagonal,
    strictUpper_series_diag (xiSupportMultiplicity_pos rho) _
      (xiCompletedNilpotent_strictUpper p q rho hrho), one_mul]
  unfold xiCompletedScalarInverse
  split_ifs <;> rfl

/-- Completion uses exactly the coefficients of the previously constructed arithmetic resolution. -/
theorem deningerMeyerXiCompletedRelationMatrix_source (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport)
    (C : DeningerMeyerFiniteXiJetSlot {rho} →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (i : Fin (xiSupportMultiplicity rho)) :
    (∑ j : Fin (xiSupportMultiplicity rho),
      (C (deningerMeyerSingleXiSlot rho j)).val *
        (deningerMeyerXiCompletedRelationMatrix p q rho j i).val) =
      (deningerMeyerXiClockRelation p q {rho} C (deningerMeyerSingleXiSlot rho i)).val := by
  rw [deningerMeyerXiClockRelation_singleton]
  simp only [deningerMeyerXiCompletedRelationMatrix, Matrix.sub_apply, Matrix.of_apply, Matrix.scalar_apply]
  push_cast
  simp only [mul_sub, mul_smul_comm, mul_one, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [Matrix.diagonal_apply_eq, nativeCompletedModulation, paperRotationPolynomialWord,
      paperRotationWord]
  · intro j _ hj
    simp [Matrix.diagonal_apply_ne _ hj]
  · simp

/-- Before completion the actual arithmetic relation has a nonzero cokernel at every Xi zero. -/
theorem deningerMeyerXiClockRelation_not_surjective (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) :
    ¬ Function.Surjective (deningerMeyerXiClockRelation p q {rho}) := by
  intro hs
  let i : DeningerMeyerFiniteXiJetSlot {rho} :=
    deningerMeyerSingleXiSlot rho ⟨0, xiSupportMultiplicity_pos rho⟩
  let e : DeningerMeyerXiClockPacket {rho} := Finsupp.single 0 (Pi.single i 1)
  obtain ⟨C, hC⟩ := deningerMeyerXiClockFreeCover_surjective p q {rho} e
  obtain ⟨D, rfl⟩ := hs C
  have hk : deningerMeyerXiClockRelation p q {rho} D ∈
      LinearMap.ker (deningerMeyerXiClockFreeCover p q {rho}) := by
    rw [← (deningerMeyerXiClockResolution_exact p q {rho}).2.1]
    exact ⟨D, rfl⟩
  change deningerMeyerXiClockFreeCover p q {rho}
    (deningerMeyerXiClockRelation p q {rho} D) = 0 at hk
  have hz : e = 0 := hC.symm.trans hk
  have hv := congrArg (fun x : DeningerMeyerXiClockPacket {rho} => x 0 i) hz
  simp [e] at hv

/-- The completed finite free relation is an actual automorphism off the line. -/
theorem deningerMeyerXiCompletedRelation_bijective (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    Function.Bijective (fun C => Matrix.vecMul C (deningerMeyerXiCompletedRelationMatrix p q rho)) := by
  constructor
  · intro C D h
    have he := congrArg (fun X => Matrix.vecMul X (deningerMeyerXiCompletedRelationInverse p q rho)) h
    simpa only [Matrix.vecMul_vecMul,
      deningerMeyerXiCompletedRelationMatrix_mul_inverse p q rho hrho,
      Matrix.vecMul_one] using he
  · intro C
    refine ⟨Matrix.vecMul C (deningerMeyerXiCompletedRelationInverse p q rho), ?_⟩
    change Matrix.vecMul (Matrix.vecMul C (deningerMeyerXiCompletedRelationInverse p q rho))
      (deningerMeyerXiCompletedRelationMatrix p q rho) = C
    rw [Matrix.vecMul_vecMul, deningerMeyerXiCompletedRelationInverse_mul p q rho hrho,
      Matrix.vecMul_one]

private theorem nativePrimePhase_dense (p : Nat.Primes) (q : ℕ) :
    DenseRange (fun n : ℤ => Circle.exp (paperPrimeRotationFrequency p (q + 1) * n)) := by
  have hi : Irrational (paperPrimeRotationFrequency p (q + 1) / (2 * Real.pi)) := by
    have he : paperPrimeRotationFrequency p (q + 1) / (2 * Real.pi) =
        -primeRotationParameter p (q + 1) := by
      unfold paperPrimeRotationFrequency
      field_simp
    rw [he]
    exact (primeRotationParameter_irrational p (Nat.succ_ne_zero q)).neg
  have hd := AddCircle.denseRange_zsmul_coe_iff.mpr hi
  have he := AddCircle.homeomorphCircle'.surjective.denseRange.comp hd
    AddCircle.homeomorphCircle'.continuous
  have hphase (n : ℤ) : AddCircle.homeomorphCircle'
      (n • (paperPrimeRotationFrequency p (q + 1) : AddCircle (2 * Real.pi))) =
      Circle.exp (paperPrimeRotationFrequency p (q + 1) * n) := by
    rw [← AddCircle.coe_zsmul, AddCircle.homeomorphCircle'_apply_mk]
    simp only [zsmul_eq_mul, mul_comm]
  simpa only [Function.comp_def, hphase] using he

private theorem modulation_sub_single (t : ℝ) (z : ℂ) (n : ℤ) :
    (paperRotationModulation t - z • (1 : PaperRotationHilbert →L[ℂ] PaperRotationHilbert))
      (lp.single (E := fun _ : ℤ => ℂ) 2 n 1) =
        (paperRotationPhase (t * n) - z) • lp.single (E := fun _ : ℤ => ℂ) 2 n 1 := by
  apply lp.ext
  funext k
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
    paperRotationModulation_apply, smul_eq_mul, lp.single_apply]
  by_cases hk : k = n
  · subst k; simp
  · simp [hk]

private theorem nativeModulation_no_left_inverse (p : Nat.Primes) (q : ℕ) (z : ℂ)
    (hz : ‖z‖ = 1) (C : PaperRotationHilbert →L[ℂ] PaperRotationHilbert) :
    C * (paperRotationModulation (paperPrimeRotationFrequency p (q + 1)) - z • 1) ≠ 1 := by
  intro hC
  let zc : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨n, hn⟩ := (nativePrimePhase_dense p q).exists_dist_lt zc
    (show 0 < 1 / (‖C‖ + 1) by positivity)
  have hd : ‖paperRotationPhase (paperPrimeRotationFrequency p (q + 1) * n) - z‖ <
      1 / (‖C‖ + 1) := by
    change dist z (paperRotationPhase (paperPrimeRotationFrequency p (q + 1) * n)) < _ at hn
    rw [dist_comm, dist_eq_norm] at hn
    exact hn
  let e := lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ)
  have he : C ((paperRotationModulation (paperPrimeRotationFrequency p (q + 1)) - z • 1) e) = e := by
    change (C * (paperRotationModulation (paperPrimeRotationFrequency p (q + 1)) - z • 1)) e = e
    rw [hC]; rfl
  have hb := C.le_opNorm ((paperRotationModulation (paperPrimeRotationFrequency p (q + 1)) - z • 1) e)
  rw [he] at hb
  simp only [e, modulation_sub_single, norm_smul,
    lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] at hb
  have hlt := (lt_div_iff₀ (show 0 < ‖C‖ + 1 by positivity)).mp hd
  nlinarith [norm_nonneg (paperRotationPhase (paperPrimeRotationFrequency p (q + 1) * n) - z)]

/-- On the line, the literal full relation has no left inverse, including at multiple zeros. -/
theorem deningerMeyerXiCompletedRelation_no_left_inverse (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re = 1 / 2)
    (C : Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho))
      (paperRotationAlgebra (paperPrimeRotationFrequency p (q + 1)))) :
    C * deningerMeyerXiCompletedRelationMatrix p q rho ≠ 1 := by
  intro hC
  let i : Fin (xiSupportMultiplicity rho) := ⟨0, xiSupportMultiplicity_pos rho⟩
  have hentry := congrArg (fun M => M i i) hC
  rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl] at hentry
  have hsum : (∑ j, C i j * deningerMeyerXiCompletedRelationMatrix p q rho j i) =
      C i i * (nativeCompletedModulation p q - deningerMeyerPrimeMellinCoordinate p rho • 1) := by
    rw [Finset.sum_eq_single i, completedRelation_diag]
    · intro j _ hj
      have hij : i < j := by
        change 0 < j.val
        exact Nat.pos_of_ne_zero (by intro h; apply hj; apply Fin.ext; exact h)
      rw [completedRelation_below p q rho j i hij, mul_zero]
    · simp
  rw [hsum] at hentry
  have hz : ‖deningerMeyerPrimeMellinCoordinate p rho‖ = 1 := by
    rw [deningerMeyerPrimeMellinCoordinate_norm, hrho]
    simp
  exact nativeModulation_no_left_inverse p q _ hz (C i i).val
    (congrArg Subtype.val hentry)

/-- Exact spectral boundary of the actual completed arithmetic relation. -/
theorem deningerMeyerXiCompletedRelation_isUnit_iff (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) :
    IsUnit (deningerMeyerXiCompletedRelationMatrix p q rho) ↔ (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · rintro ⟨u, hu⟩ hrho
    apply deningerMeyerXiCompletedRelation_no_left_inverse p q rho hrho (u⁻¹ : _)
    rw [← hu]
    exact u.inv_val
  · intro hrho
    exact ⟨⟨_, deningerMeyerXiCompletedRelationInverse p q rho,
      deningerMeyerXiCompletedRelationMatrix_mul_inverse p q rho hrho,
      deningerMeyerXiCompletedRelationInverse_mul p q rho hrho⟩, rfl⟩

/-- Logarithmic canonical trace formed from the actual full matrix inverse. -/
def deningerMeyerXiCompletedLogarithmicTrace (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) : ℂ :=
  ∑ i : Fin (xiSupportMultiplicity rho), paperRotationTrace
    (paperRotationModulation (paperPrimeRotationFrequency p (q + 1)) *
      (deningerMeyerXiCompletedRelationInverse p q rho i i).val)

/-- The contracting right-side resolution still has the complete source boundary trace. -/
theorem deningerMeyerXiCompletedLogarithmicTrace_right (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : 1 / 2 < (rho : ℂ).re) :
    deningerMeyerXiCompletedLogarithmicTrace p q rho = xiSupportMultiplicity rho := by
  have ht (b : ℤ) : paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1)) = 1 ↔ b = 0 := by
    simpa only [Nat.succ_ne_zero, false_or] using paperPrimeRotationPhase_int_eq_one p (q + 1) b
  simp only [deningerMeyerXiCompletedLogarithmicTrace,
    deningerMeyerXiCompletedRelationInverse_diag p q rho (ne_of_gt hrho), if_pos hrho,
    paperRotationInsideResolvent_logarithmicTrace _ ht _
      (deningerMeyerPrimeMellinCoordinate_norm_lt_one p rho hrho)]
  simp

/-- The same full inverse has zero logarithmic canonical trace on the left. -/
theorem deningerMeyerXiCompletedLogarithmicTrace_left (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re < 1 / 2) :
    deningerMeyerXiCompletedLogarithmicTrace p q rho = 0 := by
  have ht (b : ℤ) : paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1)) = 1 ↔ b = 0 := by
    simpa only [Nat.succ_ne_zero, false_or] using paperPrimeRotationPhase_int_eq_one p (q + 1) b
  simp only [deningerMeyerXiCompletedLogarithmicTrace,
    deningerMeyerXiCompletedRelationInverse_diag p q rho (ne_of_lt hrho), if_neg (not_lt_of_ge hrho.le),
    paperRotationOutsideResolvent_logarithmicTrace _ ht _
      (deningerMeyerPrimeMellinCoordinate_one_lt_norm p rho hrho), Finset.sum_const_zero]

/-- The full analytic inverse realizes the literal source boundary winding. -/
theorem deningerMeyerXiCompletedLogarithmicTrace_eq_boundary (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerXiCompletedLogarithmicTrace p q rho =
      (windingNumber (deningerMeyerXiRelationBoundaryLoop p rho) 0 (2 * Real.pi) : ℂ) := by
  rcases lt_or_gt_of_ne hrho with hl | hr
  · rw [deningerMeyerXiCompletedLogarithmicTrace_left p q rho hl,
      deningerMeyerXiRelationBoundaryLoop_winding_left p rho hl, Int.cast_zero]
  · rw [deningerMeyerXiCompletedLogarithmicTrace_right p q rho hr,
      deningerMeyerXiRelationBoundaryLoop_winding_right p rho hr, Int.cast_natCast]

end
end RHTower
