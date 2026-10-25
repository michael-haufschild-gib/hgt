import GaloisForLFunctions.HTGeometry.PositiveIntegerBlockOperators
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras

/-!
# Exact dilation operators on the completed pronic space

Multiplication by the square root of the reciprocal pronic weight identifies
positive-index `ell2` with finite-energy arithmetic rows. Under this identification,
floor dilation is an existing division-block operator. The exact pronic fibre
mass gives its sharp norm, and cancellation of intermediate weights gives composition.
-/

noncomputable section
open Finset
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The completed pronic space in orthonormal coordinates. -/
abbrev PronicHilbertSpace := lp (fun _ : ℕ+ => ℂ) 2

/-- The square root of the denominator of the positive pronic cell. -/
def pronicCoordinateRoot (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) * ((n : ℝ) + 1))

theorem pronicCoordinateRoot_nonneg (n : ℕ) : 0 ≤ pronicCoordinateRoot n :=
  Real.sqrt_nonneg _

theorem pronicCoordinateRoot_sq (n : ℕ) :
    pronicCoordinateRoot n ^ 2 = (n : ℝ) * ((n : ℝ) + 1) :=
  Real.sq_sqrt (by positivity)

theorem pronicCoordinateRoot_pos {n : ℕ} (hn : 0 < n) :
    0 < pronicCoordinateRoot n := by
  unfold pronicCoordinateRoot
  positivity

theorem pronicCoordinateRoot_mono : Monotone pronicCoordinateRoot := by
  intro m n hmn
  apply Real.sqrt_le_sqrt
  exact mul_le_mul (by exact_mod_cast hmn) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    (by positivity) (by positivity)

/-- The normalized coordinate weight of floor dilation. -/
def pronicDilationWeight (j n : ℕ) : ℂ :=
  ((pronicCoordinateRoot (n / j) / pronicCoordinateRoot n : ℝ) : ℂ)

theorem norm_pronicDilationWeight_le (j n : ℕ) : ‖pronicDilationWeight j n‖ ≤ 1 := by
  rw [pronicDilationWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (pronicCoordinateRoot_nonneg _) (pronicCoordinateRoot_nonneg _))]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pronicCoordinateRoot]
  · exact (div_le_one (pronicCoordinateRoot_pos hn)).mpr
      (pronicCoordinateRoot_mono (Nat.div_le_self n j))

theorem norm_sq_pronicDilationWeight (j n : ℕ) :
    ‖pronicDilationWeight j n‖ ^ 2 =
      ((n / j : ℕ) : ℝ) * (((n / j : ℕ) : ℝ) + 1) /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
  rw [pronicDilationWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    pronicCoordinateRoot_sq, pronicCoordinateRoot_sq]

private theorem sum_pronic_block {j q : ℕ} (hj : 0 < j) (hq : 0 < q) :
    (∑ r : Fin j, 1 / (((q * j + r : ℕ) : ℝ) * (((q * j + r : ℕ) : ℝ) + 1))) =
      1 / ((j : ℝ) * ((q : ℝ) * ((q : ℝ) + 1))) := by
  rw [← sum_Icc_pronic_dilation_fibre hj hq]
  refine sum_bij (fun r _ => q * j + (r : ℕ)) ?_ ?_ ?_ ?_
  · intro r _
    rw [mem_Icc, Nat.mul_comm j q]
    have := r.isLt
    omega
  · intro r _ s _ hrs
    apply Fin.ext
    omega
  · intro n hn
    rw [mem_Icc, Nat.mul_comm j q] at hn
    refine ⟨⟨n - q * j, by omega⟩, mem_univ _, ?_⟩
    change q * j + (n - q * j) = n
    omega
  · intro r _
    rfl

/-- Every positive block has exactly the reciprocal dilation mass. -/
theorem pronicDilationWeight_blockMass {j : ℕ} (hj : 0 < j) {q : ℕ} (hq : 0 < q) :
    PNatBlock.divBlockMass j (pronicDilationWeight j) q = 1 / (j : ℝ) := by
  haveI : NeZero j := ⟨hj.ne'⟩
  unfold PNatBlock.divBlockMass
  simp only [norm_sq_pronicDilationWeight, PNatBlock.div_block]
  simp_rw [div_eq_mul_inv]
  rw [← mul_sum]
  have hs := sum_pronic_block hj hq
  simp only [one_div] at hs
  rw [hs]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hjR, hqR, hq1]

/-- Floor dilation acting on the completed pronic space. -/
def pronicDilationOp (j : ℕ) : PronicHilbertSpace →L[ℂ] PronicHilbertSpace :=
  PNatBlock.divBlockOp j (pronicDilationWeight j)

theorem pronicDilationOp_apply {j : ℕ} (hj : 0 < j) (f : PronicHilbertSpace) (n : ℕ+) :
    pronicDilationOp j f n =
      pronicDilationWeight j n * PNatBlock.extZero f ((n : ℕ) / j) :=
  PNatBlock.divBlockOp_apply hj (norm_pronicDilationWeight_le j) f n

/-- The full pronic norm obeys an equality, not only a finite-cutoff contraction. -/
theorem norm_sq_pronicDilationOp {j : ℕ} (hj : 0 < j) (f : PronicHilbertSpace) :
    ‖pronicDilationOp j f‖ ^ 2 = (1 / (j : ℝ)) * ‖f‖ ^ 2 := by
  rw [pronicDilationOp, PNatBlock.norm_sq_divBlockOp hj (norm_pronicDilationWeight_le j),
    PNatBlock.norm_sq_eq_tsum_extZero, ← tsum_mul_left]
  apply tsum_congr
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · rw [pronicDilationWeight_blockMass hj hq]

/-- Dilation has its exact square-root contraction factor on every vector. -/
theorem norm_pronicDilationOp {j : ℕ} (hj : 0 < j) (f : PronicHilbertSpace) :
    ‖pronicDilationOp j f‖ = (1 / Real.sqrt (j : ℝ)) * ‖f‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
  rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    norm_sq_pronicDilationOp hj]

theorem norm_pronicDilationOp_le {j : ℕ} (hj : 0 < j) :
    ‖pronicDilationOp j‖ ≤ 1 / Real.sqrt (j : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
  exact (norm_pronicDilationOp hj f).le

private theorem pronicDilationWeight_mul (j k n : ℕ) :
    pronicDilationWeight j n * pronicDilationWeight k (n / j) =
      pronicDilationWeight (j * k) n := by
  unfold pronicDilationWeight
  rw [← Complex.ofReal_mul, ← Nat.div_div_eq_div_mul]
  apply congrArg Complex.ofReal
  by_cases hq : n / j = 0
  · simp [hq, pronicCoordinateRoot]
  · have hqroot := (pronicCoordinateRoot_pos (Nat.pos_of_ne_zero hq)).ne'
    have hn : 0 < n := lt_of_lt_of_le (Nat.pos_of_ne_zero hq) (Nat.div_le_self n j)
    have hnroot := (pronicCoordinateRoot_pos hn).ne'
    field_simp [hqroot, hnroot]

/-- The completed floor actions preserve multiplication of scales exactly. -/
theorem pronicDilationOp_comp {j k : ℕ} (hj : 0 < j) (hk : 0 < k) :
    pronicDilationOp j ∘L pronicDilationOp k = pronicDilationOp (j * k) := by
  unfold pronicDilationOp
  rw [PNatBlock.divBlockOp_comp hj hk (norm_pronicDilationWeight_le j)
    (norm_pronicDilationWeight_le k)]
  congr 1
  funext n
  exact pronicDilationWeight_mul j k n

theorem pronicDilationOp_one : pronicDilationOp 1 = ContinuousLinearMap.id ℂ _ := by
  ext f n
  rw [pronicDilationOp_apply (by norm_num), ContinuousLinearMap.id_apply]
  simp only [Nat.div_one, PNatBlock.extZero_coe, pronicDilationWeight]
  rw [div_self (pronicCoordinateRoot_pos n.pos).ne', Complex.ofReal_one, one_mul]

theorem pronicDilationOp_zero : pronicDilationOp 0 = 0 := by
  simp [pronicDilationOp, PNatBlock.divBlockOp]

/-- Multiplicativity includes the unused zero coefficient, extended by the zero operator. -/
theorem pronicDilationOp_mul (j k : ℕ) :
    pronicDilationOp (j * k) = pronicDilationOp j * pronicDilationOp k := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [zero_mul, pronicDilationOp_zero]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [mul_zero, pronicDilationOp_zero]
  exact (pronicDilationOp_comp hj hk).symm

theorem norm_pronicDilationOp_le_wienerWeight (j : ℕ) (hj : j ≠ 0) :
    ‖pronicDilationOp j‖ ≤ (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  calc
    _ ≤ 1 / Real.sqrt (j : ℝ) := norm_pronicDilationOp_le (Nat.pos_of_ne_zero hj)
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg j), one_div]

/-- Every critical Wiener kernel acts on the ordinary completed pronic space. -/
def pronicWienerRepresentation :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] (PronicHilbertSpace →L[ℂ] PronicHilbertSpace) :=
  WienerAlgebraAt.sequenceRepresentation pronicDilationOp pronicDilationOp_zero
    norm_pronicDilationOp_le_wienerWeight pronicDilationOp_one pronicDilationOp_mul

/-- The complete action is the absolutely convergent coefficient series. -/
theorem pronicWienerRepresentation_eq_tsum (a : WienerAlgebraAt (1 / 2)) :
    pronicWienerRepresentation a = ∑' j, a.toFn j • pronicDilationOp j := rfl

theorem pronicWienerRepresentation_pointMass (j : ℕ) :
    pronicWienerRepresentation (WienerAlgebraAt.pointMass j) = pronicDilationOp j :=
  WienerAlgebraAt.sequenceExtension_pointMass pronicDilationOp pronicDilationOp_zero
    norm_pronicDilationOp_le_wienerWeight j

/-- The universal pronic representation is contractive for the exact critical Wiener norm. -/
theorem norm_pronicWienerRepresentation_le (a : WienerAlgebraAt (1 / 2)) :
    ‖pronicWienerRepresentation a‖ ≤ ‖a‖ :=
  WienerAlgebraAt.norm_tsum_coefficient_smul_le pronicDilationOp pronicDilationOp_zero
    norm_pronicDilationOp_le_wienerWeight a

end GaloisForLFunctions.BiarithmeticGeometry
