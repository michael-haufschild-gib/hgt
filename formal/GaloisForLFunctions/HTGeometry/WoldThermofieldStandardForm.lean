import GaloisForLFunctions.HTGeometry.OccupationVacuumAnomalyReciprocity
import GaloisForLFunctions.HTGeometry.HilbertSchmidt

open scoped BigOperators InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Diagonal standard-form kernel associated with a square-summable vector. -/
def thermofieldDiagonalKernel {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) : Ω × Ω → ℂ :=
  fun p => if p.1 = p.2 then v p.1 else 0

theorem thermofieldDiagonalKernel_isHS {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) :
    HilbertSchmidt.IsHS (thermofieldDiagonalKernel v) := by
  rw [HilbertSchmidt.IsHS, summable_prod_of_nonneg (fun p => by positivity)]
  constructor
  · intro i
    apply summable_of_ne_finset_zero (s := {i})
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [thermofieldDiagonalKernel, Ne.symm hji]
  · have hrow : ∀ i,
        (∑' j, ‖thermofieldDiagonalKernel v (i, j)‖ ^ 2) = ‖v i‖ ^ 2 := by
      intro i
      rw [tsum_eq_single i]
      · simp [thermofieldDiagonalKernel]
      · intro j hji
        simp [thermofieldDiagonalKernel, Ne.symm hji]
    simpa only [hrow] using HilbertSchmidt.summable_coe_sq v

theorem hsNormSq_thermofieldDiagonalKernel {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) :
    HilbertSchmidt.hsNormSq (thermofieldDiagonalKernel v) = ‖v‖ ^ 2 := by
  rw [HilbertSchmidt.hsNormSq,
    (thermofieldDiagonalKernel_isHS v).tsum_prod,
    HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [thermofieldDiagonalKernel]
  · intro j hji
    simp [thermofieldDiagonalKernel, Ne.symm hji]

/-- Left diagonal multiplication on standard-form kernels. -/
def thermofieldLeftAction {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ) : Ω × Ω → ℂ :=
  fun p => f p.1 * K p

/-- Conjugate right diagonal multiplication, in standard-form coordinates. -/
def thermofieldRightAction {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ) : Ω × Ω → ℂ :=
  fun p => f p.2 * K p

theorem thermofieldLeftAction_isHS {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.IsHS (thermofieldLeftAction f K) := by
  rw [HilbertSchmidt.IsHS] at hK ⊢
  apply Summable.of_nonneg_of_le (fun p => by positivity) _ (hK.mul_left (C ^ 2))
  intro p
  have hsq : ‖f p.1‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg (f p.1), hf p.1]
  calc
    ‖thermofieldLeftAction f K p‖ ^ 2 = ‖f p.1‖ ^ 2 * ‖K p‖ ^ 2 := by
      rw [thermofieldLeftAction, norm_mul]
      ring
    _ ≤ C ^ 2 * ‖K p‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

theorem thermofieldRightAction_isHS {Ω : Type*} (f : Ω → ℂ) (K : Ω × Ω → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, ‖f i‖ ≤ C) (hK : HilbertSchmidt.IsHS K) :
    HilbertSchmidt.IsHS (thermofieldRightAction f K) := by
  rw [HilbertSchmidt.IsHS] at hK ⊢
  apply Summable.of_nonneg_of_le (fun p => by positivity) _ (hK.mul_left (C ^ 2))
  intro p
  have hsq : ‖f p.2‖ ^ 2 ≤ C ^ 2 := by
    nlinarith [norm_nonneg (f p.2), hf p.2]
  calc
    ‖thermofieldRightAction f K p‖ ^ 2 = ‖f p.2‖ ^ 2 * ‖K p‖ ^ 2 := by
      rw [thermofieldRightAction, norm_mul]
      ring
    _ ≤ C ^ 2 * ‖K p‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

theorem thermofieldDiagonalKernel_central {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) (f : Ω → ℂ) :
    thermofieldLeftAction f (thermofieldDiagonalKernel v) =
      thermofieldRightAction f (thermofieldDiagonalKernel v) := by
  funext p
  by_cases h : p.1 = p.2
  · simp [thermofieldLeftAction, thermofieldRightAction, thermofieldDiagonalKernel, h]
  · simp [thermofieldLeftAction, thermofieldRightAction, thermofieldDiagonalKernel, h]

theorem hsInner_thermofieldDiagonalKernel_actions {Ω : Type*} [DecidableEq Ω]
    (v : lp (fun _ : Ω => ℂ) 2) (f g : Ω → ℂ)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ i, ‖f i‖ ≤ Cf) (hg : ∀ i, ‖g i‖ ≤ Cg) :
    HilbertSchmidt.hsInner (thermofieldDiagonalKernel v)
        (thermofieldLeftAction f
          (thermofieldRightAction g (thermofieldDiagonalKernel v))) =
      ∑' i, ((‖v i‖ ^ 2 : ℝ) : ℂ) * f i * g i := by
  have hK := thermofieldDiagonalKernel_isHS v
  have hR := thermofieldRightAction_isHS g _ Cg hCg hg hK
  have hLR := thermofieldLeftAction_isHS f _ Cf hCf hf hR
  rw [HilbertSchmidt.hsInner, (HilbertSchmidt.hsInner_summable hK hLR).tsum_prod]
  apply tsum_congr
  intro i
  rw [tsum_eq_single i]
  · simp [thermofieldDiagonalKernel, thermofieldLeftAction, thermofieldRightAction]
    calc
      (starRingEnd ℂ) (v i) * (f i * (g i * v i)) =
          f i * g i * (v i * (starRingEnd ℂ) (v i)) := by ring
      _ = f i * g i * (Complex.normSq (v i) : ℂ) := by rw [Complex.mul_conj]
      _ = (‖v i‖ : ℂ) ^ 2 * f i * g i := by
        rw [Complex.normSq_eq_norm_sq]
        rw [Complex.ofReal_pow]
        ring
  · intro j hji
    simp [thermofieldDiagonalKernel, thermofieldLeftAction, thermofieldRightAction,
      Ne.symm hji]

/-! ## Finite occupation specialization -/

/-- Point mass of the normalized finite occupation probability law. -/
def finiteOccupationProbabilityWeight {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (ν : ι →₀ ℕ) : ℝ :=
  HTGeometry.finiteOccupationBoundaryVolume q * ν.prod (fun i n => q i ^ n)

theorem norm_finiteOccupationNormalizedHalfDensity_apply_sq
    {ι : Type*} [Fintype ι] (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (ν : ι →₀ ℕ) :
    ‖HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1 ν‖ ^ 2 =
      finiteOccupationProbabilityWeight q ν := by
  change ‖((Real.sqrt (HTGeometry.finiteOccupationBoundaryVolume q) : ℝ) : ℂ) *
      HTGeometry.finiteOccupationHalfDensityWeight q ν‖ ^ 2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (HTGeometry.finiteOccupationBoundaryVolume_pos q hq1).le,
    HTGeometry.norm_finiteOccupationHalfDensityWeight_sq q hq0 ν]
  rfl

/-- Diagonal standard-form purification of the normalized finite occupation law. -/
def finiteOccupationThermofieldKernel {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    (ι →₀ ℕ) × (ι →₀ ℕ) → ℂ :=
  thermofieldDiagonalKernel
    (HTGeometry.finiteOccupationNormalizedHalfDensity q hq0 hq1)

theorem finiteOccupationThermofieldKernel_isHS {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.IsHS (finiteOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_isHS _

theorem hsNormSq_finiteOccupationThermofieldKernel {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) :
    HilbertSchmidt.hsNormSq (finiteOccupationThermofieldKernel q hq0 hq1) = 1 := by
  rw [finiteOccupationThermofieldKernel, hsNormSq_thermofieldDiagonalKernel,
    HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq q hq0 hq1]

theorem finiteOccupationThermofieldKernel_central {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f : (ι →₀ ℕ) → ℂ) :
    thermofieldLeftAction f (finiteOccupationThermofieldKernel q hq0 hq1) =
      thermofieldRightAction f (finiteOccupationThermofieldKernel q hq0 hq1) :=
  thermofieldDiagonalKernel_central _ f

theorem finiteOccupationThermofieldVectorState {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1)
    (f g : (ι →₀ ℕ) → ℂ) (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ ν, ‖f ν‖ ≤ Cf) (hg : ∀ ν, ‖g ν‖ ≤ Cg) :
    HilbertSchmidt.hsInner (finiteOccupationThermofieldKernel q hq0 hq1)
        (thermofieldLeftAction f
          (thermofieldRightAction g (finiteOccupationThermofieldKernel q hq0 hq1))) =
      ∑' ν, (finiteOccupationProbabilityWeight q ν : ℂ) * f ν * g ν := by
  rw [finiteOccupationThermofieldKernel,
    hsInner_thermofieldDiagonalKernel_actions _ f g Cf Cg hCf hCg hf hg]
  apply tsum_congr
  intro ν
  rw [norm_finiteOccupationNormalizedHalfDensity_apply_sq q hq0 hq1 ν]

end GaloisForLFunctions.HTGeometry
