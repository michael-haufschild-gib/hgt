import GaloisForLFunctions.HTGeometry.MarkedHalfCharacterCompactActionLaw
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau
import GaloisForLFunctions.RHTower.StaticChoiTraceDistanceLaw
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

/-!
# Framed two-boundary phase fibre, recurrence, and history separation

Unconditional finite-dimensional formalization of the framed GHZ boundary fibre. The module
computes exact boundary reductions, projective phase fibre, radial QEC invariant, Fubini--Study
metric and sharp lifted-history minima, Berry quotient, exact recurrence, finite Krylov collision,
and the typed obstruction separating boundary data from executed history.
-/

open MeasureTheory Set intervalIntegral
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Projected phase geometry -/

def framedPhaseMean {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  (∑ j, v j) / d

def framedPhaseProjection {d : ℕ} (v : Fin d → ℝ) (j : Fin d) : ℝ :=
  v j - framedPhaseMean v

def framedPhaseNormSq {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  ∑ j, framedPhaseProjection v j ^ 2

def framedFubiniStudyMetric {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  (∑ j, v j ^ 2) / d - (∑ j, v j) ^ 2 / d ^ 2

theorem sum_framedPhaseProjection {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) :
    ∑ j, framedPhaseProjection v j = 0 := by
  simp_rw [framedPhaseProjection]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, framedPhaseMean]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

theorem framedFubiniStudyMetric_eq_projected
    {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) :
    framedFubiniStudyMetric v = framedPhaseNormSq v / d := by
  have hpoint (j : Fin d) :
      framedPhaseProjection v j ^ 2 =
        v j ^ 2 - 2 * framedPhaseMean v * v j + framedPhaseMean v ^ 2 := by
    simp only [framedPhaseProjection]
    ring
  rw [framedFubiniStudyMetric, framedPhaseNormSq]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  simp only [framedPhaseMean]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

theorem framedFubiniStudyMetric_expanded
    {d : ℕ} (v : Fin d → ℝ) :
    framedFubiniStudyMetric v =
      (1 / d) * ∑ j, v j ^ 2 - (1 / d ^ 2) * (∑ j, v j) ^ 2 := by
  rw [framedFubiniStudyMetric]
  ring

def framedPureStateQuantumFisher {d : ℕ} (v : Fin d → ℝ) : ℝ :=
  4 * framedFubiniStudyMetric v

def framedFubiniStudyAction {d : ℕ} (T : ℝ) (velocity : ℝ → Fin d → ℝ) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..T, framedFubiniStudyMetric (velocity t)

theorem framedFubiniStudyAction_eq_quantumFisher
    {d : ℕ} (T : ℝ) (velocity : ℝ → Fin d → ℝ) :
    framedFubiniStudyAction T velocity =
      (1 / 8) * ∫ t in (0 : ℝ)..T, framedPureStateQuantumFisher (velocity t) := by
  rw [framedFubiniStudyAction]
  simp_rw [framedPureStateQuantumFisher]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

def uniformEnergyVariance {d : ℕ} (E : Fin d → ℝ) : ℝ :=
  framedFubiniStudyMetric E

theorem constantGenerator_quantumFisher {d : ℕ} (E : Fin d → ℝ) :
    framedPureStateQuantumFisher (fun j => -E j) = 4 * uniformEnergyVariance E := by
  simp only [framedPureStateQuantumFisher, uniformEnergyVariance,
    framedFubiniStudyMetric]
  congr 1
  simp only [neg_sq, Finset.sum_neg_distrib, neg_sq]

theorem constantGenerator_action {d : ℕ} (E : Fin d → ℝ) (T : ℝ) :
    framedFubiniStudyAction T (fun _ j => -E j) =
      T / 2 * uniformEnergyVariance E := by
  rw [framedFubiniStudyAction]
  have hmetric : framedFubiniStudyMetric (fun j => -E j) =
      uniformEnergyVariance E := by
    simp [uniformEnergyVariance, framedFubiniStudyMetric]
  simp_rw [hmetric, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

def framedConstantGeneratorLength {d : ℕ} (E : Fin d → ℝ) (T : ℝ) : ℝ :=
  T * Real.sqrt (uniformEnergyVariance E)

theorem framedConstantGeneratorLength_formula {d : ℕ} (E : Fin d → ℝ) (T : ℝ) :
    framedConstantGeneratorLength E T =
      T * Real.sqrt (uniformEnergyVariance E) := rfl

/-! ## Winding and Berry quotient -/

def framedWindingProjectedNormSq {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  framedPhaseNormSq (fun j => (m j : ℝ))

def framedWindingMinimumAction {d : ℕ} (T : ℝ) (m : Fin d → ℤ) : ℝ :=
  2 * Real.pi ^ 2 / (d * T) * framedWindingProjectedNormSq m

def framedWindingMinimumLength {d : ℕ} (m : Fin d → ℤ) : ℝ :=
  2 * Real.pi / Real.sqrt d * Real.sqrt (framedWindingProjectedNormSq m)

def framedBerryHolonomy {d : ℕ} (m : Fin d → ℤ) : ℂ :=
  Complex.exp (-((2 * Real.pi / d * (∑ j, (m j : ℝ) : ℝ) : ℝ) : ℂ) * Complex.I)

theorem framedBerryHolonomy_formula {d : ℕ} (m : Fin d → ℤ) :
    framedBerryHolonomy m =
      Complex.exp (-((2 * Real.pi / d * (∑ j, (m j : ℝ) : ℝ) : ℝ) : ℂ) *
        Complex.I) := rfl

theorem framedBerryHolonomy_add_diagonal
    {d : ℕ} (hd : 0 < d) (m : Fin d → ℤ) (k : ℤ) :
    framedBerryHolonomy (fun j => m j + k) = framedBerryHolonomy m := by
  rw [framedBerryHolonomy, framedBerryHolonomy]
  have hsum : (∑ j : Fin d, ((m j + k : ℤ) : ℝ)) =
      (∑ j, (m j : ℝ)) + d * (k : ℝ) := by
    simp only [Int.cast_add, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
  rw [hsum]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨-k, ?_⟩
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  apply Complex.ext
  · norm_num [Complex.mul_re]
  · norm_num [Complex.mul_im]
    field_simp [hdR]
    ring

theorem framedPhaseProjection_add_diagonal
    {d : ℕ} (hd : 0 < d) (m : Fin d → ℤ) (k : ℤ) :
    framedPhaseProjection (fun j => ((m j + k : ℤ) : ℝ)) =
      framedPhaseProjection (fun j => (m j : ℝ)) := by
  funext j
  have hsum : (∑ i : Fin d, ((m i + k : ℤ) : ℝ)) =
      (∑ i, (m i : ℝ)) + d * (k : ℝ) := by
    simp only [Int.cast_add, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul]
  rw [framedPhaseProjection, framedPhaseProjection, framedPhaseMean, framedPhaseMean, hsum]
  push_cast
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR]
  ring

theorem framedWindingProjectedNormSq_add_diagonal
    {d : ℕ} (hd : 0 < d) (m : Fin d → ℤ) (k : ℤ) :
    framedWindingProjectedNormSq (fun j => m j + k) =
      framedWindingProjectedNormSq m := by
  rw [framedWindingProjectedNormSq, framedWindingProjectedNormSq,
    framedPhaseNormSq, framedPhaseNormSq,
    framedPhaseProjection_add_diagonal hd]

def framedWindingSetoid (d : ℕ) : Setoid (Fin d → ℤ) where
  r m n := ∃ k : ℤ, n = fun j => m j + k
  iseqv := {
    refl := fun m => ⟨0, by funext j; simp⟩
    symm := by
      rintro m n ⟨k, rfl⟩
      refine ⟨-k, ?_⟩
      funext j
      ring
    trans := by
      rintro m n p ⟨k, rfl⟩ ⟨l, rfl⟩
      refine ⟨k + l, ?_⟩
      funext j
      ring }

/-- Exact winding lattice quotient `ℤ^(n+1) / ℤ·1`. -/
abbrev FramedWindingClass (n : ℕ) := Quotient (framedWindingSetoid (n + 1))

def framedWindingClassProjectedNormSq (n : ℕ) : FramedWindingClass n → ℝ :=
  Quotient.lift framedWindingProjectedNormSq (by
    rintro m p ⟨k, rfl⟩
    exact (framedWindingProjectedNormSq_add_diagonal (Nat.succ_pos n) m k).symm)

def framedWindingClassBerryHolonomy (n : ℕ) : FramedWindingClass n → ℂ :=
  Quotient.lift framedBerryHolonomy (by
    rintro m p ⟨k, rfl⟩
    exact (framedBerryHolonomy_add_diagonal (Nat.succ_pos n) m k).symm)

theorem framedWindingClass_mk_add_diagonal
    (n : ℕ) (m : Fin (n + 1) → ℤ) (k : ℤ) :
    Quotient.mk (framedWindingSetoid (n + 1)) (fun j => m j + k) =
      Quotient.mk (framedWindingSetoid (n + 1)) m := by
  apply Quotient.sound
  exact ⟨-k, by funext j; ring⟩

def zeroWindingTwo : Fin 2 → ℤ := fun _ => 0

def oppositeWindingTwo : Fin 2 → ℤ := ![1, -1]

theorem berryHolonomy_does_not_determine_windingAction :
    framedBerryHolonomy zeroWindingTwo = framedBerryHolonomy oppositeWindingTwo ∧
      framedWindingProjectedNormSq zeroWindingTwo = 0 ∧
      framedWindingProjectedNormSq oppositeWindingTwo = 2 := by
  constructor
  · simp [framedBerryHolonomy, zeroWindingTwo, oppositeWindingTwo]
  constructor <;>
    norm_num [framedWindingProjectedNormSq, framedPhaseNormSq,
      framedPhaseProjection, framedPhaseMean, zeroWindingTwo, oppositeWindingTwo]

/-! ## Exact projective return -/

def framedProjectiveReturn {d : ℕ} (anchor : Fin d) (E : Fin d → ℝ) (T : ℝ) : Prop :=
  ∀ j, Complex.exp (-((T * E j : ℝ) : ℂ) * Complex.I) =
    Complex.exp (-((T * E anchor : ℝ) : ℂ) * Complex.I)

theorem framedProjectiveReturn_iff
    {d : ℕ} (anchor : Fin d) (E : Fin d → ℝ) (T : ℝ) :
    framedProjectiveReturn anchor E T ↔
      ∀ j, ∃ n : ℤ, T * (E j - E anchor) = 2 * Real.pi * n := by
  constructor
  · intro h j
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h j)
    refine ⟨-n, ?_⟩
    have him := congrArg Complex.im hn
    norm_num [Complex.mul_im] at him
    push_cast at him ⊢
    linear_combination -him
  · intro h j
    obtain ⟨n, hn⟩ := h j
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-n, ?_⟩
    push_cast
    apply Complex.ext
    · norm_num [Complex.mul_re]
    · norm_num [Complex.mul_im]
      linear_combination -hn

/-! ## Two-level Krylov collision -/

def twoLevelKrylovComplexity (omega t : ℝ) : ℝ :=
  Real.sin (omega * t / 2) ^ 2

def twoLevelSurvivalAmplitude (omega t : ℝ) : ℝ :=
  Real.cos (omega * t / 2)

theorem twoLevelKrylovComplexity_eq_fidelityDeficit (omega t : ℝ) :
    twoLevelKrylovComplexity omega t =
      1 - |twoLevelSurvivalAmplitude omega t| ^ 2 := by
  rw [twoLevelKrylovComplexity, twoLevelSurvivalAmplitude, sq_abs,
    ← Real.sin_sq_add_cos_sq (omega * t / 2)]
  ring

def twoLevelExecutedFubiniStudyLength (omega t : ℝ) : ℝ :=
  |omega * t| / 2

theorem twoLevel_fullPeriod_collision
    {omega : ℝ} (homega : omega ≠ 0) :
    twoLevelKrylovComplexity omega (2 * Real.pi / |omega|) = 0 ∧
      twoLevelExecutedFubiniStudyLength omega (2 * Real.pi / |omega|) = Real.pi := by
  have habs : |omega| ≠ 0 := abs_ne_zero.mpr homega
  constructor
  · rw [twoLevelKrylovComplexity]
    rcases lt_or_gt_of_ne homega with hneg | hpos
    · have harg : omega * (2 * Real.pi / |omega|) / 2 = -Real.pi := by
        rw [abs_of_neg hneg]
        field_simp [homega]
      rw [harg, Real.sin_neg, Real.sin_pi]
      norm_num
    · have harg : omega * (2 * Real.pi / |omega|) / 2 = Real.pi := by
        rw [abs_of_pos hpos]
        field_simp [homega]
      rw [harg, Real.sin_pi]
      norm_num
  · rw [twoLevelExecutedFubiniStudyLength]
    rw [abs_mul, abs_div, abs_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
      ]
    field_simp [habs]

def finiteKrylovComplexity {D : ℕ} (probability : Fin D → ℝ) : ℝ :=
  ∑ j, (j.val : ℝ) * probability j

theorem finiteKrylovComplexity_bounds
    {D : ℕ} (probability : Fin D → ℝ)
    (hnonneg : ∀ j, 0 ≤ probability j)
    (hsum : ∑ j, probability j = 1) :
    0 ≤ finiteKrylovComplexity probability ∧
      finiteKrylovComplexity probability ≤ ((D - 1 : ℕ) : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hnonneg j)
  · by_cases hD : D = 0
    · subst D
      simp [finiteKrylovComplexity]
    · have hDpos : 0 < D := Nat.pos_of_ne_zero hD
      calc
        finiteKrylovComplexity probability = ∑ j, (j.val : ℝ) * probability j := rfl
        _ ≤ ∑ j, ((D - 1 : ℕ) : ℝ) * probability j := by
          apply Finset.sum_le_sum
          intro j _
          have hj : j.val ≤ D - 1 := by omega
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (hnonneg j)
        _ = ((D - 1 : ℕ) : ℝ) := by rw [← Finset.mul_sum, hsum, mul_one]

/-! ## Framed GHZ state and exact boundary marginals -/

abbrev FramedTripartiteIndex (d : ℕ) := Fin d × (Fin d × Fin d)

def framedGHZVector (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (FramedTripartiteIndex d) :=
  WithLp.toLp 2 fun p =>
    if p.1 = p.2.1 ∧ p.1 = p.2.2 then
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x p.1)
    else 0

@[simp] theorem framedGHZVector_apply
    (d : ℕ) (x : Fin d → UnitAddCircle) (p : FramedTripartiteIndex d) :
    framedGHZVector d x p =
      if p.1 = p.2.1 ∧ p.1 = p.2.2 then
        ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x p.1)
      else 0 := rfl

def framedGHZDensity (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d) :=
  RHTower.pureStateDensity (framedGHZVector d x)

def framedBoundaryDensity (d : ℕ) :
    EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  WithLp.toLp 2 fun pq =>
    if pq.1.1 = pq.1.2 ∧ pq.2.1 = pq.2.2 ∧ pq.1.1 = pq.2.1 then
      ((d : ℝ)⁻¹ : ℂ)
    else 0

def framedPartialTraceB (d : ℕ)
    (rho : EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d)) :
    EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  WithLp.toLp 2 fun pq =>
    ∑ b : Fin d,
      rho ((pq.1.1, (pq.1.2, b)), (pq.2.1, (pq.2.2, b)))

def framedPartialTraceA (d : ℕ)
    (rho : EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d)) :
    EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  WithLp.toLp 2 fun pq =>
    ∑ a : Fin d,
      rho ((pq.1.1, (a, pq.1.2)), (pq.2.1, (a, pq.2.2)))

theorem framedGHZVector_norm
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    ‖framedGHZVector d x‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [framedGHZVector_apply]
  simp_rw [Fintype.sum_prod_type]
  simp_rw [apply_ite (fun z : ℂ => ‖z‖), norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, fourier_apply, Circle.norm_coe]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdR)
  simp only [norm_zero, mul_one, one_pow]
  have hinner (r : Fin d) :
      (∑ a : Fin d, ∑ b : Fin d,
        (if r = a ∧ r = b then |Real.sqrt (d : ℝ)|⁻¹ else 0) ^ 2) =
        |Real.sqrt (d : ℝ)|⁻¹ ^ 2 := by
    rw [Finset.sum_eq_single r]
    · rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hbr
        simp [Ne.symm hbr]
      · simp
    · intro a _ har
      simp [Ne.symm har]
    · simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring_nf
  rw [abs_of_pos (Real.sqrt_pos.2 hdR), inv_pow]
  rw [show Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) by exact Real.sq_sqrt hdR.le]
  field_simp

theorem framedGHZ_coefficient_density
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) (j : Fin d) :
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x j)) *
        starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x j)) =
      ((d : ℝ)⁻¹ : ℂ) := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdR)
  have hreal : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
      (d : ℝ)⁻¹ := by
    field_simp [hsqrt]
    simpa [pow_two] using (Real.mul_self_sqrt hdR.le).symm
  have hcoef :
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) =
        ((d : ℝ)⁻¹ : ℂ) := by
    rw [starRingEnd_apply, Complex.star_def, map_inv₀, Complex.conj_ofReal]
    exact_mod_cast hreal
  rw [map_mul]
  calc
    _ = ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
        (fourier 1 (x j) * starRingEnd ℂ (fourier 1 (x j)))) := by ring
    _ = _ := by
      rw [hcoef, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp

theorem framedGHZ_coefficient_density_expanded
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) (j : Fin d) :
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x j)) *
        (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (fourier 1 (x j))) = ((d : ℝ)⁻¹ : ℂ) := by
  have hc : starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) := by
    rw [map_inv₀, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x j)) *
        starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * fourier 1 (x j))) := by
          rw [map_mul, hc]
    _ = _ := framedGHZ_coefficient_density hd x j

theorem framedGHZ_coefficient_density_circle
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) (j : Fin d) :
    (((Real.sqrt (d : ℝ))⁻¹ : ℂ) * (AddCircle.toCircle (x j) : ℂ)) *
        (((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (AddCircle.toCircle (x j) : ℂ)) = ((d : ℝ)⁻¹ : ℂ) := by
  simpa only [fourier_one] using framedGHZ_coefficient_density_expanded hd x j

theorem framedPartialTraceB_framedGHZDensity
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    framedPartialTraceB d (framedGHZDensity d x) = framedBoundaryDensity d := by
  ext pq
  simp only [framedPartialTraceB, framedGHZDensity, RHTower.pureStateDensity_apply,
    framedGHZVector_apply, framedBoundaryDensity]
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  by_cases h1 : pq.1.1 = pq.1.2 <;>
    by_cases h2 : pq.2.1 = pq.2.2 <;>
    by_cases h3 : pq.1.1 = pq.2.1 <;>
    simp_all [eq_comm, framedGHZ_coefficient_density_circle hd]
theorem framedPartialTraceA_framedGHZDensity
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    framedPartialTraceA d (framedGHZDensity d x) = framedBoundaryDensity d := by
  ext pq
  simp only [framedPartialTraceA, framedGHZDensity, RHTower.pureStateDensity_apply,
    framedGHZVector_apply, framedBoundaryDensity]
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  by_cases h1 : pq.1.1 = pq.1.2 <;>
    by_cases h2 : pq.2.1 = pq.2.2 <;>
    by_cases h3 : pq.1.1 = pq.2.1 <;>
    simp_all [eq_comm, framedGHZ_coefficient_density_circle hd]

abbrev framedDiagonalSupport {d : ℕ} (p : FramedTripartiteIndex d) : Prop :=
  p.1 = p.2.1 ∧ p.1 = p.2.2

def framedDephasedDensity (d : ℕ) :
    EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d) :=
  WithLp.toLp 2 fun pq =>
    if framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
        pq.1.1 = pq.2.1 then
      ((d : ℝ)⁻¹ : ℂ)
    else 0

def framedCoherenceDefect (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d) :=
  framedGHZDensity d x - framedDephasedDensity d

theorem framedGHZDensity_apply
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle)
    (pq : FramedTripartiteIndex d × FramedTripartiteIndex d) :
    framedGHZDensity d x pq =
      if framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 then
        ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x pq.1.1) *
          starRingEnd ℂ (fourier 1 (x pq.2.1))
      else 0 := by
  rw [framedGHZDensity, RHTower.pureStateDensity_apply]
  simp only [framedGHZVector_apply]
  simp only [framedDiagonalSupport]
  by_cases h1 : pq.1.1 = pq.1.2.1 <;>
    by_cases h2 : pq.1.1 = pq.1.2.2 <;>
    by_cases h3 : pq.2.1 = pq.2.2.1 <;>
    by_cases h4 : pq.2.1 = pq.2.2.2 <;>
    simp_all only [and_self, true_and, and_true, if_true, if_false, map_mul,
      map_zero, mul_zero, zero_mul]
  rw [← h2, ← h4]
  calc
    _ = ((((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
          starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ))) *
        fourier 1 (x pq.1.1) * starRingEnd ℂ (fourier 1 (x pq.2.1))) := by ring
    _ = _ := by
      have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
      have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdR)
      have hreal : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ =
          (d : ℝ)⁻¹ := by
        field_simp [hsqrt]
        simpa [pow_two] using (Real.mul_self_sqrt hdR.le).symm
      have hcoef :
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
              starRingEnd ℂ (((Real.sqrt (d : ℝ))⁻¹ : ℂ)) =
            ((d : ℝ)⁻¹ : ℂ) := by
        rw [map_inv₀, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
        exact_mod_cast hreal
      rw [hcoef]

theorem norm_framedCoherenceDefect_apply_sq
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle)
    (pq : FramedTripartiteIndex d × FramedTripartiteIndex d) :
    ‖framedCoherenceDefect d x pq‖ ^ 2 =
      if framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
          pq.1.1 ≠ pq.2.1 then
        (d : ℝ)⁻¹ ^ 2
      else 0 := by
  rw [framedCoherenceDefect, PiLp.sub_apply, framedGHZDensity_apply hd]
  simp only [framedDephasedDensity]
  by_cases hp : framedDiagonalSupport pq.1
  · by_cases hq : framedDiagonalSupport pq.2
    · have hboth : framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 := ⟨hp, hq⟩
      rw [if_pos hboth]
      by_cases heq : pq.1.1 = pq.2.1
      · have hunit : fourier 1 (x pq.1.1) *
            starRingEnd ℂ (fourier 1 (x pq.1.1)) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          simp
        have hdensity :
            ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x pq.1.1) *
                starRingEnd ℂ (fourier 1 (x pq.1.1)) = ((d : ℝ)⁻¹ : ℂ) := by
          rw [mul_assoc, hunit, mul_one]
        rw [if_pos ⟨hp, hq, heq⟩,
          if_neg (fun h => h.2.2 heq)]
        rw [← heq, hdensity]
        norm_num
      · rw [if_neg (fun h => heq h.2.2), if_pos ⟨hp, hq, heq⟩, sub_zero]
        have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hdR, fourier_apply, Circle.norm_coe, RCLike.norm_conj]
        norm_num
    · have hboth : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2) :=
        fun h => hq h.2
      have htripleEq : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
          pq.1.1 = pq.2.1) := fun h => hq h.2.1
      have htripleNe : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
          pq.1.1 ≠ pq.2.1) := fun h => hq h.2.1
      rw [if_neg hboth, if_neg htripleEq, if_neg htripleNe]
      norm_num
  · have hboth : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2) :=
      fun h => hp h.1
    have htripleEq : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
        pq.1.1 = pq.2.1) := fun h => hp h.1
    have htripleNe : ¬(framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 ∧
        pq.1.1 ≠ pq.2.1) := fun h => hp h.1
    rw [if_neg hboth, if_neg htripleEq, if_neg htripleNe]
    norm_num

theorem norm_framedCoherenceDefect_sq
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    ‖framedCoherenceDefect d x‖ ^ 2 = 1 - (d : ℝ)⁻¹ := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [norm_framedCoherenceDefect_apply_sq hd]
  simp_rw [Fintype.sum_prod_type]
  simp only [framedDiagonalSupport]
  have hcollapsePair (r s : Fin d) :
      (∑ a : Fin d, ∑ b : Fin d, ∑ c : Fin d, ∑ e : Fin d,
        if (r = a ∧ r = b) ∧ (s = c ∧ s = e) ∧ r ≠ s then
          (d : ℝ)⁻¹ ^ 2 else 0) =
        if r ≠ s then (d : ℝ)⁻¹ ^ 2 else 0 := by
    by_cases hrs : r ≠ s
    · rw [if_pos hrs]
      rw [Finset.sum_eq_single r]
      · rw [Finset.sum_eq_single r]
        · rw [Finset.sum_eq_single s]
          · rw [Finset.sum_eq_single s]
            · simp [hrs]
            · intro e _ hes
              simp [Ne.symm hes]
            · simp
          · intro c _ hcs
            simp [Ne.symm hcs]
          · simp
        · intro b _ hbr
          simp [Ne.symm hbr]
        · simp
      · intro a _ har
        simp [Ne.symm har]
      · simp
    · rw [if_neg hrs]
      simp [hrs]
  have hcollapse (r : Fin d) :
      (∑ a : Fin d, ∑ b : Fin d, ∑ s : Fin d, ∑ c : Fin d, ∑ e : Fin d,
        if (r = a ∧ r = b) ∧ (s = c ∧ s = e) ∧ r ≠ s then
          (d : ℝ)⁻¹ ^ 2 else 0) =
        ∑ s : Fin d, if r ≠ s then (d : ℝ)⁻¹ ^ 2 else 0 := by
    calc
      _ = ∑ a : Fin d, ∑ s : Fin d, ∑ b : Fin d, ∑ c : Fin d, ∑ e : Fin d,
          if (r = a ∧ r = b) ∧ (s = c ∧ s = e) ∧ r ≠ s then
            (d : ℝ)⁻¹ ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
      _ = ∑ s : Fin d, ∑ a : Fin d, ∑ b : Fin d, ∑ c : Fin d, ∑ e : Fin d,
          if (r = a ∧ r = b) ∧ (s = c ∧ s = e) ∧ r ≠ s then
            (d : ℝ)⁻¹ ^ 2 else 0 := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        exact hcollapsePair r s
  simp_rw [hcollapse]
  have hcount (r : Fin d) :
      (∑ s : Fin d, if r ≠ s then (d : ℝ)⁻¹ ^ 2 else 0) =
        ((d - 1 : ℕ) : ℝ) * (d : ℝ)⁻¹ ^ 2 := by
    rw [← Finset.sum_filter]
    have hfilter : Finset.univ.filter (fun s : Fin d => r ≠ s) =
        Finset.univ.erase r := by
      ext s
      simp [eq_comm]
    rw [hfilter, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ r),
      Finset.card_fin, nsmul_eq_mul]
  simp_rw [hcount]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpred : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [hpred]
  field_simp [hdR]

def finiteMatrixTraceSquare {ι : Type*} [Fintype ι]
    (rho : EuclideanSpace ℂ (ι × ι)) : ℂ :=
  ∑ p : ι, ∑ q : ι, rho (p, q) * rho (q, p)

theorem finiteMatrixTraceSquare_eq_norm_sq_of_hermitian
    {ι : Type*} [Fintype ι] (rho : EuclideanSpace ℂ (ι × ι))
    (hherm : ∀ p q, rho (q, p) = starRingEnd ℂ (rho (p, q))) :
    finiteMatrixTraceSquare rho = ((‖rho‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteMatrixTraceSquare, EuclideanSpace.norm_sq_eq]
  push_cast
  simp_rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hherm p q, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_num

theorem framedGHZDensity_swap_star
    {d : ℕ} (x : Fin d → UnitAddCircle) (p q : FramedTripartiteIndex d) :
    framedGHZDensity d x (q, p) = starRingEnd ℂ (framedGHZDensity d x (p, q)) := by
  rw [framedGHZDensity, RHTower.pureStateDensity_apply,
    RHTower.pureStateDensity_apply]
  change framedGHZVector d x q * starRingEnd ℂ (framedGHZVector d x p) =
    starRingEnd ℂ (framedGHZVector d x p * starRingEnd ℂ (framedGHZVector d x q))
  rw [map_mul, starRingEnd_self_apply]
  ring

theorem framedDephasedDensity_swap_star
    {d : ℕ} (p q : FramedTripartiteIndex d) :
    framedDephasedDensity d (q, p) = starRingEnd ℂ (framedDephasedDensity d (p, q)) := by
  have hcond :
      (framedDiagonalSupport q ∧ framedDiagonalSupport p ∧ q.1 = p.1) =
        (framedDiagonalSupport p ∧ framedDiagonalSupport q ∧ p.1 = q.1) := by
    apply propext
    constructor
    · rintro ⟨hq, hp, hqp⟩
      exact ⟨hp, hq, hqp.symm⟩
    · rintro ⟨hp, hq, hpq⟩
      exact ⟨hq, hp, hpq.symm⟩
  change (if framedDiagonalSupport q ∧ framedDiagonalSupport p ∧ q.1 = p.1 then
      ((d : ℝ)⁻¹ : ℂ) else 0) =
    starRingEnd ℂ (if framedDiagonalSupport p ∧ framedDiagonalSupport q ∧ p.1 = q.1 then
      ((d : ℝ)⁻¹ : ℂ) else 0)
  by_cases h : framedDiagonalSupport p ∧ framedDiagonalSupport q ∧ p.1 = q.1
  · rw [if_pos h, if_pos (hcond.mpr h)]
    simp
  · rw [if_neg h, if_neg (fun hswap => h (hcond.mp hswap))]
    simp

theorem framedCoherenceDefect_swap_star
    {d : ℕ} (x : Fin d → UnitAddCircle) (p q : FramedTripartiteIndex d) :
    framedCoherenceDefect d x (q, p) =
      starRingEnd ℂ (framedCoherenceDefect d x (p, q)) := by
  rw [framedCoherenceDefect, PiLp.sub_apply, PiLp.sub_apply, map_sub,
    framedGHZDensity_swap_star, framedDephasedDensity_swap_star]

theorem traceSquare_framedCoherenceDefect
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    finiteMatrixTraceSquare (framedCoherenceDefect d x) =
      ((1 - (d : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [finiteMatrixTraceSquare_eq_norm_sq_of_hermitian
    (framedCoherenceDefect d x) (framedCoherenceDefect_swap_star x),
    norm_framedCoherenceDefect_sq hd]

/-! ## Exact marginal spectra, entropy, and recovery optimum -/

def framedBoundaryEigenvalue (d : ℕ) (u : Fin d × Fin d) : ℝ :=
  if u.1 = u.2 then (d : ℝ)⁻¹ else 0

theorem framedBoundaryDensity_spectralDiagonal
    {d : ℕ} (u v : Fin d × Fin d) :
    framedBoundaryDensity d (u, v) =
      if u = v then (framedBoundaryEigenvalue d u : ℂ) else 0 := by
  by_cases hu : u.1 = u.2 <;>
    by_cases hv : v.1 = v.2 <;>
    by_cases huv : u = v <;>
    simp_all [framedBoundaryDensity, framedBoundaryEigenvalue, Prod.ext_iff]

def finiteSpectralEntropy {ι : Type*} [Fintype ι] (eigenvalue : ι → ℝ) : ℝ :=
  -∑ i, eigenvalue i * Real.log (eigenvalue i)

def framedBoundaryEntropy (d : ℕ) : ℝ :=
  finiteSpectralEntropy (framedBoundaryEigenvalue d)

def framedSingleEigenvalue (d : ℕ) (_ : Fin d) : ℝ := (d : ℝ)⁻¹

def framedSingleEntropy (d : ℕ) : ℝ :=
  finiteSpectralEntropy (framedSingleEigenvalue d)

def framedFullPureEntropy (_d : ℕ) : ℝ := 0

def framedUniformEntropy (d : ℕ) : ℝ :=
  -(d : ℝ) * ((d : ℝ)⁻¹ * Real.log (d : ℝ)⁻¹)

theorem framedBoundaryEntropy_eq_uniformEntropy (d : ℕ) :
    framedBoundaryEntropy d = framedUniformEntropy d := by
  rw [framedBoundaryEntropy, finiteSpectralEntropy, framedUniformEntropy]
  simp_rw [Fintype.sum_prod_type]
  have hinner (i : Fin d) :
      (∑ j : Fin d, framedBoundaryEigenvalue d (i, j) *
        Real.log (framedBoundaryEigenvalue d (i, j))) =
        (d : ℝ)⁻¹ * Real.log (d : ℝ)⁻¹ := by
    rw [Finset.sum_eq_single i]
    · simp [framedBoundaryEigenvalue]
    · intro j _ hji
      simp [framedBoundaryEigenvalue, Ne.symm hji]
    · simp
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  simp only [neg_mul]

theorem framedSingleEntropy_eq_uniformEntropy (d : ℕ) :
    framedSingleEntropy d = framedUniformEntropy d := by
  rw [framedSingleEntropy, finiteSpectralEntropy, framedUniformEntropy]
  simp only [framedSingleEigenvalue, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  ring

theorem framedUniformEntropy_eq_log
    {d : ℕ} (hd : 0 < d) : framedUniformEntropy d = Real.log d := by
  rw [framedUniformEntropy, Real.log_inv]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR]

theorem framedBoundaryEntropy_eq_log
    {d : ℕ} (hd : 0 < d) : framedBoundaryEntropy d = Real.log d := by
  rw [framedBoundaryEntropy_eq_uniformEntropy, framedUniformEntropy_eq_log hd]

theorem framedSingleEntropy_eq_log
    {d : ℕ} (hd : 0 < d) : framedSingleEntropy d = Real.log d := by
  rw [framedSingleEntropy_eq_uniformEntropy, framedUniformEntropy_eq_log hd]

def framedConditionalMutualInformation (d : ℕ) : ℝ :=
  framedBoundaryEntropy d + framedBoundaryEntropy d - framedSingleEntropy d -
    framedFullPureEntropy d

theorem framedConditionalMutualInformation_eq_log
    {d : ℕ} (hd : 0 < d) :
    framedConditionalMutualInformation d = Real.log d := by
  rw [framedConditionalMutualInformation, framedBoundaryEntropy_eq_log hd,
    framedSingleEntropy_eq_log hd, framedFullPureEntropy]
  ring

structure FramedClassicalRecovery (d : ℕ) where
  probability : Fin d → Fin d → ℝ
  probability_nonneg : ∀ j k, 0 ≤ probability j k
  probability_sum_one : ∀ j, ∑ k, probability j k = 1

def framedRecoveryEntanglementFidelity {d : ℕ}
    (recovery : FramedClassicalRecovery d) : ℝ :=
  (d : ℝ)⁻¹ ^ 2 * ∑ j, recovery.probability j j

def framedLabelRecovery {d : ℕ} : FramedClassicalRecovery d where
  probability j k := if j = k then 1 else 0
  probability_nonneg := by intro j k; split_ifs <;> positivity
  probability_sum_one := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Ne.symm hkj]
    · simp

theorem framedRecoveryEntanglementFidelity_le
    {d : ℕ} (hd : 0 < d) (recovery : FramedClassicalRecovery d) :
    framedRecoveryEntanglementFidelity recovery ≤ (d : ℝ)⁻¹ := by
  have hdiag (j : Fin d) : recovery.probability j j ≤ 1 := by
    calc
      recovery.probability j j ≤ ∑ k, recovery.probability j k := by
        exact Finset.single_le_sum (fun k _ => recovery.probability_nonneg j k)
          (Finset.mem_univ j)
      _ = 1 := recovery.probability_sum_one j
  rw [framedRecoveryEntanglementFidelity]
  calc
    (d : ℝ)⁻¹ ^ 2 * ∑ j, recovery.probability j j ≤
        (d : ℝ)⁻¹ ^ 2 * ∑ _j : Fin d, (1 : ℝ) := by
      gcongr with j
      exact hdiag j
    _ = (d : ℝ)⁻¹ := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp [hdR]

theorem framedLabelRecovery_fidelity
    {d : ℕ} (hd : 0 < d) :
    framedRecoveryEntanglementFidelity (framedLabelRecovery (d := d)) =
      (d : ℝ)⁻¹ := by
  rw [framedRecoveryEntanglementFidelity]
  simp only [framedLabelRecovery, ↓reduceIte]
  rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR]

def framedOptimalRecoveryFidelity (d : ℕ) : ℝ :=
  sSup (Set.range (framedRecoveryEntanglementFidelity (d := d)))

theorem framedRecoveryFidelity_isGreatest
    {d : ℕ} (hd : 0 < d) :
    IsGreatest (Set.range (framedRecoveryEntanglementFidelity (d := d)))
      (d : ℝ)⁻¹ := by
  constructor
  · exact ⟨framedLabelRecovery,
      framedLabelRecovery_fidelity hd⟩
  · rintro _ ⟨recovery, rfl⟩
    exact framedRecoveryEntanglementFidelity_le hd recovery

theorem framedOptimalRecoveryFidelity_eq
    {d : ℕ} (hd : 0 < d) :
    framedOptimalRecoveryFidelity d = (d : ℝ)⁻¹ := by
  exact (framedRecoveryFidelity_isGreatest hd).csSup_eq

inductive FramedLostShare
  | left
  | right

def framedShareOptimalRecoveryFidelity (d : ℕ) (_share : FramedLostShare) : ℝ :=
  framedOptimalRecoveryFidelity d

theorem framedShareOptimalRecoveryFidelity_eq
    {d : ℕ} (hd : 0 < d) (share : FramedLostShare) :
    framedShareOptimalRecoveryFidelity d share = (d : ℝ)⁻¹ := by
  rw [framedShareOptimalRecoveryFidelity, framedOptimalRecoveryFidelity_eq hd]

theorem exp_neg_framedConditionalMutualInformation
    {d : ℕ} (hd : 0 < d) :
    Real.exp (-framedConditionalMutualInformation d) = (d : ℝ)⁻¹ := by
  rw [framedConditionalMutualInformation_eq_log hd, Real.exp_neg]
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [Real.exp_log hdR]

theorem framedRadialQECInvariant
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    (finiteMatrixTraceSquare (framedCoherenceDefect d x)).re =
        1 - (d : ℝ)⁻¹ ∧
      (∀ share : FramedLostShare,
        1 - framedShareOptimalRecoveryFidelity d share = 1 - (d : ℝ)⁻¹) ∧
      1 - Real.exp (-framedConditionalMutualInformation d) = 1 - (d : ℝ)⁻¹ := by
  constructor
  · rw [traceSquare_framedCoherenceDefect hd]
    norm_num
  constructor
  · intro share
    rw [framedShareOptimalRecoveryFidelity_eq hd]
  · rw [exp_neg_framedConditionalMutualInformation hd]

/-! ## Remaining proper marginals and exact phase-fibre chart -/

def framedPartialTraceR (d : ℕ)
    (rho : EuclideanSpace ℂ (FramedTripartiteIndex d × FramedTripartiteIndex d)) :
    EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  WithLp.toLp 2 fun pq =>
    ∑ r : Fin d,
      rho ((r, (pq.1.1, pq.1.2)), (r, (pq.2.1, pq.2.2)))

theorem framedPartialTraceR_framedGHZDensity
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) :
    framedPartialTraceR d (framedGHZDensity d x) = framedBoundaryDensity d := by
  ext pq
  simp only [framedPartialTraceR, framedGHZDensity, RHTower.pureStateDensity_apply,
    framedGHZVector_apply, framedBoundaryDensity]
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd
  by_cases h1 : pq.1.1 = pq.1.2 <;>
    by_cases h2 : pq.2.1 = pq.2.2 <;>
    by_cases h3 : pq.1.1 = pq.2.1 <;>
    simp_all [eq_comm, framedGHZ_coefficient_density_circle hd]
  all_goals
    symm
    apply Finset.sum_eq_zero
    intro r _
    simp_all
    intro _ hb
    exact h1 hb.symm

def framedSingleDensity (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij => if ij.1 = ij.2 then ((d : ℝ)⁻¹ : ℂ) else 0

def framedTraceReferenceBoundary (d : ℕ)
    (rho : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij => ∑ r : Fin d, rho ((r, ij.1), (r, ij.2))

theorem framedTraceReferenceBoundary_framedBoundaryDensity
    {d : ℕ} :
    framedTraceReferenceBoundary d (framedBoundaryDensity d) = framedSingleDensity d := by
  ext ij
  simp only [framedTraceReferenceBoundary, framedBoundaryDensity, framedSingleDensity]
  by_cases hij : ij.1 = ij.2
  · rw [if_pos hij]
    rw [Finset.sum_eq_single ij.1]
    · simp [hij]
    · intro r _ hri
      rw [if_neg]
      intro h
      exact hri h.1
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro r _
    rw [if_neg]
    intro h
    exact hij (h.1.symm.trans h.2.1)

theorem framedSingleDensity_spectralDiagonal
    {d : ℕ} (i j : Fin d) :
    framedSingleDensity d (i, j) =
      if i = j then (framedSingleEigenvalue d i : ℂ) else 0 := by
  simp [framedSingleDensity, framedSingleEigenvalue]

theorem framedGHZDensity_eq_support_uniformPhaseDensity
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle)
    (pq : FramedTripartiteIndex d × FramedTripartiteIndex d) :
    framedGHZDensity d x pq =
      if framedDiagonalSupport pq.1 ∧ framedDiagonalSupport pq.2 then
        RHTower.uniformPhaseDensity d x (pq.1.1, pq.2.1)
      else 0 := by
  rw [framedGHZDensity_apply hd, RHTower.uniformPhaseDensity_apply]

theorem framedGHZDensity_add_common
    {d : ℕ} (hd : 0 < d) (x : Fin d → UnitAddCircle) (a : UnitAddCircle) :
    framedGHZDensity d (fun i => x i + a) = framedGHZDensity d x := by
  ext pq
  rw [framedGHZDensity_eq_support_uniformPhaseDensity hd,
    framedGHZDensity_eq_support_uniformPhaseDensity hd,
    RHTower.uniformPhaseDensity_add_common]

def framedPhaseFibreChart (n : ℕ) (y : Fin n → UnitAddCircle) :
    Set.range (framedGHZDensity (n + 1)) :=
  ⟨framedGHZDensity (n + 1) (RHTower.zeroAnchoredPhase n y),
    ⟨RHTower.zeroAnchoredPhase n y, rfl⟩⟩

theorem framedPhaseFibreChart_injective (n : ℕ) :
    Function.Injective (framedPhaseFibreChart n) := by
  intro y z hyz
  apply funext
  intro j
  have hd : 0 < n + 1 := Nat.succ_pos n
  have hmatrix := congrArg Subtype.val hyz
  let p : FramedTripartiteIndex (n + 1) × FramedTripartiteIndex (n + 1) :=
    ((j.succ, (j.succ, j.succ)),
      ((0 : Fin (n + 1)), ((0 : Fin (n + 1)), (0 : Fin (n + 1)))))
  have hentry := congrArg (fun rho : EuclideanSpace ℂ
      (FramedTripartiteIndex (n + 1) × FramedTripartiteIndex (n + 1)) => rho p) hmatrix
  change framedGHZDensity (n + 1) (RHTower.zeroAnchoredPhase n y) p =
    framedGHZDensity (n + 1) (RHTower.zeroAnchoredPhase n z) p at hentry
  rw [framedGHZDensity_apply hd, framedGHZDensity_apply hd] at hentry
  simp only [p, framedDiagonalSupport, and_self, if_true,
    RHTower.zeroAnchoredPhase, Fin.cases_zero, Fin.cases_succ] at hentry
  have hcoef : (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero (by positivity : (n + 1 : ℝ) ≠ 0)
  have hfourier : fourier 1 (y j) = fourier 1 (z j) := by
    apply mul_left_cancel₀ hcoef
    simpa [fourier_one] using hentry
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  simpa only [fourier_one] using hfourier

theorem framedPhaseFibreChart_surjective (n : ℕ) :
    Function.Surjective (framedPhaseFibreChart n) := by
  rintro ⟨rho, x, rfl⟩
  let split := RHTower.zeroRelativePhaseEquiv n x
  refine ⟨split.2, ?_⟩
  apply Subtype.ext
  change framedGHZDensity (n + 1) (RHTower.zeroAnchoredPhase n split.2) =
    framedGHZDensity (n + 1) x
  have hx : x = fun i => RHTower.zeroAnchoredPhase n split.2 i + split.1 := by
    calc
      x = (RHTower.zeroRelativePhaseEquiv n).symm split := by
        exact (RHTower.zeroRelativePhaseEquiv n).symm_apply_apply x |>.symm
      _ = _ := RHTower.zeroRelativePhaseEquiv_symm_eq_anchored_add n split
  rw [hx, framedGHZDensity_add_common (Nat.succ_pos n)]

noncomputable def framedPhaseFibreEquiv (n : ℕ) :
    (Fin n → UnitAddCircle) ≃ Set.range (framedGHZDensity (n + 1)) :=
  Equiv.ofBijective (framedPhaseFibreChart n)
    ⟨framedPhaseFibreChart_injective n, framedPhaseFibreChart_surjective n⟩

/-! ## Sharp action and length minima on the universal cover -/

abbrev FramedPhaseCover (d : ℕ) := EuclideanSpace ℝ (Fin d)

def framedCoverAction (d : ℕ) (T : ℝ) (path : ℝ → FramedPhaseCover d) : ℝ :=
  (1 / (2 * d)) * ∫ t in (0 : ℝ)..T, ‖deriv path t‖ ^ 2

def framedCoverLength (d : ℕ) (T : ℝ) (path : ℝ → FramedPhaseCover d) : ℝ :=
  (Real.sqrt d)⁻¹ * ∫ t in (0 : ℝ)..T, ‖deriv path t‖

structure FramedCoverHistory (d : ℕ) (T : ℝ) (delta : FramedPhaseCover d) where
  path : ℝ → FramedPhaseCover d
  continuousOn : ContinuousOn path (Set.Icc 0 T)
  differentiableOn : DifferentiableOn ℝ path (Set.Ioo 0 T)
  speedIntegrable : IntervalIntegrable (fun t => ‖deriv path t‖) volume 0 T
  energyIntegrable : IntervalIntegrable (fun t => ‖deriv path t‖ ^ 2) volume 0 T
  start_eq : path 0 = 0
  finish_eq : path T = delta

theorem framedCoverLength_lowerBound
    {d : ℕ} {T : ℝ} (hT : 0 < T) {delta : FramedPhaseCover d}
    (history : FramedCoverHistory d T delta) :
    ‖delta‖ / Real.sqrt d ≤ framedCoverLength d T history.path := by
  have hdisp := norm_sub_le_integral_of_norm_deriv_le_of_le hT.le
    history.continuousOn history.differentiableOn
    (Filter.Eventually.of_forall fun _ _ => le_rfl) history.speedIntegrable
  rw [history.finish_eq, history.start_eq, sub_zero] at hdisp
  rw [framedCoverLength, div_eq_mul_inv]
  simpa [mul_comm] using
    (mul_le_mul_of_nonneg_right hdisp
      (inv_nonneg.2 (Real.sqrt_nonneg (d : ℝ))))

theorem framedCoverAction_lowerBound
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) {delta : FramedPhaseCover d}
    (history : FramedCoverHistory d T delta) :
    ‖delta‖ ^ 2 / (2 * d * T) ≤ framedCoverAction d T history.path := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let speed : ℝ → ℝ := fun t => ‖deriv history.path t‖
  have hspeed : Integrable speed mu := history.speedIntegrable.1
  have henergy : Integrable (fun t => speed t ^ 2) mu := history.energyIntegrable.1
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioc (0 : ℝ) T) volume
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hcs := sq_integral_mul_le (μ := mu)
    hone.aestronglyMeasurable hspeed.aestronglyMeasurable
    (by simpa only [one_pow] using hone) henergy
  have hmu : mu.real Set.univ = T := by
    simp [mu, Measure.real, Real.volume_Ioc, hT.le]
  have hspeedIntegral : ∫ t, speed t ∂mu = ∫ t in (0 : ℝ)..T, speed t := by
    rw [intervalIntegral.integral_of_le hT.le]
  have henergyIntegral : ∫ t, speed t ^ 2 ∂mu =
      ∫ t in (0 : ℝ)..T, speed t ^ 2 := by
    rw [intervalIntegral.integral_of_le hT.le]
  simp only [one_mul, one_pow] at hcs
  rw [MeasureTheory.integral_const, hmu, hspeedIntegral, henergyIntegral] at hcs
  simp only [smul_eq_mul, mul_one] at hcs
  have hdisp := norm_sub_le_integral_of_norm_deriv_le_of_le hT.le
    history.continuousOn history.differentiableOn
    (Filter.Eventually.of_forall fun _ _ => le_rfl) history.speedIntegrable
  rw [history.finish_eq, history.start_eq, sub_zero] at hdisp
  change ‖delta‖ ≤ ∫ t in (0 : ℝ)..T, speed t at hdisp
  have hintegral_nonneg : 0 ≤ ∫ t in (0 : ℝ)..T, speed t :=
    (norm_nonneg delta).trans hdisp
  have hsq : ‖delta‖ ^ 2 ≤
      (∫ t in (0 : ℝ)..T, speed t) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hintegral_nonneg).2 hdisp
  have hmain : ‖delta‖ ^ 2 ≤
      T * ∫ t in (0 : ℝ)..T, speed t ^ 2 := hsq.trans hcs
  rw [framedCoverAction]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hT0 : T ≠ 0 := hT.ne'
  field_simp [hdR, hT0]
  nlinarith

def framedStraightPath {d : ℕ} (T : ℝ) (delta : FramedPhaseCover d)
    (t : ℝ) : FramedPhaseCover d :=
  (t / T) • delta

theorem deriv_framedStraightPath
    {d : ℕ} {T : ℝ} (delta : FramedPhaseCover d) (t : ℝ) :
    deriv (framedStraightPath T delta) t = T⁻¹ • delta := by
  change deriv (fun y => (y / T) • delta) t = T⁻¹ • delta
  simpa only [id_eq, one_div] using
    (((hasDerivAt_id t).div_const T).smul_const delta).deriv

def framedStraightHistory
    {d : ℕ} {T : ℝ} (hT : 0 < T) (delta : FramedPhaseCover d) :
    FramedCoverHistory d T delta where
  path := framedStraightPath T delta
  continuousOn := ((continuous_id.div_const T).smul continuous_const).continuousOn
  differentiableOn := by
    intro t _
    exact ((((hasDerivAt_id t).div_const T).smul_const delta).differentiableAt).differentiableWithinAt
  speedIntegrable := by
    simp_rw [deriv_framedStraightPath]
    exact intervalIntegrable_const
  energyIntegrable := by
    simp_rw [deriv_framedStraightPath]
    exact intervalIntegrable_const
  start_eq := by simp [framedStraightPath]
  finish_eq := by
    rw [framedStraightPath, div_self hT.ne', one_smul]

theorem framedStraightPath_action
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (delta : FramedPhaseCover d) :
    framedCoverAction d T (framedStraightPath T delta) =
      ‖delta‖ ^ 2 / (2 * d * T) := by
  rw [framedCoverAction]
  simp_rw [deriv_framedStraightPath, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hT)]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR, hT.ne']

theorem framedStraightPath_length
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (delta : FramedPhaseCover d) :
    framedCoverLength d T (framedStraightPath T delta) =
      ‖delta‖ / Real.sqrt d := by
  rw [framedCoverLength]
  simp_rw [deriv_framedStraightPath, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hT)]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hT.ne']

def framedCoverActionValues (d : ℕ) (T : ℝ) (delta : FramedPhaseCover d) : Set ℝ :=
  Set.range fun history : FramedCoverHistory d T delta =>
    framedCoverAction d T history.path

def framedCoverLengthValues (d : ℕ) (T : ℝ) (delta : FramedPhaseCover d) : Set ℝ :=
  Set.range fun history : FramedCoverHistory d T delta =>
    framedCoverLength d T history.path

theorem framedCoverAction_has_exactMinimum
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (delta : FramedPhaseCover d) :
    IsLeast (framedCoverActionValues d T delta) (‖delta‖ ^ 2 / (2 * d * T)) := by
  constructor
  · exact ⟨framedStraightHistory hT delta, framedStraightPath_action hd hT delta⟩
  · rintro _ ⟨history, rfl⟩
    exact framedCoverAction_lowerBound hd hT history

theorem framedCoverLength_has_exactMinimum
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (delta : FramedPhaseCover d) :
    IsLeast (framedCoverLengthValues d T delta) (‖delta‖ / Real.sqrt d) := by
  constructor
  · exact ⟨framedStraightHistory hT delta, framedStraightPath_length hd hT delta⟩
  · rintro _ ⟨history, rfl⟩
    exact framedCoverLength_lowerBound hT history

def framedWindingDisplacement {d : ℕ} (m : Fin d → ℤ) : FramedPhaseCover d :=
  WithLp.toLp 2 fun j => 2 * Real.pi * framedPhaseProjection (fun k => (m k : ℝ)) j

theorem norm_framedWindingDisplacement_sq {d : ℕ} (m : Fin d → ℤ) :
    ‖framedWindingDisplacement m‖ ^ 2 =
      4 * Real.pi ^ 2 * framedWindingProjectedNormSq m := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin d,
    ‖2 * Real.pi * framedPhaseProjection (fun k => (m k : ℝ)) j‖ ^ 2) = _
  simp only [Real.norm_eq_abs, sq_abs, mul_pow]
  rw [← Finset.mul_sum]
  rw [framedWindingProjectedNormSq, framedPhaseNormSq]
  ring

theorem framedWindingAction_has_exactMinimum
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (m : Fin d → ℤ) :
    IsLeast (framedCoverActionValues d T (framedWindingDisplacement m))
      (framedWindingMinimumAction T m) := by
  have hmin := framedCoverAction_has_exactMinimum hd hT (framedWindingDisplacement m)
  rw [norm_framedWindingDisplacement_sq] at hmin
  convert hmin using 1
  simp only [framedWindingMinimumAction]
  field_simp
  ring

theorem framedWindingLength_has_exactMinimum
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (m : Fin d → ℤ) :
    IsLeast (framedCoverLengthValues d T (framedWindingDisplacement m))
      (framedWindingMinimumLength m) := by
  have hmin := framedCoverLength_has_exactMinimum hd hT (framedWindingDisplacement m)
  have hnormsq : 0 ≤ framedWindingProjectedNormSq m := by
    rw [framedWindingProjectedNormSq, framedPhaseNormSq]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : ‖framedWindingDisplacement m‖ =
      2 * Real.pi * Real.sqrt (framedWindingProjectedNormSq m) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
    calc
      ‖framedWindingDisplacement m‖ ^ 2 =
          4 * Real.pi ^ 2 * framedWindingProjectedNormSq m :=
        norm_framedWindingDisplacement_sq m
      _ = (2 * Real.pi * Real.sqrt (framedWindingProjectedNormSq m)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnormsq]
        ring
  rw [hnorm] at hmin
  convert hmin using 1
  simp only [framedWindingMinimumLength, div_eq_mul_inv]
  ring

def framedEndpointLiftDisplacement {d : ℕ}
    (delta : Fin d → ℝ) (n : Fin d → ℤ) : FramedPhaseCover d :=
  WithLp.toLp 2 fun j =>
    framedPhaseProjection (fun k => delta k + 2 * Real.pi * (n k : ℝ)) j

def framedEndpointLiftNormSq {d : ℕ}
    (delta : Fin d → ℝ) (n : Fin d → ℤ) : ℝ :=
  ‖framedEndpointLiftDisplacement delta n‖ ^ 2

theorem framedEndpointLiftNormSq_eq_projected
    {d : ℕ} (delta : Fin d → ℝ) (n : Fin d → ℤ) :
    framedEndpointLiftNormSq delta n =
      framedPhaseNormSq (fun k => delta k + 2 * Real.pi * (n k : ℝ)) := by
  rw [framedEndpointLiftNormSq, EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin d,
    ‖framedPhaseProjection (fun k => delta k + 2 * Real.pi * (n k : ℝ)) j‖ ^ 2) = _
  simp only [Real.norm_eq_abs, sq_abs, framedPhaseNormSq]

def framedNormalizeWinding {d : ℕ} (anchor : Fin d) (n : Fin d → ℤ) : Fin d → ℤ :=
  fun j => n j - n anchor

theorem framedPhaseProjection_add_const
    {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) (c : ℝ) :
    framedPhaseProjection (fun j => v j + c) = framedPhaseProjection v := by
  funext j
  have hsum : (∑ i : Fin d, (v i + c)) = (∑ i, v i) + d * c := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [framedPhaseProjection, framedPhaseProjection, framedPhaseMean, framedPhaseMean, hsum]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp [hdR]
  ring

theorem framedEndpointLiftNormSq_normalize
    {d : ℕ} (hd : 0 < d) (anchor : Fin d) (delta : Fin d → ℝ) (n : Fin d → ℤ) :
    framedEndpointLiftNormSq delta (framedNormalizeWinding anchor n) =
      framedEndpointLiftNormSq delta n := by
  rw [framedEndpointLiftNormSq_eq_projected, framedEndpointLiftNormSq_eq_projected]
  have hfun : (fun k => delta k + 2 * Real.pi * (framedNormalizeWinding anchor n k : ℝ)) =
      fun k => (delta k + 2 * Real.pi * (n k : ℝ)) +
        (-2 * Real.pi * (n anchor : ℝ)) := by
    funext k
    rw [framedNormalizeWinding, Int.cast_sub]
    ring
  rw [hfun, framedPhaseNormSq]
  rw [framedPhaseProjection_add_const hd]
  rfl

theorem framedNormalizeWinding_anchor
    {d : ℕ} (anchor : Fin d) (n : Fin d → ℤ) :
    framedNormalizeWinding anchor n anchor = 0 := by
  simp [framedNormalizeWinding]

theorem framedEndpointLiftNormSq_exists_global_minimizer
    {d : ℕ} (hd : 0 < d) (delta : Fin d → ℝ) :
    ∃ n : Fin d → ℤ, ∀ m : Fin d → ℤ,
      framedEndpointLiftNormSq delta n ≤ framedEndpointLiftNormSq delta m := by
  let anchor : Fin d := ⟨0, hd⟩
  let zeroWinding : Fin d → ℤ := fun _ => 0
  let C : ℝ := framedEndpointLiftNormSq delta zeroWinding
  have hC : 0 ≤ C := sq_nonneg _
  let B : ℝ := 2 * Real.sqrt C + ∑ j : Fin d, |delta j - delta anchor|
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  obtain ⟨R, hR⟩ := exists_nat_gt (B / (2 * Real.pi))
  let S : Set (Fin d → ℤ) :=
    {n | n anchor = 0 ∧ framedEndpointLiftNormSq delta n ≤ C}
  have hcoord (n : Fin d → ℤ) (hn : n ∈ S) (j : Fin d) :
      -(R : ℤ) ≤ n j ∧ n j ≤ (R : ℤ) := by
    have hna : n anchor = 0 := hn.1
    have hcost : framedEndpointLiftNormSq delta n ≤ C := hn.2
    let v : Fin d → ℝ := fun k => delta k + 2 * Real.pi * (n k : ℝ)
    let u : Fin d → ℝ := framedPhaseProjection v
    have hcostsum : framedEndpointLiftNormSq delta n = ∑ k, u k ^ 2 := by
      rw [framedEndpointLiftNormSq_eq_projected, framedPhaseNormSq]
    have hu_sq (k : Fin d) : u k ^ 2 ≤ C := by
      calc
        u k ^ 2 ≤ ∑ l, u l ^ 2 :=
          Finset.single_le_sum (fun l _ => sq_nonneg (u l)) (Finset.mem_univ k)
        _ = framedEndpointLiftNormSq delta n := hcostsum.symm
        _ ≤ C := hcost
    have hu_abs (k : Fin d) : |u k| ≤ Real.sqrt C := by
      have hsqrt : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
      apply (sq_le_sq₀ (abs_nonneg _) hsqrt).mp
      rw [sq_abs, Real.sq_sqrt hC]
      exact hu_sq k
    have huv : u j - u anchor = v j - v anchor := by
      simp only [u, framedPhaseProjection]
      ring
    have hidentity : 2 * Real.pi * (n j : ℝ) =
        (u j - u anchor) - (delta j - delta anchor) := by
      rw [huv]
      simp only [v, hna, Int.cast_zero, mul_zero, add_zero]
      ring
    have habs : |2 * Real.pi * (n j : ℝ)| ≤ B := by
      rw [hidentity]
      calc
        |(u j - u anchor) - (delta j - delta anchor)| ≤
            |u j - u anchor| + |delta j - delta anchor| := abs_sub _ _
        _ ≤ (|u j| + |u anchor|) + |delta j - delta anchor| := by
          gcongr
          exact abs_sub _ _
        _ ≤ 2 * Real.sqrt C + |delta j - delta anchor| := by
          nlinarith [hu_abs j, hu_abs anchor]
        _ ≤ B := by
          dsimp [B]
          gcongr
          exact Finset.single_le_sum (fun k _ => abs_nonneg (delta k - delta anchor))
            (Finset.mem_univ j)
    have hpi : 0 < 2 * Real.pi := by positivity
    have hnreal : |(n j : ℝ)| < (R : ℝ) := by
      have hdiv : |(n j : ℝ)| ≤ B / (2 * Real.pi) := by
        rw [abs_mul, abs_of_pos hpi] at habs
        exact (le_div_iff₀ hpi).2 (by simpa [mul_comm] using habs)
      exact hdiv.trans_lt hR
    have hint : |n j| ≤ (R : ℤ) := by
      exact_mod_cast (le_of_lt hnreal)
    exact abs_le.mp hint
  have hSfinite : S.Finite := by
    apply (Set.Finite.pi (fun _ : Fin d => Set.finite_Icc (-(R : ℤ)) (R : ℤ))).subset
    intro n hn
    simp only [Set.mem_pi, Set.mem_Icc]
    intro j _
    exact hcoord n hn j
  have hzeroS : zeroWinding ∈ S := by
    exact ⟨rfl, le_rfl⟩
  obtain ⟨nmin, hnminS, hnmin⟩ := Set.exists_min_image S
    (framedEndpointLiftNormSq delta) hSfinite ⟨zeroWinding, hzeroS⟩
  refine ⟨nmin, fun m => ?_⟩
  let m0 := framedNormalizeWinding anchor m
  by_cases hm : framedEndpointLiftNormSq delta m ≤ C
  · have hmS : m0 ∈ S := by
      constructor
      · exact framedNormalizeWinding_anchor anchor m
      · rw [framedEndpointLiftNormSq_normalize hd anchor delta m]
        exact hm
    calc
      framedEndpointLiftNormSq delta nmin ≤ framedEndpointLiftNormSq delta m0 :=
        hnmin m0 hmS
      _ = framedEndpointLiftNormSq delta m :=
        framedEndpointLiftNormSq_normalize hd anchor delta m
  · have hnminC : framedEndpointLiftNormSq delta nmin ≤ C := hnminS.2
    exact hnminC.trans (le_of_not_ge hm)

theorem framedEndpointLiftNormSq_sInf_attained
    {d : ℕ} (hd : 0 < d) (delta : Fin d → ℝ) :
    ∃ n : Fin d → ℤ,
      sInf (Set.range (framedEndpointLiftNormSq delta)) =
          framedEndpointLiftNormSq delta n ∧
        ∀ m : Fin d → ℤ,
          framedEndpointLiftNormSq delta n ≤ framedEndpointLiftNormSq delta m := by
  obtain ⟨n, hn⟩ := framedEndpointLiftNormSq_exists_global_minimizer hd delta
  refine ⟨n, ?_, hn⟩
  exact (show IsLeast (Set.range (framedEndpointLiftNormSq delta))
      (framedEndpointLiftNormSq delta n) from
    ⟨⟨n, rfl⟩, by rintro _ ⟨m, rfl⟩; exact hn m⟩).csInf_eq

def framedEndpointMinimumAction {d : ℕ} (T : ℝ) (delta : Fin d → ℝ) : ℝ :=
  (1 / (2 * d * T)) *
    sInf (Set.range (framedEndpointLiftNormSq delta))

theorem framedEndpointMinimumAction_formula
    {d : ℕ} (T : ℝ) (delta : Fin d → ℝ) :
    framedEndpointMinimumAction T delta =
      (1 / (2 * d * T)) * sInf
        (Set.range fun n : Fin d → ℤ =>
          framedPhaseNormSq (fun k => delta k + 2 * Real.pi * (n k : ℝ))) := by
  rw [framedEndpointMinimumAction]
  congr 1
  apply congrArg sInf
  ext value
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (framedEndpointLiftNormSq_eq_projected delta n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, framedEndpointLiftNormSq_eq_projected delta n⟩

theorem framedEndpointMinimumAction_le_liftHistory
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (delta : Fin d → ℝ) (n : Fin d → ℤ)
    (history : FramedCoverHistory d T (framedEndpointLiftDisplacement delta n)) :
    framedEndpointMinimumAction T delta ≤ framedCoverAction d T history.path := by
  have hbdd : BddBelow (Set.range (framedEndpointLiftNormSq delta)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact sq_nonneg _
  have hinf : sInf (Set.range (framedEndpointLiftNormSq delta)) ≤
      framedEndpointLiftNormSq delta n :=
    csInf_le hbdd ⟨n, rfl⟩
  have hcoef : 0 ≤ (1 / (2 * (d : ℝ) * T)) := by positivity
  calc
    framedEndpointMinimumAction T delta ≤
        (1 / (2 * d * T)) * framedEndpointLiftNormSq delta n := by
      rw [framedEndpointMinimumAction]
      exact mul_le_mul_of_nonneg_left hinf hcoef
    _ = ‖framedEndpointLiftDisplacement delta n‖ ^ 2 / (2 * d * T) := by
      rw [framedEndpointLiftNormSq]
      ring
    _ ≤ _ := framedCoverAction_lowerBound hd hT history

def framedEndpointActionValues
    (d : ℕ) (T : ℝ) (delta : Fin d → ℝ) : Set ℝ :=
  {action | ∃ n : Fin d → ℤ,
    ∃ history : FramedCoverHistory d T (framedEndpointLiftDisplacement delta n),
      action = framedCoverAction d T history.path}

theorem framedEndpointAction_has_exactMinimum
    {d : ℕ} (hd : 0 < d) {T : ℝ} (hT : 0 < T) (delta : Fin d → ℝ) :
    IsLeast (framedEndpointActionValues d T delta)
      (framedEndpointMinimumAction T delta) := by
  obtain ⟨n, hninf, _⟩ := framedEndpointLiftNormSq_sInf_attained hd delta
  have hvalue : framedEndpointMinimumAction T delta =
      ‖framedEndpointLiftDisplacement delta n‖ ^ 2 / (2 * d * T) := by
    rw [framedEndpointMinimumAction, hninf, framedEndpointLiftNormSq]
    ring
  constructor
  · refine ⟨n, framedStraightHistory hT (framedEndpointLiftDisplacement delta n), ?_⟩
    exact hvalue.trans (framedStraightPath_action hd hT _).symm
  · rintro _ ⟨m, history, rfl⟩
    exact framedEndpointMinimumAction_le_liftHistory hd hT delta m history

theorem twoLevel_naturalPeriods_collision
    {omega : ℝ} (homega : omega ≠ 0) (n : ℕ) :
    twoLevelKrylovComplexity omega (2 * Real.pi * n / |omega|) = 0 ∧
      twoLevelExecutedFubiniStudyLength omega (2 * Real.pi * n / |omega|) =
        n * Real.pi := by
  have habs : |omega| ≠ 0 := abs_ne_zero.mpr homega
  constructor
  · rw [twoLevelKrylovComplexity]
    rcases lt_or_gt_of_ne homega with hneg | hpos
    · have harg : omega * (2 * Real.pi * n / |omega|) / 2 =
          -((n : ℝ) * Real.pi) := by
        rw [abs_of_neg hneg]
        field_simp [homega]
      rw [harg, Real.sin_neg, Real.sin_nat_mul_pi]
      norm_num
    · have harg : omega * (2 * Real.pi * n / |omega|) / 2 =
          (n : ℝ) * Real.pi := by
        rw [abs_of_pos hpos]
        field_simp [homega]
      rw [harg, Real.sin_nat_mul_pi]
      norm_num
  · rw [twoLevelExecutedFubiniStudyLength]
    have hnonneg : 0 ≤ 2 * Real.pi * (n : ℝ) := mul_nonneg (by positivity) (Nat.cast_nonneg n)
    rw [abs_mul, abs_div, abs_abs, abs_of_nonneg hnonneg]
    field_simp [habs]

theorem twoLevel_zeroComplexity_historyLength_unbounded
    {omega : ℝ} (homega : omega ≠ 0) (M : ℝ) :
    ∃ t : ℝ, M < twoLevelExecutedFubiniStudyLength omega t ∧
      twoLevelKrylovComplexity omega t = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (M / Real.pi)
  refine ⟨2 * Real.pi * n / |omega|, ?_,
    (twoLevel_naturalPeriods_collision homega n).1⟩
  rw [(twoLevel_naturalPeriods_collision homega n).2]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_lt_iff₀ hpi] at hn
  simpa [mul_comm] using hn

theorem framedBoundaryRadialBerryData_do_not_determine_windingAction
    {T : ℝ} (hT : 0 < T) :
    framedBerryHolonomy zeroWindingTwo = framedBerryHolonomy oppositeWindingTwo ∧
      framedWindingMinimumAction T zeroWindingTwo = 0 ∧
      0 < framedWindingMinimumAction T oppositeWindingTwo := by
  refine ⟨berryHolonomy_does_not_determine_windingAction.1, ?_, ?_⟩
  · rw [framedWindingMinimumAction,
      berryHolonomy_does_not_determine_windingAction.2.1, mul_zero]
  · rw [framedWindingMinimumAction,
      berryHolonomy_does_not_determine_windingAction.2.2]
    positivity

structure FramedHistorySeparationWitness where
  radialQECDefect : ℝ
  phaseTangentMetric : (Fin 2 → ℝ) → ℝ
  windingHistory : Fin 2 → ℤ
  berryQuotient : ℂ

def zeroFramedHistoryWitness : FramedHistorySeparationWitness where
  radialQECDefect := 1 / 2
  phaseTangentMetric := framedFubiniStudyMetric
  windingHistory := zeroWindingTwo
  berryQuotient := framedBerryHolonomy zeroWindingTwo

def oppositeFramedHistoryWitness : FramedHistorySeparationWitness where
  radialQECDefect := 1 / 2
  phaseTangentMetric := framedFubiniStudyMetric
  windingHistory := oppositeWindingTwo
  berryQuotient := framedBerryHolonomy oppositeWindingTwo

theorem framedHistory_typedSeparation :
    zeroFramedHistoryWitness.radialQECDefect =
        oppositeFramedHistoryWitness.radialQECDefect ∧
      zeroFramedHistoryWitness.phaseTangentMetric =
        oppositeFramedHistoryWitness.phaseTangentMetric ∧
      zeroFramedHistoryWitness.berryQuotient =
        oppositeFramedHistoryWitness.berryQuotient ∧
      zeroFramedHistoryWitness.windingHistory ≠
        oppositeFramedHistoryWitness.windingHistory := by
  refine ⟨rfl, rfl, berryHolonomy_does_not_determine_windingAction.1, ?_⟩
  intro h
  have h0 := congrFun h 0
  norm_num [zeroFramedHistoryWitness, oppositeFramedHistoryWitness,
    zeroWindingTwo, oppositeWindingTwo] at h0

end
end GaloisForLFunctions.HTGeometry
