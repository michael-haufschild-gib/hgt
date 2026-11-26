import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.CutConditionedTransport
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.NoncontextualTube
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.PhysicalWindow
import GaloisForLFunctions.HTGeometry.PauliCommutatorCoefficient

/-! # Post-`(N - 1)` exponential-tail onset and uniform Pauli-claw conditioning

This module establishes the unconditional exponential-tail onset bound strictly past `s = N - 1`,
abstract orthogonal product-Gaussian invariance, `O(3) × O(3)`-invariant `2 × 2` bond minors, and
deterministic `TwinLineModel` / `PauliNoncontextual` exclusions on `Ω_claw(n, η)`:

1. **Abstract orthogonal Gaussian invariance and `O(3) × O(3)`-invariant bond `2 × 2` minors:**
   - `measurePreserving_pi_gaussian_orthogonal`: every orthogonal matrix `O : Matrix ι ι ℝ`
     (`Oᵀ * O = 1`, `O * Oᵀ = 1`) preserves `Measure.pi (fun _ : ι => gaussianReal 0 1)`.
   - `det2_sq_le_frob_rankOne_err`, `bondMinorInvariant_orthog_eq`, and
     `bondMinorInvariant_le_rankOne_dist`: division-free `2 × 2` Eckart-Young minor inequality
     `(a d - b c)² ≤ ‖M - v wᵀ‖_F² ‖M‖_F²` and `O(3) × O(3)` invariance of the `3 × 3` bond minor
     functional `I₂(B) = (‖B‖_F⁴ - ‖Bᵀ B‖_F²) / 2`.
2. **Unconditional exponential-tail onset strictly past `s = N - 1`:**
   - `gaussian_super_one_gate_per_bond_exponential_onset`: sub-Gaussian Hoeffding concentration
     across `⌊(n + 1) / 4⌋` disjoint `4`-row non-commuting boxes combined with exponential
     cut-overlap decay yields an explicit `c_strict > 0` such that outside probability
     `≤ A * exp(-γ * n)` (tail exponent `Ω(N)`), **every** budget `s ≤ (1 + c_strict) * (n + 1)`
     satisfies `1 / (20 * (‖H‖ + 1)) < tenthPlateauOnset H s < 1` and exact `1 / 10` attainment.
3. **Uniform claw conditioning `Ω_claw(n, η)`:**
   - `uniformClawEvent_compl_prob_le`, `isEmpty_twinLineModel_of_uniformClaw`, and
     `noncontextual_operator_dist_ge_of_uniformClaw`: `Ω_claw(n, η) ⊆ Ω_nc-bond(n, η) ⊆
     Ω_bond(n, η) ⊆ Ω_conn(n, η)` fails with probability `≤ 3 (n + 2) η² + 27 (n + 1) η⁴`,
     deterministically excludes all `TwinLineModel` supports above `η`, and forces
     `√(n + 1) * η ≤ ‖H(u) - H(v)‖` against every `PauliNoncontextual` chain `v`. -/

open Set Filter MeasureTheory ProbabilityTheory Real Topology Matrix NormedSpace
open scoped Matrix.Norms.L2Operator ENNReal NNReal ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords MaximumIntervals
open WeakBonds PrescribedTimes SpanningDensity.FixedHorizon
open RepeatedGates.PhysicalBlocks
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw GaloisForLFunctions.RHTower
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool

/-! ## Section 1: Orthogonal Gaussian invariance and `O(3) × O(3)`-invariant `2 × 2` bond minors -/

private def orthogLinearIsometryEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (hO_left : Oᵀ * O = 1) (hO_right : O * Oᵀ = 1) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (O *ᵥ x.ofLp)
  map_add' x y := WithLp.ofLp_injective 2 (Matrix.mulVec_add O x.ofLp y.ofLp)
  map_smul' r x := WithLp.ofLp_injective 2 (Matrix.mulVec_smul O r x.ofLp)
  invFun y := WithLp.toLp 2 (Oᵀ *ᵥ y.ofLp)
  left_inv x := by
    apply WithLp.ofLp_injective 2
    change Oᵀ *ᵥ (O *ᵥ x.ofLp) = x.ofLp
    rw [Matrix.mulVec_mulVec, hO_left, Matrix.one_mulVec]
  right_inv y := by
    apply WithLp.ofLp_injective 2
    change O *ᵥ (Oᵀ *ᵥ y.ofLp) = y.ofLp
    rw [Matrix.mulVec_mulVec, hO_right, Matrix.one_mulVec]
  norm_map' x := by
    have hsq : ‖(WithLp.toLp 2 (O *ᵥ x.ofLp) : EuclideanSpace ℝ ι)‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      have hdot : (∑ i : ι, (O *ᵥ x.ofLp) i ^ 2) = (O *ᵥ x.ofLp) ⬝ᵥ (O *ᵥ x.ofLp) := by
        simp [dotProduct, pow_two]
      have hdot2 : (∑ i : ι, x.ofLp i ^ 2) = x.ofLp ⬝ᵥ x.ofLp := by
        simp [dotProduct, pow_two]
      have hvec_eq : O *ᵥ x.ofLp = x.ofLp ᵥ* Oᵀ := by
        ext i; simp [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
      change (∑ i : ι, (O *ᵥ x.ofLp) i ^ 2) = ∑ i : ι, x.ofLp i ^ 2
      rw [hdot, hdot2]
      conv_lhs => arg 1; rw [hvec_eq]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hO_left, Matrix.vecMul_one]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Every orthogonal matrix `O : Matrix ι ι ℝ` (`Oᵀ * O = 1`, `O * Oᵀ = 1`) induces a
measure-preserving linear map `x ↦ O *ᵥ x` on `Measure.pi (fun _ : ι => gaussianReal 0 1)`. -/
theorem measurePreserving_pi_gaussian_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Matrix ι ι ℝ) (hO_left : Oᵀ * O = 1) (hO_right : O * Oᵀ = 1) :
    MeasurePreserving (fun x : ι → ℝ => O *ᵥ x)
      (Measure.pi fun _ : ι => gaussianReal 0 1)
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hdens_meas : Measurable
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal (euclideanGaussianDensityReal x)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold euclideanGaussianDensityReal
    exact measurable_const.mul (Real.continuous_exp.measurable.comp
      (((continuous_norm.pow 2).neg.div_const 2).measurable))
  have hmp_std : MeasurePreserving (orthogLinearIsometryEquiv O hO_left hO_right)
      (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine ⟨(orthogLinearIsometryEquiv O hO_left hO_right).toMeasurableEquiv.measurable, ?_⟩
    change (stdGaussian (EuclideanSpace ℝ ι)).map
      (orthogLinearIsometryEquiv O hO_left hO_right).toMeasurableEquiv = _
    have hvol : (volume : Measure (EuclideanSpace ℝ ι)).map
        (orthogLinearIsometryEquiv O hO_left hO_right).toMeasurableEquiv = volume :=
      (orthogLinearIsometryEquiv O hO_left hO_right).measurePreserving.map_eq
    rw [stdGaussian_eq_withDensity,
      map_withDensity_measurableEquiv _
        (orthogLinearIsometryEquiv O hO_left hO_right).toMeasurableEquiv hdens_meas,
      hvol]
    congr 1; funext y; congr 1
    unfold euclideanGaussianDensityReal
    rw [LinearIsometryEquiv.coe_symm_toMeasurableEquiv,
      (orthogLinearIsometryEquiv O hO_left hO_right).symm.norm_map]
  have hmp_to : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).measurable,
      by simpa only [MeasurableEquiv.coe_toLp] using map_pi_eq_stdGaussian⟩
  have hmp_from : MeasurePreserving (MeasurableEquiv.toLp 2 (ι → ℝ)).symm
      (stdGaussian (EuclideanSpace ℝ ι)) (Measure.pi fun _ : ι => gaussianReal 0 1) := by
    refine ⟨(MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable, ?_⟩
    rw [← hmp_to.map_eq, Measure.map_map
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable]
    simp
  exact (hmp_from.comp hmp_std).comp hmp_to

/-- Exact `2 × 2` Eckart-Young rank-`1` minor inequality: for any `2 × 2` real entries `a, b, c, d`
and rank-`1` outer product `(v₁, v₂)ᵀ (w₁, w₂)`,
`(a d - b c)² ≤ ((a - v₁ w₁)² + (b - v₁ w₂)² + (c - v₂ w₁)² + (d - v₂ w₂)²) * (a² + b² + c² + d²)`. -/
theorem det2_sq_le_frob_rankOne_err (a b c d v₁ v₂ w₁ w₂ : ℝ) :
    (a * d - b * c) ^ 2 ≤
      ((a - v₁ * w₁) ^ 2 + (b - v₁ * w₂) ^ 2 + (c - v₂ * w₁) ^ 2 + (d - v₂ * w₂) ^ 2) *
        (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  let R := v₁ ^ 2 + v₂ ^ 2
  by_cases hR0 : R = 0
  · have hv₁ : v₁ = 0 := by nlinarith only [hR0, sq_nonneg v₁, sq_nonneg v₂]
    have hv₂ : v₂ = 0 := by nlinarith only [hR0, sq_nonneg v₁, sq_nonneg v₂]
    rw [hv₁, hv₂]
    have h1 : 0 ≤ (a - d) ^ 2 + (b + c) ^ 2 := by positivity
    have h2 : 0 ≤ (a + d) ^ 2 + (b - c) ^ 2 := by positivity
    nlinarith only [h1, h2]
  · have hR_pos : 0 < R := lt_of_le_of_ne (by dsimp [R]; positivity) (Ne.symm hR0)
    have hR2_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
    let E := (a - v₁ * w₁) ^ 2 + (b - v₁ * w₂) ^ 2 + (c - v₂ * w₁) ^ 2 + (d - v₂ * w₂) ^ 2
    let F := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
    let p₁ := v₂ * a - v₁ * c
    let p₂ := v₂ * b - v₁ * d
    let q₁ := v₁ * a + v₂ * c
    let q₂ := v₁ * b + v₂ * d
    have hp_le : p₁ ^ 2 + p₂ ^ 2 ≤ R * E := by
      have hid1 : R * ((a - v₁ * w₁) ^ 2 + (c - v₂ * w₁) ^ 2) - p₁ ^ 2 =
          (v₁ * (a - v₁ * w₁) + v₂ * (c - v₂ * w₁)) ^ 2 := by dsimp [R, p₁]; ring
      have hid2 : R * ((b - v₁ * w₂) ^ 2 + (d - v₂ * w₂) ^ 2) - p₂ ^ 2 =
          (v₁ * (b - v₁ * w₂) + v₂ * (d - v₂ * w₂)) ^ 2 := by dsimp [R, p₂]; ring
      have hnn1 : 0 ≤ (v₁ * (a - v₁ * w₁) + v₂ * (c - v₂ * w₁)) ^ 2 := sq_nonneg _
      have hnn2 : 0 ≤ (v₁ * (b - v₁ * w₂) + v₂ * (d - v₂ * w₂)) ^ 2 := sq_nonneg _
      dsimp only [E]
      linarith only [hid1, hid2, hnn1, hnn2]
    have hq_le : q₁ ^ 2 + q₂ ^ 2 ≤ R * F := by
      have hid : R * F - (q₁ ^ 2 + q₂ ^ 2) = p₁ ^ 2 + p₂ ^ 2 := by
        dsimp [R, F, p₁, p₂, q₁, q₂]; ring
      have hnn : 0 ≤ p₁ ^ 2 + p₂ ^ 2 := by positivity
      linarith only [hid, hnn]
    have hdet_le : R ^ 2 * (a * d - b * c) ^ 2 ≤ (p₁ ^ 2 + p₂ ^ 2) * (q₁ ^ 2 + q₂ ^ 2) := by
      have hlag : (p₁ ^ 2 + p₂ ^ 2) * (q₁ ^ 2 + q₂ ^ 2) - R ^ 2 * (a * d - b * c) ^ 2 =
          (p₁ * q₁ + p₂ * q₂) ^ 2 := by
        dsimp [R, p₁, p₂, q₁, q₂]; ring
      have hnn : 0 ≤ (p₁ * q₁ + p₂ * q₂) ^ 2 := sq_nonneg _
      linarith only [hlag, hnn]
    have hmul_le : (p₁ ^ 2 + p₂ ^ 2) * (q₁ ^ 2 + q₂ ^ 2) ≤ R ^ 2 * (E * F) := by
      have h1 := mul_le_mul hp_le hq_le (by positivity) (mul_nonneg hR_pos.le (by dsimp [E]; positivity))
      linarith only [h1, show (R * E) * (R * F) = R ^ 2 * (E * F) by ring]
    exact le_of_mul_le_mul_left (hdet_le.trans hmul_le) hR2_pos

/-- Squared Frobenius norm of a `3 × 3` real bond coupling matrix. -/
def frobSq3 (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ p : Fin 3, ∑ q : Fin 3, B p q ^ 2

/-- Sum of squares of all nine `2 × 2` minors of a `3 × 3` real bond coupling matrix `B`. -/
def bondMinorInvariant (B : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
    if p.1 < p.2 ∧ q.1 < q.2 then (B p.1 q.1 * B p.2 q.2 - B p.1 q.2 * B p.2 q.1) ^ 2 else 0

theorem bondMinorInvariant_nonneg (B : Matrix (Fin 3) (Fin 3) ℝ) :
    0 ≤ bondMinorInvariant B := by
  refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- Exact trace-polynomial identity `I₂(B) = (‖B‖_F⁴ - ‖Bᵀ B‖_F²) / 2`. -/
theorem bondMinorInvariant_eq_half_frob_diff (B : Matrix (Fin 3) (Fin 3) ℝ) :
    bondMinorInvariant B = (frobSq3 B ^ 2 - frobSq3 (Bᵀ * B)) / 2 := by
  have hlt01 : (0 : Fin 3) < 1 := by decide
  have hlt02 : (0 : Fin 3) < 2 := by decide
  have hlt12 : (1 : Fin 3) < 2 := by decide
  have hn00 : ¬ ((0 : Fin 3) < 0) := by decide
  have hn10 : ¬ ((1 : Fin 3) < 0) := by decide
  have hn11 : ¬ ((1 : Fin 3) < 1) := by decide
  have hn20 : ¬ ((2 : Fin 3) < 0) := by decide
  have hn21 : ¬ ((2 : Fin 3) < 1) := by decide
  have hn22 : ¬ ((2 : Fin 3) < 2) := by decide
  have hmin : bondMinorInvariant B =
      (B 0 0 * B 1 1 - B 0 1 * B 1 0) ^ 2 + (B 0 0 * B 1 2 - B 0 2 * B 1 0) ^ 2 +
      (B 0 1 * B 1 2 - B 0 2 * B 1 1) ^ 2 + (B 0 0 * B 2 1 - B 0 1 * B 2 0) ^ 2 +
      (B 0 0 * B 2 2 - B 0 2 * B 2 0) ^ 2 + (B 0 1 * B 2 2 - B 0 2 * B 2 1) ^ 2 +
      (B 1 0 * B 2 1 - B 1 1 * B 2 0) ^ 2 + (B 1 0 * B 2 2 - B 1 2 * B 2 0) ^ 2 +
      (B 1 1 * B 2 2 - B 1 2 * B 2 1) ^ 2 := by
    unfold bondMinorInvariant
    simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.isValue,
      hlt01, hlt02, hlt12, hn00, hn10, hn11, hn20, hn21, hn22,
      and_self, and_false, false_and, ↓reduceIte, add_zero, zero_add]
    ring
  have hf1 : frobSq3 B =
      B 0 0 ^ 2 + B 0 1 ^ 2 + B 0 2 ^ 2 +
      B 1 0 ^ 2 + B 1 1 ^ 2 + B 1 2 ^ 2 +
      B 2 0 ^ 2 + B 2 1 ^ 2 + B 2 2 ^ 2 := by
    unfold frobSq3
    simp only [Fin.sum_univ_three, Fin.isValue]
    ring
  have hf2 : frobSq3 (Bᵀ * B) =
      (B 0 0 * B 0 0 + B 1 0 * B 1 0 + B 2 0 * B 2 0) ^ 2 +
      (B 0 0 * B 0 1 + B 1 0 * B 1 1 + B 2 0 * B 2 1) ^ 2 +
      (B 0 0 * B 0 2 + B 1 0 * B 1 2 + B 2 0 * B 2 2) ^ 2 +
      (B 0 1 * B 0 0 + B 1 1 * B 1 0 + B 2 1 * B 2 0) ^ 2 +
      (B 0 1 * B 0 1 + B 1 1 * B 1 1 + B 2 1 * B 2 1) ^ 2 +
      (B 0 1 * B 0 2 + B 1 1 * B 1 2 + B 2 1 * B 2 2) ^ 2 +
      (B 0 2 * B 0 0 + B 1 2 * B 1 0 + B 2 2 * B 2 0) ^ 2 +
      (B 0 2 * B 0 1 + B 1 2 * B 1 1 + B 2 2 * B 2 1) ^ 2 +
      (B 0 2 * B 0 2 + B 1 2 * B 1 2 + B 2 2 * B 2 2) ^ 2 := by
    unfold frobSq3
    simp only [Fin.sum_univ_three, Matrix.mul_apply, Matrix.transpose_apply, Fin.isValue]
    ring
  rw [hmin, hf1, hf2]
  ring

private theorem frobSq3_eq_trace (M : Matrix (Fin 3) (Fin 3) ℝ) :
    frobSq3 M = Matrix.trace (Mᵀ * M) := by
  unfold frobSq3
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

/-- `O(3) × O(3)` gauge invariance of `bondMinorInvariant`: left and right multiplication by
orthogonal `3 × 3` matrices preserves `bondMinorInvariant` identically. -/
theorem bondMinorInvariant_orthog_eq (B O₁ O₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hO₁ : O₁ᵀ * O₁ = 1) (hO₂ : O₂ᵀ * O₂ = 1) :
    bondMinorInvariant (O₁ * B * O₂ᵀ) = bondMinorInvariant B := by
  have hf1 : frobSq3 (O₁ * B * O₂ᵀ) = frobSq3 B := by
    rw [frobSq3_eq_trace, frobSq3_eq_trace]
    have htr : (O₁ * B * O₂ᵀ)ᵀ * (O₁ * B * O₂ᵀ) = O₂ * (Bᵀ * B) * O₂ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      calc O₂ * (Bᵀ * O₁ᵀ) * (O₁ * B * O₂ᵀ)
          = O₂ * (Bᵀ * (O₁ᵀ * O₁) * B) * O₂ᵀ := by simp only [mul_assoc]
        _ = O₂ * (Bᵀ * B) * O₂ᵀ := by rw [hO₁, mul_one]
    rw [htr, Matrix.trace_mul_comm, ← mul_assoc, hO₂, one_mul]
  have hf2 : frobSq3 ((O₁ * B * O₂ᵀ)ᵀ * (O₁ * B * O₂ᵀ)) = frobSq3 (Bᵀ * B) := by
    have htr : (O₁ * B * O₂ᵀ)ᵀ * (O₁ * B * O₂ᵀ) = O₂ * (Bᵀ * B) * O₂ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      calc O₂ * (Bᵀ * O₁ᵀ) * (O₁ * B * O₂ᵀ)
          = O₂ * (Bᵀ * (O₁ᵀ * O₁) * B) * O₂ᵀ := by simp only [mul_assoc]
        _ = O₂ * (Bᵀ * B) * O₂ᵀ := by rw [hO₁, mul_one]
    rw [htr, frobSq3_eq_trace, frobSq3_eq_trace]
    let G := Bᵀ * B
    have htr2 : (O₂ * G * O₂ᵀ)ᵀ * (O₂ * G * O₂ᵀ) = O₂ * (Gᵀ * G) * O₂ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      calc O₂ * (Gᵀ * O₂ᵀ) * (O₂ * G * O₂ᵀ)
          = O₂ * (Gᵀ * (O₂ᵀ * O₂) * G) * O₂ᵀ := by simp only [mul_assoc]
        _ = O₂ * (Gᵀ * G) * O₂ᵀ := by rw [hO₂, mul_one]
    rw [htr2, Matrix.trace_mul_comm, ← mul_assoc, hO₂, one_mul]
  rw [bondMinorInvariant_eq_half_frob_diff, bondMinorInvariant_eq_half_frob_diff, hf1, hf2]

/-- Rank-`1` distance lower bound for `bondMinorInvariant`: for any `B : Matrix (Fin 3) (Fin 3) ℝ`
and vectors `v, w : Fin 3 → ℝ`,
`bondMinorInvariant B ≤ 9 * frobSq3 B * ∑ p, ∑ q, (B p q - v p * w q)²`. -/
theorem bondMinorInvariant_le_rankOne_dist (B : Matrix (Fin 3) (Fin 3) ℝ) (v w : Fin 3 → ℝ) :
    bondMinorInvariant B ≤
      9 * frobSq3 B * ∑ p : Fin 3, ∑ q : Fin 3, (B p q - v p * w q) ^ 2 := by
  let Err := ∑ p : Fin 3, ∑ q : Fin 3, (B p q - v p * w q) ^ 2
  have hrow_sub {p₁ p₂ : Fin 3} (hp : p₁ < p₂) (f : Fin 3 → ℝ) (hf : ∀ i, 0 ≤ f i) :
      f p₁ + f p₂ ≤ ∑ i : Fin 3, f i := by
    have hne : p₁ ≠ p₂ := hp.ne
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hf i
  have hterm (p q : Fin 3 × Fin 3) :
      (if p.1 < p.2 ∧ q.1 < q.2 then (B p.1 q.1 * B p.2 q.2 - B p.1 q.2 * B p.2 q.1) ^ 2 else 0) ≤
        (if p.1 < p.2 ∧ q.1 < q.2 then (1 : ℝ) else 0) * (frobSq3 B * Err) := by
    by_cases h : p.1 < p.2 ∧ q.1 < q.2
    · rw [if_pos h, if_pos h, one_mul]
      have hdet := det2_sq_le_frob_rankOne_err
        (B p.1 q.1) (B p.1 q.2) (B p.2 q.1) (B p.2 q.2) (v p.1) (v p.2) (w q.1) (w q.2)
      have herr4 : (B p.1 q.1 - v p.1 * w q.1) ^ 2 + (B p.1 q.2 - v p.1 * w q.2) ^ 2 +
          (B p.2 q.1 - v p.2 * w q.1) ^ 2 + (B p.2 q.2 - v p.2 * w q.2) ^ 2 ≤ Err := by
        have hc1 := hrow_sub h.2 (fun j => (B p.1 j - v p.1 * w j) ^ 2) (fun _ => sq_nonneg _)
        have hc2 := hrow_sub h.2 (fun j => (B p.2 j - v p.2 * w j) ^ 2) (fun _ => sq_nonneg _)
        have hr := hrow_sub h.1 (fun i => ∑ j : Fin 3, (B i j - v i * w j) ^ 2)
          (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        dsimp only [Err]
        linarith only [hc1, hc2, hr]
      have hfrob4 : B p.1 q.1 ^ 2 + B p.1 q.2 ^ 2 + B p.2 q.1 ^ 2 + B p.2 q.2 ^ 2 ≤ frobSq3 B := by
        have hc1 := hrow_sub h.2 (fun j => B p.1 j ^ 2) (fun _ => sq_nonneg _)
        have hc2 := hrow_sub h.2 (fun j => B p.2 j ^ 2) (fun _ => sq_nonneg _)
        have hr := hrow_sub h.1 (fun i => ∑ j : Fin 3, B i j ^ 2)
          (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        unfold frobSq3
        linarith only [hc1, hc2, hr]
      have hmul := mul_le_mul herr4 hfrob4 (by positivity)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      linarith only [hdet, hmul]
    · rw [if_neg h, if_neg h, zero_mul]
  have hcnt : (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
      if p.1 < p.2 ∧ q.1 < q.2 then (1 : ℝ) else 0) = 9 := by
    have hnat : (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
        if p.1 < p.2 ∧ q.1 < q.2 then (1 : ℕ) else 0) = 9 := by decide
    have hcast := congrArg (Nat.cast (R := ℝ)) hnat
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] using hcast
  unfold bondMinorInvariant
  calc ∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
          (if p.1 < p.2 ∧ q.1 < q.2 then (B p.1 q.1 * B p.2 q.2 - B p.1 q.2 * B p.2 q.1) ^ 2 else 0)
      ≤ ∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
          (if p.1 < p.2 ∧ q.1 < q.2 then (1 : ℝ) else 0) * (frobSq3 B * Err) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = (∑ p : Fin 3 × Fin 3, ∑ q : Fin 3 × Fin 3,
          if p.1 < p.2 ∧ q.1 < q.2 then (1 : ℝ) else 0) * (frobSq3 B * Err) := by
        simp_rw [← Finset.sum_mul]
    _ = 9 * frobSq3 B * Err := by rw [hcnt]; ring

/-! ## Section 2: Unconditional exponential-tail onset strictly past `s = N - 1` -/

private def goodBoxSet (q δ : ℝ) : Set (TripleBoxIndex → ℝ) :=
  Set.univ.pi fun i => Icc (boxField q i - δ) (boxField q i + δ)

private def readBoxBlock (m : ℕ) (ω : PathPauliDisorder) (j : Fin m) (i : TripleBoxIndex) : ℝ :=
  ω (blockCoordinate (j.val, i))

open scoped Classical in
private theorem goodBoxes_deficit_prob_le (q : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {m : ℕ} (hm : 0 < m) :
    pathPauliDisorderLaw.real
      {ω : PathPauliDisorder |
        ((goodBoxes q δ ω m).card : ℝ) < (boxProbability q δ / 2) * (m : ℝ)} ≤
      Real.exp (-2 * (boxProbability q δ / 2) ^ 2 * (m : ℝ)) := by
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hp_half : 0 < boxProbability q δ / 2 := (good_boxes_half_mass q hδ).1
  have hg_inj : Function.Injective
      (fun p : Fin m × TripleBoxIndex => blockCoordinate (p.1.val, p.2)) := by
    rintro ⟨j₁, i₁⟩ ⟨j₂, i₂⟩ h
    have hb := blockCoordinate_injective h
    exact Prod.ext (Fin.ext (Prod.mk.inj hb).1) (Prod.mk.inj hb).2
  have hmp_read : MeasurePreserving (readBoxBlock m) pathPauliDisorderLaw
      (Measure.infinitePi fun _ : Fin m =>
        Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1) :=
    disjoint_window_law (gaussianReal 0 1) _ hg_inj
  have hGood_meas : MeasurableSet (goodBoxSet q δ) :=
    MeasurableSet.pi (Set.to_countable _) fun _ _ => measurableSet_Icc
  have hFail_meas : MeasurableSet (goodBoxSet q δ)ᶜ := hGood_meas.compl
  have hFail_prob :
      (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1).real (goodBoxSet q δ)ᶜ ≤
        1 - boxProbability q δ := by
    haveI : IsProbabilityMeasure
        (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1) := inferInstance
    have hadd := measure_add_measure_compl hGood_meas
      (μ := Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1)
    rw [measure_univ] at hadd
    have hreal :
        (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1).real (goodBoxSet q δ) +
        (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1).real (goodBoxSet q δ)ᶜ = 1 := by
      rw [Measure.real, Measure.real,
        ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hadd, ENNReal.toReal_one]
    have hGood_eq :
        (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1).real (goodBoxSet q δ) =
          boxProbability q δ := rfl
    linarith only [hreal, hGood_eq]
  have hhoeff := independent_window_failures (I := Fin m)
    (Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1)
    (fun _ => (goodBoxSet q δ)ᶜ) (fun _ => hFail_meas) (fun _ => hFail_prob) hp_half.le
  have hDef_meas : MeasurableSet
      {x : Fin m → (TripleBoxIndex → ℝ) |
        ((1 - boxProbability q δ) + boxProbability q δ / 2) * (Fintype.card (Fin m) : ℝ) ≤
          ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ)} := by
    have hcnt_meas : Measurable fun x : Fin m → (TripleBoxIndex → ℝ) =>
        ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ) := by
      have heq : (fun x : Fin m → (TripleBoxIndex → ℝ) =>
          ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ)) =
          fun x => ∑ j : Fin m, if x j ∈ (goodBoxSet q δ)ᶜ then (1 : ℝ) else 0 := by
        funext x
        rw [Finset.card_filter, Nat.cast_sum]
        exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
      rw [heq]
      exact Finset.measurable_sum _ fun j _ =>
        Measurable.ite (hFail_meas.preimage (measurable_pi_apply j))
          measurable_const measurable_const
    exact measurableSet_le measurable_const hcnt_meas
  have hsub : {ω : PathPauliDisorder |
        ((goodBoxes q δ ω m).card : ℝ) < (boxProbability q δ / 2) * (m : ℝ)} ⊆
      readBoxBlock m ⁻¹' {x : Fin m → (TripleBoxIndex → ℝ) |
        ((1 - boxProbability q δ) + boxProbability q δ / 2) * (Fintype.card (Fin m) : ℝ) ≤
          ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ)} := by
    intro ω hlt
    simp only [mem_preimage, mem_setOf_eq, Fintype.card_fin]
    have hpart : (Finset.univ.filter fun j : Fin m => readBoxBlock m ω j ∈ goodBoxSet q δ).card +
        (Finset.univ.filter fun j : Fin m => readBoxBlock m ω j ∈ (goodBoxSet q δ)ᶜ).card = m := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin m))) (p := fun j : Fin m => readBoxBlock m ω j ∈ goodBoxSet q δ)
      simpa only [mem_compl_iff, Finset.card_univ, Fintype.card_fin] using h
    have hgood_eq :
        (Finset.univ.filter fun j : Fin m => readBoxBlock m ω j ∈ goodBoxSet q δ).card =
          (goodBoxes q δ ω m).card := by
      refine Finset.card_bij (fun (j : Fin m) _ => j.val) ?_ ?_ ?_
      · intro j hj
        obtain ⟨_, hmem⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, fun i => hmem i (mem_univ i)⟩
      · intro j₁ _ j₂ _ h; exact Fin.ext h
      · intro k hk
        obtain ⟨hkr, hgb⟩ := Finset.mem_filter.mp hk
        exact ⟨⟨k, Finset.mem_range.mp hkr⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i _ => hgb i⟩, rfl⟩
    have hpart_r : ((goodBoxes q δ ω m).card : ℝ) +
        ((Finset.univ.filter fun j : Fin m => readBoxBlock m ω j ∈ (goodBoxSet q δ)ᶜ).card : ℝ) =
          (m : ℝ) := by
      have h1 := congrArg (Nat.cast (R := ℝ)) hpart
      rw [Nat.cast_add, hgood_eq] at h1
      exact h1
    change ((goodBoxes q δ ω m).card : ℝ) < _ at hlt
    linarith only [hlt, hpart_r]
  have hpre : pathPauliDisorderLaw.real
      (readBoxBlock m ⁻¹' {x : Fin m → (TripleBoxIndex → ℝ) |
        ((1 - boxProbability q δ) + boxProbability q δ / 2) * (Fintype.card (Fin m) : ℝ) ≤
          ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ)}) =
      (Measure.infinitePi fun _ : Fin m =>
        Measure.infinitePi fun _ : TripleBoxIndex => gaussianReal 0 1).real
        {x : Fin m → (TripleBoxIndex → ℝ) |
          ((1 - boxProbability q δ) + boxProbability q δ / 2) * (Fintype.card (Fin m) : ℝ) ≤
            ((Finset.univ.filter fun j : Fin m => x j ∈ (goodBoxSet q δ)ᶜ).card : ℝ)} :=
    congrArg ENNReal.toReal (hmp_read.measure_preimage hDef_meas.nullMeasurableSet)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  rw [hpre]
  rw [Fintype.card_fin] at hhoeff
  refine (le_of_eq (congrArg _ ?_)).trans hhoeff
  ext x
  simp only [mem_setOf_eq, Fintype.card_fin]
  apply iff_of_eq
  congr 3
  ext j
  simp

private theorem gateCount_gt_of_boxes_and_nonCut {n : ℕ} (hn15 : 15 ≤ n)
    {q δ p_box : ℝ} (hp_pos : 0 < p_box) (hδ_nn : 0 ≤ δ)
    (hqt : (q * Real.sqrt 2) * (1 : ℝ) = Real.pi / 2)
    (hsmall : |(1 : ℝ)| * (63 * (2 * δ)) ≤ 1 / 8)
    {ω : PathPauliDisorder}
    (hgood_card : (p_box / 2) * (((n + 1) / 4 : ℕ) : ℝ) ≤
      ((goodBoxes q δ ω ((n + 1) / 4)).card : ℝ))
    (hnot_cut : ω ∉ cutOverlapEvent n 1 (p_box / 40) (199 / 200))
    {s : ℕ} (hs_le : (s : ℝ) ≤ (1 + p_box / 40) * ((n + 1 : ℕ) : ℝ)) :
    ¬ HasProjectiveCircuitApproximation (n + 2) (1 / 10 : ℝ) s
      (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) 1) := by
  rintro ⟨z, hz, C, hC, herr⟩
  have hm_ge_fifth : ((n + 1 : ℕ) : ℝ) ≤ 5 * (((n + 1) / 4 : ℕ) : ℝ) := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ ((5 * ((n + 1) / 4) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (by omega)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h1
  have herr_quarter :
      ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) 1 - z • C.eval.val‖ ≤ 1 / 4 :=
    herr.trans (by norm_num)
  have hcnt := count_good_boxes (q := q) (q' := q) (δ := δ) (t := 1) (ω := ω)
    (by simp [hδ_nn]) hqt hsmall C z hz herr_quarter
  have hmark_ge : (p_box / 10) * ((n + 1 : ℕ) : ℝ) ≤
      ((RepeatedGates.Temporal.marked (RepeatedGates.Temporal.circuitWord C)).card : ℝ) := by
    have hc_r : ((goodBoxes q δ ω ((n + 1) / 4)).card : ℝ) ≤
        ((RepeatedGates.Temporal.marked (RepeatedGates.Temporal.circuitWord C)).card : ℝ) :=
      Nat.cast_le.mpr hcnt
    have hmul5 := mul_le_mul_of_nonneg_left hm_ge_fifth (show 0 ≤ p_box / 10 by positivity)
    linarith only [hmul5, hgood_card, hc_r]
  obtain ⟨cut, hcut⟩ := component_cut C
  have hcross_lt : ((SpanningDensity.crossed cut).card : ℝ) < (p_box / 40) * ((n + 1 : ℕ) : ℝ) := by
    by_contra hge; push Not at hge
    have hov : (199 / 200 : ℝ) ≤
        ‖inner ℂ
          (choiVector (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) 1))
          (choiVector C.eval.val)‖ := by
      have h := overlap_of_fit (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) 1)
        C.eval.val (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian _) 1) C.eval.2 z hz herr
      linarith only [h]
    exact hnot_cut ⟨C, cut, hge, hov⟩
  have hparts_le : ((RepeatedGates.Temporal.parts (RepeatedGates.Temporal.circuitWord C)).card : ℝ) ≤
      ((SpanningDensity.crossed cut).card : ℝ) + 1 := by
    have h1 : ((RepeatedGates.Temporal.parts (RepeatedGates.Temporal.circuitWord C)).card : ℝ) ≤
        (((SpanningDensity.crossed cut).card + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hcut
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  have hmb := RepeatedGates.Temporal.mark_budget (RepeatedGates.Temporal.circuitWord C)
  rw [Fintype.card_fin, RepeatedGates.Temporal.circuitWord_length] at hmb
  have hmb_r : ((RepeatedGates.Temporal.marked (RepeatedGates.Temporal.circuitWord C)).card : ℝ) +
      2 * ((n + 2 : ℕ) : ℝ) ≤
      2 * ((C.gateCount : ℝ) + ((RepeatedGates.Temporal.parts (RepeatedGates.Temporal.circuitWord C)).card : ℝ)) := by
    have h1 : (((RepeatedGates.Temporal.marked (RepeatedGates.Temporal.circuitWord C)).card +
        2 * (n + 2) : ℕ) : ℝ) ≤
        ((2 * (C.gateCount + (RepeatedGates.Temporal.parts (RepeatedGates.Temporal.circuitWord C)).card) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hmb
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h1
  have hCg_le : (C.gateCount : ℝ) ≤ (s : ℝ) := Nat.cast_le.mpr hC
  have hn_cast : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_ofNat]; ring
  linarith only [hmark_ge, hcross_lt, hparts_le, hmb_r, hCg_le, hs_le, hn_cast]

/-- Unconditional exponential-tail quenched onset bound strictly past `s = n + 1 = N - 1`:
there exist `c_strict > 0`, `A > 0`, and `γ > 0` such that eventually in `n`, outside an
exponentially small `pathPauliDisorderLaw` event of probability `≤ A * exp(-γ * n)`, **every**
gate budget `s` up to `(1 + c_strict) * (n + 1)` satisfies
`1 / (20 * (‖H‖ + 1)) < tenthPlateauOnset H s < 1` and exact `1 / 10` attainment. -/
theorem gaussian_super_one_gate_per_bond_exponential_onset :
    ∃ c_strict > 0, ∃ A > 0, ∃ γ > 0, ∀ᶠ n : ℕ in atTop,
      pathPauliDisorderLaw.real {ω : PathPauliDisorder |
        let u := pathPauliDisorderShell ω n
        let H : selfAdjoint (Register (n + 2)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        ∃ s : ℕ, (s : ℝ) ≤ (1 + c_strict) * (n + 1 : ℕ) ∧
          ¬ (1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧
             tenthPlateauOnset H s < 1 ∧
             orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10)} ≤
        A * Real.exp (-γ * n) := by
  haveI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hδ₀_pos : (0 : ℝ) < 1 / 2048 := by norm_num
  have hp_half : 0 < boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 2 :=
    (good_boxes_half_mass _ hδ₀_pos).1
  have hp_pos : 0 < boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) := by
    linarith only [hp_half]
  have hc_strict : 0 < boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40 :=
    div_pos hp_pos (by norm_num)
  obtain ⟨A₁, hA₁, c₁, hc₁, hcut_tail⟩ :=
    gaussian_cut_overlap_tail (a := 1) (T := 1)
      (η := boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40) (κ := 199 / 200)
      zero_lt_one hc_strict (by norm_num)
  have hγ_pos : 0 < min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10) :=
    lt_min hc₁ (by positivity)
  refine ⟨boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40, hc_strict,
    A₁ + 1, by linarith only [hA₁],
    min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10), hγ_pos, ?_⟩
  filter_upwards [hcut_tail, eventually_ge_atTop 15] with n hn_cut hn15
  have hm_pos : 0 < (n + 1) / 4 := by omega
  have hBox_prob : pathPauliDisorderLaw.real
      {ω : PathPauliDisorder |
        ((goodBoxes (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) ω ((n + 1) / 4)).card : ℝ) <
          (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 2) *
            (((n + 1) / 4 : ℕ) : ℝ)} ≤
      Real.exp (-(min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)) * n) := by
    refine (goodBoxes_deficit_prob_le _ hδ₀_pos hm_pos).trans (Real.exp_le_exp.mpr ?_)
    have hγ_le := min_le_right c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)
    have hn_le : (n : ℝ) ≤ 5 * (((n + 1) / 4 : ℕ) : ℝ) := by
      have h1 : (n : ℝ) ≤ ((5 * ((n + 1) / 4) : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using h1
    nlinarith only [hγ_le, hn_le, sq_nonneg (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048))]
  have hCut_prob : pathPauliDisorderLaw.real
      (cutOverlapEvent n 1 (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40) (199 / 200)) ≤
      A₁ * Real.exp (-(min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)) * n) := by
    refine (hn_cut 1 ⟨le_rfl, le_rfl⟩).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        nlinarith only [min_le_left c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10),
          Nat.cast_nonneg (α := ℝ) n]))
      hA₁.le
  have hqt : ((Real.pi / (2 * Real.sqrt 2)) * Real.sqrt 2) * (1 : ℝ) = Real.pi / 2 := by
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr two_pos).ne'
    field_simp [hs2]
  have hsmall : |(1 : ℝ)| * (63 * (2 * (1 / 2048 : ℝ))) ≤ 1 / 8 := by norm_num
  have hsub_bad : {ω : PathPauliDisorder |
      let u := pathPauliDisorderShell ω n
      let H : selfAdjoint (Register (n + 2)) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      ∃ s : ℕ, (s : ℝ) ≤ (1 + boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40) * (n + 1 : ℕ) ∧
        ¬ (1 / (20 * (‖H.val‖ + 1)) < tenthPlateauOnset H s ∧
           tenthPlateauOnset H s < 1 ∧
           orbitCircuitDistance H s (tenthPlateauOnset H s) = 1 / 10)} ⊆
      cutOverlapEvent n 1 (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 40) (199 / 200) ∪
        {ω : PathPauliDisorder |
          ((goodBoxes (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) ω ((n + 1) / 4)).card : ℝ) <
            (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 2) *
              (((n + 1) / 4 : ℕ) : ℝ)} := by
    rintro ω ⟨s, hs_le, hnot⟩
    by_contra hneither
    rw [mem_union, not_or] at hneither
    obtain ⟨hnot_cut, hnot_box⟩ := hneither
    have hgood_card : (boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) / 2) *
        (((n + 1) / 4 : ℕ) : ℝ) ≤
        ((goodBoxes (Real.pi / (2 * Real.sqrt 2)) (1 / 2048) ω ((n + 1) / 4)).card : ℝ) :=
      not_lt.mp hnot_box
    have hna := gateCount_gt_of_boxes_and_nonCut hn15 hp_pos hδ₀_pos.le hqt hsmall
      hgood_card hnot_cut hs_le
    obtain ⟨hlo, hhi, _, heq, _⟩ := tenthPlateauOnset_lt_of_not_affordable
      ⟨pathHamiltonian (pathPauliDisorderShell ω n),
        isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩ zero_le_one hna
    exact hnot ⟨hlo, hhi, heq⟩
  calc pathPauliDisorderLaw.real _
      ≤ pathPauliDisorderLaw.real _ := measureReal_mono hsub_bad (measure_ne_top _ _)
    _ ≤ _ + _ := measureReal_union_le _ _
    _ ≤ A₁ * Real.exp (-(min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)) * n) +
          Real.exp (-(min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)) * n) :=
          add_le_add hCut_prob hBox_prob
    _ = (A₁ + 1) * Real.exp (-(min c₁ ((boxProbability (Real.pi / (2 * Real.sqrt 2)) (1 / 2048)) ^ 2 / 10)) * n) := by
          ring

/-! ## Section 3: Uniform claw conditioning `Ω_claw(n, η)` -/

/-- Strongest coordinatewise bulk event `Ω_all(n, η)`: every one of the `12 n + 15` Pauli
couplings in `PrefixIndex n` has magnitude `≥ η`. -/
def allCoordStrongEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | ∀ i : PrefixIndex n, η ≤ |x i|}

/-- Uniform Pauli-claw bulk event `Ω_claw(n, η)`: every site `v` has at least `2` onsite axes
with `|x| ≥ η`, and every bond `e` has at least `2` left-axis rows each supporting at least `2`
right-axis entries with `|x| ≥ η`. -/
def uniformClawEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x |
    (∀ v : Fin (n + 2), ∃ a b : Fin 3, a ≠ b ∧
      η ≤ |x ((pathCoeffEquiv n).symm (.inl (v, a)))| ∧
      η ≤ |x ((pathCoeffEquiv n).symm (.inl (v, b)))|) ∧
    (∀ e : Fin (n + 1), ∃ p₁ p₂ : Fin 3, p₁ ≠ p₂ ∧
      (∃ q₁ q₂ : Fin 3, q₁ ≠ q₂ ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p₁, q₁))))| ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p₁, q₂))))|) ∧
      (∃ r₁ r₂ : Fin 3, r₁ ≠ r₂ ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p₂, r₁))))| ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p₂, r₂))))|))}

/-- Uniform consecutive-bond non-commutativity event `Ω_nc-bond(n, η)`: every bond has a `≥ η`
coupling and every adjacent bond pair `(e, f)` (`e.succ = f.castSucc`) carries anticommuting
couplings `ab.2 ≠ cd.1` both `≥ η`. -/
def nonCommutingBondEvent (n : ℕ) (η : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x |
    (∀ e : Fin (n + 1), ∃ pq : Fin 3 × Fin 3,
      η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, pq)))|) ∧
    (∀ e f : Fin (n + 1), e.succ = f.castSucc →
      ∃ ab cd : Fin 3 × Fin 3, ab.2 ≠ cd.1 ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, ab)))| ∧
        η ≤ |x ((pathCoeffEquiv n).symm (.inr (f, cd)))|)}

theorem allCoordStrongEvent_subset_uniformClawEvent (n : ℕ) (η : ℝ) :
    allCoordStrongEvent n η ⊆ uniformClawEvent n η := by
  intro x hx
  refine ⟨fun v => ⟨0, 1, by decide, hx _, hx _⟩,
    fun e => ⟨0, 1, by decide, ⟨0, 1, by decide, hx _, hx _⟩, ⟨0, 1, by decide, hx _, hx _⟩⟩⟩

theorem uniformClawEvent_subset_nonCommutingBondEvent (n : ℕ) (η : ℝ) :
    uniformClawEvent n η ⊆ nonCommutingBondEvent n η := by
  rintro x ⟨_, hbond⟩
  refine ⟨fun e => ?_, fun e f _ => ?_⟩
  · obtain ⟨p₁, _, _, ⟨q₁, _, _, h1, _⟩, _⟩ := hbond e
    exact ⟨(p₁, q₁), h1⟩
  · obtain ⟨p₁, _, _, ⟨q₁, q₂, hq_ne, hq1, hq2⟩, _⟩ := hbond e
    obtain ⟨c₁, _, _, ⟨d₁, _, _, hd1, _⟩, _⟩ := hbond f
    by_cases hqc : q₁ = c₁
    · exact ⟨(p₁, q₂), (c₁, d₁), fun heq => hq_ne (hqc.trans heq.symm), hq2, hd1⟩
    · exact ⟨(p₁, q₁), (c₁, d₁), hqc, hq1, hd1⟩

theorem nonCommutingBondEvent_subset_allBondStrongEvent (n : ℕ) (η : ℝ) :
    nonCommutingBondEvent n η ⊆ allBondStrongEvent n η := by
  rintro x ⟨h1, _⟩ e
  obtain ⟨pq, hpq⟩ := h1 e
  exact ⟨(pathCoeffEquiv n).symm (.inr (e, pq)),
    Finset.mem_image.mpr ⟨pq, Finset.mem_univ pq, rfl⟩, hpq⟩

private theorem fin3_not_two_ge_imp_two_lt {P : Fin 3 → Prop}
    (hnot : ¬ ∃ a b : Fin 3, a ≠ b ∧ P a ∧ P b) :
    ∃ a b : Fin 3, a < b ∧ ¬ P a ∧ ¬ P b := by
  by_cases h0 : P 0
  · by_cases h1 : P 1
    · exact (hnot ⟨0, 1, by decide, h0, h1⟩).elim
    · by_cases h2 : P 2
      · exact (hnot ⟨0, 2, by decide, h0, h2⟩).elim
      · exact ⟨1, 2, by decide, h1, h2⟩
  · by_cases h1 : P 1
    · by_cases h2 : P 2
      · exact (hnot ⟨1, 2, by decide, h1, h2⟩).elim
      · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 1, by decide, h0, h1⟩

/-- Product-Gaussian complement bound for `uniformClawEvent n η`:
`ℙ(Ω_claw(n, η)ᶜ) ≤ 3 (n + 2) η² + 27 (n + 1) η⁴` for all `η ≥ 0`. -/
theorem uniformClawEvent_compl_prob_le (n : ℕ) {η : ℝ} (hη : 0 ≤ η) :
    (Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1).real (uniformClawEvent n η)ᶜ ≤
      (3 * (n + 2 : ℕ) : ℝ) * η ^ 2 + (27 * (n + 1 : ℕ) : ℝ) * η ^ 4 := by
  let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
  haveI : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  let P3 : Finset (Fin 3 × Fin 3) := Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 < p.2
  have hP3_card : P3.card = 3 := by decide
  let F_site : Finset (Fin (n + 2) × (Fin 3 × Fin 3)) := Finset.univ ×ˢ P3
  have hF_site_card : F_site.card = 3 * (n + 2) := by
    dsimp only [F_site]
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, hP3_card, mul_comm]
  let S_site (idx : Fin (n + 2) × (Fin 3 × Fin 3)) : Finset (PrefixIndex n) :=
    {(pathCoeffEquiv n).symm (.inl (idx.1, idx.2.1)),
     (pathCoeffEquiv n).symm (.inl (idx.1, idx.2.2))}
  have hS_site_card (idx : Fin (n + 2) × (Fin 3 × Fin 3)) (hidx : idx ∈ F_site) :
      (S_site idx).card = 2 := by
    have hlt : idx.2.1 < idx.2.2 := (Finset.mem_filter.mp (Finset.mem_product.mp hidx).2).2
    have hne : (pathCoeffEquiv n).symm (.inl (idx.1, idx.2.1)) ≠
        (pathCoeffEquiv n).symm (.inl (idx.1, idx.2.2)) := fun h =>
      hlt.ne (Prod.mk.inj (Sum.inl.inj ((pathCoeffEquiv n).symm.injective h))).2
    exact Finset.card_pair hne
  let F_bond : Finset (Fin (n + 1) × ((Fin 3 × Fin 3) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)))) :=
    Finset.univ ×ˢ (P3 ×ˢ (P3 ×ˢ P3))
  have hF_bond_card : F_bond.card = 27 * (n + 1) := by
    dsimp only [F_bond]
    rw [Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin, hP3_card]
    ring
  let S_bond (idx : Fin (n + 1) × ((Fin 3 × Fin 3) × ((Fin 3 × Fin 3) × (Fin 3 × Fin 3)))) :
      Finset (PrefixIndex n) :=
    let e := idx.1
    let rows := idx.2.1
    let c1 := idx.2.2.1
    let c2 := idx.2.2.2
    ({(rows.1, c1.1), (rows.1, c1.2), (rows.2, c2.1), (rows.2, c2.2)} : Finset (Fin 3 × Fin 3)).image
      fun pq => (pathCoeffEquiv n).symm (.inr (e, pq))
  have hS_bond_card (idx) (hidx : idx ∈ F_bond) : (S_bond idx).card = 4 := by
    have h1 := Finset.mem_product.mp hidx
    have h2 := Finset.mem_product.mp h1.2
    have h3 := Finset.mem_product.mp h2.2
    have hr : idx.2.1.1 < idx.2.1.2 := (Finset.mem_filter.mp h2.1).2
    have hc1 : idx.2.2.1.1 < idx.2.2.1.2 := (Finset.mem_filter.mp h3.1).2
    have hc2 : idx.2.2.2.1 < idx.2.2.2.2 := (Finset.mem_filter.mp h3.2).2
    have hinj : Function.Injective fun pq : Fin 3 × Fin 3 =>
        (pathCoeffEquiv n).symm (.inr (idx.1, pq)) :=
      fun _ _ h => (Prod.mk.inj (Sum.inr.inj ((pathCoeffEquiv n).symm.injective h))).2
    dsimp only [S_bond]
    rw [Finset.card_image_of_injective _ hinj]
    have h12 : (idx.2.1.1, idx.2.2.1.1) ≠ (idx.2.1.1, idx.2.2.1.2) :=
      fun h => hc1.ne (Prod.mk.inj h).2
    have h13 : (idx.2.1.1, idx.2.2.1.1) ≠ (idx.2.1.2, idx.2.2.2.1) :=
      fun h => hr.ne (Prod.mk.inj h).1
    have h14 : (idx.2.1.1, idx.2.2.1.1) ≠ (idx.2.1.2, idx.2.2.2.2) :=
      fun h => hr.ne (Prod.mk.inj h).1
    have h23 : (idx.2.1.1, idx.2.2.1.2) ≠ (idx.2.1.2, idx.2.2.2.1) :=
      fun h => hr.ne (Prod.mk.inj h).1
    have h24 : (idx.2.1.1, idx.2.2.1.2) ≠ (idx.2.1.2, idx.2.2.2.2) :=
      fun h => hr.ne (Prod.mk.inj h).1
    have h34 : (idx.2.1.2, idx.2.2.2.1) ≠ (idx.2.1.2, idx.2.2.2.2) :=
      fun h => hc2.ne (Prod.mk.inj h).2
    simp [h12, h13, h14, h23, h24, h34]
  let Ev_site := {x : PrefixIndex n → ℝ | ∃ idx ∈ F_site, ∀ i ∈ S_site idx, |x i| < η}
  let Ev_bond := {x : PrefixIndex n → ℝ | ∃ idx ∈ F_bond, ∀ i ∈ S_bond idx, |x i| < η}
  have hsub : (uniformClawEvent n η)ᶜ ⊆ Ev_site ∪ Ev_bond := by
    intro x hx
    rw [mem_compl_iff, uniformClawEvent, mem_setOf_eq, not_and_or] at hx
    rcases hx with hns | hnb
    · left
      push Not at hns
      obtain ⟨v, hv⟩ := hns
      obtain ⟨a, b, hab, hna, hnb⟩ := fin3_not_two_ge_imp_two_lt
        (P := fun a => η ≤ |x ((pathCoeffEquiv n).symm (.inl (v, a)))|)
        (fun ⟨a, b, hne, ha, hb⟩ => not_le_of_gt (hv a b hne ha) hb)
      refine ⟨(v, (a, b)), Finset.mem_product.mpr ⟨Finset.mem_univ v,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩⟩, ?_⟩
      intro i hi
      simp only [S_site, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact not_le.mp hna
      · exact not_le.mp hnb
    · right
      push Not at hnb
      obtain ⟨e, he⟩ := hnb
      obtain ⟨p₁, p₂, hp12, hnp1, hnp2⟩ := fin3_not_two_ge_imp_two_lt
        (P := fun p => ∃ q₁ q₂ : Fin 3, q₁ ≠ q₂ ∧
          η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p, q₁))))| ∧
          η ≤ |x ((pathCoeffEquiv n).symm (.inr (e, (p, q₂))))|)
        (fun ⟨p₁, p₂, hne, h1, h2⟩ => by
          have hall := he p₁ p₂ hne h1
          obtain ⟨r₁, r₂, hrne, hr1, hr2⟩ := h2
          exact not_le_of_gt (hall r₁ r₂ hrne hr1) hr2)
      obtain ⟨q₁, q₂, hq12, hnq1, hnq2⟩ := fin3_not_two_ge_imp_two_lt hnp1
      obtain ⟨r₁, r₂, hr12, hnr1, hnr2⟩ := fin3_not_two_ge_imp_two_lt hnp2
      refine ⟨(e, ((p₁, p₂), ((q₁, q₂), (r₁, r₂)))),
        Finset.mem_product.mpr ⟨Finset.mem_univ e, Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp12⟩, Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq12⟩,
             Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr12⟩⟩⟩⟩, ?_⟩
      intro i hi
      simp only [S_bond, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with ⟨pq, (rfl | rfl | rfl | rfl), rfl⟩
      · exact not_le.mp hnq1
      · exact not_le.mp hnq2
      · exact not_le.mp hnr1
      · exact not_le.mp hnr2
  have hb_site := (pi_smallCube_union_prob_le F_site S_site 2 hS_site_card hη).2
  have hb_bond := (pi_smallCube_union_prob_le F_bond S_bond 4 hS_bond_card hη).2
  rw [hF_site_card, Nat.cast_mul, Nat.cast_ofNat] at hb_site
  rw [hF_bond_card, Nat.cast_mul, Nat.cast_ofNat] at hb_bond
  calc μ.real (uniformClawEvent n η)ᶜ
      ≤ μ.real (Ev_site ∪ Ev_bond) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real Ev_site + μ.real Ev_bond := measureReal_union_le _ _
    _ ≤ (3 * (n + 2 : ℕ) : ℝ) * η ^ 2 + (27 * (n + 1 : ℕ) : ℝ) * η ^ 4 :=
        add_le_add hb_site hb_bond

/-- Deterministic `TwinLineModel` exclusion on `uniformClawEvent n η`: for any consecutive bonds
`e, f` (`e.succ = f.castSucc`) and any set `S` containing `{l | η ≤ |u l|}`, the frustration graph
on `S` admits no `TwinLineModel` (realizing a `6`-term twin-distinguished claw on `(e, f)`). -/
theorem isEmpty_twinLineModel_of_uniformClaw {n : ℕ} {ρ : Type*} [DecidableEq ρ]
    {u : PathShell n} {η : ℝ}
    (hclaw : (fun i => u (pathCoeffEquiv n i)) ∈ uniformClawEvent n η)
    (e f : Fin (n + 1)) (hef : e.succ = f.castSucc)
    {S : Set (PathLabel n)} (hS : ∀ l : PathLabel n, η ≤ |u l| → l ∈ S) :
    IsEmpty (TwinLineModel (pathFrustrationAdj S) ρ) := by
  have hmem_S (l : PathLabel n)
      (h : η ≤ |(fun i => u (pathCoeffEquiv n i)) ((pathCoeffEquiv n).symm l)|) : l ∈ S := by
    apply hS
    simpa only [Equiv.apply_symm_apply] using h
  obtain ⟨hsite, hbond⟩ := hclaw
  obtain ⟨b₁, b₂, hb_ne, hb1, hb2⟩ := hsite f.castSucc
  obtain ⟨c₁, c₂, hc_ne, hrow_c1, hrow_c2⟩ := hbond f
  have hex_shared : ∃ b : Fin 3, (b = b₁ ∨ b = b₂) ∧ (b = c₁ ∨ b = c₂) := by
    by_cases h1 : b₁ = c₁ ∨ b₁ = c₂
    · exact ⟨b₁, Or.inl rfl, h1⟩
    · by_cases h2 : b₂ = c₁ ∨ b₂ = c₂
      · exact ⟨b₂, Or.inr rfl, h2⟩
      · exfalso
        rw [not_or] at h1 h2
        let T : Finset (Fin 3) := insert c₁ {b₁, b₂}
        have hc1_not : c₁ ∉ ({b₁, b₂} : Finset (Fin 3)) := by
          simp [Ne.symm h1.1, Ne.symm h2.1]
        have hT_card : T.card = Fintype.card (Fin 3) := by
          dsimp [T]; rw [Finset.card_insert_of_notMem hc1_not, Finset.card_pair hb_ne]; rfl
        have hT_univ : T = Finset.univ := Finset.eq_univ_of_card T hT_card
        have hc2_mem : c₂ ∈ T := hT_univ ▸ Finset.mem_univ c₂
        simp [T, Ne.symm hc_ne, Ne.symm h1.2, Ne.symm h2.2] at hc2_mem
  obtain ⟨b, hb_on, hb_bd⟩ := hex_shared
  have hb_in_S : Sum.inl (f.castSucc, b) ∈ S := by
    rcases hb_on with rfl | rfl
    · exact hmem_S _ hb1
    · exact hmem_S _ hb2
  obtain ⟨w₁, w₂, hw_ne, hw1_raw, hw2_raw⟩ :
      ∃ w₁ w₂ : Fin 3, w₁ ≠ w₂ ∧ Sum.inr (f, (b, w₁)) ∈ S ∧ Sum.inr (f, (b, w₂)) ∈ S := by
    rcases hb_bd with rfl | rfl
    · obtain ⟨w₁, w₂, hne, h1, h2⟩ := hrow_c1
      exact ⟨w₁, w₂, hne, hmem_S _ h1, hmem_S _ h2⟩
    · obtain ⟨w₁, w₂, hne, h1, h2⟩ := hrow_c2
      exact ⟨w₁, w₂, hne, hmem_S _ h1, hmem_S _ h2⟩
  obtain ⟨p₀, _, _, ⟨q₁, q₂, hq_ne, hq1, hq2⟩, _⟩ := hbond e
  obtain ⟨q₀, hq₀_ne_b, ho_in_S⟩ : ∃ q₀ : Fin 3, q₀ ≠ b ∧ Sum.inr (e, (p₀, q₀)) ∈ S := by
    by_cases h1 : q₁ = b
    · exact ⟨q₂, fun h2 => hq_ne (h1.trans h2.symm), hmem_S _ hq2⟩
    · exact ⟨q₁, h1, hmem_S _ hq1⟩
  obtain ⟨a₁, a₂, ha_ne, ha1, ha2⟩ := hsite e.castSucc
  obtain ⟨a₀, z₀, ha₀_ne_p₀, haz_ne, ha_in_S, hz_in_S⟩ :
      ∃ a₀ z₀ : Fin 3, a₀ ≠ p₀ ∧ a₀ ≠ z₀ ∧
        Sum.inl (e.castSucc, a₀) ∈ S ∧ Sum.inl (e.castSucc, z₀) ∈ S := by
    by_cases h1 : a₁ = p₀
    · exact ⟨a₂, a₁, fun h2 => ha_ne (h1.trans h2.symm), ha_ne.symm, hmem_S _ ha2, hmem_S _ ha1⟩
    · exact ⟨a₁, a₂, h1, ha_ne, hmem_S _ ha1, hmem_S _ ha2⟩
  let o : S := ⟨.inr (e, (p₀, q₀)), ho_in_S⟩
  let a : S := ⟨.inl (e.castSucc, a₀), ha_in_S⟩
  let b_v : S := ⟨.inl (f.castSucc, b), hb_in_S⟩
  let c : S := ⟨.inr (f, (b, w₁)), hw1_raw⟩
  let z : S := ⟨.inl (e.castSucc, z₀), hz_in_S⟩
  let w : S := ⟨.inr (f, (b, w₂)), hw2_raw⟩
  have hleft : e.castSucc < f.castSucc := hef ▸ e.castSucc_lt_succ
  have hoa : pathFrustrationAdj S o a := fun h => ha₀_ne_p₀
    (((commute_onsite_coupling_iff e.castSucc a₀ e (p₀, q₀)).mp h.symm).1 rfl)
  have hob : pathFrustrationAdj S o b_v := fun h => hq₀_ne_b
    (((commute_onsite_coupling_iff f.castSucc b e (p₀, q₀)).mp h.symm).2 hef.symm).symm
  have hoc : pathFrustrationAdj S o c := fun h => hq₀_ne_b
    ((commute_consecutive_coupling_iff e f hef (p₀, q₀) (b, w₁)).mp h)
  have hab : ¬ pathFrustrationAdj S a b_v := fun h => h
    ((commute_onsitePauli_iff e.castSucc f.castSucc a₀ b).mpr (Or.inl hleft.ne))
  have hac : ¬ pathFrustrationAdj S a c := fun h => h
    ((commute_onsite_coupling_iff e.castSucc a₀ f (b, w₁)).mpr
      ⟨fun he => (hleft.ne he).elim, fun he => ((hleft.trans f.castSucc_lt_succ).ne he).elim⟩)
  have hcb : ¬ pathFrustrationAdj S c b_v := fun h => h
    (((commute_onsite_coupling_iff f.castSucc b f (b, w₁)).mpr
      ⟨fun _ => rfl, fun he => (f.castSucc_lt_succ.ne he).elim⟩).symm)
  have haz : pathFrustrationAdj S a z := fun h =>
    ((commute_onsitePauli_iff e.castSucc e.castSucc a₀ z₀).mp h).elim (fun he => he rfl) haz_ne
  have hbz : ¬ pathFrustrationAdj S b_v z := fun h => h
    ((commute_onsitePauli_iff f.castSucc e.castSucc b z₀).mpr (Or.inl hleft.ne'))
  have hcz : ¬ pathFrustrationAdj S c z := fun h => h
    (((commute_onsite_coupling_iff e.castSucc z₀ f (b, w₁)).mpr
      ⟨fun he => (hleft.ne he).elim, fun he => ((hleft.trans f.castSucc_lt_succ).ne he).elim⟩).symm)
  have hcw : pathFrustrationAdj S c w := fun h =>
    hw_ne ((commute_coupling_same_left_iff f b w₁ w₂).mp h)
  have hbw : ¬ pathFrustrationAdj S b_v w := fun h => h
    ((commute_onsite_coupling_iff f.castSucc b f (b, w₂)).mpr
      ⟨fun _ => rfl, fun he => (f.castSucc_lt_succ.ne he).elim⟩)
  exact isEmpty_twinLineModel_of_claw (pathFrustrationAdj S)
    (fun {_ _} h hc => h hc.symm) (fun _ h => h (Commute.refl _))
    o a c b_v hoa hoc hob hac hab hcb ⟨z, haz, hcz⟩ ⟨z, haz, hbz⟩ ⟨w, hcw, hbw⟩

/-- Deterministic `PauliNoncontextual` operator-norm floor on `uniformClawEvent n η`: every
`u ∈ Ω_claw(n, η)` (`η ≥ 0`) satisfies `√(n + 1) * η ≤ ‖pathHamiltonian u - pathHamiltonian v‖`
against every `PauliNoncontextual` shell `v`. -/
theorem noncontextual_operator_dist_ge_of_uniformClaw {n : ℕ} {u v : PathShell n} {η : ℝ}
    (hη : 0 ≤ η) (hclaw : (fun i => u (pathCoeffEquiv n i)) ∈ uniformClawEvent n η)
    (hv : PauliNoncontextual (fun l : ActivePathLabels v => finitePauliMatrix (pathWord l.1))) :
    Real.sqrt (n + 1 : ℕ) * η ≤ ‖pathHamiltonian u - pathHamiltonian v‖ := by
  have hsub := path_noncontextual_forbids_two_multiaxis_sites v hv
  let M_set : Finset (Fin (n + 2)) :=
    Finset.univ.filter fun s : Fin (n + 2) =>
      ∃ a b : Fin 3, v (.inl (s, a)) ≠ 0 ∧ v (.inl (s, b)) ≠ 0 ∧ a ≠ b
  have hM_le1 : M_set.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun s₁ hs₁ s₂ hs₂ => ?_
    exact hsub (Finset.mem_filter.mp hs₁).2 (Finset.mem_filter.mp hs₂).2
  let GoodSites : Finset (Fin (n + 2)) := Finset.univ \ M_set
  have hGood_card : n + 1 ≤ GoodSites.card := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ M_set)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    dsimp only [GoodSites]
    omega
  have hsite_err (s : Fin (n + 2)) (hs : s ∈ GoodSites) :
      η ^ 2 ≤ ∑ a : Fin 3, ‖(u - v) (.inl (s, a))‖ ^ 2 := by
    have hs_not : s ∉ M_set := (Finset.mem_sdiff.mp hs).2
    obtain ⟨a₁, a₂, hne, h1, h2⟩ := hclaw.1 s
    have hu1 : η ≤ |u (.inl (s, a₁))| := by simpa only [Equiv.apply_symm_apply] using h1
    have hu2 : η ≤ |u (.inl (s, a₂))| := by simpa only [Equiv.apply_symm_apply] using h2
    have hzero_one : v (.inl (s, a₁)) = 0 ∨ v (.inl (s, a₂)) = 0 := by
      by_contra hboth; push Not at hboth
      exact hs_not (Finset.mem_filter.mpr ⟨Finset.mem_univ s, a₁, a₂, hboth.1, hboth.2, hne⟩)
    rcases hzero_one with hz1 | hz2
    · refine (pow_le_pow_left₀ hη hu1 2).trans ?_
      have hterm : |u (.inl (s, a₁))| ^ 2 = ‖(u - v) (.inl (s, a₁))‖ ^ 2 := by
        change _ = ‖u (.inl (s, a₁)) - v (.inl (s, a₁))‖ ^ 2
        rw [hz1, sub_zero, Real.norm_eq_abs]
      rw [hterm]
      exact Finset.single_le_sum (f := fun a : Fin 3 => ‖(u - v) (.inl (s, a))‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_univ a₁)
    · refine (pow_le_pow_left₀ hη hu2 2).trans ?_
      have hterm : |u (.inl (s, a₂))| ^ 2 = ‖(u - v) (.inl (s, a₂))‖ ^ 2 := by
        change _ = ‖u (.inl (s, a₂)) - v (.inl (s, a₂))‖ ^ 2
        rw [hz2, sub_zero, Real.norm_eq_abs]
      rw [hterm]
      exact Finset.single_le_sum (f := fun a : Fin 3 => ‖(u - v) (.inl (s, a))‖ ^ 2)
        (fun a _ => sq_nonneg _) (Finset.mem_univ a₂)
  have hnorm_sq : ((n + 1 : ℕ) : ℝ) * η ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, Fintype.sum_prod_type]
    have h1 : ((n + 1 : ℕ) : ℝ) * η ^ 2 ≤
        ∑ s ∈ GoodSites, ∑ a : Fin 3, ‖(u - v) (.inl (s, a))‖ ^ 2 := by
      calc ((n + 1 : ℕ) : ℝ) * η ^ 2
          ≤ (GoodSites.card : ℝ) * η ^ 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hGood_card) (sq_nonneg η)
        _ = ∑ _s ∈ GoodSites, η ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ s ∈ GoodSites, ∑ a : Fin 3, ‖(u - v) (.inl (s, a))‖ ^ 2 :=
            Finset.sum_le_sum hsite_err
    have h2 : (∑ s ∈ GoodSites, ∑ a : Fin 3, ‖(u - v) (.inl (s, a))‖ ^ 2) ≤
        ∑ s : Fin (n + 2), ∑ a : Fin 3, ‖(u - v) (.inl (s, a))‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h3 : 0 ≤ ∑ x : Fin (n + 1) × (Fin 3 × Fin 3), ‖(u - v) (.inr x)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith only [h1, h2, h3]
  have hsq : (Real.sqrt (n + 1 : ℕ) * η) ^ 2 ≤ ‖pathHamiltonian u - pathHamiltonian v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    exact hnorm_sq.trans (pow_le_pow_left₀ (norm_nonneg _)
      (pathShell_dist_le_pathHamiltonian_dist u v) 2)
  exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hη) (norm_nonneg _)).mp hsq

/-! ### Reusable eigenframe-parameterized tube helpers -/

/-- Full `2^N` Vandermonde rank on `[0, 1]` for any `H : selfAdjoint (Register N)` with injective
eigenvalues. -/
theorem vandermonde_full_rank_unit_interval {N : ℕ} (H : selfAdjoint (Register N))
    (hinj : Function.Injective H.2.isHermitian.eigenvalues) :
    ∃ τ > 0, (∀ m : Fin (2 ^ N), ((m : ℕ) : ℝ) * τ ∈ Icc (0 : ℝ) 1) ∧
      Module.finrank ℂ (Submodule.span ℂ
        (range fun m : Fin (2 ^ N) => unitaryEvolution H.val (((m : ℕ) : ℝ) * τ))) = 2 ^ N := by
  have hden_pos : 0 < ((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1) :=
    mul_pos (by positivity) (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
  let τ := 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1))
  have hτ_pos : 0 < τ := div_pos zero_lt_one hden_pos
  have hτ_le_pi : τ ≤ Real.pi / (‖H.val‖ + 1) := by
    have h1_le_D : (1 : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have h1 : 1 / (((2 ^ N : ℕ) : ℝ) * (‖H.val‖ + 1)) ≤ 1 / (‖H.val‖ + 1) :=
      div_le_div_of_nonneg_left zero_le_one
        (add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one)
        (le_mul_of_one_le_left (add_nonneg (norm_nonneg _) zero_le_one) h1_le_D)
    exact h1.trans (div_le_div_of_nonneg_right
      ((by norm_num : (1 : ℝ) ≤ 3).trans Real.pi_gt_three.le)
      (add_nonneg (norm_nonneg _) zero_le_one))
  obtain ⟨_, hspan_eq, hfinrank⟩ := orbit_vandermonde_span_eq_spectralSpan H hinj hτ_pos hτ_le_pi
  refine ⟨τ, hτ_pos, fun m => ⟨mul_nonneg (Nat.cast_nonneg _) hτ_pos.le, ?_⟩, ?_⟩
  · dsimp only [τ]; rw [mul_one_div, div_le_one hden_pos]
    have hm_le : ((m : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by exact_mod_cast m.isLt.le
    exact hm_le.trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_left (norm_nonneg _)))
  · rw [hspan_eq, hfinrank]

/-- Eigenframe-parameterized antipodal scalar-return excision: for any `(V, E)` diagonalizing a
traceless Hamiltonian `H` of operator norm `≥ 3` and any `T ≥ 2`, there exists `t₀ ∈ (0, T]` with
`√2 ≤ ‖unitaryEvolution H t₀ - z • 1‖` for all unit-modulus `z : ℂ`. -/
private theorem exists_antipodal_excision_of_eigenbasis {N : ℕ}
    (V : Matrix.unitaryGroup (Config N) ℂ) (E : Config N → ℝ)
    {H : Register N}
    (hspec : H = V.val * Matrix.diagonal (Complex.ofReal ∘ E) * star V.val)
    (hevol : ∀ t : ℝ, unitaryEvolution H t =
      V.val * Matrix.diagonal (fun i => Complex.exp (-(Complex.I * (t * E i)))) * star V.val)
    (htr0 : Matrix.trace H = 0) (hH_ge3 : (3 : ℝ) ≤ ‖H‖)
    {T : ℝ} (hT2 : 2 ≤ T) :
    ∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution H t₀ - z • (1 : Register N)‖ := by
  have hsum_E : (∑ c : Config N, E c) = 0 := by
    have htr_s : Matrix.trace H = ∑ c : Config N, (E c : ℂ) := by
      rw [hspec, Matrix.trace_mul_comm, ← mul_assoc, (Unitary.mem_iff.mp V.2).1, one_mul,
        Matrix.trace]; simp [Matrix.diagonal]
    rw [htr0] at htr_s
    exact Complex.ofReal_injective (by simpa [Complex.ofReal_sum] using htr_s.symm)
  have huniv_ne : (Finset.univ : Finset (Config N)).Nonempty := ⟨fun _ => false, Finset.mem_univ _⟩
  obtain ⟨c_max, _, hc_max⟩ := Finset.exists_max_image Finset.univ E huniv_ne
  obtain ⟨c_min, _, hc_min⟩ := Finset.exists_min_image Finset.univ E huniv_ne
  obtain ⟨c_abs, _, hc_abs⟩ := Finset.exists_max_image Finset.univ (fun c => |E c|) huniv_ne
  have hE_max_nn : 0 ≤ E c_max := by
    by_contra hlt; push Not at hlt
    linarith only [hsum_E, Finset.sum_neg (fun c _ => (hc_max c (Finset.mem_univ c)).trans_lt hlt) huniv_ne]
  have hE_min_np : E c_min ≤ 0 := by
    by_contra hgt; push Not at hgt
    linarith only [hsum_E, Finset.sum_pos (fun c _ => hgt.trans_le (hc_min c (Finset.mem_univ c))) huniv_ne]
  have hH_le_abs : ‖H‖ ≤ |E c_abs| := by
    have hiso := l2_opNorm_unitary_conj_eq (V := star V.val) (Unitary.star_mem V.2) H
    have hconj : star V.val * H * V.val = Matrix.diagonal (Complex.ofReal ∘ E) := by
      rw [hspec]; exact star_conj_cancel V.2 _
    rw [star_star, hconj] at hiso
    rw [← hiso, ← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)
      (Matrix.diagonal (Complex.ofReal ∘ E))).opNorm_le_bound (abs_nonneg _) fun ψ => ?_
    have hsq : ‖Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ‖ ^ 2 ≤ (|E c_abs| * ‖ψ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
      refine Finset.sum_le_sum fun c _ => ?_
      have hcoord : (Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)
          (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c = (E c : ℂ) * ψ.ofLp c := by
        rw [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]; rfl
      change ‖(Matrix.toEuclideanCLM (n := Config N) (𝕜 := ℂ)
        (Matrix.diagonal (Complex.ofReal ∘ E)) ψ).ofLp c‖ ^ 2 ≤ _
      rw [hcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hc_abs c (Finset.mem_univ c)) 2) (sq_nonneg _)
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp hsq
  have hgap_ge3 : 3 ≤ E c_max - E c_min := by
    have h3_abs : 3 ≤ |E c_abs| := hH_ge3.trans hH_le_abs
    rcases le_or_gt 0 (E c_abs) with hnn | hneg
    · rw [abs_of_nonneg hnn] at h3_abs
      linarith only [h3_abs, hc_max c_abs (Finset.mem_univ c_abs), hE_min_np]
    · rw [abs_of_neg hneg] at h3_abs
      linarith only [h3_abs, hc_min c_abs (Finset.mem_univ c_abs), hE_max_nn]
  let ΔE := E c_max - E c_min
  have hΔE_pos : 0 < ΔE := by linarith only [hgap_ge3]
  let t₀ := Real.pi / ΔE
  have ht₀_T : t₀ ∈ Ioc 0 T := ⟨div_pos Real.pi_pos hΔE_pos,
    (div_lt_div_of_pos_left Real.pi_pos two_pos (by linarith only [hgap_ge3])).le.trans
      ((div_le_div_of_nonneg_right Real.pi_lt_four.le two_pos.le).trans (by norm_num; exact hT2))⟩
  refine ⟨t₀, ht₀_T, fun z hz => ?_⟩
  let D_t₀ := Matrix.diagonal fun i => Complex.exp (-(Complex.I * (t₀ * E i)))
  have hconj_t₀ : star V.val * (unitaryEvolution H t₀ - z • (1 : Register N)) * V.val =
      D_t₀ - z • (1 : Register N) := by
    rw [hevol t₀]
    change star V.val * (V.val * D_t₀ * star V.val - z • 1) * V.val = _
    rw [Matrix.mul_sub, Matrix.sub_mul, star_conj_cancel V.2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, (Unitary.mem_iff.mp V.2).1]
  have hiso := l2_opNorm_unitary_conj_eq (V := star V.val) (Unitary.star_mem V.2)
    (unitaryEvolution H t₀ - z • (1 : Register N))
  rw [star_star, hconj_t₀] at hiso
  rw [← hiso]
  let w₁ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_max)))
  let w₂ : ℂ := Complex.exp (-(Complex.I * (t₀ * E c_min)))
  have hw₁_norm : ‖w₁‖ = 1 := by
    dsimp only [w₁]; rw [Complex.norm_exp]
    have hre : (-(Complex.I * (↑t₀ * ↑(E c_max)))).re = 0 := by simp
    rw [hre, Real.exp_zero]
  have hw₂_eq : w₂ = -w₁ := by
    dsimp only [w₁, w₂]
    have harg : -(Complex.I * (↑t₀ * ↑(E c_min))) =
        -(Complex.I * (↑t₀ * ↑(E c_max))) + ↑Real.pi * Complex.I := by
      have htΔ : t₀ * ΔE = Real.pi := div_mul_cancel₀ Real.pi hΔE_pos.ne'
      have hcast : (t₀ : ℂ) * ((E c_max : ℂ) - (E c_min : ℂ)) = (Real.pi : ℂ) := by
        exact_mod_cast htΔ
      linear_combination Complex.I * hcast
    rw [harg, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg, mul_one]
  have he₁ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register N)) c_max c_max
  have he₂ := norm_entry_le_l2_opNorm (D_t₀ - z • (1 : Register N)) c_min c_min
  simp only [D_t₀, Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
    Matrix.one_apply_eq, smul_eq_mul, mul_one] at he₁ he₂
  change ‖w₁ - z‖ ≤ _ at he₁
  change ‖w₂ - z‖ ≤ _ at he₂
  rw [hw₂_eq] at he₂
  have hpar : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 4 := by
    have h1 : ‖w₁ - z‖ ^ 2 + ‖-w₁ - z‖ ^ 2 = 2 * (‖w₁‖ ^ 2 + ‖z‖ ^ 2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.neg_re, Complex.neg_im]; ring
    rw [h1, hw₁_norm, hz]; norm_num
  have hsq_ge2 : 2 ≤ ‖D_t₀ - z • (1 : Register N)‖ ^ 2 := by
    linarith only [hpar, pow_le_pow_left₀ (norm_nonneg _) he₁ 2,
      pow_le_pow_left₀ (norm_nonneg _) he₂ 2]
  exact Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hsq_ge2⟩

/-- Antipodal scalar-return excision for any chain shell `u : PathShell n` having some label `l₀`
with `3 ≤ |u l₀|`. -/
theorem exists_antipodal_return_excision_of_shell_coeff {n : ℕ} (u : PathShell n)
    (l₀ : PathLabel n) (hl₀ : 3 ≤ |u l₀|) {T : ℝ} (hT2 : 2 ≤ T) :
    ∃ t₀ ∈ Ioc (0 : ℝ) T, ∀ z : ℂ, ‖z‖ = 1 →
      Real.sqrt 2 ≤ ‖unitaryEvolution (pathHamiltonian u) t₀ - z • (1 : Register (n + 2))‖ := by
  let N := n + 2
  let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
  have hH_ge3 : (3 : ℝ) ≤ ‖H.val‖ := by
    let W₀ := finitePauliMatrix (pathWord l₀)
    have hW₀_u : W₀ ∈ unitary (Register N) := finitePauliMatrix_mem_unitary _
    have hW₀_n : ‖star W₀‖ = 1 := by rw [norm_star]; exact CStarRing.norm_of_mem_unitary hW₀_u
    have htr_eq : Matrix.trace (star W₀ * H.val) = ((2 ^ N : ℕ) : ℂ) * ((u l₀ : ℝ) : ℂ) := by
      change Matrix.trace (star W₀ * pathHamiltonian u) = _
      rw [pathHamiltonian_eq_sum, Matrix.mul_sum, Matrix.trace_sum, Finset.sum_eq_single l₀]
      · rw [Matrix.mul_smul, Matrix.trace_smul]
        have h1 : star W₀ * W₀ = 1 := (Unitary.mem_iff.mp hW₀_u).1
        change _ • Matrix.trace (star W₀ * W₀) = _
        rw [h1, Matrix.trace_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
          smul_eq_mul, mul_comm]
      · intro l _ hne
        rw [Matrix.mul_smul, Matrix.trace_smul, trace_star_finitePauliMatrix_mul]
        have hw : pathWord l₀ ≠ pathWord l := fun h => hne (pathWord_injective h).symm
        rw [if_neg hw, smul_zero]
      · simp
    have htr_le := norm_trace_le_card_mul_l2_opNorm (star W₀ * H.val)
    have hcard : (Fintype.card (Config N) : ℝ) = (2 : ℝ) ^ N := by simp [Config]
    rw [htr_eq, norm_mul, Complex.norm_natCast, Nat.cast_pow, Nat.cast_ofNat,
      Complex.norm_real, Real.norm_eq_abs, hcard] at htr_le
    have hmul_le : ‖star W₀ * H.val‖ ≤ ‖H.val‖ :=
      (norm_mul_le _ _).trans (by rw [hW₀_n, one_mul])
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos two_pos _
    exact hl₀.trans
      (le_of_mul_le_mul_left (htr_le.trans (mul_le_mul_of_nonneg_left hmul_le h2pos.le)) h2pos)
  have htrH0 : Matrix.trace H.val = 0 := by
    rw [show H.val = pathHamiltonian u from rfl, pathHamiltonian_eq_sum, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.trace_smul,
      finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity l), smul_zero]
  exact exists_antipodal_excision_of_eigenbasis (hermitianEigenbasisUnitary H.2.isHermitian)
    H.2.isHermitian.eigenvalues H.2.isHermitian.spectral_theorem
    (unitaryEvolution_spectral H.2.isHermitian) htrH0 hH_ge3 hT2

/-- Reading `PathLabel n → ℝ` from `pathPauliDisorderLaw` is measure-preserving onto product
standard Gaussian measure. -/
theorem measurePreserving_pathDisorder_labels (n : ℕ) :
    MeasurePreserving (fun (ω : PathPauliDisorder) (l : PathLabel n) => pathPauliDisorderShell ω n l)
      pathPauliDisorderLaw (Measure.pi fun _ : PathLabel n => gaussianReal 0 1) := by
  let γ := gaussianReal 0 1
  let f_idx : PathLabel n → ℕ × PathPauliDirections
    | .inl (s, a) => (s.val, .inl a)
    | .inr (e, ab) => (e.val, .inr ab)
  have hf_inj : Function.Injective f_idx := by
    intro l j h
    rcases l with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases j with ⟨c', d'⟩ | ⟨c', d'⟩
    · have he := Prod.mk.inj h
      exact congrArg Sum.inl (Prod.ext (Fin.ext he.1) (Sum.inl.inj he.2))
    · exact nomatch congrArg Prod.snd h
    · exact nomatch congrArg Prod.snd h
    · have he := Prod.mk.inj h
      exact congrArg Sum.inr (Prod.ext (Fin.ext he.1) (Sum.inr.inj he.2))
  have hi := iIndepFun_infinitePi (P := fun _ : ℕ × PathPauliDirections => γ)
    (X := fun _ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  have heval : MeasurePreserving
      (fun ω : PathPauliDisorder => fun l : PathLabel n => ω (f_idx l))
      pathPauliDisorderLaw (Measure.pi fun _ : PathLabel n => γ) := by
    refine ⟨measurable_pi_lambda _ (fun _ => measurable_pi_apply _), ?_⟩
    have h := (hi.precomp hf_inj).map_fun_eq_pi_map (fun _ => (measurable_pi_apply _).aemeasurable)
    have hmap (l : PathLabel n) :
        Measure.map (fun ω : PathPauliDisorder => ω (f_idx l)) pathPauliDisorderLaw = γ :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ × PathPauliDirections => γ) (f_idx l)).map_eq
    exact h.trans (congrArg Measure.pi (funext hmap))
  convert heval using 1
  funext ω l; cases l <;> rfl

#print axioms measurePreserving_pi_gaussian_orthogonal
#print axioms det2_sq_le_frob_rankOne_err
#print axioms bondMinorInvariant_orthog_eq
#print axioms bondMinorInvariant_le_rankOne_dist
#print axioms gaussian_super_one_gate_per_bond_exponential_onset
#print axioms uniformClawEvent_compl_prob_le
#print axioms isEmpty_twinLineModel_of_uniformClaw
#print axioms noncontextual_operator_dist_ge_of_uniformClaw

end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
