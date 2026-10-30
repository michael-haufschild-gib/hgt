import GaloisForLFunctions.CompletedArithmeticForms.WeilPrefixPayment
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilGroundStateIsThePole
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneHorizonMakesEveryBoundedOverlapPositive

/-!
# The sharp complete Weil inverse cost

The reciprocal completed pole energy is the asymptotically optimal cost of
every mixed column against the actual tilted-spline complete Weil inverse.
One finite cost works on every bounded overlap interval. The strict threshold
retains the distinction between a limiting reserve and a finite spectral floor.
-/

noncomputable section

open Matrix Finset Filter Topology MeasureTheory
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- Reciprocal of the actual completed conductor-one energy. -/
def tiltedWeilInverseCost (c : ℝ) : ℝ :=
  (completedConductorEnergy tiltedUnitSpline c 1)⁻¹

theorem tiltedWeilGroundEnergy_pos {c : ℝ} (hc : 0 < c) :
    0 < completedConductorEnergy tiltedUnitSpline c 1 := by
  exact (mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
    (integral_shellSpectrum_tiltedUnitSpline_pos c)).trans_le
      (tiltedUnitSpline_completedConductorEnergy_ge_boundedOverlapTail hc le_rfl one_pos)

theorem tiltedWeilInverseCost_pos {c : ℝ} (hc : 0 < c) :
    0 < tiltedWeilInverseCost c := inv_pos.mpr (tiltedWeilGroundEnergy_pos hc)

/-- Spectral floors pay the full square mass, including every mixed entry. -/
private theorem squareMass_le_of_eigenvalue_floor {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {C : ℝ} (hC : 0 < C)
    (hfloor : ∀ i, C⁻¹ ≤ hA.eigenvalues i) (v : I → ℝ) :
    v ⬝ᵥ v ≤ C * (v ⬝ᵥ A *ᵥ v) := by
  let x : EuclideanSpace ℝ I := WithLp.toLp 2 v
  have he : C⁻¹ * ‖x‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA,
      ← hA.eigenvectorBasis.sum_sq_inner_left x, mul_sum]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hfloor i) (sq_nonneg _)
  rw [← real_inner_self_eq_norm_sq] at he
  have hq : C⁻¹ * (v ⬝ᵥ v) ≤ v ⬝ᵥ A *ᵥ v := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      star_trivial] using he
  have h := mul_le_mul_of_nonneg_left hq hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using h

/-- A positive eigenvalue gives an attained unit-vector reciprocal inverse cost. -/
private theorem inverse_eigenvector_unit_cost {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.PosDef) (i : I) :
    ∃ b : I → ℝ, b ⬝ᵥ b = 1 ∧ b ⬝ᵥ A⁻¹ *ᵥ b = (hA.isHermitian.eigenvalues i)⁻¹ := by
  let b : I → ℝ := hA.isHermitian.eigenvectorBasis i
  let λ := hA.isHermitian.eigenvalues i
  have hλ : 0 < λ := hA.isHermitian.posDef_iff_eigenvalues_pos.mp hA i
  have hb : b ⬝ᵥ b = 1 := by
    have h := (orthonormal_iff_ite.mp hA.isHermitian.eigenvectorBasis.orthonormal) i i
    simpa only [ite_true, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using h
  have heig : A *ᵥ b = λ • b := hA.isHermitian.mulVec_eigenvectorBasis i
  have hscale : λ • (A⁻¹ *ᵥ b) = b := by
    rw [← mulVec_smul, ← heig, mulVec_mulVec,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'), one_mulVec]
  have hinv : A⁻¹ *ᵥ b = λ⁻¹ • b := by
    calc
      _ = λ⁻¹ • (λ • (A⁻¹ *ᵥ b)) := by rw [smul_smul, inv_mul_cancel₀ hλ.ne', one_smul]
      _ = _ := by rw [hscale]
  refine ⟨b, hb, ?_⟩
  rw [hinv, dotProduct_smul, smul_eq_mul, hb, mul_one]

/-- Every constant above the reciprocal ground energy eventually pays all complete inverse columns. -/
theorem eventually_tiltedWeil_inverse_cost_le {c C : ℝ} (hc : 0 < c)
    (hC : tiltedWeilInverseCost c < C) :
    ∀ᶠ N : ℕ in atTop, ∀ b : PrimeHorizonIndex N → ℝ,
      0 ≤ b ⬝ᵥ (completeWeilMatrix tiltedUnitSpline c N)⁻¹ *ᵥ b ∧
        b ⬝ᵥ (completeWeilMatrix tiltedUnitSpline c N)⁻¹ *ᵥ b ≤ C * (b ⬝ᵥ b) := by
  have hE := tiltedWeilGroundEnergy_pos hc
  have hC0 : 0 < C := (tiltedWeilInverseCost_pos hc).trans hC
  have hgap : C⁻¹ < completedConductorEnergy tiltedUnitSpline c 1 := by
    exact (inv_lt_comm₀ hC0 hE).mpr hC
  have hε : 0 < (completedConductorEnergy tiltedUnitSpline c 1 - C⁻¹) / 2 :=
    half_pos (sub_pos.mpr hgap)
  filter_upwards [eventually_tiltedUnitSpline_completeWeil_ground_near_pole hc hε,
    eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc] with N hspec hpos
  have hfloor : ∀ i, C⁻¹ ≤
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvalues i := by
    intro i
    have h := hspec.1 i
    change completedConductorEnergy tiltedUnitSpline c 1 -
      (completedConductorEnergy tiltedUnitSpline c 1 - C⁻¹) / 2 <
        (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvalues i at h
    linarith only [h, hgap]
  intro b
  refine ⟨?_, inverseQuadratic_le_of_squareMass_bound hpos hC0
    (squareMass_le_of_eigenvalue_floor
      (completeWeilMatrix_isHermitian tiltedUnitSpline c N) hC0 hfloor) b⟩
  simpa only [star_trivial] using hpos.inv.posSemidef.dotProduct_mulVec_nonneg b

/-- Every positive constant below the limiting cost is violated by an actual unit direction. -/
theorem eventually_tiltedWeil_inverse_cost_gt {c C : ℝ} (hc : 0 < c) (hC0 : 0 < C)
    (hC : C < tiltedWeilInverseCost c) :
    ∀ᶠ N : ℕ in atTop, ∃ b : PrimeHorizonIndex N → ℝ,
      b ⬝ᵥ b = 1 ∧ C < b ⬝ᵥ (completeWeilMatrix tiltedUnitSpline c N)⁻¹ *ᵥ b := by
  have hE := tiltedWeilGroundEnergy_pos hc
  have hgap : completedConductorEnergy tiltedUnitSpline c 1 < C⁻¹ := by
    exact (lt_inv_comm₀ hE hC0).mpr hC
  have hε : 0 < (C⁻¹ - completedConductorEnergy tiltedUnitSpline c 1) / 2 :=
    half_pos (sub_pos.mpr hgap)
  filter_upwards [eventually_tiltedUnitSpline_completeWeil_ground_near_pole hc hε,
    eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc] with N hspec hpos
  obtain ⟨i, hi⟩ := hspec.2
  obtain ⟨b, hb, he⟩ := inverse_eigenvector_unit_cost hpos i
  refine ⟨b, hb, ?_⟩
  rw [he]
  have hλ : hpos.isHermitian.eigenvalues i < C⁻¹ := by
    have hu := (abs_lt.mp hi).2
    change hpos.isHermitian.eigenvalues i - completedConductorEnergy tiltedUnitSpline c 1 <
      (C⁻¹ - completedConductorEnergy tiltedUnitSpline c 1) / 2 at hu
    linarith only [hu, hgap]
  exact (lt_inv_comm₀ hC0 (hpos.isHermitian.posDef_iff_eigenvalues_pos.mp hpos i)).mpr hλ

/-- Bounded moving overlap has one inverse cost and one horizon, for the literal complete source. -/
theorem exists_tiltedWeil_uniform_boundedOverlap_inverse_cost (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 0 < c → c ≤ K →
      ∀ b : PrimeHorizonIndex N → ℝ,
        0 ≤ b ⬝ᵥ (completeWeilMatrix tiltedUnitSpline c N)⁻¹ *ᵥ b ∧
          b ⬝ᵥ (completeWeilMatrix tiltedUnitSpline c N)⁻¹ *ᵥ b ≤ C * (b ⬝ᵥ b) := by
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_completeWeil_uniform_boundedOverlap_floor K
  refine ⟨e⁻¹, inv_pos.mpr he, ?_⟩
  filter_upwards [hfloor] with N hN
  intro c hc hcK b
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have hpos : (completeWeilMatrix tiltedUnitSpline c N).PosDef :=
    hA.posDef_iff_eigenvalues_pos.mpr fun i => he.trans_le (hN c hc hcK i)
  refine ⟨?_, inverseQuadratic_le_of_squareMass_bound hpos (inv_pos.mpr he)
    (squareMass_le_of_eigenvalue_floor hA (inv_pos.mpr he) ?_) b⟩
  · simpa only [star_trivial] using hpos.inv.posSemidef.dotProduct_mulVec_nonneg b
  · simpa only [inv_inv] using hN c hc hcK

#print axioms eventually_tiltedWeil_inverse_cost_le
#print axioms eventually_tiltedWeil_inverse_cost_gt
#print axioms exists_tiltedWeil_uniform_boundedOverlap_inverse_cost

end GaloisForLFunctions.CompletedArithmeticForms
