import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import Mathlib

/-!
# Large-system distinguishability of concrete bosonic-pair states

The large-`N` distinguishability mechanism in arXiv:2601.07437 is realized
using the corpus finite occupation tensor spaces. The actual Hilbert overlaps
are powers of a Hellinger affinity and converge to the equality indicator of
the thermal coordinate. This is a pointwise overlap limit, not an assertion
about a distributional delta function or convergence of changing Hilbert spaces.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- The thermal ratio labels each real inverse-scale parameter faithfully. -/
theorem thermalRatio_injective : Function.Injective thermalRatio := by
  intro a b h
  exact Real.exp_injective (neg_injective (Real.exp_injective h))

/-- Single-pair overlap between two thermal scales. -/
def radiationAffinity (tau sigma : ℝ) : ℝ :=
  geometricHellingerAffinity (thermalRatio tau) (thermalRatio sigma)

/-- Every finite-scale overlap is positive. -/
theorem radiationAffinity_pos (tau sigma : ℝ) : 0 < radiationAffinity tau sigma := by
  have ha0 := thermalRatio_pos tau
  have hb0 := thermalRatio_pos sigma
  have ha1 := thermalRatio_lt_one tau
  have hb1 := thermalRatio_lt_one sigma
  have hp : thermalRatio tau * thermalRatio sigma < 1 := by nlinarith
  have hs : Real.sqrt (thermalRatio tau * thermalRatio sigma) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one]
    nlinarith
  unfold radiationAffinity geometricHellingerAffinity
  apply div_pos
  · apply Real.sqrt_pos.mpr
    exact mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)
  · linarith

/-- The corpus Hellinger curvature bounds loss of thermal overlap. -/
theorem radiationAffinity_defect_bound (tau sigma : ℝ) :
    (Real.sqrt (thermalRatio tau) - Real.sqrt (thermalRatio sigma)) ^ (2 : ℕ) / 2 ≤
      1 - radiationAffinity tau sigma :=
  geometricHellinger_defect_ge (thermalRatio_pos tau).le (thermalRatio_lt_one tau)
    (thermalRatio_pos sigma).le (thermalRatio_lt_one sigma)

/-- Thermal overlap is at most one. -/
theorem radiationAffinity_le_one (tau sigma : ℝ) : radiationAffinity tau sigma ≤ 1 := by
  have h := radiationAffinity_defect_bound tau sigma
  nlinarith [sq_nonneg (Real.sqrt (thermalRatio tau) - Real.sqrt (thermalRatio sigma))]

/-- Unit overlap identifies exactly equal thermal scales. -/
theorem radiationAffinity_eq_one_iff (tau sigma : ℝ) :
    radiationAffinity tau sigma = 1 ↔ tau = sigma := by
  constructor
  · intro h
    have hb := radiationAffinity_defect_bound tau sigma
    have hs : Real.sqrt (thermalRatio tau) = Real.sqrt (thermalRatio sigma) := by
      nlinarith [sq_nonneg (Real.sqrt (thermalRatio tau) - Real.sqrt (thermalRatio sigma))]
    apply thermalRatio_injective
    have ha := Real.sq_sqrt (thermalRatio_pos tau).le
    have hc := Real.sq_sqrt (thermalRatio_pos sigma).le
    rw [hs] at ha
    exact ha.symm.trans hc
  · intro h
    subst sigma
    unfold radiationAffinity geometricHellingerAffinity
    rw [← sq, ← sq, Real.sqrt_sq (sub_nonneg.mpr (thermalRatio_lt_one tau).le),
      Real.sqrt_sq (thermalRatio_pos tau).le]
    exact div_self (ne_of_gt (sub_pos.mpr (thermalRatio_lt_one tau)))

/-- The actual `N`-pair state on the existing occupation Hilbert space. -/
def manyRadiation (N : ℕ) (tau : ℝ) : lp (fun _ : Fin N →₀ ℕ => ℂ) 2 :=
  HTGeometry.finiteOccupationNormalizedHalfDensity (fun _ => thermalRatio tau)
    (fun _ => (thermalRatio_pos tau).le) (fun _ => thermalRatio_lt_one tau)

/-- Every finite tensor size has a normalized state. -/
theorem manyRadiation_norm_sq (N : ℕ) (tau : ℝ) : ‖manyRadiation N tau‖ ^ (2 : ℕ) = 1 :=
  HTGeometry.norm_finiteOccupationNormalizedHalfDensity_sq _ _ _

/-- The actual many-pair overlap is the power of its local affinity. -/
theorem manyRadiation_overlap (N : ℕ) (tau sigma : ℝ) :
    inner ℂ (manyRadiation N tau) (manyRadiation N sigma) =
      (radiationAffinity tau sigma : ℂ) ^ N := by
  rw [manyRadiation, manyRadiation, inner_finiteOccupationNormalizedHalfDensity]
  simp [radiationAffinity]

/-- Distinct thermal coordinates become orthogonal in the large-system overlap limit. -/
theorem manyRadiation_classical_limit (tau sigma : ℝ) :
    Filter.Tendsto (fun N : ℕ => (inner ℂ (manyRadiation N tau) (manyRadiation N sigma)).re)
      Filter.atTop (nhds (if tau = sigma then 1 else 0)) := by
  simp only [manyRadiation_overlap, ← Complex.ofReal_pow, Complex.ofReal_re]
  by_cases h : tau = sigma
  · rw [if_pos h, (radiationAffinity_eq_one_iff tau sigma).mpr h]
    simp
  · rw [if_neg h]
    apply tendsto_pow_atTop_nhds_zero_of_lt_one (radiationAffinity_pos tau sigma).le
    exact lt_of_le_of_ne (radiationAffinity_le_one tau sigma)
      (fun he => h ((radiationAffinity_eq_one_iff tau sigma).mp he))

/-- Pure many-pair thermofield kernel attached to the occupation tensor state. -/
def manyRadiationPair (N : ℕ) (tau : ℝ) : (Fin N →₀ ℕ) × (Fin N →₀ ℕ) → ℂ :=
  thermofieldDiagonalKernel (manyRadiation N tau)

/-- All finite many-pair purifications are actual Hilbert--Schmidt states. -/
theorem manyRadiationPair_isHS (N : ℕ) (tau : ℝ) :
    HilbertSchmidt.IsHS (manyRadiationPair N tau) := thermofieldDiagonalKernel_isHS _

/-- Every collective diagonal energy is synchronized between the two partners. -/
theorem manyRadiationPair_stationary (N : ℕ) (tau : ℝ) (E : (Fin N →₀ ℕ) → ℂ) :
    thermofieldLeftAction E (manyRadiationPair N tau) -
      thermofieldRightAction E (manyRadiationPair N tau) = 0 := by
  rw [manyRadiationPair, thermofieldDiagonalKernel_central, sub_self]

end GaloisForLFunctions.HTGeometry.CPV
