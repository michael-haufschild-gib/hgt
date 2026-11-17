import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TwoSupportProbeRigidity

/-!
# Normal modes of the arithmetic two-probe energy

Diagonal normalization produces symmetric and antisymmetric stiffnesses
`1 + c` and `1 - c`. Their sharp bounds and equality cases follow from
two-probe positivity; the soft mode vanishes exactly at node collision.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
open ProbeCuts

/-- Positive normalization of a single arithmetic probe. -/
def probeAmplitude (s : ℝ) : ℝ := Real.sqrt (safeProbeEntry s s)

private theorem probeAmplitude_pos (s : ℝ) : 0 < probeAmplitude s :=
  Real.sqrt_pos.mpr (probeEntry_pos s s)

private theorem probeAmplitude_sq (s : ℝ) : probeAmplitude s ^ 2 = safeProbeEntry s s :=
  Real.sq_sqrt (probeEntry_pos s s).le

/-- Correlation of two probes after normalizing their diagonal energies. -/
def probeCorrelation (s t : ℝ) : ℝ :=
  safeProbeEntry s t / (probeAmplitude s * probeAmplitude t)

/-- Two-probe energy expressed in normalized amplitudes. -/
def normalizedProbeEnergy (s t u v : ℝ) : ℝ :=
  twoProbeQuadratic s t (u / probeAmplitude s) (v / probeAmplitude t)

theorem probeCorrelation_pos (s t : ℝ) : 0 < probeCorrelation s t :=
  div_pos (probeEntry_pos s t) (mul_pos (probeAmplitude_pos s) (probeAmplitude_pos t))

private theorem normalizedProbeEnergy_formula (s t u v : ℝ) :
    normalizedProbeEnergy s t u v = u ^ 2 + v ^ 2 + 2 * probeCorrelation s t * u * v := by
  unfold normalizedProbeEnergy twoProbeQuadratic probeCorrelation
  rw [← probeAmplitude_sq s, ← probeAmplitude_sq t]
  field_simp [(probeAmplitude_pos s).ne', (probeAmplitude_pos t).ne']
  ring

/-- The symmetric and antisymmetric coordinates diagonalize the actual two-probe energy. -/
theorem normalizedProbeEnergy_modes (s t u v : ℝ) :
    normalizedProbeEnergy s t u v =
      ((1 + probeCorrelation s t) / 2) * (u + v) ^ 2 +
      ((1 - probeCorrelation s t) / 2) * (u - v) ^ 2 := by
  rw [normalizedProbeEnergy_formula]
  ring

/-- Positivity bounds every normalized arithmetic correlation by one. -/
theorem probeCorrelation_le_one (s t : ℝ) : probeCorrelation s t ≤ 1 := by
  have h := twoProbeQuadratic_nonneg s t (1 / probeAmplitude s) (-1 / probeAmplitude t)
  change 0 ≤ normalizedProbeEnergy s t 1 (-1) at h
  rw [normalizedProbeEnergy_formula] at h
  linarith only [h]

/-- The antisymmetric stiffness vanishes exactly when the two probe nodes collide. -/
theorem probeCorrelation_eq_one_iff (s t : ℝ) :
    probeCorrelation s t = 1 ↔ node s = node t := by
  constructor
  · intro h
    have hz : normalizedProbeEnergy s t 1 (-1) = 0 := by
      rw [normalizedProbeEnergy_formula, h]
      norm_num
    have hk := (twoProbeQuadratic_zero_iff s t
      (1 / probeAmplitude s) (-1 / probeAmplitude t)).mp hz
    by_contra hst
    rw [if_neg hst] at hk
    exact (div_ne_zero one_ne_zero (probeAmplitude_pos s).ne') hk.1
  · intro hst
    have ha : probeAmplitude s = probeAmplitude t := by
      unfold probeAmplitude safeProbeEntry
      rw [hst]
    have hz : normalizedProbeEnergy s t 1 (-1) = 0 := by
      apply (twoProbeQuadratic_zero_iff s t _ _).mpr
      rw [if_pos hst, ha]
      ring
    rw [normalizedProbeEnergy_formula] at hz
    linarith only [hz]

/-- The smaller mode gives the sharp lower energy bound. -/
theorem normalizedProbeEnergy_lower (s t u v : ℝ) :
    (1 - probeCorrelation s t) * (u ^ 2 + v ^ 2) ≤ normalizedProbeEnergy s t u v := by
  rw [normalizedProbeEnergy_formula]
  have h := mul_nonneg (probeCorrelation_pos s t).le (sq_nonneg (u + v))
  nlinarith only [h]

/-- The larger mode gives the sharp upper energy bound. -/
theorem normalizedProbeEnergy_upper (s t u v : ℝ) :
    normalizedProbeEnergy s t u v ≤ (1 + probeCorrelation s t) * (u ^ 2 + v ^ 2) := by
  rw [normalizedProbeEnergy_formula]
  have h := mul_nonneg (probeCorrelation_pos s t).le (sq_nonneg (u - v))
  nlinarith only [h]

/-- Equality in the lower bound picks out the antisymmetric mode exactly. -/
theorem normalizedProbeEnergy_lower_eq_iff (s t u v : ℝ) :
    normalizedProbeEnergy s t u v = (1 - probeCorrelation s t) * (u ^ 2 + v ^ 2) ↔
      u + v = 0 := by
  rw [normalizedProbeEnergy_formula]
  have hp := probeCorrelation_pos s t
  constructor
  · intro h
    have hz : probeCorrelation s t * (u + v) ^ 2 = 0 := by nlinarith only [h]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hp.ne')
  · intro h
    have huv : u = -v := by linarith only [h]
    rw [huv]
    ring

/-- Equality in the upper bound picks out the symmetric mode exactly. -/
theorem normalizedProbeEnergy_upper_eq_iff (s t u v : ℝ) :
    normalizedProbeEnergy s t u v = (1 + probeCorrelation s t) * (u ^ 2 + v ^ 2) ↔
      u - v = 0 := by
  rw [normalizedProbeEnergy_formula]
  have hp := probeCorrelation_pos s t
  constructor
  · intro h
    have hz : probeCorrelation s t * (u - v) ^ 2 = 0 := by nlinarith only [h]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hp.ne')
  · intro h
    have huv := sub_eq_zero.mp h
    rw [huv]
    ring

/-- The product of the mode stiffnesses is the normalized arithmetic Gram determinant. -/
theorem probe_mode_stiffness_product (s t : ℝ) :
    (1 - probeCorrelation s t) * (1 + probeCorrelation s t) =
      (safeProbeEntry s s * safeProbeEntry t t - safeProbeEntry s t ^ 2) /
        (safeProbeEntry s s * safeProbeEntry t t) := by
  unfold probeCorrelation
  rw [← probeAmplitude_sq s, ← probeAmplitude_sq t]
  field_simp [(probeAmplitude_pos s).ne', (probeAmplitude_pos t).ne']
  ring

#print axioms normalizedProbeEnergy_modes
#print axioms probeCorrelation_le_one
#print axioms probeCorrelation_eq_one_iff
#print axioms normalizedProbeEnergy_lower
#print axioms normalizedProbeEnergy_upper
#print axioms normalizedProbeEnergy_lower_eq_iff
#print axioms normalizedProbeEnergy_upper_eq_iff
#print axioms probe_mode_stiffness_product
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
