import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TwoProbeNormalModes
import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing

/-!
# Cauchy dephasing of arithmetic normal modes

Normalized inverse Jordan smoothing multiplies the arithmetic correlation
by its exact Cauchy coherence. Symmetric and antisymmetric modes persist;
a null mode survives precisely when both probe nodes and rates collide.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
open HilbertMetric.CauchyDephasing

/-- Arithmetic correlation after normalized inverse Jordan smoothing. -/
def dephasedProbeCorrelation (s t a b : ℝ) : ℝ := coherence a b * probeCorrelation s t

/-- Normalized two-probe energy after a Cauchy dephasing step. -/
def dephasedTwoProbeEnergy (s t a b u v : ℝ) : ℝ :=
  u ^ 2 + v ^ 2 + 2 * dephasedProbeCorrelation s t a b * u * v

private theorem dephasedProbeCorrelation_pos (s t a b : ℝ) :
    0 < dephasedProbeCorrelation s t a b :=
  mul_pos (coherence_pos a b) (probeCorrelation_pos s t)

theorem dephasedProbeCorrelation_le_one (s t a b : ℝ) :
    dephasedProbeCorrelation s t a b ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (probeCorrelation_le_one s t)
    (coherence_pos a b).le).trans (by simpa only [mul_one] using coherence_le_one a b)

/-- Complete correlation survives exactly a simultaneous physical-node and rate collision. -/
theorem dephasedProbeCorrelation_eq_one_iff (s t a b : ℝ) :
    dephasedProbeCorrelation s t a b = 1 ↔ node s = node t ∧ a = b := by
  constructor
  · intro h
    have hc := probeCorrelation_le_one s t
    have hq := coherence_le_one a b
    have hp := coherence_pos a b
    have heq : coherence a b = 1 := by
      apply le_antisymm hq
      have hm := mul_le_mul_of_nonneg_left hc hp.le
      change dephasedProbeCorrelation s t a b ≤ coherence a b * 1 at hm
      simpa only [h, mul_one] using hm
    have hec : probeCorrelation s t = 1 := by
      simpa only [dephasedProbeCorrelation, heq, one_mul] using h
    exact ⟨(probeCorrelation_eq_one_iff s t).mp hec,
      (coherence_eq_one_iff a b).mp heq⟩
  · rintro ⟨hc, rfl⟩
    rw [dephasedProbeCorrelation, coherence_self, one_mul,
      (probeCorrelation_eq_one_iff s t).mpr hc]

/-- Cauchy smoothing preserves the symmetric and antisymmetric normal modes exactly. -/
theorem dephasedTwoProbeEnergy_modes (s t a b u v : ℝ) :
    dephasedTwoProbeEnergy s t a b u v =
      (1 + dephasedProbeCorrelation s t a b) / 2 * (u + v) ^ 2 +
      (1 - dephasedProbeCorrelation s t a b) / 2 * (u - v) ^ 2 := by
  unfold dephasedTwoProbeEnergy
  ring

/-- Dephasing interpolates the actual normalized Weil energy with its diagonal part. -/
theorem dephasedTwoProbeEnergy_interpolation (s t a b u v : ℝ) :
    dephasedTwoProbeEnergy s t a b u v =
      coherence a b * normalizedProbeEnergy s t u v +
        (1 - coherence a b) * (u ^ 2 + v ^ 2) := by
  rw [normalizedProbeEnergy_modes]
  unfold dephasedTwoProbeEnergy dephasedProbeCorrelation
  ring

/-- The exact stiffness bounds control all coefficient directions. -/
theorem dephasedTwoProbeEnergy_bounds (s t a b u v : ℝ) :
    (1 - dephasedProbeCorrelation s t a b) * (u ^ 2 + v ^ 2) ≤
        dephasedTwoProbeEnergy s t a b u v ∧
      dephasedTwoProbeEnergy s t a b u v ≤
        (1 + dephasedProbeCorrelation s t a b) * (u ^ 2 + v ^ 2) := by
  have hp := (dephasedProbeCorrelation_pos s t a b).le
  constructor
  · have h := mul_nonneg hp (sq_nonneg (u + v))
    unfold dephasedTwoProbeEnergy
    nlinarith only [h]
  · have h := mul_nonneg hp (sq_nonneg (u - v))
    unfold dephasedTwoProbeEnergy
    nlinarith only [h]

/-- The determinant is strictly positive precisely when at least one collision is separated. -/
theorem dephased_probe_determinant_pos_iff (s t a b : ℝ) :
    0 < 1 - dephasedProbeCorrelation s t a b ^ 2 ↔
      node s ≠ node t ∨ a ≠ b := by
  have hp := dephasedProbeCorrelation_pos s t a b
  have hle := dephasedProbeCorrelation_le_one s t a b
  have he : 0 < 1 - dephasedProbeCorrelation s t a b ^ 2 ↔
      dephasedProbeCorrelation s t a b ≠ 1 := by
    constructor
    · intro h hz
      rw [hz] at h
      norm_num at h
    · intro h
      have hlt := lt_of_le_of_ne hle (Ne.symm h)
      nlinarith only [hp, hlt, mul_pos (sub_pos.mpr hlt) (by linarith only [hp] :
        0 < 1 + dephasedProbeCorrelation s t a b)]
  rw [he, ne_eq, dephasedProbeCorrelation_eq_one_iff, not_and_or]

/-- The only surviving null direction comes from simultaneous node and rate collision. -/
theorem dephasedTwoProbeEnergy_zero_iff (s t a b u v : ℝ) :
    dephasedTwoProbeEnergy s t a b u v = 0 ↔
      if node s = node t ∧ a = b then u + v = 0 else u = 0 ∧ v = 0 := by
  classical
  have hp := dephasedProbeCorrelation_pos s t a b
  have hle := dephasedProbeCorrelation_le_one s t a b
  by_cases hc : node s = node t ∧ a = b
  · rw [if_pos hc, dephasedTwoProbeEnergy_modes,
      (dephasedProbeCorrelation_eq_one_iff s t a b).mpr hc]
    simp only [show (1 + 1 : ℝ) / 2 = 1 by norm_num, sub_self, zero_div,
      zero_mul, add_zero, one_mul, sq_eq_zero_iff]
  · rw [if_neg hc]
    have hlt : dephasedProbeCorrelation s t a b < 1 :=
      lt_of_le_of_ne hle (Ne.symm (fun h => hc
        ((dephasedProbeCorrelation_eq_one_iff s t a b).mp h)))
    constructor
    · intro h
      rw [dephasedTwoProbeEnergy_modes] at h
      have hplus : 0 < (1 + dephasedProbeCorrelation s t a b) / 2 := by
        exact div_pos (by linarith only [hp]) (by norm_num)
      have hminus : 0 < (1 - dephasedProbeCorrelation s t a b) / 2 :=
        div_pos (sub_pos.mpr hlt) (by norm_num)
      have hsum := mul_nonneg hplus.le (sq_nonneg (u + v))
      have hdiff := mul_nonneg hminus.le (sq_nonneg (u - v))
      have heplus : (1 + dephasedProbeCorrelation s t a b) / 2 * (u + v) ^ 2 = 0 := by
        linarith only [h, hsum, hdiff]
      have heminus : (1 - dephasedProbeCorrelation s t a b) / 2 * (u - v) ^ 2 = 0 := by
        linarith only [h, hsum, hdiff]
      have hu := sq_eq_zero_iff.mp ((mul_eq_zero.mp heplus).resolve_left hplus.ne')
      have hv := sq_eq_zero_iff.mp ((mul_eq_zero.mp heminus).resolve_left hminus.ne')
      constructor <;> linarith only [hu, hv]
    · rintro ⟨rfl, rfl⟩
      simp only [dephasedTwoProbeEnergy, zero_pow (by decide : 2 ≠ 0),
        add_zero, mul_zero]

#print axioms dephasedProbeCorrelation_eq_one_iff
#print axioms dephasedTwoProbeEnergy_modes
#print axioms dephasedTwoProbeEnergy_interpolation
#print axioms dephasedTwoProbeEnergy_bounds
#print axioms dephased_probe_determinant_pos_iff
#print axioms dephasedTwoProbeEnergy_zero_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.Pick
