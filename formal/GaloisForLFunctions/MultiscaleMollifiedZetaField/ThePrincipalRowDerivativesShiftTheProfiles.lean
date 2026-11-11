import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedPrincipalRowIsAProfileProduct

/-!
# Directional derivatives of the principal harmonic row

A power-shift derivative multiplies a mollifier profile by `1−x`.
A diagonal-shift derivative inserts the normalized harmonic logarithm.
The finite-sum derivative identity therefore stays inside the same
polynomial-profile family, at every logarithmic weight.
-/

open Filter Set Topology
open RHTower.Sieve

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Multiplication by the complementary logarithmic coordinate. -/
def logComplementProfile (P : ℝ → ℝ) (x : ℝ) : ℝ := (1 - x) * P x

/-- Differentiating the coefficient power replaces the profile by `(1−x)P`. -/
theorem hasDerivAt_shiftedProfileWeight (P : ℝ → ℝ) (N n : ℕ) (v : ℝ) :
    HasDerivAt (fun y => shiftedProfileWeight P N y n)
      (shiftedProfileWeight (logComplementProfile P) N v n) v := by
  have he : HasDerivAt (fun y : ℝ => Real.exp (y * Real.log n / Real.log N))
      (Real.exp (v * Real.log n / Real.log N) * (Real.log n / Real.log N)) v := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id v).mul_const (Real.log n)).div_const (Real.log N)).exp
  apply (he.mul_const (P (1 - Real.log n / Real.log N))).congr_deriv
  simp only [shiftedProfileWeight, logComplementProfile]
  ring

/-- The arithmetic Möbius transform commutes with the profile-shifting derivative. -/
theorem hasDerivAt_selbergMoebiusWeightedSum_shiftedProfile (P : ℝ → ℝ) (N q : ℕ) (v : ℝ) :
    HasDerivAt (fun y => selbergMoebiusWeightedSum (shiftedProfileWeight P N y) N q)
      (selbergMoebiusWeightedSum (shiftedProfileWeight (logComplementProfile P) N v) N q) v := by
  have hterm (n : ℕ) := (hasDerivAt_shiftedProfileWeight P N (q * n) v).const_mul
    (selbergMoebiusReciprocalCoeff n)
  simpa only [selbergMoebiusWeightedSum] using
    HasDerivAt.fun_sum (u := Finset.Icc 1 (N / q)) (fun n _ => hterm n)

/-- A directional derivative changes only the logarithmic power and the two profiles. -/
theorem hasDerivAt_shiftedProfileHarmonicRow_direction
    (P Q : ℝ → ℝ) (N a b k : ℕ) (c v κ ν z : ℝ) :
    HasDerivAt (fun y => shiftedProfileHarmonicRow P Q N a b (c + κ * y) (v + ν * y) k)
      (κ * shiftedProfileHarmonicRow P Q N a b (c + κ * z) (v + ν * z) (k + 1) +
        ν * shiftedProfileHarmonicRow (logComplementProfile P) Q N a b (c + κ * z) (v + ν * z) k +
        ν * shiftedProfileHarmonicRow P (logComplementProfile Q) N a b (c + κ * z) (v + ν * z) k) z := by
  have hterm (d : ℕ) : HasDerivAt (fun y : ℝ =>
      (Real.log d / Real.log N) ^ k * Real.exp ((c + κ * y) * (Real.log d / Real.log N)) *
        (selbergMoebiusWeightedSum (shiftedProfileWeight P N (v + ν * y)) N (a * d) *
          selbergMoebiusWeightedSum (shiftedProfileWeight Q N (v + ν * y)) N (b * d)) / d)
      (κ * ((Real.log d / Real.log N) ^ (k + 1) * Real.exp ((c + κ * z) * (Real.log d / Real.log N)) *
        (selbergMoebiusWeightedSum (shiftedProfileWeight P N (v + ν * z)) N (a * d) *
          selbergMoebiusWeightedSum (shiftedProfileWeight Q N (v + ν * z)) N (b * d)) / d) +
        ν * ((Real.log d / Real.log N) ^ k * Real.exp ((c + κ * z) * (Real.log d / Real.log N)) *
        (selbergMoebiusWeightedSum (shiftedProfileWeight (logComplementProfile P) N (v + ν * z)) N (a * d) *
          selbergMoebiusWeightedSum (shiftedProfileWeight Q N (v + ν * z)) N (b * d)) / d) +
        ν * ((Real.log d / Real.log N) ^ k * Real.exp ((c + κ * z) * (Real.log d / Real.log N)) *
        (selbergMoebiusWeightedSum (shiftedProfileWeight P N (v + ν * z)) N (a * d) *
          selbergMoebiusWeightedSum (shiftedProfileWeight (logComplementProfile Q) N (v + ν * z)) N (b * d)) / d)) z := by
    have he : HasDerivAt (fun y : ℝ => Real.exp ((c + κ * y) * (Real.log d / Real.log N)))
        (Real.exp ((c + κ * z) * (Real.log d / Real.log N)) * (κ * (Real.log d / Real.log N))) z := by
      simpa only [id_eq, mul_one] using
        ((((hasDerivAt_id z).const_mul κ).const_add c).mul_const (Real.log d / Real.log N)).exp
    have hP : HasDerivAt (fun y : ℝ =>
        selbergMoebiusWeightedSum (shiftedProfileWeight P N (v + ν * y)) N (a * d))
        (selbergMoebiusWeightedSum (shiftedProfileWeight (logComplementProfile P) N (v + ν * z)) N (a * d) * ν) z := by
      simpa only [id_eq, mul_one, Function.comp_def] using
        (hasDerivAt_selbergMoebiusWeightedSum_shiftedProfile P N (a * d) (v + ν * z)).comp z
          (((hasDerivAt_id z).const_mul ν).const_add v)
    have hQ : HasDerivAt (fun y : ℝ =>
        selbergMoebiusWeightedSum (shiftedProfileWeight Q N (v + ν * y)) N (b * d))
        (selbergMoebiusWeightedSum (shiftedProfileWeight (logComplementProfile Q) N (v + ν * z)) N (b * d) * ν) z := by
      simpa only [id_eq, mul_one, Function.comp_def] using
        (hasDerivAt_selbergMoebiusWeightedSum_shiftedProfile Q N (b * d) (v + ν * z)).comp z
          (((hasDerivAt_id z).const_mul ν).const_add v)
    apply (((he.const_mul ((Real.log d / Real.log N) ^ k)).mul (hP.mul hQ)).div_const (d : ℝ)).congr_deriv
    simp only [Pi.mul_apply]
    rw [pow_succ]
    ring
  have hh := (HasDerivAt.fun_sum (u := Finset.Icc 1 (N / max a b)) (fun d _ => hterm d)).const_mul (Real.log N)
  apply hh.congr_deriv
  simp only [shiftedProfileHarmonicRow, Finset.sum_add_distrib, ← Finset.mul_sum] <;> ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
