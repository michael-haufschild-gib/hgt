import GaloisForLFunctions.RHTower.XiFiniteLocalSpectralFrameObstruction
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

/-!
# The canonical Hedenmalm orientation multiplier is forced to be singular

The horizontal derivative of the Xi modulus square has one canonical quotient by the Xi modulus
square: the sum of the two completed logarithmic derivatives on conjugate vertical lines.  This
file proves its exact real-frequency law, including at Xi zeros, and its uniqueness wherever the
Xi factor is nonzero.

At every positive aperture the canonical multiplier fails to be entire.  Otherwise it would give
an entire Hermitian-diagonal law and hence an impossible positive real-shift coboundary for the
completed Xi logarithmic flux.  This expresses the obstruction positively: any source-side
orientation must retain a non-entire transverse divisor singularity.
-/

open Complex Set

namespace RHTower

noncomputable section

def xiCanonicalHorizontalOrientationMultiplier (a : ℝ) (b : ℂ) : ℂ :=
  logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) + b * I) +
    logDeriv xi ((1 : ℂ) / 2 + (a : ℂ) - b * I)

theorem xiCanonicalHorizontalOrientationMultiplier_real_law
    (a b : ℝ) :
    deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) +
        xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          deriv xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) =
      xiCanonicalHorizontalOrientationMultiplier a (b : ℂ) *
        xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
          xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) := by
  let s : ℂ := (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I
  let t : ℂ := (1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I
  have ht : t = (starRingEnd ℂ) s := by
    dsimp [s, t]
    have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
      rw [map_div₀, map_one, map_ofNat]
    rw [map_add, map_add, map_mul, hhalf]
    simp
    ring
  by_cases hs : xi s = 0
  · have ht0 : xi t = 0 := by rw [ht, xi_conj, hs, map_zero]
    change deriv xi s * xi t + xi s * deriv xi t =
      xiCanonicalHorizontalOrientationMultiplier a (b : ℂ) * xi s * xi t
    rw [hs, ht0]
    ring
  · have htne : xi t ≠ 0 := by
      rw [ht, xi_conj]
      exact (map_ne_zero (starRingEnd ℂ)).2 hs
    dsimp [xiCanonicalHorizontalOrientationMultiplier, logDeriv]
    change deriv xi s * xi t + xi s * deriv xi t =
      (deriv xi s / xi s + deriv xi t / xi t) * xi s * xi t
    field_simp [hs, htne]

theorem xiCanonicalHorizontalOrientationMultiplier_unique_on_real
    {a : ℝ} {Q : ℂ → ℂ}
    (hlaw : ∀ b : ℝ,
      deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) +
          xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            deriv xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) =
        Q (b : ℂ) *
          xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
            xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I))
    {b : ℝ}
    (hb : xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) ≠ 0) :
    Q (b : ℂ) = xiCanonicalHorizontalOrientationMultiplier a (b : ℂ) := by
  have hminus : xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I) ≠ 0 := by
    have harg : (1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I =
        (starRingEnd ℂ) ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
      have hhalf : (starRingEnd ℂ) ((1 : ℂ) / 2) = (1 : ℂ) / 2 := by
        rw [map_div₀, map_one, map_ofNat]
      rw [map_add, map_add, map_mul, hhalf]
      simp
      ring
    rw [harg, xi_conj]
    exact (map_ne_zero (starRingEnd ℂ)).2 hb
  have hcanonical := xiCanonicalHorizontalOrientationMultiplier_real_law a b
  have hQ := hlaw b
  apply mul_right_cancel₀ (b :=
    xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) *
      xi ((1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I))
    (mul_ne_zero hb hminus)
  simpa only [mul_assoc] using hQ.symm.trans hcanonical

theorem not_differentiable_xiCanonicalHorizontalOrientationMultiplier
    {a : ℝ} (ha : 0 < a) :
    ¬ Differentiable ℂ (xiCanonicalHorizontalOrientationMultiplier a) := by
  intro hd
  exact no_XiEntireHermitianDiagonalLaw_of_pos ha
    ⟨xiCanonicalHorizontalOrientationMultiplier a,
      hd, xiCanonicalHorizontalOrientationMultiplier_real_law a⟩

theorem exists_not_analyticAt_xiCanonicalHorizontalOrientationMultiplier
    {a : ℝ} (ha : 0 < a) :
    ∃ b : ℂ,
      ¬ AnalyticAt ℂ (xiCanonicalHorizontalOrientationMultiplier a) b := by
  have hnot := not_differentiable_xiCanonicalHorizontalOrientationMultiplier ha
  by_contra h
  push Not at h
  exact hnot (fun b => (h b).differentiableAt)

end

end RHTower
