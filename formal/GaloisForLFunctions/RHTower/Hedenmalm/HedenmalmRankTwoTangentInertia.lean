import GaloisForLFunctions.HTGeometry.PureStateProjectorTangentInertia
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAutocorrelationPath

/-!
# Exact rank-two inertia of the Hedenmalm source tangent

The exponentially tilted theta source and its aperture tangent define two vectors in complex
`L²(ℝ)`.  They are unconditionally linearly independent: injectivity of the Schwartz-to-`L²`
map returns a putative relation to source space, where evaluation at two positive points and
strict positivity of the theta source force both coefficients to vanish.

The general pure-state projector-tangent law then gives an exact source-specific result.  On the
span of the source and tangent, the form matrix is Hermitian and nonsingular and has both signs.
Thus ambient positive-operator factorization is ruled out without adding a positivity or RH
hypothesis; only the distinguished momentum diagonal can carry the remaining orientation law.
-/

open Complex MeasureTheory
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- The right-line theta source as a vector of complex `L²(ℝ)`. -/
def thetaCuspRightLineSourceL2
    (a : ℝ) (ha : |a| < 1) : Lp (α := ℝ) ℂ 2 volume :=
  (thetaCuspRightLineSource a ha).toLp 2 volume

/-- The aperture tangent of the right-line theta source as a vector of complex `L²(ℝ)`. -/
def thetaCuspRightLineTangentL2
    (a : ℝ) (ha : |a| < 1) : Lp (α := ℝ) ℂ 2 volume :=
  (thetaCuspRightLineTangent a ha).toLp 2 volume

/-- Strict theta-source positivity discharges independence of the source and aperture tangent. -/
theorem thetaCuspRightLine_source_tangent_linearIndependent
    (a : ℝ) (ha : |a| < 1) :
    LinearIndependent ℂ
      ![thetaCuspRightLineSourceL2 a ha,
        thetaCuspRightLineTangentL2 a ha] := by
  rw [LinearIndependent.pair_iff]
  intro s t hrel
  have hschwartz :
      s • thetaCuspRightLineSource a ha +
          t • thetaCuspRightLineTangent a ha = 0 := by
    apply SchwartzMap.injective_toLp (F := ℂ) 2 (volume : Measure ℝ)
    simpa [thetaCuspRightLineSourceL2,
      thetaCuspRightLineTangentL2] using! hrel
  have h1 := congrArg (fun f : SchwartzMap ℝ ℂ => f 1) hschwartz
  have h2 := congrArg (fun f : SchwartzMap ℝ ℂ => f 2) hschwartz
  simp only [_root_.add_apply, _root_.smul_apply,
    thetaCuspRightLineTangent_apply, smul_eq_mul] at h1 h2
  change s * thetaCuspRightLineSource a ha 1 +
    t * (-(1 : ℂ) * thetaCuspRightLineSource a ha 1) = 0 at h1
  change s * thetaCuspRightLineSource a ha 2 +
    t * (-(2 : ℂ) * thetaCuspRightLineSource a ha 2) = 0 at h2
  have hu1 : thetaCuspRightLineSource a ha 1 ≠ 0 := by
    rw [thetaCuspRightLineSource_apply]
    exact_mod_cast mul_ne_zero (Real.exp_ne_zero _)
      (thetaCuspFullSource_pos_of_pos (by norm_num)).ne'
  have hu2 : thetaCuspRightLineSource a ha 2 ≠ 0 := by
    rw [thetaCuspRightLineSource_apply]
    exact_mod_cast mul_ne_zero (Real.exp_ne_zero _)
      (thetaCuspFullSource_pos_of_pos (by norm_num)).ne'
  have hst : s - t = 0 := by
    apply mul_right_cancel₀ hu1
    calc
      (s - t) * thetaCuspRightLineSource a ha 1 =
          s * thetaCuspRightLineSource a ha 1 +
            t * (-(1 : ℂ) * thetaCuspRightLineSource a ha 1) := by ring
      _ = 0 := h1
      _ = 0 * thetaCuspRightLineSource a ha 1 := by ring
  have hst2 : s - 2 * t = 0 := by
    apply mul_right_cancel₀ hu2
    calc
      (s - 2 * t) * thetaCuspRightLineSource a ha 2 =
          s * thetaCuspRightLineSource a ha 2 +
            t * (-(2 : ℂ) * thetaCuspRightLineSource a ha 2) := by ring
      _ = 0 := h2
      _ = 0 * thetaCuspRightLineSource a ha 2 := by ring
  constructor
  · linear_combination 2 * hst - hst2
  · linear_combination hst - hst2

/-- The theta source and tangent have strictly positive projective Gram/Fisher energy. -/
theorem thetaCuspRightLine_projectiveGramTangentEnergy_pos
    (a : ℝ) (ha : |a| < 1) :
    0 < HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (thetaCuspRightLineSourceL2 a ha)
      (thetaCuspRightLineTangentL2 a ha) :=
  (HTGeometry.projectiveGramTangentEnergy_pos_iff_linearIndependent_pair _ _).2
    (thetaCuspRightLine_source_tangent_linearIndependent a ha)

/-- The actual Hedenmalm source projector tangent has exact mixed signature for `|a| < 1`. -/
theorem thetaCuspRightLine_projectorTangentCompression_exact_mixed_signature
    (a : ℝ) (ha : |a| < 1) :
    let M := HTGeometry.pureStateProjectorTangentCompression
      (thetaCuspRightLineSourceL2 a ha)
      (thetaCuspRightLineTangentL2 a ha)
    M.IsHermitian ∧ M.det ≠ 0 ∧
      ¬ M.PosSemidef ∧ ¬ (-M).PosSemidef := by
  exact HTGeometry.pureStateProjectorTangentCompression_exact_mixed_signature
    (thetaCuspRightLine_source_tangent_linearIndependent a ha)

end

end RHTower
