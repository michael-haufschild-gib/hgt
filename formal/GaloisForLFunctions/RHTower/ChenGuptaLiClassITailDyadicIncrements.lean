/-
# Chen--Gupta--Li Class-I dyadic tail increments

Canonical power-of-two tail prefixes telescope into finite dyadic increments.
This turns CGL's large infinite tail alternative into a closed finite dyadic
witness, before identifying each increment with a character-row polynomial.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailDyadicPrefixes

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- The shifted detector tail has zero coefficient at zero. -/
theorem cglShiftedDetectorTailCoefficient_zero
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    cglShiftedDetectorTailCoefficient X q χ s 0 = 0 := by
  simp [cglShiftedDetectorTailCoefficient, cglDetectorTailCoefficient,
    cglUnitCoefficient, LSeries.convolution_map_zero]

/-- The shifted detector tail has zero unit coefficient. -/
theorem cglShiftedDetectorTailCoefficient_one
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1)) (s : CGLRightHalfPlanePoint) :
    cglShiftedDetectorTailCoefficient X q χ s 1 = 0 := by
  simp [cglShiftedDetectorTailCoefficient, cglDetectorTailCoefficient_one]

/-- The initial power-of-two shifted-tail prefix is zero. -/
theorem cglShiftedDetectorTailDyadicPrefix_zero
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    cglShiftedDetectorTailDyadicPrefix X q χ s x 0 = 0 := by
  unfold cglShiftedDetectorTailDyadicPrefix cglShiftedDetectorTailPartialProfile
  norm_num [Finset.sum_range_succ, cglShiftedDetectorTailCoefficient_zero,
    cglShiftedDetectorTailCoefficient_one]

/-- The literal finite CGL tail increment between consecutive power-of-two
prefix endpoints. It is supported on the corresponding dyadic annulus. -/
def cglShiftedDetectorTailDyadicIncrement
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (L : ℕ) : ℂ :=
  cglShiftedDetectorTailDyadicPrefix X q χ s x (L + 1) -
    cglShiftedDetectorTailDyadicPrefix X q χ s x L

/-- Canonical CGL power-of-two prefixes telescope exactly into their finite
dyadic increments. -/
theorem cglShiftedDetectorTailDyadicPrefix_eq_sum_increment
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (L : ℕ) :
    cglShiftedDetectorTailDyadicPrefix X q χ s x L =
      ∑ r ∈ Finset.range L, cglShiftedDetectorTailDyadicIncrement X q χ s x r := by
  induction L with
  | zero => simp [cglShiftedDetectorTailDyadicPrefix_zero]
  | succ L ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold cglShiftedDetectorTailDyadicIncrement
      ring

/-- Each canonical CGL tail increment is exactly the literal finite sum on
its dyadic annulus `2^L < n ≤ 2^(L+1)`. -/
theorem cglShiftedDetectorTailDyadicIncrement_eq_block
    (X q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) (L : ℕ) :
    cglShiftedDetectorTailDyadicIncrement X q χ s x L =
      ∑ j ∈ Finset.range (2 ^ L),
        cglShiftedDetectorTailCoefficient X q χ s (2 ^ L + j + 1) *
          Complex.exp (-(((2 ^ L + j + 1 : ℕ) : ℝ) * x.1 : ℝ)) := by
  unfold cglShiftedDetectorTailDyadicIncrement
    cglShiftedDetectorTailDyadicPrefix cglShiftedDetectorTailPartialProfile
  have hpow : 2 ^ (L + 1) + 1 = 2 ^ L * 2 + 1 := by
    rw [pow_succ]
  rw [hpow, ← Finset.sum_Ico_eq_sub]
  · rw [Finset.sum_Ico_eq_sum_range]
    have hlen : 2 ^ L * 2 + 1 - (2 ^ L + 1) = 2 ^ L := by omega
    rw [hlen]
    apply Finset.sum_congr rfl
    intro j hj
    have hidx : 2 ^ L + 1 + j = 2 ^ L + j + 1 := by omega
    rw [hidx]
  · omega

/-- **Chen--Gupta--Li, Section 12.1: finite dyadic-increment alternative.**
Every certified primitive Class-I zero forces either a finite canonical CGL
tail increment to be large, with the explicit dyadic-depth loss, or the
normalized critical-line Mellin integral to be large. -/
theorem cglPrimitiveClassI_dyadicIncrement_or_safeLineIntegral_large
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    (∃ L : ℕ, ∃ r : Fin L,
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ)) ≤
        ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1
          (cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z)
          ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩ r.1‖) ∨
      Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 2 ≤
        ‖(1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
          cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
            (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
            ((2 : ℂ) + (t : ℂ) * I))‖ := by
  let s : CGLRightHalfPlanePoint :=
    cglPrimitiveClassIWindowZeroRightHalfPlanePoint n χ τ H z
  let x : CGLPositiveSmoothingScale := ⟨((Y + 1 : ℕ) : ℝ)⁻¹, by positivity⟩
  rcases cglPrimitiveClassI_dyadicPrefix_or_safeLineIntegral_large X n Y χ τ H z with ⟨L, hlarge⟩ | hsafe
  · left
    have hLne : L ≠ 0 := by
      intro hL
      subst L
      rw [cglShiftedDetectorTailDyadicPrefix_zero] at hlarge
      simp only [norm_zero] at hlarge
      have hpos : 0 < Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by positivity
      linarith
    refine ⟨L, ?_⟩
    by_contra h
    push Not at h
    change ∀ r : Fin L,
      ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x r.1‖ <
        Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ)) at h
    have hsum_lt :
        ∑ j ∈ Finset.range L, ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x j‖ <
          Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
      calc
        ∑ j ∈ Finset.range L, ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x j‖ <
            ∑ _j ∈ Finset.range L,
              Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ)) := by
          apply Finset.sum_lt_sum
          · intro j hj
            exact (h ⟨j, Finset.mem_range.mp hj⟩).le
          · refine ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hLne), ?_⟩
            exact h ⟨0, Nat.pos_of_ne_zero hLne⟩
        _ = (L : ℝ) * (Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / (4 * (L : ℝ))) := by simp
        _ = Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 := by
          have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hLne
          field_simp
    have hnorm : ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖ ≤
        ∑ j ∈ Finset.range L, ‖cglShiftedDetectorTailDyadicIncrement X n χ.1.1 s x j‖ := by
      rw [cglShiftedDetectorTailDyadicPrefix_eq_sum_increment]
      exact norm_sum_le _ _
    change Real.exp (-(((Y + 1 : ℕ) : ℝ)⁻¹)) / 4 ≤
      ‖cglShiftedDetectorTailDyadicPrefix X n χ.1.1 s x L‖ at hlarge
    linarith
  · exact Or.inr hsafe

end RHTower
