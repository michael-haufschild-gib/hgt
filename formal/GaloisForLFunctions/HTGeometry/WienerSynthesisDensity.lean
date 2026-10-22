import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFlowPointwise
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# From weighted data to an integrable density

An element of the weighted space is a bounded continuous `G`, standing for the frequency density
`⟨ξ⟩⁻ᴺG(ξ)`. To read that density as a function of space one integrates it against the character,
and the integral converges as soon as the weight beats the dimension:

`∫ ⟨ξ⟩ʲ⁻ᴺ dξ < ∞` whenever `dim E < N - j`.

Each derivative taken under the frequency integral — in time or in space — costs one power of `⟨ξ⟩`,
so `j` counts the derivatives the synthesis can afford. Two in time and two in space is `j = 2`,
which is why the construction asks for `N > dim E + 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-! ## The tail of the weight is integrable -/

/-- **A negative power of the frequency beyond the dimension is integrable.** -/
theorem integrable_kgFreq_inv_pow {m : ℕ} (hm : (Module.finrank ℝ E : ℝ) < m) :
    Integrable (fun ξ : E => (kgFreq ξ ^ m)⁻¹) (volume : Measure E) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := E) (μ := (volume : Measure E))
    (r := (m : ℝ)) hm
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  have hbase : (0 : ℝ) < 1 + ‖ξ‖ ^ 2 := by positivity
  have hrw : ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(m : ℝ) / 2) = (kgFreq ξ ^ m)⁻¹ := by
    rw [kgFreq_eq_rpow, ← Real.rpow_natCast (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ)) m,
      ← Real.rpow_mul hbase.le, ← Real.rpow_neg hbase.le]
    congr 1
    ring
  exact hrw

/-! ## The density of a weighted datum -/

/-- The frequency density represented by a weighted datum. -/
noncomputable def kgWeighted (N : ℕ) (G : E →ᵇ ℂ) (ξ : E) : ℂ := ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * G ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgWeighted_le (N : ℕ) (G : E →ᵇ ℂ) (ξ : E) :
    ‖kgWeighted N G ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * ‖G‖ := by
  have hpos : (0 : ℝ) < kgFreq ξ ^ N := pow_pos (kgFreq_pos ξ) N
  rw [kgWeighted, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left (G.norm_coe_le_norm ξ) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgWeighted (N : ℕ) (G : E →ᵇ ℂ) : Continuous (kgWeighted N G) := by
  refine Continuous.mul ?_ G.continuous
  refine Continuous.inv₀ (Complex.continuous_ofReal.comp (continuous_kgFreq.pow N)) fun ξ => ?_
  exact Complex.ofReal_ne_zero.mpr (pow_pos (kgFreq_pos ξ) N).ne'

/-- **The density carries as many derivatives as the weight exceeds the dimension.** -/
theorem integrable_kgFreq_pow_mul_kgWeighted {j m : ℕ} (hm : (Module.finrank ℝ E : ℝ) < m)
    (G : E →ᵇ ℂ) :
    Integrable (fun ξ : E => kgFreq ξ ^ j * ‖kgWeighted (j + m) G ξ‖) (volume : Measure E) := by
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := E) hm).const_mul ‖G‖)
    (((continuous_kgFreq.pow j).mul
      ((continuous_kgWeighted (j + m) G).norm)).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hj : (0 : ℝ) < kgFreq ξ ^ j := pow_pos (kgFreq_pos ξ) j
  have hm' : (0 : ℝ) < kgFreq ξ ^ m := pow_pos (kgFreq_pos ξ) m
  have hsplit : (kgFreq ξ ^ (j + m))⁻¹ = (kgFreq ξ ^ j)⁻¹ * (kgFreq ξ ^ m)⁻¹ := by
    rw [pow_add, mul_inv]
  have hbound := norm_kgWeighted_le (j + m) G ξ
  have hstep : kgFreq ξ ^ j * ‖kgWeighted (j + m) G ξ‖
      ≤ kgFreq ξ ^ j * ((kgFreq ξ ^ (j + m))⁻¹ * ‖G‖) :=
    mul_le_mul_of_nonneg_left hbound hj.le
  have hfinal : kgFreq ξ ^ j * ((kgFreq ξ ^ (j + m))⁻¹ * ‖G‖) = ‖G‖ * (kgFreq ξ ^ m)⁻¹ := by
    rw [hsplit]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc kgFreq ξ ^ j * ‖kgWeighted (j + m) G ξ‖
      ≤ kgFreq ξ ^ j * ((kgFreq ξ ^ (j + m))⁻¹ * ‖G‖) := hstep
    _ = ‖G‖ * (kgFreq ξ ^ m)⁻¹ := hfinal

/-- In particular the density itself is integrable. -/
theorem integrable_kgWeighted {m : ℕ} (hm : (Module.finrank ℝ E : ℝ) < m) (G : E →ᵇ ℂ) :
    Integrable (kgWeighted m G) (volume : Measure E) := by
  have h := integrable_kgFreq_pow_mul_kgWeighted (E := E) (j := 0) hm G
  simp only [pow_zero, one_mul, zero_add] at h
  exact (integrable_norm_iff (continuous_kgWeighted m G).aestronglyMeasurable).mp h

/-- **A weight beaten by more than the dimension is integrable against `j` derivatives.** -/
theorem integrable_kgFreq_pow_mul_inv_pow {j m : ℕ} (h : (Module.finrank ℝ E : ℝ) + j < m) :
    Integrable (fun ξ : E => kgFreq ξ ^ j * (kgFreq ξ ^ m)⁻¹) (volume : Measure E) := by
  have hjm : j < m := by
    have hj : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have : (j : ℝ) < m := by linarith
    exact_mod_cast this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m = j + k := ⟨m - j, by omega⟩
  subst hk
  have hkdim : (Module.finrank ℝ E : ℝ) < k := by
    push_cast at h
    linarith
  refine (integrable_kgFreq_inv_pow (E := E) hkdim).congr
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hj : (0 : ℝ) < kgFreq ξ ^ j := pow_pos (kgFreq_pos ξ) j
  have hkpos : (0 : ℝ) < kgFreq ξ ^ k := pow_pos (kgFreq_pos ξ) k
  show (kgFreq ξ ^ k)⁻¹ = kgFreq ξ ^ j * (kgFreq ξ ^ (j + k))⁻¹
  rw [pow_add, mul_inv]
  field_simp

/-- **The density carries `j` derivatives whenever the weight beats the dimension by `j`.** -/
theorem integrable_kgFreq_pow_mul_kgWeighted' {j m : ℕ} (h : (Module.finrank ℝ E : ℝ) + j < m)
    (G : E →ᵇ ℂ) :
    Integrable (fun ξ : E => kgFreq ξ ^ j * ‖kgWeighted m G ξ‖) (volume : Measure E) := by
  refine Integrable.mono' ((integrable_kgFreq_pow_mul_inv_pow (E := E) h).mul_const ‖G‖)
    (((continuous_kgFreq.pow j).mul ((continuous_kgWeighted m G).norm)).aestronglyMeasurable) ?_
  filter_upwards with ξ
  have hj : (0 : ℝ) < kgFreq ξ ^ j := pow_pos (kgFreq_pos ξ) j
  have hbound := norm_kgWeighted_le m G ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc kgFreq ξ ^ j * ‖kgWeighted m G ξ‖
      ≤ kgFreq ξ ^ j * ((kgFreq ξ ^ m)⁻¹ * ‖G‖) := mul_le_mul_of_nonneg_left hbound hj.le
    _ = kgFreq ξ ^ j * (kgFreq ξ ^ m)⁻¹ * ‖G‖ := by ring

end GaloisForLFunctions.HTGeometry
