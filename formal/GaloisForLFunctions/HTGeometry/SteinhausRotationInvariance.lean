import GaloisForLFunctions.HTGeometry.SteinhausComplexSum

/-!
# Rotation invariance of the Steinhaus sum

The diagonal translation of all phases preserves the product Haar measure and rotates the sum, so
the law of `Y = ∑ a_i ζ_i` is rotation invariant.  Together with the fact that the `K`-th roots of
unity form a `2π/K`-net of the unit circle, this bounds the mass of an annulus by `K` times the
mass of a single ball, which is what the large-deviation lower bound needs.
-/

open MeasureTheory Filter Topology Complex

namespace HTGeometry

local instance phaseCirclePositiveRot : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

variable {ι : Type*} [Fintype ι]

theorem steinhausSum_add_const (a : ι → ℝ) (x : ι → PhaseCircle) (s : ℝ) :
    steinhausSum a (fun i => x i + (s : PhaseCircle))
      = Complex.exp (s * Complex.I) * steinhausSum a x := by
  rw [steinhausSum, steinhausSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [steinhausPhase_add_coe]
  ring

/-- **The law of the Steinhaus sum is rotation invariant.** -/
theorem measure_steinhausSum_rot (a : ι → ℝ) {S : Set ℂ} (hS : MeasurableSet S) (s : ℝ) :
    (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x | Complex.exp (s * Complex.I) * steinhausSum a x ∈ S}
      = (Measure.pi fun _ : ι => AddCircle.haarAddCircle) {x | steinhausSum a x ∈ S} := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  have hmp : MeasurePreserving (fun x : ι → PhaseCircle => fun i => x i + (s : PhaseCircle)) μ μ :=
    measurePreserving_add_right μ (fun _ => (s : PhaseCircle))
  have hmeas : MeasurableSet {x : ι → PhaseCircle | steinhausSum a x ∈ S} := by
    refine hS.preimage ?_
    refine Measurable.comp' ?_ measurable_id
    exact (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (continuous_steinhausPhase.comp (continuous_apply i))).measurable
  have hpre := hmp.measure_preimage hmeas.nullMeasurableSet
  have hset : (fun x : ι → PhaseCircle => fun i => x i + (s : PhaseCircle)) ⁻¹'
      {x : ι → PhaseCircle | steinhausSum a x ∈ S}
      = {x | Complex.exp (s * Complex.I) * steinhausSum a x ∈ S} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, steinhausSum_add_const]
  rw [← hset, hpre]

theorem norm_exp_ofReal_mul_I_sub_one_le (s : ℝ) :
    ‖Complex.exp ((s : ℂ) * Complex.I) - 1‖ ≤ |s| := by
  have h1 : Complex.exp ((s : ℂ) * Complex.I) - 1
      = ((Real.cos s - 1 : ℝ) : ℂ) + ((Real.sin s : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    push_cast
    ring
  rw [h1, Complex.norm_add_mul_I]
  have hcos : Real.cos s = 1 - 2 * Real.sin (s / 2) ^ (2 : ℕ) := by
    have h := Real.sin_sq_eq_half_sub (s / 2)
    rw [show 2 * (s / 2) = s by ring] at h
    linarith
  have hpyth := Real.sin_sq_add_cos_sq s
  have hid : (Real.cos s - 1) ^ (2 : ℕ) + Real.sin s ^ (2 : ℕ) = (2 * |Real.sin (s / 2)|) ^ (2 : ℕ) := by
    rw [mul_pow, sq_abs, hcos]
    nlinarith only [hpyth, hcos]
  rw [hid, Real.sqrt_sq (by positivity)]
  have hs : |Real.sin (s / 2)| ≤ |s / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hs
  linarith

/-- **The `K`-th roots of unity are a `2π/K`-net of the unit circle.** -/
theorem exists_angle_close {K : ℕ} (hK : 0 < K) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ∃ k < K, ‖ζ - Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I)‖
      ≤ 2 * Real.pi / K := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set φ : ℝ := Complex.arg ζ with hφ
  have hφ1 : -Real.pi < φ := Complex.neg_pi_lt_arg ζ
  have hφ2 : φ ≤ Real.pi := Complex.arg_le_pi ζ
  set t : ℝ := (φ + Real.pi) / (2 * Real.pi) with ht
  have ht0 : 0 < t := by rw [ht]; have : 0 < φ + Real.pi := by linarith
                         positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    linarith
  have hφt : φ = 2 * Real.pi * t - Real.pi := by
    rw [ht]
    field_simp
    ring
  clear_value t
  have htK : 0 < t * K := by positivity
  set k : ℕ := ⌈t * (K : ℝ)⌉₊ - 1 with hk
  have hceil1 : 1 ≤ ⌈t * (K : ℝ)⌉₊ := Nat.one_le_ceil_iff.2 htK
  have hceilK : ⌈t * (K : ℝ)⌉₊ ≤ K := by
    refine Nat.ceil_le.2 ?_
    push_cast
    nlinarith only [ht1, hKR]
  have hkK : k < K := by omega
  refine ⟨k, hkK, ?_⟩
  set θ : ℝ := -Real.pi + 2 * Real.pi * k / K with hθ
  have hkcast : ((k : ℝ)) = (⌈t * (K : ℝ)⌉₊ : ℝ) - 1 := by
    rw [hk]
    have : (1 : ℕ) ≤ ⌈t * (K : ℝ)⌉₊ := hceil1
    push_cast [Nat.cast_sub this]
    ring
  have hdiff : φ - θ = 2 * Real.pi / K * (t * K - ((⌈t * (K : ℝ)⌉₊ : ℝ) - 1)) := by
    rw [hθ, hφt, hkcast]
    field_simp
    ring
  have hlow : 0 ≤ t * K - ((⌈t * (K : ℝ)⌉₊ : ℝ) - 1) := by
    have := Nat.ceil_lt_add_one htK.le
    linarith
  have hhigh : t * K - ((⌈t * (K : ℝ)⌉₊ : ℝ) - 1) ≤ 1 := by
    have := Nat.le_ceil (t * (K : ℝ))
    linarith
  have habs : |φ - θ| ≤ 2 * Real.pi / K := by
    rw [hdiff, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi / K),
      abs_of_nonneg hlow]
    nlinarith only [hhigh, hpi, hKR, (by positivity : (0:ℝ) < 2 * Real.pi / K)]
  have hζeq : ζ = Complex.exp ((φ : ℝ) * Complex.I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ] at this
    rw [← this, hφ]
    simp
  rw [hζeq]
  have hfact : Complex.exp ((φ : ℝ) * Complex.I) - Complex.exp ((θ : ℝ) * Complex.I)
      = Complex.exp ((θ : ℝ) * Complex.I) * (Complex.exp (((φ - θ : ℝ)) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfact, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsq : ‖Complex.exp (((φ - θ : ℝ)) * Complex.I) - 1‖ ≤ |φ - θ| :=
    norm_exp_ofReal_mul_I_sub_one_le (φ - θ)
  linarith [hsq, habs]


/-- **The annulus is covered by finitely many rotations of a ball.** -/
theorem annulus_subset_iUnion_balls {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) {K : ℕ}
    (hK : 0 < K) (hKb : 4 * Real.pi * ‖z‖ / r < K) :
    {w : ℂ | ‖z‖ ≤ ‖w‖ ∧ ‖w‖ ≤ ‖z‖ + r / 2}
      ⊆ ⋃ k ∈ Finset.range K,
          Metric.ball (Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z) r := by
  intro w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hz0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hw0 : (0 : ℝ) < ‖w‖ := lt_of_lt_of_le hz0 hw1
  have hwne : w ≠ 0 := norm_pos_iff.1 hw0
  set ζ : ℂ := (w * (starRingEnd ℂ) z) / ((‖w‖ : ℂ) * (‖z‖ : ℂ)) with hζdef
  have hζnorm : ‖ζ‖ = 1 := by
    rw [hζdef, norm_div, norm_mul, norm_mul, RCLike.norm_conj]
    simp [hw0.ne', hz0.ne']
  have hζz : ζ * z = ((‖z‖ / ‖w‖ : ℝ) : ℂ) * w := by
    have hzz : (starRingEnd ℂ) z * z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      push_cast
      ring
    rw [hζdef, div_mul_eq_mul_div, mul_assoc, hzz]
    push_cast
    field_simp
  have hdist1 : ‖w - ζ * z‖ ≤ r / 2 := by
    rw [hζz]
    have hid : w - ((‖z‖ / ‖w‖ : ℝ) : ℂ) * w = ((1 - ‖z‖ / ‖w‖ : ℝ) : ℂ) * w := by
      push_cast
      ring
    rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hfrac : 0 ≤ 1 - ‖z‖ / ‖w‖ := by
      rw [sub_nonneg, div_le_one hw0]
      exact hw1
    rw [abs_of_nonneg hfrac]
    have : (1 - ‖z‖ / ‖w‖) * ‖w‖ = ‖w‖ - ‖z‖ := by field_simp
    rw [this]
    linarith
  obtain ⟨k, hk, hkclose⟩ := exists_angle_close hK ζ hζnorm
  refine Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  have hdist2 : ‖ζ * z - Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z‖
      ≤ (2 * Real.pi / K) * ‖z‖ := by
    rw [← sub_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right hkclose (norm_nonneg z)
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hsmall : (2 * Real.pi / K) * ‖z‖ < r / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hKR]
    rw [div_lt_iff₀ hr] at hKb
    nlinarith only [hKb, hr]
  calc ‖w - Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z‖
      ≤ ‖w - ζ * z‖
        + ‖ζ * z - Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < r := by linarith [hdist1, hdist2, hsmall]

end

end HTGeometry

