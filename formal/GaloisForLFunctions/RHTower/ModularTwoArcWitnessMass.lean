import GaloisForLFunctions.RHTower.ModularTwoArcWitness
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The two-arc witness has no logarithmic tail and a positive Mellin value at `s = 1`

Every generator profile has the same leading term:
`𝒦_c(v) = 2 (cosh v)^{−1/2} + R_c(v)` with `0 ≤ R_c(v) ≤ (2√2/y)(cosh v)^{−5/2}`
(`symCoshKernel_sub_nonneg`, `symCoshKernel_sub_le`), and `R_c(v)` increases with `|c|` at every
`v` (`symCoshKernel_le_of_abs_le'`, `symCoshKernel_lt_of_abs_lt'`).

The two-arc witness `h` is a difference of two superpositions of total mass one, so the common
term `2(cosh v)^{−1/2}`, which carries the `1/|x|` tail of each superposition, cancels:

* `abs_twoArcProfile_le`: `|e^{v/2} h(e^v)| ≤ C (cosh v)^{−5/2}`; the log profile decays like
  `e^{−5|v|/2}`, so `h` is integrable and its Mellin transform has no pole at `s = 1`.
* `twoArcMellinOne_pos`: `∫ e^{v/2} · e^{v/2} h(e^v) dv = ∫₀^∞ h(x) dx > 0`.  With
  `ρ(c) = ∫ e^{v/2} R_c(v) dv`, the value is `2^{−1/2}(⟨ρ⟩_S − ⟨ρ⟩_A)`, and side-arc points have
  `|c| ≥ ½ ≥ |c|` of bottom-arc points, strictly on a set of positive measure.

So the witness is integer-blind, self-reciprocal, strictly positive definite, decays at rate
`5/2` in the log variable, and has `∫₀^∞ h > 0`.  A decay-class (N1) witness in the sense of the
twisted-arc reduction is the same object with `∫₀^∞ h = 0`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Pointwise structure of the generator profiles -/

theorem symCoshTerm_le_of_abs_le {c c' : ℝ} (h : |c'| ≤ |c|) (j : ℕ) (v : ℝ) :
    symCoshTerm c' j v ≤ symCoshTerm c j v := by
  unfold symCoshTerm
  have h1 := choose_neg_half_even_pos j
  have h2 := pow_two_mul_le_of_abs_le h j
  have h3 : 0 ≤ Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := Real.rpow_nonneg (Real.cosh_pos v).le _
  have h4 : 0 ≤ 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) := by positivity
  calc 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c' ^ (2 * j) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))
      = (2 * Ring.choose (-1 / 2 : ℝ) (2 * j)) * c' ^ (2 * j) *
          Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := rfl
    _ ≤ (2 * Ring.choose (-1 / 2 : ℝ) (2 * j)) * c ^ (2 * j) *
          Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := by gcongr

/-- **Pointwise monotonicity of `𝒦_c(v)` in `|c|`.** -/
theorem symCoshKernel_le_of_abs_le' {c c' : ℝ} (hc : |c| < 1) (h : |c'| ≤ |c|) (v : ℝ) :
    symCoshKernel c' v ≤ symCoshKernel c v :=
  hasSum_le (fun j => symCoshTerm_le_of_abs_le h j v)
    (hasSum_symCoshKernel (lt_of_le_of_lt h hc) v) (hasSum_symCoshKernel hc v)

/-- **Strict pointwise monotonicity of `𝒦_c(v)` in `|c|`.** -/
theorem symCoshKernel_lt_of_abs_lt' {c c' : ℝ} (hc : |c| < 1) (h : |c'| < |c|) (v : ℝ) :
    symCoshKernel c' v < symCoshKernel c v := by
  refine hasSum_lt (i := 1) (fun j => symCoshTerm_le_of_abs_le h.le j v) ?_
    (hasSum_symCoshKernel (lt_trans h hc) v) (hasSum_symCoshKernel hc v)
  unfold symCoshTerm
  have h1 := choose_neg_half_even_pos 1
  have h3 : 0 < Real.cosh v ^ (-(1 / 2 + 2 * ((1 : ℕ) : ℝ) : ℝ)) :=
    Real.rpow_pos_of_pos (Real.cosh_pos v) _
  have h2 : c' ^ (2 * 1) < c ^ (2 * 1) := by
    rw [mul_one, ← sq_abs c', ← sq_abs c]
    exact pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
  have h4 : 0 < 2 * Ring.choose (-1 / 2 : ℝ) (2 * 1) := by positivity
  have := mul_lt_mul_of_pos_left h2 h4
  exact mul_lt_mul_of_pos_right this h3

theorem symCoshTerm_zero (c v : ℝ) :
    symCoshTerm c 0 v = 2 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  simp [symCoshTerm]

/-- `𝒦_c(v) ≥ 2 (cosh v)^{−1/2}`. -/
theorem symCoshKernel_sub_nonneg {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    0 ≤ symCoshKernel c v - 2 * Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have h0 : HasSum (fun j : ℕ => if j = 0 then 2 * Real.cosh v ^ (-(1 / 2) : ℝ) else 0)
      (2 * Real.cosh v ^ (-(1 / 2) : ℝ)) := hasSum_ite_eq 0 _
  have hle := hasSum_le (fun j => ?_) h0 (hasSum_symCoshKernel hc v)
  · linarith
  · split_ifs with hj
    · rw [hj, symCoshTerm_zero]
    · exact symCoshTerm_nonneg c j v

/-- **The tail of a generator profile.**
`𝒦_c(v) − 2(cosh v)^{−1/2} ≤ (𝒦_c(0) − 2)(cosh v)^{−5/2}`. -/
theorem symCoshKernel_sub_le_zero {c : ℝ} (hc : |c| < 1) (v : ℝ) :
    symCoshKernel c v - 2 * Real.cosh v ^ (-(1 / 2) : ℝ) ≤
      (symCoshKernel c 0 - 2) * Real.cosh v ^ (-(5 / 2) : ℝ) := by
  have hA := hasSum_symCoshKernel hc 0
  have hA' : HasSum (fun j => symCoshTerm c j 0 * Real.cosh v ^ (-(5 / 2) : ℝ))
      (symCoshKernel c 0 * Real.cosh v ^ (-(5 / 2) : ℝ)) := hA.mul_right _
  have hI : HasSum (fun j : ℕ => if j = 0 then
      2 * (Real.cosh v ^ (-(1 / 2) : ℝ) - Real.cosh v ^ (-(5 / 2) : ℝ)) else 0)
      (2 * (Real.cosh v ^ (-(1 / 2) : ℝ) - Real.cosh v ^ (-(5 / 2) : ℝ))) := hasSum_ite_eq 0 _
  have hT := hA'.add hI
  have hle := hasSum_le (fun j => ?_) (hasSum_symCoshKernel hc v) hT
  · linarith
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [symCoshTerm_zero, Real.cosh_zero, Real.one_rpow, mul_one, if_true]
      ring_nf
      linarith
    · rw [if_neg hj.ne', add_zero]
      unfold symCoshTerm
      simp only [Real.cosh_zero, Real.one_rpow, mul_one]
      have h1 := choose_neg_half_even_pos j
      have hc2 : 0 ≤ c ^ (2 * j) := by rw [pow_mul]; positivity
      have hpow : Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) ≤ Real.cosh v ^ (-(5 / 2) : ℝ) :=
        cosh_rpow_neg_le_of_le (by
          have : (1 : ℝ) ≤ j := by exact_mod_cast hj
          linarith) v
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- `𝒦_c(0) ≤ 2√2/y` on the unit circle. -/
theorem symCoshKernel_zero_le {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) (hy : 0 < y) :
    symCoshKernel c 0 ≤ 2 * Real.sqrt 2 / y := by
  have h := symCoshKernel_le_of_circle hcy hy 0
  simpa using h

/-- **Tail bound.**  `0 ≤ 𝒦_c(v) − 2(cosh v)^{−1/2} ≤ (2√2/y)(cosh v)^{−5/2}`. -/
theorem symCoshKernel_sub_le {c y : ℝ} (hcy : c ^ 2 + y ^ 2 = 1) (hy : 0 < y) (v : ℝ) :
    symCoshKernel c v - 2 * Real.cosh v ^ (-(1 / 2) : ℝ) ≤
      2 * Real.sqrt 2 / y * Real.cosh v ^ (-(5 / 2) : ℝ) := by
  have hc : |c| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  refine (symCoshKernel_sub_le_zero hc v).trans ?_
  have h5 : 0 ≤ Real.cosh v ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (Real.cosh_pos v).le _
  have h0 := symCoshKernel_zero_le hcy hy
  nlinarith

/-! ### Superpositions -/

/-- The residual profile `R_c(v) = 𝒦_c(v) − 2(cosh v)^{−1/2}`. -/
def symCoshResidual (c v : ℝ) : ℝ := symCoshKernel c v - 2 * Real.cosh v ^ (-(1 / 2) : ℝ)

theorem exp_half_mul_cosh_rpow_le (v : ℝ) :
    Real.exp (v / 2) * Real.cosh v ^ (-(5 / 2) : ℝ) ≤ Real.sqrt 2 * Real.cosh v ^ (-(2 : ℝ)) := by
  have hc := Real.cosh_pos v
  calc Real.exp (v / 2) * Real.cosh v ^ (-(5 / 2) : ℝ)
      ≤ Real.sqrt 2 * Real.cosh v ^ (1 / 2 : ℝ) * Real.cosh v ^ (-(5 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_right (exp_half_le_sqrt_two_mul v) (Real.rpow_nonneg hc.le _)
    _ = Real.sqrt 2 * Real.cosh v ^ (-(2 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hc]; norm_num

variable {X : Type*} [MeasurableSpace X] {κ : Measure X} {c y : X → ℝ}

theorem measurable_symCoshKernel_prod (h : CircleData κ c y) :
    Measurable fun q : ℝ × X => symCoshKernel (c q.2) q.1 := by
  simp only [symCoshKernel]
  have hc : Measurable fun q : ℝ × X => c q.2 := h.meas_c.comp measurable_snd
  have hch : Measurable fun q : ℝ × X => Real.cosh q.1 := Real.measurable_cosh.comp measurable_fst
  exact ((hch.add hc).pow_const _).add ((hch.sub hc).pow_const _)

theorem integrable_symCoshKernel_comp [IsFiniteMeasure κ] (h : CircleData κ c y) (v : ℝ) :
    Integrable (fun p => symCoshKernel (c p) v) κ := by
  have hm : Measurable fun p => symCoshKernel (c p) v := by
    simp only [symCoshKernel]
    have hch : Measurable fun _ : X => Real.cosh v := measurable_const
    exact ((hch.add h.meas_c).pow_const _).add ((hch.sub h.meas_c).pow_const _)
  refine ((h.integrable_one_add.const_mul (2 * Real.sqrt 2 * Real.cosh v ^ (-(1 / 2) : ℝ)))).mono'
    hm.aestronglyMeasurable ?_
  filter_upwards [h.circle, h.pos] with p hcp hp
  have hc1 : |c p| ≤ 1 := by rw [abs_le]; constructor <;> nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (symCoshKernel_nonneg hc1 v)]
  calc symCoshKernel (c p) v ≤ 2 * Real.sqrt 2 / y p * Real.cosh v ^ (-(1 / 2) : ℝ) :=
        symCoshKernel_le_of_circle hcp hp v
    _ = 2 * Real.sqrt 2 * Real.cosh v ^ (-(1 / 2) : ℝ) * (1 / y p) := by ring
    _ ≤ 2 * Real.sqrt 2 * Real.cosh v ^ (-(1 / 2) : ℝ) * (1 + 1 / y p ^ 2) := by
        gcongr; exact inv_le_one_add_inv_sq hp

/-- The superposed residual: `∫ 𝒦_c(v) dκ = 2(cosh v)^{−1/2} κ(X) + ∫ R_c(v) dκ`. -/
theorem integral_symCoshKernel_eq [IsFiniteMeasure κ] (h : CircleData κ c y) (v : ℝ) :
    ∫ p, symCoshKernel (c p) v ∂κ =
      2 * Real.cosh v ^ (-(1 / 2) : ℝ) * κ.real univ + ∫ p, symCoshResidual (c p) v ∂κ := by
  unfold symCoshResidual
  rw [integral_sub (integrable_symCoshKernel_comp h v) (integrable_const _), integral_const,
    smul_eq_mul]
  ring

theorem abs_integral_symCoshResidual_le [IsFiniteMeasure κ] (h : CircleData κ c y) (v : ℝ) :
    |∫ p, symCoshResidual (c p) v ∂κ| ≤
      (∫ p, 2 * Real.sqrt 2 / y p ∂κ) * Real.cosh v ^ (-(5 / 2) : ℝ) := by
  have hint : Integrable (fun p => 2 * Real.sqrt 2 / y p) κ := by
    refine (h.integrable_one_add.const_mul (2 * Real.sqrt 2)).mono'
      ((measurable_const.div h.meas_y).aestronglyMeasurable) ?_
    filter_upwards [h.pos] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 2 * Real.sqrt 2 / y p = 2 * Real.sqrt 2 * (1 / y p) := by ring
      _ ≤ 2 * Real.sqrt 2 * (1 + 1 / y p ^ 2) := by
        gcongr; exact inv_le_one_add_inv_sq hp
  rw [← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => abs_nonneg _) (hint.mul_const _) ?_)
  filter_upwards [h.circle, h.pos] with p hcp hp
  have hc : |c p| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  unfold symCoshResidual
  rw [abs_of_nonneg (symCoshKernel_sub_nonneg hc v)]
  exact symCoshKernel_sub_le hcp hp v

/-! ### The residual Mellin value -/

theorem measurable_symCoshResidual (c : ℝ) : Measurable (symCoshResidual c) := by
  unfold symCoshResidual symCoshKernel
  have hch := Real.measurable_cosh
  exact (((hch.add_const c).pow_const _).add ((hch.sub_const c).pow_const _)).sub
    ((hch.pow_const _).const_mul 2)

/-- `ρ(c) = ∫ e^{v/2} R_c(v) dv`. -/
def residualMellin (c : ℝ) : ℝ := ∫ v, Real.exp (v / 2) * symCoshResidual c v

theorem integrable_exp_half_mul_symCoshResidual {c : ℝ} (hc : |c| < 1) :
    Integrable fun v => Real.exp (v / 2) * symCoshResidual c v := by
  have hI := (_root_.HTGeometry.integrable_cosh_rpow_neg (s := 2) (by norm_num)).const_mul
    ((symCoshKernel c 0 - 2) * Real.sqrt 2)
  refine hI.mono' (((Real.measurable_exp.comp (measurable_id.div_const 2)).mul
    (measurable_symCoshResidual c)).aestronglyMeasurable) (Eventually.of_forall fun v => ?_)
  have hR := symCoshKernel_sub_nonneg hc v
  have hR' := symCoshKernel_sub_le_zero hc v
  have hK0 : 0 ≤ symCoshKernel c 0 - 2 := by
    have := symCoshKernel_sub_nonneg hc 0; simpa using this
  have he := exp_half_mul_cosh_rpow_le v
  unfold symCoshResidual
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hR)]
  calc Real.exp (v / 2) * (symCoshKernel c v - 2 * Real.cosh v ^ (-(1 / 2) : ℝ))
      ≤ Real.exp (v / 2) * ((symCoshKernel c 0 - 2) * Real.cosh v ^ (-(5 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR' (Real.exp_pos _).le
    _ = (symCoshKernel c 0 - 2) * (Real.exp (v / 2) * Real.cosh v ^ (-(5 / 2) : ℝ)) := by ring
    _ ≤ (symCoshKernel c 0 - 2) * (Real.sqrt 2 * Real.cosh v ^ (-(2 : ℝ))) :=
        mul_le_mul_of_nonneg_left he hK0
    _ = (symCoshKernel c 0 - 2) * Real.sqrt 2 * Real.cosh v ^ (-(2 : ℝ)) := by ring

/-- `ρ` is monotone in `|c|`. -/
theorem residualMellin_le_of_abs_le {c c' : ℝ} (hc : |c| < 1) (h : |c'| ≤ |c|) :
    residualMellin c' ≤ residualMellin c := by
  refine integral_mono (integrable_exp_half_mul_symCoshResidual (lt_of_le_of_lt h hc))
    (integrable_exp_half_mul_symCoshResidual hc) fun v => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  unfold symCoshResidual
  linarith [symCoshKernel_le_of_abs_le' hc h v]

/-- `ρ` is strictly monotone in `|c|`. -/
theorem residualMellin_lt_of_abs_lt {c c' : ℝ} (hc : |c| < 1) (h : |c'| < |c|) :
    residualMellin c' < residualMellin c := by
  have i1 := integrable_exp_half_mul_symCoshResidual (lt_trans h hc)
  have i2 := integrable_exp_half_mul_symCoshResidual hc
  have hpos : 0 < ∫ v, (Real.exp (v / 2) * symCoshResidual c v -
      Real.exp (v / 2) * symCoshResidual c' v) := by
    have hpt : ∀ v, 0 < Real.exp (v / 2) * symCoshResidual c v -
        Real.exp (v / 2) * symCoshResidual c' v := fun v => by
      rw [← mul_sub]
      refine mul_pos (Real.exp_pos _) ?_
      unfold symCoshResidual
      linarith [symCoshKernel_lt_of_abs_lt' hc h v]
    refine (integral_pos_iff_support_of_nonneg (fun v => (hpt v).le) (i2.sub i1)).mpr ?_
    have : Function.support (fun v => Real.exp (v / 2) * symCoshResidual c v -
        Real.exp (v / 2) * symCoshResidual c' v) = univ :=
      eq_univ_of_forall fun v => (hpt v).ne'
    rw [this, Real.volume_univ]
    exact ENNReal.zero_lt_top
  rw [integral_sub i2 i1] at hpos
  unfold residualMellin
  linarith

variable {X : Type*} [MeasurableSpace X] {κ : Measure X} {c y : X → ℝ}

theorem integrable_exp_half_mul_symCoshResidual_prod [IsFiniteMeasure κ] (h : CircleData κ c y) :
    Integrable (fun q : ℝ × X => Real.exp (q.1 / 2) * symCoshResidual (c q.2) q.1)
      (volume.prod κ) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 2) (by norm_num)
  have hFmeas : Measurable fun q : ℝ × X =>
      Real.exp (q.1 / 2) * symCoshResidual (c q.2) q.1 := by
    unfold symCoshResidual
    have hch : Measurable fun q : ℝ × X => Real.cosh q.1 :=
      Real.measurable_cosh.comp measurable_fst
    exact (Real.measurable_exp.comp (measurable_fst.div_const 2)).mul
      ((measurable_symCoshKernel_prod h).sub ((hch.pow_const _).const_mul 2))
  have hb : Integrable (fun q : ℝ × X =>
      Real.cosh q.1 ^ (-(2 : ℝ)) * (Real.sqrt 2 * (2 * Real.sqrt 2) * (1 + 1 / y q.2 ^ 2)))
      (volume.prod κ) :=
    hI.mul_prod (h.integrable_one_add.const_mul (Real.sqrt 2 * (2 * Real.sqrt 2)))
  refine hb.mono' hFmeas.aestronglyMeasurable ?_
  have hae := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := κ)).ae
    (h.circle.and h.pos)
  filter_upwards [hae] with q hq
  obtain ⟨hcq, hyq⟩ := hq
  have hc : |c q.2| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hR := symCoshKernel_sub_nonneg hc q.1
  have hR' := symCoshKernel_sub_le hcq hyq q.1
  have he := exp_half_mul_cosh_rpow_le q.1
  have hy1 := inv_le_one_add_inv_sq hyq
  have hch : 0 ≤ Real.cosh q.1 ^ (-(2 : ℝ)) := Real.rpow_nonneg (Real.cosh_pos _).le _
  unfold symCoshResidual
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hR)]
  calc Real.exp (q.1 / 2) * (symCoshKernel (c q.2) q.1 - 2 * Real.cosh q.1 ^ (-(1 / 2) : ℝ))
      ≤ Real.exp (q.1 / 2) * (2 * Real.sqrt 2 / y q.2 * Real.cosh q.1 ^ (-(5 / 2) : ℝ)) :=
        mul_le_mul_of_nonneg_left hR' (Real.exp_pos _).le
    _ = 2 * Real.sqrt 2 * (1 / y q.2) *
          (Real.exp (q.1 / 2) * Real.cosh q.1 ^ (-(5 / 2) : ℝ)) := by ring
    _ ≤ 2 * Real.sqrt 2 * (1 + 1 / y q.2 ^ 2) * (Real.sqrt 2 * Real.cosh q.1 ^ (-(2 : ℝ))) := by
        gcongr
    _ = Real.cosh q.1 ^ (-(2 : ℝ)) * (Real.sqrt 2 * (2 * Real.sqrt 2) * (1 + 1 / y q.2 ^ 2)) := by
        ring

/-- The residual Mellin value of a superposition: `∫ e^{v/2} ∫ R_c(v) dκ dv = ∫ ρ(c) dκ`. -/
theorem integral_exp_half_mul_integral_symCoshResidual [IsFiniteMeasure κ]
    (h : CircleData κ c y) :
    ∫ v, Real.exp (v / 2) * ∫ p, symCoshResidual (c p) v ∂κ = ∫ p, residualMellin (c p) ∂κ := by
  have hswap := integral_integral_swap
    (f := fun v p => Real.exp (v / 2) * symCoshResidual (c p) v)
    (integrable_exp_half_mul_symCoshResidual_prod h)
  unfold residualMellin
  rw [← hswap]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [integral_const_mul]

theorem integrable_exp_half_mul_integral_symCoshResidual [IsFiniteMeasure κ]
    (h : CircleData κ c y) :
    Integrable fun v => Real.exp (v / 2) * ∫ p, symCoshResidual (c p) v ∂κ := by
  refine (integrable_exp_half_mul_symCoshResidual_prod h).integral_prod_left.congr
    (Eventually.of_forall fun v => ?_)
  simp only
  rw [integral_const_mul]

theorem integrable_residualMellin [IsFiniteMeasure κ] (h : CircleData κ c y) :
    Integrable (fun p => residualMellin (c p)) κ :=
  (integrable_exp_half_mul_symCoshResidual_prod h).integral_prod_right

/-! ### Side and bottom residual values -/

theorem sideResidualMellin_ge {s : ArcParam} (hs : (s : ℝ) ≠ 0) :
    residualMellin (1 / 2) ≤ residualMellin (sidePointRe s) := by
  have h1 : |(s : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [s.2.1], s.2.2⟩
  have hp := abs_pos.mpr hs
  have hc : |sidePointRe s| < 1 := by
    unfold sidePointRe; rw [abs_lt]; constructor <;> linarith [abs_nonneg (s : ℝ)]
  refine residualMellin_le_of_abs_le hc ?_
  unfold sidePointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (by linarith)]
  linarith

theorem sideResidualMellin_gt {s : ArcParam} (hs : (s : ℝ) ≠ 0) (hs2 : |(s : ℝ)| < 1 / 2) :
    residualMellin (1 / 2) < residualMellin (sidePointRe s) := by
  have hp := abs_pos.mpr hs
  have hc : |sidePointRe s| < 1 := by
    unfold sidePointRe; rw [abs_lt]; constructor <;> linarith [abs_nonneg (s : ℝ)]
  refine residualMellin_lt_of_abs_lt hc ?_
  unfold sidePointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (by linarith)]
  linarith

theorem arcResidualMellin_le (u : ArcParam) :
    residualMellin (arcPointRe u) ≤ residualMellin (1 / 2) := by
  refine residualMellin_le_of_abs_le (by norm_num) ?_
  unfold arcPointRe
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩

/-! ### The two-arc witness -/

section Witness

variable {μA μS : Measure ArcParam} [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]

/-- **Cancellation of the common term.**  The log profile of the two-arc witness is
`2^{−1/2}(⟨R⟩_S − ⟨R⟩_A)`, a difference of residual superpositions. -/
theorem exp_half_mul_twoArcLine (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) (v : ℝ) :
    Real.exp (v / 2) * twoArcLine μA μS (Real.exp v) =
      (Real.sqrt 2)⁻¹ * ((∫ p, symCoshResidual (sidePointRe p) v ∂(sideGenMeasure μS)) /
          (sideGenMeasure μS).real univ -
        ∫ p, symCoshResidual (arcPointRe p) v ∂μA) := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  have hmS0 := sideGenMeasure_real_pos hcusp hann
  have ha := exp_half_mul_circleLine hS v
  have hb := exp_half_mul_circleLine hA v
  rw [integral_symCoshKernel_eq hS v] at ha
  have hmA : μA.real univ = 1 := probReal_univ
  rw [integral_symCoshKernel_eq hA v, hmA] at hb
  unfold twoArcLine
  rw [hmA, div_one, mul_sub, mul_div_assoc', ha, hb]
  field_simp
  ring

/-- **No logarithmic tail.**  `|e^{v/2} h(e^v)| ≤ C (cosh v)^{−5/2}`. -/
theorem abs_twoArcProfile_le (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    ∃ C, ∀ v, |Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)| ≤
      C * Real.cosh v ^ (-(5 / 2) : ℝ) := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  have hmS0 := sideGenMeasure_real_pos hcusp hann
  set mS := (sideGenMeasure μS).real univ
  set AS := ∫ p, 2 * Real.sqrt 2 / sidePointIm p ∂(sideGenMeasure μS)
  set AA := ∫ p, 2 * Real.sqrt 2 / arcPointIm p ∂μA
  refine ⟨(Real.sqrt 2)⁻¹ * (AS / mS + AA), fun v => ?_⟩
  have hsq : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr two_pos)
  rw [exp_half_mul_twoArcLine hcusp hann v, abs_mul, abs_of_pos hsq]
  have h1 := abs_integral_symCoshResidual_le hS v
  have h2 := abs_integral_symCoshResidual_le hA v
  set X := ∫ p, symCoshResidual (sidePointRe p) v ∂(sideGenMeasure μS)
  set Y := ∫ p, symCoshResidual (arcPointRe p) v ∂μA
  set ch := Real.cosh v ^ (-(5 / 2) : ℝ)
  calc (Real.sqrt 2)⁻¹ * |X / mS - Y| ≤ (Real.sqrt 2)⁻¹ * (|X| / mS + |Y|) := by
        gcongr
        calc |X / mS - Y| ≤ |X / mS| + |Y| := abs_sub _ _
          _ = |X| / mS + |Y| := by rw [abs_div, abs_of_pos hmS0]
    _ ≤ (Real.sqrt 2)⁻¹ * (AS * ch / mS + AA * ch) := by gcongr
    _ = (Real.sqrt 2)⁻¹ * (AS / mS + AA) * ch := by ring

theorem exp_half_mul_twoArcProfile_eq (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    (fun v => Real.exp (v / 2) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v))) =
      fun v => (Real.sqrt 2)⁻¹ *
        ((Real.exp (v / 2) * ∫ p, symCoshResidual (sidePointRe p) v ∂(sideGenMeasure μS)) /
            (sideGenMeasure μS).real univ -
          Real.exp (v / 2) * ∫ p, symCoshResidual (arcPointRe p) v ∂μA) := by
  funext v
  rw [exp_half_mul_twoArcLine hcusp hann v]
  ring

theorem integrable_exp_half_mul_twoArcProfile (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    Integrable fun v => Real.exp (v / 2) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) := by
  rw [exp_half_mul_twoArcProfile_eq hcusp hann]
  exact (((integrable_exp_half_mul_integral_symCoshResidual
    (circleData_side μS hcusp hann)).div_const _).sub
    (integrable_exp_half_mul_integral_symCoshResidual (circleData_arc μA))).const_mul _

/-- **The Mellin value at `s = 1`** as a difference of averaged residual values. -/
theorem integral_exp_half_mul_twoArcProfile (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    ∫ v, Real.exp (v / 2) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) =
      (Real.sqrt 2)⁻¹ * ((∫ p, residualMellin (sidePointRe p) ∂(sideGenMeasure μS)) /
          (sideGenMeasure μS).real univ -
        ∫ p, residualMellin (arcPointRe p) ∂μA) := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  rw [exp_half_mul_twoArcProfile_eq hcusp hann, integral_const_mul,
    integral_sub ((integrable_exp_half_mul_integral_symCoshResidual hS).div_const _)
      (integrable_exp_half_mul_integral_symCoshResidual hA), integral_div,
    integral_exp_half_mul_integral_symCoshResidual hS,
    integral_exp_half_mul_integral_symCoshResidual hA]

/-- **Positive mass.**  `∫ e^{v/2} · e^{v/2} h(e^v) dv > 0`: side-arc points have larger `|c|`
than bottom-arc points, and `ρ` is strictly increasing in `|c|`. -/
theorem integral_exp_half_mul_twoArcProfile_pos (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    0 < ∫ v, Real.exp (v / 2) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) := by
  have hS := circleData_side μS hcusp hann
  have hA := circleData_arc μA
  rw [integral_exp_half_mul_twoArcProfile hcusp hann]
  set mS := (sideGenMeasure μS).real univ with hmS
  have hmS0 : 0 < mS := sideGenMeasure_real_pos hcusp hann
  set ρh : ℝ := residualMellin (1 / 2) with hρh
  have hspecS := integrable_residualMellin hS
  have h0 : ∀ᵐ s : ArcParam ∂μS, (s : ℝ) ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hcusp
    simp only [mem_setOf_eq, not_not] at hs
    exact hs
  have hae : ∀ᵐ p : ArcParam ∂(sideGenMeasure μS), (p : ℝ) ≠ 0 :=
    (sideGenMeasure_ac μS).ae_le h0
  have hgap : 0 < ∫ p, (residualMellin (sidePointRe p) - ρh) ∂(sideGenMeasure μS) := by
    have hint : Integrable (fun p => residualMellin (sidePointRe p) - ρh)
        (sideGenMeasure μS) := hspecS.sub (integrable_const ρh)
    have hnn : 0 ≤ᵐ[sideGenMeasure μS] fun p => residualMellin (sidePointRe p) - ρh := by
      filter_upwards [hae] with p hp
      exact sub_nonneg.mpr (sideResidualMellin_ge hp)
    refine (integral_pos_iff_support_of_nonneg_ae hnn hint).mpr ?_
    refine lt_of_lt_of_le (sideGenMeasure_sideOpen_pos hcusp hann) (measure_mono ?_)
    intro p hp
    simp only [Function.mem_support]
    exact (sub_pos.mpr (sideResidualMellin_gt hp.1 hp.2)).ne'
  rw [integral_sub hspecS (integrable_const _), integral_const, smul_eq_mul] at hgap
  have hspecA := integrable_residualMellin hA
  have hle : ∫ p, residualMellin (arcPointRe p) ∂μA ≤ ρh := by
    calc ∫ p, residualMellin (arcPointRe p) ∂μA
        ≤ ∫ _p, ρh ∂μA := integral_mono hspecA (integrable_const _) arcResidualMellin_le
      _ = ρh := by rw [integral_const, probReal_univ, one_smul]
  have h1 : ρh < (∫ p, residualMellin (sidePointRe p) ∂(sideGenMeasure μS)) / mS := by
    rw [lt_div_iff₀ hmS0]; linarith
  have hsq : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr two_pos)
  exact mul_pos hsq (by linarith)

omit [IsProbabilityMeasure μA] [IsProbabilityMeasure μS] in
theorem integral_Ioi_twoArcLine :
    ∫ x in Ioi (0 : ℝ), twoArcLine μA μS x =
      ∫ v, Real.exp (v / 2) * (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)) := by
  rw [_root_.GaloisForLFunctions.HTGeometry.integral_Ioi_comp_exp]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [← mul_assoc, ← Real.exp_add, add_halves]

theorem integrableOn_Ioi_twoArcLine (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) :
    IntegrableOn (twoArcLine μA μS) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (twoArcLine μA μS)
  rw [image_univ, Real.range_exp, integrableOn_univ] at h
  rw [h]
  refine (integrable_exp_half_mul_twoArcProfile (μA := μA) hcusp hann).congr
    (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [abs_of_pos (Real.exp_pos v), ← mul_assoc, ← Real.exp_add, add_halves]

/-- The two-arc witness is integrable on the whole line. -/
theorem integrable_twoArcLine (hcusp : μS sideCusp = 0)
    (hann : ∀ n, ∫ s, sideCosMode n s ∂μS = 0) : Integrable (twoArcLine μA μS) := by
  have hg := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_Ioi_twoArcLine (μA := μA) (μS := μS) hcusp hann)
  refine (hg.add hg.comp_neg).congr ?_
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, setOf_eq_eq_singleton]; exact measure_singleton 0
  filter_upwards [hne] with x hx
  simp only [Pi.add_apply]
  rcases hx.lt_or_gt with h | h
  · rw [indicator_of_notMem (show x ∉ Ioi 0 from not_lt.mpr h.le),
      indicator_of_mem (show -x ∈ Ioi 0 from neg_pos.mpr h), twoArcLine_neg, zero_add]
  · rw [indicator_of_mem (show x ∈ Ioi 0 from h),
      indicator_of_notMem (show -x ∉ Ioi 0 from not_lt.mpr (neg_nonpos.mpr h.le)), add_zero]

end Witness

/-- **The two-arc witness, with mass.**  There is an even integrable `h` with
`h(1/x) = |x| h(x)`, integrable derivative orthogonal to `sin(2π(n+1)x)` and `cos(2π(n+1)x)`
for every `n`, strictly positive definite log profile decaying like `(cosh v)^{−5/2}`, and
`∫₀^∞ h > 0`. -/
theorem exists_twoArcWitness_mass :
    ∃ μA μS : ProbabilityMeasure ArcParam,
      (∀ x, twoArcLine μA μS (-x) = twoArcLine μA μS x) ∧
      (∀ x, x ≠ 0 → twoArcLine μA μS (1 / x) = |x| * twoArcLine μA μS x) ∧
      (∀ x, HasDerivAt (twoArcLine μA μS) (twoArcDeriv μA μS x) x) ∧
      Integrable (twoArcLine μA μS) ∧ Integrable (twoArcDeriv μA μS) ∧
      (∀ n : ℕ, ∫ x, twoArcDeriv μA μS x * Real.sin (arcFreq n * x) = 0 ∧
        ∫ x, twoArcDeriv μA μS x * Real.cos (arcFreq n * x) = 0) ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp (v / 2) * twoArcLine μA μS (Real.exp v))) ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * twoArcLine μA μS (Real.exp v)| ≤
        C * Real.cosh v ^ (-(5 / 2) : ℝ)) ∧
      0 < ∫ x in Ioi (0 : ℝ), twoArcLine μA μS x := by
  obtain ⟨μA, hA⟩ := exists_probabilityMeasure_arc_annihilating
  obtain ⟨μS, hS, hcusp⟩ := exists_probabilityMeasure_sideArc_annihilating
  have hannS : ∀ n, ∫ s, sideCosMode n s ∂(μS : Measure ArcParam) = 0 := fun n => (hS n).1
  have hannA : ∀ n, ∫ u, arcCosMode n u ∂(μA : Measure ArcParam) = 0 := fun n => (hA n).1
  refine ⟨μA, μS, twoArcLine_neg, fun x hx => twoArcLine_inv hcusp hannS hx,
    hasDerivAt_twoArcLine hcusp hannS, integrable_twoArcLine hcusp hannS,
    integrable_twoArcDeriv hcusp hannS,
    fun n => ⟨integral_twoArcDeriv_mul_sin hcusp hannS hannA n,
      integral_twoArcDeriv_mul_cos hcusp hannS _⟩,
    integral_cos_mul_twoArcProfile_pos hcusp hannS, abs_twoArcProfile_le hcusp hannS, ?_⟩
  rw [integral_Ioi_twoArcLine]
  exact integral_exp_half_mul_twoArcProfile_pos hcusp hannS

end

end RHTower
