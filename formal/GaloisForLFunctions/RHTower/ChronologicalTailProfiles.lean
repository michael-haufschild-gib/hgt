import GaloisForLFunctions.RHTower.ChronologicalTailMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The critical profile and the tail profile

The fixed-tail obstruction compares two Bose transforms on the sampling interval `[1,2]`:

  `K_ρ(u) = ∫₀^θ x^(ρ-1) h(xu) dx`  and  `F_f(u) = ∫_θ¹ f(x) h(xu) dx`.

Here the two integrands are packaged as profiles on `(0,1)`: `criticalProfile θ ρ` is `x^(ρ-1)`
truncated at `θ`, and `tailProfile θ f` is `f` supported on `[θ,1)`. The critical profile is
defined through `Complex.exp` so that its measurability is immediate; it agrees with the complex
power on the truncation range.

The main result here is the **moment identity**: if the two transforms agree on `[1,2]` then for
every real `0 < s < 1/2`

  `∫₀^θ x^(ρ-1-s) dx = ∫_θ¹ f(x) x^(-s) dx`,

that is `θ^(ρ-s)/(ρ-s) = ∫_θ¹ f(x) x^(-s) dx`. The left-hand side has a pole at `s = ρ`; the
right-hand side is bounded on the critical strip. That is the contradiction, completed in the
separation module after continuing the identity analytically in `s`.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-! ### The profiles -/

/-- The critical profile `x^(ρ-1)` truncated at `θ`. -/
def criticalProfile (θ : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  if 0 < x ∧ x < θ then Complex.exp (((Real.log x : ℝ) : ℂ) * (ρ - 1)) else 0

/-- A tail profile: `f` supported on `[θ, 1)`. -/
def tailProfile (θ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ := if θ ≤ x then f x else 0

theorem criticalProfile_eq_cpow {θ : ℝ} {ρ : ℂ} {x : ℝ} (hx : 0 < x) (hxθ : x < θ) :
    criticalProfile θ ρ x = (x : ℂ) ^ (ρ - 1) := by
  rw [criticalProfile, if_pos ⟨hx, hxθ⟩,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx)),
    Complex.ofReal_log hx.le]

theorem criticalProfile_of_not {θ : ℝ} {ρ : ℂ} {x : ℝ} (h : ¬(0 < x ∧ x < θ)) :
    criticalProfile θ ρ x = 0 := by
  rw [criticalProfile, if_neg h]

theorem measurable_criticalProfile (θ : ℝ) (ρ : ℂ) : Measurable (criticalProfile θ ρ) := by
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  · exact Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp Real.measurable_log).mul measurable_const)

theorem norm_criticalProfile {θ : ℝ} {ρ : ℂ} {x : ℝ} (hx : 0 < x) (hxθ : x < θ) :
    ‖criticalProfile θ ρ x‖ = x ^ (ρ.re - 1) := by
  rw [criticalProfile_eq_cpow hx hxθ, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1

theorem norm_criticalProfile_le {θ : ℝ} {ρ : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖criticalProfile θ ρ x‖ ≤ x ^ (ρ.re - 1) := by
  by_cases h : x < θ
  · rw [norm_criticalProfile hx h]
  · rw [criticalProfile_of_not (by tauto), norm_zero]
    exact Real.rpow_nonneg hx.le _

theorem measurable_tailProfile (θ : ℝ) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (tailProfile θ f) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) hf measurable_const

theorem tailProfile_of_lt {θ : ℝ} {f : ℝ → ℂ} {x : ℝ} (h : x < θ) : tailProfile θ f x = 0 := by
  rw [tailProfile, if_neg (by linarith)]

theorem norm_tailProfile_le {θ : ℝ} {f : ℝ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x, ‖f x‖ ≤ C) (x : ℝ) : ‖tailProfile θ f x‖ ≤ C := by
  rw [tailProfile]
  split
  · exact hfb x
  · simpa using hC

/-! ### Integrability -/

theorem integrableOn_rpow_Ioo {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ r) (Ioo a b) :=
  ((intervalIntegral.intervalIntegrable_rpow' (a := a) (b := b) hr).1).mono_set
    Ioo_subset_Ioc_self

theorem integrableOn_criticalProfile_weight {θ : ℝ} {ρ : ℂ} {s : ℝ}
    (hre : -1 < ρ.re - 1 - s) :
    IntegrableOn (fun x : ℝ => ‖criticalProfile θ ρ x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono' (g := fun x : ℝ => x ^ (ρ.re - 1 - s))
    (integrableOn_rpow_Ioo hre 0 1) ?_ ?_
  · exact (((measurable_criticalProfile θ ρ).norm).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hnn : 0 ≤ ‖criticalProfile θ ρ x‖ * x ^ (-s) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx0.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc ‖criticalProfile θ ρ x‖ * x ^ (-s) ≤ x ^ (ρ.re - 1) * x ^ (-s) :=
          mul_le_mul_of_nonneg_right (norm_criticalProfile_le hx0) (Real.rpow_nonneg hx0.le _)
      _ = x ^ (ρ.re - 1 - s) := by
          rw [← Real.rpow_add hx0]; congr 1

theorem integrableOn_tailProfile_weight {θ : ℝ} (hθ0 : 0 < θ) {f : ℝ → ℂ} {C s : ℝ}
    (hC : 0 ≤ C) (hfm : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ C) (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ => ‖tailProfile θ f x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1) := by
  haveI hfin : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  refine Integrable.mono' (g := fun _ : ℝ => C * θ ^ (-s)) (integrable_const _) ?_ ?_
  · exact (((measurable_tailProfile θ hfm).norm).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hnn : 0 ≤ ‖tailProfile θ f x‖ * x ^ (-s) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx0.le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    by_cases hxθ : θ ≤ x
    · have hw : x ^ (-s) ≤ θ ^ (-s) := by
        rw [Real.rpow_neg hθ0.le, Real.rpow_neg hx0.le, ← one_div, ← one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθ0 _)
          (Real.rpow_le_rpow hθ0.le hxθ hs)
      exact mul_le_mul (norm_tailProfile_le hC hfb x) hw (Real.rpow_nonneg hx0.le _) hC
    · rw [tailProfile_of_lt (by linarith), norm_zero, zero_mul]
      exact mul_nonneg hC (Real.rpow_nonneg hθ0.le _)

theorem integrableOn_of_weight {g : ℝ → ℂ} (hgm : Measurable g) {s : ℝ} (hs : 0 ≤ s)
    (hint : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1)) :
    IntegrableOn g (Ioo (0 : ℝ) 1) := by
  refine Integrable.mono' hint hgm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hx1 : x < 1 := hx.2
  have h1 : (1 : ℝ) ≤ x ^ (-s) := by
    have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith : -s ≤ (0 : ℝ))
    rwa [Real.rpow_zero] at this
  nlinarith [norm_nonneg (g x)]

/-! ### The kernel bound at one point, and linearity -/

theorem exists_kernel_bound_at {u : ℂ} (hu : u ∈ boseDomain) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) 1, ‖boseKernelE ((x : ℂ) * u)‖ ≤ M := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_boseDomain u hu
  have hr : 0 < ε / 2 := by positivity
  have hclosed : Metric.closedBall u (ε / 2) ⊆ boseDomain :=
    subset_trans (Metric.closedBall_subset_ball (by linarith)) hεsub
  obtain ⟨M, hM0, hMb⟩ := exists_kernel_bound hr hclosed
  exact ⟨M, hM0, fun x hx => (hMb x hx u (Metric.mem_closedBall_self hr.le)).1⟩

theorem integrableOn_profile_kernel {g : ℝ → ℂ} (_hgm : Measurable g)
    (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) {u : ℂ} (hu : u ∈ boseDomain) :
    IntegrableOn (fun x : ℝ => g x * boseKernelE ((x : ℂ) * u)) (Ioo (0 : ℝ) 1) := by
  obtain ⟨M, hM0, hMb⟩ := exists_kernel_bound_at hu
  refine Integrable.mono' (g := fun x : ℝ => M * ‖g x‖) (hg.norm.const_mul M)
    (aestronglyMeasurable_boseIntegrand hg hu) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [norm_mul]
  have hb := hMb x ⟨hx.1.le, hx.2.le⟩
  calc ‖g x‖ * ‖boseKernelE ((x : ℂ) * u)‖ ≤ ‖g x‖ * M :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = M * ‖g x‖ := by ring

theorem boseTransform_sub {g₁ g₂ : ℝ → ℂ} (hg₁m : Measurable g₁) (hg₂m : Measurable g₂)
    (hg₁ : IntegrableOn g₁ (Ioo (0 : ℝ) 1)) (hg₂ : IntegrableOn g₂ (Ioo (0 : ℝ) 1))
    {u : ℂ} (hu : u ∈ boseDomain) :
    boseTransform (fun x => g₁ x - g₂ x) u = boseTransform g₁ u - boseTransform g₂ u := by
  rw [boseTransform, boseTransform, boseTransform,
    ← integral_sub (integrableOn_profile_kernel hg₁m hg₁ hu)
      (integrableOn_profile_kernel hg₂m hg₂ hu)]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x _ => ?_)
  ring

/-! ### The moment identity -/

theorem moment_eq_zero_of_transform_eqOn {g : ℝ → ℂ} (hgm : Measurable g) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hint : IntegrableOn (fun x : ℝ => ‖g x‖ * x ^ (-s)) (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform g (t : ℂ) = 0) :
    ∫ x in Ioo (0 : ℝ) 1, g x * ((x ^ (-s) : ℝ) : ℂ) = 0 := by
  have hzero : ∀ u : ℝ, 0 < u → boseTransform g (u : ℂ) = 0 := fun u hu =>
    boseTransform_ofReal_eq_zero (integrableOn_of_weight hgm hs0.le hint) h hu
  have hlhs : ∫ u in Ioi (0 : ℝ), ((u ^ (s - 1) : ℝ) : ℂ) * boseTransform g (u : ℂ) = 0 := by
    have : ∫ u in Ioi (0 : ℝ), ((u ^ (s - 1) : ℝ) : ℂ) * boseTransform g (u : ℂ)
        = ∫ _u in Ioi (0 : ℝ), (0 : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      rw [hzero u hu, mul_zero]
    rw [this, integral_zero]
  have hmel := mellin_boseTransform hs0 hs1 hgm hint
  rw [hlhs] at hmel
  have hb : ((boseBracket s : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (boseBracket_pos hs0 hs1))
  exact (mul_eq_zero.mp hmel.symm).resolve_left hb

/-! ### The explicit critical moment -/

theorem integral_criticalProfile_weight {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {ρ : ℂ} {s : ℝ}
    (hre : -1 < ρ.re - 1 - s) (hne : ρ - (s : ℂ) ≠ 0) :
    ∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)
      = (θ : ℂ) ^ (ρ - (s : ℂ)) / (ρ - (s : ℂ)) := by
  have hpt : ∀ x ∈ Ioo (0 : ℝ) θ,
      criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ) = (x : ℂ) ^ (ρ - 1 - (s : ℂ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
    rw [criticalProfile_eq_cpow hx0 hx.2, Complex.ofReal_cpow hx0.le,
      ← Complex.cpow_add _ _ hxne]
    congr 1
    push_cast
    ring
  have hrestrict : ∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)
      = ∫ x in Ioo (0 : ℝ) θ, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ) := by
    have hind : ∫ x in Ioo (0 : ℝ) 1, criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)
        = ∫ x in Ioo (0 : ℝ) 1,
            (Ioo (0 : ℝ) θ).indicator (fun x => criticalProfile θ ρ x * ((x ^ (-s) : ℝ) : ℂ)) x := by
      refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
      by_cases hxθ : x < θ
      · rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hx.1, hxθ⟩)]
      · rw [Set.indicator_of_notMem (by simp [hxθ]),
          criticalProfile_of_not (by tauto), zero_mul]
    have hset : Ioo (0 : ℝ) 1 ∩ Ioo (0 : ℝ) θ = Ioo (0 : ℝ) θ := by
      rw [Set.Ioo_inter_Ioo, max_self, min_eq_right hθ1]
    rw [hind, setIntegral_indicator measurableSet_Ioo, hset]
  rw [hrestrict, setIntegral_congr_fun measurableSet_Ioo hpt,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0.le]
  have hre' : -1 < (ρ - 1 - (s : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  rw [integral_cpow (Or.inl hre')]
  have hsum : ρ - 1 - (s : ℂ) + 1 = ρ - (s : ℂ) := by ring
  rw [hsum, Complex.ofReal_zero, Complex.zero_cpow hne, sub_zero]

/-! ### The tail moment is bounded on the critical strip -/

/-- The analytic tail moment. -/
def tailMoment (θ : ℝ) (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * ((x : ℂ) ^ (-w))

theorem tailMoment_ofReal (θ : ℝ) {f : ℝ → ℂ} (s : ℝ) :
    tailMoment θ f (s : ℂ) = ∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * ((x ^ (-s) : ℝ) : ℂ) := by
  rw [tailMoment]
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  rw [Complex.ofReal_cpow hx.1.le]
  congr 2
  push_cast
  ring

theorem norm_tailMoment_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {f : ℝ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hfm : Measurable f) (hfb : ∀ x, ‖f x‖ ≤ C) {w : ℂ}
    (hw0 : 0 ≤ w.re) (hw : w.re ≤ 1 / 2) :
    ‖tailMoment θ f w‖ ≤ C * θ ^ (-(1 / 2) : ℝ) := by
  have hbd : ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖tailProfile θ f x * ((x : ℂ) ^ (-w))‖ ≤ C * θ ^ (-(1 / 2) : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    by_cases hxθ : θ ≤ x
    · have hexp : (-w).re = -w.re := by simp
      rw [hexp]
      have h1 : x ^ (-w.re) ≤ θ ^ (-w.re) := by
        rw [Real.rpow_neg hθ0.le, Real.rpow_neg hx0.le, ← one_div, ← one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθ0 _)
          (Real.rpow_le_rpow hθ0.le hxθ hw0)
      have h2 : θ ^ (-w.re) ≤ θ ^ (-(1 / 2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1.le (by linarith)
      exact mul_le_mul (norm_tailProfile_le hC hfb x) (le_trans h1 h2)
        (Real.rpow_nonneg hx0.le _) hC
    · rw [tailProfile_of_lt (by linarith), norm_zero, zero_mul]
      exact mul_nonneg hC (Real.rpow_nonneg hθ0.le _)
  have hbound := norm_setIntegral_le_of_norm_le_const
    (C := C * θ ^ (-(1 / 2) : ℝ))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) hbd
  have hmr : volume.real (Ioo (0 : ℝ) 1) = 1 := by
    simp [MeasureTheory.measureReal_def, Real.volume_Ioo]
  rw [tailMoment]
  calc ‖∫ x in Ioo (0 : ℝ) 1, tailProfile θ f x * ((x : ℂ) ^ (-w))‖
      ≤ C * θ ^ (-(1 / 2) : ℝ) * volume.real (Ioo (0 : ℝ) 1) := hbound
    _ = C * θ ^ (-(1 / 2) : ℝ) := by rw [hmr, mul_one]

end RHTower
