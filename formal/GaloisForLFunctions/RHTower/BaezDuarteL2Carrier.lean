import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.QuantitativeNymanBeurling
import GaloisForLFunctions.RHTower.VanishingCostRCLike
import GaloisForLFunctions.HTGeometry.HardyClosureZeroFree

/-!
# The Nyman--Beurling carrier, with bounded point evaluations and no Hardy space

`HTGeometry.HardyClosureZeroFree` proves the closure obstruction for an arbitrary normed space and an
arbitrary continuous linear functional, and records what was missing to use it:

> Instantiating it with the paper's concrete half-plane Hardy space still requires the half-plane `H²`
> carrier, its bounded point evaluations, and the concrete zeta generators; those are the current
> source-realization wall.

That wall dissolves.  No Hardy space, no Paley--Wiener theorem and no reproducing-kernel theory is
needed, because on the Nyman--Beurling carrier the Mellin point evaluation *is* an `L²` inner product
against an explicit vector.

**The carrier.**  Báez-Duarte's generators `ρ_θ(t) = {θ/t} − θ{1/t}` and the target `1_{(0,1]}` all live
in `L²((0,1], dt)`.  Pushing forward along the measure-preserving change of variable `t = 1/u`,
`(Uf)(u) = f(1/u)/u`, they live in `L²((1,∞), du)` — plain Lebesgue measure on the tail ray, which is
what this file uses.  The generators become `({θu} − θ{u})/u` and the target becomes `1/u`.

**The point evaluation.**  The Mellin transform `f ↦ ∫₀¹ f(t)t^{-s}dt` becomes
`F ↦ ∫₁^∞ F(u)u^{s-1}du`, which is the inner product of `F` against `bdDetectorFun s`, the pointwise
conjugate of `u ↦ u^{s-1}`.  That vector is in `L²((1,∞))` exactly when `Re s < ½`, with

`‖bdDetectorFun s‖² = ∫₁^∞ u^{2Re s − 2} du = 1/(1 − 2Re s)`,

so point evaluation is bounded on the half-plane `Re s < ½` by Cauchy--Schwarz alone.  This is the
`1/(2σ)` diagonal kernel of `QuantitativeNymanBeurling` in the form the argument actually consumes.

**The generators.**  `RHTower.FractionalPartZeta.integral_Ioi_zero_fract_dilate_cpow` evaluates the
dilated fractional-part Mellin integral as `c^w·(−ζ(w)/w)`.  Since `{θu} − θ{u}` vanishes on `(0,1)` for
`θ ≤ 1`, the tail integral equals the full-ray integral, and the detector at `s = 1 − ρ` sends the
generator `ρ_θ` to `−(θ^ρ − θ)ζ(ρ)/ρ`.  At a zero `ρ` of `ζ` that is `0`, while the target goes to
`1/ρ ≠ 0`.

**Consequences, both unconditional.**  For a zero `ρ` of `ζ` with `½ < Re ρ < 1`:

* the target is not in the closed span of the generators (`bdTarget_notMem_closedSpan_of_zero`), the
  concrete instance of the closure obstruction; and
* every `G` annihilated by the detector — in particular every finite combination of generators, and
  every `L²`-limit of such — satisfies

  `‖bdTarget − G‖ ≥ √(2Re ρ − 1)/|ρ|`  (`bdTarget_dist_floor_of_zero`),

  the quantitative Nyman--Beurling floor of `QuantitativeNymanBeurling.nbFloor`, now attached to the
  actual `L²` distances rather than to an abstract modulus.  The bound is exactly attained
  (`bdTarget_dist_floor_attained_of_zero`).
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## The carrier -/

/-- Lebesgue measure on the tail ray `u > 1`: the Nyman--Beurling carrier measure in the coordinate
`u = 1/t`. -/
noncomputable abbrev bdMeasure : Measure ℝ := volume.restrict (Ioi (1 : ℝ))

/-- The Nyman--Beurling carrier: `L²` of the tail ray. -/
abbrev BDCarrier := MeasureTheory.Lp ℂ 2 bdMeasure

/-- A square bound by an integrable power puts a function in the carrier. -/
theorem memLp_two_bdMeasure_of_sq_le {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f bdMeasure) {C b : ℝ} (hb : b < -1)
    (hbound : ∀ u ∈ Ioi (1 : ℝ), ‖f u‖ ^ 2 ≤ C * u ^ b) :
    MemLp f 2 bdMeasure := by
  refine (memLp_two_iff_integrable_sq_norm hf).2 ?_
  refine Integrable.mono' (g := fun u => C * u ^ b)
    ((integrableOn_Ioi_rpow_of_lt hb one_pos).const_mul C) (hf.norm.pow 2) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hbound u hu

/-! ## The point evaluation -/

/-- The detector vector at `s`: the pointwise conjugate of `u ↦ u^{s-1}`, so that its inner product
with `F` is the Mellin integral `∫₁^∞ F(u) u^{s-1} du`. -/
def bdDetectorFun (s : ℂ) : ℝ → ℂ := fun u => (starRingEnd ℂ) ((u : ℂ) ^ (s - 1))

theorem norm_bdDetectorFun {s : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖bdDetectorFun s u‖ = u ^ (s.re - 1) := by
  rw [bdDetectorFun, RCLike.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re,
    Complex.one_re]

theorem aestronglyMeasurable_cpow_const (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => ((u : ℂ) ^ z)) bdMeasure := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  refine ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn ?_
  intro u hu
  exact Or.inl (by rw [Complex.ofReal_re]; linarith [mem_Ioi.mp hu])

theorem aestronglyMeasurable_bdDetectorFun (s : ℂ) :
    AEStronglyMeasurable (bdDetectorFun s) bdMeasure :=
  (aestronglyMeasurable_cpow_const (s - 1)).star

/-- **The detector is in the carrier exactly on the half-plane the criterion uses.**  For `Re s < ½`
the Mellin kernel is square integrable on the tail ray. -/
theorem memLp_bdDetectorFun {s : ℂ} (hs : s.re < 1 / 2) :
    MemLp (bdDetectorFun s) 2 bdMeasure := by
  refine memLp_two_bdMeasure_of_sq_le (aestronglyMeasurable_bdDetectorFun s)
    (C := 1) (b := 2 * s.re - 2) (by linarith) ?_
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
  rw [norm_bdDetectorFun hu0, ← Real.rpow_natCast (u ^ (s.re - 1)) 2, ← Real.rpow_mul hu0.le,
    one_mul]
  norm_num
  ring_nf
  exact le_rfl

/-- The detector, as an element of the carrier. -/
def bdDetector {s : ℂ} (hs : s.re < 1 / 2) : BDCarrier :=
  (memLp_bdDetectorFun hs).toLp _

/-- **The detector computes the Mellin integral.** -/
theorem inner_bdDetector {s : ℂ} (hs : s.re < 1 / 2) (F : BDCarrier) :
    inner ℂ (bdDetector hs) F = ∫ u in Ioi (1 : ℝ), (F : ℝ → ℂ) u * (u : ℂ) ^ (s - 1) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_bdDetectorFun hs).coeFn_toLp] with u hu
  rw [RCLike.inner_apply, bdDetector]
  rw [hu, bdDetectorFun, Complex.conj_conj]

/-- **The squared norm of the detector.**  This is the reproducing-kernel value the quantitative
criterion uses, computed directly. -/
theorem norm_sq_bdDetector {s : ℂ} (hs : s.re < 1 / 2) :
    ‖bdDetector hs‖ ^ 2 = 1 / (1 - 2 * s.re) := by
  have hsq : inner ℂ (bdDetector hs) (bdDetector hs)
      = ((1 / (1 - 2 * s.re) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    have hint : ∀ᵐ u ∂bdMeasure,
        inner ℂ ((bdDetector hs : ℝ → ℂ) u) ((bdDetector hs : ℝ → ℂ) u)
          = ((u ^ (2 * s.re - 2) : ℝ) : ℂ) := by
      filter_upwards [(memLp_bdDetectorFun hs).coeFn_toLp, ae_restrict_mem measurableSet_Ioi]
        with u hu hu1
      have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu1)
      rw [bdDetector, hu, RCLike.inner_apply, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, norm_bdDetectorFun hu0,
        ← Real.rpow_natCast (u ^ (s.re - 1)) 2, ← Real.rpow_mul hu0.le]
      norm_num
      ring_nf
    rw [integral_congr_ae hint, integral_complex_ofReal,
      integral_Ioi_rpow_of_lt (by linarith : 2 * s.re - 2 < -1) one_pos]
    congr 1
    rw [Real.one_rpow, show (2 * s.re - 2 + 1) = -(1 - 2 * s.re) from by ring,
      show (-1 : ℝ) = -(1 : ℝ) from rfl, neg_div_neg_eq]
  have h2 : (RCLike.re (inner ℂ (bdDetector hs) (bdDetector hs)) : ℝ) = ‖bdDetector hs‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [hsq] at h2
  rw [← h2]
  show ((1 / (1 - 2 * s.re) : ℝ) : ℂ).re = 1 / (1 - 2 * s.re)
  exact Complex.ofReal_re _

theorem bdDetector_ne_zero {s : ℂ} (hs : s.re < 1 / 2) : bdDetector hs ≠ 0 := by
  intro h
  have h0 : ‖bdDetector hs‖ ^ 2 = 0 := by rw [h, norm_zero]; ring
  rw [norm_sq_bdDetector hs] at h0
  have : (0 : ℝ) < 1 - 2 * s.re := by linarith
  rw [div_eq_zero_iff] at h0
  rcases h0 with h | h
  · exact one_ne_zero h
  · linarith

/-- The norm of the detector in closed form. -/
theorem norm_bdDetector {s : ℂ} (hs : s.re < 1 / 2) :
    ‖bdDetector hs‖ = 1 / Real.sqrt (1 - 2 * s.re) := by
  have hpos : (0 : ℝ) < 1 - 2 * s.re := by linarith
  have h := norm_sq_bdDetector hs
  have hnn : 0 ≤ ‖bdDetector hs‖ := norm_nonneg _
  have hsq : ‖bdDetector hs‖ = Real.sqrt (1 / (1 - 2 * s.re)) := by
    rw [← h, Real.sqrt_sq hnn]
  rw [hsq, one_div, Real.sqrt_inv, one_div]

/-! ## The target and the generators -/

/-- The Nyman--Beurling target `1_{(0,1]}`, in the tail coordinate. -/
def bdTargetFun : ℝ → ℂ := fun u => ((u : ℂ))⁻¹

theorem norm_bdTargetFun {u : ℝ} (hu : 0 < u) : ‖bdTargetFun u‖ = u⁻¹ := by
  rw [bdTargetFun, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]

theorem inv_sq_eq_rpow {u : ℝ} (hu : 0 < u) : (u⁻¹) ^ 2 = u ^ (-2 : ℝ) := by
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) from by norm_num, Real.rpow_neg hu.le, Real.rpow_natCast,
    inv_pow]

theorem aestronglyMeasurable_bdTargetFun : AEStronglyMeasurable bdTargetFun bdMeasure := by
  refine Measurable.aestronglyMeasurable ?_
  exact (Complex.measurable_ofReal).inv

theorem memLp_bdTargetFun : MemLp bdTargetFun 2 bdMeasure := by
  refine memLp_two_bdMeasure_of_sq_le aestronglyMeasurable_bdTargetFun (C := 1) (b := -2)
    (by norm_num) ?_
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
  rw [norm_bdTargetFun hu0, inv_sq_eq_rpow hu0, one_mul]

/-- The target, as an element of the carrier. -/
def bdTarget : BDCarrier := memLp_bdTargetFun.toLp _

/-- The Báez-Duarte generator `ρ_θ(t) = {θ/t} − θ{1/t}`, in the tail coordinate. -/
def bdGenFun (θ : ℝ) : ℝ → ℂ := fun u =>
  (((Int.fract (θ * u) : ℝ) : ℂ) - (θ : ℂ) * ((Int.fract u : ℝ) : ℂ)) * ((u : ℂ))⁻¹

theorem norm_bdGenFun_le {θ : ℝ} {u : ℝ} (hu : 0 < u) :
    ‖bdGenFun θ u‖ ≤ (1 + |θ|) * u⁻¹ := by
  rw [bdGenFun, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖((Int.fract (θ * u) : ℝ) : ℂ)‖ ≤ 1 := norm_fract_le _
  have h2 : ‖(θ : ℂ) * ((Int.fract u : ℝ) : ℂ)‖ ≤ |θ| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |θ| * ‖((Int.fract u : ℝ) : ℂ)‖ ≤ |θ| * 1 :=
          mul_le_mul_of_nonneg_left (norm_fract_le _) (abs_nonneg θ)
      _ = |θ| := mul_one _
  linarith

theorem aestronglyMeasurable_bdGenFun (θ : ℝ) :
    AEStronglyMeasurable (bdGenFun θ) bdMeasure := by
  refine Measurable.aestronglyMeasurable ?_
  refine Measurable.mul ?_ (Complex.measurable_ofReal).inv
  exact ((measurable_fract_complex.comp (measurable_const_mul θ)).sub
    ((measurable_const).mul measurable_fract_complex))

theorem memLp_bdGenFun (θ : ℝ) : MemLp (bdGenFun θ) 2 bdMeasure := by
  refine memLp_two_bdMeasure_of_sq_le (aestronglyMeasurable_bdGenFun θ)
    (C := (1 + |θ|) ^ 2) (b := -2) (by norm_num) ?_
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
  calc ‖bdGenFun θ u‖ ^ 2 ≤ ((1 + |θ|) * u⁻¹) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_bdGenFun_le hu0) 2
    _ = (1 + |θ|) ^ 2 * u ^ (-2 : ℝ) := by rw [mul_pow, inv_sq_eq_rpow hu0]

/-- The generator, as an element of the carrier. -/
def bdGen (θ : ℝ) : BDCarrier := (memLp_bdGenFun θ).toLp _

/-! ## The two Mellin evaluations -/

theorem one_sub_re_lt {ρ : ℂ} (hρ : 1 / 2 < ρ.re) : (1 - ρ).re < 1 / 2 := by
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- **The detector sends the target to `1/ρ`.** -/
theorem inner_bdDetector_bdTarget {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) bdTarget = 1 / ρ := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  rw [inner_bdDetector]
  have hcongr : ∀ᵐ u ∂bdMeasure,
      (bdTarget : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1) = (u : ℂ) ^ (-(ρ + 1)) := by
    filter_upwards [memLp_bdTargetFun.coeFn_toLp, ae_restrict_mem measurableSet_Ioi] with u hu hu1
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu1)
    have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu0)
    rw [bdTarget, hu, bdTargetFun, ← Complex.cpow_neg_one,
      ← Complex.cpow_add _ _ hune]
    congr 1
    ring
  rw [bdTarget] at hcongr
  rw [show (∫ u in Ioi (1:ℝ), (bdTarget : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1))
      = ∫ u in Ioi (1:ℝ), (u : ℂ) ^ (-(ρ + 1)) from integral_congr_ae hcongr,
    integral_Ioi_cpow_of_lt (by rw [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith)
      one_pos]
  rw [show (-(ρ + 1) + 1 : ℂ) = -ρ from by ring, Complex.ofReal_one, Complex.one_cpow,
    div_neg, neg_div, neg_neg]

/-- **The detector sends the generator to `-(θ^ρ - θ)ζ(ρ)/ρ`** — the Báez-Duarte transform. -/
theorem inner_bdDetector_bdGen {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (bdGen θ)
      = -(((θ : ℝ) : ℂ) ^ ρ - ((θ : ℝ) : ℂ)) * (riemannZeta ρ / ρ) := by
  have hρ0 : 0 < ρ.re := by linarith
  -- the two ingredient integrals on the whole ray
  have hI1 : IntegrableOn
      (fun u : ℝ => ((Int.fract (θ * u) : ℝ) : ℂ) * (u : ℂ) ^ (-(ρ + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_dilate_cpow hρ0 hρ1 hθ0
  have hI2 : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(ρ + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_cpow hρ0 hρ1
  set G : ℝ → ℂ := fun u =>
    (((Int.fract (θ * u) : ℝ) : ℂ) - (θ : ℂ) * ((Int.fract u : ℝ) : ℂ)) * (u : ℂ) ^ (-(ρ + 1))
    with hG
  have hGeq : ∀ u : ℝ, G u = ((Int.fract (θ * u) : ℝ) : ℂ) * (u : ℂ) ^ (-(ρ + 1))
      - (θ : ℂ) * (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(ρ + 1))) := by
    intro u; rw [hG]; ring
  have hIG : IntegrableOn G (Ioi 0) := by
    refine (hI1.sub (hI2.const_mul (θ : ℂ))).congr_fun (fun u _ => (hGeq u).symm)
      measurableSet_Ioi
  -- the full-ray value
  have hfull : (∫ u in Ioi (0:ℝ), G u)
      = -(((θ : ℝ) : ℂ) ^ ρ - ((θ : ℝ) : ℂ)) * (riemannZeta ρ / ρ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hGeq u),
      integral_sub hI1 (hI2.const_mul (θ : ℂ)), integral_const_mul,
      integral_Ioi_zero_fract_dilate_cpow hρ0 hρ1 hθ0, integral_Ioi_zero_fract_cpow hρ0 hρ1]
    ring
  -- the head vanishes
  have hhead : (∫ u in Ioc (0:ℝ) 1, G u) = 0 := by
    have hzero : ∀ u ∈ Ioo (0:ℝ) 1, G u = 0 := by
      intro u hu
      have hfr1 : Int.fract (θ * u) = θ * u := by
        refine Int.fract_eq_self.mpr ⟨(mul_pos hθ0 hu.1).le, ?_⟩
        calc θ * u < θ * 1 := by
              refine mul_lt_mul_of_pos_left hu.2 hθ0
          _ = θ := mul_one θ
          _ ≤ 1 := hθ1
      have hfr2 : Int.fract u = u := Int.fract_eq_self.mpr ⟨hu.1.le, hu.2⟩
      rw [hG]
      simp only [hfr1, hfr2]
      push_cast
      ring
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo hzero, integral_zero]
  -- split
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hsplit : (∫ u in Ioi (0:ℝ), G u)
      = (∫ u in Ioc (0:ℝ) 1, G u) + ∫ u in Ioi (1:ℝ), G u := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hIG.mono_set (by rw [← hunion]; exact Set.subset_union_left))
      (hIG.mono_set (by rw [← hunion]; exact Set.subset_union_right))
  have htail : (∫ u in Ioi (1:ℝ), G u)
      = -(((θ : ℝ) : ℂ) ^ ρ - ((θ : ℝ) : ℂ)) * (riemannZeta ρ / ρ) := by
    rw [← hfull, hsplit, hhead, zero_add]
  -- identify the inner product with the tail integral
  rw [inner_bdDetector]
  have hcongr : ∀ᵐ u ∂bdMeasure,
      (bdGen θ : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1) = G u := by
    filter_upwards [(memLp_bdGenFun θ).coeFn_toLp, ae_restrict_mem measurableSet_Ioi] with u hu hu1
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu1)
    have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu0)
    rw [bdGen, hu, bdGenFun, hG]
    rw [mul_assoc, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hune]
    congr 2
    ring
  rw [bdGen] at hcongr
  rw [show (∫ u in Ioi (1:ℝ), (bdGen θ : ℝ → ℂ) u * (u : ℂ) ^ ((1 - ρ) - 1))
      = ∫ u in Ioi (1:ℝ), G u from integral_congr_ae hcongr]
  exact htail

/-! ## The two conclusions at a hypothetical off-line zero -/

/-- The index set of the Báez-Duarte generators: the dilation parameters in `(0,1]`. -/
def bdIndex : Type := {θ : ℝ // 0 < θ ∧ θ ≤ 1}

/-- **The detector annihilates every generator at a zero of zeta.** -/
theorem inner_bdDetector_bdGen_eq_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) (i : bdIndex) :
    inner ℂ (bdDetector (one_sub_re_lt hρ)) (bdGen i.1) = 0 := by
  rw [inner_bdDetector_bdGen hρ hρ1 i.2.1 i.2.2, hzero]
  simp

/-- **The concrete closure obstruction.**  At a zero of zeta off the critical line the Nyman--Beurling
target is not in the closed span of the Báez-Duarte generators.  This is
`HTGeometry.not_mem_closedSpan_of_continuous_evaluation` with the source realization supplied. -/
theorem bdTarget_notMem_closedSpan_of_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) :
    bdTarget ∉
      (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  refine GaloisForLFunctions.HTGeometry.not_mem_closedSpan_of_continuous_evaluation
    (innerSL ℂ (bdDetector (one_sub_re_lt hρ))) bdTarget (fun i : bdIndex => bdGen i.1)
    (fun i => inner_bdDetector_bdGen_eq_zero hρ hρ1 hzero i) ?_
  show inner ℂ (bdDetector (one_sub_re_lt hρ)) bdTarget ≠ 0
  rw [inner_bdDetector_bdTarget hρ]
  exact one_div_ne_zero hρ0

/-- **The quantitative floor at a point of the right half-plane.**  Every element of the carrier
annihilated by the detector at `ρ` stays at distance at least `√(2Re ρ − 1)/|ρ|` from the target.  No
property of `ρ` beyond `½ < Re ρ` is used: the zeta zero enters only through
`bdTarget_dist_floor_of_mem_closedSpan`, which identifies a set of annihilated vectors. -/
theorem bdTarget_dist_floor {ρ : ℂ} (hρ : 1 / 2 < ρ.re) {G : BDCarrier}
    (hG : inner ℂ (bdDetector (one_sub_re_lt hρ)) G = 0) :
    Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ ≤ ‖bdTarget - G‖ := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith
  have hpos : (0 : ℝ) < 2 * ρ.re - 1 := by linarith
  have hnormρ : (0 : ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hkey := dist_innerKer_ge (bdDetector (one_sub_re_lt hρ)) bdTarget
    (bdDetector_ne_zero (one_sub_re_lt hρ)) hG
  have hv : ‖bdDetector (one_sub_re_lt hρ)‖ = 1 / Real.sqrt (2 * ρ.re - 1) := by
    rw [norm_bdDetector (one_sub_re_lt hρ)]
    congr 2
    rw [Complex.sub_re, Complex.one_re]
    ring
  have hnum : ‖inner ℂ (bdDetector (one_sub_re_lt hρ)) bdTarget‖ = 1 / ‖ρ‖ := by
    rw [inner_bdDetector_bdTarget hρ, norm_div, norm_one]
  rw [hnum, hv] at hkey
  have hsne : Real.sqrt (2 * ρ.re - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have harith : (1 / ‖ρ‖) / (1 / Real.sqrt (2 * ρ.re - 1))
      = Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ := by
    field_simp
  rw [harith] at hkey
  exact hkey

/-- **The quantitative Nyman--Beurling floor.**  At a zero of zeta with `½ < Re ρ < 1`, every finite
combination of Báez-Duarte generators — and every `L²` limit of such — stays at distance at least
`√(2Re ρ − 1)/|ρ|` from the target.  So the Báez-Duarte distances cannot tend to zero, with an explicit
modulus. -/
theorem bdTarget_dist_floor_of_mem_closedSpan {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    Real.sqrt (2 * ρ.re - 1) / ‖ρ‖ ≤ ‖bdTarget - G‖ := by
  refine bdTarget_dist_floor hρ ?_
  have hker := GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
    (innerSL ℂ (bdDetector (one_sub_re_lt hρ))) (fun i : bdIndex => bdGen i.1)
    (fun i => inner_bdDetector_bdGen_eq_zero hρ hρ1 hzero i) hG
  exact hker

/-- **The floor is the corpus's `nbFloor`.**  The scalar bookkeeping of `QuantitativeNymanBeurling` is
attached to the actual `L²` distances: the modulus `m` is `1/|ρ|` and the boundary distance `σ` is
`Re ρ − ½`. -/
theorem bdTarget_dist_floor_eq_nbFloor {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) {G : BDCarrier}
    (hG : G ∈ (Submodule.span ℂ (Set.range (fun i : bdIndex => bdGen i.1))).topologicalClosure) :
    nbFloor (1 / ‖ρ‖) (ρ.re - 1 / 2) ≤ ‖bdTarget - G‖ := by
  refine le_trans (le_of_eq ?_) (bdTarget_dist_floor_of_mem_closedSpan hρ hρ1 hzero hG)
  rw [nbFloor, show 2 * (ρ.re - 1 / 2) = 2 * ρ.re - 1 from by ring, one_div, inv_mul_eq_div]

/-- The floor is exactly attained: the vanishing cost is not an artefact of the estimate. -/
theorem bdTarget_dist_floor_attained_of_zero {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    ∃ G : BDCarrier, inner ℂ (bdDetector (one_sub_re_lt hρ)) G = 0 ∧
      ‖bdTarget - G‖
        = ‖inner ℂ (bdDetector (one_sub_re_lt hρ)) bdTarget‖
            / ‖bdDetector (one_sub_re_lt hρ)‖ :=
  dist_innerKer_attained _ _ (bdDetector_ne_zero (one_sub_re_lt hρ))

end RHTower

end
