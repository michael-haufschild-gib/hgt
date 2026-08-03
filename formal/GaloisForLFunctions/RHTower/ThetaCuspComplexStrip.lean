import GaloisForLFunctions.RHTower.ThetaCuspFourierLaplace
import GaloisForLFunctions.HTGeometry.VerticalContourShift
import GaloisForLFunctions.HTGeometry.L2DecayProfile
import GaloisForLFunctions.RHTower.WeightedEulerStripFourierAnalytic

/-!
# The theta-cusp source complexified on a horizontal strip

The theta-cusp seed is a polynomial times a Gaussian, so it complexifies to an entire function, and
the logarithmic source terms complexify to entire functions of the logarithmic variable.  The
Gaussian factor has modulus `exp (-pi n^2 exp (2 re z) cos (2 im z))`, which still decays as long as
`cos (2 im z) > 0`, that is on the open strip `|im z| < pi/4`.  This module proves the exact modulus
identity and the uniform Gaussian domination of the terms on every closed substrip with bounded real
part --- the majorant a locally uniform convergence argument needs.

The strip `|im z| < pi/4` is exactly where `i exp (2 z)` stays in the upper half plane, so it is the
natural domain of the theta source in logarithmic coordinates.
-/

open Complex Real MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The theta-cusp seed as an entire function. -/
def thetaCuspComplexSeed (w : ℂ) : ℂ :=
  2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * w ^ 2)

theorem thetaCuspComplexSeed_ofReal (t : ℝ) :
    thetaCuspComplexSeed ((t : ℝ) : ℂ) = ((thetaCuspSeed t : ℝ) : ℂ) := by
  rw [thetaCuspComplexSeed, thetaCuspSeed]
  push_cast [Complex.ofReal_exp]
  ring

theorem differentiable_thetaCuspComplexSeed : Differentiable ℂ thetaCuspComplexSeed := by
  unfold thetaCuspComplexSeed
  fun_prop

/-- The `n`-th complexified theta-cusp source term in logarithmic coordinates. -/
def thetaCuspComplexTerm (z : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (z / 2) * thetaCuspComplexSeed ((n : ℂ) * Complex.exp z)

theorem thetaCuspComplexTerm_ofReal (x : ℝ) (n : ℕ) :
    thetaCuspComplexTerm ((x : ℝ) : ℂ) n = ((thetaCuspSourceTerm x n : ℝ) : ℂ) := by
  rw [thetaCuspComplexTerm, thetaCuspSourceTerm]
  have hbase : ((n : ℂ) * Complex.exp ((x : ℝ) : ℂ)) = (((n * Real.exp x : ℝ)) : ℂ) := by
    push_cast
    rw [← Complex.ofReal_exp]
  rw [hbase, thetaCuspComplexSeed_ofReal]
  rw [show (((x : ℝ) : ℂ) / 2) = (((x / 2 : ℝ)) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
  push_cast
  ring

theorem differentiable_thetaCuspComplexTerm (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => thetaCuspComplexTerm z n) := by
  unfold thetaCuspComplexTerm
  exact (Complex.differentiable_exp.comp (differentiable_id.div_const 2)).mul
    (differentiable_thetaCuspComplexSeed.comp
      ((differentiable_const _).mul Complex.differentiable_exp))

/-- The modulus of the complexified Gaussian factor. -/
theorem norm_exp_neg_pi_sq (z : ℂ) (n : ℕ) :
    ‖Complex.exp (-(Real.pi : ℂ) * ((n : ℂ) * Complex.exp z) ^ 2)‖ =
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * z.re) * Real.cos (2 * z.im))) := by
  rw [Complex.norm_exp]
  congr 1
  have hsq : (-(Real.pi : ℂ) * ((n : ℂ) * Complex.exp z) ^ 2) =
      ((-Real.pi * (n : ℝ) ^ 2 : ℝ) : ℂ) * Complex.exp (2 * z) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring
  rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hre : (Complex.exp (2 * z)).re = Real.exp (2 * z.re) * Real.cos (2 * z.im) := by
    rw [Complex.exp_re]
    congr 2 <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hre]


theorem cos_le_cos_of_abs_le {δ y : ℝ} (hδ : 2 * δ ≤ Real.pi / 2) (h : |y| ≤ δ) :
    Real.cos (2 * δ) ≤ Real.cos (2 * y) := by
  have habs : Real.cos (2 * y) = Real.cos (2 * |y|) := by
    rw [← Real.cos_abs (2 * y), abs_mul, abs_two]
  rw [habs]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    (by linarith [Real.pi_pos]) ?_
  linarith [h]

/-- **Uniform strip bound for the complexified theta-cusp terms.**  On a horizontal strip strictly
inside `|im z| < pi/4` and a bounded range of real parts, every term is dominated by a Gaussian in
the summation index. -/
theorem norm_thetaCuspComplexTerm_le {δ R : ℝ} (hδ4 : 2 * δ ≤ Real.pi / 2)
    {z : ℂ} (him : |z.im| ≤ δ) (hre : |z.re| ≤ R) (n : ℕ) :
    ‖thetaCuspComplexTerm z n‖ ≤
      Real.exp (R / 2) * (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
        (((n : ℝ) ^ 4 + (n : ℝ) ^ 2) *
          Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2)) := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  set w : ℂ := (n : ℂ) * Complex.exp z with hw
  have hnw : ‖w‖ = (n : ℝ) * Real.exp z.re := by
    rw [hw, norm_mul, Complex.norm_natCast, Complex.norm_exp]
  have hcos : Real.cos (2 * δ) ≤ Real.cos (2 * z.im) := cos_le_cos_of_abs_le hδ4 him
  -- the exponential factor
  have hgauss : ‖Complex.exp (-(Real.pi : ℂ) * w ^ 2)‖ ≤
      Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2) := by
    rw [hw, norm_exp_neg_pi_sq]
    refine Real.exp_le_exp.mpr ?_
    have hexpre : Real.exp (-(2 * R)) ≤ Real.exp (2 * z.re) :=
      Real.exp_le_exp.mpr (by linarith)
    have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    have hδnn : (0 : ℝ) ≤ δ := le_trans (abs_nonneg z.im) him
    have hcospos : (0 : ℝ) ≤ Real.cos (2 * δ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hδ4⟩
    have hprod : Real.cos (2 * δ) * Real.exp (-(2 * R)) ≤
        Real.exp (2 * z.re) * Real.cos (2 * z.im) := by
      calc Real.cos (2 * δ) * Real.exp (-(2 * R))
          ≤ Real.cos (2 * δ) * Real.exp (2 * z.re) :=
            mul_le_mul_of_nonneg_left hexpre hcospos
        _ ≤ Real.cos (2 * z.im) * Real.exp (2 * z.re) :=
            mul_le_mul_of_nonneg_right hcos (Real.exp_pos _).le
        _ = Real.exp (2 * z.re) * Real.cos (2 * z.im) := by ring
    have hscaled : Real.pi * (n : ℝ) ^ 2 * (Real.cos (2 * δ) * Real.exp (-(2 * R))) ≤
        Real.pi * (n : ℝ) ^ 2 * (Real.exp (2 * z.re) * Real.cos (2 * z.im)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    nlinarith [hscaled]
  -- the polynomial factor
  have hpoly : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ ≤
      (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
        ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) := by
    have h4 : ‖w‖ ^ 4 ≤ Real.exp (4 * R) * (n : ℝ) ^ 4 := by
      rw [hnw, mul_pow]
      have : Real.exp z.re ^ 4 ≤ Real.exp (4 * R) := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by push_cast; linarith)
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 4, Real.exp_pos z.re,
        pow_nonneg (Real.exp_pos z.re).le 4]
    have h2 : ‖w‖ ^ 2 ≤ Real.exp (2 * R) * (n : ℝ) ^ 2 := by
      rw [hnw, mul_pow]
      have : Real.exp z.re ^ 2 ≤ Real.exp (2 * R) := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by push_cast; linarith)
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) n) 2, pow_nonneg (Real.exp_pos z.re).le 2]
    have hsplit : ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ ≤
        2 * Real.pi * ‖w‖ ^ 4 + 3 * ‖w‖ ^ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      have e1 : ‖2 * (Real.pi : ℂ) * w ^ 4‖ = 2 * Real.pi * ‖w‖ ^ 4 := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        norm_num
      have e2 : ‖(3 : ℂ) * w ^ 2‖ = 3 * ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        norm_num
      rw [e1, e2]
    have hfront : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ =
        2 * Real.pi * ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    rw [hfront]
    have hstep : 2 * Real.pi * ‖w‖ ^ 4 + 3 * ‖w‖ ^ 2 ≤
        (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) * ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) := by
      have hA : 2 * Real.pi * ‖w‖ ^ 4 ≤ 2 * Real.pi * (Real.exp (4 * R) * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      have hB : 3 * ‖w‖ ^ 2 ≤ 3 * (Real.exp (2 * R) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by norm_num)
      have hextra : (0 : ℝ) ≤ 2 * Real.pi * Real.exp (4 * R) * (n : ℝ) ^ 2 +
          3 * Real.exp (2 * R) * (n : ℝ) ^ 4 := by positivity
      nlinarith [hA, hB, hextra]
    calc 2 * Real.pi * ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖
        ≤ 2 * Real.pi * (2 * Real.pi * ‖w‖ ^ 4 + 3 * ‖w‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ ≤ 2 * Real.pi *
          ((2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
            ((n : ℝ) ^ 4 + (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 2 * Real.pi * (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
            ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) := by ring
  -- assemble
  have hfrontexp : ‖Complex.exp (z / 2)‖ ≤ Real.exp (R / 2) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [Complex.div_re, Complex.normSq_ofNat]
    norm_num
    linarith
  rw [thetaCuspComplexTerm, thetaCuspComplexSeed, ← hw, norm_mul, norm_mul, ← mul_assoc]
  have hA : (0 : ℝ) ≤ ‖Complex.exp (z / 2)‖ := norm_nonneg _
  have hB : (0 : ℝ) ≤ ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ :=
    norm_nonneg _
  have hC : (0 : ℝ) ≤ ‖Complex.exp (-(Real.pi : ℂ) * w ^ 2)‖ := norm_nonneg _
  have hPnn : (0 : ℝ) ≤ (2 * Real.pi) *
      (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
      ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) := by positivity
  have hEnn : (0 : ℝ) ≤
      Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2) :=
    (Real.exp_pos _).le
  calc ‖Complex.exp (z / 2)‖ * ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ *
        ‖Complex.exp (-(Real.pi : ℂ) * w ^ 2)‖
      ≤ Real.exp (R / 2) *
        ((2 * Real.pi) * (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
          ((n : ℝ) ^ 4 + (n : ℝ) ^ 2)) *
        Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2) := by
        exact mul_le_mul (mul_le_mul hfrontexp hpoly hB (Real.exp_pos _).le) hgauss hC
          (by positivity)
    _ = Real.exp (R / 2) * (2 * Real.pi) *
        (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
        (((n : ℝ) ^ 4 + (n : ℝ) ^ 2) *
          Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2)) := by
        ring


/-- The complexified all-integer theta-cusp state. -/
def thetaCuspStripSource (z : ℂ) : ℂ := ∑' n : ℕ, thetaCuspComplexTerm z n

/-- The natural analyticity strip of the theta source in logarithmic coordinates: exactly where
`i exp (2 z)` stays in the upper half plane. -/
def thetaCuspStrip : Set ℂ := {z : ℂ | |z.im| < Real.pi / 4}

theorem isOpen_thetaCuspStrip : IsOpen thetaCuspStrip := by
  have : thetaCuspStrip = (fun z : ℂ => |z.im|) ⁻¹' (Set.Iio (Real.pi / 4)) := rfl
  rw [this]
  exact (Complex.continuous_im.abs).isOpen_preimage _ isOpen_Iio

/-- Summability of the Gaussian majorant. -/
theorem summable_thetaCuspMajorant {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => ((n : ℝ) ^ 4 + (n : ℝ) ^ 2) * Real.exp (-c * (n : ℝ) ^ 2)) := by
  have h4 := summable_pow_mul_exp_neg_nat_sq 4 hc
  have h2 := summable_pow_mul_exp_neg_nat_sq 2 hc
  refine (h4.add h2).congr fun n => ?_
  ring

/-- **Absolute convergence of the complexified theta-cusp series on the strip.** -/
theorem summable_thetaCuspComplexTerm {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    Summable (thetaCuspComplexTerm z) := by
  set δ : ℝ := |z.im| with hδ
  set R : ℝ := |z.re| with hR
  have hδ4 : 2 * δ ≤ Real.pi / 2 := by
    have := hz
    rw [thetaCuspStrip, Set.mem_setOf_eq] at this
    linarith
  have hcpos : 0 < Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R)) := by
    have hδnn : (0 : ℝ) ≤ δ := abs_nonneg _
    have hcos : 0 < Real.cos (2 * δ) := by
      refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ?_⟩
      have h2 : 2 * δ < Real.pi / 2 := by
        rw [hδ] at *
        rw [thetaCuspStrip, Set.mem_setOf_eq] at hz
        linarith
      exact h2
    positivity
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => Real.exp (R / 2) * (2 * Real.pi) *
      (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)) *
      (((n : ℝ) ^ 4 + (n : ℝ) ^ 2) *
        Real.exp (-(Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R))) * (n : ℝ) ^ 2)))
    ((summable_thetaCuspMajorant hcpos).mul_left _) (fun n => ?_)
  exact norm_thetaCuspComplexTerm_le hδ4 (le_of_eq rfl) (le_of_eq rfl) n

theorem thetaCuspStripSource_ofReal (x : ℝ) :
    thetaCuspStripSource ((x : ℝ) : ℂ) = ((thetaCuspFullSource x : ℝ) : ℂ) := by
  have hpush : ((∑' n : ℕ, thetaCuspSourceTerm x n : ℝ) : ℂ) =
      ∑' n : ℕ, ((thetaCuspSourceTerm x n : ℝ) : ℂ) := by
    simpa using Complex.ofRealCLM.map_tsum (summable_thetaCuspSourceTerm x)
  rw [thetaCuspStripSource, thetaCuspFullSource, hpush]
  exact tsum_congr fun n => thetaCuspComplexTerm_ofReal x n

/-- **The complexified theta-cusp source is holomorphic on the strip.**  Weierstrass: the series
converges uniformly on every bounded closed substrip. -/
theorem differentiableAt_thetaCuspStripSource {z₀ : ℂ} (hz₀ : z₀ ∈ thetaCuspStrip) :
    DifferentiableAt ℂ thetaCuspStripSource z₀ := by
  rw [thetaCuspStrip, Set.mem_setOf_eq] at hz₀
  obtain ⟨δ, hδ1, hδ2⟩ := exists_between hz₀
  set R : ℝ := |z₀.re| + 1 with hR
  set s : Set ℂ := {z : ℂ | |z.im| < δ ∧ |z.re| < R} with hs
  have hsopen : IsOpen s := by
    have h1 : IsOpen {z : ℂ | |z.im| < δ} :=
      (Complex.continuous_im.abs).isOpen_preimage _ isOpen_Iio
    have h2 : IsOpen {z : ℂ | |z.re| < R} :=
      (Complex.continuous_re.abs).isOpen_preimage _ isOpen_Iio
    exact h1.inter h2
  have hz₀s : z₀ ∈ s := ⟨hδ1, by rw [hR]; linarith⟩
  have hδnn : (0 : ℝ) ≤ δ := le_trans (abs_nonneg _) hδ1.le
  have hδ4 : 2 * δ ≤ Real.pi / 2 := by linarith
  have hRnn : (0 : ℝ) ≤ R := by rw [hR]; linarith [abs_nonneg z₀.re]
  have hcpos : 0 < Real.pi * Real.cos (2 * δ) * Real.exp (-(2 * R)) := by
    have hcos : 0 < Real.cos (2 * δ) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
    positivity
  have huni : TendstoUniformlyOn
      (fun t : Finset ℕ => fun z : ℂ => ∑ n ∈ t, thetaCuspComplexTerm z n)
      (fun z : ℂ => ∑' n : ℕ, thetaCuspComplexTerm z n) atTop s := by
    refine tendstoUniformlyOn_tsum
      ((summable_thetaCuspMajorant hcpos).mul_left
        (Real.exp (R / 2) * (2 * Real.pi) *
          (2 * Real.pi * Real.exp (4 * R) + 3 * Real.exp (2 * R)))) ?_
    intro n z hz
    exact norm_thetaCuspComplexTerm_le hδ4 (le_of_lt hz.1) (le_of_lt hz.2) n
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, thetaCuspComplexTerm z n) s := by
    refine huni.tendstoLocallyUniformlyOn.differentiableOn ?_ hsopen
    refine Filter.Eventually.of_forall fun t => Differentiable.differentiableOn ?_
    exact Differentiable.fun_sum fun n _ => differentiable_thetaCuspComplexTerm n
  exact (hdiff.differentiableAt (hsopen.mem_nhds hz₀s))


theorem convex_thetaCuspStrip : Convex ℝ thetaCuspStrip := by
  have h : thetaCuspStrip = {z : ℂ | -(Real.pi / 4) < z.im} ∩ {z : ℂ | z.im < Real.pi / 4} := by
    ext z
    simp only [thetaCuspStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
  rw [h]
  exact (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)

theorem isPreconnected_thetaCuspStrip : IsPreconnected thetaCuspStrip :=
  convex_thetaCuspStrip.isPreconnected

theorem neg_mem_thetaCuspStrip {z : ℂ} (hz : z ∈ thetaCuspStrip) : -z ∈ thetaCuspStrip := by
  simpa [thetaCuspStrip, Complex.neg_im, abs_neg] using hz

theorem differentiableOn_thetaCuspStripSource :
    DifferentiableOn ℂ thetaCuspStripSource thetaCuspStrip :=
  fun _ hz => (differentiableAt_thetaCuspStripSource hz).differentiableWithinAt

theorem analyticOnNhd_thetaCuspStripSource :
    AnalyticOnNhd ℂ thetaCuspStripSource thetaCuspStrip :=
  differentiableOn_thetaCuspStripSource.analyticOnNhd isOpen_thetaCuspStrip

/-- **The complexified theta-cusp source is even on its strip.**  Both sides are holomorphic on the
symmetric strip and agree on the real axis, where the source is even. -/
theorem thetaCuspStripSource_neg {z : ℂ} (hz : z ∈ thetaCuspStrip) :
    thetaCuspStripSource (-z) = thetaCuspStripSource z := by
  set F : ℂ → ℂ := fun w => thetaCuspStripSource (-w) - thetaCuspStripSource w with hF
  have hFan : AnalyticOnNhd ℂ F thetaCuspStrip := by
    intro w hw
    refine AnalyticAt.sub ?_ (analyticOnNhd_thetaCuspStripSource w hw)
    exact (analyticOnNhd_thetaCuspStripSource (-w) (neg_mem_thetaCuspStrip hw)).comp
      ((analyticAt_id (𝕜 := ℂ) (z := w)).neg)
  have hreal : ∀ x : ℝ, F ((x : ℝ) : ℂ) = 0 := by
    intro x
    have hneg : ((-x : ℝ) : ℂ) = -((x : ℝ) : ℂ) := by push_cast; ring
    rw [hF]
    simp only
    rw [← hneg, thetaCuspStripSource_ofReal, thetaCuspStripSource_ofReal,
      thetaCuspFullSource_neg, sub_self]
  have hzero : (0 : ℂ) ∈ thetaCuspStrip := by
    simp [thetaCuspStrip, Real.pi_pos]
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = 0 := by
    have htend : Filter.Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ))
        atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hreal0 : Filter.Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal0
        simpa [Function.comp_def] using this
      · refine Filter.Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_ne_zero]
        positivity
    exact htend.frequently (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun n => hreal _))
  have heq := hFan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_thetaCuspStrip hzero hfreq
  have := heq hz
  simpa [hF, sub_eq_zero] using this


/-- Sharp pointwise bound for a complexified theta-cusp term: the Gaussian keeps the actual real
part, not a substrip lower bound. -/
theorem norm_thetaCuspComplexTerm_le_pointwise {δ : ℝ} (hδ4 : 2 * δ ≤ Real.pi / 2)
    {z : ℂ} (him : |z.im| ≤ δ) (n : ℕ) :
    ‖thetaCuspComplexTerm z n‖ ≤
      Real.exp (z.re / 2) * (2 * Real.pi) *
        (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
          3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) *
        Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by
  set w : ℂ := (n : ℂ) * Complex.exp z with hw
  have hnw : ‖w‖ = (n : ℝ) * Real.exp z.re := by
    rw [hw, norm_mul, Complex.norm_natCast, Complex.norm_exp]
  have hcos : Real.cos (2 * δ) ≤ Real.cos (2 * z.im) := cos_le_cos_of_abs_le hδ4 him
  have hδnn : (0 : ℝ) ≤ δ := le_trans (abs_nonneg z.im) him
  have hcospos : (0 : ℝ) ≤ Real.cos (2 * δ) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hδ4⟩
  have hgauss : ‖Complex.exp (-(Real.pi : ℂ) * w ^ 2)‖ ≤
      Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by
    rw [hw, norm_exp_neg_pi_sq]
    refine Real.exp_le_exp.mpr ?_
    have hscaled : Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * z.re) * Real.cos (2 * δ) ≤
        Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * z.re) * Real.cos (2 * z.im) :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    nlinarith [hscaled]
  have hpoly : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ ≤
      (2 * Real.pi) * (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
        3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by
    have h4 : ‖w‖ ^ 4 = (n : ℝ) ^ 4 * Real.exp (4 * z.re) := by
      rw [hnw, mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    have h2 : ‖w‖ ^ 2 = (n : ℝ) ^ 2 * Real.exp (2 * z.re) := by
      rw [hnw, mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    have hsplit : ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ ≤
        2 * Real.pi * ‖w‖ ^ 4 + 3 * ‖w‖ ^ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      have e1 : ‖2 * (Real.pi : ℂ) * w ^ 4‖ = 2 * Real.pi * ‖w‖ ^ 4 := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
        norm_num
      have e2 : ‖(3 : ℂ) * w ^ 2‖ = 3 * ‖w‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        norm_num
      rw [e1, e2]
    have hfront : ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ =
        2 * Real.pi * ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    rw [hfront, h4, h2] at *
    calc 2 * Real.pi * ‖2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2‖
        ≤ 2 * Real.pi * (2 * Real.pi * ((n : ℝ) ^ 4 * Real.exp (4 * z.re)) +
            3 * ((n : ℝ) ^ 2 * Real.exp (2 * z.re))) :=
          mul_le_mul_of_nonneg_left hsplit (by positivity)
      _ = 2 * Real.pi * (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
            3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by ring
  have hfrontexp : ‖Complex.exp (z / 2)‖ = Real.exp (z.re / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.div_re, Complex.normSq_ofNat]
    norm_num
    ring
  rw [thetaCuspComplexTerm, thetaCuspComplexSeed, ← hw, norm_mul, norm_mul, ← mul_assoc,
    hfrontexp]
  have hstep : Real.exp (z.re / 2) *
      ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖ ≤
      Real.exp (z.re / 2) * (2 * Real.pi) *
        (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
          3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by
    calc Real.exp (z.re / 2) *
        ‖2 * (Real.pi : ℂ) * (2 * (Real.pi : ℂ) * w ^ 4 - 3 * w ^ 2)‖
        ≤ Real.exp (z.re / 2) * ((2 * Real.pi) *
            (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
              3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re))) :=
          mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
      _ = Real.exp (z.re / 2) * (2 * Real.pi) *
            (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * z.re) +
              3 * (n : ℝ) ^ 2 * Real.exp (2 * z.re)) := by ring
  exact mul_le_mul hstep hgauss (norm_nonneg _) (by positivity)


@[simp] theorem thetaCuspComplexTerm_zero (z : ℂ) : thetaCuspComplexTerm z 0 = 0 := by
  simp [thetaCuspComplexTerm, thetaCuspComplexSeed]

/-- Gaussian sums of the power weights at a fixed positive rate. -/
def thetaGaussianPowerSum (c : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ k * Real.exp (-c * (n : ℝ) ^ 2)

theorem thetaGaussianPowerSum_nonneg (c : ℝ) (k : ℕ) : 0 ≤ thetaGaussianPowerSum c k :=
  tsum_nonneg fun n => by positivity

/-- **Decay of the complexified theta-cusp source to the right.**  Beyond the origin the Gaussian
factor beats every polynomial weight, uniformly on each closed substrip. -/
theorem exists_norm_thetaCuspStripSource_le_of_nonneg {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ δ → 0 ≤ z.re →
      ‖thetaCuspStripSource z‖ ≤ C * Real.exp (-z.re) := by
  have hδle : 2 * δ ≤ Real.pi / 2 := le_of_lt hδ4
  have hcos : 0 < Real.cos (2 * δ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδ4⟩
  set c : ℝ := Real.pi * Real.cos (2 * δ) with hc
  have hcpos : 0 < c := by positivity
  have hchalf : 0 < c / 2 := by linarith
  set S4 : ℝ := thetaGaussianPowerSum (c / 2) 4 with hS4
  set S2 : ℝ := thetaGaussianPowerSum (c / 2) 2 with hS2
  have hS4nn : 0 ≤ S4 := thetaGaussianPowerSum_nonneg _ 4
  have hS2nn : 0 ≤ S2 := thetaGaussianPowerSum_nonneg _ 2
  refine ⟨2 * Real.pi * (2 * Real.pi * S4 + 3 * S2) * (6 * (2 / c) ^ 3), by positivity, ?_⟩
  intro z him hre
  set x : ℝ := z.re with hx
  have hex : (1 : ℝ) ≤ Real.exp (2 * x) := Real.one_le_exp (by linarith)
  set K1 : ℝ := Real.exp (x / 2) * (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * x)) *
    Real.exp (-(c / 2) * Real.exp (2 * x)) with hK1
  set K2 : ℝ := Real.exp (x / 2) * (2 * Real.pi) * (3 * Real.exp (2 * x)) *
    Real.exp (-(c / 2) * Real.exp (2 * x)) with hK2
  set maj : ℕ → ℝ := fun n =>
    K1 * ((n : ℝ) ^ 4 * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) +
    K2 * ((n : ℝ) ^ 2 * Real.exp (-(c / 2) * (n : ℝ) ^ 2)) with hmaj
  have hsum4 := summable_pow_mul_exp_neg_nat_sq 4 hchalf
  have hsum2 := summable_pow_mul_exp_neg_nat_sq 2 hchalf
  have hsummaj : Summable maj := (hsum4.mul_left K1).add (hsum2.mul_left K2)
  -- termwise domination
  have hdom : ∀ n : ℕ, ‖thetaCuspComplexTerm z n‖ ≤ maj n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [thetaCuspComplexTerm_zero, norm_zero, hmaj]
      simp only
      positivity
    · refine le_trans (norm_thetaCuspComplexTerm_le_pointwise hδle him n) ?_
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hsplit : Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2 * Real.exp (2 * x)) ≤
          Real.exp (-(c / 2) * Real.exp (2 * x)) * Real.exp (-(c / 2) * (n : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have hbase : (0 : ℝ) ≤
            (n : ℝ) ^ 2 * Real.exp (2 * x) - Real.exp (2 * x) / 2 - (n : ℝ) ^ 2 / 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hex)
            (by linarith : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 / 2), hn2]
        have hkey : c / 2 * Real.exp (2 * x) + c / 2 * (n : ℝ) ^ 2 ≤
            c * (n : ℝ) ^ 2 * Real.exp (2 * x) := by
          nlinarith [mul_nonneg hcpos.le hbase]
        rw [← hc]
        linarith [hkey]
      have hposfac : (0 : ℝ) ≤ Real.exp (x / 2) * (2 * Real.pi) *
          (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * x) +
            3 * (n : ℝ) ^ 2 * Real.exp (2 * x)) := by positivity
      calc Real.exp (x / 2) * (2 * Real.pi) *
            (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * x) +
              3 * (n : ℝ) ^ 2 * Real.exp (2 * x)) *
            Real.exp (-(Real.pi * Real.cos (2 * δ)) * (n : ℝ) ^ 2 * Real.exp (2 * x))
          ≤ Real.exp (x / 2) * (2 * Real.pi) *
              (2 * Real.pi * (n : ℝ) ^ 4 * Real.exp (4 * x) +
                3 * (n : ℝ) ^ 2 * Real.exp (2 * x)) *
              (Real.exp (-(c / 2) * Real.exp (2 * x)) *
                Real.exp (-(c / 2) * (n : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hsplit hposfac
        _ = maj n := by rw [hmaj, hK1, hK2]; ring
  have hnormsummable : Summable (fun n : ℕ => ‖thetaCuspComplexTerm z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hdom hsummaj
  have hbound : ‖thetaCuspStripSource z‖ ≤ ∑' n : ℕ, maj n := by
    refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
    exact hnormsummable.tsum_le_tsum hdom hsummaj
  have hmajsum : (∑' n : ℕ, maj n) = K1 * S4 + K2 * S2 := by
    rw [hmaj]
    rw [(hsum4.mul_left K1).tsum_add (hsum2.mul_left K2), hsum4.tsum_mul_left,
      hsum2.tsum_mul_left, hS4, hS2, thetaGaussianPowerSum, thetaGaussianPowerSum]
  -- the double-exponential factor beats every power
  have hexpbound : Real.exp (-(c / 2) * Real.exp (2 * x)) ≤ 6 * (2 / c) ^ 3 * Real.exp (-(6 * x)) := by
    have hs : (0 : ℝ) < c / 2 * Real.exp (2 * x) := by positivity
    have hpow := Real.pow_div_factorial_le_exp (c / 2 * Real.exp (2 * x)) hs.le 3
    have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num
    rw [hfac] at hpow
    have hcube : (c / 2 * Real.exp (2 * x)) ^ 3 = (c / 2) ^ 3 * Real.exp (6 * x) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [hcube] at hpow
    have hinv : Real.exp (-(c / 2 * Real.exp (2 * x))) =
        (Real.exp (c / 2 * Real.exp (2 * x)))⁻¹ := by
      rw [Real.exp_neg]
    have hkey : Real.exp (-(c / 2) * Real.exp (2 * x)) =
        (Real.exp (c / 2 * Real.exp (2 * x)))⁻¹ := by
      rw [← hinv]
      congr 1
      ring
    rw [hkey]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have hposc : (0 : ℝ) < (c / 2) ^ 3 * Real.exp (6 * x) := by positivity
    have h1 : (c / 2) ^ 3 * Real.exp (6 * x) / 6 ≤ Real.exp (c / 2 * Real.exp (2 * x)) := hpow
    have hrw : 6 * (2 / c) ^ 3 * Real.exp (-(6 * x)) * Real.exp (c / 2 * Real.exp (2 * x)) =
        (6 * (2 / c) ^ 3 * Real.exp (-(6 * x))) * Real.exp (c / 2 * Real.exp (2 * x)) := by ring
    rw [hrw]
    have hfrac : (6 : ℝ) * (2 / c) ^ 3 * Real.exp (-(6 * x)) * ((c / 2) ^ 3 * Real.exp (6 * x) / 6)
        = 1 := by
      field_simp
      rw [← Real.exp_add]
      norm_num
    nlinarith [h1, hfrac, Real.exp_pos (-(6 * x)), Real.exp_pos (6 * x)]
  refine le_trans hbound ?_
  rw [hmajsum, hK1, hK2]
  have hrw : Real.exp (x / 2) * (2 * Real.pi) * (2 * Real.pi * Real.exp (4 * x)) *
        Real.exp (-(c / 2) * Real.exp (2 * x)) * S4 +
      Real.exp (x / 2) * (2 * Real.pi) * (3 * Real.exp (2 * x)) *
        Real.exp (-(c / 2) * Real.exp (2 * x)) * S2 =
      (2 * Real.pi) * Real.exp (-(c / 2) * Real.exp (2 * x)) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x)) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hrw]
  have hfacnn : (0 : ℝ) ≤ 2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) +
      3 * S2 * Real.exp (x / 2 + 2 * x) := by positivity
  calc (2 * Real.pi) * Real.exp (-(c / 2) * Real.exp (2 * x)) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x))
      ≤ (2 * Real.pi) * (6 * (2 / c) ^ 3 * Real.exp (-(6 * x))) *
        (2 * Real.pi * S4 * Real.exp (x / 2 + 4 * x) + 3 * S2 * Real.exp (x / 2 + 2 * x)) := by
        have := mul_le_mul_of_nonneg_left hexpbound (by positivity : (0:ℝ) ≤ 2 * Real.pi)
        exact mul_le_mul_of_nonneg_right this hfacnn
    _ = 2 * Real.pi * (6 * (2 / c) ^ 3) *
        (2 * Real.pi * S4 * Real.exp (-(3 * x / 2)) + 3 * S2 * Real.exp (-(7 * x / 2))) := by
        have h1 : Real.exp (-(6 * x)) * Real.exp (x / 2 + 4 * x) = Real.exp (-(3 * x / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have h2 : Real.exp (-(6 * x)) * Real.exp (x / 2 + 2 * x) = Real.exp (-(7 * x / 2)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        linear_combination (2 * Real.pi * (6 * (2 / c) ^ 3) * (2 * Real.pi * S4)) * h1 +
          (2 * Real.pi * (6 * (2 / c) ^ 3) * (3 * S2)) * h2
    _ ≤ 2 * Real.pi * (2 * Real.pi * S4 + 3 * S2) * (6 * (2 / c) ^ 3) * Real.exp (-x) := by
        have e1 : Real.exp (-(3 * x / 2)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.mpr (by linarith)
        have e2 : Real.exp (-(7 * x / 2)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.mpr (by linarith)
        have hA : (0 : ℝ) ≤ 2 * Real.pi * (6 * (2 / c) ^ 3) := by positivity
        have p1 : (0 : ℝ) ≤ 2 * Real.pi * S4 * (Real.exp (-x) - Real.exp (-(3 * x / 2))) :=
          mul_nonneg (mul_nonneg (by positivity) hS4nn) (by linarith)
        have p2 : (0 : ℝ) ≤ 3 * S2 * (Real.exp (-x) - Real.exp (-(7 * x / 2))) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith [mul_nonneg hA p1, mul_nonneg hA p2]


theorem integrable_exp_neg_abs_line : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos hx]
    ring_nf
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := (1 : ℝ)) (by norm_num) 0
    refine h.congr_fun (fun x hx => ?_) measurableSet_Iic
    rw [abs_of_nonpos hx]
    ring_nf
  simpa [Ioi_union_Iic] using hpos.union hneg

/-- **Two-sided decay of the complexified theta-cusp source on a closed substrip.** -/
theorem exists_norm_thetaCuspStripSource_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ δ →
      ‖thetaCuspStripSource z‖ ≤ C * Real.exp (-|z.re|) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le_of_nonneg hδ0 hδ4
  refine ⟨C, hC, fun z him => ?_⟩
  rcases le_or_gt 0 z.re with hre | hre
  · rw [abs_of_nonneg hre]
    exact hbound z him hre
  · have hzmem : z ∈ thetaCuspStrip := by
      rw [thetaCuspStrip, Set.mem_setOf_eq]
      have : 2 * δ < Real.pi / 2 := hδ4
      calc |z.im| ≤ δ := him
        _ < Real.pi / 4 := by linarith
    have hneg : ‖thetaCuspStripSource z‖ = ‖thetaCuspStripSource (-z)‖ := by
      rw [thetaCuspStripSource_neg hzmem]
    rw [hneg, abs_of_neg hre]
    refine hbound (-z) ?_ ?_
    · rw [Complex.neg_im, abs_neg]
      exact him
    · rw [Complex.neg_re]
      linarith

/-- The complexified source is continuous along every horizontal line inside the strip. -/
theorem continuous_thetaCuspStripSource_horizontal {u : ℝ} (hu : |u| < Real.pi / 4) :
    Continuous (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hmem : ((x : ℂ) + (u : ℂ) * Complex.I) ∈ thetaCuspStrip := by
    rw [thetaCuspStrip, Set.mem_setOf_eq]
    simpa using hu
  have hinner : ContinuousAt (fun y : ℝ => ((y : ℂ) + (u : ℂ) * Complex.I)) x := by
    fun_prop
  have hcomp := ContinuousAt.comp (x := x) (g := thetaCuspStripSource)
    (f := fun y : ℝ => ((y : ℂ) + (u : ℂ) * Complex.I))
    ((differentiableAt_thetaCuspStripSource hmem).continuousAt) hinner
  simpa [Function.comp_def] using hcomp

/-- **Absolute integrability of the complexified source along every horizontal line of the
strip.**  This is the input the contour shift consumes. -/
theorem integrable_thetaCuspStripSource_horizontal {δ u : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hu : |u| ≤ δ) :
    Integrable (fun x : ℝ => thetaCuspStripSource ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  have hu4 : |u| < Real.pi / 4 := by
    calc |u| ≤ δ := hu
      _ < Real.pi / 4 := by linarith
  refine Integrable.mono' (g := fun x : ℝ => C * Real.exp (-|x|))
    (integrable_exp_neg_abs_line.const_mul C)
    (continuous_thetaCuspStripSource_horizontal hu4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have him : |((x : ℂ) + (u : ℂ) * Complex.I).im| ≤ δ := by
    simpa using hu
  have hre : ((x : ℂ) + (u : ℂ) * Complex.I).re = x := by simp
  have := hbound _ him
  rw [hre] at this
  exact this


/-- The Fourier--Laplace integrand of the theta source at a real frequency. -/
def thetaStripFourierIntegrand (t : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (t : ℂ) * w) * thetaCuspStripSource w

theorem norm_thetaStripFourierIntegrand (t : ℝ) (w : ℂ) :
    ‖thetaStripFourierIntegrand t w‖ =
      Real.exp (t * w.im) * ‖thetaCuspStripSource w‖ := by
  rw [thetaStripFourierIntegrand, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem differentiableAt_thetaStripFourierIntegrand (t : ℝ) {w : ℂ} (hw : w ∈ thetaCuspStrip) :
    DifferentiableAt ℂ (thetaStripFourierIntegrand t) w := by
  refine DifferentiableAt.mul ?_ (differentiableAt_thetaCuspStripSource hw)
  exact (Complex.differentiable_exp.differentiableAt).comp w (by fun_prop)

theorem continuous_thetaStripFourierIntegrand_horizontal (t : ℝ) {u : ℝ}
    (hu : |u| < Real.pi / 4) :
    Continuous (fun x : ℝ => thetaStripFourierIntegrand t ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  have hK := continuous_thetaCuspStripSource_horizontal hu
  have hexp : Continuous
      (fun x : ℝ => Complex.exp (-Complex.I * (t : ℂ) * ((x : ℂ) + (u : ℂ) * Complex.I))) := by
    fun_prop
  have heq : (fun x : ℝ => thetaStripFourierIntegrand t ((x : ℂ) + (u : ℂ) * Complex.I)) =
      fun x : ℝ => Complex.exp (-Complex.I * (t : ℂ) * ((x : ℂ) + (u : ℂ) * Complex.I)) *
        thetaCuspStripSource ((x : ℂ) + (u : ℂ) * Complex.I) := rfl
  rw [heq]
  exact hexp.mul hK

/-- **Absolute integrability of the Fourier--Laplace integrand along every horizontal line of the
strip.** -/
theorem integrable_thetaStripFourierIntegrand_horizontal {δ u : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hu : |u| ≤ δ) (t : ℝ) :
    Integrable (fun x : ℝ => thetaStripFourierIntegrand t ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  have hu4 : |u| < Real.pi / 4 := by
    calc |u| ≤ δ := hu
      _ < Real.pi / 4 := by linarith
  refine Integrable.mono' (g := fun x : ℝ => Real.exp (t * u) * (C * Real.exp (-|x|)))
    ((integrable_exp_neg_abs_line.const_mul C).const_mul _)
    (continuous_thetaStripFourierIntegrand_horizontal t hu4).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have him : |((x : ℂ) + (u : ℂ) * Complex.I).im| ≤ δ := by simpa using hu
  have hre : ((x : ℂ) + (u : ℂ) * Complex.I).re = x := by simp
  have hbd := hbound _ him
  rw [hre] at hbd
  rw [norm_thetaStripFourierIntegrand]
  have him2 : ((x : ℂ) + (u : ℂ) * Complex.I).im = u := by simp
  rw [him2]
  exact mul_le_mul_of_nonneg_left hbd (Real.exp_pos _).le


theorem neg_I_mul_eq (u s : ℝ) :
    -Complex.I * ((u : ℂ) + (s : ℂ) * Complex.I) = (s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Horizontal contour shift for the theta Fourier--Laplace integrand.**  The full-line integral
does not depend on the height inside the strip.  The rotation `w ↦ -i w` turns the horizontal shift
into the vertical one the corpus already owns. -/
theorem integral_thetaStripFourierIntegrand_shift {δ v : ℝ} (hδ0 : 0 ≤ δ)
    (hδ4 : 2 * δ < Real.pi / 2) (hv : |v| ≤ δ) (hv0 : 0 ≤ v) (t : ℝ) :
    (∫ x : ℝ, thetaStripFourierIntegrand t ((x : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ x : ℝ, thetaStripFourierIntegrand t ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  set G : ℂ → ℂ := fun w => thetaStripFourierIntegrand t (-Complex.I * w) with hG
  have hδ4' : δ < Real.pi / 4 := by linarith
  have hvδ : v ≤ δ := le_trans (le_abs_self v) hv
  have hmem : ∀ w : ℂ, -v ≤ w.re → w.re ≤ 0 → (-Complex.I * w) ∈ thetaCuspStrip := by
    intro w h1 h2
    rw [thetaCuspStrip, Set.mem_setOf_eq]
    have hre : (-Complex.I * w).im = -w.re := by simp [Complex.mul_im]
    rw [hre, abs_neg]
    exact abs_lt.mpr ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hdiff : DifferentiableOn ℂ G (verticalStrip (-v) 0) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hw
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiableAt_thetaStripFourierIntegrand t (hmem w h1 h2)).comp w (by fun_prop)
  have hline : ∀ s y : ℝ,
      G (((-s : ℝ) : ℂ) + (y : ℝ) * Complex.I) =
        thetaStripFourierIntegrand t ((y : ℂ) + (s : ℂ) * Complex.I) := by
    intro s y
    rw [hG]
    simp only
    rw [neg_I_mul_eq (-s) y]
    norm_num
  have hnormG : ∀ u s : ℝ, |u| ≤ δ →
      ‖G ((u : ℂ) + (s : ℂ) * Complex.I)‖ ≤ Real.exp (|t| * δ) * (C * Real.exp (-|s|)) := by
    intro u s hu
    have hval : G ((u : ℂ) + (s : ℂ) * Complex.I) =
        thetaStripFourierIntegrand t ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) := by
      rw [hG]
      simp only
      rw [neg_I_mul_eq u s]
    rw [hval, norm_thetaStripFourierIntegrand]
    have him : ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).im = -u := by simp
    have hre : ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I).re = s := by simp
    rw [him]
    have hK : ‖thetaCuspStripSource ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I)‖ ≤
        C * Real.exp (-|s|) := by
      have := hbound ((s : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) (by rw [him, abs_neg]; exact hu)
      rwa [hre] at this
    have hexp : Real.exp (t * -u) ≤ Real.exp (|t| * δ) := by
      refine Real.exp_le_exp.mpr ?_
      calc t * -u ≤ |t * -u| := le_abs_self _
        _ = |t| * |u| := by rw [abs_mul, abs_neg]
        _ ≤ |t| * δ := mul_le_mul_of_nonneg_left hu (abs_nonneg t)
    exact mul_le_mul hexp hK (norm_nonneg _) (Real.exp_pos _).le
  have hedge : ∀ sgn : ℝ → ℝ, (∀ T : ℝ, |sgn T| = |T|) →
      Tendsto (fun T : ℝ => ∫ u in (-v)..(0 : ℝ), G ((u : ℂ) + ((sgn T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) := by
    intro sgn hsgn
    refine tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => Real.exp (|t| * δ) * (C * Real.exp (-|T|))) ?_ ?_
    · filter_upwards with T
      intro u hu
      have hu' : |u| ≤ δ := by
        rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_le]
          constructor <;> linarith
        · rw [abs_le]
          constructor <;> linarith
      rw [← hsgn T]
      exact hnormG u (sgn T) hu'
    · have hbase : Tendsto (fun T : ℝ => Real.exp (-|T|)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun T : ℝ => -|T|) atTop atBot :=
          tendsto_neg_atTop_atBot.comp tendsto_abs_atTop_atTop
        exact Real.tendsto_exp_atBot.comp h1
      have h2 := hbase.const_mul C
      have h3 := h2.const_mul (Real.exp (|t| * δ))
      simpa using h3
  have hc : Integrable fun y : ℝ => G (((-v : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
    refine (integrable_thetaStripFourierIntegrand_horizontal hδ0 hδ4 hv t).congr
      (Filter.Eventually.of_forall fun y => ?_)
    exact (hline v y).symm
  have hd : Integrable fun y : ℝ => G (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
    have h0 : |(0 : ℝ)| ≤ δ := by simpa using hδ0
    refine (integrable_thetaStripFourierIntegrand_horizontal hδ0 hδ4 h0 t).congr
      (Filter.Eventually.of_forall fun y => ?_)
    have hz := hline 0 y
    simpa using hz.symm
  have hshift := integral_vertical_line_eq_of_horizontal_tendsto (G := G) (c := -v) (d := 0)
    (by linarith) hdiff hc hd
    (hedge (fun T => -T) (fun T => by rw [abs_neg]))
    (hedge (fun T => T) (fun _ => rfl))
  have hL : (∫ y : ℝ, G (((0 : ℝ) : ℂ) + (y : ℝ) * Complex.I)) =
      ∫ x : ℝ, thetaStripFourierIntegrand t ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hz := hline 0 y
    simpa using hz
  have hR : (∫ y : ℝ, G (((-v : ℝ) : ℂ) + (y : ℝ) * Complex.I)) =
      ∫ x : ℝ, thetaStripFourierIntegrand t ((x : ℂ) + (v : ℂ) * Complex.I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact hline v y
  rw [← hL, ← hR]
  exact hshift.symm


theorem integral_thetaStripFourierIntegrand_zero_height (t : ℝ) :
    (∫ x : ℝ, thetaStripFourierIntegrand t ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) =
      XiC ((t : ℝ) : ℂ) := by
  rw [← thetaCuspFourierLaplace_ofReal t, thetaCuspFourierLaplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [thetaStripFourierIntegrand, thetaCuspFourierLaplaceIntegrand]
  have hz : ((x : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) = ((x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hz, thetaCuspStripSource_ofReal]

/-- **Exponential decay of the centered xi function along the real axis.**  Shifting the
Fourier--Laplace contour to the height `delta` inside the analyticity strip of the theta source
converts strip analyticity into a genuine exponential bound. -/
theorem exists_norm_XiC_ofReal_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ4 : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖XiC ((t : ℝ) : ℂ)‖ ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_thetaCuspStripSource_le hδ0 hδ4
  set A : ℝ := ∫ x : ℝ, Real.exp (-|x|) with hA
  have hAnn : 0 ≤ A := integral_nonneg fun x => (Real.exp_pos _).le
  have hδδ : |δ| ≤ δ := by rw [abs_of_nonneg hδ0]
  have hkey : ∀ t : ℝ, t ≤ 0 → ‖XiC ((t : ℝ) : ℂ)‖ ≤ C * A * Real.exp (-(δ * |t|)) := by
    intro t ht
    rw [← integral_thetaStripFourierIntegrand_zero_height t,
      ← integral_thetaStripFourierIntegrand_shift hδ0 hδ4 hδδ hδ0 t]
    have hint := integrable_thetaStripFourierIntegrand_horizontal hδ0 hδ4 hδδ t
    have hmaj : Integrable (fun x : ℝ => Real.exp (t * δ) * (C * Real.exp (-|x|))) :=
      (integrable_exp_neg_abs_line.const_mul C).const_mul _
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hmono : (∫ x : ℝ, ‖thetaStripFourierIntegrand t ((x : ℂ) + (δ : ℂ) * Complex.I)‖) ≤
        ∫ x : ℝ, Real.exp (t * δ) * (C * Real.exp (-|x|)) := by
      refine integral_mono hint.norm hmaj (fun x => ?_)
      rw [norm_thetaStripFourierIntegrand]
      have him : ((x : ℂ) + (δ : ℂ) * Complex.I).im = δ := by simp
      have hre : ((x : ℂ) + (δ : ℂ) * Complex.I).re = x := by simp
      rw [him]
      have hK := hbound ((x : ℂ) + (δ : ℂ) * Complex.I) (by rw [him]; exact hδδ)
      rw [hre] at hK
      exact mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
    refine le_trans hmono ?_
    rw [integral_const_mul, integral_const_mul, ← hA]
    have habs : |t| = -t := abs_of_nonpos ht
    rw [habs]
    have hexp : Real.exp (t * δ) = Real.exp (-(δ * -t)) := by
      congr 1
      ring
    rw [hexp]
    ring_nf
    exact le_of_eq rfl
  refine ⟨C * A, by positivity, fun t => ?_⟩
  rcases le_or_gt t 0 with ht | ht
  · exact hkey t ht
  · have hneg : XiC ((t : ℝ) : ℂ) = XiC (((-t : ℝ)) : ℂ) := by
      rw [show (((-t : ℝ)) : ℂ) = -((t : ℝ) : ℂ) by push_cast; ring, XiC_even]
    rw [hneg]
    have := hkey (-t) (by linarith)
    rwa [abs_neg] at this


/-- The real zero set of the centered xi function. -/
def xiCRealZeroSet : Set ℝ := {x : ℝ | XiC ((x : ℝ) : ℂ) = 0}

theorem finite_xiCRealZeroSet_inter (n : ℕ) :
    (xiCRealZeroSet ∩ Set.Icc (-(n : ℝ)) (n : ℝ)).Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨x₀, -, hacc⟩ :=
    hinf.exists_accPt_of_subset_isCompact isCompact_Icc Set.inter_subset_right
  have hfreqR : ∃ᶠ x in 𝓝 x₀, x ≠ x₀ ∧ XiC ((x : ℝ) : ℂ) = 0 := by
    have h := accPt_iff_frequently.mp hacc
    refine h.mono fun x hx => ⟨hx.1, ?_⟩
    exact hx.2.1
  have hfreqW : ∃ᶠ x in 𝓝[≠] x₀, XiC ((x : ℝ) : ℂ) = 0 := by
    rw [frequently_nhdsWithin_iff]
    exact hfreqR.mono fun x hx => ⟨hx.2, hx.1⟩
  have hmap : Filter.Tendsto (fun x : ℝ => ((x : ℝ) : ℂ)) (𝓝[≠] x₀) (𝓝[≠] ((x₀ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hc
    exact hx (Complex.ofReal_inj.mp hc)
  have hfreqC : ∃ᶠ z in 𝓝[≠] ((x₀ : ℝ) : ℂ), XiC z = 0 := hmap.frequently hfreqW
  have hall := (XiC_analytic.mono (Set.subset_univ _)).eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ ((x₀ : ℝ) : ℂ)) hfreqC
  exact XiC_zero_ne (hall (Set.mem_univ 0))

theorem countable_xiCRealZeroSet : xiCRealZeroSet.Countable := by
  have hcover : xiCRealZeroSet = ⋃ n : ℕ, (xiCRealZeroSet ∩ Set.Icc (-(n : ℝ)) (n : ℝ)) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, hx, by cases abs_le.mp hn with | intro h1 h2 => exact ⟨by linarith, h2⟩⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  rw [hcover]
  exact Set.countable_iUnion fun n => (finite_xiCRealZeroSet_inter n).countable

/-- **The centered xi function vanishes only on a null subset of the real axis.** -/
theorem volume_xiCRealZeroSet : volume xiCRealZeroSet = 0 :=
  countable_xiCRealZeroSet.measure_zero volume

theorem XiC_ofReal_ne_zero_ae : ∀ᵐ x : ℝ, XiC ((x : ℝ) : ℂ) ≠ 0 := by
  rw [Filter.eventually_iff, mem_ae_iff]
  have hsub : {x : ℝ | XiC ((x : ℝ) : ℂ) ≠ 0}ᶜ = xiCRealZeroSet := by
    ext x
    simp [xiCRealZeroSet]
  rw [hsub]
  exact volume_xiCRealZeroSet


theorem memLp_two_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    MemLp (fun x : ℝ => Real.exp (-(b * |x|))) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (-(b * |x|))) volume := by
    fun_prop
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hsq : (fun x : ℝ => ‖Real.exp (-(b * |x|))‖ ^ 2) =
      fun x : ℝ => Real.exp (-((2 * b) * |x|)) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hsq]
  simpa [neg_mul] using integrable_exp_neg_mul_abs (c := 2 * b) (by linarith)

/-- **The exponentially weighted moment integrand of a square-integrable function against the
centered xi function is integrable**, for every weight strictly below the decay rate. -/
theorem integrable_memLp_mul_XiC_mul_expWeight {δ a : ℝ} (ha : |a| < δ)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun x : ℝ => ‖f x‖ * (Real.exp (-(δ * |x|)) * Real.exp (a * |x|))) := by
  have hb : 0 < δ - |a| := by linarith
  have hnorm : MemLp (fun x : ℝ => ‖f x‖) 2 volume := hf.norm
  have hweight : MemLp (fun x : ℝ => Real.exp (-((δ - |a|) * |x|))) 2 volume :=
    memLp_two_exp_neg_mul_abs hb
  have hmul := hnorm.integrable_mul hweight
  refine hmul.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine AEStronglyMeasurable.mul hf.aestronglyMeasurable.norm ?_
    fun_prop
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-(δ * |x|)) * Real.exp (a * |x|) ≤
        Real.exp (-((δ - |a|) * |x|)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hax : a * |x| ≤ |a| * |x| :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (abs_nonneg x)
      nlinarith [abs_nonneg x]
    exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

end RHTower
