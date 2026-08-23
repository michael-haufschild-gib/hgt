import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.HTGeometry.CauchyKernelLineMass

/-!
# The continued Mellin transform determines the vector

If the continued Mellin transform of a vector of `L_a` vanishes on the strip `1/2 < Re s < 1`, the
vector is zero.  Two elementary steps:

* the band constant `d` must vanish, because the head `d·a^{1−s}/(1−s)` has a pole at `s = 1` and
  the tail transform is a Laplace transform of an `L²` datum, whose mass on the vertical line
  `Re w = σ` stays bounded as `σ ↑ 1/2` while the mass of `1/(1/2−w)` blows up;
* with `d = 0` the Laplace transform vanishes on a whole line, so Plancherel kills the datum.

## Main results

* `ae_eq_zero_of_laplaceRay_line_eq_zero` — injectivity of the half-line Laplace transform.
* `eq_zero_of_extendedMellinContinuation_eq_zero` — **injectivity of the continued Mellin
  transform on `L_a`**.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Two mass computations -/

theorem integral_norm_sq_pole_rayLine {A : ℝ} (hA : 0 < A) :
    (∫ ξ : ℝ, ‖((A : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹‖ ^ 2) = 1 / (2 * A) := by
  have hval : ∀ ξ : ℝ, ‖((A : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹‖ ^ 2
      = (A ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ := by
    intro ξ
    have hne : ((A : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I) ≠ 0 := by
      intro hzero
      have := congrArg Complex.re hzero
      simp at this
      linarith
    rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hval)]
  have hbase : (∫ t : ℝ, (A ^ 2 + t ^ 2)⁻¹) = Real.pi / A := by
    have h := integral_inv_sq_add_sq_shift (a := A) (c := 0) hA
    simpa using h
  have hcomp := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => (A ^ 2 + t ^ 2)⁻¹) (2 * Real.pi)
  rw [hcomp, hbase]
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  field_simp

theorem integral_norm_sq_laplaceRay_line_le {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    (∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2) ≤ ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2 := by
  have hsq : Integrable (fun x : ℝ => ‖φ x‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hφ.1).1 hφ
  have hdamp : Integrable (fun x : ℝ => Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hsq ?_ ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul hsq.1)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := hx
      have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        nlinarith
      have hnn : (0 : ℝ) ≤ ‖φ x‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [Real.exp_pos (-(2 * σ * x))]
  rw [integral_norm_sq_laplaceRay_line hφ hσ]
  refine integral_mono_ae hdamp hsq ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hnn : (0 : ℝ) ≤ ‖φ x‖ ^ 2 := by positivity
  have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
    refine Real.exp_le_one_iff.2 ?_
    nlinarith
  nlinarith

/-! ## Injectivity of the half-line Laplace transform -/

theorem ae_eq_zero_of_laplaceRay_line_eq_zero {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ)
    (hzero : ∀ ξ : ℝ, laplaceRay φ (rayLine σ ξ) = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), φ x = 0 := by
  have hsq : Integrable (fun x : ℝ => ‖φ x‖ ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq_norm hφ.1).1 hφ
  have hdamp : Integrable (fun x : ℝ => Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hsq ?_ ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul hsq.1)
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0:ℝ)))] with x hx
      have hx0 : (0 : ℝ) < x := hx
      have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
        refine Real.exp_le_one_iff.2 ?_
        nlinarith
      have hnn : (0 : ℝ) ≤ ‖φ x‖ ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [Real.exp_pos (-(2 * σ * x))]
  have hmass : (∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2) = 0 := by
    rw [← integral_norm_sq_laplaceRay_line hφ hσ]
    refine integral_eq_zero_of_ae ?_
    filter_upwards with ξ
    rw [hzero ξ]
    simp
  have hae := (integral_eq_zero_iff_of_nonneg_ae ?_ hdamp).1 hmass
  · filter_upwards [hae] with x hx
    have hpos : (0 : ℝ) < Real.exp (-(2 * σ * x)) := Real.exp_pos _
    have hsqz : ‖φ x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hx with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    have : ‖φ x‖ = 0 := by nlinarith [norm_nonneg (φ x)]
    exact norm_eq_zero.1 this
  · filter_upwards with x
    have hnn : (0 : ℝ) ≤ ‖φ x‖ ^ 2 := by positivity
    have hpos : (0 : ℝ) < Real.exp (-(2 * σ * x)) := Real.exp_pos _
    positivity

/-! ## Injectivity of the continued Mellin transform -/

/-- **The continued Mellin transform is injective on `L_a`.** -/
theorem eq_zero_of_extendedMellinContinuation_eq_zero {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hzero : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → extendedMellinContinuation a c d f s = 0) :
    f = 0 := by
  set φ : ℝ → ℂ := logChart a ((f : ℝ → ℂ)) with hφdef
  have hfL2 : MemLp ((f : ℝ → ℂ)) 2 (volume.restrict (Ioi a)) := (Lp.memLp f).restrict (Ioi a)
  have hφL2 : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_logChart ha hfL2
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  set M : ℝ := ∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2 with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact integral_nonneg fun x => by positivity
  -- the Laplace transform on the strip
  have hlap : ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 →
      laplaceRay φ w = -d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 / 2 - w) := by
    intro w hw1 hw2
    set s : ℂ := w + 1 / 2 with hsdef
    have hsre : s.re = w.re + 1 / 2 := by rw [hsdef]; simp
    have hs1 : 1 / 2 < s.re := by rw [hsre]; linarith
    have hs2 : s.re < 1 := by rw [hsre]; linarith
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at hsre; simp at hsre; linarith
    have hs1' : s ≠ 1 := by
      intro h; rw [h] at hsre; simp at hsre; linarith
    have hval := hzero s hs1 hs2
    rw [extendedMellinContinuation_eq_right a c d f (le_of_lt hs1) hs0 hs1', extendedMellinRight,
      extendedTailMellin_eq ha hc hs1, mellinTail_eq_laplaceRay ha ((f : ℝ → ℂ)) s] at hval
    have hws : s - 1 / 2 = w := by rw [hsdef]; ring
    rw [hws] at hval
    -- solve for the Laplace transform
    have hne : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hs1')
    have hpow : ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) ≠ 0 := cpow_ne_zero_iff.2 (Or.inl hane)
    have hsplit : ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)
        = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s) := by
      rw [← Complex.cpow_add _ _ hane]
      congr 1
      ring
    rw [hsplit] at hval
    have h2 : ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s)
        * (laplaceRay φ w + d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 - s)) = 0 := by
      rw [← hval]
      ring
    have h3 : laplaceRay φ w + d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 - s) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hpow
      · exact h
    have hsub : (1 : ℂ) - s = 1 / 2 - w := by rw [hsdef]; ring
    rw [hsub] at h3
    linear_combination h3
  -- the head constant vanishes
  have hd0 : d = 0 := by
    by_contra hdne
    have hdpos : 0 < ‖d‖ ^ 2 * a := by
      have : 0 < ‖d‖ := norm_pos_iff.2 hdne
      positivity
    set r : ℝ := min (1 / 4) (‖d‖ ^ 2 * a / (4 * (M + 1))) with hrdef
    have hr0 : 0 < r := by
      rw [hrdef]
      refine lt_min (by norm_num) ?_
      positivity
    have hr4 : r ≤ 1 / 4 := by rw [hrdef]; exact min_le_left _ _
    have hrle : r ≤ ‖d‖ ^ 2 * a / (4 * (M + 1)) := by rw [hrdef]; exact min_le_right _ _
    set σ : ℝ := 1 / 2 - r with hσdef
    have hσ0 : 0 < σ := by rw [hσdef]; linarith
    have hσ2 : σ < 1 / 2 := by rw [hσdef]; linarith
    have hline : ∀ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2
        = ‖d‖ ^ 2 * a * ‖((r : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I)⁻¹‖ ^ 2 := by
      intro ξ
      have hre : (rayLine σ ξ).re = σ := rayLine_re σ ξ
      have hw := hlap (rayLine σ ξ) (by rw [hre]; exact hσ0) (by rw [hre]; exact hσ2)
      have hkey : (1 : ℂ) / 2 - rayLine σ ξ = (r : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I := by
        rw [rayLine, hσdef]
        push_cast
        ring
      rw [hw, hkey, div_eq_mul_inv, norm_mul, mul_pow, norm_mul, mul_pow, norm_neg]
      have hsqrt : ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt a : ℝ) : ℂ) := by
        rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
        norm_num
      have hasq : ‖((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2)‖ ^ 2 = a := by
        rw [hsqrt, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a),
          Real.sq_sqrt ha.le]
      rw [hasq]
    have hmass : (∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2) = ‖d‖ ^ 2 * a * (1 / (2 * r)) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hline), integral_const_mul,
        integral_norm_sq_pole_rayLine hr0]
    have hle := integral_norm_sq_laplaceRay_line_le hφL2 hσ0
    rw [hmass] at hle
    -- but the mass blows up
    have hDr : 4 * (M + 1) * r ≤ ‖d‖ ^ 2 * a := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * (M + 1))] at hrle
      linarith
    have hkey : M * (2 * r) < ‖d‖ ^ 2 * a := by
      nlinarith [hDr, hr0, hM0, mul_nonneg hM0 hr0.le]
    have hcontra : M < ‖d‖ ^ 2 * a * (1 / (2 * r)) := by
      rw [mul_one_div, lt_div_iff₀ (by positivity : (0:ℝ) < 2 * r)]
      exact hkey
    linarith
  -- with `d = 0` the Laplace transform vanishes on a line
  have hφ0 : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), φ x = 0 := by
    refine ae_eq_zero_of_laplaceRay_line_eq_zero hφL2 (σ := 1 / 4) (by norm_num) ?_
    intro ξ
    have hre : (rayLine (1 / 4 : ℝ) ξ).re = 1 / 4 := rayLine_re _ ξ
    rw [hlap (rayLine (1 / 4 : ℝ) ξ) (by rw [hre]; norm_num) (by rw [hre]; norm_num), hd0]
    simp
  -- hence the vector vanishes on the tail
  have htail : ∀ᵐ t ∂(volume.restrict (Ioi a)), (f : ℝ → ℂ) t = 0 := by
    have hmass : (∫ t in Ioi a, ‖(f : ℝ → ℂ) t‖ ^ 2) = 0 := by
      rw [← integral_norm_sq_logChart ha ((f : ℝ → ℂ))]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hφ0] with x hx
      rw [← hφdef, hx]
      simp
    have hint : Integrable (fun t : ℝ => ‖(f : ℝ → ℂ) t‖ ^ 2) (volume.restrict (Ioi a)) :=
      (memLp_two_iff_integrable_sq_norm hfL2.1).1 hfL2
    have hae := (integral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hmass
    · filter_upwards [hae] with t ht
      simp only [Pi.zero_apply] at ht
      have : ‖(f : ℝ → ℂ) t‖ = 0 := by nlinarith [norm_nonneg ((f : ℝ → ℂ) t)]
      exact norm_eq_zero.1 this
    · filter_upwards with t
      positivity
  -- and on the band, and by evenness on the left
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioi a → (f : ℝ → ℂ) x = 0 :=
    (ae_restrict_iff' measurableSet_Ioi).1 htail
  have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a → (f : ℝ → ℂ) x = 0 := by
    filter_upwards [hd] with x hx hmem
    rw [hx hmem, hd0]
  have hrefl : ∀ᵐ x ∂(volume : Measure ℝ), (f : ℝ → ℂ) (-x) = (f : ℝ → ℂ) x := by
    have hfix : l2Reflection f = f := (mem_evenSubspace_iff f).1 hev
    have hae := l2Reflection_ae f
    rw [hfix] at hae
    exact hae.symm
  have h3 : ∀ᵐ x ∂(volume : Measure ℝ), (-x) ∈ Ioi a → (f : ℝ → ℂ) (-x) = 0 :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h1
  have hmain : ∀ᵐ x ∂(volume : Measure ℝ), (f : ℝ → ℂ) x = 0 := by
    filter_upwards [h1, h2, h3, hrefl] with x hx1 hx2 hx3 hx4
    rcases lt_trichotomy x (-a) with hlt | heq | hgt
    · rw [← hx4]
      refine hx3 ?_
      simp only [Set.mem_Ioi]
      linarith
    · refine hx2 ?_
      rw [centralInterval, Set.mem_Icc]
      constructor <;> linarith [heq]
    · rcases le_or_gt x a with hxa | hxa
      · refine hx2 ?_
        rw [centralInterval, Set.mem_Icc]
        exact ⟨le_of_lt hgt, hxa⟩
      · exact hx1 hxa
  refine (Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [hmain] with x hx
  simpa using hx

end

end RHTower
