import GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-!
# Nonnegativity and `L¹` derivative products of the Steklov profile

The Steklov average `S_a f(x) = (2a)⁻¹ ∫_{-a}^{a} f(x + t) dt` preserves nonnegativity, is an
`L¹` contraction, and its derivative `(f(x + a) - f(x - a))/(2a)` has `L¹` norm at most
`a⁻¹ ‖f‖₁` by translation invariance. The iterates `ψ_m = S_{a_{m-1}} ⋯ S_{a_0} ψ₀` of the
unit-mass nonnegative base bump therefore satisfy `‖ψ_m^{(q)}‖₁ ≤ ∏_{j<q} a_j⁻¹` for `q ≤ m`, and
the uniform limit `steklovDCProfile` is nonnegative with
`‖φ^{(q)}‖₁ ≤ ∏_{j<q} 4 (j + 3) log²(j + 3) ≤ 6 · 16^q · q! · log(q + 3)^{2q}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis

open private tendstoUniformly_steklovDerivLimit from
  GaloisForLFunctions.TransMetzlerWeilPositivity.SuperGevreyCriticalGrowth

/-! ### 1. Nonnegativity -/

theorem steklovAvg_nonneg {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a) (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ steklovAvg a f x := by
  unfold steklovAvg
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (intervalIntegral.integral_nonneg (by linarith only [ha]) fun t _ => hf _)

theorem steklovBase_nonneg (x : ℝ) : 0 ≤ steklovBase x := by
  unfold steklovBase dilate dcProfile dcBump
  exact mul_nonneg (by norm_num) (mul_nonneg (inv_nonneg.mpr (integral_dcBump_pos odd_one).le)
    (mul_nonneg (glueR_nonneg _) (glueR_nonneg _)))

theorem steklovSeq_nonneg : ∀ (m : ℕ) (x : ℝ), 0 ≤ steklovSeq m x
  | 0, x => steklovBase_nonneg x
  | m + 1, x => steklovAvg_nonneg (steklovRadius_pos m) (steklovSeq_nonneg m) x

/-- The Steklov Denjoy–Carleman profile is nonnegative. -/
theorem steklovDCProfile_nonneg (x : ℝ) : 0 ≤ steklovDCProfile x := by
  have hpt : Tendsto (fun m => steklovSeq m x) atTop (𝓝 (steklovDCProfile x)) := by
    simpa only [iteratedDeriv_zero, steklovDCProfile] using
      (tendstoUniformly_steklovDerivLimit 0).tendsto_at x
  exact ge_of_tendsto' hpt fun m => steklovSeq_nonneg m x

/-! ### 2. `L¹` calculus of the Steklov average -/

private theorem supportedIn_iteratedDeriv {f : ℝ → ℝ} {R : ℝ} (hf : SupportedIn R f) (q : ℕ) :
    SupportedIn R (iteratedDeriv q f) := fun t ht =>
  iteratedDeriv_eq_zero_of_vanish (α := -R) (β := R) (fun s hs => hf s (by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with hs | hs
      · exact lt_of_lt_of_le (by linarith only [hs]) (neg_le_abs s)
      · exact lt_of_lt_of_le hs (le_abs_self s))) q (fun h => by
    have := abs_le.mpr ⟨h.1, h.2⟩
    linarith only [this, ht])

private theorem integrable_of_supportedIn {f : ℝ → ℝ} {R : ℝ} (hf : Continuous f)
    (hs : SupportedIn R f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (hasCompactSupport_of_vanishes hs)

/-- The Steklov average is an `L¹` contraction on continuous compactly supported functions. -/
theorem integral_abs_steklovAvg_le {g : ℝ → ℝ} {R a : ℝ} (hg : Continuous g)
    (hs : SupportedIn R g) (hR : 0 ≤ R) (ha : 0 < a) :
    ∫ x, |steklovAvg a g x| ≤ ∫ x, |g x| := by
  have hpt : ∀ x, |steklovAvg a g x| ≤ steklovAvg a (fun y => |g y|) x := by
    intro x
    unfold steklovAvg
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * a))]
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral.abs_integral_le_integral_abs (by linarith only [ha])) (by positivity)
  have hcontS : Continuous (steklovAvg a g) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_steklovAvg hg ha x).continuousAt
  have habs_s : SupportedIn R (fun y => |g y|) := fun u hu => by simp [hs u hu]
  have hcontA : Continuous (steklovAvg a fun y => |g y|) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_steklovAvg hg.abs ha x).continuousAt
  have hSs := supportedIn_steklovAvg ha hs
  calc ∫ x, |steklovAvg a g x| ≤ ∫ x, steklovAvg a (fun y => |g y|) x :=
        integral_mono (integrable_of_supportedIn hcontS.abs (fun u hu => by simp [hSs u hu]))
          (integrable_of_supportedIn hcontA (supportedIn_steklovAvg ha habs_s)) hpt
    _ = ∫ x, |g x| := integral_steklovAvg hg.abs habs_s hR ha

/-- The derivative `(g(x + a) - g(x - a))/(2a)` of a Steklov average has `L¹` norm at most
`a⁻¹ ‖g‖₁`. -/
theorem integral_abs_deriv_steklovAvg_le {g : ℝ → ℝ} {R a : ℝ} (hg : Continuous g)
    (hs : SupportedIn R g) (ha : 0 < a) :
    ∫ x, |deriv (steklovAvg a g) x| ≤ a⁻¹ * ∫ x, |g x| := by
  have hd : ∀ x, deriv (steklovAvg a g) x = (2 * a)⁻¹ * (g (x + a) - g (x - a)) :=
    deriv_steklovAvg_eq_sub hg ha
  have hgi : Integrable (fun x => |g x|) := (integrable_of_supportedIn hg hs).abs
  have h1 : Integrable (fun x => |g (x + a)|) := hgi.comp_add_right a
  have h2 : Integrable (fun x => |g (x - a)|) := hgi.comp_sub_right a
  have hpt : ∀ x, |deriv (steklovAvg a g) x| ≤ (2 * a)⁻¹ * (|g (x + a)| + |g (x - a)|) := by
    intro x
    rw [hd, abs_mul, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * a))]
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
  have hcont : Continuous (deriv (steklovAvg a g)) := by
    rw [show deriv (steklovAvg a g) = fun x => (2 * a)⁻¹ * (g (x + a) - g (x - a)) from funext hd]
    fun_prop
  have hdom : Integrable (fun x => (2 * a)⁻¹ * (|g (x + a)| + |g (x - a)|)) :=
    (h1.add h2).const_mul _
  have hint : Integrable (fun x => |deriv (steklovAvg a g) x|) :=
    hdom.mono' hcont.abs.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_abs]; exact hpt x)
  have e1 : ∫ x, |g (x + a)| = ∫ x, |g x| := integral_add_right_eq_self (fun x => |g x|) a
  have e2 : ∫ x, |g (x - a)| = ∫ x, |g x| := integral_sub_right_eq_self (fun x => |g x|) a
  calc ∫ x, |deriv (steklovAvg a g) x|
      ≤ ∫ x, (2 * a)⁻¹ * (|g (x + a)| + |g (x - a)|) := integral_mono hint hdom hpt
    _ = (2 * a)⁻¹ * ((∫ x, |g (x + a)|) + ∫ x, |g (x - a)|) := by
        rw [integral_const_mul, integral_add h1 h2]
    _ = a⁻¹ * ∫ x, |g x| := by
        rw [e1, e2]
        field_simp
        ring

/-! ### 3. `L¹` derivative products -/

/-- For `q ≤ m`, `‖ψ_m^{(q)}‖₁ ≤ ∏_{j<q} a_j⁻¹`: each of the first `q` Steklov stages pays one
reciprocal radius, the remaining stages are `L¹` contractions, and `‖ψ₀‖₁ = 1`. -/
theorem integral_abs_iteratedDeriv_steklovSeq_le :
    ∀ (m q : ℕ), q ≤ m →
      ∫ x, |iteratedDeriv q (steklovSeq m) x| ≤ ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹
  | 0, q, hq => by
      have hq0 : q = 0 := Nat.le_zero.mp hq
      subst hq0
      simp only [iteratedDeriv_zero, Finset.range_zero, Finset.prod_empty, steklovSeq]
      rw [show (fun x => |steklovBase x|) = steklovBase from
        funext fun x => abs_of_nonneg (steklovBase_nonneg x), integral_steklovBase]
  | m + 1, q, hq => by
      have hsm : ContDiff ℝ ∞ (steklovSeq m) := contDiff_steklovSeq m
      rcases Nat.of_le_succ hq with hle | rfl
      · rw [steklovSeq, iteratedDeriv_steklovAvg hsm (steklovRadius_pos m) q]
        exact (integral_abs_steklovAvg_le (hsm.continuous_iteratedDeriv q (natCast_le_infty q))
          (supportedIn_iteratedDeriv (supportedIn_one_steklovSeq m) q) zero_le_one
          (steklovRadius_pos m)).trans (integral_abs_iteratedDeriv_steklovSeq_le m q hle)
      · rw [steklovSeq, iteratedDeriv_succ, iteratedDeriv_steklovAvg hsm (steklovRadius_pos m) m,
          Finset.prod_range_succ]
        have h := integral_abs_deriv_steklovAvg_le
          (hsm.continuous_iteratedDeriv m (natCast_le_infty m))
          (supportedIn_iteratedDeriv (supportedIn_one_steklovSeq m) m) (steklovRadius_pos m)
        have ih := integral_abs_iteratedDeriv_steklovSeq_le m m le_rfl
        calc _ ≤ _ := h
          _ ≤ (steklovRadius m)⁻¹ * ∏ j ∈ Finset.range m, (steklovRadius j)⁻¹ :=
              mul_le_mul_of_nonneg_left ih (inv_nonneg.mpr (steklovRadius_pos m).le)
          _ = _ := mul_comm _ _

/-- **`L¹` derivative products of the Steklov profile**: `‖φ^{(q)}‖₁ ≤ ∏_{j<q} a_j⁻¹`. The bound
passes to the uniform limit because all iterates are supported in `[-1, 1]`. -/
theorem integral_abs_iteratedDeriv_steklovDCProfile_le_prod (q : ℕ) :
    ∫ t, |iteratedDeriv q steklovDCProfile t| ≤ ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ := by
  have hφc : Continuous (iteratedDeriv q steklovDCProfile) :=
    contDiff_steklovDCProfile.continuous_iteratedDeriv q (natCast_le_infty q)
  have hφs : SupportedIn 1 (iteratedDeriv q steklovDCProfile) :=
    supportedIn_iteratedDeriv steklovDCProfile_vanishesOff q
  have hunif := tendstoUniformly_steklovDerivLimit q
  rw [← iteratedDeriv_steklovDCProfile_eq q] at hunif
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨m, hm, hmq⟩ : ∃ m, (∀ x, |iteratedDeriv q steklovDCProfile x -
      iteratedDeriv q (steklovSeq m) x| ≤ ε / 2) ∧ q ≤ m := by
    have h := Metric.tendstoUniformly_iff.mp hunif (ε / 2) (by positivity)
    obtain ⟨m, hm1, hm2⟩ := (h.and (eventually_ge_atTop q)).exists
    refine ⟨m, fun x => ?_, hm2⟩
    have hx := hm1 x
    rw [Real.dist_eq] at hx
    exact hx.le
  have hψc : Continuous (iteratedDeriv q (steklovSeq m)) :=
    (contDiff_steklovSeq m).continuous_iteratedDeriv q (natCast_le_infty q)
  have hψs : SupportedIn 1 (iteratedDeriv q (steklovSeq m)) :=
    supportedIn_iteratedDeriv (supportedIn_one_steklovSeq m) q
  have hds : SupportedIn 1
      (fun x => iteratedDeriv q steklovDCProfile x - iteratedDeriv q (steklovSeq m) x) :=
    fun u hu => by simp [hφs u hu, hψs u hu]
  have hdiff : ∫ x, |iteratedDeriv q steklovDCProfile x - iteratedDeriv q (steklovSeq m) x| ≤
      2 * 1 * (ε / 2) :=
    integral_abs_le_of_bound (hφc.sub hψc) (hasCompactSupport_of_vanishes hds) hm hds zero_le_one
  have hψ := integral_abs_iteratedDeriv_steklovSeq_le m q hmq
  have hint1 : Integrable fun x => |iteratedDeriv q (steklovSeq m) x| :=
    (integrable_of_supportedIn hψc hψs).abs
  have hint2 : Integrable fun x =>
      |iteratedDeriv q steklovDCProfile x - iteratedDeriv q (steklovSeq m) x| :=
    (integrable_of_supportedIn (hφc.sub hψc) hds).abs
  have htri : ∫ x, |iteratedDeriv q steklovDCProfile x| ≤
      (∫ x, |iteratedDeriv q (steklovSeq m) x|) +
        ∫ x, |iteratedDeriv q steklovDCProfile x - iteratedDeriv q (steklovSeq m) x| := by
    rw [← integral_add hint1 hint2]
    refine integral_mono (integrable_of_supportedIn hφc hφs).abs (hint1.add hint2) fun x => ?_
    have h := abs_sub_abs_le_abs_sub (iteratedDeriv q steklovDCProfile x)
      (iteratedDeriv q (steklovSeq m) x)
    simp only [Pi.add_apply]
    linarith only [h]
  linarith only [htri, hdiff, hψ]

/-- **Explicit logarithmic Denjoy–Carleman bound**: `‖φ^{(q)}‖₁ ≤ ∏_{j<q} 4 (j + 3) log²(j + 3)`
and `‖φ^{(q)}‖₁ ≤ 6 · 16^q · W_q` with `W_q = q! log(q + 3)^{2q}`. -/
theorem integral_abs_iteratedDeriv_steklovDCProfile_le_explicit (q : ℕ) :
    ∫ t, |iteratedDeriv q steklovDCProfile t| ≤
        ∏ j ∈ Finset.range q, (4 * ((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2) ∧
      ∫ t, |iteratedDeriv q steklovDCProfile t| ≤ 6 * 16 ^ q * dcLogWeight q := by
  have hprod := integral_abs_iteratedDeriv_steklovDCProfile_le_prod q
  have heq : ∏ j ∈ Finset.range q, (steklovRadius j)⁻¹ =
      ∏ j ∈ Finset.range q, (4 * ((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2) :=
    Finset.prod_congr rfl fun j _ => by rw [steklovRadius, one_div, inv_inv]
  refine ⟨heq ▸ hprod, hprod.trans ((prod_inv_steklovRadius_le q).trans ?_)⟩
  have hW := (dcLogWeight_pos q).le
  have h12 : (12 : ℝ) ^ q ≤ 16 ^ q := pow_le_pow_left₀ (by norm_num) (by norm_num) q
  have h16 : (0 : ℝ) ≤ 16 ^ q := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right h12 hW, mul_nonneg h16 hW]

#print axioms steklovDCProfile_nonneg
#print axioms integral_abs_iteratedDeriv_steklovDCProfile_le_prod
#print axioms integral_abs_iteratedDeriv_steklovDCProfile_le_explicit

end GaloisForLFunctions.TransMetzlerWeilPositivity
