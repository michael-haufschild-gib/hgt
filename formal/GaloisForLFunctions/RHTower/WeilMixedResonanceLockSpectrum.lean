import GaloisForLFunctions.RHTower.WeilDirichletLockRigidity

/-!
# Exponential-sum lock factors and Bohr means

Let `ρ_j > 0` be reals and let
`W(s) = Σ_j q_j ρ_j^{−(s−½)}` with `Σ_j |q_j| max(1, ρ_j^{−1}) < ∞`.  The series converges absolutely
on the strip `½ ≤ Re s ≤ 3/2`.  It need not converge to the right of the strip, so `W` is
evaluated with `Re s` clamped to `[½, 3/2]` (`apLock`).

**Theorem** (`tendsto_apLock_abel_res`).  For `m, n ≥ 1`,
`ε ∫_{y ≤ −2} W(3/2 + iy) e^{y(κ_{ε+im} − i log n)} dy → Σ_{n ρ_j = m} n q_j` as `ε → 0⁺`.
So the limit vanishes when the coefficients aggregated at every rational value vanish, for instance
when no `ρ_j` is rational (`tendsto_apLock_abel`).

**Theorem** (`tendsto_mean_expSum`).  For an absolutely summable family `c_i` and real frequencies
`θ_i`, the Bohr mean `(1/T) ∫_0^T Σ_i c_i e^{iθ_i y} dy` tends to `Σ_{θ_i = 0} c_i`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity

noncomputable section

/-! ### The strip clamp -/

/-- The real part clamped to `[½, 3/2]`. -/
def clampStrip (s : ℂ) : ℂ := ((max (min s.re (3 / 2)) (1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I

theorem clampStrip_of_mem {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) : clampStrip s = s := by
  unfold clampStrip; rw [min_eq_left h2, max_eq_left h1]; exact Complex.re_add_im s

theorem continuous_clampStrip : Continuous clampStrip := by
  unfold clampStrip
  exact (Complex.continuous_ofReal.comp
      ((Complex.continuous_re.min continuous_const).max continuous_const)).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

theorem re_clampStrip_sub_mem (s : ℂ) :
    0 ≤ (clampStrip s - 1 / 2).re ∧ (clampStrip s - 1 / 2).re ≤ 1 := by
  simp only [clampStrip, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
  norm_num

/-! ### The exponential sum -/

/-- `ρ^{−x}` is at most `max(1, ρ⁻¹)` for `0 ≤ x ≤ 1`. -/
theorem rpow_neg_le_max {ρ x : ℝ} (hρ : 0 < ρ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ρ ^ (-x) ≤ max 1 ρ⁻¹ := by
  rcases le_or_gt 1 ρ with h | h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (le_max_left _ _)
  · have hinv : 1 ≤ ρ⁻¹ := by rw [one_le_inv₀ hρ]; exact h.le
    rw [Real.rpow_neg hρ.le, ← Real.inv_rpow hρ.le]
    calc ρ⁻¹ ^ x ≤ ρ⁻¹ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hinv hx1
      _ = ρ⁻¹ := Real.rpow_one _
      _ ≤ max 1 ρ⁻¹ := le_max_right _ _

theorem norm_cpow_neg_le_max {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖(ρ : ℂ) ^ (-z)‖ ≤ max 1 ρ⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hρ, Complex.neg_re]
  exact rpow_neg_le_max hρ hz0 hz1

/-- The exponential sum `W(s) = Σ_j q_j ρ_j^{−(s−½)}`, with `Re s` clamped to `[½, 3/2]`. -/
def apLock (q : ℕ → ℂ) (ρ : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' j, q j * (ρ j : ℂ) ^ (-(clampStrip s - 1 / 2))

theorem apLock_of_mem (q : ℕ → ℂ) (ρ : ℕ → ℝ) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) :
    apLock q ρ s = ∑' j, q j * (ρ j : ℂ) ^ (-(s - 1 / 2)) := by
  rw [apLock, clampStrip_of_mem h1 h2]

theorem norm_apLock_term_le {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j) (j : ℕ) (s : ℂ) :
    ‖q j * (ρ j : ℂ) ^ (-(clampStrip s - 1 / 2))‖ ≤ ‖q j‖ * max 1 (ρ j)⁻¹ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cpow_neg_le_max (hρ j) (re_clampStrip_sub_mem s).1
    (re_clampStrip_sub_mem s).2) (norm_nonneg _)

theorem continuous_apLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) : Continuous (apLock q ρ) := by
  refine continuous_tsum (fun j => ?_) hq (fun j s => norm_apLock_term_le hρ j s)
  have hb : (ρ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ j).ne'
  exact continuous_const.mul
    (((continuous_clampStrip.sub continuous_const).neg).const_cpow (Or.inl hb))

theorem norm_apLock_le {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) (s : ℂ) :
    ‖apLock q ρ s‖ ≤ ∑' j, ‖q j‖ * max 1 (ρ j)⁻¹ := by
  have hs : Summable fun j => ‖q j * (ρ j : ℂ) ^ (-(clampStrip s - 1 / 2))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_apLock_term_le hρ j s) hq
  exact (norm_tsum_le_tsum_norm hs).trans
    (Summable.tsum_le_tsum (fun j => norm_apLock_term_le hρ j s) hs hq)

theorem differentiableAt_apLock {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) {s : ℂ} (h1 : 1 / 2 < s.re)
    (h2 : s.re < 3 / 2) : DifferentiableAt ℂ (apLock q ρ) s := by
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 3 / 2} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hd : DifferentiableOn ℂ (fun w => ∑' j, q j * (ρ j : ℂ) ^ (-(w - 1 / 2))) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hq (fun j => ?_) hUo
      (fun j w hw => ?_)
    · have hb : (ρ j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ j).ne'
      intro w _
      exact ((differentiableAt_const _).mul
        ((differentiableAt_id.sub_const _).neg.const_cpow (Or.inl hb))).differentiableWithinAt
    · have hw' : clampStrip w = w := clampStrip_of_mem hw.1.le hw.2.le
      have := norm_apLock_term_le (q := q) hρ j w
      rwa [hw'] at this
  have hsU : s ∈ U := ⟨h1, h2⟩
  refine (hd.differentiableAt (hUo.mem_nhds hsU)).congr_of_eventuallyEq ?_
  filter_upwards [hUo.mem_nhds hsU] with z hz
  exact apLock_of_mem q ρ hz.1.le hz.2.le

theorem apLock_edgePt (q : ℕ → ℂ) (ρ : ℕ → ℝ) (y : ℝ) :
    apLock q ρ (edgePt y) = ∑' j, q j * (ρ j : ℂ) ^ (-(1 + (y : ℂ) * I)) := by
  rw [apLock_of_mem q ρ (by rw [edgePt_re]; norm_num) (by rw [edgePt_re])]
  congr 1; funext j; congr 2
  unfold edgePt; push_cast; ring

theorem ap_term_mul_exp (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) (w : ℂ) :
    c * (ρ : ℂ) ^ (-(1 + (y : ℂ) * I)) * cexp ((y : ℂ) * w) =
      c / ρ * cexp ((y : ℂ) * (w - ((Real.log ρ : ℝ) : ℂ) * I)) := by
  have hb : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  rw [Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log hρ.le]
  have he : cexp (((Real.log ρ : ℝ) : ℂ) * -(1 + (y : ℂ) * I)) * cexp ((y : ℂ) * w) =
      cexp ((y : ℂ) * (w - ((Real.log ρ : ℝ) : ℂ) * I)) / (ρ : ℂ) := by
    rw [← Complex.exp_add]
    have : ((Real.log ρ : ℝ) : ℂ) * -(1 + (y : ℂ) * I) + (y : ℂ) * w =
        (y : ℂ) * (w - ((Real.log ρ : ℝ) : ℂ) * I) - ((Real.log ρ : ℝ) : ℂ) := by ring
    rw [this, Complex.exp_sub, Complex.ofReal_log hρ.le, Complex.exp_log hb]
  rw [mul_assoc, he]
  ring

/-- The `j`-th edge Abel integral `(q_j/ρ_j) e^{−2(w − i log ρ_j)}/(w − i log ρ_j)`. -/
def apAbel (q : ℕ → ℂ) (ρ : ℕ → ℝ) (w : ℂ) (j : ℕ) : ℂ :=
  q j / ρ j * (cexp ((w - ((Real.log (ρ j) : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) /
    (w - ((Real.log (ρ j) : ℝ) : ℂ) * I))

theorem integral_apLock_mul_exp {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) {w : ℂ} (hw : 0 < w.re) :
    ∫ y in Iic (-2 : ℝ), apLock q ρ (edgePt y) * cexp ((y : ℂ) * w) = ∑' j, apAbel q ρ w j := by
  set F : ℕ → ℝ → ℂ := fun j y =>
    q j / ρ j * cexp ((y : ℂ) * (w - ((Real.log (ρ j) : ℝ) : ℂ) * I)) with hF
  have hre : ∀ j : ℕ, (w - ((Real.log (ρ j) : ℝ) : ℂ) * I).re = w.re := by
    intro j
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hnorm : ∀ j y, ‖F j y‖ = ‖q j / ρ j‖ * Real.exp (w.re * y) := by
    intro j y
    simp only [hF]
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hre]
    ring
  have hexpInt : IntegrableOn (fun y : ℝ => Real.exp (w.re * y)) (Iic (-2 : ℝ)) := by
    have h : IntegrableOn (fun y : ℝ => ‖cexp ((w.re : ℂ) * (y : ℂ))‖) (Iic (-2 : ℝ)) :=
      (integrableOn_exp_mul_complex_Iic (a := (w.re : ℂ)) (by simpa using hw) (-2)).norm
    refine h.congr_fun (fun y _ => ?_) measurableSet_Iic
    simp only
    rw [Complex.norm_exp]
    congr 1; simp
  have hFint : ∀ j, Integrable (F j) (volume.restrict (Iic (-2 : ℝ))) := by
    intro j
    have hcont : Continuous (F j) := by simp only [hF]; fun_prop
    exact (hexpInt.const_mul ‖q j / ρ j‖).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun y => le_of_eq (hnorm j y))
  have hInorm : ∀ j, ∫ y in Iic (-2 : ℝ), ‖F j y‖ =
      ‖q j / ρ j‖ * (Real.exp (w.re * (-2)) / w.re) := by
    intro j
    simp only [hnorm]
    rw [integral_const_mul, integral_exp_mul_Iic_real hw]
  have hqj : ∀ j, ‖q j / ρ j‖ ≤ ‖q j‖ * max 1 (ρ j)⁻¹ := by
    intro j
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ j), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  have hsum : Summable fun j => ∫ y in Iic (-2 : ℝ), ‖F j y‖ := by
    simp only [hInorm]
    exact Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => mul_le_mul_of_nonneg_right (hqj j) (by positivity)) (hq.mul_right _)
  have hlhs : (fun y : ℝ => apLock q ρ (edgePt y) * cexp ((y : ℂ) * w)) = fun y => ∑' j, F j y := by
    funext y
    rw [apLock_edgePt, ← tsum_mul_right]
    congr 1; funext j
    exact ap_term_mul_exp (q j) (hρ j) y w
  rw [hlhs, ← integral_tsum_of_summable_integral_norm hFint hsum]
  congr 1
  funext j
  have : F j = fun y : ℝ => q j / ρ j *
      cexp ((w - ((Real.log (ρ j) : ℝ) : ℂ) * I) * (y : ℂ)) :=
    funext fun y => by simp only [hF]; rw [mul_comm (y : ℂ)]
  rw [this, integral_const_mul, integral_exp_mul_complex_Iic (by rw [hre]; exact hw)]
  rfl

/-- **The edge Abel spectrum of an exponential sum.**  At height `m` the frequency `ρ_j` resonates
exactly when `n ρ_j = m`, and contributes `n q_j`. -/
theorem tendsto_apLock_abel_res {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ), apLock q ρ (edgePt y) *
      cexp ((y : ℂ) * (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 (∑' j, if (n : ℝ) * ρ j = m then (n : ℂ) * q j else 0)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set κ : ℝ → ℂ := fun ε => edgeExp ((ε : ℂ) + (m : ℂ) * I) with hκ
  have hreκ : ∀ ε : ℝ, ∀ j : ℕ,
      (κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log (ρ j) : ℝ) : ℂ) * I).re = (κ ε).re := by
    intro ε j
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ 1 / (2 * (m : ℝ)) < (κ ε).re / ε := by
    have h1 : 1 / (2 * (m : ℝ)) < 1 / m := by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) hm0]; linarith
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_re_edgeExp_div hm).eventually (lt_mem_nhds h1)] with ε hε h
    exact ⟨hε, h⟩
  have hfacts : ∀ ε : ℝ, 0 < ε → 1 / (2 * (m : ℝ)) < (κ ε).re / ε →
      0 < (κ ε).re ∧ ε / (κ ε).re ≤ 2 * m := by
    intro ε hε h
    have hpos : 0 < (κ ε).re := by
      have : 0 < (κ ε).re / ε := lt_trans (by positivity) h
      exact (div_pos_iff_of_pos_right hε).mp this
    refine ⟨hpos, ?_⟩
    rw [div_le_iff₀ hpos]
    rw [lt_div_iff₀ hε] at h
    have h2 : 2 * (m : ℝ) * (1 / (2 * m) * ε) = ε := by field_simp
    nlinarith
  set f : ℝ → ℕ → ℂ := fun ε j => (ε : ℂ) * apAbel q ρ (κ ε - ((Real.log n : ℝ) : ℂ) * I) j
    with hf
  have hsum_eq : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑' j, f ε j = (ε : ℂ) * ∫ y in Iic (-2 : ℝ),
      apLock q ρ (edgePt y) * cexp ((y : ℂ) * (κ ε - ((Real.log n : ℝ) : ℂ) * I)) := by
    filter_upwards [hev] with ε hε
    obtain ⟨hpos, _⟩ := hfacts ε hε.1 hε.2
    have hw : 0 < (κ ε - ((Real.log n : ℝ) : ℂ) * I).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      linarith
    rw [integral_apLock_mul_exp hρ hq hw, ← tsum_mul_left]
  have hκlim := tendsto_edgeExp_eps hm
  have hεlim : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
      (Complex.continuous_ofReal.tendsto (0 : ℝ))
    simpa using this
  have hlim : ∀ j : ℕ, Tendsto (fun ε => f ε j) (𝓝[>] 0)
      (𝓝 (if (n : ℝ) * ρ j = m then (n : ℂ) * q j else 0)) := by
    intro j
    have hwlim : Tendsto (fun ε => κ ε - ((Real.log n : ℝ) : ℂ) * I -
        ((Real.log (ρ j) : ℝ) : ℂ) * I) (𝓝[>] 0)
        (𝓝 (((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log (ρ j) : ℝ) : ℂ) * I)) :=
      (hκlim.sub_const _).sub_const _
    by_cases hres : (n : ℝ) * ρ j = m
    · -- resonance
      rw [if_pos hres]
      have hlog : Real.log m = Real.log n + Real.log (ρ j) := by
        rw [← hres, Real.log_mul hn0.ne' (hρ j).ne']
      have hwm : ∀ ε, κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log (ρ j) : ℝ) : ℂ) * I =
          κ ε - ((Real.log m : ℝ) : ℂ) * I := by
        intro ε; rw [hlog]; push_cast; ring
      have hc0 : ((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log (ρ j) : ℝ) : ℂ) * I = 0 := by
        rw [hlog]; push_cast; ring
      have hexp : Tendsto (fun ε => cexp ((κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log (ρ j) : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
        have := ((Complex.continuous_exp.tendsto _).comp (hwlim.mul_const ((-2 : ℝ) : ℂ)))
        rw [hc0, zero_mul, Complex.exp_zero] at this
        exact this
      have hdiv : Tendsto (fun ε : ℝ => (ε : ℂ) / (κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log (ρ j) : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 (m : ℂ)) := by
        simp only [hwm]
        exact tendsto_eps_div_edgeExp_sub hm
      have hval : q j / ρ j * (1 * (m : ℂ)) = (n : ℂ) * q j := by
        have hρ0 : ((ρ j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρ j).ne'
        have hm' : (m : ℂ) = (n : ℂ) * (ρ j : ℂ) := by exact_mod_cast hres.symm
        rw [hm']; field_simp
      rw [← hval]
      refine ((hexp.mul hdiv).const_mul (q j / ρ j)).congr' (Eventually.of_forall fun ε => ?_)
      simp only [hf, apAbel]
      ring
    rw [if_neg hres]
    have hc : ((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
        ((Real.log (ρ j) : ℝ) : ℂ) * I ≠ 0 := by
      intro h0
      have hre : (((Real.log m - Real.log n - Real.log (ρ j) : ℝ)) : ℂ) * I = 0 := by
        rw [← h0]; push_cast; ring
      have hr : Real.log m - Real.log n - Real.log (ρ j) = 0 := by
        rcases mul_eq_zero.mp hre with h1 | h1
        · exact_mod_cast h1
        · exact absurd h1 Complex.I_ne_zero
      have hlog : Real.log m = Real.log ((n : ℝ) * ρ j) := by
        rw [Real.log_mul hn0.ne' (hρ j).ne']; linarith
      exact hres (Real.log_injOn_pos (Set.mem_Ioi.mpr (mul_pos hn0 (hρ j)))
        (Set.mem_Ioi.mpr hm0) hlog.symm)
    have hq' : Tendsto (fun ε => cexp ((κ ε - ((Real.log n : ℝ) : ℂ) * I -
        ((Real.log (ρ j) : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) / (κ ε - ((Real.log n : ℝ) : ℂ) * I -
          ((Real.log (ρ j) : ℝ) : ℂ) * I)) (𝓝[>] 0) (𝓝 (cexp ((((Real.log m : ℝ) : ℂ) * I -
            ((Real.log n : ℝ) : ℂ) * I - ((Real.log (ρ j) : ℝ) : ℂ) * I) * ((-2 : ℝ) : ℂ)) /
              (((Real.log m : ℝ) : ℂ) * I - ((Real.log n : ℝ) : ℂ) * I -
                ((Real.log (ρ j) : ℝ) : ℂ) * I))) :=
      ((Complex.continuous_exp.tendsto _).comp (hwlim.mul_const ((-2 : ℝ) : ℂ))).div hwlim hc
    have h := (hεlim.mul hq').const_mul (q j / ρ j)
    rw [zero_mul, mul_zero] at h
    refine h.congr' (Eventually.of_forall fun ε => ?_)
    simp only [hf, apAbel]
    ring
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ j, ‖f ε j‖ ≤ 2 * m * (‖q j‖ * max 1 (ρ j)⁻¹) := by
    filter_upwards [hev] with ε hε j
    obtain ⟨hpos, hq2⟩ := hfacts ε hε.1 hε.2
    set W : ℂ := κ ε - ((Real.log n : ℝ) : ℂ) * I - ((Real.log (ρ j) : ℝ) : ℂ) * I with hW
    have hWre : W.re = (κ ε).re := hreκ ε j
    have hWn : (κ ε).re ≤ ‖W‖ := hWre ▸ Complex.re_le_norm W
    have hE : ‖cexp (W * ((-2 : ℝ) : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      have : (W * ((-2 : ℝ) : ℂ)).re = -2 * (κ ε).re := by
        rw [← hWre]; simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
          sub_zero]; ring
      rw [this, Real.exp_le_one_iff]; linarith
    have hqj : ‖q j / ρ j‖ ≤ ‖q j‖ * max 1 (ρ j)⁻¹ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ j), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
    have hf' : f ε j = (ε : ℂ) * (q j / ρ j * (cexp (W * ((-2 : ℝ) : ℂ)) / W)) := by
      simp only [hf, apAbel, hW]
    rw [hf', norm_mul, norm_mul, norm_div (cexp (W * ((-2 : ℝ) : ℂ))) W, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hε.1]
    have h1 : ‖cexp (W * ((-2 : ℝ) : ℂ))‖ / ‖W‖ ≤ 1 / (κ ε).re :=
      div_le_div₀ zero_le_one hE hpos hWn
    have hε0 := hε.1.le
    calc ε * (‖q j / ↑(ρ j)‖ * (‖cexp (W * ((-2 : ℝ) : ℂ))‖ / ‖W‖))
        ≤ ε * ((‖q j‖ * max 1 (ρ j)⁻¹) * (1 / (κ ε).re)) := by gcongr
      _ = (‖q j‖ * max 1 (ρ j)⁻¹) * (ε / (κ ε).re) := by ring
      _ ≤ (‖q j‖ * max 1 (ρ j)⁻¹) * (2 * m) := by gcongr
      _ = 2 * m * (‖q j‖ * max 1 (ρ j)⁻¹) := by ring
  have hT := tendsto_tsum_of_dominated_convergence (hq.mul_left (2 * (m : ℝ))) hlim hbound
  exact hT.congr' hsum_eq

/-- **Exponential sums whose aggregated rational coefficients vanish have no edge Abel spectrum.**
In particular this holds when no `ρ_j` is rational. -/
theorem tendsto_apLock_abel {q : ℕ → ℂ} {ρ : ℕ → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hq : Summable fun j => ‖q j‖ * max 1 (ρ j)⁻¹) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hagg : (∑' j, if (n : ℝ) * ρ j = m then q j else 0) = 0) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ y in Iic (-2 : ℝ), apLock q ρ (edgePt y) *
      cexp ((y : ℂ) * (edgeExp ((ε : ℂ) + (m : ℂ) * I) - ((Real.log n : ℝ) : ℂ) * I))) (𝓝[>] 0)
      (𝓝 0) := by
  have h := tendsto_apLock_abel_res hρ hq hm hn
  have he : (∑' j, if (n : ℝ) * ρ j = m then (n : ℂ) * q j else 0) =
      (n : ℂ) * ∑' j, if (n : ℝ) * ρ j = m then q j else 0 := by
    rw [← tsum_mul_left]; congr 1; funext j; split_ifs <;> simp
  rwa [he, hagg, mul_zero] at h

/-! ### Bohr means -/

/-- `(1/T) ∫_0^T e^{iθy} dy → [θ = 0]`. -/
theorem tendsto_mean_exp (θ : ℝ) :
    Tendsto (fun T : ℝ => (1 / T : ℂ) * ∫ y in (0 : ℝ)..T, cexp ((θ : ℂ) * I * y)) atTop
      (𝓝 (if θ = 0 then 1 else 0)) := by
  split_ifs with h
  · subst h
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one]
    have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    field_simp
  · have hc : (θ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast h) Complex.I_ne_zero
    have hbd : ∀ T : ℝ, ‖cexp ((θ : ℂ) * I * T) - cexp ((θ : ℂ) * I * (0 : ℝ))‖ ≤ 2 := by
      intro T
      have hn : ∀ x : ℝ, ‖cexp ((θ : ℂ) * I * x)‖ = 1 := by
        intro x; rw [Complex.norm_exp]; simp
      calc _ ≤ ‖cexp ((θ : ℂ) * I * T)‖ + ‖cexp ((θ : ℂ) * I * (0 : ℝ))‖ := norm_sub_le _ _
        _ = 2 := by rw [hn, hn]; norm_num
    refine squeeze_zero_norm' (a := fun T : ℝ => 2 / ‖(θ : ℂ) * I‖ * T⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with T hT
      rw [integral_exp_mul_complex hc, norm_mul, norm_div, norm_div]
      have hTn : ‖(1 : ℂ)‖ / ‖(T : ℂ)‖ = T⁻¹ := by
        rw [norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, one_div]
      rw [hTn]
      have hcn : 0 < ‖(θ : ℂ) * I‖ := norm_pos_iff.mpr hc
      calc T⁻¹ * (‖cexp ((θ : ℂ) * I * T) - cexp ((θ : ℂ) * I * (0 : ℝ))‖ / ‖(θ : ℂ) * I‖)
          ≤ T⁻¹ * (2 / ‖(θ : ℂ) * I‖) := by
            gcongr
            exact hbd T
        _ = 2 / ‖(θ : ℂ) * I‖ * T⁻¹ := by ring
    · simpa using tendsto_inv_atTop_zero.const_mul (2 / ‖(θ : ℂ) * I‖)

/-- **Bohr means of absolutely convergent exponential sums.** -/
theorem tendsto_mean_expSum {ι : Type*} [Countable ι] {c : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (θ : ι → ℝ) :
    Tendsto (fun T : ℝ => (1 / T : ℂ) * ∫ y in (0 : ℝ)..T, ∑' i, c i * cexp ((θ i : ℂ) * I * y))
      atTop (𝓝 (∑' i, if θ i = 0 then c i else 0)) := by
  have hterm : ∀ T : ℝ, 0 < T → (1 / T : ℂ) * ∫ y in (0 : ℝ)..T, ∑' i, c i *
      cexp ((θ i : ℂ) * I * y) =
      ∑' i, c i * ((1 / T : ℂ) * ∫ y in (0 : ℝ)..T, cexp ((θ i : ℂ) * I * y)) := by
    intro T hT
    have hF : ∀ i, Integrable (fun y : ℝ => c i * cexp ((θ i : ℂ) * I * y))
        (volume.restrict (Ioc 0 T)) := by
      intro i
      exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
    have hnorm : ∀ i, ∫ y in Ioc 0 T, ‖c i * cexp ((θ i : ℂ) * I * y)‖ = ‖c i‖ * T := by
      intro i
      have : ∀ y : ℝ, ‖c i * cexp ((θ i : ℂ) * I * y)‖ = ‖c i‖ := by
        intro y; rw [norm_mul, Complex.norm_exp]; simp
      simp only [this, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        Set.univ_inter, Real.volume_real_Ioc, smul_eq_mul]
      rw [max_eq_left (by linarith), sub_zero, mul_comm]
    have hsum : Summable fun i => ∫ y in Ioc 0 T, ‖c i * cexp ((θ i : ℂ) * I * y)‖ := by
      simp only [hnorm]; exact hc.mul_right T
    rw [intervalIntegral.integral_of_le hT.le, ← integral_tsum_of_summable_integral_norm hF hsum,
      ← tsum_mul_left]
    congr 1; funext i
    rw [intervalIntegral.integral_of_le hT.le, integral_const_mul]
    ring
  have hlim : ∀ i, Tendsto (fun T : ℝ => c i * ((1 / T : ℂ) * ∫ y in (0 : ℝ)..T,
      cexp ((θ i : ℂ) * I * y))) atTop (𝓝 (if θ i = 0 then c i else 0)) := by
    intro i
    have := (tendsto_mean_exp (θ i)).const_mul (c i)
    split_ifs at this ⊢ <;> simpa using this
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ i, ‖c i * ((1 / T : ℂ) * ∫ y in (0 : ℝ)..T,
      cexp ((θ i : ℂ) * I * y))‖ ≤ ‖c i‖ := by
    filter_upwards [eventually_gt_atTop 0] with T hT i
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [norm_mul]
    have hint : ‖∫ y in (0 : ℝ)..T, cexp ((θ i : ℂ) * I * y)‖ ≤ T := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
        (f := fun y : ℝ => cexp ((θ i : ℂ) * I * y)) (fun y _ => by
          rw [Complex.norm_exp]; simp)
      simpa [abs_of_pos hT] using h
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    calc 1 / T * ‖∫ y in (0 : ℝ)..T, cexp ((θ i : ℂ) * I * y)‖ ≤ 1 / T * T := by gcongr
      _ = 1 := by field_simp
  have hT := tendsto_tsum_of_dominated_convergence hc hlim hbound
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT0
  exact (hterm T hT0).symm

end

end AbelianTwist

end RHTower
