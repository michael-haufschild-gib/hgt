import GaloisForLFunctions.RHTower.SelbergPoincareContinuation
import GaloisForLFunctions.RHTower.SelbergMaassExpDecayCell
import GaloisForLFunctions.RHTower.SelbergPoincarePairing

open Complex MeasureTheory Topology Metric UpperHalfPlane
open scoped FourierTransform

/-!
# The continued Poincaré pairing and the pole of the Mellin side

`z ↦ Q_m(z,s)` is measurable (`measurable_Q`), so with the cusp integrability of the paired function and
`|Q_m| ≤ C(y^{-6}+y³)` the pairing `s ↦ ∫_{cellP} Q_m(z,s) g(z) dμ` is holomorphic on `3/4 < Re s < 3`
(`differentiableAt_pairing`). The Mellin side `∫_0^∞ y^{s-2} e^{-cy} a(y) dy` is holomorphic on `Re s > s₀` when
`|a| ≤ A y^{1-s₀}` near `0` and `a` is bounded (`differentiableAt_mel`). If `a = α y^{1-s₀} + O(y^{s₀})` and the Mellin
side stays bounded as real `s ↓ s₀`, then `α = 0` (`alpha_eq_zero`), since
`∫_0^1 y^{s-1-s₀} e^{-cy} dy ≥ e^{-c}/(s - s₀)` (`J_lower`) while the remaining parts stay bounded.
-/

namespace GaloisForLFunctions.RHTower.SelbergPoincarePole
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergPoincareContinuation

theorem measurable_ker (β : ℝ) (s : ℂ) : Measurable (fun p : ℝ × ℝ => ker β p.1 s p.2) := by
  unfold ker wt wz
  have h1 : Measurable (fun p : ℝ × ℝ => Real.log (p.1 / (p.2 ^ 2 + p.1 ^ 2))) :=
    Real.measurable_log.comp (by fun_prop)
  have h2 : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ) + (p.1 : ℂ) * Complex.I)⁻¹) :=
    (by fun_prop : Measurable (fun p : ℝ × ℝ => ((p.2 : ℂ) + (p.1 : ℂ) * Complex.I))).inv
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp h1)).sub
    (measurable_const.mul h2))

theorem measurable_fourier_ker (β : ℝ) (s : ℂ) (ξ : ℝ) : Measurable (fun y : ℝ => 𝓕 (ker β y s) ξ) := by
  simp_rw [Real.fourier_real_eq]
  have hF : StronglyMeasurable (fun p : ℝ × ℝ => 𝐞 (-(p.2 * ξ)) • ker β p.1 s p.2) := by
    apply Measurable.stronglyMeasurable
    have he : Continuous (fun p : ℝ × ℝ => (𝐞 (-(p.2 * ξ)) : Circle)) :=
      Real.continuous_fourierChar.comp (by fun_prop)
    exact he.measurable.smul (measurable_ker β s)
  exact (hF.integral_prod_right' (ν := volume)).measurable

theorem measurable_Q (M m : ℕ) (s : ℂ) : Measurable (fun z : ℍ => Q M m s z) := by
  unfold Q
  have hmain : Continuous (fun z : ℍ => (z.im : ℂ) ^ s * cexp (2 * Real.pi * Complex.I * m * (z : ℂ) / M)) := by
    refine Continuous.mul ?_ (by fun_prop)
    exact Continuous.cpow (by fun_prop) continuous_const (fun z => Complex.ofReal_mem_slitPlane.mpr z.im_pos)
  refine hmain.measurable.add (Measurable.tsum (fun c => ?_))
  unfold Qc
  by_cases hc : c = 0
  · simp only [if_pos hc]; exact measurable_const
  simp only [if_neg hc]
  refine measurable_const.mul (Measurable.tsum (fun n => ?_))
  have h1 : Measurable (fun z : ℍ => 𝓕 (ker (m / ((c : ℝ) ^ 2 * M) / M) (z.im / M) s) n) :=
    (measurable_fourier_ker _ s n).comp (by fun_prop)
  exact (h1.mul (by fun_prop)).mul measurable_const

open GaloisForLFunctions.RHTower.SarnakXuePretrace

/-- **Holomorphy of the continued pairing** `s ↦ ∫_{cellP} Q_m(z,s) g(z) dμ` on `3/4 < Re s < 3`. -/
theorem differentiableAt_pairing (M m : ℕ) [NeZero M] (hm : m ≠ 0) {g : ℍ → ℂ} (hgm : Measurable g)
    (hgi : IntegrableOn (fun z : ℍ => (z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) * ‖g z‖) (cellP M) volume)
    {s₀ : ℂ} (h1 : 3 / 4 < s₀.re) (h2 : s₀.re < 3) :
    DifferentiableAt ℂ (fun s => ∫ z in cellP M, Q M m s z * g z) s₀ := by
  set r := min ((s₀.re - 3 / 4) / 2) ((3 - s₀.re) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hr1 : r ≤ (s₀.re - 3 / 4) / 2 := min_le_left _ _
  have hr2 : r ≤ (3 - s₀.re) / 2 := min_le_right _ _
  set σ₁ := s₀.re - r
  set σ₂ := s₀.re + r
  set R := ‖s₀‖ + r
  have hσ₁ : 3 / 4 < σ₁ := by simp only [σ₁]; linarith
  have hσ₂ : σ₂ ≤ 3 := by simp only [σ₂]; linarith
  apply GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated hr
    (bound := fun z => qconst M m σ₁ R * ((z.im ^ (-6 : ℝ) + z.im ^ (3 : ℝ)) * ‖g z‖))
  · intro s _
    exact ((measurable_Q M m s).mul hgm).aestronglyMeasurable
  · intro z s hs
    obtain ⟨hs1, _, _⟩ := ball_props hs
    exact ((differentiableAt_Q M m z hm (by linarith)).mul_const _).differentiableWithinAt
  · intro z s hs
    obtain ⟨hs1, hs2, hs3⟩ := ball_props hs
    rw [norm_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_Q_le_poly M m z hm hσ₁ hσ₂ hs1 hs2 hs3) (norm_nonneg _)
  · exact hgi.const_mul _

open Set

/-- The Mellin side `∫_0^∞ y^{s-2} e^{-cy} a(y) dy`. -/
noncomputable def mel (c : ℝ) (a : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), ((y : ℂ)) ^ (s - 2) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y

/-- The integrand, extended by zero to `y ≤ 0` and written through `exp((s-2) log y)`. -/
noncomputable def melF (c : ℝ) (a : ℝ → ℂ) (s : ℂ) (y : ℝ) : ℂ :=
  if 0 < y then cexp ((s - 2) * (Real.log y : ℂ)) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y else 0

theorem mel_eq (c : ℝ) (a : ℝ → ℂ) (s : ℂ) : mel c a s = ∫ y in Ioi (0 : ℝ), melF c a s y := by
  unfold mel
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp only [melF, if_pos (show 0 < y from hy)]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (show (y : ℝ) ≠ 0 from ne_of_gt hy)),
    ← Complex.ofReal_log (le_of_lt hy), mul_comm (Real.log y : ℂ)]

theorem norm_melF (c : ℝ) (a : ℝ → ℂ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    ‖melF c a s y‖ = y ^ (s.re - 2) * Real.exp (-c * y) * ‖a y‖ := by
  simp only [melF, if_pos hy, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.rpow_def_of_pos hy]
  congr 2
  simp [Complex.mul_re]; ring

/-- **Holomorphy of the Mellin side** for `Re s > s₀`, given `|a(y)| ≤ A y^{1-s₀}` on `(0,1]` and `|a| ≤ B`. -/
theorem differentiableAt_mel {c A B s₀ : ℝ} (hc : 0 < c) {a : ℝ → ℂ} (ha : ContinuousOn a (Ioi 0))
    (hA : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ A * y ^ (1 - s₀)) (hB : ∀ y, 0 < y → ‖a y‖ ≤ B)
    {s₁ : ℂ} (h : s₀ < s₁.re) : DifferentiableAt ℂ (mel c a) s₁ := by
  have hmel : mel c a = fun s => ∫ y in Ioi (0 : ℝ), melF c a s y := funext (mel_eq c a)
  rw [hmel]
  set r := (s₁.re - s₀) / 2
  have hr : 0 < r := by simp only [r]; linarith
  set σ₁ := s₁.re - r
  set σ₂ := s₁.re + r
  have hσ₁ : s₀ < σ₁ := by simp only [σ₁, r]; linarith
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 1 ⟨one_pos, le_rfl⟩); simpa using this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  set bnd : ℝ → ℝ := fun y => if 0 < y then A * Real.exp c * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) +
    B * (y ^ |σ₂| * Real.exp (-c * y)) else 0
  apply GaloisForLFunctions.HTGeometry.differentiableAt_integral_of_cauchy_dominated hr (bound := bnd)
  · intro s _
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have : EqOn (melF c a s) (fun y => cexp ((s - 2) * (Real.log y : ℂ)) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y) (Ioi 0) :=
      fun y hy => by simp only [melF, if_pos (show 0 < y from hy)]
    refine ContinuousOn.congr ?_ this
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ha
    refine (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_))
    exact Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono (fun y hy => ne_of_gt hy))
  · intro y
    by_cases hy : 0 < y
    · simp only [melF, if_pos hy]
      exact (((differentiable_id.sub_const 2).mul_const _).cexp.mul_const _ |>.mul_const _).differentiableOn
    · simp only [melF, if_neg hy]; exact differentiableOn_const _
  · intro y s hs
    obtain ⟨hs1, hs2, _⟩ := ball_props hs
    by_cases hy : 0 < y
    · rw [norm_melF c a s hy]
      have he := Real.exp_pos (-c * y)
      rcases le_or_gt y 1 with hy1 | hy1
      · have h1 : y ^ (s.re - 2) ≤ y ^ (σ₁ - 2) := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
        have h2 := hA y ⟨hy, hy1⟩
        have hec : 1 ≤ Real.exp c := Real.one_le_exp hc.le
        have hp : y ^ (σ₁ - 2) * y ^ (1 - s₀) = y ^ (σ₁ - 1 - s₀) := by
          rw [← Real.rpow_add hy]; congr 1; ring
        have hbnd2 : 0 ≤ B * (y ^ |σ₂| * Real.exp (-c * y)) := by positivity
        calc y ^ (s.re - 2) * Real.exp (-c * y) * ‖a y‖ ≤ y ^ (σ₁ - 2) * Real.exp (-c * y) * (A * y ^ (1 - s₀)) := by
              gcongr
          _ = A * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) := by rw [← hp]; ring
          _ ≤ A * Real.exp c * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) := by
              have : 0 ≤ A * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) := by positivity
              nlinarith
          _ ≤ bnd y := by simp only [bnd, if_pos hy]; linarith
      · have h1 : y ^ (s.re - 2) ≤ y ^ |σ₂| :=
          Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith [le_abs_self σ₂])
        have h2 := hB y hy
        have hbnd1 : 0 ≤ A * Real.exp c * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) := by positivity
        calc y ^ (s.re - 2) * Real.exp (-c * y) * ‖a y‖ ≤ y ^ |σ₂| * Real.exp (-c * y) * B := by gcongr
          _ ≤ bnd y := by simp only [bnd, if_pos hy]; linarith
    · simp only [melF, if_neg hy, norm_zero, bnd, le_refl]
  · have i1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ₁ - 1 - s₀) (by linarith) le_rfl hc
    have i2 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := |σ₂|) (by linarith [abs_nonneg σ₂]) le_rfl hc
    simp only [Real.rpow_one] at i1 i2
    have hI : IntegrableOn (fun y => A * Real.exp c * (y ^ (σ₁ - 1 - s₀) * Real.exp (-c * y)) +
        B * (y ^ |σ₂| * Real.exp (-c * y))) (Ioi 0) := (i1.const_mul _).add (i2.const_mul _)
    exact hI.congr_fun (fun y hy => by simp only [bnd, if_pos (show 0 < y from hy)]) measurableSet_Ioi

/-- Integrability of the Mellin integrand for real `s ∈ (s₀, 2]`. -/
theorem integrableOn_mel_real {c A B s₀ : ℝ} (hc : 0 < c) {a : ℝ → ℂ} (ha : ContinuousOn a (Ioi 0))
    (hA : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ A * y ^ (1 - s₀)) (hB : ∀ y, 0 < y → ‖a y‖ ≤ B)
    {s : ℝ} (hs : s₀ < s) (hs2 : s ≤ 2) :
    IntegrableOn (fun y : ℝ => ((y : ℂ)) ^ ((s : ℂ) - 2) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y) (Ioi 0) := by
  have hA0 : 0 ≤ A := by
    have := (norm_nonneg _).trans (hA 1 ⟨one_pos, le_rfl⟩); simpa using this
  have i1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 - s₀) (by linarith) le_rfl hc
  have i2 := exp_neg_integrableOn_Ioi 0 hc
  simp only [Real.rpow_one] at i1
  have hI : IntegrableOn (fun y => A * Real.exp c * (y ^ (s - 1 - s₀) * Real.exp (-c * y)) +
      B * Real.exp (-c * y)) (Ioi 0) := (i1.const_mul _).add (i2.const_mul _)
  refine hI.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul ?_ (by fun_prop)) ha
    exact ContinuousOn.cpow_const (Complex.continuous_ofReal.continuousOn)
      (fun y hy => Complex.ofReal_mem_slitPlane.mpr hy)
  · have hy0 : 0 < y := hy
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_ofNat]
    have he := Real.exp_pos (-c * y)
    rcases le_or_gt y 1 with hy1 | hy1
    · have h2 := hA y ⟨hy0, hy1⟩
      have hec : 1 ≤ Real.exp c := Real.one_le_exp hc.le
      have hp : y ^ (s - 2) * y ^ (1 - s₀) = y ^ (s - 1 - s₀) := by rw [← Real.rpow_add hy0]; congr 1; ring
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y hy0)
      calc y ^ (s - 2) * Real.exp (-c * y) * ‖a y‖ ≤ y ^ (s - 2) * Real.exp (-c * y) * (A * y ^ (1 - s₀)) := by
            gcongr
        _ = A * (y ^ (s - 1 - s₀) * Real.exp (-c * y)) := by rw [← hp]; ring
        _ ≤ A * Real.exp c * (y ^ (s - 1 - s₀) * Real.exp (-c * y)) + B * Real.exp (-c * y) := by
            have : 0 ≤ A * (y ^ (s - 1 - s₀) * Real.exp (-c * y)) := by positivity
            have : 0 ≤ B * Real.exp (-c * y) := by positivity
            nlinarith
    · have h1 : y ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith)
      have h2 := hB y hy0
      have hA' : 0 ≤ A * Real.exp c * (y ^ (s - 1 - s₀) * Real.exp (-c * y)) := by positivity
      calc y ^ (s - 2) * Real.exp (-c * y) * ‖a y‖ ≤ 1 * Real.exp (-c * y) * B := by gcongr
        _ ≤ _ := by linarith

theorem integral_Ioc_rpow {r : ℝ} (hr : -1 < r) : ∫ y in Ioc (0 : ℝ) 1, y ^ r = 1 / (r + 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith)]; ring

theorem integrableOn_Ioc_rpow {r : ℝ} (hr : -1 < r) : IntegrableOn (fun y : ℝ => y ^ r) (Ioc 0 1) := by
  have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this

/-- `∫_0^1 y^{s-1-s₀} e^{-cy} dy ≥ e^{-c}/(s - s₀)`. -/
theorem J_lower {c s s₀ : ℝ} (hc : 0 < c) (hs : s₀ < s) :
    Real.exp (-c) / (s - s₀) ≤ ∫ y in Ioc (0 : ℝ) 1, y ^ (s - 1 - s₀) * Real.exp (-c * y) := by
  have hr : -1 < s - 1 - s₀ := by linarith
  have h1 : ∫ y in Ioc (0 : ℝ) 1, y ^ (s - 1 - s₀) * Real.exp (-c) = Real.exp (-c) / (s - s₀) := by
    rw [integral_mul_const, integral_Ioc_rpow hr]; field_simp
    rw [show s - 1 - s₀ + 1 = s - s₀ by ring]
  rw [← h1]
  have hi1 : IntegrableOn (fun y : ℝ => y ^ (s - 1 - s₀) * Real.exp (-c)) (Ioc 0 1) :=
    (integrableOn_Ioc_rpow hr).mul_const _
  have hi2 : IntegrableOn (fun y : ℝ => y ^ (s - 1 - s₀) * Real.exp (-c * y)) (Ioc 0 1) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 - s₀) hr le_rfl hc
    simp only [Real.rpow_one] at this
    exact this.mono_set Ioc_subset_Ioi_self
  refine setIntegral_mono_on hi1 hi2 measurableSet_Ioc (fun y hy => ?_)
  have hy0 : 0 < y := hy.1
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
  apply Real.exp_le_exp.mpr
  nlinarith [hy.2]

/-- **The pole forces `α = 0`.** If `a(y) = α y^{1-s₀} + O(y^{s₀})` on `(0,1]` (`1/2 < s₀ < 1`), `a` is bounded,
and the Mellin side stays bounded as real `s ↓ s₀`, then `α = 0`: otherwise it grows like `|α| e^{-c}/(s - s₀)`. -/
theorem alpha_eq_zero {c C B s₀ : ℝ} {α : ℂ} (hc : 0 < c) (hs₀ : 1 / 2 < s₀) (hs₀1 : s₀ < 1)
    {a : ℝ → ℂ} (ha : ContinuousOn a (Ioi 0))
    (hE : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ ≤ C * y ^ s₀)
    (hB : ∀ y, 0 < y → ‖a y‖ ≤ B) {δ K : ℝ} (hδ : 0 < δ)
    (hK : ∀ s : ℝ, s₀ < s → s < s₀ + δ → ‖mel c a s‖ ≤ K) : α = 0 := by
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hE 1 ⟨one_pos, le_rfl⟩); simpa using this
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1 one_pos)
  -- `|a| ≤ (|α| + C) y^{1-s₀}` on `(0,1]`
  have hA : ∀ y ∈ Ioc (0 : ℝ) 1, ‖a y‖ ≤ (‖α‖ + C) * y ^ (1 - s₀) := by
    intro y hy
    have hy0 := hy.1
    have hle : y ^ s₀ ≤ y ^ (1 - s₀) := Real.rpow_le_rpow_of_exponent_ge hy0 hy.2 (by linarith)
    have h1 := hE y hy
    have h2 : ‖α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ = ‖α‖ * y ^ (1 - s₀) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy0.le _)]
    calc ‖a y‖ = ‖(a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)) + α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖ := by ring_nf
      _ ≤ C * y ^ s₀ + ‖α‖ * y ^ (1 - s₀) := (norm_add_le _ _).trans (by rw [h2]; linarith)
      _ ≤ C * y ^ (1 - s₀) + ‖α‖ * y ^ (1 - s₀) := by gcongr
      _ = _ := by ring
  set Kt := ∫ y in Ioi (1 : ℝ), B * Real.exp (-c * y)
  have hKt : 0 ≤ Kt := setIntegral_nonneg measurableSet_Ioi (fun y _ => by positivity)
  set L := K + C / (2 * s₀ - 1) + Kt
  -- the key estimate
  have hkey : ∀ s : ℝ, s₀ < s → s < s₀ + δ → s ≤ 2 → ‖α‖ * (Real.exp (-c) / (s - s₀)) ≤ L := by
    intro s hs hsδ hs2
    set F : ℝ → ℂ := fun y => ((y : ℂ)) ^ ((s : ℂ) - 2) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y
    have hF := integrableOn_mel_real hc ha hA hB hs hs2
    have hmel : mel c a s = (∫ y in Ioc (0 : ℝ) 1, F y) + ∫ y in Ioi (1 : ℝ), F y := by
      unfold mel
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi zero_le_one))]
    -- decomposition on `(0,1]`
    have hr : -1 < s - 1 - s₀ := by linarith
    set G1 : ℝ → ℝ := fun y => y ^ (s - 1 - s₀) * Real.exp (-c * y)
    have hG1 : IntegrableOn G1 (Ioc 0 1) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1 - s₀) hr le_rfl hc
      simp only [Real.rpow_one] at this
      exact this.mono_set Ioc_subset_Ioi_self
    have hcpow : ∀ y ∈ Ioc (0 : ℝ) 1, ((y : ℂ)) ^ ((s : ℂ) - 2) = ((y ^ (s - 2) : ℝ) : ℂ) := by
      intro y hy
      rw [Complex.ofReal_cpow hy.1.le]; push_cast; rfl
    set G2 : ℝ → ℂ := fun y => F y - α * (G1 y : ℂ)
    have hsplit : ∫ y in Ioc (0 : ℝ) 1, F y = α * ((∫ y in Ioc (0 : ℝ) 1, G1 y : ℝ) : ℂ) + ∫ y in Ioc (0 : ℝ) 1, G2 y := by
      have h1 : IntegrableOn (fun y => α * ((G1 y : ℝ) : ℂ)) (Ioc 0 1) := (hG1.ofReal (𝕜 := ℂ)).const_mul α
      have h2 : IntegrableOn G2 (Ioc 0 1) := (hF.mono_set Ioc_subset_Ioi_self).sub h1
      calc ∫ y in Ioc (0 : ℝ) 1, F y = ∫ y in Ioc (0 : ℝ) 1, (α * ((G1 y : ℝ) : ℂ) + G2 y) := by
            congr 1; funext y; simp only [G2]; ring
        _ = (∫ y in Ioc (0 : ℝ) 1, α * ((G1 y : ℝ) : ℂ)) + ∫ y in Ioc (0 : ℝ) 1, G2 y := integral_add h1 h2
        _ = _ := by rw [integral_const_mul, integral_complex_ofReal]
    have hG2 : ‖∫ y in Ioc (0 : ℝ) 1, G2 y‖ ≤ C / (2 * s₀ - 1) := by
      have hr2 : -1 < s + s₀ - 2 := by linarith
      have hb : ∀ y ∈ Ioc (0 : ℝ) 1, ‖G2 y‖ ≤ C * y ^ (s + s₀ - 2) := by
        intro y hy
        have hy0 := hy.1
        simp only [G2, F, G1]
        rw [hcpow y hy]
        have e : ((y ^ (s - 2) : ℝ) : ℂ) * ((Real.exp (-c * y) : ℝ) : ℂ) * a y -
            α * ((y ^ (s - 1 - s₀) * Real.exp (-c * y) : ℝ) : ℂ) =
            ((y ^ (s - 2) * Real.exp (-c * y) : ℝ) : ℂ) * (a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)) := by
          have hp : y ^ (s - 1 - s₀) = y ^ (s - 2) * y ^ (1 - s₀) := by
            rw [← Real.rpow_add hy0]; congr 1; ring
          rw [hp]; push_cast; ring
        rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have he1 : Real.exp (-c * y) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hy.1])
        have hp2 : y ^ (s - 2) * y ^ s₀ = y ^ (s + s₀ - 2) := by rw [← Real.rpow_add hy0]; congr 1; ring
        calc y ^ (s - 2) * Real.exp (-c * y) * ‖a y - α * ((y ^ (1 - s₀) : ℝ) : ℂ)‖
            ≤ y ^ (s - 2) * 1 * (C * y ^ s₀) := by gcongr; exact hE y hy
          _ = C * y ^ (s + s₀ - 2) := by rw [← hp2]; ring
      have hint : IntegrableOn (fun y : ℝ => C * y ^ (s + s₀ - 2)) (Ioc 0 1) := (integrableOn_Ioc_rpow hr2).const_mul C
      calc ‖∫ y in Ioc (0 : ℝ) 1, G2 y‖ ≤ ∫ y in Ioc (0 : ℝ) 1, C * y ^ (s + s₀ - 2) :=
            norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioc hb)
        _ = C / (s + s₀ - 1) := by
            rw [integral_const_mul, integral_Ioc_rpow hr2, show s + s₀ - 2 + 1 = s + s₀ - 1 by ring]; ring
        _ ≤ C / (2 * s₀ - 1) := div_le_div_of_nonneg_left hC0 (by linarith) (by linarith)
    have htail : ‖∫ y in Ioi (1 : ℝ), F y‖ ≤ Kt := by
      have hint : IntegrableOn (fun y : ℝ => B * Real.exp (-c * y)) (Ioi 1) := (exp_neg_integrableOn_Ioi 1 hc).const_mul B
      refine norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi (fun y hy => ?_))
      have hy1 : 1 < y := hy
      have hy0 : 0 < y := by linarith
      simp only [F]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.re_ofNat]
      have h1 : y ^ (s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith)
      calc y ^ (s - 2) * Real.exp (-c * y) * ‖a y‖ ≤ 1 * Real.exp (-c * y) * B := by
            gcongr; exact hB y hy0
        _ = B * Real.exp (-c * y) := by ring
    have hJ := J_lower (s := s) (s₀ := s₀) hc hs
    have hJ0 : 0 ≤ Real.exp (-c) / (s - s₀) := by have : 0 < s - s₀ := by linarith
                                                  positivity
    have hnorm : ‖α‖ * (∫ y in Ioc (0 : ℝ) 1, G1 y) ≤ L := by
      have hαJ : ‖α * ((∫ y in Ioc (0 : ℝ) 1, G1 y : ℝ) : ℂ)‖ = ‖α‖ * ∫ y in Ioc (0 : ℝ) 1, G1 y := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJ0.trans hJ)]
      rw [← hαJ]
      have heq : α * ((∫ y in Ioc (0 : ℝ) 1, G1 y : ℝ) : ℂ) = mel c a s - (∫ y in Ioc (0 : ℝ) 1, G2 y) -
          ∫ y in Ioi (1 : ℝ), F y := by rw [hmel, hsplit]; ring
      rw [heq]
      calc ‖mel c a s - (∫ y in Ioc (0 : ℝ) 1, G2 y) - ∫ y in Ioi (1 : ℝ), F y‖
          ≤ ‖mel c a s‖ + ‖∫ y in Ioc (0 : ℝ) 1, G2 y‖ + ‖∫ y in Ioi (1 : ℝ), F y‖ := by
            refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
        _ ≤ K + C / (2 * s₀ - 1) + Kt := add_le_add (add_le_add (hK s hs hsδ) hG2) htail
    exact (mul_le_mul_of_nonneg_left hJ (norm_nonneg α)).trans hnorm
  -- conclude
  by_contra hα
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK (s₀ + δ / 2) (by linarith) (by linarith))
  have hL : 0 ≤ L := by
    have : 0 ≤ C / (2 * s₀ - 1) := div_nonneg hC0 (by linarith)
    simp only [L]; linarith
  set ε := min (min (δ / 2) ((2 - s₀) / 2)) (‖α‖ * Real.exp (-c) / (2 * (L + 1)))
  have hε : 0 < ε := lt_min (lt_min (half_pos hδ) (by linarith)) (by positivity)
  have h := hkey (s₀ + ε) (by linarith) (by
      have := min_le_left (min (δ / 2) ((2 - s₀) / 2)) (‖α‖ * Real.exp (-c) / (2 * (L + 1)))
      have := min_le_left (δ / 2) ((2 - s₀) / 2); linarith) (by
      have := min_le_left (min (δ / 2) ((2 - s₀) / 2)) (‖α‖ * Real.exp (-c) / (2 * (L + 1)))
      have := min_le_right (δ / 2) ((2 - s₀) / 2); linarith)
  rw [show s₀ + ε - s₀ = ε by ring] at h
  have hε2 : ε ≤ ‖α‖ * Real.exp (-c) / (2 * (L + 1)) := min_le_right _ _
  have hec : 0 < Real.exp (-c) := Real.exp_pos _
  rw [mul_div_assoc', div_le_iff₀ hε] at h
  rw [le_div_iff₀ (by positivity)] at hε2
  nlinarith

end GaloisForLFunctions.RHTower.SelbergPoincarePole
