import GaloisForLFunctions.RHTower.RiemannKernelModulatedWindowTests

/-!
# Floquet block tests for radical pairings on lattice-periodic supports

With `X(ξ) = Ξ(2πξ)` and `K = Φ⋆Φ̃` (`𝓕K = X²`), a full-cone Weil-positive `lam` pairs
nonnegatively with every radical test. This module builds radical tests whose transform takes
prescribed values on a lattice `ℓℤ` and on a shifted lattice `α + ℓℤ`.

**Window tests** (`spectralWindowTest`, `riemannPairForm_spectralWindowTest`). For a smooth real `h`
supported in `|ξ| < R < 1633/1000`, the test `g = 𝓕⁻(h/X)` has pairing `∫ h(ξ)² e^{2πiξy} dξ`.
Finite families pair nonnegatively with deviations of logarithmic size
(`spectralWindowTests_pairing_nonneg`).

**Period partition** (`floquetBump`). `ψ(x) = sin(πτ(x)/2) sin(πτ(P − x)/2)`, with `τ` a smooth
ramp across `[−δ, δ]`, is supported in `[−δ, P + δ]` and satisfies `Σ_n ψ(ξ + nP)² = 1`
(`floquetBump_fiber`).

**Fiber identity** (`integral_blockSq_spectralChar`). With `Pℓ = 1`, the block
`ψ(η − kP)² w(η − kP)`, for `w` that is `P`-periodic on the overlap, has transform at `β + qℓ`
equal to `∫₀^P w(ξ) e^{2πiξ(β+qℓ)} e^{2πikPβ} Ψ_β(ξ) dξ`, where
`Ψ_β(ξ) = ψ(ξ − P)² e^{−2πiPβ} + ψ(ξ)² + ψ(ξ + P)² e^{2πiPβ}` (`fiberPhase`). Integer frequencies
`qℓ` see only the fiber sum, so lattice values are Fourier coefficients of fiber data.

**Three blocks** (`floquetTransform_lattice_zero`, `floquetTransform_lattice_alpha`). Blocks at
offsets `k = −2, 0, 1`, weighted by the barycentric coordinates (`floquetWeight`) of a target
`(u, x)` with respect to the vertices `e^{2πikPα}`, give transform `∫₀^P u(ξ) e^{2πiξqℓ} dξ` on
`ℓℤ` and `∫₀^P x(ξ) e^{2πiξ(α+qℓ)} Ψ_α(ξ) dξ` on `α + ℓℤ`. The weights are nonnegative as soon as
the vertex triangle contains `0` and the target is small, so the tests are radical tests with
exactly prescribed lattice values (`floquet_pairing_nonneg`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## Window profile tests -/

/-- The profile `h/X` of a real window `h`. -/
def windowProfile (h : ℝ → ℝ) (ξ : ℝ) : ℂ := ((h ξ * (phiFourierReal ξ)⁻¹ : ℝ) : ℂ)

theorem contDiff_windowProfile {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {R : ℝ}
    (hR : R < 1633 / 1000) (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (windowProfile h) := by
  refine Complex.ofRealCLM.contDiff.comp ?_
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : |x| ≤ 1633 / 1000
  · exact hh.contDiffAt.mul
      (contDiff_phiFourierReal.contDiffAt.inv (phiFourierReal_ne_zero_of_abs_le hx))
  · push Not at hx
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    have hev : ∀ᶠ ξ in 𝓝 x, |ξ| ∈ Ioi R :=
      (continuous_abs.tendsto x).eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [hev] with ξ hξ
    change h ξ * (phiFourierReal ξ)⁻¹ = 0
    rw [hsupp ξ (le_of_lt hξ), zero_mul]

theorem hasCompactSupport_windowProfile {h : ℝ → ℝ} {R : ℝ} (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) :
    HasCompactSupport (windowProfile h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun x hx => ?_
  have h1 : R ≤ |x| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rw [le_abs]
    rcases hx with h | h
    · right; linarith
    · left; linarith
  simp [windowProfile, hsupp x h1]

/-- The window test `g = 𝓕⁻(h/X)` as a Schwartz function. -/
def spectralWindowTest {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {R : ℝ} (hR : R < 1633 / 1000)
    (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) : SchwartzMap ℝ ℂ :=
  𝓕⁻ ((hasCompactSupport_windowProfile hsupp).toSchwartzMap (contDiff_windowProfile hh hR hsupp))

theorem fourier_spectralWindowTest {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {R : ℝ}
    (hR : R < 1633 / 1000) (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) :
    𝓕 (spectralWindowTest hh hR hsupp : ℝ → ℂ) = windowProfile h := by
  rw [← SchwartzMap.fourier_coe, spectralWindowTest, FourierInvPair.fourier_fourierInv_eq]
  rfl

theorem exists_spectralWindowTest_decay {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {R : ℝ}
    (hR : R < 1633 / 1000) (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) (m : ℕ) :
    ∃ D : ℝ, ∀ x, ‖spectralWindowTest hh hR hsupp x‖ ≤ D * ((1 + |x|) ^ m)⁻¹ := by
  set f := spectralWindowTest hh hR hsupp
  refine ⟨2 ^ m * ((Finset.Iic (m, 0)).sup fun p => SchwartzMap.seminorm ℝ p.1 p.2) f,
    fun x => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0)) (k := m) (n := 0)
    le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rw [le_mul_inv_iff₀ (by positivity), mul_comm]
  exact h

theorem phiFourier_sq_mul_windowProfile {h : ℝ → ℝ} {R : ℝ} (hR : R < 1633 / 1000)
    (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) (ξ : ℝ) :
    phiFourier ξ ^ 2 * (windowProfile h ξ * conj (windowProfile h ξ)) = ((h ξ ^ 2 : ℝ) : ℂ) := by
  unfold windowProfile
  rw [phiFourier_eq_ofReal, Complex.conj_ofReal]
  by_cases hx : |ξ| ≤ 1633 / 1000
  · have hP : (phiFourierReal ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (phiFourierReal_ne_zero_of_abs_le hx)
    push_cast
    field_simp
  · push Not at hx
    rw [hsupp ξ (by linarith)]
    push_cast; ring

/-- The pairing of a window test is the Fourier transform of `h²`. -/
theorem riemannPairForm_spectralWindowTest {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {R : ℝ}
    (hR : R < 1633 / 1000) (hsupp : ∀ ξ, R ≤ |ξ| → h ξ = 0) (y : ℝ) :
    riemannPairForm riemannAutocorr (spectralWindowTest hh hR hsupp) y =
      ∫ ξ, ((h ξ ^ 2 : ℝ) : ℂ) * spectralChar ξ y := by
  have hg : Continuous (spectralWindowTest hh hR hsupp : ℝ → ℂ) := SchwartzMap.continuous _
  have hgi : Integrable (spectralWindowTest hh hR hsupp : ℝ → ℂ) := SchwartzMap.integrable _
  rw [riemannPairForm_eq_integral_fourier hg hgi, fourier_spectralWindowTest]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [phiFourier_sq_mul_windowProfile hR hsupp]

/-- Summability of the pairing sequence of a decaying test against a sparse deviation. -/
theorem summable_normDeficit_pairing {lam : ℕ → ℝ} {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {g : ℝ → ℂ} {D : ℝ} (hD : ∀ x, ‖g x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹) :
    Summable fun n : ℕ => ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) +
        riemannPairForm riemannAutocorr g (-Real.log n)) := by
  obtain ⟨B, hB0, hB⟩ := exists_riemannAutocorr_mul_pow_le k
  set c := D ^ 2 * B * (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) ^ 2 with hc
  refine Summable.of_norm_bounded (hZ.mul_left (2 * c)) fun n => ?_
  have h1 := norm_riemannPairForm_le_of_decay hB hD (Real.log n)
  have h2 := norm_riemannPairForm_le_of_decay hB hD (-Real.log n)
  rw [abs_neg] at h2
  rw [← hc] at h1 h2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h3 := norm_add_le (riemannPairForm riemannAutocorr g (Real.log n))
    (riemannPairForm riemannAutocorr g (-Real.log n))
  have ha := abs_nonneg (normDeficit lam n)
  calc |normDeficit lam n| * ‖riemannPairForm riemannAutocorr g (Real.log n) +
        riemannPairForm riemannAutocorr g (-Real.log n)‖
      ≤ |normDeficit lam n| * (2 * (c * ((1 + |Real.log n|) ^ k)⁻¹)) :=
        mul_le_mul_of_nonneg_left (by linarith) ha
    _ = _ := by ring

/-- **Positivity for finite families of window tests.** -/
theorem spectralWindowTests_pairing_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {ι : Type*} (s : Finset ι) (h : ι → ℝ → ℝ) (hh : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i)) {R : ℝ}
    (hR : R < 1633 / 1000) (hsupp : ∀ i ξ, R ≤ |ξ| → h i ξ = 0) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) * ∑ i ∈ s,
      (riemannPairForm riemannAutocorr (spectralWindowTest (hh i) hR (hsupp i)) (Real.log n) +
        riemannPairForm riemannAutocorr (spectralWindowTest (hh i) hR (hsupp i)) (-Real.log n))).re := by
  have hdec : ∀ i, ∃ D : ℝ, ∀ x, ‖spectralWindowTest (hh i) hR (hsupp i) x‖ ≤
      D * ((1 + |x|) ^ (k + 2))⁻¹ := fun i => exists_spectralWindowTest_decay (hh i) hR (hsupp i) (k + 2)
  have hsum : ∀ i ∈ s, Summable fun n : ℕ => ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr (spectralWindowTest (hh i) hR (hsupp i)) (Real.log n) +
        riemannPairForm riemannAutocorr (spectralWindowTest (hh i) hR (hsupp i)) (-Real.log n)) := by
    intro i _
    obtain ⟨D, hD⟩ := hdec i
    exact summable_normDeficit_pairing hZ hD
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨D, hD⟩ := hdec i
  exact normDeficit_pairing_nonneg_of_decay_log hW hA hZ (SchwartzMap.continuous _) hD

/-! ## A smooth square partition of unity along a period -/

theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  rw [sub_sub_cancel]
  have h := Real.smoothTransition.pos_denom x
  have h' : expNegInvGlue (1 - x) + expNegInvGlue x ≠ 0 := by linarith
  rw [div_add_div _ _ h.ne' h', div_eq_one_iff_eq (mul_ne_zero h.ne' h')]
  ring

/-- The rising edge `τ(x) = S((x + δ)/(2δ))`: `0` below `−δ`, `1` above `δ`. -/
def edgeRamp (δ x : ℝ) : ℝ := Real.smoothTransition ((x + δ) / (2 * δ))

theorem edgeRamp_add_neg {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : edgeRamp δ x + edgeRamp δ (-x) = 1 := by
  unfold edgeRamp
  have e : (-x + δ) / (2 * δ) = 1 - (x + δ) / (2 * δ) := by field_simp; ring
  rw [e, smoothTransition_add_one_sub]

theorem edgeRamp_eq_zero {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ -δ) : edgeRamp δ x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem edgeRamp_eq_one {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : edgeRamp δ x = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)

theorem contDiff_edgeRamp (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (edgeRamp δ) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)

/-- The period bump `ψ(x) = sin(πτ(x)/2) sin(πτ(P − x)/2)`: supported in `[−δ, P + δ]`, equal to
`1` on `[δ, P − δ]`, with `ψ(x)² + ψ(x + P)² = 1` on the overlap `[−δ, δ]`. -/
def floquetBump (δ P x : ℝ) : ℝ :=
  Real.sin (π / 2 * edgeRamp δ x) * Real.sin (π / 2 * edgeRamp δ (P - x))

theorem contDiff_floquetBump (δ P : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (floquetBump δ P) :=
  (Real.contDiff_sin.comp (contDiff_const.mul (contDiff_edgeRamp δ))).mul
    (Real.contDiff_sin.comp (contDiff_const.mul ((contDiff_edgeRamp δ).comp
      (contDiff_const.sub contDiff_id))))

theorem floquetBump_eq_zero_of_le {δ P x : ℝ} (hδ : 0 < δ) (hx : x ≤ -δ) :
    floquetBump δ P x = 0 := by
  unfold floquetBump; rw [edgeRamp_eq_zero hδ hx]; simp

theorem floquetBump_eq_zero_of_ge {δ P x : ℝ} (hδ : 0 < δ) (hx : P + δ ≤ x) :
    floquetBump δ P x = 0 := by
  unfold floquetBump; rw [edgeRamp_eq_zero hδ (by linarith : P - x ≤ -δ)]; simp

theorem floquetBump_eq_one {δ P x : ℝ} (hδ : 0 < δ) (h1 : δ ≤ x) (h2 : x ≤ P - δ) :
    floquetBump δ P x = 1 := by
  unfold floquetBump
  rw [edgeRamp_eq_one hδ h1, edgeRamp_eq_one hδ (by linarith : δ ≤ P - x)]
  simp

theorem floquetBump_sq_add_sq {δ P x : ℝ} (hδ : 0 < δ) (hP : 2 * δ ≤ P) (h1 : -δ ≤ x)
    (h2 : x ≤ δ) : floquetBump δ P x ^ 2 + floquetBump δ P (x + P) ^ 2 = 1 := by
  unfold floquetBump
  rw [edgeRamp_eq_one hδ (by linarith : δ ≤ P - x), edgeRamp_eq_one hδ (by linarith : δ ≤ x + P),
    show P - (x + P) = -x by ring]
  have e := edgeRamp_add_neg hδ x
  have e2 : π / 2 * edgeRamp δ (-x) = π / 2 - π / 2 * edgeRamp δ x := by
    rw [show edgeRamp δ (-x) = 1 - edgeRamp δ x by linarith]; ring
  rw [e2, Real.sin_pi_div_two_sub, mul_one, Real.sin_pi_div_two, mul_one, one_mul, Real.sin_sq_add_cos_sq]

/-- On a period, the three shifted squares sum to `1`. -/
theorem floquetBump_fiber {δ P ξ : ℝ} (hδ : 0 < δ) (hP : 2 * δ ≤ P) (h0 : 0 ≤ ξ) (h1 : ξ ≤ P) :
    floquetBump δ P (ξ - P) ^ 2 + floquetBump δ P ξ ^ 2 + floquetBump δ P (ξ + P) ^ 2 = 1 := by
  rcases le_or_gt ξ δ with ha | ha
  · rw [floquetBump_eq_zero_of_le hδ (by linarith : ξ - P ≤ -δ)]
    have := floquetBump_sq_add_sq hδ hP (by linarith : -δ ≤ ξ) ha
    linarith [sq_nonneg (0 : ℝ)]
  rcases le_or_gt ξ (P - δ) with hb | hb
  · rw [floquetBump_eq_zero_of_le hδ (by linarith : ξ - P ≤ -δ),
      floquetBump_eq_one hδ ha.le hb, floquetBump_eq_zero_of_ge hδ (by linarith : P + δ ≤ ξ + P)]
    norm_num
  · rw [floquetBump_eq_zero_of_ge hδ (by linarith : P + δ ≤ ξ + P)]
    have := floquetBump_sq_add_sq hδ hP (by linarith : -δ ≤ ξ - P) (by linarith : ξ - P ≤ δ)
    rw [sub_add_cancel] at this
    linarith

/-! ## Unfolding an integral over three periods -/

theorem integral_eq_intervalIntegral_three_periods {F : ℝ → ℂ} (hF : Continuous F) {P c : ℝ}
    (hP : 0 < P) (hsupp : ∀ η, (η ≤ c ∨ c + 3 * P ≤ η) → F η = 0) :
    ∫ η, F η = ∫ ξ in (0 : ℝ)..P, (F (ξ + c) + F (ξ + c + P) + F (ξ + c + 2 * P)) := by
  have hI : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b =>
    hF.intervalIntegrable a b
  have h1 : ∫ η, F η = ∫ η in c..c + 3 * P, F η := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun η hη => ?_).symm
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hη
    rcases hη with h | h
    · exact hsupp η (Or.inl h)
    · exact hsupp η (Or.inr h.le)
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (hI c (c + P)) (hI (c + P) (c + 3 * P)),
    ← intervalIntegral.integral_add_adjacent_intervals (hI (c + P) (c + 2 * P))
      (hI (c + 2 * P) (c + 3 * P))]
  have s0 : ∫ η in c..c + P, F η = ∫ ξ in (0 : ℝ)..P, F (ξ + c) := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm P c]
  have s1 : ∫ η in c + P..c + 2 * P, F η = ∫ ξ in (0 : ℝ)..P, F (ξ + c + P) := by
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := P) F (c + P)
    simp only [add_assoc] at this ⊢
    rw [this]; congr 1 <;> ring
  have s2 : ∫ η in c + 2 * P..c + 3 * P, F η = ∫ ξ in (0 : ℝ)..P, F (ξ + c + 2 * P) := by
    have := intervalIntegral.integral_comp_add_right (a := 0) (b := P) F (c + 2 * P)
    simp only [add_assoc] at this ⊢
    rw [this]; congr 1 <;> ring
  have c0 : Continuous fun ξ => F (ξ + c) := hF.comp (continuous_id.add continuous_const)
  have c1 : Continuous fun ξ => F (ξ + c + P) :=
    hF.comp ((continuous_id.add continuous_const).add continuous_const)
  have c2 : Continuous fun ξ => F (ξ + c + 2 * P) :=
    hF.comp ((continuous_id.add continuous_const).add continuous_const)
  have hsplit : ∫ ξ in (0 : ℝ)..P, (F (ξ + c) + F (ξ + c + P) + F (ξ + c + 2 * P)) =
      (∫ ξ in (0 : ℝ)..P, F (ξ + c)) + (∫ ξ in (0 : ℝ)..P, F (ξ + c + P)) +
        ∫ ξ in (0 : ℝ)..P, F (ξ + c + 2 * P) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
    · exact c0.intervalIntegrable _ _
    · exact c1.intervalIntegrable _ _
    · exact (c0.add c1).intervalIntegrable _ _
    · exact c2.intervalIntegrable _ _
  rw [s0, s1, s2, hsplit]
  ring

/-! ## Characters along a lattice -/

theorem spectralChar_add_left (a b z : ℝ) :
    spectralChar (a + b) z = spectralChar a z * spectralChar b z := by
  unfold spectralChar
  rw [← Complex.exp_add]
  congr 1; push_cast; ring

theorem spectralChar_int_lattice {P ℓ : ℝ} (hPl : P * ℓ = 1) (m q : ℤ) :
    spectralChar (m * P) (q * ℓ) = 1 := by
  unfold spectralChar
  have e : (((2 * π * (m * P) * (q * ℓ) : ℝ) : ℂ) * I) = ((m * q : ℤ) : ℂ) * (2 * π * I) := by
    have : (m : ℝ) * P * (q * ℓ) = (m * q : ℤ) * (P * ℓ) := by push_cast; ring
    rw [show (2 * π * (m * P) * (q * ℓ) : ℝ) = 2 * π * ((m : ℝ) * P * (q * ℓ)) by ring, this, hPl]
    push_cast; ring
  rw [e, Complex.exp_int_mul_two_pi_mul_I]

theorem integral_spectralChar_period {P ℓ : ℝ} (hPl : P * ℓ = 1) (m : ℤ) :
    ∫ ξ in (0 : ℝ)..P, spectralChar ξ (m * ℓ) = if m = 0 then (P : ℂ) else 0 := by
  split_ifs with hm
  · subst hm; simp [spectralChar]
  · have hℓ : ℓ ≠ 0 := by rintro rfl; simp at hPl
    set c : ℂ := 2 * π * (m * ℓ) * I with hc
    have hc0 : c ≠ 0 := by
      rw [hc]
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
      simp [*, Complex.I_ne_zero]
    have e : ∀ ξ : ℝ, spectralChar ξ (m * ℓ) = Complex.exp (c * ξ) := fun ξ => by
      unfold spectralChar; congr 1; rw [hc]; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc0]
    have h1 : Complex.exp (c * P) = 1 := by
      have : c * P = (m : ℂ) * (2 * π * I) := by
        rw [hc]
        have : (P : ℂ) * ℓ = 1 := by exact_mod_cast hPl
        linear_combination (2 * π * m * I) * this
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp [h1]

/-! ## Block spectra and their fibers -/

/-- The fiber phase `ψ(ξ − P)² e_β(−P) + ψ(ξ)² + ψ(ξ + P)² e_β(P)` of the period bump. -/
def fiberPhase (δ P β ξ : ℝ) : ℂ :=
  ((floquetBump δ P (ξ - P) ^ 2 : ℝ) : ℂ) * spectralChar (-P) β +
    ((floquetBump δ P ξ ^ 2 : ℝ) : ℂ) + ((floquetBump δ P (ξ + P) ^ 2 : ℝ) : ℂ) * spectralChar P β

theorem fiberPhase_zero {δ P ξ : ℝ} (hδ : 0 < δ) (hP : 2 * δ ≤ P) (h0 : 0 ≤ ξ) (h1 : ξ ≤ P) :
    fiberPhase δ P 0 ξ = 1 := by
  have h := floquetBump_fiber hδ hP h0 h1
  unfold fiberPhase
  simp only [spectralChar, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  exact_mod_cast h

/-- A weight that is `P`-periodic on the overlap can be moved along a fiber. -/
theorem floquetBump_sq_mul_shift {δ P ξ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ ξ)
    (h1 : ξ ≤ P) {w : ℝ → ℝ} (hper : ∀ t ∈ Icc (-δ) δ, w (t + P) = w t) :
    floquetBump δ P (ξ - P) ^ 2 * w (ξ - P) = floquetBump δ P (ξ - P) ^ 2 * w ξ ∧
      floquetBump δ P (ξ + P) ^ 2 * w (ξ + P) = floquetBump δ P (ξ + P) ^ 2 * w ξ := by
  constructor
  · rcases le_or_gt (ξ - P) (-δ) with h | h
    · rw [floquetBump_eq_zero_of_le hδ h]; ring
    · have := hper (ξ - P) ⟨h.le, by linarith⟩
      rw [sub_add_cancel] at this
      rw [this]
  · rcases le_or_gt (P + δ) (ξ + P) with h | h
    · rw [floquetBump_eq_zero_of_ge hδ h]; ring
    · rw [hper ξ ⟨by linarith, by linarith⟩]

/-- **Fiber identity for one block.** The block `ψ(η − kP)² w(η − kP)` has transform at the lattice
point `β + qℓ` equal to one period of `w · e_{β+qℓ} · e_β(kP) · fiberPhase`. -/
theorem integral_blockSq_spectralChar {δ P ℓ : ℝ} (hδ : 0 < δ) (hP : 2 * δ ≤ P)
    (hPl : P * ℓ = 1) {w : ℝ → ℝ} (hw : Continuous w) (hper : ∀ t ∈ Icc (-δ) δ, w (t + P) = w t)
    (k q : ℤ) (β : ℝ) :
    ∫ η, ((floquetBump δ P (η - k * P) ^ 2 * w (η - k * P) : ℝ) : ℂ) *
        spectralChar η (β + q * ℓ) =
      ∫ ξ in (0 : ℝ)..P, (w ξ : ℂ) * spectralChar ξ (β + q * ℓ) * spectralChar (k * P) β *
        fiberPhase δ P β ξ := by
  have hP0 : 0 < P := by linarith
  set y := β + q * ℓ with hy
  set F : ℝ → ℂ := fun η => ((floquetBump δ P (η - k * P) ^ 2 * w (η - k * P) : ℝ) : ℂ) *
    spectralChar η y with hF
  have hψ := contDiff_floquetBump δ P
  have hFc : Continuous F := by
    refine (Complex.continuous_ofReal.comp (((hψ.continuous.comp
      (continuous_id.sub continuous_const)).pow 2).mul (hw.comp
        (continuous_id.sub continuous_const)))).mul ?_
    exact continuous_spectralChar.comp (continuous_id.prodMk continuous_const)
  have hsupp : ∀ η, (η ≤ (k - 1) * P ∨ (k - 1) * P + 3 * P ≤ η) → F η = 0 := by
    intro η hη
    simp only [hF]
    rcases hη with h | h
    · rw [floquetBump_eq_zero_of_le hδ (by nlinarith : η - k * P ≤ -δ)]; simp
    · rw [floquetBump_eq_zero_of_ge hδ (by nlinarith : P + δ ≤ η - k * P)]; simp
  rw [integral_eq_intervalIntegral_three_periods hFc hP0 hsupp]
  refine intervalIntegral.integral_congr fun ξ hξ => ?_
  rw [Set.uIcc_of_le hP0.le] at hξ
  obtain ⟨h0, h1⟩ := hξ
  obtain ⟨e1, e2⟩ := floquetBump_sq_mul_shift hδ h0 h1 hper
  have a0 : ξ + (k - 1) * P - k * P = ξ - P := by ring
  have a1 : ξ + (k - 1) * P + P - k * P = ξ := by ring
  have a2 : ξ + (k - 1) * P + 2 * P - k * P = ξ + P := by ring
  simp only [hF, a0, a1, a2]
  rw [e1, e2]
  -- phases along the fiber
  have ph : ∀ m : ℤ, spectralChar (ξ + m * P) y = spectralChar ξ y * spectralChar (m * P) β := by
    intro m
    rw [spectralChar_add_left, hy, spectralChar_add ((m : ℝ) * P) β ((q : ℝ) * ℓ),
      spectralChar_int_lattice hPl, mul_one]
  have p0 : ξ + (k - 1) * P = ξ + ((k - 1 : ℤ) : ℝ) * P := by push_cast; ring
  have p1 : ξ + (k - 1) * P + P = ξ + (k : ℝ) * P := by ring
  have p2 : ξ + (k - 1) * P + 2 * P = ξ + ((k + 1 : ℤ) : ℝ) * P := by push_cast; ring
  rw [p1, p2, p0, ph, ph, ph]
  have q0 : spectralChar (((k - 1 : ℤ) : ℝ) * P) β = spectralChar (k * P) β * spectralChar (-P) β := by
    rw [← spectralChar_add_left]; congr 1; push_cast; ring
  have q2 : spectralChar (((k + 1 : ℤ) : ℝ) * P) β = spectralChar (k * P) β * spectralChar P β := by
    rw [← spectralChar_add_left]; congr 1; push_cast; ring
  rw [q0, q2]
  unfold fiberPhase
  push_cast
  ring

/-! ## Three-point barycentric weights -/

/-- The planar cross product `a × b = Im(ā b)`. -/
def planarCross (a b : ℂ) : ℝ := (conj a * b).im

theorem planarCross_eq (a b : ℂ) : planarCross a b = a.re * b.im - a.im * b.re := by
  simp [planarCross]; ring

theorem abs_planarCross_le (a b : ℂ) : |planarCross a b| ≤ ‖a‖ * ‖b‖ := by
  unfold planarCross
  calc |(conj a * b).im| ≤ ‖conj a * b‖ := Complex.abs_im_le_norm _
    _ = ‖a‖ * ‖b‖ := by rw [norm_mul, Complex.norm_conj]

/-- The unnormalized barycentric weight of the vertex opposite the edge `(z₂, z₃)`, for the
point `x` with total mass `u`. -/
def baryWeight (z₂ z₃ : ℂ) (u : ℝ) (x : ℂ) : ℝ := u * planarCross z₂ z₃ + planarCross x (z₂ - z₃)

theorem baryWeight_sum (z₁ z₂ z₃ : ℂ) (u : ℝ) (x : ℂ) :
    baryWeight z₂ z₃ u x + baryWeight z₃ z₁ u x + baryWeight z₁ z₂ u x =
      u * (planarCross z₂ z₃ + planarCross z₃ z₁ + planarCross z₁ z₂) := by
  simp only [baryWeight, planarCross_eq, Complex.sub_re, Complex.sub_im]; ring

theorem baryWeight_moment (z₁ z₂ z₃ : ℂ) (u : ℝ) (x : ℂ) :
    (baryWeight z₂ z₃ u x : ℂ) * z₁ + (baryWeight z₃ z₁ u x : ℂ) * z₂ +
      (baryWeight z₁ z₂ u x : ℂ) * z₃ =
      ((planarCross z₂ z₃ + planarCross z₃ z₁ + planarCross z₁ z₂ : ℝ) : ℂ) * x := by
  apply Complex.ext <;>
    simp only [baryWeight, planarCross_eq, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im] <;>
    ring

theorem baryWeight_ge (z₂ z₃ : ℂ) (u : ℝ) (x : ℂ) :
    u * planarCross z₂ z₃ - ‖x‖ * ‖z₂ - z₃‖ ≤ baryWeight z₂ z₃ u x := by
  unfold baryWeight
  have := abs_planarCross_le x (z₂ - z₃)
  linarith [neg_abs_le (planarCross x (z₂ - z₃))]

/-! ## The fiber phase -/

/-- Along the fiber, the squares of the three shifted bumps either sum to `1` without the left one
or sum to `1` without the right one. -/
theorem floquetBump_fiber_cases {δ P ξ : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P) (h0 : -(2 * δ) ≤ ξ)
    (h1 : ξ ≤ P + 2 * δ) :
    (floquetBump δ P (ξ - P) = 0 ∧ floquetBump δ P ξ ^ 2 + floquetBump δ P (ξ + P) ^ 2 = 1) ∨
      (floquetBump δ P (ξ + P) = 0 ∧ floquetBump δ P (ξ - P) ^ 2 + floquetBump δ P ξ ^ 2 = 1) := by
  rcases le_or_gt ξ δ with ha | ha
  · left
    refine ⟨floquetBump_eq_zero_of_le hδ (by linarith), ?_⟩
    rcases le_or_gt (-δ) ξ with hb | hb
    · exact floquetBump_sq_add_sq hδ (by linarith) hb ha
    · rw [floquetBump_eq_zero_of_le hδ hb.le, floquetBump_eq_one hδ (by linarith) (by linarith)]
      norm_num
  · right
    refine ⟨floquetBump_eq_zero_of_ge hδ (by linarith), ?_⟩
    rcases le_or_gt ξ (P + δ) with hb | hb
    · rcases le_or_gt ξ (P - δ) with hc | hc
      · rw [floquetBump_eq_zero_of_le hδ (by linarith : ξ - P ≤ -δ), floquetBump_eq_one hδ ha.le hc]
        norm_num
      · have := floquetBump_sq_add_sq (P := P) hδ (by linarith) (by linarith : -δ ≤ ξ - P)
          (by linarith : ξ - P ≤ δ)
        rwa [sub_add_cancel] at this
    · rw [floquetBump_eq_zero_of_ge hδ hb.le, floquetBump_eq_one hδ (by linarith) (by linarith)]
      norm_num

/-- `|a + b ω|² ≥ 1/2` for `a + b = 1`, `a, b ≥ 0`, `|ω| = 1`, `Re ω ≥ 0`. -/
theorem normSq_convex_ge_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {ω : ℂ}
    (hω : ‖ω‖ = 1) (hre : 0 ≤ ω.re) : 1 / 2 ≤ Complex.normSq ((a : ℂ) + (b : ℂ) * ω) := by
  have hω2 : ω.re ^ 2 + ω.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq ω
    rw [hω, Complex.normSq_apply] at this
    nlinarith
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, zero_mul, sub_zero, add_zero, zero_add]
  have : (a + b * ω.re) * (a + b * ω.re) + b * ω.im * (b * ω.im) =
      a ^ 2 + b ^ 2 * (ω.re ^ 2 + ω.im ^ 2) + 2 * a * b * ω.re := by ring
  rw [this, hω2]
  nlinarith [mul_nonneg (mul_nonneg ha hb) hre, sq_nonneg (a - b)]

/-- **Lower bound for the fiber phase** on a neighborhood of a period. -/
theorem normSq_fiberPhase_ge {δ P β ξ : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hre : 0 ≤ (spectralChar P β).re) (h0 : -(2 * δ) ≤ ξ) (h1 : ξ ≤ P + 2 * δ) :
    1 / 2 ≤ Complex.normSq (fiberPhase δ P β ξ) := by
  rcases floquetBump_fiber_cases hδ hP h0 h1 with ⟨hz, hs⟩ | ⟨hz, hs⟩
  · have e : fiberPhase δ P β ξ = ((floquetBump δ P ξ ^ 2 : ℝ) : ℂ) +
        ((floquetBump δ P (ξ + P) ^ 2 : ℝ) : ℂ) * spectralChar P β := by
      unfold fiberPhase; rw [hz]; push_cast; ring
    rw [e]
    exact normSq_convex_ge_half (sq_nonneg _) (sq_nonneg _) hs (norm_spectralChar _ _) hre
  · have e : fiberPhase δ P β ξ = spectralChar (-P) β * (((floquetBump δ P (ξ - P) ^ 2 : ℝ) : ℂ) +
        ((floquetBump δ P ξ ^ 2 : ℝ) : ℂ) * spectralChar P β) := by
      unfold fiberPhase; rw [hz]
      have hm : spectralChar (-P) β * spectralChar P β = 1 := by
        rw [← spectralChar_add_left, neg_add_cancel]; simp [spectralChar]
      push_cast
      linear_combination ((floquetBump δ P ξ : ℂ) ^ 2) * hm.symm
    rw [e, Complex.normSq_mul]
    have h1' : Complex.normSq (spectralChar (-P) β) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_spectralChar]; norm_num
    rw [h1', one_mul]
    exact normSq_convex_ge_half (sq_nonneg _) (sq_nonneg _) hs (norm_spectralChar _ _) hre

/-- On the overlap, the fiber phase is quasi-periodic. -/
theorem fiberPhase_add_period {δ P β t : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P) (h0 : -δ ≤ t)
    (h1 : t ≤ δ) : fiberPhase δ P β (t + P) = spectralChar (-P) β * fiberPhase δ P β t := by
  unfold fiberPhase
  rw [floquetBump_eq_zero_of_ge hδ (by linarith : P + δ ≤ t + P + P),
    floquetBump_eq_zero_of_le hδ (by linarith : t - P ≤ -δ), add_sub_cancel_right]
  have hm : spectralChar (-P) β * spectralChar P β = 1 := by
    rw [← spectralChar_add_left, neg_add_cancel]; simp [spectralChar]
  push_cast
  linear_combination ((floquetBump δ P (t + P) : ℂ) ^ 2) * hm.symm

theorem contDiff_fiberPhase (δ P β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fiberPhase δ P β) := by
  have hψ := contDiff_floquetBump δ P
  unfold fiberPhase
  refine ((Complex.ofRealCLM.contDiff.comp ((hψ.comp (contDiff_id.sub contDiff_const)).pow 2)).mul
    contDiff_const).add (Complex.ofRealCLM.contDiff.comp (hψ.pow 2)) |>.add ?_
  exact (Complex.ofRealCLM.contDiff.comp ((hψ.comp (contDiff_id.add contDiff_const)).pow 2)).mul
    contDiff_const

/-! ## Three Floquet blocks -/

/-- The block offsets `−2, 0, 1`. -/
def floquetIndex : Fin 3 → ℤ := ![-2, 0, 1]

/-- The vertex `e_α(kP)` of block `k`. -/
def floquetVertex (P α : ℝ) (k : ℤ) : ℂ := spectralChar (k * P) α

/-- Twice the signed area of the vertex triangle. -/
def floquetArea (P α : ℝ) : ℝ :=
  planarCross (floquetVertex P α 0) (floquetVertex P α 1) +
    planarCross (floquetVertex P α 1) (floquetVertex P α (-2)) +
      planarCross (floquetVertex P α (-2)) (floquetVertex P α 0)

/-- The normalized barycentric weight of block `i` for total mass `u` and moment `x`. -/
def floquetWeight (P α : ℝ) (u : ℝ) (x : ℂ) (i : Fin 3) : ℝ :=
  (![baryWeight (floquetVertex P α 0) (floquetVertex P α 1) u x,
    baryWeight (floquetVertex P α 1) (floquetVertex P α (-2)) u x,
    baryWeight (floquetVertex P α (-2)) (floquetVertex P α 0) u x] i) / floquetArea P α

theorem sum_floquetWeight {P α : ℝ} (hA : floquetArea P α ≠ 0) (u : ℝ) (x : ℂ) :
    ∑ i, floquetWeight P α u x i = u := by
  simp only [Fin.sum_univ_three, floquetWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [← add_div, ← add_div, baryWeight_sum (floquetVertex P α (-2)) (floquetVertex P α 0)
    (floquetVertex P α 1)]
  exact mul_div_cancel_right₀ u hA

theorem sum_floquetWeight_mul_vertex {P α : ℝ} (hA : floquetArea P α ≠ 0) (u : ℝ) (x : ℂ) :
    ∑ i, (floquetWeight P α u x i : ℂ) * floquetVertex P α (floquetIndex i) = x := by
  simp only [Fin.sum_univ_three, floquetWeight, floquetIndex, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h := baryWeight_moment (floquetVertex P α (-2)) (floquetVertex P α 0)
    (floquetVertex P α 1) u x
  have hA' : ((floquetArea P α : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA
  unfold floquetArea at hA' ⊢
  push_cast at h hA' ⊢
  field_simp
  linear_combination h

theorem floquetWeight_ge {P α : ℝ} (hA : 0 < floquetArea P α) (u : ℝ) (x : ℂ) (i : Fin 3)
    {c : ℝ} (hc : ∀ j : Fin 3, c ≤ ![planarCross (floquetVertex P α 0) (floquetVertex P α 1),
      planarCross (floquetVertex P α 1) (floquetVertex P α (-2)),
      planarCross (floquetVertex P α (-2)) (floquetVertex P α 0)] j) (hu : 0 ≤ u) :
    (u * c - 2 * ‖x‖) / floquetArea P α ≤ floquetWeight P α u x i := by
  have hv : ∀ a b : ℤ, ‖floquetVertex P α a - floquetVertex P α b‖ ≤ 2 := fun a b => by
    calc ‖floquetVertex P α a - floquetVertex P α b‖ ≤ ‖floquetVertex P α a‖ +
          ‖floquetVertex P α b‖ := norm_sub_le _ _
      _ = 2 := by unfold floquetVertex; rw [norm_spectralChar, norm_spectralChar]; norm_num
  unfold floquetWeight
  refine div_le_div_of_nonneg_right ?_ hA.le
  have hx := norm_nonneg x
  have hc0 := hc 0
  have hc1 := hc 1
  have hc2 := hc 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hc0 hc1 hc2
  fin_cases i
  · have h2 := baryWeight_ge (floquetVertex P α 0) (floquetVertex P α 1) u x
    have h3 := hv 0 1
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    nlinarith [mul_le_mul_of_nonneg_left hc0 hu, mul_le_mul_of_nonneg_left h3 hx]
  · have h2 := baryWeight_ge (floquetVertex P α 1) (floquetVertex P α (-2)) u x
    have h3 := hv 1 (-2)
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    nlinarith [mul_le_mul_of_nonneg_left hc1 hu, mul_le_mul_of_nonneg_left h3 hx]
  · have h2 := baryWeight_ge (floquetVertex P α (-2)) (floquetVertex P α 0) u x
    have h3 := hv (-2) 0
    simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    nlinarith [mul_le_mul_of_nonneg_left hc2 hu, mul_le_mul_of_nonneg_left h3 hx]

theorem contDiffAt_planarCross_left {x : ℝ → ℂ} {t : ℝ} (hx : ContDiffAt ℝ (⊤ : ℕ∞) x t) (d : ℂ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s => planarCross (x s) d) t := by
  simp only [planarCross_eq]
  exact ((Complex.reCLM.contDiff.contDiffAt.comp t hx).mul contDiffAt_const).sub
    ((Complex.imCLM.contDiff.contDiffAt.comp t hx).mul contDiffAt_const)

theorem continuous_planarCross_left {x : ℝ → ℂ} (hx : Continuous x) (d : ℂ) :
    Continuous (fun s => planarCross (x s) d) := by
  simp only [planarCross_eq]
  exact ((Complex.continuous_re.comp hx).mul continuous_const).sub
    ((Complex.continuous_im.comp hx).mul continuous_const)

theorem contDiffAt_floquetWeight {P α : ℝ} {u : ℝ → ℝ} {x : ℝ → ℂ} {t : ℝ}
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u t) (hx : ContDiffAt ℝ (⊤ : ℕ∞) x t) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s => floquetWeight P α (u s) (x s) i) t := by
  unfold floquetWeight baryWeight
  refine ContDiffAt.div_const ?_ _
  fin_cases i <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
  exact (hu.mul contDiffAt_const).add (contDiffAt_planarCross_left hx _)

theorem continuous_floquetWeight {P α : ℝ} {u : ℝ → ℝ} {x : ℝ → ℂ} (hu : Continuous u)
    (hx : Continuous x) (i : Fin 3) : Continuous (fun s => floquetWeight P α (u s) (x s) i) := by
  unfold floquetWeight baryWeight
  refine Continuous.div_const ?_ _
  fin_cases i <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
  exact (hu.mul continuous_const).add (continuous_planarCross_left hx _)

/-- The profile of block `i`: `ψ(η − kP) √(w_i(η − kP))` with `k = floquetIndex i`. -/
def floquetProfile (δ P α : ℝ) (u : ℝ → ℝ) (x : ℝ → ℂ) (i : Fin 3) (η : ℝ) : ℝ :=
  floquetBump δ P (η - floquetIndex i * P) *
    Real.sqrt (floquetWeight P α (u (η - floquetIndex i * P)) (x (η - floquetIndex i * P)) i)

theorem floquetProfile_sq {δ P α : ℝ} {u : ℝ → ℝ} {x : ℝ → ℂ}
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) (i : Fin 3) (η : ℝ) :
    floquetProfile δ P α u x i η ^ 2 = floquetBump δ P (η - floquetIndex i * P) ^ 2 *
      floquetWeight P α (u (η - floquetIndex i * P)) (x (η - floquetIndex i * P)) i := by
  unfold floquetProfile
  rw [mul_pow, Real.sq_sqrt (hpos _ _).le]

theorem floquetProfile_eq_zero {δ P α : ℝ} (hδ : 0 < δ) {u : ℝ → ℝ} {x : ℝ → ℂ} (i : Fin 3)
    {η : ℝ} (h : η - floquetIndex i * P ≤ -δ ∨ P + δ ≤ η - floquetIndex i * P) :
    floquetProfile δ P α u x i η = 0 := by
  unfold floquetProfile
  rcases h with h | h
  · rw [floquetBump_eq_zero_of_le hδ h, zero_mul]
  · rw [floquetBump_eq_zero_of_ge hδ h, zero_mul]

theorem floquetProfile_window {δ P α : ℝ} (hδ : 0 < δ) (hP : 0 < P) {u : ℝ → ℝ} {x : ℝ → ℂ}
    (i : Fin 3) {η : ℝ} (hη : 2 * P + δ ≤ |η|) : floquetProfile δ P α u x i η = 0 := by
  refine floquetProfile_eq_zero hδ i ?_
  rw [le_abs] at hη
  fin_cases i <;> simp only [floquetIndex, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] <;> push_cast <;> rcases hη with h | h
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith
  · left; linarith

theorem contDiff_floquetProfile {δ P α : ℝ} (hδ : 0 < δ) {u : ℝ → ℝ} {x : ℝ → ℂ}
    (hsm : ∀ t ∈ Ioo (-(2 * δ)) (P + 2 * δ), ContDiffAt ℝ (⊤ : ℕ∞) u t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (floquetProfile δ P α u x i) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  set k : ℝ := (floquetIndex i : ℝ)
  have hshift : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => s - k * P := contDiff_id.sub contDiff_const
  by_cases ht : η - k * P ∈ Ioo (-(2 * δ)) (P + 2 * δ)
  · obtain ⟨hu, hx⟩ := hsm _ ht
    have hw := contDiffAt_floquetWeight (P := P) (α := α) hu hx i
    have hw' : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun s => floquetWeight P α (u (s - k * P)) (x (s - k * P)) i) η :=
      ContDiffAt.comp (g := fun s => floquetWeight P α (u s) (x s) i) (f := fun s => s - k * P) η
        hw hshift.contDiffAt
    exact ((contDiff_floquetBump δ P).comp hshift).contDiffAt.mul
      (hw'.sqrt (hpos i _).ne')
  · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht
    rcases ht with h | h
    · have hev : ∀ᶠ s in 𝓝 η, s - k * P < -δ :=
        ((continuous_sub_right (k * P)).tendsto η).eventually
          (Iio_mem_nhds (by linarith : η - k * P < -δ))
      filter_upwards [hev] with s hs
      exact floquetProfile_eq_zero hδ i (Or.inl hs.le)
    · have hev : ∀ᶠ s in 𝓝 η, P + δ < s - k * P :=
        ((continuous_sub_right (k * P)).tendsto η).eventually
          (Ioi_mem_nhds (by linarith : P + δ < η - k * P))
      filter_upwards [hev] with s hs
      exact floquetProfile_eq_zero hδ i (Or.inr hs.le)

/-- The transform of the three blocks at lag `y`. -/
def floquetTransform (δ P α : ℝ) (u : ℝ → ℝ) (x : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑ i, ∫ η, ((floquetProfile δ P α u x i η ^ 2 : ℝ) : ℂ) * spectralChar η y

theorem floquetTransform_neg (δ P α : ℝ) (u : ℝ → ℝ) (x : ℝ → ℂ) (y : ℝ) :
    floquetTransform δ P α u x (-y) = conj (floquetTransform δ P α u x y) := by
  unfold floquetTransform
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [map_mul, Complex.conj_ofReal, conj_spectralChar]

/-- **Fiber formula for the three blocks** at the lattice points `β + qℓ`. -/
theorem floquetTransform_lattice {δ P ℓ α : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P) (hPl : P * ℓ = 1)
    {u : ℝ → ℝ} {x : ℝ → ℂ} (hu : Continuous u) (hx : Continuous x)
    (hper : ∀ t ∈ Icc (-δ) δ, u (t + P) = u t ∧ x (t + P) = x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) (β : ℝ) (q : ℤ) :
    floquetTransform δ P α u x (β + q * ℓ) =
      ∫ ξ in (0 : ℝ)..P, (∑ i, (floquetWeight P α (u ξ) (x ξ) i : ℂ) *
        spectralChar (floquetIndex i * P) β) * spectralChar ξ (β + q * ℓ) *
          fiberPhase δ P β ξ := by
  unfold floquetTransform
  have hblock : ∀ i, ∫ η, ((floquetProfile δ P α u x i η ^ 2 : ℝ) : ℂ) *
      spectralChar η (β + q * ℓ) =
      ∫ ξ in (0 : ℝ)..P, (floquetWeight P α (u ξ) (x ξ) i : ℂ) * spectralChar ξ (β + q * ℓ) *
        spectralChar (floquetIndex i * P) β * fiberPhase δ P β ξ := by
    intro i
    simp_rw [floquetProfile_sq hpos]
    have hwper : ∀ t ∈ Icc (-δ) δ, (fun s => floquetWeight P α (u s) (x s) i) (t + P) =
        (fun s => floquetWeight P α (u s) (x s) i) t := fun t ht => by
      simp only [(hper t ht).1, (hper t ht).2]
    exact integral_blockSq_spectralChar hδ (by linarith) hPl
      (w := fun s => floquetWeight P α (u s) (x s) i) (continuous_floquetWeight hu hx i) hwper
      (floquetIndex i) q β
  simp_rw [hblock]
  have hcI : ∀ i, Continuous fun ξ => (floquetWeight P α (u ξ) (x ξ) i : ℂ) *
      spectralChar ξ (β + q * ℓ) * spectralChar (floquetIndex i * P) β * fiberPhase δ P β ξ := by
    intro i
    exact (((Complex.continuous_ofReal.comp (continuous_floquetWeight hu hx i)).mul
      (continuous_spectralChar.comp (continuous_id.prodMk continuous_const))).mul
        continuous_const).mul (contDiff_fiberPhase δ P β).continuous
  rw [← intervalIntegral.integral_finsetSum fun i _ => (hcI i).intervalIntegrable _ _]
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem floquetTransform_lattice_zero {δ P ℓ α : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0) {u : ℝ → ℝ} {x : ℝ → ℂ} (hu : Continuous u)
    (hx : Continuous x) (hper : ∀ t ∈ Icc (-δ) δ, u (t + P) = u t ∧ x (t + P) = x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) (q : ℤ) :
    floquetTransform δ P α u x (q * ℓ) = ∫ ξ in (0 : ℝ)..P, (u ξ : ℂ) * spectralChar ξ (q * ℓ) := by
  have h := floquetTransform_lattice (α := α) hδ hP hPl hu hx hper hpos 0 q
  rw [zero_add] at h
  rw [h]
  have hP0 : 0 ≤ P := by linarith
  refine intervalIntegral.integral_congr fun ξ hξ => ?_
  rw [Set.uIcc_of_le hP0] at hξ
  have h1 : ∀ i : Fin 3, spectralChar (floquetIndex i * P) 0 = 1 := fun i => by
    simp [spectralChar]
  simp only [h1, mul_one, fiberPhase_zero hδ (by linarith) hξ.1 hξ.2]
  have hs := sum_floquetWeight hA (u ξ) (x ξ)
  rw [← Complex.ofReal_sum, hs]

theorem floquetTransform_lattice_alpha {δ P ℓ α : ℝ} (hδ : 0 < δ) (hP : 4 * δ ≤ P)
    (hPl : P * ℓ = 1) (hA : floquetArea P α ≠ 0) {u : ℝ → ℝ} {x : ℝ → ℂ} (hu : Continuous u)
    (hx : Continuous x) (hper : ∀ t ∈ Icc (-δ) δ, u (t + P) = u t ∧ x (t + P) = x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) (q : ℤ) :
    floquetTransform δ P α u x (α + q * ℓ) =
      ∫ ξ in (0 : ℝ)..P, x ξ * spectralChar ξ (α + q * ℓ) * fiberPhase δ P α ξ := by
  rw [floquetTransform_lattice hδ hP hPl hu hx hper hpos α q]
  refine intervalIntegral.integral_congr fun ξ _ => ?_
  have hs := sum_floquetWeight_mul_vertex hA (u ξ) (x ξ)
  unfold floquetVertex at hs
  show (∑ i, (floquetWeight P α (u ξ) (x ξ) i : ℂ) * spectralChar (floquetIndex i * P) α) *
    spectralChar ξ (α + q * ℓ) * fiberPhase δ P α ξ = x ξ * spectralChar ξ (α + q * ℓ) *
      fiberPhase δ P α ξ
  rw [hs]

/-- **Positivity of the three-block pairing.** -/
theorem floquet_pairing_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hAbox : ∀ n, |normDeficit lam n| ≤ A * (1 + |Real.log n|)) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {δ P α : ℝ} (hδ : 0 < δ) (hP : 0 < P) (hwin : 2 * P + δ < 1633 / 1000)
    {u : ℝ → ℝ} {x : ℝ → ℂ}
    (hsm : ∀ t ∈ Ioo (-(2 * δ)) (P + 2 * δ), ContDiffAt ℝ (⊤ : ℕ∞) u t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) x t)
    (hpos : ∀ i t, 0 < floquetWeight P α (u t) (x t) i) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (floquetTransform δ P α u x (Real.log n) + floquetTransform δ P α u x (-Real.log n))).re := by
  have h := spectralWindowTests_pairing_nonneg hW hAbox hZ Finset.univ (floquetProfile δ P α u x)
    (contDiff_floquetProfile hδ hsm hpos) hwin (fun i ξ hξ => floquetProfile_window hδ hP i hξ)
  simpa only [riemannPairForm_spectralWindowTest, Finset.sum_add_distrib, floquetTransform] using h


end

end RHTower
