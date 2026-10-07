import GaloisForLFunctions.RHTower.CCMParityQuartetOddTest

/-!
# Parity selection of the restricted Weil ground state fails under an isolated off-line quartet

**Theorem** (`exists_aperture_ground_odd`).  Suppose the Xi zero copies with non-real spectral point
form a finite set, and some spectral point `σ = t + iδ` (`t, δ > 0`) has the largest imaginary part
among them, attained only on its quartet `{σ, σ̄, −σ, −σ̄}` (`IsolatedTopQuartet σ`).  Then for every
`A` there is an aperture `a > A` at which every ground state of the CCM restricted Weil form is
reflection-odd.  Consequently the ground level at that aperture is not simple with an even
eigenvector, which is the input that the zero-reality theorem for minimal eigenvectors of even
Toeplitz forms requires.

**Proof.**  At the phase apertures `a_k = (arg(δ + it) + 2πk)/(2t)`:

* the even floor (`sourceQuadratic_ge_of_isEven`) gives `Q ≥ c_e ‖J·‖²` on even vectors, with
  `c_e = −((M/4) D⁺ + L)`;
* the smooth odd tests `v_n` satisfy `Q(v_n) ≤ Σ_{off-line} Re(term) + K² Σ_q |z_q|^{−2}`.  The
  off-line part converges to that of the truncated model, which is at most
  `−(M/4)(D⁻² − 4I²) + L D⁻`, and `‖J v_n‖² → D⁻`;
* the phase-aperture gap (`exists_phaseAperture_gap`) makes the limit strictly below `c_e D⁻`.

So some `v_n` has Rayleigh quotient below `c_e`, the ground energy lies below the even floor, and
the even part of every ground state, itself a ground state, vanishes.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityQuartet

noncomputable section

/-! ## The off-line part of the truncated model -/

theorem norm_zeroSumTerm_gTrunc_le (t δ : ℝ) {a : ℝ} (ha : 0 ≤ a) (z : ℂ) :
    ‖zeroSumTerm (gTrunc t δ a) z‖ ≤
      oddTestMass t δ a * (2 * a * Real.exp (2 * a * |z.im|)) := by
  have h1 := norm_testTransform_gTrunc_sq_le t δ ha (-z)
  have h2 := norm_testTransform_gTrunc_sq_le t δ ha (-(starRingEnd ℂ) z)
  simp only [Complex.neg_im, Complex.conj_im, neg_neg, abs_neg] at h1 h2
  unfold zeroSumTerm
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (testTransform (gTrunc t δ a) (-z)),
    norm_nonneg (testTransform (gTrunc t δ a) (-(starRingEnd ℂ) z)),
    sq_nonneg (‖testTransform (gTrunc t δ a) (-z)‖ -
      ‖testTransform (gTrunc t δ a) (-(starRingEnd ℂ) z)‖)]

/-- The off-line part of the truncated model is at most `−(M/4)(D⁻² − 4I²) + L D⁻`. -/
theorem offLine_gTrunc_le {σ : ℂ} (h : IsolatedTopQuartet σ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ q ∈ h.offLine, (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re ≤
      -((h.topCount : ℝ) / 4 * (oddTestMass σ.re σ.im a ^ 2 - 4 * oddTestCross σ.re σ.im a ^ 2)) +
        oddTestMass σ.re σ.im a * h.lowWeight a := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not h.offLine
    (fun q => InQuartet σ (xiSpectralPoint q))]
  have hσ : (⟨σ.re, σ.im⟩ : ℂ) = σ := Complex.eta σ
  have htop : ∀ q ∈ h.topSet, (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re =
      -(oddTestMass σ.re σ.im a ^ 2 / 4 - oddTestCross σ.re σ.im a ^ 2) := by
    intro q hq
    unfold IsolatedTopQuartet.topSet at hq
    rw [Finset.mem_filter] at hq
    rw [re_zeroSumTerm_quartet (s := -1) (gTrunc_neg σ.re σ.im a) (by simp) σ hq.2, ← hσ]
    exact re_top_gTrunc σ.re σ.im ha
  have htopsum : ∑ q ∈ h.offLine with InQuartet σ (xiSpectralPoint q),
      (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re =
      (h.topCount : ℝ) * -(oddTestMass σ.re σ.im a ^ 2 / 4 - oddTestCross σ.re σ.im a ^ 2) := by
    have hset : ∑ q ∈ h.offLine with InQuartet σ (xiSpectralPoint q),
        (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re =
        ∑ q ∈ h.topSet, (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re := rfl
    rw [hset, Finset.sum_congr rfl htop, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hlowsum : ∑ q ∈ h.offLine with ¬ InQuartet σ (xiSpectralPoint q),
      (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re ≤
      oddTestMass σ.re σ.im a * h.lowWeight a := by
    have hset : ∑ q ∈ h.offLine with ¬ InQuartet σ (xiSpectralPoint q),
        (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re =
        ∑ q ∈ h.lowSet, (zeroSumTerm (gTrunc σ.re σ.im a) (xiSpectralPoint q)).re := rfl
    rw [hset, IsolatedTopQuartet.lowWeight, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _
    exact (Complex.re_le_norm _).trans (norm_zeroSumTerm_gTrunc_le _ _ ha _)
  rw [htopsum]
  linarith

/-! ## The off-line part of the smooth tests converges -/

theorem tendsto_re_zeroSumTerm_oddTestSeq (t δ : ℝ) (hδ : 0 ≤ δ) (a : SuzukiPositiveAperture)
    (z : ℂ) :
    Tendsto (fun n => (zeroSumTerm (oddTestSeq t δ a n) z).re) atTop
      (𝓝 (zeroSumTerm (gTrunc t δ a.1) z).re) := by
  unfold zeroSumTerm
  exact Complex.continuous_re.continuousAt.tendsto.comp
    ((tendsto_testTransform_oddTestSeq t δ hδ a (-z)).mul
      ((Complex.continuous_conj.tendsto _).comp
        (tendsto_testTransform_oddTestSeq t δ hδ a (-(starRingEnd ℂ) z))))

/-- **An odd test below a given level.**  If the limiting upper bound is strictly below
`c · D⁻(a)`, some smooth test has Rayleigh quotient below `c`. -/
theorem exists_smooth_below {σ : ℂ} (h : IsolatedTopQuartet σ) (a : SuzukiPositiveAperture)
    {c : ℝ}
    (hlt : -((h.topCount : ℝ) / 4 *
          (oddTestMass σ.re σ.im a.1 ^ 2 - 4 * oddTestCross σ.re σ.im a.1 ^ 2)) +
        oddTestMass σ.re σ.im a.1 * h.lowWeight a.1 +
        (4 * (a.1 * (σ.re + σ.im) + 1) * Real.cosh (σ.im * a.1)) ^ 2 *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) <
      c * oddTestMass σ.re σ.im a.1) :
    ∃ v : CCMComplexSmoothInteriorSource a,
      ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector <
        c * ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
  set t := σ.re
  set δ := σ.im
  have ht : 0 ≤ t := h.re_pos.le
  have hδ : 0 ≤ δ := h.im_pos.le
  set K : ℝ := 4 * (a.1 * (t + δ) + 1) * Real.cosh (δ * a.1) with hK
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set X : ℝ := ∑ q ∈ h.offLine, (zeroSumTerm (gTrunc t δ a.1) (xiSpectralPoint q)).re with hX
  have hXle := offLine_gTrunc_le h a.2.le
  -- the upper bound for each smooth test
  have hbound : ∀ n, ccmRestrictedWeilSourceQuadratic a (oddTestSeq t δ a n).toCCMFormVector ≤
      ∑ q ∈ h.offLine, (zeroSumTerm (oddTestSeq t δ a n) (xiSpectralPoint q)).re + K ^ 2 * S := by
    intro n
    refine (sourceQuadratic_le_offLine_add h (oddTestSeq t δ a n)).trans ?_
    have hK1 : (∫ x, ‖deriv (oddTestSeq t δ a n : ℝ → ℂ) x‖) ≤ K :=
      integral_norm_deriv_oddTestSource_le ht hδ a _ _
    have hK0 : 0 ≤ ∫ x, ‖deriv (oddTestSeq t δ a n : ℝ → ℂ) x‖ :=
      integral_nonneg fun _ => norm_nonneg _
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hK0 hK1 2) hS0
    linarith
  -- convergence of the comparison quantity
  have hconv : Tendsto (fun n =>
      (∑ q ∈ h.offLine, (zeroSumTerm (oddTestSeq t δ a n) (xiSpectralPoint q)).re + K ^ 2 * S) -
        c * ∫ x, ‖(oddTestSeq t δ a n : ℝ → ℂ) x‖ ^ 2) atTop
      (𝓝 ((X + K ^ 2 * S) - c * oddTestMass t δ a.1)) := by
    refine ((tendsto_finsetSum _ fun q _ => ?_).add_const _).sub
      ((tendsto_integral_norm_sq_oddTestSeq t δ hδ a).const_mul c)
    exact tendsto_re_zeroSumTerm_oddTestSeq t δ hδ a _
  have hneg : (X + K ^ 2 * S) - c * oddTestMass t δ a.1 < 0 := by
    have := hlt
    linarith
  obtain ⟨n, hn⟩ := (hconv.eventually (gt_mem_nhds hneg)).exists
  refine ⟨oddTestSeq t δ a n, ?_⟩
  rw [norm_sq_toAperture_toCCMFormVector]
  have := hbound n
  linarith

/-! ## The low weight and the critical-line constant -/

theorem exists_low_exponent {σ : ℂ} (h : IsolatedTopQuartet σ) :
    ∃ δ₀ : ℝ, δ₀ < σ.im ∧ ∀ q ∈ h.lowSet, |(xiSpectralPoint q).im| ≤ δ₀ := by
  by_cases hne : h.lowSet.Nonempty
  · obtain ⟨q₀, hq₀, hmax⟩ := h.lowSet.exists_max_image (fun q => |(xiSpectralPoint q).im|) hne
    exact ⟨_, h.abs_im_lt_of_mem_lowSet hq₀, hmax⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, h.im_pos, by simp [hne]⟩

theorem lowWeight_le {σ : ℂ} (h : IsolatedTopQuartet σ) {δ₀ δ' : ℝ} (hδ₀ : δ₀ < δ')
    (hlow : ∀ q ∈ h.lowSet, |(xiSpectralPoint q).im| ≤ δ₀) {A : ℝ} (hA : 0 ≤ A) :
    h.lowWeight A ≤ (h.lowSet.card / (δ' - δ₀)) * Real.exp (2 * δ' * A) := by
  have hd : 0 < δ' - δ₀ := by linarith
  have hterm : ∀ q ∈ h.lowSet, 2 * A * Real.exp (2 * A * |(xiSpectralPoint q).im|) ≤
      Real.exp (2 * δ' * A) / (δ' - δ₀) := by
    intro q hq
    rw [le_div_iff₀ hd]
    have h1 : Real.exp (2 * A * |(xiSpectralPoint q).im|) ≤ Real.exp (2 * δ₀ * A) :=
      Real.exp_le_exp.mpr (by nlinarith [hlow q hq])
    have h2 : 2 * A * (δ' - δ₀) ≤ Real.exp (2 * A * (δ' - δ₀)) := by
      have := Real.add_one_le_exp (2 * A * (δ' - δ₀))
      linarith
    have h3 : Real.exp (2 * δ₀ * A) * Real.exp (2 * A * (δ' - δ₀)) = Real.exp (2 * δ' * A) := by
      rw [← Real.exp_add]
      ring_nf
    calc 2 * A * Real.exp (2 * A * |(xiSpectralPoint q).im|) * (δ' - δ₀)
        ≤ 2 * A * Real.exp (2 * δ₀ * A) * (δ' - δ₀) := by gcongr
      _ = Real.exp (2 * δ₀ * A) * (2 * A * (δ' - δ₀)) := by ring
      _ ≤ Real.exp (2 * δ₀ * A) * Real.exp (2 * A * (δ' - δ₀)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = Real.exp (2 * δ' * A) := h3
  calc h.lowWeight A ≤ ∑ _q ∈ h.lowSet, Real.exp (2 * δ' * A) / (δ' - δ₀) :=
        Finset.sum_le_sum hterm
    _ = (h.lowSet.card / (δ' - δ₀)) * Real.exp (2 * δ' * A) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem critical_constant_le {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 ≤ δ) {A : ℝ} (hA : 0 ≤ A) {S : ℝ}
    (hS : 0 ≤ S) :
    (4 * (A * (t + δ) + 1) * Real.cosh (δ * A)) ^ 2 * S ≤
      (16 * (t + δ + 1) ^ 2 * S) * (1 + A) ^ 2 * Real.exp (2 * δ * A) := by
  have hc := cosh_le_exp_of_nonneg (mul_nonneg hδ hA)
  have hc0 := (Real.cosh_pos (δ * A)).le
  have hlin : A * (t + δ) + 1 ≤ (t + δ + 1) * (1 + A) := by nlinarith
  have hexp : Real.exp (δ * A) ^ 2 = Real.exp (2 * δ * A) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hstep : 4 * (A * (t + δ) + 1) * Real.cosh (δ * A) ≤
      4 * ((t + δ + 1) * (1 + A)) * Real.exp (δ * A) := by
    apply mul_le_mul (by linarith) hc hc0 (by positivity)
  calc (4 * (A * (t + δ) + 1) * Real.cosh (δ * A)) ^ 2 * S
      ≤ (4 * ((t + δ + 1) * (1 + A)) * Real.exp (δ * A)) ^ 2 * S := by
        gcongr
    _ = (16 * (t + δ + 1) ^ 2 * S) * (1 + A) ^ 2 * Real.exp (δ * A) ^ 2 := by ring
    _ = (16 * (t + δ + 1) ^ 2 * S) * (1 + A) ^ 2 * Real.exp (2 * δ * A) := by rw [hexp]

/-! ## The no-go theorem -/

/-- **Parity selection fails.**  Under an isolated off-line quartet, arbitrarily large apertures
have only reflection-odd ground states of the CCM restricted Weil form. -/
theorem exists_aperture_ground_odd {σ : ℂ} (h : IsolatedTopQuartet σ) (A : ℝ) :
    ∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = -u := by
  set t := σ.re with ht_def
  set δ := σ.im with hδ_def
  have ht : 0 < t := h.re_pos
  have hδ : 0 < δ := h.im_pos
  obtain ⟨δ₀, hδ₀, hlow⟩ := exists_low_exponent h
  set δ' := (δ₀ + δ) / 2 with hδ'_def
  have hδ₀' : δ₀ < δ' := by linarith
  have hδ'δ : δ' < δ := by linarith
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℝ := (h.topCount : ℝ) with hM_def
  have hM : 0 < M := by
    rw [hM_def]
    exact_mod_cast h.topCount_pos
  set C₁ : ℝ := h.lowSet.card / (δ' - δ₀) with hC₁_def
  have hC₁ : 0 ≤ C₁ := div_nonneg (Nat.cast_nonneg _) (by linarith)
  set C₂ : ℝ := 16 * (t + δ + 1) ^ 2 * S with hC₂_def
  have hC₂ : 0 ≤ C₂ := by positivity
  obtain ⟨k, hkA, hk0, hD, hgap⟩ := exists_phaseAperture_gap ht hδ hδ'δ hM hC₁ hC₂ A
  set a : SuzukiPositiveAperture := ⟨phaseAperture t δ k, hk0⟩ with ha_def
  have haval : a.1 = phaseAperture t δ k := rfl
  refine ⟨a, hkA, ?_⟩
  set D := oddTestMass t δ a.1 with hD_def
  set Dp := evenFloorMass t δ a.1 with hDp_def
  set I := oddTestCross t δ a.1 with hI_def
  set L := h.lowWeight a.1 with hL_def
  set ce : ℝ := -(M / 4 * Dp + L) with hce
  have hDpos : 0 < D := by rw [hD_def, haval]; exact hD
  have hL : L ≤ C₁ * Real.exp (2 * δ' * a.1) := lowWeight_le h hδ₀' hlow a.2.le
  have hcrit := critical_constant_le ht.le hδ.le a.2.le hS0
  -- the limiting bound is below the even floor
  have hlt : -(M / 4 * (D ^ 2 - 4 * I ^ 2)) + D * L +
      (4 * (a.1 * (t + δ) + 1) * Real.cosh (δ * a.1)) ^ 2 * S < ce * D := by
    rw [← haval] at hgap
    have hgap' : 2 * L + C₂ * (1 + a.1) ^ 2 * Real.exp (2 * δ * a.1) / D + M * I ^ 2 / D <
        M / 4 * (D - Dp) := by
      have : 2 * L ≤ 2 * C₁ * Real.exp (2 * δ' * a.1) := by linarith
      linarith
    have hmul := mul_lt_mul_of_pos_right hgap' hDpos
    have e1 : (2 * L + C₂ * (1 + a.1) ^ 2 * Real.exp (2 * δ * a.1) / D + M * I ^ 2 / D) * D =
        2 * L * D + C₂ * (1 + a.1) ^ 2 * Real.exp (2 * δ * a.1) + M * I ^ 2 := by
      field_simp
    rw [e1] at hmul
    rw [hce]
    nlinarith
  obtain ⟨v, hv⟩ := exists_smooth_below h a hlt
  -- the ground energy lies strictly below the even floor
  have hμv := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v.toCCMFormVector
  intro u hu
  obtain ⟨heven, -⟩ := ccmRestrictedWeil_ground_evenOdd_components a u hu
  set e := ccmRestrictedWeilEvenPart a u with he
  have hRe : ccmArchimedeanFormReflection a e = e := ccmArchimedeanFormReflection_evenPart a u
  have hfloor := sourceQuadratic_ge_of_isEven h e hRe
  have hvpos : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0] at hv hμv
    linarith
  have hμ : ccmRestrictedWeilGroundEnergy a < ce := by
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hvpos.le
    linarith
  have hJe : ‖ccmArchimedeanFormToAperture a e‖ ^ 2 = 0 := by
    have hfl : ce * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 ≤
        ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by
      rw [← heven]
      exact hfloor
    have hnn : 0 ≤ ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by positivity
    obtain ⟨X, hXdef⟩ : ∃ X, X = ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ccmRestrictedWeilGroundEnergy a := ⟨_, rfl⟩
    rw [← hXdef] at hfl hnn ⊢
    rw [← hμdef] at hfl hμ
    have hpos : 0 < ce - μ := sub_pos.mpr hμ
    have hprod : (ce - μ) * X ≤ 0 := by rw [sub_mul]; linarith
    by_contra hX
    have hXpos : 0 < X := lt_of_le_of_ne hnn (Ne.symm hX)
    have := mul_pos hpos hXpos
    linarith
  have he0 : e = 0 := by
    apply ccmArchimedeanFormToAperture_injective a
    rw [map_zero]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hJe)
  have hsum : u + ccmArchimedeanFormReflection a u = 0 := by
    have h2 : (2 : ℂ)⁻¹ • (u + ccmArchimedeanFormReflection a u) = 0 := he0
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero two_ne_zero)] at h2
  exact eq_neg_of_add_eq_zero_right hsum

/-- **Contrapositive form.**  If at every sufficiently large aperture some ground state of the CCM
restricted Weil form is not reflection-odd, then no isolated off-line quartet exists. -/
theorem not_isolatedTopQuartet_of_eventually_ground_not_odd
    (hground : ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A < a.1 →
      ∃ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ∧
          ccmArchimedeanFormReflection a u ≠ -u) (σ : ℂ) :
    ¬ IsolatedTopQuartet σ := by
  intro h
  obtain ⟨A, hA⟩ := hground
  obtain ⟨a, ha, hodd⟩ := exists_aperture_ground_odd h A
  obtain ⟨u, hu, hne⟩ := hA a ha
  exact hne (hodd u hu)

/-- **Even ground states exclude isolated quartets.**  If every sufficiently large aperture carries
a nonzero reflection-even ground state of the CCM restricted Weil form (the parity half of the
simple-even-ground-state condition), then the Xi zeros off the critical line are not a finite set
with a unique top quartet. -/
theorem not_isolatedTopQuartet_of_eventually_even_ground
    (hstep : ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A < a.1 →
      ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u ≠ 0 ∧
        ccmArchimedeanFormReflection a u = u ∧
        ccmRestrictedWeilSourceQuadratic a u =
          ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2) (σ : ℂ) :
    ¬ IsolatedTopQuartet σ := by
  apply not_isolatedTopQuartet_of_eventually_ground_not_odd _ σ
  obtain ⟨A, hA⟩ := hstep
  refine ⟨A, fun a ha => ?_⟩
  obtain ⟨u, hJu, hRu, hu⟩ := hA a ha
  refine ⟨u, hu, fun hodd => hJu ?_⟩
  have hu0 : u = 0 := by
    have h2 : u = -u := hRu.symm.trans hodd
    have : (2 : ℂ) • u = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel u
    rwa [smul_eq_zero, or_iff_right two_ne_zero] at this
  rw [hu0, map_zero]

end

end RHTower.CCMParityQuartet
