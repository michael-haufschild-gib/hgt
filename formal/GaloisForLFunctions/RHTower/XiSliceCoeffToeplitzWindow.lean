import GaloisForLFunctions.RHTower.XiSliceOffCentreToeplitzWindow

/-!
# Toeplitz windows of the slice coefficients at the centre

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` at `x = 0`.  The odd ones
vanish; the even ones `c_{2k}(t)` are the sequence whose `PF_∞` property at a single height is the
Riemann hypothesis (`riemannHypothesis_iff_forall_pfSeq_xiSliceCoeff_at`).

**Theorem** (`exists_xiSliceCoeff_toeplitzDet_pos_sharp_window`).  For every `r ≥ 1`, `0 < η ≤ 1/8`
and `R₁ ≥ 1` there is `t₀` such that for `t ≥ t₀` and every centre `k ≥ r − 1` with
`(¼ + 2η) log t ≤ k ≤ (R₁/4) log t`,

  `det [c_{2(k+i−j)}(t)]_{0 ≤ i, j < r} > 0`.

So above the quarter-log edge every contiguous Toeplitz minor of every fixed order of the centre
sequence is positive: the failures of `PF_∞` that RH excludes can only involve coefficients of order
below `(¼ + ε) log t`, and `r = 1` is the corpus positivity window
`exists_xiSliceCoeff_pos_sharp_window`.

**Mechanism.**  On the saddle circle of the order `2k`, the circle integrand of the order `2m` is
`g_t(R)` times `S(θ) e^{−2i(m−k)θ}` with `S` the normalised arc value; it has period `π` and is
conjugate-symmetric, so (`xiSliceCoeff_two_mul_eq_quarter_freq`)

  `c_{2m} = (2|ξ(½+R+it)|²/(πR^{2m})) ∫₀^{π/2} Re(S(θ) e^{−i(m−k)·2θ}) dθ`.

Hence `det[c_{2(k+i−j)}] = Cʳ det T` with `T_{ij} = ∫₀^{π/2} Re(S e^{−i(i−j)2θ})`, and
`xᵀTx = ∫₀^{π/2} Re S |Σ_j x_j e^{2ijθ}|²` (`toeplitz_quadForm_eq_gen`).  The core arc
`[δ₀/2, δ₀]` carries `≥ (c_r/2) δ₀^{2r−1} ‖x‖²` of `|p(2θ)|²`, the far arc is controlled by the
convexity tail `exists_sliceArc_tail_le_euler`, and the quadratic form is positive.
-/

open Complex Real Metric intervalIntegral Matrix
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **The quarter formula on the saddle circle of another order.** -/
theorem xiSliceCoeff_two_mul_eq_quarter_freq (t : ℝ) (k m : ℕ) {R : ℝ} (hR : 1 / 2 < R) :
    xiSliceCoeff t (2 * m)
      = ((2 * ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 / (Real.pi * R ^ (2 * m))
          * ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R k θ
              * Complex.exp (-((((m : ℝ) - k) * (2 * θ) : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℂ, H = fun θ => sliceArc t R k θ
      * Complex.exp (-((((m : ℝ) - k) * (2 * θ) : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hRHS : (∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R k θ
      * Complex.exp (-((((m : ℝ) - k) * (2 * θ) : ℝ) : ℂ) * I)).re)
      = ∫ θ in (0 : ℝ)..(Real.pi / 2), (H θ).re := by rw [hHdef]
  rw [hRHS, xiSliceCoeff_eq_circle t (2 * m) hR0]
  have harc : ∀ θ : ℝ, Complex.exp (-((((2 * m : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)
      * xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
      = xiSliceProduct t (R : ℂ) * H θ := by
    intro θ
    have hsplit : Complex.exp (-((((2 * m : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)
        = Complex.exp (-((((2 * k : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)
          * Complex.exp (-((((m : ℝ) - k) * (2 * θ) : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit, mul_comm (Complex.exp (-((((2 * k : ℕ) : ℝ) * θ : ℝ) : ℂ) * I)), mul_assoc,
      exp_mul_xiSliceProduct_eq_saddleArc t R θ k hR, hHdef]
    simp only [sliceArc]
    ring
  simp_rw [harc]
  have hHc : Continuous H := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    rw [hHdef]
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  have hper : ∀ θ, H (θ + Real.pi) = H θ := by
    intro θ
    rw [hHdef]
    simp only [sliceArc]
    rw [saddleArc_xiSlice_add_pi]
    congr 1
    have hk : Complex.exp ((((-((m : ℤ) - k)) : ℤ) : ℂ) * (2 * Real.pi * I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I _
    rw [show (-((((m : ℝ) - k) * (2 * (θ + Real.pi)) : ℝ) : ℂ) * I)
        = -((((m : ℝ) - k) * (2 * θ) : ℝ) : ℂ) * I
          + (((-((m : ℤ) - k)) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, hk, mul_one]
  have hconj : ∀ θ, H (-θ) = (starRingEnd ℂ) (H θ) := by
    intro θ
    rw [hHdef]
    simp only [sliceArc]
    rw [saddleArc_xiSlice_neg, map_mul]
    congr 1
    rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  rw [intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable H MeasureTheory.volume 0 (2 * Real.pi) :=
    hHc.intervalIntegrable _ _
  have hre : (∫ θ in (0 : ℝ)..(2 * Real.pi), H θ).re
      = 4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (H θ).re := by
    rw [HTGeometry.re_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (H θ).re) (σ := 1)
      (Complex.continuous_re.comp hHc) (fun θ => by simp only [hper])
      (fun θ => by simp only [hconj]; simp)]
    ring
  have him : (∫ θ in (0 : ℝ)..(2 * Real.pi), H θ).im = 0 := by
    rw [HTGeometry.im_intervalIntegral hint]
    rw [integral_zero_two_pi_of_period_pi_parity (h := fun θ => (H θ).im) (σ := -1)
      (Complex.continuous_im.comp hHc) (fun θ => by simp only [hper])
      (fun θ => by simp only [hconj]; simp)]
    ring
  have hI : (∫ θ in (0 : ℝ)..(2 * Real.pi), H θ)
      = ((4 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (H θ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [hre]; simp
    · rw [him]; simp
  rw [hI, xiSliceProduct_ofReal_eq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hRn : R ^ (2 * m) ≠ 0 := pow_ne_zero _ hR0.ne'
  push_cast
  field_simp
  ring

/-- **Positive Toeplitz determinant at the centre from saddle data.**  Under the saddle conditions
of `xiSliceCoeff_pos_of_saddle_euler` at the order `2n`, `n ≥ k − 1`, given the short-arc constants
`(c, h₀)` of order `k` and the losses
`2·10⁻³ e^{−Λ^{1/5}/8}, πE ≤ (7/160) c Λ^{−(2k−1)/2}/(2k²)`, the Toeplitz matrix
`[c_{2(n+i−j)}]_{i,j<k}` has positive determinant. -/
theorem xiSliceCoeff_toeplitzDet_pos_of_saddle_euler {η R₁ K t u R E c h₀ : ℝ} {n k : ℕ}
    (hk : 1 ≤ k) (hnk : k - 1 ≤ n)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hR₁ : 1 ≤ R₁) (hKdef : K = R₁ / (2 * η)) (ht8 : 8 ≤ t)
    (hu0 : 0 < u) (hRa : 1 / 2 + 2 * η ≤ R) (hRb : R ≤ R₁) (hRt : R ≤ t / 2)
    (hsad : (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re = 2 * (n : ℝ))
    (hF₁lo : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re)
    (hF₁hi : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * u)
    (hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u)
    (htail : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 → ‖sliceArc t R n θ‖ ≤ E)
    (hΛ1 : 1 ≤ R * u)
    (hE3 : (R * u) ^ (-(2 / 5) : ℝ) < 1 / (1000 * K))
    (hE4 : (R * u) ^ (-(1 / 5) : ℝ) < 3 / (2 * (1 + 128 * K)))
    (hc : 0 < c)
    (hshort : ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ y : Fin k → ℂ,
      c * h ^ (2 * k - 1) * ‖y‖ ^ 2
        ≤ ∫ θ in (0 : ℝ)..h, ‖GaloisForLFunctions.HTGeometry.shortArcTrigPoly y θ‖ ^ 2)
    (hΛh : (R * u) ^ (-(1 / 2) : ℝ) ≤ h₀)
    (hmidΛ : 2 * (1 / 1000 * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8))
      ≤ 7 / 160 * (c * ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * k - 1) / 2 / (k : ℝ) ^ 2))
    (htailΛ : 2 * (Real.pi / 2 * E)
      ≤ 7 / 160 * (c * ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * k - 1) / 2 / (k : ℝ) ^ 2)) :
    0 < (Matrix.of fun i j : Fin k => (xiSliceCoeff t (2 * (n + i - j))).re).det := by
  have hR₁0 : 0 < R₁ := by linarith
  have hR0 : 0 < R := by linarith
  have hRR₁ : R ≤ R₁ := hRb
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  have hKd0 : 0 ≤ xiSliceDiscConstantEuler η t R := by
    unfold xiSliceDiscConstantEuler
    have h1 : 0 ≤ Real.log (3 * t / 2) := Real.log_nonneg (by linarith)
    have h2 := xiEulerConstant_pos hη
    have h3 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    exact add_nonneg (mul_nonneg hη.le (by linarith [Real.pi_pos]))
      (mul_nonneg hR0.le (by linarith [Real.pi_pos]))
  obtain ⟨D, hDdef⟩ : ∃ D, D = xiSliceDiscConstantEuler η t R * R / (4 * η ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hDdef]; exact div_nonneg (mul_nonneg hKd0 hR0.le) (by positivity)
  have hD : D ≤ K * u := by
    rw [hDdef, div_le_iff₀ (by positivity), hKdef]
    have e : R₁ / (2 * η) * u * (4 * η ^ 2) = 2 * η * u * R₁ := by field_simp; ring
    rw [e]
    calc xiSliceDiscConstantEuler η t R * R ≤ xiSliceDiscConstantEuler η t R * R₁ :=
          mul_le_mul_of_nonneg_left hRR₁ hKd0
      _ ≤ 2 * η * u * R₁ := mul_le_mul_of_nonneg_right hKd hR₁0.le
  have hcub : ∀ θ : ℝ, 32 * xiSliceDiscConstantEuler η t R / η ^ 2 * R ^ 2 * θ ^ 3 / 3
      = 128 / 3 * (R * D) * θ ^ 3 := by
    intro θ; rw [hDdef]; field_simp; ring
  have hR₁θ : R₁ * (1 / (1000 * K)) = η / 500 := by rw [hKdef]; field_simp; ring
  have hb : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 / (1000 * K) →
      ‖sliceArc t R n θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
          * R * (1 - Real.cos θ)) + 128 / 3 * (R * D) * θ ^ 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
          + 128 / 3 * (R * D) * θ ^ 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 128 / 3 * (R * D) * θ ^ 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 128 / 3 * (R * D) * θ ^ 3)
          ≤ (sliceArc t R n θ).re) := by
    intro θ hθ0 hθ
    have hRθ : R * θ ≤ η / 2 := by
      have h1 : R * θ ≤ R₁ * θ := mul_le_mul_of_nonneg_right hRb hθ0
      have h2 : R₁ * θ ≤ R₁ * (1 / (1000 * K)) := mul_le_mul_of_nonneg_left hθ hR₁0.le
      linarith
    have h := xiSlice_saddleArc_bounds_euler hη (by linarith) ht8 hRa hRt hθ0 hRθ
    rw [hsad, hcub θ] at h
    exact h
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = R * u := ⟨_, rfl⟩
  rw [← hΛ] at hΛ1 hE3 hE4 hΛh hmidΛ htailΛ
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀, δ₀ = Λ ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = Λ ^ (-(2 / 5) : ℝ) := ⟨_, rfl⟩
  rw [← hδ₀] at hΛh hmidΛ htailΛ
  have hδ₀pos : 0 < δ₀ := hδ₀ ▸ Real.rpow_pos_of_pos hΛ0 _
  have hδ₀δ : δ₀ ≤ δ := by
    rw [hδ₀, hδ]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 (by norm_num)
  have hδθ : δ ≤ 1 / (1000 * K) := by rw [hδ]; exact hE3.le
  have hcore : Λ * δ₀ ^ 2 ≤ 1 := by rw [hδ₀]; exact (mul_rpow_neg_half_sq hΛ0).le
  have hphase : (1 + 128 * K) * Λ * δ ^ 3 ≤ 3 / 2 := by
    have := mul_rpow_neg_two_fifths_cube hΛ0
    rw [hδ, mul_assoc, this]
    have h4 := hE4.le
    rw [le_div_iff₀ (by positivity)] at h4
    linarith
  have hmidexp : Real.exp (-Λ * δ ^ 2 / 8) = Real.exp (-(Λ ^ (1 / 5 : ℝ)) / 8) := by
    congr 1
    rw [hδ, ← mul_rpow_neg_two_fifths_sq hΛ0]; ring
  have hSc : Continuous fun θ : ℝ => sliceArc t R n θ := by
    have hg := differentiable_xiSliceProduct t
    have : Continuous fun θ : ℝ => xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) :=
      hg.continuous.comp (by fun_prop)
    simp only [sliceArc, HTGeometry.saddleArc]
    fun_prop
  subst hΛ
  have hU : (1 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  -- the Toeplitz matrix of the arc
  set T : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => ∫ θ in (0 : ℝ)..(Real.pi / 2),
    (sliceArc t R n θ
      * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * (2 * θ) : ℝ) : ℂ) * I)).re with hT
  have hTpos : ∀ x : Fin k → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (T *ᵥ x) := by
    intro x hx
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set p : ℝ → ℂ := fun θ =>
      GaloisForLFunctions.HTGeometry.shortArcTrigPoly (fun j => (x j : ℂ)) (2 * θ) with hp
    have hpc : Continuous p :=
      (GaloisForLFunctions.HTGeometry.continuous_shortArcTrigPoly _).comp (by fun_prop)
    set Kx : ℝ := ((k : ℝ) * ‖x‖) ^ 2 with hKx
    have hKx0 : 0 < Kx := by rw [hKx]; positivity
    have hpbd : ∀ θ, ‖p θ‖ ^ 2 ≤ Kx := by
      intro θ
      have h1 : ‖p θ‖ ≤ (k : ℝ) * ‖x‖ := by
        simp only [hp, GaloisForLFunctions.HTGeometry.shortArcTrigPoly]
        calc ‖∑ j : Fin k, (x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * ((2 * θ : ℝ) : ℂ) * I)‖
            ≤ ∑ j : Fin k, ‖(x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * ((2 * θ : ℝ) : ℂ) * I)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ _j : Fin k, ‖x‖ := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_mul, show ((j : ℕ) : ℂ) * ((2 * θ : ℝ) : ℂ) * I
                = ((((j : ℕ) : ℝ) * (2 * θ) : ℝ) : ℂ) * I
                by push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
              exact norm_le_pi_norm x j
          _ = (k : ℝ) * ‖x‖ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hKx]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    -- the core mass of `|p(2θ)|²`
    have hcoreW : c * δ₀ ^ (2 * k - 1) / 2 / (k : ℝ) ^ 2
        ≤ ∫ θ in (δ₀ / 2)..δ₀, ‖p θ‖ ^ 2 / Kx := by
      set q : ℝ → ℝ := fun φ =>
        ‖GaloisForLFunctions.HTGeometry.shortArcTrigPoly (fun j => (x j : ℂ)) φ‖ ^ 2 / Kx with hq
      have hscale := intervalIntegral.integral_comp_mul_left q (by norm_num : (2 : ℝ) ≠ 0)
        (a := δ₀ / 2) (b := δ₀)
      have hpq : (fun θ => ‖p θ‖ ^ 2 / Kx) = fun θ => q (2 * θ) := by
        funext θ; simp only [hp, hq]
      rw [hpq, hscale, show 2 * (δ₀ / 2) = δ₀ by ring, smul_eq_mul]
      have hshift := intervalIntegral.integral_comp_add_right q δ₀ (a := 0) (b := δ₀)
      rw [zero_add, show δ₀ + δ₀ = 2 * δ₀ by ring] at hshift
      rw [← hshift]
      set y : Fin k → ℂ := fun j => (x j : ℂ) * Complex.exp (((j : ℕ) : ℂ) * ((δ₀ : ℝ) : ℂ) * I)
        with hy
      have hpy : ∀ θ, q (θ + δ₀)
          = ‖GaloisForLFunctions.HTGeometry.shortArcTrigPoly y θ‖ ^ 2 / Kx := by
        intro θ
        simp only [hq, hy]
        rw [shortArcTrigPoly_add]
      have hyn : ‖y‖ = ‖x‖ := by
        have hj : ∀ j, ‖y j‖ = ‖x j‖ := by
          intro j
          simp only [hy]
          rw [norm_mul, show ((j : ℕ) : ℂ) * ((δ₀ : ℝ) : ℂ) * I
            = ((((j : ℕ) : ℝ) * δ₀ : ℝ) : ℂ) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
        refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
          ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_)
        · rw [hj]; exact norm_le_pi_norm x j
        · rw [← hj]; exact norm_le_pi_norm y j
      have hs := hshort δ₀ hδ₀pos hΛh y
      rw [hyn] at hs
      simp_rw [hpy]
      rw [intervalIntegral.integral_div]
      have hKx' : Kx = (k : ℝ) ^ 2 * ‖x‖ ^ 2 := by rw [hKx]; ring
      rw [hKx']
      have hx2 : 0 < ‖x‖ ^ 2 := by positivity
      calc c * δ₀ ^ (2 * k - 1) / 2 / (k : ℝ) ^ 2
          = 2⁻¹ * ((c * δ₀ ^ (2 * k - 1) * ‖x‖ ^ 2) / ((k : ℝ) ^ 2 * ‖x‖ ^ 2)) := by
            field_simp
        _ ≤ 2⁻¹ * ((∫ θ in (0 : ℝ)..δ₀,
              ‖GaloisForLFunctions.HTGeometry.shortArcTrigPoly y θ‖ ^ 2)
              / ((k : ℝ) ^ 2 * ‖x‖ ^ 2)) := by gcongr
    have hwpos := integral_weighted_pos_of_arc_bounds_scaled_int (w := fun θ => ‖p θ‖ ^ 2 / Kx)
      hSc (by fun_prop) hR0 hu0 hK1 hU hF₁lo hF₁hi hD hD0 hb htail
      (fun θ _ _ => by positivity)
      (fun θ _ _ => by
        have := hpbd θ
        rw [div_le_iff₀ hKx0]; nlinarith)
      hcoreW (by positivity) hδ₀pos hδ₀δ hδθ hcore hphase
      (by rw [hmidexp]; exact hmidΛ) (by linarith only [htailΛ])
    have hform := toeplitz_quadForm_eq_gen (φ := fun θ => 2 * θ) hSc (by fun_prop) 0
      (Real.pi / 2) x
    have hlhs : x ⬝ᵥ (T *ᵥ x) = ∑ i : Fin k, ∑ j : Fin k, x i * x j
        * ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R n θ
          * Complex.exp (-(((((i : ℕ) : ℝ) - (j : ℕ)) * (2 * θ) : ℝ) : ℂ) * I)).re := by
      simp only [dotProduct, Matrix.mulVec, hT, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hlhs, hform]
    have hmul : ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R n θ).re * ‖p θ‖ ^ 2
        = Kx * ∫ θ in (0 : ℝ)..(Real.pi / 2), (sliceArc t R n θ).re * (‖p θ‖ ^ 2 / Kx) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext θ
      field_simp
    simp only [hp] at hmul
    rw [hmul]
    exact mul_pos hKx0 hwpos
  have hTdet : 0 < T.det := GaloisForLFunctions.HTGeometry.det_pos_of_quadForm_pos T hTpos
  -- the coefficient matrix
  have hR2 : 0 < R ^ 2 := by positivity
  have hRh : 1 / 2 < R := by linarith
  set X := ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hX
  have hXpos : 0 < X := by
    rw [hX]; exact pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith))) 2
  set C := 2 * X / (Real.pi * (R ^ 2) ^ n) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  have hentry : ∀ i j : Fin k,
      (Matrix.of fun i j : Fin k => (xiSliceCoeff t (2 * (n + i - j))).re) i j
      = C * (R ^ 2) ^ (j : ℕ) / (R ^ 2) ^ (i : ℕ) * T i j := by
    intro i j
    have hji : (j : ℕ) ≤ n + i := by have := j.isLt; omega
    have hcast : (((n + i - j : ℕ) : ℝ) - n) = ((i : ℕ) : ℝ) - (j : ℕ) := by
      rw [Nat.cast_sub hji]; push_cast; ring
    have hf := congrArg Complex.re (xiSliceCoeff_two_mul_eq_quarter_freq t n (n + i - j) hRh)
    rw [Complex.ofReal_re, hcast, pow_mul] at hf
    rw [Matrix.of_apply, hf, scale_entry_eq hR2 hji]
    rfl
  rw [det_eq_pow_mul_det_of_diag_conj hR2 T _ hentry]
  exact mul_pos (pow_pos hCpos k) hTdet

/-- **Toeplitz windows at the centre.**  For `r ≥ 1`, `0 < η ≤ 1/8` and `R₁ ≥ 1` there is `t₀ ≥ 1`
such that `det [c_{2(k+i−j)}(t)]_{i,j<r} > 0` whenever `t ≥ t₀`, `k ≥ r − 1` and
`(¼ + 2η) log t ≤ k ≤ (R₁/4) log t`. -/
theorem exists_xiSliceCoeff_toeplitzDet_pos_sharp_window (r : ℕ) (hr : 1 ≤ r) {η R₁ : ℝ}
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hR₁ : 1 ≤ R₁) :
    ∃ t₀ : ℝ, 1 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ k : ℕ, r - 1 ≤ k → (1 / 4 + 2 * η) * Real.log t ≤ k →
      (k : ℝ) ≤ R₁ / 4 * Real.log t →
      0 < (Matrix.of fun i j : Fin r => (xiSliceCoeff t (2 * (k + i - j))).re).det := by
  obtain ⟨cS, hcS, h₀, hh₀, hshort⟩ :=
    GaloisForLFunctions.HTGeometry.exists_integral_shortArcTrigPoly_sq_ge r hr
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = 2 * r - 1 := ⟨_, rfl⟩
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 7 / 160 * (cS / 2 / (r : ℝ) ^ 2) := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; positivity
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log 4 + Real.pi + 4 * E := ⟨_, rfl⟩
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hM0 : 0 < M := by rw [hMdef]; positivity
  have hR₁0 : 0 < R₁ := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K, K = R₁ / (2 * η) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hKdef, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨θ₁, hθ₁def⟩ : ∃ θ₁, θ₁ = 1 / (1000 * K) := ⟨_, rfl⟩
  have hθ₁0 : 0 < θ₁ := by rw [hθ₁def]; positivity
  have hR₁θ : R₁ * θ₁ = η / 500 := by
    rw [hθ₁def, hKdef]; field_simp; ring
  obtain ⟨c, hcdef⟩ : ∃ c, c = θ₁ ^ 2 / 10 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hcη : c ≤ η := by
    have h1 : θ₁ ≤ η / 500 := by rw [← hR₁θ]; exact le_mul_of_one_le_left hθ₁0.le hR₁
    have h2 : θ₁ ^ 2 ≤ θ₁ := by
      rw [sq]; exact mul_le_of_le_one_left hθ₁0.le (by linarith)
    rw [hcdef]; linarith
  obtain ⟨A, hA0, htail⟩ := exists_sliceArc_tail_le_euler (R₁ := R₁) hη (by linarith) hθ₁0
  -- thresholds in `Λ`
  have e1 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_fifth_root (N / 2 : ℝ))).2 (500 * κ)
    (by positivity)
  have e6 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2))).2
    h₀ hh₀
  have e3 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 5))).2 θ₁ hθ₁0
  have e4 := (tendsto_order.1 (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 5))).2
    (3 / (2 * (1 + 128 * K))) (by positivity)
  obtain ⟨Λ₀, hΛ₀⟩ := Filter.eventually_atTop.mp (e1.and (e3.and (e4.and e6)))
  -- threshold in `log t` for the tail
  have e5 := (tendsto_order.1 (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (N / 2 : ℝ) c hc0)).2
    (κ / (2 * Real.pi * A * R₁ ^ (N / 2 : ℝ))) (by positivity)
  obtain ⟨U₅, hU₅⟩ := Filter.eventually_atTop.mp e5
  -- the threshold `L` for `log t`
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hpi := Real.pi_pos
  have hRMη : 0 ≤ R₁ * M / η := by positivity
  have hEη : 0 ≤ E / η := by positivity
  have hΛ₀a := abs_nonneg Λ₀
  have hU₅a := abs_nonneg U₅
  obtain ⟨L, hLdef⟩ : ∃ L, L = 32 * R₁ + 16 + 2 * |Λ₀| + 2
      + 10 * (Real.log 2 + 2 * E + R₁ * M / η)
      + (Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η) + E / η + |U₅| := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  refine ⟨Real.exp L, Real.one_le_exp hL0, ?_⟩
  intro t ht k hkr hklo hkhi
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos L) ht
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  rw [← hudef] at hklo hkhi
  have hLu : L ≤ u := by
    rw [hudef, ← Real.log_exp L]; exact Real.log_le_log (Real.exp_pos L) ht
  have htu : u + 1 ≤ t := by
    have := Real.add_one_le_exp u
    rw [hudef, Real.exp_log ht0] at this; rw [hudef]; exact this
  rw [hLdef] at hLu
  have hu1 : 32 * R₁ + 16 ≤ u := by linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0]
  have hu2 : 2 * |Λ₀| + 2 ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu3 : 10 * (Real.log 2 + 2 * E + R₁ * M / η) ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu4 : Real.log (3 / 2) + Real.pi / 2 + 2 * E + R₁ * M / η ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu5 : E / η ≤ u := by
    linarith only [hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu6 : U₅ ≤ u := by
    have := le_abs_self U₅
    linarith only [this, hLu, hΛ₀a, hU₅a, hl2, hl32, hpi, hRMη, hEη, hE0, hR₁0]
  have hu0 : 0 < u := by linarith only [hu1, hR₁0]
  have ht32 : 32 * R₁ + 16 ≤ t := by linarith only [hu1, htu]
  have ht8 : 8 ≤ t := by linarith only [ht32, hR₁0]
  have hR₁t : R₁ ≤ t / 2 := by linarith only [ht32, hR₁0]
  -- the saddle radius
  have hlo : (1 / 2 + 2 * η) * (Real.log t + 2 * xiEulerConstant η) ≤ 2 * (k : ℝ) := by
    rw [← hudef, ← hEdef]
    have h1 : 2 * η * (E / η) = 2 * E := by field_simp
    have h2 : 2 * η * (E / η) ≤ 2 * η * u := mul_le_mul_of_nonneg_left hu5 (by linarith)
    have h3 : η * E ≤ 1 / 8 * E := mul_le_mul_of_nonneg_right hη8 hE0.le
    linarith only [h1, h2, h3, hklo, hE0]
  have hhi : 2 * (k : ℝ) ≤ R₁ * (Real.log (t / 2) - 2 * xiEulerConstant η) := by
    rw [Real.log_div ht0.ne' (by norm_num), ← hudef, ← hEdef]
    have h1 : Real.log 2 + 2 * E ≤ u / 2 := by linarith only [hu3, hRMη, hl2, hE0]
    have h2 := mul_le_mul_of_nonneg_left h1 hR₁0.le
    linarith only [h2, hkhi]
  obtain ⟨R, ⟨hRa, hRb⟩, hsad⟩ := exists_saddle_radius_euler (t := t) (k := k) hη ht8
    (by linarith : 1 / 2 + η ≤ 1 / 2 + 2 * η) (by linarith : 1 / 2 + 2 * η ≤ R₁) hR₁t hlo hhi
  have hR0 : 0 < R := by linarith only [hRa, hη]
  have hRt : R ≤ t / 2 := le_trans hRb hR₁t
  -- the slope
  obtain ⟨hF₁lo, hF₁hi⟩ := xiSlice_saddleSlope_bounds_euler (t := t) (R := R) hη
    (by linarith) ht8 hRa hRt
  rw [← hEdef] at hF₁lo hF₁hi
  rw [← hMdef] at hF₁lo hF₁hi
  have hRM : R * M / η ≤ R₁ * M / η :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRb hM0.le) hη.le
  rw [Real.log_div ht0.ne' (by norm_num), ← hudef] at hF₁lo
  rw [← hudef] at hF₁hi
  have hF₁lo' : 9 / 10 * u ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re := by
    linarith only [hF₁lo, hRM, hu3]
  have hF₁hi' : (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re ≤ 2 * u := by
    linarith only [hF₁hi, hRM, hu3, hl2, hRMη, hE0]
  -- the disc constant
  have hKd : xiSliceDiscConstantEuler η t R ≤ 2 * η * u := by
    unfold xiSliceDiscConstantEuler
    rw [← hEdef, ← hMdef]
    have e : Real.log (3 * t / 2) = Real.log (3 / 2) + u := by
      rw [show 3 * t / 2 = 3 / 2 * t by ring, Real.log_mul (by norm_num) ht0.ne', hudef]
    rw [e]
    have h1 : η * (R₁ * M / η) = R₁ * M := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hu4 hη.le
    have h3 : R * M ≤ R₁ * M := mul_le_mul_of_nonneg_right hRb hM0.le
    linarith only [h1, h2, h3]
  -- the tail on `[1/(1000K), π/2]`
  have htail' : ∀ θ : ℝ, 1 / (1000 * K) ≤ θ → θ ≤ Real.pi / 2 →
      ‖sliceArc t R k θ‖ ≤ 2 * A * t ^ (-c) := by
    intro θ hθ hθπ
    have h := htail t R θ k ht32 hRa hRb (by rw [hθ₁def]; exact hθ) hθπ
    rw [← hcdef] at h
    have hηc : t ^ (-η) ≤ t ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    calc ‖sliceArc t R k θ‖ ≤ A * (t ^ (-η) + t ^ (-c)) := h
      _ ≤ A * (t ^ (-c) + t ^ (-c)) := mul_le_mul_of_nonneg_left (by linarith) hA0.le
      _ = 2 * A * t ^ (-c) := by ring
  -- the scale conditions
  have hΛlo : u / 2 ≤ R * u := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) / 2 ≤ R) hu0.le; linarith
  have hΛhi : R * u ≤ R₁ * u := mul_le_mul_of_nonneg_right hRb hu0.le
  have hΛbig : max Λ₀ 1 ≤ R * u :=
    max_le (by have := le_abs_self Λ₀; linarith only [this, hΛlo, hu2])
      (by linarith only [hΛlo, hu2, hΛ₀a])
  obtain ⟨hE1, hE3, hE4, hE6⟩ := hΛ₀ (R * u) (le_trans (le_max_left _ _) hΛbig)
  rw [hθ₁def] at hE3
  have hΛpos : 0 < R * u := by linarith only [hΛlo, hu0]
  have hpowΛ : ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * r - 1) = (R * u) ^ (-(N / 2 : ℝ)) := by
    rw [← hNdef, ← Real.rpow_natCast ((R * u) ^ (-(1 / 2) : ℝ)), ← Real.rpow_mul hΛpos.le]
    congr 1
    ring
  have hprodΛ : (R * u) ^ (N / 2 : ℝ) * (R * u) ^ (-(N / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hΛpos]; norm_num
  have hnegΛ : 0 < (R * u) ^ (-(N / 2 : ℝ)) := Real.rpow_pos_of_pos hΛpos _
  have hrhs : 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * r - 1) / 2 / (r : ℝ) ^ 2)
      = κ * (R * u) ^ (-(N / 2 : ℝ)) := by
    rw [hpowΛ, hκdef]
    field_simp
  have hmid : 2 * (1 / 1000 * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8))
      ≤ 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * r - 1) / 2 / (r : ℝ) ^ 2) := by
    rw [hrhs]
    have h1 : Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8)
        = (R * u) ^ (N / 2 : ℝ) * Real.exp (-((R * u) ^ (1 / 5 : ℝ)) / 8)
          * (R * u) ^ (-(N / 2 : ℝ)) := by
      rw [mul_comm ((R * u) ^ (N / 2 : ℝ)), mul_assoc, hprodΛ, mul_one]
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hE1.le hnegΛ.le
    linarith only [h2]
  have htailE : 2 * (Real.pi / 2 * (2 * A * t ^ (-c)))
      ≤ 7 / 160 * (cS * ((R * u) ^ (-(1 / 2) : ℝ)) ^ (2 * r - 1) / 2 / (r : ℝ) ^ 2) := by
    rw [hrhs]
    have htc : t ^ (-c) = Real.exp (-c * u) := by
      rw [Real.rpow_def_of_pos ht0, hudef]; ring_nf
    have hpow : (R * u) ^ (N / 2 : ℝ) ≤ R₁ ^ (N / 2 : ℝ) * u ^ (N / 2 : ℝ) := by
      rw [← Real.mul_rpow hR₁0.le hu0.le]
      exact Real.rpow_le_rpow hΛpos.le hΛhi (by positivity)
    have h5 := (hU₅ u hu6).le
    have hR₁N : 0 < R₁ ^ (N / 2 : ℝ) := Real.rpow_pos_of_pos hR₁0 _
    have key : 2 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ) ≤ κ := by
      calc 2 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ)
          ≤ 2 * Real.pi * A * Real.exp (-c * u) * (R₁ ^ (N / 2 : ℝ) * u ^ (N / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = 2 * Real.pi * A * R₁ ^ (N / 2 : ℝ) * (u ^ (N / 2 : ℝ) * Real.exp (-c * u)) := by ring
        _ ≤ 2 * Real.pi * A * R₁ ^ (N / 2 : ℝ) * (κ / (2 * Real.pi * A * R₁ ^ (N / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = κ := by field_simp
    rw [htc]
    have h3 := mul_le_mul_of_nonneg_right key hnegΛ.le
    have e : 2 * Real.pi * A * Real.exp (-c * u) * (R * u) ^ (N / 2 : ℝ) * (R * u) ^ (-(N / 2 : ℝ))
        = 2 * (Real.pi / 2 * (2 * A * Real.exp (-c * u))) := by
      rw [mul_assoc (2 * Real.pi * A * Real.exp (-c * u)), hprodΛ]; ring
    linarith
  exact xiSliceCoeff_toeplitzDet_pos_of_saddle_euler hr hkr hη hη8 hR₁ hKdef ht8 hu0 hRa hRb
    hRt hsad hF₁lo' hF₁hi' hKd htail' (le_trans (le_max_right _ _) hΛbig) hE3 hE4 hcS
    hshort hE6.le hmid htailE

end

end RHTower
