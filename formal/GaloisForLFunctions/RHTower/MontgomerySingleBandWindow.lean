import GaloisForLFunctions.RHTower.MontgomeryBochnerBandSum

/-!
# The band block of the pair form over a window of scales

For a set `A` of zero copies whose real parts lie in the band `[σ, σ + τ/log T]` and whose
ordinates are `D`-separated in mean-spacing units, the integral of the `A`-block of Montgomery's
form over the scale window `[a, a+ℓ]` is at least `2 e^{−3} T^{2a(σ−1/2)} c_K |A|`, with `c_K` the
Montgomery–Vaughan band constant.  Ingredients: the `|ξ| ≤ 1` Bochner window, Fubini on the
rectangle, the common amplitude `T^{α(σ−1/2)} ≥ T^{a(σ−1/2)}`, and the band-perturbation bound.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Fubini for a continuous integrand on a rectangle, in interval-integral form. -/
theorem interval_integral_swap_of_continuous {f : ℝ → ℝ → ℝ}
    (hf : Continuous (Function.uncurry f)) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  simp_rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact hK
  exact hint.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Exponential form of the zero power sum at scale `T^α e^{−ξ}`. -/
theorem zeroPowerSum_scale_eq_exp (A : Finset XiZeroCopy) {T : ℝ} (hT : 0 < T) (α ξ : ℝ) :
    zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ)) =
      ∑ j ∈ A, cexp (((j.1 : ℂ) - 1 / 2) * (((α * Real.log T : ℝ) : ℂ) - (ξ : ℂ))) := by
  unfold zeroPowerSum
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT α
  rw [cpow_mul_exp_neg hx ξ ((j.1 : ℂ) - 1 / 2)]
  have hxne : ((T ^ α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hxne, ← Complex.ofReal_log hx.le, Real.log_rpow hT, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Joint continuity of the squared zero power sum in scale and Laplace variables. -/
theorem continuous_normSq_zeroPowerSum_scale (A : Finset XiZeroCopy) {T : ℝ} (hT : 0 < T) :
    Continuous (Function.uncurry fun α ξ : ℝ =>
      ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2) := by
  have hfun : (Function.uncurry fun α ξ : ℝ =>
      ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2)
      = fun p : ℝ × ℝ => ‖∑ j ∈ A, cexp (((j.1 : ℂ) - 1 / 2) *
          (((p.1 * Real.log T : ℝ) : ℂ) - (p.2 : ℂ)))‖ ^ 2 := by
    funext p
    simp only [Function.uncurry]
    rw [zeroPowerSum_scale_eq_exp A hT]
  rw [hfun]
  fun_prop

/-- The pair form of a finite configuration is continuous in the scale exponent. -/
theorem continuous_montgomeryForm_rpow (A : Finset XiZeroCopy) {T : ℝ} (hT : 0 < T) :
    Continuous (fun α : ℝ => (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re) := by
  have hfun : (fun α : ℝ => montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α))
      = fun α : ℝ => ∑ j ∈ A, ∑ k ∈ A,
          cexp (((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) * ((α * Real.log T : ℝ) : ℂ)) *
            montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) := by
    funext α
    unfold montgomeryForm
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have hx : 0 < T ^ α := Real.rpow_pos_of_pos hT α
    have hxne : ((T ^ α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    rw [cpow_def_of_ne_zero hxne, ← Complex.ofReal_log hx.le, Real.log_rpow hT]
    congr 1
    push_cast
    ring
  have : Continuous (fun α : ℝ => montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)) := by
    rw [hfun]
    fun_prop
  exact Complex.continuous_re.comp this

/-- The Montgomery–Vaughan band constant. -/
def mvBandConstant (ℓ D τ : ℝ) (K N : ℕ) : ℝ :=
  1 / 2 * (ℓ - 26 / (Real.pi * D))
    - 4 * (ℓ + 26 / (Real.pi * D)) * ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)
    - 2 * ℓ * (N : ℝ) * (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ 2

/-- **Scale-window lower bound from a per-`ξ` inner bound.**  If the inner scale integral of the
squared zero power sum is at least `Λ` for every `|ξ| ≤ 1`, then the window integral of the
`A`-block of Montgomery's form is at least `2 e^{−2} Λ`. -/
theorem montgomeryForm_window_ge_of_inner (A : Finset XiZeroCopy) {T a ℓ : ℝ} (hT : 0 < T)
    (hℓ : 0 ≤ ℓ) (Λ : ℝ)
    (hinner : ∀ ξ ∈ Icc (-1 : ℝ) 1, Λ ≤ ∫ α in a..a + ℓ,
      ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2) :
    2 * Real.exp (-2) * Λ
      ≤ ∫ α in a..a + ℓ, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
  classical
  set b := a + ℓ with hb
  have hab' : a ≤ b := by rw [hb]; linarith
  set g : ℝ → ℝ → ℝ := fun α ξ =>
    ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2 with hg
  have hgcont : Continuous (Function.uncurry g) := continuous_normSq_zeroPowerSum_scale A hT
  have hstep1 : ∀ α, Real.exp (-2) * ∫ ξ in (-1 : ℝ)..1, g α ξ
      ≤ (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re :=
    fun α => montgomeryForm_re_ge_window A (Real.rpow_pos_of_pos hT α)
  have hcontF := continuous_montgomeryForm_rpow A hT
  have hcontInner : Continuous (fun α => ∫ ξ in (-1 : ℝ)..1, g α ξ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := -1)
      (s := fun _ => (1 : ℝ)) hgcont continuous_const
  have hint1 : (∫ α in a..b, Real.exp (-2) * ∫ ξ in (-1 : ℝ)..1, g α ξ)
      ≤ ∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
    apply intervalIntegral.integral_mono_on hab'
    · exact (continuous_const.mul hcontInner).intervalIntegrable _ _
    · exact hcontF.intervalIntegrable _ _
    · intro α _; exact hstep1 α
  have hswap : (∫ α in a..b, ∫ ξ in (-1 : ℝ)..1, g α ξ) = ∫ ξ in (-1 : ℝ)..1, ∫ α in a..b, g α ξ :=
    interval_integral_swap_of_continuous hgcont hab' (by norm_num)
  have hcontOuter : Continuous (fun ξ => ∫ α in a..b, g α ξ) := by
    have hsw : Continuous (Function.uncurry fun ξ α => g α ξ) := by
      have : (Function.uncurry fun ξ α => g α ξ) = (Function.uncurry g) ∘ Prod.swap := by
        funext p; rfl
      rw [this]
      exact hgcont.comp continuous_swap
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := a)
      (s := fun _ => b) hsw continuous_const
  have hint3 : (∫ ξ in (-1 : ℝ)..1, Λ) ≤ ∫ ξ in (-1 : ℝ)..1, ∫ α in a..b, g α ξ := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact intervalIntegrable_const
    · exact hcontOuter.intervalIntegrable _ _
    · intro ξ hξ
      exact hinner ξ hξ
  rw [intervalIntegral.integral_const] at hint3
  simp only [smul_eq_mul] at hint3
  have hfinal : 2 * Real.exp (-2) * Λ
      ≤ ∫ α in a..b, Real.exp (-2) * ∫ ξ in (-1 : ℝ)..1, g α ξ := by
    rw [intervalIntegral.integral_const_mul, hswap]
    have := mul_le_mul_of_nonneg_left hint3 (Real.exp_pos (-2)).le
    calc 2 * Real.exp (-2) * Λ = Real.exp (-2) * ((1 - (-1)) * Λ) := by ring
      _ ≤ _ := this
  rw [hb] at hfinal hint1
  linarith [hfinal, hint1]

/-- **Band block over a scale window.** -/
theorem singleBand_block_window_ge (A : Finset XiZeroCopy) {T σ D a ℓ τ : ℝ} (hT : 1 < T)
    (hD : 0 < D) (hℓ : 0 ≤ ℓ) (ha : 0 ≤ a) (hab : a + ℓ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hσ : 1 / 2 ≤ σ)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    {K : ℕ} (hK : 1 ≤ K) (hc : 0 ≤ mvBandConstant ℓ D τ K A.card) :
    2 * Real.exp (-3) * Real.exp (2 * (a * (σ - 1 / 2) * Real.log T)) *
        mvBandConstant ℓ D τ K A.card * A.card
      ≤ ∫ α in a..a + ℓ, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
  classical
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  set b := a + ℓ with hb
  have hab' : a ≤ b := by rw [hb]; linarith
  set c := mvBandConstant ℓ D τ K A.card with hcdef
  set E : ℝ := Real.exp (2 * (a * (σ - 1 / 2) * Real.log T)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set g : ℝ → ℝ → ℝ := fun α ξ =>
    ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2 with hg
  have hgcont : Continuous (Function.uncurry g) := continuous_normSq_zeroPowerSum_scale A hT0
  have hinner : ∀ ξ ∈ Icc (-1 : ℝ) 1,
      E * c * Real.exp (-1) * A.card ≤ ∫ α in a..b, g α ξ := by
    intro ξ hξ
    set u : A → ℝ := fun j => bandFreq T j with hu
    set d : A → ℂ := fun j => bandCoeff ξ j with hd
    set θ : A → ℝ := fun j => bandTheta T σ j with hθ
    set B : ℝ → ℂ := fun α => GaloisForLFunctions.HTGeometry.mvBandSum u d θ α with hB
    have hgB : ∀ α, g α ξ = Real.exp (2 * (α * (σ - 1 / 2) * Real.log T)) * ‖B α‖ ^ 2 := by
      intro α
      simp only [hg, hB, hu, hd, hθ]
      exact normSq_zeroPowerSum_eq_bandSum A hT0 σ ξ α
    have hBcont : Continuous B := by
      simp only [hB]
      unfold GaloisForLFunctions.HTGeometry.mvBandSum
      fun_prop
    have hmono : ∀ α ∈ Icc a b, E * ‖B α‖ ^ 2 ≤ g α ξ := by
      intro α hα
      rw [hgB α, hE]
      have : Real.exp (2 * (a * (σ - 1 / 2) * Real.log T))
          ≤ Real.exp (2 * (α * (σ - 1 / 2) * Real.log T)) := by
        apply Real.exp_le_exp.mpr
        have hσ' : 0 ≤ σ - 1 / 2 := by linarith
        have : a * (σ - 1 / 2) * Real.log T ≤ α * (σ - 1 / 2) * Real.log T := by
          gcongr
          exact hα.1
        linarith
      gcongr
    have hint2 : E * ∫ α in a..b, ‖B α‖ ^ 2 ≤ ∫ α in a..b, g α ξ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab'
      · exact (continuous_const.mul (hBcont.norm.pow 2)).intervalIntegrable _ _
      · exact (hgcont.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
      · exact hmono
    have hθb : ∀ r : A, |θ r| ≤ τ := by
      intro r
      obtain ⟨h1, h2⟩ := hband r.1 r.2
      simp only [hθ, bandTheta]
      have h0 : 0 ≤ (((r.1).1 : ℂ).re - σ) * Real.log T := mul_nonneg (by linarith) hL.le
      rw [abs_of_nonneg h0]
      have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
      calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
        _ = τ := by field_simp
    have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
      intro r s hrs
      exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
    have hband_lemma := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_ge
      u d θ hD hℓ ha hab hτ0 hτ1 hθb hsep' hK
    have hcoef : Real.exp (-1) * A.card ≤ ∑ r : A, ‖d r‖ ^ 2 := by
      have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
      have : ∀ r : A, Real.exp (-1) ≤ ‖d r‖ ^ 2 := by
        intro r
        refine le_trans ?_ (normSq_bandCoeff_ge ξ r.1)
        apply Real.exp_le_exp.mpr
        linarith
      calc Real.exp (-1) * A.card = ∑ _r : A, Real.exp (-1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ r : A, ‖d r‖ ^ 2 := Finset.sum_le_sum fun r _ => this r
    have hcard : (Fintype.card A : ℝ) = A.card := by rw [Fintype.card_coe]
    have hband' : c * (Real.exp (-1) * A.card) ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by
      have h := hband_lemma
      unfold mvBandConstant at hcdef
      rw [hcard] at h
      calc c * (Real.exp (-1) * A.card) ≤ c * ∑ r : A, ‖d r‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hcoef hc
        _ ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by
            rw [hcdef]
            simpa [hb] using h
    calc E * c * Real.exp (-1) * A.card = E * (c * (Real.exp (-1) * A.card)) := by ring
      _ ≤ E * ∫ α in a..b, ‖B α‖ ^ 2 := mul_le_mul_of_nonneg_left hband' hE0.le
      _ ≤ ∫ α in a..b, g α ξ := hint2
  have := montgomeryForm_window_ge_of_inner A hT0 hℓ (E * c * Real.exp (-1) * A.card)
    (by intro ξ hξ; exact hinner ξ hξ)
  have h3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  calc 2 * (Real.exp (-2) * Real.exp (-1)) * E * c * A.card
      = 2 * Real.exp (-2) * (E * c * Real.exp (-1) * A.card) := by ring
    _ ≤ _ := this

end

end RHTower
