import GaloisForLFunctions.RHTower.MontgomerySingleBandIsolation
import GaloisForLFunctions.HTGeometry.MontgomeryVaughanDampedMeanSquare

/-!
# The single-band isolation law for wide bands

The band width of the single-band isolation law is no longer restricted to `τ/log T` with
`τ ≤ 1`.  With the damped Montgomery–Vaughan inequality, a band `[σ, σ + τ/log T]` of any width
`τ ≥ 0` gives the lower bound
`2 e^{−3} T^{2a(σ−1/2)} (ℓ₀ e^{−2τℓ₀} − 26/(πD) − 9τ/(π²D²)) |A|` for the window integral of the
band block, for every `0 ≤ ℓ₀ ≤ ℓ`.  The constant is positive as soon as the separation `D`
exceeds a fixed multiple of the band width `τ`: the natural unit of band width is the
separation in mean gaps divided by `log T`.  Consequently, `D`-separated zero copies in a band
of width `τ/log T` with `D ≥ 100 τ` (and `τ ≥ 5/3`) number at most
`(3 e³ τ/π) T^{1 − (6/5)(σ−1/2)} log T`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The damped Montgomery–Vaughan band constant `ℓ₀ e^{−2τℓ₀} − 26/(πD) − 9τ/(π²D²)`. -/
def mvWideBandConstant (ℓ₀ D τ : ℝ) : ℝ :=
  ℓ₀ * Real.exp (-(2 * τ * ℓ₀)) - 26 / (Real.pi * D) - 9 * τ / (Real.pi ^ 2 * D ^ 2)

/-- **Band block over a scale window, wide bands.** -/
theorem singleBand_block_window_ge_wide (A : Finset XiZeroCopy) {T σ D a ℓ ℓ₀ τ : ℝ}
    (hT : 1 < T) (hD : 0 < D) (hℓ₀ : 0 ≤ ℓ₀) (hℓ : ℓ₀ ≤ ℓ) (ha : 0 ≤ a) (hτ0 : 0 ≤ τ)
    (hσ : 1 / 2 ≤ σ)
    (hband : ∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|)
    (hc : 0 ≤ mvWideBandConstant ℓ₀ D τ) :
    2 * Real.exp (-3) * Real.exp (2 * (a * (σ - 1 / 2) * Real.log T)) *
        mvWideBandConstant ℓ₀ D τ * A.card
      ≤ ∫ α in a..a + ℓ, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
  classical
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hℓ0 : 0 ≤ ℓ := le_trans hℓ₀ hℓ
  set b := a + ℓ with hb
  have hab' : a ≤ b := by rw [hb]; linarith
  set c := mvWideBandConstant ℓ₀ D τ with hcdef
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
    have hθb : ∀ r : A, τ - τ ≤ θ r ∧ θ r ≤ τ := by
      intro r
      obtain ⟨h1, h2⟩ := hband r.1 r.2
      simp only [hθ, bandTheta]
      constructor
      · rw [sub_self]
        exact mul_nonneg (by linarith) hL.le
      · have h3 : ((r.1).1 : ℂ).re - σ ≤ τ / Real.log T := by linarith
        calc (((r.1).1 : ℂ).re - σ) * Real.log T ≤ (τ / Real.log T) * Real.log T := by gcongr
          _ = τ := by field_simp
    have hθnn : ∀ r : A, 0 ≤ θ r := fun r => by
      have := (hθb r).1
      rwa [sub_self] at this
    have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
      intro r s hrs
      exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
    have hband_lemma := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_ge_band
      u d θ (a := a) hD hℓ₀ hℓ hτ0 hτ0 hθb hsep'
    have hcoef : Real.exp (-1) * A.card ≤ ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
      have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
      have : ∀ r : A, Real.exp (-1) ≤ ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
        intro r
        have h1 : Real.exp (-1) ≤ ‖d r‖ ^ 2 := by
          refine le_trans ?_ (normSq_bandCoeff_ge ξ r.1)
          apply Real.exp_le_exp.mpr
          linarith
        have h2 : 1 ≤ Real.exp (2 * θ r * a) := by
          rw [← Real.exp_zero, Real.exp_le_exp]
          have := hθnn r
          positivity
        calc Real.exp (-1) = Real.exp (-1) * 1 := by ring
          _ ≤ ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
              mul_le_mul h1 h2 zero_le_one (by positivity)
      calc Real.exp (-1) * A.card = ∑ _r : A, Real.exp (-1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun r _ => this r
    have hband' : c * (Real.exp (-1) * A.card) ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by
      calc c * (Real.exp (-1) * A.card)
          ≤ c * ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
            mul_le_mul_of_nonneg_left hcoef hc
        _ ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by
            rw [hcdef]
            unfold mvWideBandConstant
            simpa [hb] using hband_lemma
    calc E * c * Real.exp (-1) * A.card = E * (c * (Real.exp (-1) * A.card)) := by ring
      _ ≤ E * ∫ α in a..b, ‖B α‖ ^ 2 := mul_le_mul_of_nonneg_left hband' hE0.le
      _ ≤ ∫ α in a..b, g α ξ := hint2
  have := montgomeryForm_window_ge_of_inner A hT0 hℓ0 (E * c * Real.exp (-1) * A.card)
    (by intro ξ hξ; exact hinner ξ hξ)
  have h3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [h3]
  calc 2 * (Real.exp (-2) * Real.exp (-1)) * E * c * A.card
      = 2 * Real.exp (-2) * (E * c * Real.exp (-1) * A.card) := by ring
    _ ≤ _ := this

/-- **Single-band isolation law, wide bands.**  For a band `[σ, σ + τ/log T]` of any width
`τ ≥ 0`, `D`-separated in mean-spacing units, with all other zeros within `δ₀` of the line and
`σ ≥ 1/2 + 4δ₀`: whenever the damped band constant `κ = ℓ₀ e^{−2τℓ₀} − 26/(πD) − 9τ/(π²D²)` is
positive for some `0 ≤ ℓ₀ ≤ ℓ`, the band has at most `(ℓ e³/(πκ)) T^{1 − 2a(σ−1/2)} log T`
elements. -/
theorem eventually_card_singleBand_le_wide {a ℓ ℓ₀ σ δ₀ D τ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hσ : 1 / 2 + 4 * δ₀ ≤ σ) (hD : 0 < D) (hτ0 : 0 ≤ τ)
    (hℓ₀ : 0 ≤ ℓ₀) (hℓ₀ℓ : ℓ₀ ≤ ℓ) (hκ : 0 < mvWideBandConstant ℓ₀ D τ) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|) →
      (A.card : ℝ) ≤ (ℓ * Real.exp 3 / (Real.pi * mvWideBandConstant ℓ₀ D τ)) *
        T ^ (1 - 2 * a * (σ - 1 / 2)) * Real.log T := by
  classical
  set κ := mvWideBandConstant ℓ₀ D τ with hκdef
  set b := a + ℓ with hb
  set δ := σ - 1 / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδ₀δ : 4 * δ₀ ≤ δ := by rw [hδ]; linarith
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := hab
  have hab' : a ≤ b := by rw [hb]; linarith
  set η := 2 * a * δ - b * (δ₀ + δ) with hη
  have hηpos : 0 < η := by
    rw [hη]
    have : 4 * b ≤ 6 * a := by rw [hb]; linarith
    nlinarith [hδpos, hδ₀δ, hb0]
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  set ε₁ : ℝ := Real.exp (-3) * κ / (192 * Real.exp τ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  -- eventual facts
  have E1 := eventually_montgomeryForm_div_leadingOrder_uniform ha hab' hb1 (one_pos)
  have E2 := eventually_log_bounds
  have E3 := (tendsto_log_pow_div_rpow 1 hηpos).eventually (eventually_le_nhds hε₁pos)
  have E4 := Real.tendsto_log_atTop.eventually_ge_atTop C₀
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro A hA hband hR hsep
  obtain ⟨hl1, _, _, hl4⟩ := e2
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set L := Real.log T with hLdef
  set N : ℝ := (A.card : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  -- (i) the band block over the window
  have hwindow := singleBand_block_window_ge_wide A hT1 hD hℓ₀ hℓ₀ℓ ha.le hτ0 (by linarith)
    hband hsep hκ.le
  have hEexp : Real.exp (2 * (a * (σ - 1 / 2) * Real.log T)) = T ^ (2 * a * δ) := by
    rw [Real.rpow_def_of_pos hT0, hδ]
    congr 1
    ring
  rw [hEexp, ← hb, ← hκdef] at hwindow
  have hlow : 2 * Real.exp (-3) * T ^ (2 * a * δ) * κ * N
      ≤ ∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := hwindow
  -- (ii) pointwise upper bound for the band block at every scale of the window
  have hW : windowLog T ≤ 3 * L := by
    unfold windowLog
    linarith
  have hpt : ∀ α ∈ Icc a b,
      (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
    intro α hα
    have hα0 : 0 ≤ α := ha.le.trans hα.1
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα0
    have hx0 : 0 < T ^ α := by linarith
    have hF : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L := by
      have h := e1 α hα
      have hNα : 0 < (T / (2 * Real.pi)) * (α * L) := by
        have : 0 < α := lt_of_lt_of_le ha hα.1
        positivity
      rw [abs_lt] at h
      have h2 := h.2
      rw [div_sub_one (ne_of_gt hNα), div_lt_iff₀ hNα] at h2
      have hαL : α * L ≤ L := by
        have : α ≤ 1 := by linarith [hα.2]
        nlinarith
      calc (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          ≤ 1 * (T / (2 * Real.pi) * (α * L)) + T / (2 * Real.pi) * (α * L) := by linarith
        _ = T / Real.pi * (α * L) := by field_simp; ring
        _ ≤ T / Real.pi * L := by gcongr
    have hRα : ∀ k ∈ zeroWindow T \ A, zeroAmp (T ^ α) k ≤ (T ^ α) ^ δ₀ := by
      intro k hk
      unfold zeroAmp
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith [hR k hk]
    have hsplit := montgomeryForm_block_split hx0 A hA (Θ := (T ^ α) ^ δ₀) (by positivity) hRα
    have hamp : ∑ j ∈ A, zeroAmp (T ^ α) j ≤ N * (T ^ (b * δ) * Real.exp τ) := by
      have hone : ∀ j ∈ A, zeroAmp (T ^ α) j ≤ T ^ (b * δ) * Real.exp τ := by
        intro j hj
        obtain ⟨_, hj2⟩ := hband j hj
        unfold zeroAmp
        rw [← Real.rpow_mul hT0.le]
        have hexp : α * ((j.1 : ℂ).re - 1 / 2) ≤ b * δ + τ / L := by
          have h1 : (j.1 : ℂ).re - 1 / 2 ≤ δ + τ / L := by rw [hδ]; linarith
          have h2 : 0 ≤ δ + τ / L := by positivity
          calc α * ((j.1 : ℂ).re - 1 / 2) ≤ α * (δ + τ / L) := by gcongr
            _ ≤ b * (δ + τ / L) := mul_le_mul_of_nonneg_right hα.2 h2
            _ = b * δ + b * (τ / L) := by ring
            _ ≤ b * δ + τ / L := by
                have : b * (τ / L) ≤ 1 * (τ / L) :=
                  mul_le_mul_of_nonneg_right hb1.le (by positivity)
                linarith
        calc T ^ (α * ((j.1 : ℂ).re - 1 / 2)) ≤ T ^ (b * δ + τ / L) :=
              Real.rpow_le_rpow_of_exponent_le hT1.le hexp
          _ = T ^ (b * δ) * T ^ (τ / L) := Real.rpow_add hT0 _ _
          _ = T ^ (b * δ) * Real.exp τ := by
              congr 1
              rw [Real.rpow_def_of_pos hT0, ← hLdef]
              congr 1
              field_simp
      calc ∑ j ∈ A, zeroAmp (T ^ α) j ≤ ∑ _j ∈ A, T ^ (b * δ) * Real.exp τ :=
            Finset.sum_le_sum hone
        _ = N * (T ^ (b * δ) * Real.exp τ) := by
            rw [Finset.sum_const, nsmul_eq_mul, hN]
    have hΘ : (T ^ α) ^ δ₀ ≤ T ^ (b * δ₀) := by
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      exact mul_le_mul_of_nonneg_right hα.2 hδ₀.le
    have hcross : 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
        ≤ 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
      have hsum0 : 0 ≤ ∑ j ∈ A, zeroAmp (T ^ α) j :=
        Finset.sum_nonneg fun j _ => zeroAmp_nonneg hx0.le j
      have hW0 : 0 ≤ windowLog T := windowLog_nonneg hT0.le
      calc 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
          ≤ 64 * T ^ (b * δ₀) * (3 * L) * (N * (T ^ (b * δ) * Real.exp τ)) := by
            gcongr
        _ = 192 * Real.exp τ * L * N * (T ^ (b * δ₀) * T ^ (b * δ)) := by ring
        _ = 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := by
            rw [← Real.rpow_add hT0, show b * δ₀ + b * δ = b * (δ₀ + δ) by ring]
    have h1 := sub_le_iff_le_add.mp hsplit
    calc (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          + 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j := h1
      _ ≤ T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)) := add_le_add hF hcross
  -- (iii) integrate the pointwise bound
  have hcontF := continuous_montgomeryForm_rpow A hT0
  have hup : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
      ≤ ℓ * (T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
    have this : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
        ≤ ∫ _α in a..b, (T / Real.pi * L + 192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) :=
      intervalIntegral.integral_mono_on hab' (hcontF.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hba : b - a = ℓ := by rw [hb]; ring
    rw [hba] at this
    exact this
  -- (iv) the cross term is dominated by the detection term
  have hgap : 192 * Real.exp τ * L * T ^ (b * (δ₀ + δ)) ≤ Real.exp (-3) * κ * T ^ (2 * a * δ) := by
    have hpow : T ^ (2 * a * δ) = T ^ η * T ^ (b * (δ₀ + δ)) := by
      rw [← Real.rpow_add hT0, hη]; ring_nf
    rw [hpow]
    have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
    have hTb : 0 < T ^ (b * (δ₀ + δ)) := Real.rpow_pos_of_pos hT0 _
    have hlogT : L ≤ ε₁ * T ^ η := by
      have h := e3
      simp only [pow_one] at h
      rwa [div_le_iff₀ hTη] at h
    have : 192 * Real.exp τ * L ≤ Real.exp (-3) * κ * T ^ η := by
      calc 192 * Real.exp τ * L ≤ 192 * Real.exp τ * (ε₁ * T ^ η) := by gcongr
        _ = Real.exp (-3) * κ * T ^ η := by
            rw [hε₁]; field_simp
    calc 192 * Real.exp τ * L * T ^ (b * (δ₀ + δ))
        ≤ Real.exp (-3) * κ * T ^ η * T ^ (b * (δ₀ + δ)) := by gcongr
      _ = _ := by ring
  -- conclude
  have hmain : Real.exp (-3) * κ * T ^ (2 * a * δ) * N ≤ ℓ * (T / Real.pi * L) := by
    have h1 : 2 * Real.exp (-3) * T ^ (2 * a * δ) * κ * N
        ≤ ℓ * (T / Real.pi * L) + ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ))) := by
      linarith only [hlow, hup]
    have h2 : ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
        ≤ Real.exp (-3) * κ * T ^ (2 * a * δ) * N := by
      have hℓ1 : ℓ ≤ 1 := by linarith
      calc ℓ * (192 * Real.exp τ * L * N * T ^ (b * (δ₀ + δ)))
          = ℓ * N * (192 * Real.exp τ * L * T ^ (b * (δ₀ + δ))) := by ring
        _ ≤ 1 * N * (Real.exp (-3) * κ * T ^ (2 * a * δ)) := by
            gcongr
        _ = _ := by ring
    linarith only [h1, h2]
  have hTpow : 0 < T ^ (2 * a * δ) := Real.rpow_pos_of_pos hT0 _
  have hfinal : N ≤ (ℓ * Real.exp 3 / (Real.pi * κ)) * (T / T ^ (2 * a * δ)) * L := by
    have hpos : 0 < Real.exp (-3) * κ * T ^ (2 * a * δ) := by positivity
    rw [show Real.exp (-3) * κ * T ^ (2 * a * δ) * N = N * (Real.exp (-3) * κ * T ^ (2 * a * δ)) by ring,
      ← le_div_iff₀ hpos] at hmain
    refine hmain.trans (le_of_eq ?_)
    rw [Real.exp_neg]
    field_simp
  have hdiv : T / T ^ (2 * a * δ) = T ^ (1 - 2 * a * δ) := by
    rw [Real.rpow_sub hT0, Real.rpow_one]
  rw [hdiv] at hfinal
  exact hfinal

/-- With `ℓ₀ = 1/(2τ)` and separation `D = 100 τ`, the damped band constant is at least
`1/(10τ)` for every `τ > 0`. -/
theorem mvWideBandConstant_hundred {τ : ℝ} (hτ : 0 < τ) :
    1 / (10 * τ) ≤ mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ := by
  unfold mvWideBandConstant
  have hexp : Real.exp (-(2 * τ * (1 / (2 * τ)))) = Real.exp (-1) := by
    congr 1
    field_simp
  rw [hexp]
  have he : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hpi1 := Real.pi_gt_d4
  have hpi2 := Real.pi_lt_d4
  have hpipos := Real.pi_pos
  have hinv : (0.3678794 : ℝ) ≤ (Real.exp 1)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    exact (lt_of_lt_of_le he1 (by norm_num)).le
  rw [he]
  have h1 : 26 / (Real.pi * (100 * τ)) ≤ 26 / (3.1415 * (100 * τ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have h2 : 9 * τ / (Real.pi ^ 2 * (100 * τ) ^ 2) ≤ 9 * τ / (3.1415 ^ 2 * (100 * τ) ^ 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have h3 : 1 / (2 * τ) * (Real.exp 1)⁻¹ ≥ 1 / (2 * τ) * 0.3678794 :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have h4 : 26 / (3.1415 * (100 * τ)) = (26 / 314.15) * (1 / τ) := by
    field_simp
    ring
  have h5 : 9 * τ / (3.1415 ^ 2 * (100 * τ) ^ 2) = (9 / (3.1415 ^ 2 * 10000)) * (1 / τ) := by
    field_simp
    ring
  have h6 : 1 / (2 * τ) * 0.3678794 = (0.3678794 / 2) * (1 / τ) := by
    field_simp
  have h7 : 1 / (10 * τ) = (1 / 10) * (1 / τ) := by
    field_simp
  rw [h4] at h1
  rw [h5] at h2
  rw [h6] at h3
  rw [h7]
  have hτinv : 0 < 1 / τ := by positivity
  have hnum : (1 / 10 : ℝ) ≤ 0.3678794 / 2 - 26 / 314.15 - 9 / (3.1415 ^ 2 * 10000) := by
    norm_num
  nlinarith [mul_le_mul_of_nonneg_right hnum hτinv.le]

/-- **Single-band isolation law, explicit wide instance.**  Window `[3/5, 9/10]`, band width
`τ/log T` with `τ ≥ 5/3`, separation `100 τ` mean gaps: the band has at most
`(3 e³ τ/π) T^{1 − (6/5)(σ−1/2)} log T` elements.  The admissible band width grows linearly
with the separation. -/
theorem eventually_card_singleBand_le_wide_example {σ δ₀ τ : ℝ} (hδ₀ : 0 < δ₀)
    (hσ : 1 / 2 + 4 * δ₀ ≤ σ) (hτ : 5 / 3 ≤ τ) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, σ ≤ (j.1 : ℂ).re ∧ (j.1 : ℂ).re ≤ σ + τ / Real.log T) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → 100 * τ ≤ |bandFreq T j - bandFreq T k|) →
      (A.card : ℝ) ≤ (3 * Real.exp 3 * τ / Real.pi) *
        T ^ (1 - 6 / 5 * (σ - 1 / 2)) * Real.log T := by
  have hτ0 : 0 < τ := by linarith
  have hκ0 : 0 < mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ :=
    lt_of_lt_of_le (by positivity) (mvWideBandConstant_hundred hτ0)
  have hℓ₀ : (1 : ℝ) / (2 * τ) ≤ 3 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h := eventually_card_singleBand_le_wide (a := 3 / 5) (ℓ := 3 / 10) (ℓ₀ := 1 / (2 * τ))
    (σ := σ) (δ₀ := δ₀) (D := 100 * τ) (τ := τ) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ₀ hσ (by positivity) hτ0.le (by positivity) hℓ₀ hκ0
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro A hA hband hR hsep
  have h1 := hT A hA hband hR hsep
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hTpow : 0 < T ^ (1 - 2 * (3 / 5) * (σ - 1 / 2)) := Real.rpow_pos_of_pos (by linarith) _
  have hexp : (1 : ℝ) - 2 * (3 / 5) * (σ - 1 / 2) = 1 - 6 / 5 * (σ - 1 / 2) := by ring
  rw [hexp] at h1 hTpow
  have hconst : 3 / 10 * Real.exp 3 / (Real.pi * mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ)
      ≤ 3 * Real.exp 3 * τ / Real.pi := by
    have hκ := mvWideBandConstant_hundred hτ0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 3 / 10 * Real.exp 3 * Real.pi = (3 * Real.exp 3 * Real.pi) * (1 / 10) := by ring
    rw [this]
    have hτκ : 1 / 10 ≤ τ * mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ := by
      calc (1 : ℝ) / 10 = τ * (1 / (10 * τ)) := by field_simp
        _ ≤ τ * mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ :=
            mul_le_mul_of_nonneg_left hκ hτ0.le
    calc (3 * Real.exp 3 * Real.pi) * (1 / 10)
        ≤ (3 * Real.exp 3 * Real.pi) * (τ * mvWideBandConstant (1 / (2 * τ)) (100 * τ) τ) :=
          mul_le_mul_of_nonneg_left hτκ (by positivity)
      _ = _ := by ring
  calc (A.card : ℝ) ≤ _ := h1
    _ ≤ (3 * Real.exp 3 * τ / Real.pi) * T ^ (1 - 6 / 5 * (σ - 1 / 2)) * Real.log T := by
        gcongr

end

end RHTower
