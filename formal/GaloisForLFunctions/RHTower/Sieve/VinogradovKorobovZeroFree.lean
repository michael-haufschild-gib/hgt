import GaloisForLFunctions.RHTower.Sieve.VinogradovZetaGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaWideDLVP
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv

/-!
# The Vinogradov–Korobov zero-free region

`ζ(β + iγ) ≠ 0` whenever `γ ≥ γ₀` and

`β > 1 - (log γ)^{-2/3} (log log γ)^{-5/3} / 10⁷`

(`riemannZeta_ne_zero_vinogradovKorobov`).

The growth bound `‖ζ(σ+iτ)‖ ≤ C log τ` on `σ ≥ 1 - θ(log τ)`
(`norm_riemannZeta_le_vinogradovKorobov`)
holds on the discs of radius `R₀ = θ(log 5γ)` around `1 + δ + iγ`, `1 + δ + 2iγ` and at
`1 + δ + 4iγ`, with `Φ = C log 5γ + 1`.  The de la Vallée Poussin inequality against a radius and a
growth bound (`dlvp_inequality_of_bound`) with `R = R₀/2`, `ε = R₀/(16000 M)`, `M = log log 5γ`,
`δ = 7ε` gives `1/(14ε) ≤ 3A + 961 M/R₀`,
which fails for `γ` large since `1/(14ε) = (16000/14) M/R₀`.

In mean-spacing units the region has width `(log γ)^{1/3 - o(1)}`.
-/

namespace RHTower.Sieve

open Complex Metric

noncomputable section

/-- `θ` is antitone. -/
theorem vinogradovKorobovWidth_anti {L L' : ℝ} (hL : Real.exp 30 ≤ L) (hLL' : L ≤ L') :
    vinogradovKorobovWidth L' ≤ vinogradovKorobovWidth L := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hl := one_le_log_of_exp_thirty_le hL
  have hlog : Real.log L ≤ Real.log L' := Real.log_le_log hL0 hLL'
  unfold vinogradovKorobovWidth
  have h1 : L' ^ (-(2 : ℝ) / 3) ≤ L ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hL0 hLL' (by norm_num)
  have h2 : Real.log L' ^ (-(2 : ℝ) / 3) ≤ Real.log L ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hlog (by norm_num)
  have h0 : 0 ≤ Real.log L' ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have h0' : 0 ≤ L ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  calc 1 / 100 * L' ^ (-(2 : ℝ) / 3) * Real.log L' ^ (-(2 : ℝ) / 3)
      ≤ 1 / 100 * L ^ (-(2 : ℝ) / 3) * Real.log L' ^ (-(2 : ℝ) / 3) := by gcongr
    _ ≤ 1 / 100 * L ^ (-(2 : ℝ) / 3) * Real.log L ^ (-(2 : ℝ) / 3) := by gcongr

/-- The growth bound on a disc of radius `θ(log 5γ)` around `1 + δ + ih`, `γ ≤ h ≤ 4γ`. -/
theorem norm_riemannZeta_lt_on_disc {γ δ h : ℝ} (hγ : 2 * Real.exp (Real.exp 30) ≤ γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hh1 : γ ≤ h) (hh2 : h ≤ 4 * γ) {w : ℂ}
    (hw : w ∈ ball (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)
      (vinogradovKorobovWidth (Real.log (5 * γ)))) :
    ‖riemannZeta w‖ < vinogradovKorobovGrowthConstant * Real.log (5 * γ) + 1 := by
  set R₀ := vinogradovKorobovWidth (Real.log (5 * γ)) with hR₀
  have hE : (0 : ℝ) < Real.exp (Real.exp 30) := Real.exp_pos _
  have hγ0 : 0 < γ := by linarith
  have hL5 : Real.exp 30 ≤ Real.log (5 * γ) := by
    rw [← Real.log_exp (Real.exp 30)]
    exact Real.log_le_log hE (by linarith)
  have hR₀0 := vinogradovKorobovWidth_pos hL5
  have hR₀1 : R₀ ≤ 1 / 100 := (vinogradovKorobovWidth_le hL5).trans (by norm_num)
  have hd : ‖w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)‖ < R₀ := by
    simpa [dist_eq_norm] using hw
  have hre : |w.re - (1 + δ)| < R₀ := by
    have h1 := Complex.abs_re_le_norm (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I))
    have : (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)).re = w.re - (1 + δ) := by simp
    rw [this] at h1; linarith
  have him : |w.im - h| < R₀ := by
    have h1 := Complex.abs_im_le_norm (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I))
    have : (w - (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I)).im = w.im - h := by simp
    rw [this] at h1; linarith
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  have hE1 : (1 : ℝ) ≤ Real.exp (Real.exp 30) := Real.one_le_exp (Real.exp_pos _).le
  have hτlow : Real.exp (Real.exp 30) ≤ w.im := by
    have := him'.1; linarith [hγ, hR₀1, hh1, hE1]
  have hτup : w.im ≤ 5 * γ := by
    have := him'.2; linarith [hγ, hR₀1, hh2, hE1]
  have hτ0 : 0 < w.im := lt_of_lt_of_le hE hτlow
  have hLτ : Real.exp 30 ≤ Real.log w.im := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log hE hτlow
  have hθ : R₀ ≤ vinogradovKorobovWidth (Real.log w.im) :=
    vinogradovKorobovWidth_anti hLτ (Real.log_le_log hτ0 hτup)
  have hw_eq : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have hgrowth := norm_riemannZeta_le_vinogradovKorobov (τ := w.im) (σ := w.re) hτlow
    (by linarith) (by linarith)
  rw [← hw_eq] at hgrowth
  have hC : 0 ≤ vinogradovKorobovGrowthConstant := by
    unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant; positivity
  have hlog : Real.log w.im ≤ Real.log (5 * γ) := Real.log_le_log hτ0 hτup
  calc ‖riemannZeta w‖ ≤ vinogradovKorobovGrowthConstant * Real.log w.im := hgrowth
    _ ≤ vinogradovKorobovGrowthConstant * Real.log (5 * γ) := mul_le_mul_of_nonneg_left hlog hC
    _ < vinogradovKorobovGrowthConstant * Real.log (5 * γ) + 1 := by linarith

/-- `log(C L + 1) ≤ 2 log L` once `log(C+1) ≤ log L`. -/
theorem vk_log_Phi_le {C L : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L) (hMC : Real.log (C + 1) ≤ Real.log L) :
    Real.log (C * L + 1) ≤ 2 * Real.log L := by
  have hL0 : 0 < L := by linarith
  have h1 : C * L + 1 ≤ (C + 1) * L := by nlinarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul (by linarith) hL0.ne'] at h2
  linarith

/-- `log(1 + 1/δ) ≤ 4 log L` for `δ = 7θ(L)/(16000 log L)`. -/
theorem vk_log_delta_le {L : ℝ} (hL : Real.exp 30 ≤ L)
    (hMK : Real.log 1600001 ≤ Real.log L) :
    Real.log (1 + 1 / (7 * (vinogradovKorobovWidth L / (16000 * Real.log L)))) ≤
      4 * Real.log L := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hM30 := one_le_log_of_exp_thirty_le hL
  set M := Real.log L with hMdef
  have hM0 : 0 < M := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith [Real.add_one_le_exp (30 : ℝ)]
  have hMle : M ≤ L := by rw [hMdef]; have := Real.log_le_sub_one_of_pos hL0; linarith
  have hR₀0 := vinogradovKorobovWidth_pos hL
  have hinvR : 1 / vinogradovKorobovWidth L ≤ 100 * L ^ 2 := by
    unfold vinogradovKorobovWidth
    rw [← hMdef]
    have hL23 : L ^ ((2 : ℝ) / 3) ≤ L := Real.rpow_le_self_of_one_le hL1 (by norm_num)
    have hM23 : M ^ ((2 : ℝ) / 3) ≤ L :=
      (Real.rpow_le_self_of_one_le (by linarith) (by norm_num)).trans hMle
    have hval : 1 / (1 / 100 * L ^ (-(2 : ℝ) / 3) * M ^ (-(2 : ℝ) / 3)) =
        100 * L ^ ((2 : ℝ) / 3) * M ^ ((2 : ℝ) / 3) := by
      rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring, Real.rpow_neg hL0.le, Real.rpow_neg hM0.le]
      field_simp
    rw [hval]
    have h0 : 0 ≤ L ^ ((2 : ℝ) / 3) := by positivity
    calc 100 * L ^ ((2 : ℝ) / 3) * M ^ ((2 : ℝ) / 3) ≤ 100 * L * L := by gcongr
      _ = 100 * L ^ 2 := by ring
  have hinvδ : 1 / (7 * (vinogradovKorobovWidth L / (16000 * M))) ≤ 1600000 * L ^ 3 := by
    have e : 1 / (7 * (vinogradovKorobovWidth L / (16000 * M))) =
        16000 * M / 7 * (1 / vinogradovKorobovWidth L) := by field_simp
    rw [e]
    calc 16000 * M / 7 * (1 / vinogradovKorobovWidth L) ≤ 16000 * M / 7 * (100 * L ^ 2) := by
          gcongr
      _ ≤ 16000 * L / 7 * (100 * L ^ 2) := by gcongr
      _ ≤ 1600000 * L ^ 3 := by nlinarith
  have h1 : 1 + 1 / (7 * (vinogradovKorobovWidth L / (16000 * M))) ≤ 1600001 * L ^ 3 := by
    have : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
    linarith
  have h2 := Real.log_le_log (by
    have : 0 < 1 / (7 * (vinogradovKorobovWidth L / (16000 * M))) := by positivity
    linarith) h1
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, ← hMdef] at h2
  push_cast at h2
  linarith

/-- The final arithmetic of the de la Vallée Poussin step. -/
theorem vk_dlvp_contradiction {β δ ε M R₀ A Xb : ℝ} (hR₀0 : 0 < R₀) (hM24 : 24 ≤ M)
    (hε : ε = R₀ / (16000 * M)) (hδ : δ = 7 * ε) (hA3 : 3 * A ≤ M / R₀)
    (hXb : Xb ≤ 6 * M) (hgap0 : 0 < 1 + δ - β) (hgap8 : 1 + δ - β < 8 * ε)
    (hdlvp : 4 / (1 + δ - β) ≤ 3 / δ + 3 * A + 80 / (R₀ / 2) * Xb) : False := by
  have hM0 : 0 < M := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hLHS : 1 / (2 * ε) < 4 / (1 + δ - β) := by
    have := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 4) hgap0 hgap8
    have e : (4 : ℝ) / (8 * ε) = 1 / (2 * ε) := by field_simp; ring
    linarith
  have hrem : 80 / (R₀ / 2) * Xb ≤ 960 * M / R₀ := by
    calc 80 / (R₀ / 2) * Xb ≤ 80 / (R₀ / 2) * (6 * M) := by
          by_cases hX : 0 ≤ Xb
          · exact mul_le_mul_of_nonneg_left hXb (by positivity)
          · push Not at hX
            have : 80 / (R₀ / 2) * Xb ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hX.le
            have : 0 ≤ 80 / (R₀ / 2) * (6 * M) := by positivity
            linarith
      _ = 960 * M / R₀ := by field_simp; ring
  have hsplit : 1 / (2 * ε) = 3 / δ + 1 / (14 * ε) := by rw [hδ]; field_simp; ring
  have hεval : 1 / (14 * ε) = 16000 * M / (14 * R₀) := by rw [hε]; field_simp
  have hmain : 1 / (14 * ε) < M / R₀ + 960 * M / R₀ := by linarith
  rw [hεval] at hmain
  have : M / R₀ + 960 * M / R₀ < 16000 * M / (14 * R₀) := by
    rw [show M / R₀ + 960 * M / R₀ = 961 * M / R₀ by ring,
      div_lt_div_iff₀ hR₀0 (by positivity)]
    nlinarith
  linarith

/-- The zero-free width `ε(γ) = θ(log 5γ) / (16000 log log 5γ)`. -/
def vinogradovKorobovZeroFreeWidth (γ : ℝ) : ℝ :=
  vinogradovKorobovWidth (Real.log (5 * γ)) / (16000 * Real.log (Real.log (5 * γ)))

/-- **The Vinogradov–Korobov zero-free region**, with the width `ε(γ)`. -/
theorem exists_riemannZeta_ne_zero_vinogradovKorobov_width :
    ∃ γ₀ : ℝ, ∀ β γ : ℝ, γ₀ ≤ γ → 1 - vinogradovKorobovZeroFreeWidth γ < β →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  obtain ⟨C, hCdef⟩ : ∃ C, C = vinogradovKorobovGrowthConstant := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCdef]; unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant; positivity
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = max (max 24 (Real.log (C + 1)))
      (max (Real.log 1600001) (3 * max A 0 + 1)) := ⟨_, rfl⟩
  refine ⟨max (2 * Real.exp (Real.exp 30)) (Real.exp (Real.exp M₀)), ?_⟩
  intro β γ hγ hβ hzero
  have hγ1 : 2 * Real.exp (Real.exp 30) ≤ γ := le_trans (le_max_left _ _) hγ
  have hγ2 : Real.exp (Real.exp M₀) ≤ γ := le_trans (le_max_right _ _) hγ
  have hE : (0 : ℝ) < Real.exp (Real.exp 30) := Real.exp_pos _
  have hγ0 : 0 < γ := by linarith
  have hβ1 : β ≤ 1 := by
    by_contra hb; push Not at hb
    exact riemannZeta_ne_zero_of_one_le_re (s := (β : ℂ) + (γ : ℂ) * Complex.I)
      (by simp; linarith) hzero
  obtain ⟨L5, hL5def⟩ : ∃ L5, L5 = Real.log (5 * γ) := ⟨_, rfl⟩
  have hL5 : Real.exp 30 ≤ L5 := by
    rw [hL5def, ← Real.log_exp (Real.exp 30)]
    exact Real.log_le_log hE (by linarith)
  have hL50 : 0 < L5 := lt_of_lt_of_le (Real.exp_pos _) hL5
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log L5 := ⟨_, rfl⟩
  have hM30 : 30 ≤ M := by rw [hMdef]; exact one_le_log_of_exp_thirty_le hL5
  have hMM₀ : M₀ ≤ M := by
    have h1 : Real.exp (Real.exp M₀) ≤ 5 * γ := by linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp, ← hL5def] at h2
    have h3 := Real.log_le_log (Real.exp_pos _) h2
    rwa [Real.log_exp, ← hMdef] at h3
  have hM24 : 24 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_left (24 : ℝ) (Real.log (C + 1)),
      le_max_left (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMC : Real.log (C + 1) ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_right (24 : ℝ) (Real.log (C + 1)),
      le_max_left (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMK : Real.log 1600001 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_left (Real.log 1600001) (3 * max A 0 + 1),
      le_max_right (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  have hMA : 3 * max A 0 + 1 ≤ M := by
    rw [hM₀] at hMM₀
    linarith [le_max_right (Real.log 1600001) (3 * max A 0 + 1),
      le_max_right (max 24 (Real.log (C + 1))) (max (Real.log 1600001) (3 * max A 0 + 1))]
  obtain ⟨R₀, hR₀⟩ : ∃ R₀, R₀ = vinogradovKorobovWidth L5 := ⟨_, rfl⟩
  have hR₀0 : 0 < R₀ := by rw [hR₀]; exact vinogradovKorobovWidth_pos hL5
  have hR₀1 : R₀ ≤ 1 / 100 := by rw [hR₀]; exact (vinogradovKorobovWidth_le hL5).trans (by norm_num)
  obtain ⟨ε, hε⟩ : ∃ ε, ε = R₀ / (16000 * M) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hβε : 1 - ε < β := by
    have e : vinogradovKorobovZeroFreeWidth γ = ε := by
      rw [hε, hR₀, hMdef, hL5def]; rfl
    rw [e] at hβ; exact hβ
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = 7 * ε := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hεsmall : ε ≤ R₀ / 32 := by
    rw [hε, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ16 : δ ≤ 1 / 16 := by rw [hδ]; linarith
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = C * L5 + 1 := ⟨_, rfl⟩
  have hΦ1 : 1 ≤ Φ := by
    rw [hΦ]; have : 0 ≤ C * L5 := by positivity
    linarith
  have hdisc : ∀ h : ℝ, γ ≤ h → h ≤ 4 * γ →
      ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (h : ℂ) * Complex.I) R₀, ‖riemannZeta w‖ < Φ := by
    intro h hh1 hh2 w hw
    rw [hR₀, hL5def] at hw
    have := norm_riemannZeta_lt_on_disc hγ1 hδ0 (by linarith) hh1 hh2 hw
    rw [hΦ, hCdef, hL5def]; exact this
  have hΦa : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * Complex.I) R₀, ‖riemannZeta w‖ < Φ :=
    hdisc γ le_rfl (by linarith)
  have hΦb : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I) R₀,
      ‖riemannZeta w‖ < Φ := hdisc (2 * γ) (by linarith) (by linarith)
  have hΦc : ‖riemannZeta (((1 + δ : ℝ) : ℂ) + ((4 * γ : ℝ) : ℂ) * Complex.I)‖ ≤ Φ :=
    le_of_lt (hdisc (4 * γ) (by linarith) le_rfl _ (Metric.mem_ball_self hR₀0))
  have hgap0 : 0 < 1 + δ - β := by linarith
  have hgap8 : 1 + δ - β < 8 * ε := by rw [hδ]; linarith
  have hclose : 1 + δ - β ≤ R₀ / 2 / 2 := by linarith
  have hγ3 : (3 : ℝ) ≤ γ := by
    have h1 := Real.add_one_le_exp (Real.exp 30)
    have h2 : (1 : ℝ) ≤ Real.exp 30 := Real.one_le_exp (by norm_num)
    linarith
  have hdlvp := dlvp_inequality_of_bound hA hγ3 hδ0 hδ16 (R := R₀ / 2)
    (R₀ := R₀) (by linarith) (by linarith) (by linarith) hΦa hΦb hΦc hΦ1 hβ1 hclose hzero
  have hlogΦ : Real.log Φ ≤ 2 * M := by
    rw [hΦ, hMdef]
    exact vk_log_Phi_le hC0 (by linarith [Real.add_one_le_exp (30 : ℝ)])
      (by rw [← hMdef]; exact hMC)
  have hlogδ : Real.log (1 + 1 / δ) ≤ 4 * M := by
    rw [hδ, hε, hR₀, hMdef]
    exact vk_log_delta_le hL5 (by rw [← hMdef]; exact hMK)
  have hXb : 5 / 4 * Real.log Φ + 3 / 4 * Real.log (1 + 1 / δ) + 6 ≤ 6 * M := by linarith
  have hA3 : 3 * A ≤ M / R₀ := by
    have h1 : 3 * A ≤ M := by have := le_max_left A 0; linarith
    have h2 : M ≤ M / R₀ := by
      rw [le_div_iff₀ hR₀0]; nlinarith
    linarith
  exact vk_dlvp_contradiction hR₀0 hM24 hε hδ hA3 hXb hgap0 hgap8 hdlvp


/-- `ε(γ) ≥ (log γ)^{-2/3} (log log γ)^{-5/3} / 10⁸` once `log γ ≥ e^{30}`. -/
theorem le_vinogradovKorobovZeroFreeWidth {γ : ℝ} (hγ0 : 0 < γ) (hγ : Real.exp 30 ≤ Real.log γ) :
    Real.log γ ^ (-(2 : ℝ) / 3) * Real.log (Real.log γ) ^ (-(5 : ℝ) / 3) / 10 ^ 8 ≤
      vinogradovKorobovZeroFreeWidth γ := by
  set L := Real.log γ with hLdef
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hγ
  have hγ1 : (1 : ℝ) ≤ γ := by
    by_contra h; push Not at h
    have : Real.log γ ≤ 0 := Real.log_nonpos hγ0.le h.le
    linarith [Real.exp_pos (30 : ℝ)]
  have hM30 := one_le_log_of_exp_thirty_le hγ
  set M := Real.log L with hMdef
  have hM0 : 0 < M := by linarith
  -- `log 5γ ≤ 2L` and `log log 5γ ≤ 2M`
  have hL5 : Real.log (5 * γ) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hγ0.ne']
    have : Real.log 5 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.add_one_le_exp (2 : ℝ)
      have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [h2]; nlinarith
    have : (2 : ℝ) ≤ L := by linarith [Real.add_one_le_exp (30 : ℝ)]
    linarith
  have hL5low : L ≤ Real.log (5 * γ) := Real.log_le_log hγ0 (by linarith)
  have hL5pos : 0 < Real.log (5 * γ) := by linarith
  have hM5 : Real.log (Real.log (5 * γ)) ≤ 2 * M := by
    have h1 := Real.log_le_log hL5pos hL5
    rw [Real.log_mul (by norm_num) hL0.ne'] at h1
    have : Real.log 2 ≤ M := by
      have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    linarith
  have hM5low : M ≤ Real.log (Real.log (5 * γ)) := Real.log_le_log hL0 hL5low
  have hM5pos : 0 < Real.log (Real.log (5 * γ)) := by linarith
  unfold vinogradovKorobovZeroFreeWidth vinogradovKorobovWidth
  set L5 := Real.log (5 * γ)
  set M5 := Real.log L5
  -- rewrite the width as `L5^{-2/3} M5^{-5/3} / 1600000`
  have hval : 1 / 100 * L5 ^ (-(2 : ℝ) / 3) * M5 ^ (-(2 : ℝ) / 3) / (16000 * M5) =
      L5 ^ (-(2 : ℝ) / 3) * M5 ^ (-(5 : ℝ) / 3) / 1600000 := by
    have e : M5 ^ (-(2 : ℝ) / 3) / M5 = M5 ^ (-(5 : ℝ) / 3) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hM5pos]; norm_num
    rw [show 1 / 100 * L5 ^ (-(2 : ℝ) / 3) * M5 ^ (-(2 : ℝ) / 3) / (16000 * M5) =
      L5 ^ (-(2 : ℝ) / 3) * (M5 ^ (-(2 : ℝ) / 3) / M5) / 1600000 by field_simp; ring, e]
  rw [hval]
  have h1 : (2 * L) ^ (-(2 : ℝ) / 3) ≤ L5 ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hL5pos hL5 (by norm_num)
  have h2 : (2 * M) ^ (-(5 : ℝ) / 3) ≤ M5 ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hM5pos hM5 (by norm_num)
  have h3 : L ^ (-(2 : ℝ) / 3) / 2 ≤ (2 * L) ^ (-(2 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) hL0.le]
    have : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring, Real.rpow_neg (by norm_num), one_div]
      apply inv_anti₀ (by positivity)
      have : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [Real.rpow_one] at this
      exact this
    have h0 : 0 ≤ L ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
    nlinarith
  have h4 : M ^ (-(5 : ℝ) / 3) / 4 ≤ (2 * M) ^ (-(5 : ℝ) / 3) := by
    rw [Real.mul_rpow (by norm_num) hM0.le]
    have : (1 : ℝ) / 4 ≤ (2 : ℝ) ^ (-(5 : ℝ) / 3) := by
      rw [show -(5 : ℝ) / 3 = -((5 : ℝ) / 3) by ring, Real.rpow_neg (by norm_num)]
      rw [one_div]
      apply inv_anti₀ (by positivity)
      have : (2 : ℝ) ^ ((5 : ℝ) / 3) ≤ 2 ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
      exact this
    have h0 : 0 ≤ M ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg hM0.le _
    nlinarith
  have hA0 : 0 ≤ L ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg hL0.le _
  have hB0 : 0 ≤ M ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg hM0.le _
  calc L ^ (-(2 : ℝ) / 3) * M ^ (-(5 : ℝ) / 3) / 10 ^ 8
      ≤ (L ^ (-(2 : ℝ) / 3) / 2) * (M ^ (-(5 : ℝ) / 3) / 4) / 1600000 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith [mul_nonneg hA0 hB0]
    _ ≤ L5 ^ (-(2 : ℝ) / 3) * M5 ^ (-(5 : ℝ) / 3) / 1600000 := by
        gcongr
        · exact h3.trans h1
        · exact h4.trans h2

/-- **The Vinogradov–Korobov zero-free region.**
`ζ(β + iγ) ≠ 0` for `γ ≥ γ₀` and `β > 1 - (log γ)^{-2/3}(log log γ)^{-5/3}/10⁸`. -/
theorem riemannZeta_ne_zero_vinogradovKorobov :
    ∃ γ₀ : ℝ, ∀ β γ : ℝ, γ₀ ≤ γ →
      1 - Real.log γ ^ (-(2 : ℝ) / 3) * Real.log (Real.log γ) ^ (-(5 : ℝ) / 3) / 10 ^ 8 < β →
      riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨γ₀, hγ₀⟩ := exists_riemannZeta_ne_zero_vinogradovKorobov_width
  refine ⟨max γ₀ (Real.exp (Real.exp 30)), fun β γ hγ hβ => ?_⟩
  have hγ1 : γ₀ ≤ γ := le_trans (le_max_left _ _) hγ
  have hγ2 : Real.exp (Real.exp 30) ≤ γ := le_trans (le_max_right _ _) hγ
  have hL : Real.exp 30 ≤ Real.log γ := by
    rw [← Real.log_exp (Real.exp 30)]; exact Real.log_le_log (Real.exp_pos _) hγ2
  have hγ0 : 0 < γ := lt_of_lt_of_le (Real.exp_pos _) hγ2
  exact hγ₀ β γ hγ1 (by linarith [le_vinogradovKorobovZeroFreeWidth hγ0 hL])

end

end RHTower.Sieve
