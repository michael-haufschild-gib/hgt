import GaloisForLFunctions.RHTower.ZetaFrobeniusSurplusSplit
import GaloisForLFunctions.RHTower.FamilyMuMuWide
import GaloisForLFunctions.RHTower.FamilyCrossWide
import GaloisForLFunctions.RHTower.ThmEUniformTraceSquare

/-!
# Three quarters on the line from the surplus of the prime pairs

At bandwidth `λ = 4/3` the Frobenius norm of the Gram matrix of `ζ` splits as the diagonal and
archimedean part plus the surplus `𝒮` (`ZetaFrobeniusSurplusSplit`).  Every term outside `𝒮` is evaluated
unconditionally (`diagonal_part_le`):

`𝓜[μ,μ] + (1/2π²)𝒟 + 2𝓜[μ,P_X] + 2𝓜[μ,Π_X] + 𝓜[Π_X,Π_X] ≤ (TL/2π)(ℓ₁² + L²/3) + O(T l² + T^{2/3} log²T)`,

and `(TL/2π)(ℓ₁² + L²/3)` is `43/36` of the normalisation `(aL)²Tℓ₁/2π` up to `o(1)`
(`diagonal_main_le`).  Since `43/36 + 1/18 = 5/4`, the hypothesis that the surplus is at most `1/18` of
the normalisation (`SurplusFourThirds`) gives the bandwidth-`4/3` Frobenius inequality
(`frobeniusFourThirds_of_surplus`), hence three quarters of the zeros simple and on the line
(`zeta_three_quarters_of_surplus`, `zeta_three_quarters_simple_of_surplus`).

The surplus consists of the off-diagonal prime pairs `Σ_{n≠m≤X} a_n a_m A⁻(log n, log m)`, the sum
frequencies, the prime–pole cross term and the end correction of the grid; the random-matrix prediction for it
is `−1/144` of the normalisation, so the hypothesis leaves a margin of `1/16`.
-/

open MeasureTheory Real Filter Topology Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace RHTower

/-- **The main term is `43/36` of the normalisation, up to `ε`.**  With `ℓ₁ = l + c₀`, `0 ≤ c₀ ≤ 1`,
`L = 4l/3`, `1 − 2/L ≤ a` and `l ≥ 14/ε`. -/
theorem diagonal_main_le {ε l c₀ a T : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 14 / ε ≤ l) (hl1 : 1 ≤ l)
    (hc₀ : 0 ≤ c₀) (hc₁ : c₀ ≤ 1) (ha : 1 - 2 / (4 / 3 * l) ≤ a) (hT : 0 < T) :
    T * (4 / 3 * l) / (2 * π) * ((l + c₀) ^ 2 + (4 / 3 * l) ^ 2 / 3)
      ≤ (43 / 36 + ε / 2) * (a * (4 / 3 * l)) ^ 2 * (T * (l + c₀) / (2 * π)) := by
  set L := 4 / 3 * l with hL
  set e := l + c₀ with he
  have hL1 : 4 / 3 ≤ L := by rw [hL]; linarith only [hl1]
  have hLpos : 0 < L := by linarith only [hL1]
  have he1 : 1 ≤ e := by rw [he]; linarith only [hl1, hc₀]
  -- `ℓ₁² + L²/3 = (43/36) L ℓ₁ + (11/27) c₀ l + c₀²`
  have hid : e ^ 2 + L ^ 2 / 3 = 43 / 36 * L * e + 11 / 27 * c₀ * l + c₀ ^ 2 := by
    rw [hL, he]; ring
  -- `a² ≥ 1 − 4/L`
  have ha0 : 0 ≤ 1 - 2 / L := by
    rw [sub_nonneg, div_le_one hLpos]
    have : 14 ≤ l := by
      have : 14 ≤ 14 / ε := by rw [le_div_iff₀ hε]; linarith only [hε1]
      linarith only [this, hl]
    rw [hL]; linarith only [this]
  have ha2 : 1 - 4 / L ≤ a ^ 2 := by
    have h1 : (1 - 2 / L) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ ha0 ha 2
    have h2 : 1 - 4 / L ≤ (1 - 2 / L) ^ 2 := by
      have e : (1 - 2 / L) ^ 2 = 1 - 4 / L + (2 / L) ^ 2 := by ring
      linarith only [e, sq_nonneg (2 / L)]
    linarith only [h1, h2]
  -- the key inequality `ℓ₁² + L²/3 ≤ (43/36 + ε/2) a² L ℓ₁`
  have hLε : 18 / ε ≤ L := by
    rw [hL]
    have : 18 / ε ≤ 4 / 3 * (14 / ε) := by
      rw [show 4 / 3 * (14 / ε) = (56 / 3) / ε by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hε.le
    linarith only [this, hl]
  have hkey : e ^ 2 + L ^ 2 / 3 ≤ (43 / 36 + ε / 2) * a ^ 2 * L * e := by
    have hcoef : 0 ≤ (43 / 36 + ε / 2) * L * e := by positivity
    have h1 : (43 / 36 + ε / 2) * (1 - 4 / L) * L * e ≤ (43 / 36 + ε / 2) * a ^ 2 * L * e := by
      have := mul_le_mul_of_nonneg_right ha2 hcoef
      nlinarith only [this]
    have h2 : (43 / 36 + ε / 2) * (1 - 4 / L) * L * e
        = (43 / 36) * L * e + ε / 2 * L * e - (43 / 36 + ε / 2) * 4 * e := by
      field_simp
    have h3 : 11 / 27 * c₀ * l + c₀ ^ 2 + (43 / 36 + ε / 2) * 4 * e ≤ ε / 2 * L * e := by
      have hle : l ≤ e := by rw [he]; linarith only [hc₀]
      have hA : 11 / 27 * c₀ * l ≤ e := by nlinarith only [hc₀, hc₁, hle, hl1]
      have hB : c₀ ^ 2 ≤ e := by nlinarith only [hc₀, hc₁, he1]
      have hC : (43 / 36 + ε / 2) * 4 * e ≤ 7 * e := by nlinarith only [hε1, he1]
      have hD : 9 * e ≤ ε / 2 * L * e := by
        have : 18 ≤ ε * L := by rw [div_le_iff₀ hε] at hLε; linarith only [hLε]
        nlinarith only [this, he1]
      linarith only [hA, hB, hC, hD]
    linarith only [hid, h1, h2, h3]
  -- scale by `T L / 2π`
  have hTL : 0 ≤ T / (2 * π) := by positivity
  have e1 : T * L / (2 * π) * (e ^ 2 + L ^ 2 / 3) = T / (2 * π) * ((e ^ 2 + L ^ 2 / 3) * L) := by ring
  have e2 : (43 / 36 + ε / 2) * (a * L) ^ 2 * (T * e / (2 * π))
      = T / (2 * π) * ((43 / 36 + ε / 2) * a ^ 2 * L * e * L) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey hLpos.le) hTL

/-- `sumA2g X g ≤ L³/6 + C L²` at every bandwidth: `g(y) ≤ (L − y)₊` and Chebyshev–Mertens. -/
theorem sumA2g_le_wide {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log x - Real.log n)
      - Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2)
    {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHypsCoreW cϱ p F) (hX : 2 ≤ p.X) :
    sumA2g p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2 := by
  have hlogX : Real.log p.X = p.L := Real.log_exp _
  have h1 : sumA2g p.X F.g
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 / n * (Real.log p.X - Real.log n) := by
    unfold sumA2g primeRange
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : (1:ℝ) ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast this
    have hnX : (n : ℝ) ≤ p.X := by
      have h := (Finset.mem_Ioc.mp hn).2
      exact (Nat.cast_le.mpr h).trans (Nat.floor_le (by linarith only [hX]))
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlogn : Real.log n ≤ p.L := by
      rw [← hlogX]; exact Real.log_le_log (by linarith only [hn1]) hnX
    have hg : F.g (Real.log n) ≤ p.L - Real.log n := by
      have h := (hF.g_le_Aphi (Real.log n)).trans (hF.Aphi_le (Real.log n))
      rw [abs_of_nonneg hlog0, max_eq_left (by linarith only [hlogn])] at h
      exact h
    rw [hlogX]
    exact mul_le_mul_of_nonneg_left hg (by positivity)
  have h2 := (abs_le.mp (hC p.X hX)).2
  rw [hlogX] at h2 h1
  linarith only [h1, h2]

/-- `Σ_{n ≤ X} a_n² ≤ L²/2 + C L`. -/
theorem sum_acoef_sq_le_wide {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℝ) ^ 2 / n - Real.log x ^ 2 / 2|
      ≤ C * Real.log x) {X L : ℝ} (hXL : Real.log X = L) (hX : 2 ≤ X) :
    ∑ n ∈ primeRange X, acoef n ^ 2 ≤ L ^ 2 / 2 + C * L := by
  have h := (abs_le.mp (hC X hX)).2
  have e : ∑ n ∈ primeRange X, acoef n ^ 2 = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (Λ n : ℝ) ^ 2 / n := by
    unfold primeRange; exact Finset.sum_congr rfl fun n _ => acoef_sq n
  rw [e]; rw [hXL] at h; linarith only [h]

/-- **The diagonal and archimedean part of the bandwidth-`4/3` Frobenius norm, unconditionally.** -/
theorem diagonal_part_le :
    ∃ K K' T₀ : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧ ∀ T, T₀ ≤ T →
      LocalHypsCoreW params43.crho (params43.toSetting T) (params43.localFun T) ∧
      Mform (params43.PhiR T) T Zeta23.mu Zeta23.mu
        + (1 / (2 * π ^ 2)) * ppDiag (params43.PhiR T) T (params43.X T)
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PX (params43.X T))
        + 2 * Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PiX (params43.X T))
        + Mform (params43.PhiR T) T (Zeta23.PiX (params43.X T)) (Zeta23.PiX (params43.X T))
      ≤ T * params43.L T / (2 * π) * (ell1 T ^ 2 + params43.L T ^ 2 / 3)
        + K * (T * Zeta23.l T ^ 2) + K' * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) := by
  have hP := paramsValidFam_params43
  have hΓ : GammaFacts := paperInputs_zeta.Gamma
  have hcheb : ChebyshevMertens := paperInputs_zeta.cheb
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨Cm, Tm, hCm, hm⟩ := prop_mumu_uniform_wide params43.crho (4 / 3)
  obtain ⟨CΓ, TΓ, hΓsq⟩ := hΓ.int_mu_sq
  obtain ⟨Cx, Tx, hCx, hx⟩ := prop_cross_uniform_wide params43.crho (by norm_num : (0:ℝ) < 4 / 3)
  obtain ⟨Tμ, hμ⟩ := mu_abs_le_l hΓ
  obtain ⟨C₁, hC₁⟩ := hcheb.cheb2a
  obtain ⟨C₂, hC₂⟩ := hcheb.cheb2b
  set cr := params43.crho with hcr
  obtain ⟨Tl, hTlb⟩ := Filter.eventually_atTop.mp eventually_l_bounds
  have hcr4 : 4 ≤ cr := (hTL (max TL 0) (le_max_left _ _)).four_le_cϱ
  set K : ℝ := 8 * |CΓ| / (3 * π) + 4 / 3 * Cm + 16 / 9 * (|C₂| / π)
    + 64 / 27 * (1 / (2 * π ^ 2) * ((1 / 2 + |C₁|) * (8 + 2 * cr))) with hK
  set K' : ℝ := 2 * Cx + 16 * π + 24 * π with hK'
  have hK0 : 0 ≤ K := by rw [hK]; have := Real.pi_pos; positivity
  have hK'0 : 0 ≤ K' := by rw [hK']; have := Real.pi_pos; positivity
  refine ⟨K, K', max (max (max TL Tm) (max TΓ Tx)) (max (max Tμ Tl) (2 * π * Real.exp 2)),
    hK0, hK'0, fun T hT => ?_⟩
  have hT1 := (le_max_left _ _).trans hT
  have hT2 := (le_max_right _ _).trans hT
  have hTLT : TL ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT1)
  have hTm : Tm ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT1)
  have hTΓ : TΓ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT1)
  have hTx : Tx ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT1)
  have hTμ : Tμ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT2)
  have hTl : Tl ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT2)
  have hTe : 2 * π * Real.exp 2 ≤ T := (le_max_right _ _).trans hT2
  have hF := hTL T hTLT
  refine ⟨hF, ?_⟩
  obtain ⟨hlog1, hl1, hlo, hhi⟩ := hTlb T hTl
  have hπ := Real.pi_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hTe
  -- notation
  set p := params43.toSetting T with hp
  set F := params43.localFun T with hFdef
  set l := Zeta23.l T with hldef
  set L := params43.L T with hLdef
  set X := params43.X T with hXdef
  have hLl : L = 4 / 3 * l := rfl
  have hXL : X = Real.exp L := rfl
  have hpT : p.T = T := rfl
  have hpL : p.L = L := rfl
  have hpX : p.X = X := rfl
  have hpl : p.l = l := rfl
  have hFPhi : F.Phi = params43.PhiR T := rfl
  have hl2 : 2 ≤ l := by
    have : Real.exp 2 ≤ T / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith only [hTe]
    rw [hldef]; unfold Zeta23.l
    have h := Real.log_le_log (Real.exp_pos 2) this
    rwa [Real.log_exp] at h
  have hL0 : 0 < L := by rw [hLl]; linarith only [hl2]
  have hL1 : 1 ≤ L := by rw [hLl]; linarith only [hl2]
  have hX2 : 2 ≤ X := by
    rw [hXL]
    have : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith only [this]
    exact this.trans (Real.exp_le_exp.mpr hL1)
  have hlogXL : Real.log X = L := by rw [hXL, Real.log_exp]
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hc₁ : 2 * Real.log 2 - 1 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
  have hell : ell1 T = l + (2 * Real.log 2 - 1) := by unfold ell1; rw [hldef]; ring
  have hsX : Real.sqrt X ≤ T ^ (2 / 3 : ℝ) := by
    have h := sqrt_exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 hhi
    rw [show (4 / 3 : ℝ) / 2 = 2 / 3 by norm_num] at h
    exact h
  have hXT : X ≤ T ^ (4 / 3 : ℝ) := exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 hhi
  have hlT : l ≤ T := by
    have := Real.log_le_sub_one_of_pos hT0; linarith only [this, hhi]
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hIΦ : ∫ x, F.Phi x ^ 2 ≤ 2 * π * L := hF.integral_Phi_sq_le
  -- (i) the archimedean diagonal
  have hmm := (abs_le.mp (hm 0 1 (by norm_num) le_rfl p F rfl hTm hF)).2
  rw [← mu_eq_muq, Nat.cast_one, Real.log_one, add_zero, one_pow, mul_one] at hmm
  have hint := (abs_le.mp (hΓsq T hTΓ)).2
  have hI0 : 0 ≤ ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith only [hT0]) fun τ _ => sq_nonneg _
  have hmumu := mumu_main_le (Mf := Mform F.Phi p.T Zeta23.mu Zeta23.mu) (b := F.b) (L := L)
    (I := ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) (M₀ := T * ell1 T ^ 2 / (4 * π ^ 2)) (Cg := CΓ)
    (l2 := l ^ 2) (Cm := Cm) (SE := l ^ 2 * Real.log L) (T := T) (ell := ell1 T ^ 2)
    (hF.b_le_a.trans hF.a_le_one) hL0.le hI0 rfl (by positivity)
    (by have e : CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / l ^ 2
            = CΓ * (T * ell1 T ^ 2 / (4 * π ^ 2)) / Zeta23.l T ^ 2 := rfl
        linarith only [hint, e]) (by positivity) hmm
  -- (ii) the prime diagonal
  have hdiag := (abs_le.mp (diag_estimate (Φ := F.Phi) (T := T) hT0.le hΦ hF.Phi_sq_integrable
    hF.Phi_sq_mul_abs_integrable hF.Phi_sq_fourier X)).2
  have hsum := sumA2g_le_wide hC₂ hF hX2
  have hsq := sum_acoef_sq_le_wide hC₁ hlogXL hX2
  have hsq0 : 0 ≤ ∑ n ∈ primeRange X, acoef n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hIabs := hF.integral_Phi_sq_mul_abs_le
  have hIabs0 : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hw : p.w = 1 := rfl
  rw [hpL, hw, mul_one] at hIabs
  have hlogc : Real.log (cr * L / 4) ≤ cr * L / 4 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < cr * L / 4)
    linarith only [h]
  have hdiag' : (1 / (2 * π ^ 2)) * ppDiag F.Phi T X
      ≤ T / π * (L ^ 3 / 6 + C₂ * L ^ 2)
        + 1 / (2 * π ^ 2) * ((L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L)) := by
    have h1 : (1 / (2 * π ^ 2)) * ppDiag F.Phi T X
        ≤ T / π * sumA2g X F.g
          + (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x| := by
      unfold ppDiag; linarith only [hdiag]
    have h2 : T / π * sumA2g X F.g ≤ T / π * (L ^ 3 / 6 + C₂ * L ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have h3 : ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 2 * cr * L := by linarith only [hIabs, hlogc]
    have h4 : (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|
        ≤ (L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L) :=
      mul_le_mul hsq h3 hIabs0 (hsq0.trans hsq)
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0:ℝ) ≤ 1 / (2 * π ^ 2))
    rw [← mul_assoc] at h5
    linarith only [h1, h2, h5]
  -- (iii) the archimedean–prime cross term
  have hPX : PXc (fun _ => 1) p.X = Zeta23.PX X := funext fun τ => (PX_eq_PXc_one X τ).symm
  have hcross := hx 0 1 (by norm_num) le_rfl (fun _ => 1) coeffOK_one p F rfl hTx hF
  rw [← mu_eq_muq, hPX, Nat.cast_one, Real.log_one, add_zero, mul_one] at hcross
  -- pointwise bounds on the window
  have hμI : ∀ τ ∈ Set.Icc T (2 * T), |Zeta23.mu τ| ≤ l := fun τ hτ => hμ p hTμ τ hτ
  have hPiI : ∀ τ ∈ Set.Icc T (2 * T), |Zeta23.PiX X τ| ≤ 3 * Real.sqrt X / T := by
    intro τ hτ
    refine (hF.PiX_bound τ).trans ?_
    apply div_le_div_of_nonneg_left (by positivity) hT0
    rw [abs_of_nonneg (by linarith only [hτ.1, hT0])]; linarith only [hτ.1]
  -- (iv) archimedean–pole, (v) pole–pole
  have hmuPi := abs_Mform_le hT0.le hΦ hΓ.smooth.continuous hF.PiX_cont hF.Phi_sq_integrable hμI hPiI
  have hPiPi := abs_Mform_le hT0.le hΦ hF.PiX_cont hF.PiX_cont hF.Phi_sq_integrable hPiI hPiI
  have hsX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg _
  have hmuPi' : |Mform F.Phi T Zeta23.mu (Zeta23.PiX X)| ≤ 6 * π * (l * L * Real.sqrt X) := by
    refine hmuPi.trans ?_
    have hc : 0 ≤ l * (3 * Real.sqrt X / T) := by positivity
    calc l * (3 * Real.sqrt X / T) * (T * ∫ x, F.Phi x ^ 2)
        ≤ l * (3 * Real.sqrt X / T) * (T * (2 * π * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIΦ hT0.le) hc
      _ = 6 * π * (l * L * Real.sqrt X) := by field_simp; ring
  have hPiPi' : |Mform F.Phi T (Zeta23.PiX X) (Zeta23.PiX X)| ≤ 18 * π * (L * X / T) := by
    refine hPiPi.trans ?_
    have hc : 0 ≤ 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) := by positivity
    calc 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) * (T * ∫ x, F.Phi x ^ 2)
        ≤ 3 * Real.sqrt X / T * (3 * Real.sqrt X / T) * (T * (2 * π * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIΦ hT0.le) hc
      _ = 18 * π * (L * Real.sqrt X ^ 2 / T) := by field_simp; ring
      _ = 18 * π * (L * X / T) := by rw [Real.sq_sqrt (by linarith only [hX2])]
  -- the error terms
  have hell2 : ell1 T ≤ 2 * l := by rw [hell]; linarith only [hc₁, hl2]
  have hell0 : 0 ≤ ell1 T := by rw [hell]; linarith only [hc₀, hl2]
  have hE1 : |CΓ| / (2 * π) * (T * L * ell1 T ^ 2 / l ^ 2) ≤ 8 * |CΓ| / (3 * π) * (T * l ^ 2) := by
    have hl0 : 0 < l := by linarith only [hl2]
    have h1 : ell1 T ^ 2 ≤ 4 * l ^ 2 := by nlinarith only [hell2, hell0]
    have h2 : T * L * ell1 T ^ 2 / l ^ 2 ≤ T * L * 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ T * L)
      have e : T * L * (4 * l ^ 2) = T * L * 4 * l ^ 2 := by ring
      linarith only [this, e]
    have h3 : T * L * 4 ≤ 16 / 3 * (T * l ^ 2) := by
      have a : T * l ≤ T * l ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith only [hl2]) hT0.le
      have e1 : T * L * 4 = 16 / 3 * (T * l) := by rw [hLl]; ring
      linarith only [a, e1]
    have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity : (0:ℝ) ≤ |CΓ| / (2 * π))
    have e : |CΓ| / (2 * π) * (16 / 3 * (T * l ^ 2)) = 8 * |CΓ| / (3 * π) * (T * l ^ 2) := by
      field_simp; ring
    linarith only [h4, e]
  have hE2 : Cm * (l ^ 2 * Real.log L) ≤ 4 / 3 * Cm * (T * l ^ 2) := by
    have h1 : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith only [this]
    have h2 : l ^ 2 * Real.log L ≤ 4 / 3 * (T * l ^ 2) := by
      have h3 : l ^ 2 * Real.log L ≤ l ^ 2 * L := mul_le_mul_of_nonneg_left h1 (sq_nonneg l)
      have e : l ^ 2 * L = 4 / 3 * (l * l ^ 2) := by rw [hLl]; ring
      have a : l * l ^ 2 ≤ T * l ^ 2 := mul_le_mul_of_nonneg_right hlT (sq_nonneg l)
      linarith only [h3, e, a]
    have := mul_le_mul_of_nonneg_left h2 hCm
    have e : Cm * (4 / 3 * (T * l ^ 2)) = 4 / 3 * Cm * (T * l ^ 2) := by ring
    linarith only [this, e]
  have hE3 : T / π * (C₂ * L ^ 2) ≤ 16 / 9 * (|C₂| / π) * (T * l ^ 2) := by
    have h1 : C₂ * L ^ 2 ≤ |C₂| * L ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ T / π)
    have e : T / π * (|C₂| * L ^ 2) = 16 / 9 * (|C₂| / π) * (T * l ^ 2) := by
      rw [hLl]; field_simp; ring
    linarith only [h2, e]
  have hE4 : 1 / (2 * π ^ 2) * ((L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L))
      ≤ 64 / 27 * (1 / (2 * π ^ 2) * ((1 / 2 + |C₁|) * (8 + 2 * cr))) * (T * l ^ 2) := by
    have h1 : L ^ 2 / 2 + C₁ * L ≤ (1 / 2 + |C₁|) * L ^ 2 := by
      have : C₁ * L ≤ |C₁| * L ^ 2 := by
        have a1 : C₁ * L ≤ |C₁| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL0.le
        have a2 : |C₁| * L ≤ |C₁| * L ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith only [hL1]
        linarith only [a1, a2]
      linarith only [this]
    have h2 : 8 + 2 * cr * L ≤ (8 + 2 * cr) * L := by nlinarith only [hL1, hcr4]
    have h0 : 0 ≤ 8 + 2 * cr * L := by nlinarith only [hL1, hcr4]
    have h3 : (L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L) ≤ ((1 / 2 + |C₁|) * (8 + 2 * cr)) * L ^ 3 := by
      have := mul_le_mul h1 h2 h0 (by positivity)
      nlinarith only [this]
    have h4 : L ^ 3 ≤ 64 / 27 * (T * l ^ 2) := by
      rw [hLl]; nlinarith only [hlT, hl2, sq_nonneg l]
    have h5 : ((1 / 2 + |C₁|) * (8 + 2 * cr)) * L ^ 3
        ≤ ((1 / 2 + |C₁|) * (8 + 2 * cr)) * (64 / 27 * (T * l ^ 2)) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 := mul_le_mul_of_nonneg_left (h3.trans h5) (by positivity : (0:ℝ) ≤ 1 / (2 * π ^ 2))
    nlinarith only [h6]
  have hlogT : l ≤ Real.log T := hhi
  have hTone : 1 ≤ T := by
    have h1 := Real.add_one_le_exp (2:ℝ)
    have h2 : 2 * π * Real.exp 2 ≥ 1 := by nlinarith only [h1, Real.pi_gt_three]
    linarith only [h2, hTe]
  have hE5 : 2 * (Cx * (l * Real.sqrt X)) ≤ 2 * Cx * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) := by
    have h1 : l * Real.sqrt X ≤ Real.log T ^ 2 * T ^ (2 / 3 : ℝ) := by
      have a1 : l * Real.sqrt X ≤ Real.log T * T ^ (2 / 3 : ℝ) :=
        mul_le_mul hlogT hsX hsX0 (by linarith only [hlog1])
      have a2 : Real.log T * T ^ (2 / 3 : ℝ) ≤ Real.log T ^ 2 * T ^ (2 / 3 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith only [hlog1]
      linarith only [a1, a2]
    have := mul_le_mul_of_nonneg_left h1 hCx
    linarith only [this]
  have hE6 : 2 * (6 * π * (l * L * Real.sqrt X)) ≤ 16 * π * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) := by
    have h1 : l * L ≤ 4 / 3 * Real.log T ^ 2 := by
      rw [hLl]; nlinarith only [hlogT, hl2]
    have h2 : l * L * Real.sqrt X ≤ 4 / 3 * Real.log T ^ 2 * T ^ (2 / 3 : ℝ) :=
      mul_le_mul h1 hsX hsX0 (by positivity)
    nlinarith only [h2, hπ]
  have hE7 : 18 * π * (L * X / T) ≤ 24 * π * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) := by
    have h1 : L * X / T ≤ 4 / 3 * Real.log T * T ^ (1 / 3 : ℝ) := by
      rw [div_le_iff₀ hT0]
      have a1 : L * X ≤ 4 / 3 * Real.log T * T ^ (4 / 3 : ℝ) := by
        rw [hLl]
        exact mul_le_mul (by linarith only [hlogT]) hXT (by positivity) (by linarith only [hlog1])
      have a2 : T ^ (4 / 3 : ℝ) = T ^ (1 / 3 : ℝ) * T := by
        rw [← Real.rpow_add_one hT0.ne']; norm_num
      rw [a2] at a1; linarith only [a1]
    have h2 : Real.log T * T ^ (1 / 3 : ℝ) ≤ Real.log T ^ 2 * T ^ (2 / 3 : ℝ) := by
      have b1 : T ^ (1 / 3 : ℝ) ≤ T ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by norm_num)
      have b2 : Real.log T ≤ Real.log T ^ 2 := by nlinarith only [hlog1]
      exact mul_le_mul b2 b1 (by positivity) (by positivity)
    nlinarith only [h1, h2, hπ]
  -- assemble
  have hmain : T * L / (2 * π) * ell1 T ^ 2 + T / π * (L ^ 3 / 6)
      = T * L / (2 * π) * (ell1 T ^ 2 + L ^ 2 / 3) := by field_simp; ring
  have hcr' : Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PX X) ≤ Cx * (l * Real.sqrt X) :=
    (abs_le.mp hcross).2
  have hmuPi'' : Mform (params43.PhiR T) T Zeta23.mu (Zeta23.PiX X) ≤ 6 * π * (l * L * Real.sqrt X) :=
    (abs_le.mp hmuPi').2
  have hPiPi'' : Mform (params43.PhiR T) T (Zeta23.PiX X) (Zeta23.PiX X) ≤ 18 * π * (L * X / T) :=
    (abs_le.mp hPiPi').2
  have hmumu' : Mform (params43.PhiR T) T Zeta23.mu Zeta23.mu
      ≤ T * L / (2 * π) * ell1 T ^ 2 + |CΓ| / (2 * π) * (T * L * ell1 T ^ 2 / l ^ 2)
        + Cm * (l ^ 2 * Real.log L) := hmumu
  have hdiag'' : (1 / (2 * π ^ 2)) * ppDiag (params43.PhiR T) T X
      ≤ T / π * (L ^ 3 / 6 + C₂ * L ^ 2)
        + 1 / (2 * π ^ 2) * ((L ^ 2 / 2 + C₁ * L) * (8 + 2 * cr * L)) := hdiag'
  have e3 : T / π * (L ^ 3 / 6 + C₂ * L ^ 2) = T / π * (L ^ 3 / 6) + T / π * (C₂ * L ^ 2) := by ring
  have eK : K * (T * l ^ 2) = 8 * |CΓ| / (3 * π) * (T * l ^ 2) + 4 / 3 * Cm * (T * l ^ 2)
      + 16 / 9 * (|C₂| / π) * (T * l ^ 2)
      + 64 / 27 * (1 / (2 * π ^ 2) * ((1 / 2 + |C₁|) * (8 + 2 * cr))) * (T * l ^ 2) := by
    rw [hK]; ring
  have eK' : K' * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ))
      = 2 * Cx * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) + 16 * π * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ))
        + 24 * π * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) := by
    rw [hK']; ring
  linarith only [hmumu', hdiag'', hcr', hmuPi'', hPiPi'', hE1, hE2, hE3, hE4, hE5, hE6, hE7, hmain,
    e3, eK, eK']

/-- **The surplus hypothesis at bandwidth `4/3`**: the off-diagonal prime pairs, sum frequencies,
prime–pole cross term and end correction of the bandwidth-`4/3` Gram matrix of `ζ` amount to at most
`1/18 + ε` of the normalisation `(aL)² Tℓ₁/2π`, for all large `T`. -/
def SurplusFourThirds : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop,
    frobSurplus (params43.toSetting T) (params43.localFun T)
      ≤ (1 / 18 + ε) * (params43.a T * params43.L T) ^ 2 * (T * ell1 T / (2 * π))

/-- `1 − 2w/L ≤ a` for the bandwidth-`4/3` taper. -/
theorem one_sub_le_a_params43 {T : ℝ} (hwL : 8 * params43.w ≤ params43.L T) :
    1 - 2 * params43.w / params43.L T ≤ params43.a T := by
  have hP := paramsValidFam_params43
  have hb := Taper.bConst_le_aConst hP.taper hP.w_pos (hP.two_w_le hwL)
  have h1 := Taper.one_sub_le_bConst hP.taper hP.w_pos (hP.two_w_le hwL)
  rw [Params.a_eq]
  linarith only [hb, h1]

/-- **The surplus hypothesis gives the bandwidth-`4/3` Frobenius inequality.** -/
theorem frobeniusFourThirds_of_surplus (h : SurplusFourThirds) : FrobeniusFourThirds := by
  intro ε hε
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  obtain ⟨K, K', T₀, hK, hK', hdp⟩ := diagonal_part_le
  have hΓ : GammaFacts := paperInputs_zeta.Gamma
  have hπ := Real.pi_pos
  have h2π : (0:ℝ) < 2 * π := by positivity
  have hl := Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const h2π)
  have hε4 : (0:ℝ) < ε' / 4 := by positivity
  have hc : (0:ℝ) < ε' / (18 * π) := by positivity
  have hs : (2:ℝ) / 3 < 1 := by norm_num
  filter_upwards [h (ε' / 4) hε4, eventually_ge_atTop T₀, eventually_l_bounds,
    hl.eventually_ge_atTop (28 / ε' + 18 * π * K / ε' + 14),
    eventually_log_pow_rpow_le 2 hs hK' hc, eventually_gt_atTop 0]
    with T hS hT₀ ⟨hlog1, hl1, hlo, hhi⟩ hlbig hrate hT0
  have hlbig' : 28 / ε' + 18 * π * K / ε' + 14 ≤ Zeta23.l T := hlbig
  obtain ⟨hF, hpart⟩ := hdp T hT₀
  have hsplit := trGtildeSq_eq_split hΓ hF hT0.le
  -- notation
  set l := Zeta23.l T with hldef
  set a := params43.a T with hadef
  have hLl : params43.L T = 4 / 3 * l := rfl
  have hell : ell1 T = l + (2 * Real.log 2 - 1) := by unfold ell1; rw [hldef]; ring
  have hc₀ : 0 ≤ 2 * Real.log 2 - 1 := by have := Real.log_two_gt_d9; linarith only [this]
  have hc₁ : 2 * Real.log 2 - 1 ≤ 1 := by have := Real.log_two_lt_d9; linarith only [this]
  have hl14 : 14 / (ε' / 2) ≤ l := by
    have e : 14 / (ε' / 2) = 28 / ε' := by field_simp; norm_num
    have : 0 ≤ 18 * π * K / ε' := by positivity
    linarith only [hlbig', e, this]
  have hl1' : 1 ≤ l := by linarith only [hl1]
  have hw : params43.w = 1 := rfl
  have hl14' : 14 ≤ l := by
    have h1 : 0 ≤ 28 / ε' := by positivity
    have h2 : 0 ≤ 18 * π * K / ε' := by positivity
    linarith only [hlbig', h1, h2]
  have hwL : 8 * params43.w ≤ params43.L T := by rw [hw, hLl]; linarith only [hl14']
  have ha : 1 - 2 / (4 / 3 * l) ≤ a := by
    have := one_sub_le_a_params43 hwL
    rw [hw, hLl] at this; simpa using this
  -- the main term
  have hmain := diagonal_main_le (ε := ε' / 2) (by positivity) (by linarith only [hε'1]) hl14 hl1'
    hc₀ hc₁ ha hT0
  rw [← hell, ← hLl] at hmain
  -- the normalisation
  set D := (a * params43.L T) ^ 2 * (T * ell1 T / (2 * π)) with hD
  have ha2 : 1 / 2 ≤ a := half_le_a_fam paramsValidFam_params43 hwL
  have hellge : l ≤ ell1 T := by rw [hell]; linarith only [hc₀]
  have hDlow : 2 / (9 * π) * (T * l ^ 3) ≤ D := by
    have h1 : (2 / 3 * l) ^ 2 ≤ (a * params43.L T) ^ 2 := by
      rw [hLl]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [ha2, hl1']
    have h2 : T * l / (2 * π) ≤ T * ell1 T / (2 * π) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hellge hT0.le
    have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have e : (2 / 3 * l) ^ 2 * (T * l / (2 * π)) = 2 / (9 * π) * (T * l ^ 3) := by
      field_simp; ring
    rw [hD]; linarith only [h3, e]
  -- the error terms
  have hE1 : K * (T * l ^ 2) ≤ ε' / 4 * D := by
    have h1 : 18 * π * K / ε' ≤ l := by
      have : 0 ≤ 28 / ε' := by positivity
      linarith only [hlbig', this]
    have h2 : K ≤ ε' / (18 * π) * l := by
      rw [div_le_iff₀ hε'0] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith only [h1]
    have h3 : K * (T * l ^ 2) ≤ ε' / (18 * π) * l * (T * l ^ 2) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have e : ε' / (18 * π) * l * (T * l ^ 2) = ε' / 4 * (2 / (9 * π) * (T * l ^ 3)) := by
      field_simp; ring
    have h4 := mul_le_mul_of_nonneg_left hDlow (by positivity : (0:ℝ) ≤ ε' / 4)
    linarith only [h3, e, h4]
  have hE2 : K' * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) ≤ ε' / 4 * D := by
    have h1 : K' * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) ≤ ε' / (18 * π) * T := by
      have e : K' * (Real.log T ^ 2 * T ^ (2 / 3 : ℝ)) = K' * Real.log T ^ 2 * T ^ (2 / 3 : ℝ) := by
        ring
      linarith only [hrate, e]
    have h2 : ε' / (18 * π) * T ≤ ε' / (18 * π) * (T * l ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : 1 ≤ l ^ 3 := one_le_pow₀ hl1'
      nlinarith only [this, hT0]
    have e : ε' / (18 * π) * (T * l ^ 3) = ε' / 4 * (2 / (9 * π) * (T * l ^ 3)) := by
      field_simp; ring
    have h4 := mul_le_mul_of_nonneg_left hDlow (by positivity : (0:ℝ) ≤ ε' / 4)
    linarith only [h1, h2, e, h4]
  -- assemble
  have hS' : frobSurplus (params43.toSetting T) (params43.localFun T) ≤ (1 / 18 + ε' / 4) * D := by
    rw [hD, ← mul_assoc]; exact hS
  have hmain' : T * params43.L T / (2 * π) * (ell1 T ^ 2 + params43.L T ^ 2 / 3)
      ≤ (43 / 36 + ε' / 2 / 2) * D := by
    rw [hD, ← mul_assoc]; exact hmain
  have hD0 : 0 ≤ D := le_trans (by positivity) hDlow
  have hfin : params43.trGtildeSq T ≤ (5 / 4 + ε') * D := by
    rw [hsplit]
    have e : (43 / 36 + ε' / 2 / 2) * D + ε' / 4 * D + ε' / 4 * D + (1 / 18 + ε' / 4) * D
        = (5 / 4 + ε') * D := by ring
    linarith only [hpart, hmain', hE1, hE2, hS', e]
  have hmono : (5 / 4 + ε') * D ≤ (5 / 4 + ε) * D :=
    mul_le_mul_of_nonneg_right (by linarith only [hε'ε]) hD0
  rw [hD] at hfin hmono
  rw [mul_assoc]
  exact hfin.trans hmono

/-- **Three quarters on the line from the surplus hypothesis.** -/
theorem zeta_three_quarters_of_surplus (h : SurplusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  zeta_three_quarters_cumulative_of_frobenius (frobeniusFourThirds_of_surplus h)

/-- **…and three quarters simple and on the line.** -/
theorem zeta_three_quarters_simple_of_surplus (h : SurplusFourThirds) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  zeta_three_quarters_simple_cumulative_of_frobenius (frobeniusFourThirds_of_surplus h)

end RHTower
