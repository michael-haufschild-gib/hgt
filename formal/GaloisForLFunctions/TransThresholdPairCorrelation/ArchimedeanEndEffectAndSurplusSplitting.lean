import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfPrimeSurplus
import GaloisForLFunctions.RHTower.ThmEUniformEnds

/-!
# Bilinear Splitting of the End-Effect Form and Unconditional Archimedean End-Effect Bounds

In the bandwidth-`λ` Frobenius decomposition (`ZetaFrobeniusSurplusSplit`), the grid end correction
`endForm p F (ν_X) (ν_X) = L⁻² ∑_{k,l<d} G_{kl}(ν_X)² − 𝓜[ν_X, ν_X]` is packaged inside
`primeSurplus p F` as a single quadratic form in the combined density `ν_X = μ + Π_X + P_X`.
If one applies `lem_ends_nu_W` monolithically to `ν_X` with `B = l + 4√X`, even the purely
archimedean grid boundary interaction is charged the prime-length bound `O(L l log l · X)`.

This module establishes the bilinear decomposition of `endForm` along `ν_X = μ + Π_X + P_X` and
proves unconditional bounds on its archimedean and pole components at every bandwidth `λ ≤ 2`:

1. **Exact trinomial splitting (`endForm_trinomial`, `endForm_nuX_split`):**
   By `endForm_add_add`, `endForm_add_left`, and `endForm_comm`,
   `endForm p F (u + v + w) (u + v + w)` expands into six symmetric bilinear terms, separating
   `μ`, `Π_X`, and `P_X`.
2. **Unconditional `X`-independent archimedean end-effect bound (`exists_abs_endForm_mu_mu_le`):**
   Because `μ = μ_{0,1}` satisfies `|μ(τ)| ≤ C₀ l + log⁺(|τ|/4T)` with `C₀ ≥ 1` (`mu_nuBound`),
   `lem_ends_nu_W` gives
   `|endForm p F μ μ| ≤ C · L · l³ · log l`
   at every bandwidth with `L ≤ 2l`, completely independent of the prime cutoff `X`.
3. **Bandwidth-`4/3` specialization (`exists_abs_endForm_mu_mu_params43_le`):**
   At `λ = 4/3`, `|endForm (params43.toSetting T) (params43.localFun T) μ μ| = O(l⁴ log l) = o(T/log T)`.
-/

open MeasureTheory Real Set Filter Zeta23 Zeta23.PrimeSide Zeta23.ThmE RHTower
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-! ## Component-wise `NuBound` estimates for `μ`, `Π_X`, and `P_X` -/

/-- The archimedean density `μ` satisfies `NuBound p (C₀ * p.l) μ` for large `T`, with `C₀ ≥ 1`
independent of the prime cutoff `X`. -/
theorem mu_nuBound :
    ∃ C₀ T₀ : ℝ, 1 ≤ C₀ ∧ ∀ p : Setting, T₀ ≤ p.T → NuBound p (C₀ * p.l) Zeta23.mu := by
  obtain ⟨C₀, T₀, hC₀, hB⟩ := muq_nuBound (κ := 0) (q := 1)
    (GammaChi.gammaFactsChi (by norm_num) le_rfl) le_rfl
  refine ⟨C₀, T₀, hC₀, fun p hT τ => ?_⟩
  rw [mu_eq_muq]
  exact hB p hT τ

/-- Pointwise bound `|Π_X(τ)| ≤ 3 √X` under `LocalHypsCoreW`. -/
theorem abs_PiX_le (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X :=
  (hF.PiX_bound τ).trans (div_le_self (by positivity) (by linarith [abs_nonneg τ]))

/-- The pole density `Π_X` satisfies `NuBound p (3 * √X) (Π_X)` under `LocalHypsCoreW`. -/
theorem PiX_nuBound (hF : LocalHypsCoreW cϱ p F) :
    NuBound p (3 * Real.sqrt p.X) (Zeta23.PiX p.X) :=
  nuBound_of_abs_le (abs_PiX_le hF)

/-- The prime Dirichlet polynomial `P_X` satisfies `NuBound p ((1/π) Σ_{n≤X} a_n) (P_X)`. -/
theorem PX_nuBound (p : Setting) :
    NuBound p ((1 / π) * ∑ n ∈ primeRange p.X, acoef n) (Zeta23.PX p.X) :=
  nuBound_of_abs_le fun τ => Zeta23.PX_abs_le p.X τ

/-- If `u` satisfies `NuBound p Bu u` and `|v τ| ≤ Bv` pointwise, then `u + v` satisfies
`NuBound p (Bu + Bv) (u + v)`. -/
theorem nuBound_add_of_abs_le {u v : ℝ → ℝ} {Bu Bv : ℝ} (hu : NuBound p Bu u)
    (hv : ∀ τ, |v τ| ≤ Bv) :
    NuBound p (Bu + Bv) (u + v) := by
  intro τ
  have h1 := hu τ
  have h2 := hv τ
  have htri : |u τ + v τ| ≤ |u τ| + |v τ| := abs_add_le (u τ) (v τ)
  change |u τ + v τ| ≤ Bu + Bv + max (Real.log (|τ| / (4 * p.T))) 0
  linarith

/-! ## Bilinear trinomial splitting of `endForm` -/

/-- Polarization identity for `endForm`:
`2 E(u, v) = E(u + v, u + v) − E(u, u) − E(v, v)`. -/
theorem two_mul_endForm_eq (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) {Bu Bv : ℝ} (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hνu : NuBound p Bu u) (hνv : NuBound p Bv v) :
    2 * endForm p F u v
      = endForm p F (u + v) (u + v) - endForm p F u u - endForm p F v v := by
  have hadd := endForm_add_add hF hT hu hv hBu hBv hνu hνv
  have hcomm := endForm_comm hF v u
  linarith

/-- Left additivity of `endForm`: `E(u + v, w) = E(u, w) + E(v, w)`. -/
theorem endForm_add_left (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) {Bu Bv : ℝ}
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) (hνu : NuBound p Bu u) (hνv : NuBound p Bv v) :
    endForm p F (u + v) w = endForm p F u w + endForm p F v w := by
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold endForm
  simp_rw [GentryNu_add hF hT hu hv hBu hBv hνu hνv]
  rw [Mform_add_left hΦ hu hv hw]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

/-- **Trinomial expansion of `endForm`:** for continuous densities `u, v, w` where `u` satisfies
`NuBound` and `v, w` are bounded,
`E(u + v + w, u + v + w) = E(u, u) + E(v, v) + E(w, w) + 2 E(u, v) + 2 E(u, w) + 2 E(v, w)`. -/
theorem endForm_trinomial (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) {u v w : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) {Bu Bv Bw : ℝ}
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) (hBw : 0 ≤ Bw)
    (hνu : NuBound p Bu u) (hvB : ∀ τ, |v τ| ≤ Bv) (hwB : ∀ τ, |w τ| ≤ Bw) :
    endForm p F (u + v + w) (u + v + w)
      = endForm p F u u + endForm p F v v + endForm p F w w
        + 2 * endForm p F u v + 2 * endForm p F u w + 2 * endForm p F v w := by
  have hνv : NuBound p Bv v := nuBound_of_abs_le hvB
  have hνw : NuBound p Bw w := nuBound_of_abs_le hwB
  have huv_nu : NuBound p (Bu + Bv) (u + v) := nuBound_add_of_abs_le hνu hvB
  have h1 := endForm_add_add hF hT (hu.add hv) hw (add_nonneg hBu hBv) hBw huv_nu hνw
  have h2 := endForm_add_add hF hT hu hv hBu hBv hνu hνv
  have hc_vu := endForm_comm hF v u
  have hc_w_uv := endForm_comm hF w (u + v)
  have h_lin := endForm_add_left hF hT hu hv hw hBu hBv hνu hνv
  linarith

/-- **Exact splitting of the grid end-effect form `endForm p F (ν_X) (ν_X)`** into its archimedean,
pole, and prime components. -/
theorem endForm_nuX_split (hΓ : GammaFacts) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ {cϱ : ℝ} {p : Setting} {F : LocalFun},
      T₀ ≤ p.T → LocalHypsCoreW cϱ p F →
      endForm p F (Zeta23.nuX p.X) (Zeta23.nuX p.X)
        = endForm p F Zeta23.mu Zeta23.mu
          + endForm p F (Zeta23.PiX p.X) (Zeta23.PiX p.X)
          + endForm p F (Zeta23.PX p.X) (Zeta23.PX p.X)
          + 2 * endForm p F Zeta23.mu (Zeta23.PiX p.X)
          + 2 * endForm p F Zeta23.mu (Zeta23.PX p.X)
          + 2 * endForm p F (Zeta23.PiX p.X) (Zeta23.PX p.X) := by
  obtain ⟨C₀, T₀, hC₀, hμB⟩ := mu_nuBound
  refine ⟨max T₀ 1, le_max_right _ _, fun {cϱ p F} hT hF => ?_⟩
  have hT₀ : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT
  have hl0 : 0 ≤ p.l := by linarith [hF.one_le_l]
  have hBu : 0 ≤ C₀ * p.l := mul_nonneg (by linarith) hl0
  have hBv : 0 ≤ 3 * Real.sqrt p.X := by positivity
  have hBw : 0 ≤ (1 / π) * ∑ n ∈ primeRange p.X, acoef n :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => acoef_nonneg n)
  exact endForm_trinomial hF hT1 hΓ.smooth.continuous hF.PiX_cont (PX_continuous p.X)
    hBu hBv hBw (hμB p hT₀) (abs_PiX_le hF) (fun τ => Zeta23.PX_abs_le p.X τ)

/-! ## Unconditional `X`-independent bound on the archimedean end-effect `endForm p F μ μ` -/

/-- **Unconditional `X`-independent archimedean end-effect bound:** at every bandwidth `λ` with
`L ≤ 2l`, `|endForm p F μ μ| ≤ C · L · l³ · log l`, independent of the prime cutoff `X`. -/
theorem exists_abs_endForm_mu_mu_le (cϱ lam : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ (p : Setting) (F : LocalFun),
      p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l →
      |endForm p F Zeta23.mu Zeta23.mu| ≤ C * (p.L * p.l ^ 3 * Real.log p.l) := by
  obtain ⟨Ce, Te, hends⟩ := exists_abs_endForm_self_le cϱ lam
  obtain ⟨C₀, Tμ, hC₀1, hμB⟩ := mu_nuBound
  have hΓ : GammaFacts := paperInputs_zeta.Gamma
  refine ⟨|Ce| * C₀ ^ 2, max Te (max Tμ (2 * π * Real.exp (Real.exp 1))),
    by positivity, fun p F hplam hT hF hL2l => ?_⟩
  have hTe : Te ≤ p.T := (le_max_left _ _).trans hT
  have hTμ : Tμ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hTe1 : 2 * π * Real.exp (Real.exp 1) ≤ p.T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hl_exp : Real.exp 1 ≤ p.l := Setting.le_l_of_T hTe1
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hl1 : 1 ≤ p.l := hexp1.trans hl_exp
  have hlogl : 0 ≤ Real.log p.l := Real.log_nonneg hl1
  have hBl : p.l ≤ C₀ * p.l := le_mul_of_one_le_left (by linarith) hC₀1
  have hmain := hends p F (C₀ * p.l) Zeta23.mu hplam hTe hF hL2l
    hΓ.smooth.continuous (hμB p hTμ) hBl
  have hL0 : 0 ≤ p.L := hF.L_pos.le
  have hstep : Ce * (p.L * p.l * Real.log p.l * (C₀ * p.l) ^ 2)
      ≤ |Ce| * C₀ ^ 2 * (p.L * p.l ^ 3 * Real.log p.l) := by
    calc Ce * (p.L * p.l * Real.log p.l * (C₀ * p.l) ^ 2)
        ≤ |Ce| * (p.L * p.l * Real.log p.l * (C₀ * p.l) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self Ce) (by positivity)
      _ = |Ce| * C₀ ^ 2 * (p.L * p.l ^ 3 * Real.log p.l) := by ring
  exact hmain.trans hstep

/-- **At bandwidth `λ = 4/3`, the archimedean end-effect `endForm (params43) μ μ` is
`O(l⁴ log l) = O(log⁴ T log log T)` unconditionally** — independent of `X = (T/2π)^{4/3}`. -/
theorem exists_abs_endForm_mu_mu_params43_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T in atTop,
      |endForm (params43.toSetting T) (params43.localFun T) Zeta23.mu Zeta23.mu|
        ≤ K * (Zeta23.l T ^ 4 * Real.log (Zeta23.l T)) := by
  have hP := paramsValidFam_params43
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨C, T₀, hC0, hend⟩ := exists_abs_endForm_mu_mu_le params43.crho (4 / 3)
  refine ⟨4 / 3 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop TL, eventually_ge_atTop T₀] with T hTL' hT₀
  have hF := hTL T hTL'
  set p := params43.toSetting T
  set F := params43.localFun T
  have hpl : p.l = Zeta23.l T := rfl
  have hpL : p.L = 4 / 3 * p.l := rfl
  have hL2l : p.L ≤ 2 * p.l := by rw [hpL]; linarith [hF.one_le_l]
  have h := hend p F rfl hT₀ hF hL2l
  refine h.trans (le_of_eq ?_)
  rw [hpL, hpl]
  ring

end GaloisForLFunctions.TransThresholdPairCorrelation
