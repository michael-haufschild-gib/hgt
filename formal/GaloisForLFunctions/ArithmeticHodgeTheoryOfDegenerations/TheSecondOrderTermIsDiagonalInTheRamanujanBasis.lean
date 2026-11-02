import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRamanujanWindowCountsEveryConductor

/-!
# The Ramanujan expansion diagonalizes the second-order term
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### The sharp form of a twisted window from its energy -/

/-- **The sharp form of a twisted window from its energy.** For a mean-zero `M`-periodic twist whose
block energy is `2π Ξ_N(c) + O(c/N)` and whose energy below `N e^{−A}/M` is `O(N^{−1/2})`:
`c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²) Ξ_N(c) → 0` along every schedule with `c → ∞`,
`c (log N)²/N → 0`. -/
theorem twisted_layer_sharp_of_energy (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hclog : Tendsto (fun N : ℕ => c N * Real.log N ^ 2 / N) atTop (𝓝 0))
    {χ : ℕ → ℝ} {Mχ : ℕ} (hχ : MeanZeroTwist χ Mχ) (Ξ : ℝ → ℕ → ℝ)
    (hE : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 / N)) - 2 * Real.pi * Ξ c N| ≤
        K * c / N)
    (hL : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log Mχ))))
          ((N : ℝ) * Real.exp (-(A + Real.log Mχ))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (χ) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / (∫ u, φ u ^ 2) * Ξ (c N) N) atTop (𝓝 0) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hcN := tendsto_div_of_log_sq hc1 hclog
  have hm' : 0 < Mχ := hχ.pos
  have hlogp : 0 ≤ Real.log Mχ := Real.log_nonneg (by exact_mod_cast hχ.pos)
  obtain ⟨S', hS'⟩ : ∃ S', S' = ∑ j ∈ range Mχ, |χ j| := ⟨_, rfl⟩
  obtain ⟨Cp, hCp0, hCp⟩ := exists_abs_twistedPole_le hφ hφsupp hφ2 hh hA hsupp
    (hχ)
  obtain ⟨KE, hKE0, hKE⟩ := hE
  obtain ⟨CL, hCL0, hCL⟩ := hL
  obtain ⟨C, hC0, hC⟩ := exists_abs_mu_sub_log_le
  obtain ⟨Aν, hAν, hν⟩ := exists_abs_nuSymbol_le (Real.exp_pos (2 * (A + 1))).le
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  set M := ∫ u, φ u ^ 2 with hM
  set A' := A + Real.log Mχ with hA'
  set x : ℕ → ℕ → ℝ := fun N => twistedWeights h (χ) N with hx
  set T₀ : ℕ → ℝ := fun N => (N : ℝ) * Real.exp (-A') with hT₀
  set S : ℕ → ℝ → ℝ := fun N => symbolW φ (x N) (c N) N (Real.exp (2 * (A + 1))) with hS
  set E : ℕ → ℝ → ℝ := fun N τ => ‖paperFT (cx φ) (((c N / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (x N) τ‖ ^ 2 / N) with hE
  set P : ℕ → ℝ := fun N =>
    (paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (χ) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (χ) N) (c N) N))) (Complex.I / 2) +
    paperFT (EF.weilTest (cx (centredAtomicTest φ (twistedWeights h (χ) N) (c N) N))
      (cx (centredAtomicTest φ (twistedWeights h (χ) N) (c N) N))) (-Complex.I / 2)).re /
        (c N * (c N / N * M)) with hP
  set Rm : ℕ → ℝ := fun N => ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ,
    (S N τ - Real.log N / (2 * Real.pi) * E N τ) with hRm
  set Lo : ℕ → ℝ := fun N => ∫ τ in Set.Icc (-T₀ N) (T₀ N), S N τ with hLo
  set LoE : ℕ → ℝ := fun N => Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ with hLoE
  set Df : ℕ → ℝ := fun N => Real.log N * ((∫ τ, E N τ) - 2 * Real.pi * Ξ (c N) N)
    with hDf
  -- eventual conditions
  have hlogN := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev3 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N := hlogN.eventually (eventually_ge_atTop 1)
  have hev4 : ∀ᶠ N : ℕ in atTop, 4 * c N ≤ N := by
    filter_upwards [hcN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      eventually_ge_atTop 1] with N h1 hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0] at h1; linarith
  have hevA := tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp A'))
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A')) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  have hevT := hT.eventually (eventually_ge_atTop 2)
  -- the pole terms
  have hPt : Tendsto P atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => Cp / (N : ℝ) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    rw [Real.norm_eq_abs]
    exact hCp N hN (c N) (hc0 N) (by linarith [hc0 N])
  -- the quiet region
  have hEnn : ∀ N τ, 0 ≤ E N τ := fun N τ => by simp only [hE]; positivity
  have hLoEt : Tendsto LoE atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * (Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      simpa using tendsto_log_div_sqrt.const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hI := hCL N hN (c N) (hc0 N)
    have hI0 : 0 ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ :=
      setIntegral_nonneg measurableSet_Icc fun τ _ => hEnn N τ
    simp only [hLoE]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hI0]
    calc Real.log N * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ ≤ Real.log N * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hI hlog0
      _ = CL * (Real.log N / Real.sqrt N) := by ring
  have hLot : Tendsto Lo atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => CL * ((Aν + Real.log 3) / Real.sqrt N +
        Real.log N / Real.sqrt N)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (Aν + Real.log 3) / Real.sqrt N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
      simpa using (h1.add tendsto_log_div_sqrt).const_mul CL
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
    have hT₀N : T₀ N ≤ N := by
      simp only [hT₀, hA']
      have : Real.exp (-(A + Real.log Mχ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
    have hWl : 0 ≤ Aν + Real.log (2 + N) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + N by linarith); linarith
    have hpt : ∀ τ ∈ Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤ (Aν + Real.log (2 + N)) * E N τ :=
      fun τ hτ => by
        have hτN : |τ| ≤ N := (abs_le.mpr hτ).trans hT₀N
        have hν' : |nuSymbol (Real.exp (2 * (A + 1))) τ| ≤ Aν + Real.log (2 + N) :=
          (hν τ).trans (by
            have := Real.log_le_log (by positivity : (0 : ℝ) < 2 + |τ|) (by linarith :
              2 + |τ| ≤ 2 + N)
            linarith)
        show |symbolW φ (twistedWeights h (χ) N) (c N) N (Real.exp (2 * (A + 1))) τ| ≤ _
        rw [symbolW, abs_mul, abs_of_nonneg (by positivity), mul_comm]
        exact mul_le_mul_of_nonneg_right hν' (by positivity)
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp _ (hc0 N) hN _
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp _ (hc0 N) hN
    have h1 : ‖Lo N‖ ≤ ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| := by
      simp only [hLo]
      rw [Real.norm_eq_abs]
      exact abs_integral_le_integral_abs
    have h2 : ∫ τ in Set.Icc (-T₀ N) (T₀ N), |S N τ| ≤
        ∫ τ in Set.Icc (-T₀ N) (T₀ N), (Aν + Real.log (2 + N)) * E N τ :=
      setIntegral_mono_on hSi.abs.integrableOn (hEi.const_mul _).integrableOn measurableSet_Icc hpt
    rw [integral_const_mul] at h2
    have hI := hCL N hN (c N) (hc0 N)
    have hlog3 : Real.log (2 + N) ≤ Real.log 3 + Real.log N := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    refine h1.trans (h2.trans ?_)
    calc (Aν + Real.log (2 + N)) * ∫ τ in Set.Icc (-T₀ N) (T₀ N), E N τ
        ≤ (Aν + Real.log (2 + N)) * (CL / Real.sqrt N) := mul_le_mul_of_nonneg_left hI hWl
      _ ≤ (Aν + Real.log 3 + Real.log N) * (CL / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = CL * ((Aν + Real.log 3) / Real.sqrt N + Real.log N / Real.sqrt N) := by ring
  -- the remainder above the cut
  have hRmt : Tendsto Rm atTop (𝓝 0) := by
    set VV := C + Real.exp (2 * (A + 1)) ^ 2 / Real.pi + A' + 1 with hVV
    have hcp : Tendsto (fun N : ℕ => c N ^ q) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp hcinf
    have hlim : Tendsto (fun N : ℕ => 2 * (aliasConst Cφ q A' (S' * Bh) * VV / c N ^ q)) atTop
        (𝓝 0) := by
      have := (tendsto_const_nhds (x := aliasConst Cφ q A' (S' * Bh) * VV)).div_atTop hcp
      simpa using this.const_mul 2
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hevA, hevT, eventually_ge_atTop 1] with N h1 h2 hN
    rw [Real.norm_eq_abs]
    have hsq : ∀ n, x N n ^ 2 ≤ S' ^ 2 * horizonWeights h N n ^ 2 := fun n => by
      simp only [hx, twistedWeights, mul_pow]
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hb := abs_periodic_le hm' hχ.periodic n
      rw [← hS'] at hb
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hS1 : ∑ n ∈ Icc 1 N, x N n ^ 2 ≤ (S' * Bh) ^ 2 * Real.exp A' := by
      refine (sum_le_sum fun n _ => hsq n).trans ?_
      rw [← mul_sum, mul_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((sum_horizonWeights_sq_le hsupp hB hN).trans ?_)
        (by positivity)
      gcongr
      linarith
    have hS2 : ∑ n ∈ Icc 1 N, (n : ℝ) * x N n ^ 2 ≤ N * (S' * Bh) ^ 2 := by
      refine (sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hsq n) (Nat.cast_nonneg n)).trans ?_
      have := sum_mul_horizonWeights_sq_le hB N (h := h)
      calc ∑ n ∈ Icc 1 N, (n : ℝ) * (S' ^ 2 * horizonWeights h N n ^ 2)
          = S' ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) * horizonWeights h N n ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        _ ≤ S' ^ 2 * (N * Bh ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = N * (S' * Bh) ^ 2 := by ring
    exact abs_remainderW_le hφ hφsupp (by linarith : 1 < q) hCφ hdecay hC0 hC (2 * (A + 1))
      (by linarith) h1 hS1 hS2 h2 (hc0 N)
  -- the energy defect
  have hDft : Tendsto Df atTop (𝓝 0) := by
    have t1 : Tendsto (fun N : ℕ => Real.log N * (c N / N)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ hclog
      · have := hc1 N
        have := Real.log_natCast_nonneg N
        positivity
      · filter_upwards [hev3] with N hN
        have hc0' : 0 ≤ c N / N := by have := hc1 N; positivity
        calc Real.log N * (c N / N) ≤ Real.log N * Real.log N * (c N / N) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by linarith) hN) hc0'
          _ = c N * Real.log N ^ 2 / N := by ring
    have hlim := t1.const_mul KE
    rw [mul_zero] at hlim
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    rw [Real.norm_eq_abs]
    simp only [hDf]
    rw [abs_mul, abs_of_nonneg hlog0]
    have := hKE (c N) (hc1 N) N h4
    calc Real.log N * |(∫ τ, E N τ) - 2 * Real.pi * Ξ (c N) N|
        ≤ Real.log N * (KE * c N / N) := mul_le_mul_of_nonneg_left this hlog0
      _ = KE * (Real.log N * (c N / N)) := by ring
  -- the identity
  have hid : ∀ᶠ N : ℕ in atTop, P N + M⁻¹ * Lo N + M⁻¹ * Rm N - M⁻¹ * (2 * Real.pi)⁻¹ * LoE N +
      M⁻¹ * (2 * Real.pi)⁻¹ * Df N =
      (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (χ) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) -
      Real.log N / M * Ξ (c N) N := by
    filter_upwards [hev4, eventually_ge_atTop 1] with N h4 hN
    have hcle : c N ≤ N := by linarith [hc0 N]
    rw [atomForm_eq hφ hφsupp hφ2 (twistedWeights_eq_zero hsupp (χ) N) hA (hc0 N) hN hcle,
      ← hM]
    have hSi : Integrable (S N) := integrable_symbolW hφ hφsupp (x N) (hc0 N) hN (2 * (A + 1))
    have hEi : Integrable (E N) := integrable_energyW hφ hφsupp (x N) (hc0 N) hN
    have hsplitS := (integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hSi).symm
    have hsplitE := integral_add_compl (s := Set.Icc (-T₀ N) (T₀ N)) measurableSet_Icc hEi
    have hcompl : ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, S N τ = Rm N +
        Real.log N / (2 * Real.pi) * ∫ τ in (Set.Icc (-T₀ N) (T₀ N))ᶜ, E N τ := by
      simp only [hRm]
      rw [integral_sub hSi.integrableOn (hEi.const_mul _).integrableOn, integral_const_mul]
      ring
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have hM0 : M ≠ 0 := hφ2.ne'
    have hSeq : (∫ τ, symbolW φ (twistedWeights h (χ) N) (c N) N
        (Real.exp (2 * (A + 1))) τ) = ∫ τ, S N τ := rfl
    rw [hSeq, hsplitS, hcompl]
    simp only [hP, hLo, hLoE, hDf]
    rw [← hsplitE]
    have hpi' : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
    linear_combination (-(M⁻¹ * Real.log N * Ξ (c N) N)) * hpi'
  refine Tendsto.congr' hid ?_
  have := (((hPt.add (hLot.const_mul M⁻¹)).add (hRmt.const_mul M⁻¹)).sub
    (hLoEt.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))).add (hDft.const_mul (M⁻¹ * (2 * Real.pi)⁻¹))
  simpa using this

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
