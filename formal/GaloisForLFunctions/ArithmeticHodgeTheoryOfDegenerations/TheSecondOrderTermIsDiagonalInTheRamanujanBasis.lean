import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRamanujanWindowCountsEveryConductor

/-!
# The second-order term is diagonal in the Ramanujan basis

A window twisted by a finite Ramanujan expansion `χ = Σ_{m ∈ S} a_m c_m`, conductors `m ≥ 2`, has
second-order term `(Σ_m a_m² J_{β+1}(m)) βJ/K ‖H‖²_{−(β+1)}` at the critical curve: Ramanujan sums of
distinct conductors are orthogonal for the second-order form and each carries the count of its
conductor (Parseval for the count).

* **Orthogonality at every offset** (`sum_ramTwist_mul_ramTwist_add`): for `m, m' ∣ M`,
  `Σ_{r<M} c_m(r) c_{m'}(r + s) = [m = m'] M c_m(s)`. In the primitive-root expansion the sum over
  `r` keeps `ζξ = 1`, which forces `ξ⁻¹` to be primitive of both orders.
* **Autocorrelation** (`autoCorr_ramComb`): `C_χ(δ) = Σ_m a_m² c_m(δ)`, so the energy law of
  periodic twists gives `E_N = 2π Σ_m a_m² 𝒜^{(m)}_N(c) + O(c/N)` (`abs_ramCombEnergy_sub_le`).
* **Quiet region** (`exists_ramCombLow_energy_le`): Cauchy–Schwarz over the conductors reduces the
  quiet energy to that of each Ramanujan block.
* **Sharp form from the energy** (`twisted_layer_sharp_of_energy`): for every mean-zero periodic
  twist whose energy is `2πΞ_N(c) + O(c/N)` and which is quiet below `N e^{−A}/M`,
  `c⁻¹⟨W x, x⟩/∫g² − (log N/∫φ²) Ξ_N(c) → 0`.
* **Parseval for the count** (`ramComb_layer_criticalCurve_of_regularBulk`,
  `ramComb_layer_criticalCurve_exact`): tilted spline `(7/K) Σ_m a_m² φ(m) J(m) ‖H‖²_{−8}`.
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

/-! ### Ramanujan expansions -/

/-- A finite Ramanujan expansion `χ(n) = Σ_{m ∈ S} a_m c_m(n)`. -/
def ramComb (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ S, a m * ramTwist m n

theorem ramTwist_add_mul (m n k : ℕ) : ramTwist m (n + m * k) = ramTwist m n :=
  periodic_add_mul (ramTwist_add_self m) n k

theorem ramComb_add_prod (S : Finset ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ramComb S a (n + ∏ m ∈ S, m) = ramComb S a n := by
  unfold ramComb
  refine sum_congr rfl fun m hm => ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun m => m) hm
  rw [hk, ramTwist_add_mul]

/-- A Ramanujan expansion with conductors `≥ 2` is a mean-zero twist of period `∏ m`. -/
theorem meanZeroTwist_ramComb {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    MeanZeroTwist (ramComb S a) (∏ m ∈ S, m) where
  pos := Finset.prod_pos fun m hm => by linarith [hS m hm]
  periodic := ramComb_add_prod S a
  mean_zero := by
    unfold ramComb
    rw [Finset.sum_comm]
    refine sum_eq_zero fun m hm => ?_
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun m => m) hm
    rw [← Finset.mul_sum, hk, show m * k = k * m + 0 by ring,
      sum_range_mul_add (meanZeroTwist_ramTwist (hS m hm)), Finset.sum_range_zero, mul_zero]

/-- **Ramanujan sums of distinct conductors are orthogonal at every offset**:
`Σ_{r<M} c_m(r) c_{m'}(r + s) = [m = m'] M c_m(s)` for `m, m' ∣ M`. -/
theorem sum_ramTwist_mul_ramTwist_add {m m' M : ℕ} (hm : 0 < m) (hm' : 0 < m') (hmM : m ∣ M)
    (hm'M : m' ∣ M) (s : ℕ) :
    ∑ r ∈ range M, ramTwist m r * ramTwist m' (r + s) =
      if m = m' then (M : ℝ) * ramTwist m s else 0 := by
  have h : ((∑ r ∈ range M, ramTwist m r * ramTwist m' (r + s) : ℝ) : ℂ) =
      ((if m = m' then (M : ℝ) * ramTwist m s else 0 : ℝ) : ℂ) := by
    push_cast
    simp_rw [← ramanujanSum_eq_ramTwist hm, ← ramanujanSum_eq_ramTwist hm',
      ArithmeticEffectivityTheory.ramanujanSum]
    set P := primitiveRoots m ℂ with hP
    set P' := primitiveRoots m' ℂ with hP'
    have e1 : ∑ r ∈ range M, (∑ ζ ∈ P, ζ ^ r) * ∑ ξ ∈ P', ξ ^ (r + s) =
        ∑ ξ ∈ P', ξ ^ s * ∑ ζ ∈ P, ∑ r ∈ range M, (ζ * ξ) ^ r := by
      have hpt : ∀ r, (∑ ζ ∈ P, ζ ^ r) * ∑ ξ ∈ P', ξ ^ (r + s) =
          ∑ ξ ∈ P', ξ ^ s * ∑ ζ ∈ P, (ζ * ξ) ^ r := fun r => by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
        refine sum_congr rfl fun ξ _ => ?_
        rw [Finset.mul_sum]
        refine sum_congr rfl fun ζ _ => ?_
        rw [pow_add, mul_pow]
        ring
      rw [sum_congr rfl fun r _ => hpt r, Finset.sum_comm]
      refine sum_congr rfl fun ξ _ => ?_
      rw [← Finset.mul_sum, Finset.sum_comm]
    have e2 : ∀ ξ ∈ P', ∑ ζ ∈ P, ∑ r ∈ range M, (ζ * ξ) ^ r =
        if m = m' then (M : ℂ) else 0 := fun ξ hξ => by
      have hξp := (mem_primitiveRoots hm').mp hξ
      have hξ0 : ξ ≠ 0 := hξp.ne_zero hm'.ne'
      have hroot : ∀ ζ ∈ P, ∑ r ∈ range M, (ζ * ξ) ^ r = if ζ = ξ⁻¹ then (M : ℂ) else 0 :=
        fun ζ hζ => by
          have hζp := (mem_primitiveRoots hm).mp hζ
          have hζM : ζ ^ M = 1 := (hζp.pow_eq_one_iff_dvd M).mpr hmM
          have hξM : ξ ^ M = 1 := (hξp.pow_eq_one_iff_dvd M).mpr hm'M
          rw [sum_range_pow_root (by rw [mul_pow, hζM, hξM, one_mul])]
          congr 1
          exact propext (mul_eq_one_iff_eq_inv₀ hξ0)
      rw [sum_congr rfl hroot, Finset.sum_ite_eq' P ξ⁻¹ (fun _ => (M : ℂ))]
      by_cases hmm : m = m'
      · subst hmm
        rw [if_pos ((mem_primitiveRoots hm).mpr hξp.inv), if_pos rfl]
      · rw [if_neg hmm, if_neg]
        intro hin
        exact hmm (((mem_primitiveRoots hm).mp hin).unique hξp.inv)
    rw [e1, sum_congr rfl fun ξ hξ => by rw [e2 ξ hξ]]
    split_ifs with hmm
    · subst hmm
      rw [← Finset.sum_mul, Complex.ofReal_mul, ← ramanujanSum_eq_ramTwist hm,
        ArithmeticEffectivityTheory.ramanujanSum, hP']
      push_cast
      ring
    · simp
  exact_mod_cast h

theorem periodicExt_add_nat {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n)
    (r : ℕ) (δ : ℤ) : periodicExt χ M (r + δ) = χ (r + (δ % M).toNat) := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hs : (((δ % M).toNat : ℕ) : ℤ) = δ % M := Int.toNat_of_nonneg (Int.emod_nonneg δ hM'.ne')
  unfold periodicExt
  have e : ((r : ℤ) + δ) % M = (((r + (δ % M).toNat) % M : ℕ) : ℤ) := by
    push_cast
    rw [hs, Int.add_emod_emod]
  rw [e, Int.toNat_natCast, periodic_mod hper]

/-- At an offset reduced modulo a multiple `M` of `m`, the Ramanujan sum is
`Σ_{de = m} μ(d) e [e ∣ δ]`. -/
theorem ramTwist_emod_eq {m M : ℕ} (hM : 0 < M) (hmM : m ∣ M) (δ : ℤ) :
    ramTwist m (δ % M).toNat = ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℝ) * (if (x.2 : ℤ) ∣ δ then (x.2 : ℝ) else 0) := by
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hs : (((δ % M).toNat : ℕ) : ℤ) = δ % M := Int.toNat_of_nonneg (Int.emod_nonneg δ hM'.ne')
  unfold ramTwist
  refine sum_congr rfl fun x hx => ?_
  have hxM : (x.2 : ℤ) ∣ M := Int.natCast_dvd_natCast.mpr
    ((Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)).trans hmM)
  have hiff : x.2 ∣ (δ % M).toNat ↔ (x.2 : ℤ) ∣ δ := by
    rw [← Int.natCast_dvd_natCast, hs]
    have e := Int.mul_ediv_add_emod δ M
    constructor
    · intro h1
      rw [← e]
      exact dvd_add (dvd_mul_of_dvd_left hxM _) h1
    · intro h1
      have : δ % M = δ - M * (δ / M) := by linarith
      rw [this]
      exact dvd_sub h1 (dvd_mul_of_dvd_left hxM _)
  by_cases h1 : (x.2 : ℤ) ∣ δ
  · rw [if_pos (hiff.mpr h1), if_pos h1]
  · rw [if_neg (fun h => h1 (hiff.mp h)), if_neg h1]

/-- **The autocorrelation of a Ramanujan expansion is diagonal**:
`C_χ(δ) = Σ_{m ∈ S} a_m² c_m(δ)`. -/
theorem autoCorr_ramComb {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) (δ : ℤ) :
    autoCorr (ramComb S a) (∏ m ∈ S, m) δ = ∑ m ∈ S, a m ^ 2 * autoCorr (ramTwist m) m δ := by
  have hM := (meanZeroTwist_ramComb hS a).pos
  have hM0 : ((∏ m ∈ S, m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [autoCorr, periodMean]
  simp_rw [periodicExt_add_nat hM (ramComb_add_prod S a)]
  have hsum : ∑ r ∈ range (∏ m ∈ S, m), ramComb S a r *
      ramComb S a (r + (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat) =
      ∑ m ∈ S, a m ^ 2 * ((∏ m ∈ S, m : ℕ) * ramTwist m (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat) := by
    unfold ramComb
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun m hm => ?_
    rw [Finset.sum_comm]
    have hmM := Finset.dvd_prod_of_mem (fun m => m) hm
    have hcross : ∀ m' ∈ S, ∑ r ∈ range (∏ m ∈ S, m), a m * ramTwist m r *
        (a m' * ramTwist m' (r + (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat)) =
        if m = m' then a m ^ 2 * ((∏ m ∈ S, m : ℕ) *
          ramTwist m (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat) else 0 := fun m' hm' => by
      have hm'M := Finset.dvd_prod_of_mem (fun m => m) hm'
      have e : ∑ r ∈ range (∏ m ∈ S, m), a m * ramTwist m r *
          (a m' * ramTwist m' (r + (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat)) =
          a m * a m' * ∑ r ∈ range (∏ m ∈ S, m), ramTwist m r *
            ramTwist m' (r + (δ % ((∏ m ∈ S, m : ℕ) : ℤ)).toNat) := by
        rw [Finset.mul_sum]; exact sum_congr rfl fun r _ => by ring
      rw [e, sum_ramTwist_mul_ramTwist_add (by linarith [hS m hm]) (by linarith [hS m' hm'])
        hmM hm'M]
      split_ifs with hmm
      · subst hmm; push_cast; ring
      · ring
    rw [sum_congr rfl hcross, Finset.sum_ite_eq S m]
    rw [if_pos hm]
  rw [hsum, Finset.mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmM := Finset.dvd_prod_of_mem (fun m => m) hm
  rw [autoCorr_ramTwist (by linarith [hS m hm] : 0 < m),
    periodicExt_ramTwist_eq (by linarith [hS m hm] : 0 < m), ← ramTwist_emod_eq hM hmM δ]
  field_simp

/-! ### The energy of a Ramanujan expansion -/

/-- The main term of a Ramanujan window: `(2π/c) Σ_n y_n² Σ_δ c_m(δ) G(δ/a_n) = 2π 𝒜^{(m)}_N(c)`. -/
theorem ramMain_eq (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (h : ℝ → ℝ)
    {m : ℕ} (hm : 1 < m) {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN0 : (0 : ℝ) < N) :
    2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * ramAlias φ h m c N := by
  unfold ramAlias
  have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
      autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      ∑ x ∈ m.divisorsAntidiagonal, 2 * c / N * ((ArithmeticFunction.moebius x.1 : ℝ) *
        (h (Real.log n - Real.log N) ^ 2 * aliasDensity φ (c / x.2 * n / N))) := fun n hn => by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have ha0 : 0 < c * n / N := by positivity
    have haD : c * n / N ≤ ⌈c⌉₊ := by
      refine le_trans ?_ (Nat.le_ceil c)
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN hc0.le
    rw [sum_offset_ramTwist_eq hφ hφsupp hm ha0 haD, horizonWeights, div_pow,
      Real.sq_sqrt hn0.le, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [show c * n / N / x.2 = c / x.2 * n / N by ring]
    field_simp
  rw [sum_congr rfl e, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  unfold horizonAlias
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  field_simp

/-- **The energy of a Ramanujan expansion**: `E_N = 2π Σ_{m ∈ S} a_m² 𝒜^{(m)}_N(c) + O(c/N)`. -/
theorem abs_ramCombEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramComb S a) N) τ‖ ^ 2 / N)) -
        2 * Real.pi * ∑ m ∈ S, a m ^ 2 * ramAlias φ h m c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := periodicEnergy_le hφ hφsupp hh hA hsupp
    (meanZeroTwist_ramComb hS a).pos (ramComb_add_prod S a)
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        autoCorr (ramComb S a) (∏ m ∈ S, m) δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * ∑ m ∈ S, a m ^ 2 * ramAlias φ h m c N := by
    simp_rw [autoCorr_ramComb hS a, Finset.sum_mul]
    have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        ∑ m ∈ S, a m ^ 2 * autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
        ∑ m ∈ S, a m ^ 2 * (horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
          autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹)) := fun n _ => by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact sum_congr rfl fun δ _ => by ring
    rw [sum_congr rfl e, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← Finset.mul_sum]
    linear_combination (a m ^ 2) * ramMain_eq hφ hφsupp h (hS m hm) hc0 hN0
  rw [← hmain]
  exact hK c hc N hcN

/-- The Dirichlet polynomial of a Ramanujan expansion is the expansion of the Dirichlet
polynomials. -/
theorem dirichletPoly_ramComb (S : Finset ℕ) (a : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    dirichletPoly N (twistedWeights h (ramComb S a) N) z =
      ∑ m ∈ S, (a m : ℂ) * dirichletPoly N (twistedWeights h (ramTwist m) N) z := by
  unfold dirichletPoly twistedWeights ramComb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun n _ => ?_
  push_cast
  rw [Finset.sum_mul]
  exact sum_congr rfl fun m _ => by ring

/-- **A Ramanujan expansion is quiet below its first resonance**: the energy on
`|τ| ≤ N e^{−A}/∏ m` is `O(N^{−1/2})`, by Cauchy–Schwarz over the conductors. -/
theorem exists_ramCombLow_energy_le (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log ((∏ m ∈ S, m : ℕ) : ℝ)))))
          ((N : ℝ) * Real.exp (-(A + Real.log ((∏ m ∈ S, m : ℕ) : ℝ)))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramComb S a) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N := by
  have hex : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (1 < m → ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log m))))
          ((N : ℝ) * Real.exp (-(A + Real.log m))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N) :=
    fun m => by
      by_cases hm : 1 < m
      · obtain ⟨C, hC0, hC⟩ := exists_ramLow_energy_le hφ hφsupp hq hCφ hdecay hh hA hsupp hm
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h' => absurd h' hm⟩
  choose C hC0 hC using hex
  refine ⟨S.card * ∑ m ∈ S, a m ^ 2 * C m, by
    have : 0 ≤ ∑ m ∈ S, a m ^ 2 * C m := Finset.sum_nonneg fun m _ => mul_nonneg (sq_nonneg _)
      (hC0 m)
    positivity, fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM := (meanZeroTwist_ramComb hS a).pos
  set T : ℝ := (N : ℝ) * Real.exp (-(A + Real.log ((∏ m ∈ S, m : ℕ) : ℝ))) with hT
  set E : ℕ → ℝ → ℝ := fun m τ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
    (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N) with hE
  have hEi : ∀ m, Integrable (E m) := fun m => integrable_energyW hφ hφsupp _ hc hN
  have hpt : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (ramComb S a) N) τ‖ ^ 2 / N) ≤
      S.card * ∑ m ∈ S, a m ^ 2 * E m τ := fun τ => by
    rw [dirichletPoly_ramComb]
    have h1 : ‖∑ m ∈ S, (a m : ℂ) * dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 ≤
        S.card * ∑ m ∈ S, a m ^ 2 * ‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 := by
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      refine (sq_sum_le_card_mul_sum_sq).trans (le_of_eq ?_)
      congr 1
      refine sum_congr rfl fun m _ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [hE]
    have hF := sq_nonneg ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖
    calc ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖∑ m ∈ S, (a m : ℂ) * dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N)
        ≤ ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * ((S.card * ∑ m ∈ S, a m ^ 2 *
            ‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2) / N) := by gcongr
      _ = S.card * ∑ m ∈ S, a m ^ 2 * (‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
            (‖dirichletPoly N (twistedWeights h (ramTwist m) N) τ‖ ^ 2 / N)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
          exact sum_congr rfl fun m _ => by ring
  have hint : Integrable fun τ => (S.card : ℝ) * ∑ m ∈ S, a m ^ 2 * E m τ :=
    (integrable_finsetSum _ fun m _ => (hEi m).const_mul _).const_mul _
  refine (setIntegral_mono_on (integrable_energyW hφ hφsupp _ hc hN).integrableOn hint.integrableOn
    measurableSet_Icc fun τ _ => hpt τ).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun m _ => ((hEi m).const_mul _).integrableOn]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine sum_le_sum fun m hm => ?_
  have hm1 := hS m hm
  have hmM : m ≤ ∏ m ∈ S, m := Finset.single_le_prod' (fun i hi => (hS i hi).le) hm
  have hTm : T ≤ (N : ℝ) * Real.exp (-(A + Real.log m)) := by
    rw [hT]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN0.le
    have : Real.log m ≤ Real.log ((∏ m ∈ S, m : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < m)) (by exact_mod_cast hmM)
    linarith
  have hsub : Set.Icc (-T) T ⊆ Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log m))))
      ((N : ℝ) * Real.exp (-(A + Real.log m))) := Set.Icc_subset_Icc (by linarith) hTm
  have hmono := setIntegral_mono_set (hEi m).integrableOn
    (Eventually.of_forall fun τ => by simp only [hE]; positivity) hsub.eventuallyLE
  rw [integral_const_mul]
  calc (S.card : ℝ) * (a m ^ 2 * ∫ τ in Set.Icc (-T) T, E m τ)
      ≤ (S.card : ℝ) * (a m ^ 2 * (C m / Real.sqrt N)) := by
        gcongr
        exact hmono.trans (hC m hm1 N hN c hc)
    _ = S.card * (a m ^ 2 * C m) / Real.sqrt N := by ring

/-! ### The second-order term is diagonal in the Ramanujan basis -/

/-- The Ramanujan aliasing along the critical curve:
`(log N/∫φ²) 𝒜^{(m)}_N(c) → J_{β+1}(m) βJ/K ∫ e^{−βy} h²`. -/
theorem tendsto_log_mul_ramAlias (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) (m : ℕ) :
    Tendsto (fun N : ℕ => Real.log N / (∫ u, φ u ^ 2) * ramAlias φ h m (c N) N) atTop
      (𝓝 (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K *
        ∫ y, Real.exp (-(β * y)) * h y ^ 2)) := by
  have hsum := tendsto_finsetSum m.divisorsAntidiagonal fun x hx =>
    (tendsto_log_mul_horizonAlias_div hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK
      hcrit (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx))).const_mul
        (ArithmeticFunction.moebius x.1 : ℝ)
  have hval : ∑ x ∈ m.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
      (K⁻¹ * ((x.2 : ℝ) ^ (β + 1) * (J * (β * ∫ y, Real.exp (-(β * y)) * h y ^ 2)))) =
      ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K *
        ∫ y, Real.exp (-(β * y)) * h y ^ 2 := by
    rw [← sum_antidiagonal_moebius_rpow, Finset.sum_mul, Finset.sum_mul, Finset.sum_div,
      Finset.sum_mul]
    exact sum_congr rfl fun x _ => by field_simp
  rw [hval] at hsum
  refine hsum.congr fun N => ?_
  unfold ramAlias
  rw [Finset.mul_sum]
  exact sum_congr rfl fun x _ => by ring

/-- **The second-order term is diagonal in the Ramanujan basis.** For every profile whose bulk energy
has the rescaled limit `s^β E₁(s) → J`, along `c^{β+1}/log N → K`, the window twisted by a Ramanujan
expansion `χ = Σ_{m ∈ S} a_m c_m` with conductors `m ≥ 2` has
`c⁻¹⟨W x, x⟩/∫g² → (Σ_{m ∈ S} a_m² J_{β+1}(m)) βJ/K ∫ e^{−(β+1)y} H²`:
Ramanujan sums of distinct conductors are orthogonal for the second-order form, and each carries the
count of its conductor. -/
theorem ramComb_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramComb S a) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 ((∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsharp := twisted_layer_sharp_of_energy hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp hc1 hcinf
    hclog (meanZeroTwist_ramComb hS a) (fun c N => ∑ m ∈ S, a m ^ 2 * ramAlias φ h m c N)
    (abs_ramCombEnergy_sub_le hφ hφsupp hh hA hsupp hS a)
    (exists_ramCombLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay hh hA hsupp hS a)
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  have hterm : Tendsto (fun N : ℕ => Real.log N / (∫ u, φ u ^ 2) *
      ∑ m ∈ S, a m ^ 2 * ramAlias φ h m (c N) N) atTop
      (𝓝 (∑ m ∈ S, a m ^ 2 * (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K *
        I))) := by
    have := tendsto_finsetSum S fun m _ =>
      (tendsto_log_mul_ramAlias hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit
        m).const_mul (a m ^ 2)
    refine this.congr fun N => ?_
    rw [Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : ∑ m ∈ S, a m ^ 2 * (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J /
      K * I) = (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β *
        J / K * I := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

/-- **Parseval for the count.** For the tilted spline, a Ramanujan expansion `χ = Σ_{m ∈ S} a_m c_m`
(`m ≥ 2`) and `c⁸/log N → K`: `c⁻¹⟨W x, x⟩/∫g² → (7/K) Σ_{m ∈ S} a_m² φ(m) J(m) ∫ e^{−8y} H²`. -/
theorem ramComb_layer_criticalCurve_exact (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K))
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (ramComb S a) N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
      atTop (𝓝 (7 * (∑ m ∈ S, a m ^ 2 * ((m.totient : ℝ) *
        ArithmeticDegenerationTheory.jordanCoefficient m)) / K *
          ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := ramComb_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hK hcrit' hS a
  have hint : ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight h y ^ 2 =
      ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2 := by
    congr 1; funext y; norm_num
  have h8 : ((7 : ℝ) + 1) = 8 := by norm_num
  rw [hint, h8] at hlim
  rw [sum_congr rfl fun m hm => by
    rw [totient_mul_jordanCoefficient (by linarith [hS m hm] : 0 < m)]]
  convert hlim using 2
  have hs : ∑ m ∈ S, a m ^ 2 * (ArithmeticDegenerationTheory.jordanTotient 8 m * tiltedJordanOne) =
      (∑ m ∈ S, a m ^ 2 * ArithmeticDegenerationTheory.jordanTotient 8 m) * tiltedJordanOne := by
    rw [Finset.sum_mul]; exact sum_congr rfl fun m _ => by ring
  rw [hs]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
