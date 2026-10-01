import GaloisForLFunctions.RHTower.GammaRCubeRegularClass
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.HTGeometry.MellinRegularStripLinear

/-!
# The antisymmetric chart space of `Γ_ℝ(s)^d`, `d ≥ 3`

Degree-`d` version of the cube-root chart. In the chart `x = X^d`,
`(Uf)(X) = √d X^{(d-1)/2} f(X^d)` (unitary), a Mellin symbol `Ψ` on `0 < Re s < 1` becomes
`d^{-1/2} Ψ((w + (d-1)/2)/d)`, and the Voronoi multiplier of `Γ_ℝ(s)^d` becomes
`m_d(w) = Γℝ(s)^d/Γℝ(1-s)^d` with `s = (w + (d-1)/2)/d`.

* On `Re w = -1/2` one has `Re s = (d-2)/(2d)`, and Stirling gives `|Γℝ(s)/Γℝ(1-s)|^d ≍ |w|^{-1}`.
  So `|w m_d(w)|` is bounded for every `d ≥ 3`.
* For antisymmetric regular symbols, Mellin–Plancherel on `Re w = -1/2, 3/2` then gives
  `∫|F'|² ≤ K² ∫X²|F|²`.
* The charts of the theta test functions `K_{d-1}(yx) - y⁻¹K_{d-1}(x/y)` are rapidly decaying
  members of the antisymmetric chart space.
-/

open Complex MeasureTheory Filter Set Topology

noncomputable section

namespace RHTower.GammaRPowTwins

open GaloisForLFunctions.HTGeometry



/-- `|Γℝ(s)^m| ≤ C^m (1+t²)^{-K}` on closed substrips of `Re s > 0`, for `m ≥ 1`. -/
theorem exists_bound_norm_gammaR_pow_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (m K : ℕ)
    (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Gammaℝ s ^ m‖ ≤ C / (1 + s.im ^ 2) ^ K := by
  obtain ⟨C, hC⟩ := exists_bound_norm_gammaR_strip ha hab K
  refine ⟨(max C 0) ^ m, fun s hsa hsb => ?_⟩
  have hden : 0 < (1 + s.im ^ 2) ^ K := by positivity
  have hone : 1 ≤ (1 + s.im ^ 2) ^ K := one_le_pow₀ (by nlinarith [sq_nonneg s.im])
  have hG : ‖Gammaℝ s‖ ≤ max C 0 / (1 + s.im ^ 2) ^ K :=
    (hC s hsa hsb).trans (div_le_div_of_nonneg_right (le_max_left _ _) hden.le)
  rw [norm_pow]
  refine (pow_le_pow_left₀ (norm_nonneg _) hG m).trans ?_
  rw [div_pow, div_le_div_iff₀ (by positivity) hden]
  have h0 : 0 ≤ (max C 0) ^ m := by positivity
  apply mul_le_mul_of_nonneg_left _ h0
  calc (1 + s.im ^ 2) ^ K = ((1 + s.im ^ 2) ^ K) ^ 1 := (pow_one _).symm
    _ ≤ ((1 + s.im ^ 2) ^ K) ^ m := pow_le_pow_right₀ hone hm

/-- The Mellin symbol `Γℝ(s)^{k+1} (y^{-s} - y^{s-1})` of `K_k(y·) - y⁻¹ K_k(·/y)`. -/
def thetaSymbol (k : ℕ) (y : ℝ) (s : ℂ) : ℂ :=
  Gammaℝ s ^ (k + 1) * ((y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1))

/-- The theta test function `K_k(y x) - y⁻¹ K_k(x/y)`. -/
def thetaFunction (k : ℕ) (y : ℝ) (x : ℝ) : ℂ :=
  gammaRPowKernel k (y * x) - ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel k (y⁻¹ * x)

private theorem norm_cpow_neg_le_aux {x : ℝ} (hx : 0 < x) {c₁ c₂ : ℝ} {s : ℂ}
    (hs : s.re ∈ uIcc c₁ c₂) : ‖(x : ℂ) ^ (-s)‖ ≤ x ^ (-c₁) + x ^ (-c₂) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re]
  rcases le_total 1 x with h1 | h1
  · rcases le_total c₁ c₂ with hc | hc
    · rw [Set.uIcc_of_le hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₁) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.1])
      linarith [Real.rpow_nonneg hx.le (-c₂)]
    · rw [Set.uIcc_of_ge hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₂) := Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hs.1])
      linarith [Real.rpow_nonneg hx.le (-c₁)]
  · rcases le_total c₁ c₂ with hc | hc
    · rw [Set.uIcc_of_le hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₂) :=
        Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hs.2])
      linarith [Real.rpow_nonneg hx.le (-c₁)]
    · rw [Set.uIcc_of_ge hc] at hs
      have : x ^ (-s.re) ≤ x ^ (-c₁) :=
        Real.rpow_le_rpow_of_exponent_ge hx h1 (by linarith [hs.2])
      linarith [Real.rpow_nonneg hx.le (-c₂)]

/-- The theta symbols are regular on `0 < Re s < 1`. -/
theorem mellinRegularStrip_thetaSymbol (k : ℕ) {y : ℝ} (hy : 0 < y) :
    MellinRegularStrip (thetaSymbol k y) 0 1 := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  refine ⟨fun s h0 _ => ?_, fun a b ha hb K => ?_⟩
  · exact ((differentiableAt_gammaR_of_re_pos h0).pow (k + 1)).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl hy0)).sub
        ((differentiableAt_id.sub_const 1).const_cpow (Or.inl hy0)))
  · by_cases hab : a ≤ b
    · obtain ⟨C, hC⟩ := exists_bound_norm_gammaR_pow_strip ha hab (k + 1) K (by omega)
      set L := (y ^ (-a) + y ^ (-b)) + (y ^ (-(1 - a)) + y ^ (-(1 - b))) with hL
      refine ⟨C * L, fun s hsa hsb => ?_⟩
      have hmem : s.re ∈ uIcc a b := by rw [Set.uIcc_of_le hab]; exact ⟨hsa, hsb⟩
      have hmem' : (1 - s).re ∈ uIcc (1 - a) (1 - b) := by
        rw [Set.uIcc_of_ge (by linarith)]; simp only [sub_re, one_re]; constructor <;> linarith
      have hP : ‖(y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1)‖ ≤ L := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_cpow_neg_le_aux hy hmem) ?_)
        have := norm_cpow_neg_le_aux hy hmem'
        rwa [show -(1 - s) = s - 1 by ring] at this
      have hG := hC s hsa hsb
      have hC0 : 0 ≤ C := by
        have h0 := (norm_nonneg _).trans hG
        have hD : 0 < (1 + s.im ^ 2) ^ K := by positivity
        have := mul_nonneg h0 hD.le
        rwa [div_mul_cancel₀ _ hD.ne'] at this
      unfold thetaSymbol
      rw [norm_mul]
      calc ‖Gammaℝ s ^ (k + 1)‖ * ‖(y : ℂ) ^ (-s) - (y : ℂ) ^ (s - 1)‖
          ≤ (C / (1 + s.im ^ 2) ^ K) * L := mul_le_mul hG hP (norm_nonneg _) (by positivity)
        _ = C * L / (1 + s.im ^ 2) ^ K := by ring
    · exact ⟨0, fun s hsa hsb => absurd (le_trans hsa hsb) hab⟩

/-- Antisymmetry: `Ψ(s) = -(Γℝ(s)/Γℝ(1-s))^{k+1} Ψ(1-s)` for `Re s < 1`. -/
theorem thetaSymbol_antisymm (k : ℕ) {y : ℝ} (s : ℂ) (h1 : s.re < 1) :
    thetaSymbol k y s = -(Gammaℝ s ^ (k + 1) / Gammaℝ (1 - s) ^ (k + 1)) * thetaSymbol k y (1 - s) := by
  have hne : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  unfold thetaSymbol
  rw [show -(1 - s) = s - 1 by ring, show 1 - s - 1 = -s by ring]
  field_simp
  ring

private theorem mellinConvergent_scaled (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (fun x : ℝ => gammaRPowKernel k (y * x)) s :=
  (MellinConvergent.comp_mul_left hy).mpr (hasMellin_gammaRPowKernel k hs).1

private theorem mellinConvergent_theta (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (thetaFunction k y) s := by
  have h1 := mellinConvergent_scaled k hy hs
  have h2 := (mellinConvergent_scaled k (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  unfold MellinConvergent at h1 h2 ⊢
  have := h1.sub h2
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, thetaFunction, smul_eq_mul]
  ring

theorem mellin_thetaFunction (k : ℕ) {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : 0 < s.re) :
    mellin (thetaFunction k y) s = thetaSymbol k y s := by
  have h1 := mellinConvergent_scaled k hy hs
  have h2 := (mellinConvergent_scaled k (inv_pos.mpr hy) hs).const_smul ((y⁻¹ : ℝ) : ℂ)
  have hsplit : mellin (thetaFunction k y) s
      = mellin (fun x : ℝ => gammaRPowKernel k (y * x)) s
        - mellin (fun x : ℝ => ((y⁻¹ : ℝ) : ℂ) • gammaRPowKernel k (y⁻¹ * x)) s := by
    unfold mellin
    rw [← integral_sub h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [thetaFunction, smul_eq_mul]; ring
  rw [hsplit, mellin_const_smul, mellin_comp_mul_left _ _ hy,
    mellin_comp_mul_left _ _ (inv_pos.mpr hy), (hasMellin_gammaRPowKernel k hs).2]
  unfold thetaSymbol
  have hyarg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_ne_zero.symm
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  simp only [smul_eq_mul, Complex.ofReal_inv]
  rw [Complex.inv_cpow _ _ hyarg, ← Complex.cpow_neg, neg_neg]
  have : (y : ℂ) ^ (s - 1) = (y : ℂ)⁻¹ * (y : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]; ring
  rw [this]; ring

/-- Mellin inversion for the theta test functions on every line `0 < c < 1`. -/
theorem mellinInv_thetaSymbol (k : ℕ) {y : ℝ} (hy : 0 < y) {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {x : ℝ} (hx : 0 < x) : mellinInv c (thetaSymbol k y) x = thetaFunction k y x := by
  have hreg := mellinRegularStrip_thetaSymbol k hy
  have hcre : 0 < ((c : ℂ)).re := by simpa using hc
  have hconv := mellinConvergent_theta k hy hcre
  have hvert : VerticalIntegrable (mellin (thetaFunction k y)) c := by
    unfold VerticalIntegrable
    refine (hreg.integrable_line hc hc1).congr (Eventually.of_forall fun t => ?_)
    show thetaSymbol k y ((c : ℂ) + t * I) = mellin (thetaFunction k y) ((c : ℂ) + t * I)
    rw [mellin_thetaFunction k hy (s := (c : ℂ) + t * I) (by simpa using hc)]
  have hcontx : ContinuousAt (thetaFunction k y) x := by
    unfold thetaFunction
    have h1 : ContinuousAt (fun x : ℝ => gammaRPowKernel k (y * x)) x :=
      ((continuousOn_gammaRPowKernel k).continuousAt (Ioi_mem_nhds (mul_pos hy hx))).comp
        (by fun_prop)
    have h2 : ContinuousAt (fun x : ℝ => gammaRPowKernel k (y⁻¹ * x)) x :=
      ((continuousOn_gammaRPowKernel k).continuousAt
        (Ioi_mem_nhds (mul_pos (inv_pos.mpr hy) hx))).comp (by fun_prop)
    exact h1.sub (continuousAt_const.mul h2)
  have hinv := mellinInv_mellin_eq c (thetaFunction k y) hx hconv hvert hcontx
  rw [← hinv]
  unfold mellinInv
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show (x : ℂ) ^ (-((c : ℂ) + t * I)) • thetaSymbol k y ((c : ℂ) + t * I)
    = (x : ℂ) ^ (-((c : ℂ) + t * I)) • mellin (thetaFunction k y) ((c : ℂ) + t * I)
  rw [mellin_thetaFunction k hy (s := (c : ℂ) + t * I) (by simpa using hc)]



/-- The Mellin variable of the degree-`d` chart `x = X^d`: `s = (w + (d-1)/2)/d`. -/
def chartArg (d : ℕ) (w : ℂ) : ℂ := (w + ((d : ℂ) - 1) / 2) / d

/-- The Voronoi multiplier of `Γℝ(s)^d` in the chart: `m_d(w) = Γℝ(s)^d / Γℝ(1-s)^d`. -/
def chartMultiplier (d : ℕ) (w : ℂ) : ℂ :=
  Gammaℝ (chartArg d w) ^ d / Gammaℝ (1 - chartArg d w) ^ d

/-- The chart symbol `d^{-1/2} Ψ((w + (d-1)/2)/d)`: Mellin transform of `√d X^{(d-1)/2} f(X^d)`. -/
def chartSymbol (d : ℕ) (Ψ : ℂ → ℂ) (w : ℂ) : ℂ := ((d : ℂ) ^ (-(1 / 2 : ℂ))) * Ψ (chartArg d w)

theorem chartArg_one_sub (d : ℕ) (hd : d ≠ 0) (w : ℂ) : chartArg d (1 - w) = 1 - chartArg d w := by
  unfold chartArg
  have : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  field_simp; ring

theorem chartSymbol_antisymm (d : ℕ) (hd : d ≠ 0) {Ψ : ℂ → ℂ} {w : ℂ}
    (hΨ : Ψ (chartArg d w) = -(Gammaℝ (chartArg d w) ^ d / Gammaℝ (1 - chartArg d w) ^ d)
      * Ψ (1 - chartArg d w)) :
    chartSymbol d Ψ w = -chartMultiplier d w * chartSymbol d Ψ (1 - w) := by
  unfold chartSymbol chartMultiplier
  rw [chartArg_one_sub d hd, hΨ]; ring

theorem norm_Gamma_abs_im (a t : ℝ) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ = ‖Complex.Gamma ((a : ℂ) + (|t| : ℝ) * I)‖ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht]
    have hconj : (a : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) ((a : ℂ) + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hconj, Complex.Gamma_conj, Complex.norm_conj]

theorem norm_gammaR (z : ℂ) : ‖Gammaℝ z‖ = Real.pi ^ (-z.re / 2) * ‖Complex.Gamma (z / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 2; simp [neg_div]

/-- **The derivative bound for the degree-`d` chart** (`d ≥ 3`): `|w m_d(w)|` is bounded on
`Re w = -1/2`. There `Re s = (d-2)/(2d)`, and Stirling gives `|Γℝ(s)/Γℝ(1-s)|^d ≍ |w|^{-1}`. -/
theorem exists_bound_mul_chartMultiplier_neg_half (d : ℕ) (hd : 3 ≤ d) :
    ∃ K : ℝ, ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  set σ : ℝ := ((d : ℝ) - 2) / (2 * d) with hσ
  have hσ0 : 0 < σ := by rw [hσ]; apply div_pos <;> linarith
  have hσ1 : σ < 1 / 2 := by rw [hσ, div_lt_iff₀ (by positivity)]; linarith
  have harg : ∀ t : ℝ, chartArg d ((-1 / 2 : ℂ) + t * I) = (σ : ℂ) + ((t / d : ℝ) : ℂ) * I := by
    intro t
    unfold chartArg
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [hσ]; push_cast; field_simp; ring
  have harg' : ∀ t : ℝ, 1 - chartArg d ((-1 / 2 : ℂ) + t * I)
      = ((1 - σ : ℝ) : ℂ) + ((-(t / d) : ℝ) : ℂ) * I := by
    intro t; rw [harg]; push_cast; ring
  -- the function to bound
  set g : ℝ → ℂ := fun t => ((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I) with hg
  -- continuity
  have hne : ∀ t : ℝ, Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I)) ≠ 0 := by
    intro t; rw [harg']; exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro t
    have hlin : Continuous fun t : ℝ => chartArg d ((-1 / 2 : ℂ) + t * I) := by
      unfold chartArg; fun_prop
    have hlin' : Continuous fun t : ℝ => 1 - chartArg d ((-1 / 2 : ℂ) + t * I) :=
      continuous_const.sub hlin
    have hc1 : ContinuousAt (fun t : ℝ => Gammaℝ (chartArg d ((-1 / 2 : ℂ) + t * I))) t := by
      have h := (differentiableAt_gammaR_of_re_pos (s := chartArg d ((-1 / 2 : ℂ) + t * I))
        (by rw [harg]; simp; exact hσ0)).continuousAt
      exact ContinuousAt.comp (g := Gammaℝ) h hlin.continuousAt
    have hc2 : ContinuousAt (fun t : ℝ => Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I))) t := by
      have h := (differentiableAt_gammaR_of_re_pos (s := 1 - chartArg d ((-1 / 2 : ℂ) + t * I))
        (by rw [harg']; simp; linarith)).continuousAt
      exact ContinuousAt.comp (g := Gammaℝ) h hlin'.continuousAt
    simp only [hg, chartMultiplier]
    exact (by fun_prop : ContinuousAt (fun t : ℝ => (-1 / 2 : ℂ) + t * I) t).mul
      ((hc1.pow d).div (hc2.pow d) (pow_ne_zero _ (hne t)))
  -- compact part
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(8 * (d : ℝ))) (b := 8 * (d : ℝ))).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B (Real.pi * Real.exp (3 / 4 * d) * (2 * d + 1)), fun t => ?_⟩
  rcases le_or_gt |t| (8 * d) with ht | ht
  · exact (hB t (abs_le.mp ht)).trans (le_max_left _ _)
  refine le_trans ?_ (le_max_right _ _)
  set y : ℝ := |t| / (2 * d) with hy
  have hy4 : 4 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  have hy0 : 0 < y := by linarith
  -- the Gamma ratio
  have hratio : ‖Complex.Gamma ((σ / 2 : ℝ) + (y : ℂ) * I)‖
      ≤ y ^ (σ - 1 / 2) * Real.exp (3 / 4) * ‖Complex.Gamma (((1 - σ) / 2 : ℝ) + (y : ℂ) * I)‖ := by
    have h := norm_Gamma_vertical_le_rpow_mul (a := σ / 2) (b := (1 - σ) / 2) (y := y)
      (by positivity) (by linarith) hy4
    have he : Real.exp (6 * ((1 - σ) / 2 - σ / 2) / y) ≤ Real.exp (3 / 4) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ hy0]; nlinarith
    have hrp : 0 ≤ y ^ (σ / 2 - (1 - σ) / 2) := Real.rpow_nonneg hy0.le _
    calc _ ≤ y ^ (σ / 2 - (1 - σ) / 2) * Real.exp (6 * ((1 - σ) / 2 - σ / 2) / y) *
          ‖Complex.Gamma (((1 - σ) / 2 : ℝ) + (y : ℂ) * I)‖ := h
      _ ≤ y ^ (σ / 2 - (1 - σ) / 2) * Real.exp (3 / 4) *
          ‖Complex.Gamma (((1 - σ) / 2 : ℝ) + (y : ℂ) * I)‖ := by gcongr
      _ = _ := by congr 3; ring
  have hden_pos : 0 < ‖Complex.Gamma (((1 - σ) / 2 : ℝ) + (y : ℂ) * I)‖ := by
    rw [norm_pos_iff]; apply Complex.Gamma_ne_zero_of_re_pos; simp; linarith
  -- norms of the two `Γℝ` factors
  have hnum : ‖Gammaℝ (chartArg d ((-1 / 2 : ℂ) + t * I))‖
      = Real.pi ^ (-σ / 2) * ‖Complex.Gamma ((σ / 2 : ℝ) + (y : ℂ) * I)‖ := by
    rw [norm_gammaR, harg]
    have e : ((σ : ℂ) + ((t / d : ℝ) : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / (2 * d) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e, norm_Gamma_abs_im]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    congr 3
    rw [hy, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * d)]
  have hden : ‖Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I))‖
      = Real.pi ^ (-(1 - σ) / 2) * ‖Complex.Gamma (((1 - σ) / 2 : ℝ) + (y : ℂ) * I)‖ := by
    rw [norm_gammaR, harg']
    have e : (((1 - σ : ℝ) : ℂ) + ((-(t / d) : ℝ) : ℂ) * I) / 2
        = (((1 - σ) / 2 : ℝ) : ℂ) + ((-(t / (2 * d)) : ℝ) : ℂ) * I := by push_cast; ring
    rw [e, norm_Gamma_abs_im]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    congr 3
    rw [hy, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * d)]
  -- the single ratio
  have hpi : Real.pi ^ (-σ / 2) / Real.pi ^ (-(1 - σ) / 2) = Real.pi ^ (1 / (d : ℝ)) := by
    rw [← Real.rpow_sub Real.pi_pos]; congr 1; rw [hσ]; field_simp; ring
  have hR : ‖Gammaℝ (chartArg d ((-1 / 2 : ℂ) + t * I))‖ / ‖Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I))‖
      ≤ Real.pi ^ (1 / (d : ℝ)) * (y ^ (σ - 1 / 2) * Real.exp (3 / 4)) := by
    rw [hnum, hden, mul_div_mul_comm, hpi]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [div_le_iff₀ hden_pos]; linarith [hratio]
  have hR0 : 0 ≤ ‖Gammaℝ (chartArg d ((-1 / 2 : ℂ) + t * I))‖ / ‖Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I))‖ :=
    by positivity
  have hpow : (Real.pi ^ (1 / (d : ℝ)) * (y ^ (σ - 1 / 2) * Real.exp (3 / 4))) ^ d
      = Real.pi * Real.exp (3 / 4 * d) * y⁻¹ := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (Real.pi ^ (1 / (d : ℝ))), ← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_natCast (y ^ (σ - 1 / 2)), ← Real.rpow_mul hy0.le, ← Real.exp_nat_mul]
    have e1 : 1 / (d : ℝ) * (d : ℝ) = 1 := by field_simp
    have e2 : (σ - 1 / 2) * (d : ℝ) = -1 := by rw [hσ]; field_simp; ring
    rw [e1, e2, Real.rpow_one, Real.rpow_neg_one]; ring_nf
  have hw : ‖(-1 / 2 : ℂ) + t * I‖ ≤ (2 * d + 1) * y := by
    have h1 : ‖(-1 / 2 : ℂ) + t * I‖ ≤ 1 / 2 + |t| := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      simp [Complex.norm_real]
    have h2 : |t| = 2 * d * y := by rw [hy]; field_simp
    rw [h2] at h1; nlinarith
  calc ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖
      = ‖(-1 / 2 : ℂ) + t * I‖ * (‖Gammaℝ (chartArg d ((-1 / 2 : ℂ) + t * I))‖ /
          ‖Gammaℝ (1 - chartArg d ((-1 / 2 : ℂ) + t * I))‖) ^ d := by
        rw [norm_mul, chartMultiplier, norm_div, norm_pow, norm_pow, div_pow]
    _ ≤ ((2 * d + 1) * y) * (Real.pi * Real.exp (3 / 4 * d) * y⁻¹) := by
        rw [← hpow]
        exact mul_le_mul hw (pow_le_pow_left₀ hR0 hR d) (by positivity) (by positivity)
    _ = Real.pi * Real.exp (3 / 4 * d) * (2 * d + 1) := by field_simp


/-- **Derivative bound for antisymmetric symbols.** If `Φ` is regular on `-1 < Re w < 2`, `Φ(w) = -m(w)Φ(1-w)` there, and `|u m(u)| ≤ K` on `Re u = -1/2`, then
`∫|F'|² ≤ K² ∫X²|F|²` for `F = Mellin⁻¹_{1/2}Φ`, `F'(X) = X⁻¹Mellin⁻¹(-wΦ)(X)`. -/
theorem integral_norm_sq_deriv_le_of_antisymm (m : ℂ → ℂ) {Φ : ℂ → ℂ} (hΦ : MellinRegularStrip Φ (-1) 2)
    (hanti : ∀ w : ℂ, -1 < w.re → w.re < 2 → Φ w = -m w * Φ (1 - w))
    {K : ℝ} (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * m ((-1 / 2 : ℂ) + t * I)‖ ≤ K) :
    ∫ x in Ioi (0 : ℝ), ‖((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x‖ ^ 2
      ≤ K ^ 2 * ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2 := by
  have hdΦ : MellinRegularStrip (fun w => -w * Φ w) (-1) 2 := by
    have h := hΦ.mul_id
    refine ⟨fun s h1 h2 => (h.diff s h1 h2).neg.congr_of_eventuallyEq
      (Eventually.of_forall fun z => by simp only [Pi.neg_apply]; ring), fun a b ha hb k => ?_⟩
    obtain ⟨C, hC⟩ := h.decay a b ha hb k
    exact ⟨C, fun s h1 h2 => by simpa [neg_mul, norm_neg] using hC s h1 h2⟩
  -- left side: Plancherel at `-1/2`
  have hL : ∫ x in Ioi (0 : ℝ), ‖((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x‖ ^ 2
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    rw [← integral_norm_sq_mellinInv (Ψ := fun w => -w * Φ w) (σ := -1 / 2)
      (hdΦ.integrable_line (c := -1 / 2) (by norm_num) (by norm_num))
      (hdΦ.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [hdΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := -1 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx']
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx', mul_pow]
    have : x ^ (2 * (-1 / 2 : ℝ) - 1) = (x ^ 2)⁻¹ := by
      rw [show 2 * (-1 / 2 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx'.le]; norm_cast
    rw [this, inv_pow]; ring
  -- right side: Plancherel at `3/2`
  have hR : ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    rw [← integral_norm_sq_mellinInv (Ψ := Φ) (σ := 3 / 2)
      (hΦ.integrable_line (c := 3 / 2) (by norm_num) (by norm_num))
      (hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    rw [hΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := 3 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx']
    congr 1
    rw [show 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) by norm_num, Real.rpow_natCast]
  rw [hL, hR]
  -- pointwise comparison on the lines
  have hpt : ∀ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 := by
    intro t
    set u : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I with hu
    have hre1 : -1 < u.re := by simp [hu]; norm_num
    have hre2 : u.re < 2 := by simp [hu]; norm_num
    have h1u : 1 - u = ((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I := by rw [hu]; push_cast; ring
    have hbound := hK t
    have hu' : ((-1 / 2 : ℂ) + t * I) = u := by rw [hu]; push_cast; ring
    rw [hu'] at hbound
    simp only
    rw [hanti u hre1 hre2, h1u]
    have hK0 : 0 ≤ K := le_trans (norm_nonneg _) hbound
    calc ‖-u * (-m u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I))‖ ^ 2
        = (‖u * m u‖ * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖) ^ 2 := by
          rw [show -u * (-m u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I))
            = u * m u * Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I) by ring, norm_mul]
      _ ≤ (K * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖) ^ 2 := by
          gcongr
      _ = K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 := by ring
  have hint1 : Integrable fun t : ℝ => ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    have := hdΦ.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num)
    exact (memLp_two_iff_integrable_sq_norm this.1).mp this
  have hint2 : Integrable fun t : ℝ => ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 := by
    have := hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num)
    exact (memLp_two_iff_integrable_sq_norm this.1).mp this
  have hneg : ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2
      = ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 :=
    integral_neg_eq_self (fun t : ℝ => ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) volume
  have hmono : ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ ∫ t : ℝ, K ^ 2 * ‖Φ (((3 / 2 : ℝ) : ℂ) + (-t : ℝ) * I)‖ ^ 2 :=
    integral_mono hint1 ((hint2.comp_neg).const_mul _) hpt
  rw [integral_const_mul, hneg] at hmono
  have h2π : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc 1 / (2 * Real.pi) * ∫ t : ℝ, ‖(fun w => -w * Φ w) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      ≤ 1 / (2 * Real.pi) * (K ^ 2 * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono h2π
    _ = K ^ 2 * (1 / (2 * Real.pi) * ∫ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2) := by ring


theorem re_chartArg (d : ℕ) (w : ℂ) : (chartArg d w).re = (w.re + ((d : ℝ) - 1) / 2) / d := by
  unfold chartArg
  rw [show (w + ((d : ℂ) - 1) / 2) / (d : ℂ) = (w + ((d : ℂ) - 1) / 2) * ((1 / (d : ℝ) : ℝ) : ℂ) by
    push_cast; ring]
  rw [Complex.re_mul_ofReal]; simp; ring

/-- Chart symbols of regular symbols on `0 < Re s < 1` are regular on `-1 < Re w < 2` (`d ≥ 3`). -/
theorem mellinRegularStrip_chartSymbol {d : ℕ} (hd : 3 ≤ d) {Ψ : ℂ → ℂ}
    (h : MellinRegularStrip Ψ 0 1) : MellinRegularStrip (chartSymbol d Ψ) (-1) 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hre : ∀ w : ℂ, (chartArg d w).re = (w.re + ((d : ℝ) - 1) / 2) / d := by
    intro w; unfold chartArg
    rw [show (w + ((d : ℂ) - 1) / 2) / (d : ℂ) = (w + ((d : ℂ) - 1) / 2) * ((1 / (d : ℝ) : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.re_mul_ofReal]; simp; ring
  have him : ∀ w : ℂ, (chartArg d w).im = w.im / d := by
    intro w; unfold chartArg
    rw [show (w + ((d : ℂ) - 1) / 2) / (d : ℂ) = (w + ((d : ℂ) - 1) / 2) * ((1 / (d : ℝ) : ℝ) : ℂ) by
      push_cast; ring]
    rw [Complex.im_mul_ofReal]; simp; ring
  have hlo : ∀ a : ℝ, -1 < a → 0 < (a + ((d : ℝ) - 1) / 2) / d := by
    intro a ha; apply div_pos _ hd0; linarith
  have hhi : ∀ b : ℝ, b < 2 → (b + ((d : ℝ) - 1) / 2) / d < 1 := by
    intro b hb; rw [div_lt_one hd0]; linarith
  refine ⟨fun w h1 h2 => ?_, fun a b ha hb K => ?_⟩
  · have hs1 : 0 < (chartArg d w).re := by rw [hre]; exact hlo _ h1
    have hs2 : (chartArg d w).re < 1 := by rw [hre]; exact hhi _ h2
    have hdiff : DifferentiableAt ℂ (chartArg d) w := by unfold chartArg; fun_prop
    exact (h.diff _ hs1 hs2).comp w hdiff |>.const_mul _
  · obtain ⟨C, hC⟩ := h.decay ((a + ((d : ℝ) - 1) / 2) / d) ((b + ((d : ℝ) - 1) / 2) / d)
      (hlo a ha) (hhi b hb) K
    refine ⟨‖((d : ℂ) ^ (-(1 / 2 : ℂ)))‖ * ((d : ℝ) ^ 2) ^ K * max C 0, fun w h1 h2 => ?_⟩
    have hΨ := hC (chartArg d w) (by rw [hre]; gcongr) (by rw [hre]; gcongr)
    rw [him] at hΨ
    have hden : 0 < (1 + (w.im / d) ^ 2) ^ K := by positivity
    have hcmp : (1 + w.im ^ 2) ^ K ≤ ((d : ℝ) ^ 2) ^ K * (1 + (w.im / d) ^ 2) ^ K := by
      rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity)
      have : (d : ℝ) ^ 2 * (1 + (w.im / d) ^ 2) = (d : ℝ) ^ 2 + w.im ^ 2 := by field_simp
      rw [this]; nlinarith
    have hq : ‖Ψ (chartArg d w)‖ ≤ ((d : ℝ) ^ 2) ^ K * max C 0 / (1 + w.im ^ 2) ^ K := by
      refine hΨ.trans ?_
      rw [div_le_div_iff₀ hden (by positivity)]
      have h0 : 0 ≤ max C 0 := le_max_right _ _
      calc C * (1 + w.im ^ 2) ^ K ≤ max C 0 * (((d : ℝ) ^ 2) ^ K * (1 + (w.im / d) ^ 2) ^ K) :=
            mul_le_mul (le_max_left _ _) hcmp (by positivity) h0
        _ = _ := by ring
    unfold chartSymbol
    rw [norm_mul, mul_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)

/-- The degree-`d` chart of a function: `(Uf)(X) = √d X^{(d-1)/2} f(X^d)`. -/
def chartFun (d : ℕ) (f : ℝ → ℂ) (X : ℝ) : ℂ :=
  ((Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) : ℝ) : ℂ) * f (X ^ d)

/-- **The chart identity:** `Mellin⁻¹_{1/2}(chartSymbol d Ψ)(X) = √d X^{(d-1)/2} Mellin⁻¹_{1/2}Ψ(X^d)`. -/
theorem mellinInv_chartSymbol {d : ℕ} (hd : 0 < d) (Ψ : ℂ → ℂ) {X : ℝ} (hX : 0 < X) :
    mellinInv (1 / 2) (chartSymbol d Ψ) X = chartFun d (mellinInv (1 / 2) Ψ) X := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hxd : 0 < X ^ d := pow_pos hX d
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hxd0 : ((X ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxd.ne'
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hlogd : Complex.log (d : ℂ) = ((Real.log d : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hd0.le, Complex.ofReal_natCast]
  have hlogX : Complex.log X = ((Real.log X : ℝ) : ℂ) := (Complex.ofReal_log hX.le).symm
  have hlogx : Complex.log ((X ^ d : ℝ) : ℂ) = (((d : ℝ) * Real.log X : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hxd.le, Real.log_pow]
  set g : ℝ → ℂ := fun t => (X : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + t * I)) •
    chartSymbol d Ψ (((1 / 2 : ℝ) : ℂ) + t * I) with hg
  have hsub := Measure.integral_comp_mul_left g (d : ℝ)
  have hint : ∫ t : ℝ, g t = (d : ℂ) * ∫ τ : ℝ, g (d * τ) := by
    rw [hsub, abs_inv, abs_of_pos hd0, Complex.real_smul]
    push_cast; field_simp
  unfold chartFun mellinInv
  rw [show (∫ y : ℝ, (X : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + y * I)) •
      chartSymbol d Ψ (((1 / 2 : ℝ) : ℂ) + y * I)) = ∫ t : ℝ, g t from rfl, hint]
  have hpt : ∀ τ : ℝ, (d : ℂ) * g (d * τ) =
      ((Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) : ℝ) : ℂ) *
        (((X ^ d : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + τ * I)) • Ψ (((1 / 2 : ℝ) : ℂ) + τ * I)) := by
    intro τ
    have harg : chartArg d (((1 / 2 : ℝ) : ℂ) + ((d * τ : ℝ) : ℂ) * I) = ((1 / 2 : ℝ) : ℂ) + τ * I := by
      unfold chartArg; push_cast; field_simp; ring
    simp only [hg, chartSymbol, smul_eq_mul]
    rw [harg]
    have esq : ((Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) : ℝ) : ℂ)
        = Complex.exp ((((1 / 2) * Real.log d + (((d : ℝ) - 1) / 2) * Real.log X : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_exp, Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hd0,
        Real.rpow_def_of_pos hX]
      push_cast; ring_nf
    have ed : (d : ℂ) = Complex.exp ((Real.log d : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log hd0]; norm_cast
    rw [esq, Complex.cpow_def_of_ne_zero hX0, Complex.cpow_def_of_ne_zero hdC,
      Complex.cpow_def_of_ne_zero hxd0, hlogd, hlogX, hlogx]
    rw [show (d : ℂ) * (Complex.exp (((Real.log X : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + ((d * τ : ℝ) : ℂ) * I))
        * (Complex.exp (((Real.log d : ℝ) : ℂ) * -(1 / 2 : ℂ)) * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I)))
        = Complex.exp ((Real.log d : ℝ) + ((Real.log X : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + ((d * τ : ℝ) : ℂ) * I)
          + ((Real.log d : ℝ) : ℂ) * -(1 / 2 : ℂ)) * Ψ (((1 / 2 : ℝ) : ℂ) + τ * I) by
      rw [Complex.exp_add, Complex.exp_add, ← ed]; ring]
    rw [show Complex.exp ((((1 / 2) * Real.log d + (((d : ℝ) - 1) / 2) * Real.log X : ℝ) : ℂ)) *
        (Complex.exp ((((d : ℝ) * Real.log X : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + τ * I)) *
          Ψ (((1 / 2 : ℝ) : ℂ) + τ * I))
        = Complex.exp ((((1 / 2) * Real.log d + (((d : ℝ) - 1) / 2) * Real.log X : ℝ) : ℂ)
          + (((d : ℝ) * Real.log X : ℝ) : ℂ) * -(((1 / 2 : ℝ) : ℂ) + τ * I)) *
          Ψ (((1 / 2 : ℝ) : ℂ) + τ * I) by rw [Complex.exp_add]; ring]
    congr 2
    push_cast; ring
  rw [show (d : ℂ) * ∫ τ : ℝ, g (d * τ) = ∫ τ : ℝ, (d : ℂ) * g (d * τ) from
    (integral_const_mul _ _).symm]
  simp_rw [hpt]
  rw [integral_const_mul]
  simp only [smul_eq_mul, Complex.real_smul]
  ring

/-- Antisymmetric degree-`d` chart functions: `F = Mellin⁻¹_{1/2} Φ` on `(0,∞)` with `Φ` regular on
`-1 < Re w < 2` and `Φ(w) = -m_d(w) Φ(1-w)`. -/
def IsAntiChart (d : ℕ) (F : ℝ → ℂ) : Prop :=
  ∃ Φ : ℂ → ℂ, MellinRegularStrip Φ (-1) 2 ∧
    (∀ w : ℂ, -1 < w.re → w.re < 2 → Φ w = -chartMultiplier d w * Φ (1 - w)) ∧
    ∀ X : ℝ, 0 < X → F X = mellinInv (1 / 2) Φ X

/-- Decay faster than every power at infinity. -/
def RapidDecay (F : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ X : ℝ, 1 ≤ X → ‖F X‖ ≤ C * X ^ (-(N : ℝ))

/-- The space of rapidly decaying antisymmetric degree-`d` chart functions. -/
def antiChartSpace (d : ℕ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {F | IsAntiChart d F ∧ RapidDecay F}
  zero_mem' := ⟨⟨fun _ => 0, MellinRegularStrip.zero, fun w _ _ => by simp,
    fun X _ => by simp [mellinInv]⟩, fun N => ⟨0, fun X _ => by simp⟩⟩
  add_mem' := by
    rintro F G ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩ ⟨⟨Γ, hΓ, haΓ, hGΓ⟩, hdG⟩
    refine ⟨⟨fun s => Φ s + Γ s, hΦ.add hΓ, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2, haΓ w h1 h2]; ring
    · rw [mellinInv_add hΦ hΓ (by norm_num) (by norm_num) hX, Pi.add_apply, hFΦ X hX, hGΓ X hX]
    · obtain ⟨C₁, hC₁⟩ := hdF N
      obtain ⟨C₂, hC₂⟩ := hdG N
      refine ⟨C₁ + C₂, fun X hX => ?_⟩
      calc ‖(F + G) X‖ ≤ ‖F X‖ + ‖G X‖ := norm_add_le _ _
        _ ≤ C₁ * X ^ (-(N : ℝ)) + C₂ * X ^ (-(N : ℝ)) := add_le_add (hC₁ X hX) (hC₂ X hX)
        _ = (C₁ + C₂) * X ^ (-(N : ℝ)) := by ring
  smul_mem' := by
    rintro c F ⟨⟨Φ, hΦ, haΦ, hFΦ⟩, hdF⟩
    refine ⟨⟨fun s => c * Φ s, hΦ.const_mul c, fun w h1 h2 => ?_, fun X hX => ?_⟩, fun N => ?_⟩
    · simp only [haΦ w h1 h2]; ring
    · rw [mellinInv_const_mul, Pi.smul_apply, smul_eq_mul, hFΦ X hX]
    · obtain ⟨C, hC⟩ := hdF N
      refine ⟨‖c‖ * C, fun X hX => ?_⟩
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC X hX) (norm_nonneg c)

/-- **Analytic package.** `F' = X⁻¹ Mellin⁻¹(-wΦ)` is the derivative of `F` on `(0,∞)` and is
continuous there; `X²|F|²` and `|F'|²` are integrable; `∫|F'|² ≤ K²∫X²|F|²`. -/
theorem IsAntiChart.analytic {d : ℕ} {K : ℝ}
    (hK : ∀ t : ℝ, ‖((-1 / 2 : ℂ) + t * I) * chartMultiplier d ((-1 / 2 : ℂ) + t * I)‖ ≤ K)
    {F : ℝ → ℂ} (hF : IsAntiChart d F) :
    ∃ F' : ℝ → ℂ, (∀ x, 0 < x → HasDerivAt F (F' x) x) ∧ ContinuousOn F' (Ioi 0) ∧
      IntegrableOn (fun x => x ^ 2 * ‖F x‖ ^ 2) (Ioi 0) ∧
      IntegrableOn (fun x => ‖F' x‖ ^ 2) (Ioi 0) ∧
      ∫ x in Ioi 0, ‖F' x‖ ^ 2 ≤ K ^ 2 * ∫ x in Ioi 0, x ^ 2 * ‖F x‖ ^ 2 := by
  obtain ⟨Φ, hΦ, hanti, hFeq⟩ := hF
  have hG : MellinRegularStrip (fun w => -w * Φ w) (-1) 2 := by
    have h := (hΦ.mul_id).const_mul (-1)
    have e : (fun s => -1 * (s * Φ s)) = fun w => -w * Φ w := by funext s; ring
    rwa [e] at h
  refine ⟨fun x => ((x : ℂ))⁻¹ * mellinInv (1 / 2) (fun w => -w * Φ w) x, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hΦ.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num) hx
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hFeq y hy
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have h := (hG.hasDerivAt_mellinInv (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
      hx').continuousAt
    have hinv : ContinuousAt (fun x : ℝ => ((x : ℂ))⁻¹) x :=
      (Complex.continuous_ofReal.continuousAt).inv₀ (by exact_mod_cast hx'.ne')
    exact (hinv.mul h).continuousWithinAt
  · have h := integrableOn_norm_sq_mellinInv (Ψ := Φ) (σ := 3 / 2)
      (hΦ.integrable_line (c := 3 / 2) (by norm_num) (by norm_num))
      (hΦ.memLp_two_line (c := 3 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hFeq x hx', hΦ.mellinInv_eq (c₁ := 1 / 2) (c₂ := 3 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', show 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
    ring
  · have h := integrableOn_norm_sq_mellinInv (Ψ := fun w => -w * Φ w) (σ := -1 / 2)
      (hG.integrable_line (c := -1 / 2) (by norm_num) (by norm_num))
      (hG.memLp_two_line (c := -1 / 2) (by norm_num) (by norm_num))
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx' : (0 : ℝ) < x := hx
    beta_reduce
    rw [hG.mellinInv_eq (c₁ := -1 / 2) (c₂ := 1 / 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hx', norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx', mul_pow, show 2 * (-1 / 2 : ℝ) - 1 = -2 by norm_num, Real.rpow_neg hx'.le]
    norm_cast
    ring
  · have h := integral_norm_sq_deriv_le_of_antisymm (chartMultiplier d) hΦ hanti hK
    have e : ∫ x in Ioi (0 : ℝ), x ^ 2 * ‖F x‖ ^ 2
        = ∫ x in Ioi (0 : ℝ), ‖mellinInv (1 / 2) Φ x‖ ^ 2 * x ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [hFeq x hx]; ring
    rw [e]
    exact h

/-- The degree-`(k+1)` charts of the theta test functions `K_k(yx) - y⁻¹K_k(x/y)` belong to the
antisymmetric chart space (`k ≥ 2`). -/
theorem chartFun_thetaFunction_mem {k : ℕ} (hk : 2 ≤ k) {y : ℝ} (hy : 0 < y) :
    chartFun (k + 1) (thetaFunction k y) ∈ antiChartSpace (k + 1) := by
  have hd : 3 ≤ k + 1 := by omega
  have hd0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  refine ⟨⟨chartSymbol (k + 1) (thetaSymbol k y),
    mellinRegularStrip_chartSymbol hd (mellinRegularStrip_thetaSymbol k hy),
    fun w h1 h2 => chartSymbol_antisymm (k + 1) (by omega)
      (thetaSymbol_antisymm k _ (by
        rw [re_chartArg, div_lt_one hd0]
        have : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [this]
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith)),
    fun X hX => ?_⟩, fun N => ?_⟩
  · rw [mellinInv_chartSymbol (by omega) _ hX]
    unfold chartFun
    rw [mellinInv_thetaSymbol k hy (by norm_num) (by norm_num) (pow_pos hX _)]
  · set d : ℕ := k + 1 with hdd
    set c : ℝ := ((N : ℝ) + ((d : ℝ) - 1) / 2) / d with hc
    have hc0 : 0 < c := by
      rw [hc]; apply div_pos _ hd0
      have : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    obtain ⟨C, hC⟩ := exists_norm_gammaRPowKernel_le k hc0
    have hC0 : 0 ≤ C := by
      have := (norm_nonneg _).trans (hC 1 one_pos)
      simpa using this
    set D : ℝ := Real.sqrt d * (C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c))) with hD
    refine ⟨D, fun X hX => ?_⟩
    have hX0 : 0 < X := by linarith
    have hx : 0 < X ^ d := pow_pos hX0 d
    have hth : ‖thetaFunction k y (X ^ d)‖ ≤ C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * (X ^ d) ^ (-c) := by
      unfold thetaFunction
      have h1 := hC (y * X ^ d) (mul_pos hy hx)
      have h2 := hC (y⁻¹ * X ^ d) (mul_pos (inv_pos.mpr hy) hx)
      rw [Real.mul_rpow hy.le hx.le] at h1
      rw [Real.mul_rpow (inv_pos.mpr hy).le hx.le] at h2
      calc ‖gammaRPowKernel k (y * X ^ d) - ((y⁻¹ : ℝ) : ℂ) * gammaRPowKernel k (y⁻¹ * X ^ d)‖
          ≤ ‖gammaRPowKernel k (y * X ^ d)‖ + y⁻¹ * ‖gammaRPowKernel k (y⁻¹ * X ^ d)‖ := by
            refine (norm_sub_le _ _).trans (le_of_eq ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy)]
        _ ≤ C * (y ^ (-c) * (X ^ d) ^ (-c)) + y⁻¹ * (C * (y⁻¹ ^ (-c) * (X ^ d) ^ (-c))) :=
            add_le_add h1 (mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hy).le)
        _ = _ := by ring
    have hpow : X ^ (((d : ℝ) - 1) / 2) * (X ^ d) ^ (-c) = X ^ (-(N : ℝ)) := by
      rw [← Real.rpow_natCast X d, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
      congr 1; rw [hc]; field_simp; ring
    unfold chartFun
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt d * X ^ (((d : ℝ) - 1) / 2))]
    calc Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) * ‖thetaFunction k y (X ^ d)‖
        ≤ Real.sqrt d * X ^ (((d : ℝ) - 1) / 2) *
            (C * (y ^ (-c) + y⁻¹ * y⁻¹ ^ (-c)) * (X ^ d) ^ (-c)) :=
          mul_le_mul_of_nonneg_left hth (by positivity)
      _ = D * (X ^ (((d : ℝ) - 1) / 2) * (X ^ d) ^ (-c)) := by rw [hD]; ring
      _ = D * X ^ (-(N : ℝ)) := by rw [hpow]

end RHTower.GammaRPowTwins
