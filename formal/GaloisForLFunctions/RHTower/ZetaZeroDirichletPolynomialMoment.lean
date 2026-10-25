import GaloisForLFunctions.RHTower.ZetaSmoothedZeroCount

/-!
# Dirichlet polynomials summed over the zeros of `ζ`

For a `C²` profile `w` supported in `[−1, 1]`, coefficients `a_n` and `Y + 2 ≤ T`,

`Σ_ρ m_ρ ŵ(γ_ρ/T) Σ_{n≤Y} a_n n^{−(ρ−½)} = a_1 (T w(0) log T + c_w T) − T w(0) Σ_{2≤n≤Y} a_n Λ(n)/√n
  + O(Σ_n |a_n| (√n + √T))`

over all nontrivial zeros with multiplicity (`exists_zeroSum_dirichletPolynomial_le`): a smoothed
form of Gonek's lemma `Σ_γ x^{−ρ} ≈ −(T/2π) Λ(x)/x`.  The `n = 1` term is the smoothed zero count
(`exists_smoothedZeroCount`); for `n ≥ 2` the factor `n^{−(ρ−½)} ŵ(γ_ρ/T)` is the transform of the
Landau test centred at `−log n`, whose zero sum equals that of the reflected test centred at
`log n` (`zeroSum_comp_neg`: Weil's right-hand side is invariant under `u ↦ −u` since `μ` is even),
and the smoothed Landau formula applies to the reflected profile.
-/

open Complex MeasureTheory Real Set
open scoped Real

noncomputable section

namespace RHTower

open Zeta23

/-! ## Reflection of the test function -/

/-- `h_{k(−·)}(z) = h_k(−z)`. -/
lemma paperFT_comp_neg (k : ℝ → ℂ) (z : ℂ) : paperFT (fun u => k (-u)) z = paperFT k (-z) := by
  unfold paperFT
  rw [← integral_neg_eq_self (fun u : ℝ => k u * Complex.exp (I * -z * (u : ℂ))) volume]
  congr 1; funext u
  push_cast; ring_nf

/-- Weil's right-hand side is invariant under reflecting the test, because `μ` is even. -/
lemma literatureRHS_comp_neg (k : ℝ → ℂ) :
    EF.literatureRHS (fun u => k (-u)) = EF.literatureRHS k := by
  unfold EF.literatureRHS
  rw [EF.gamma_term, EF.gamma_term]
  simp only [paperFT_comp_neg, neg_neg]
  have hp : paperFT k (-(I / 2)) + paperFT k (-(-I / 2)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    rw [show -(I / 2) = -I / 2 by ring, show -(-I / 2) = I / 2 by ring, add_comm]
  have hn : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (k (-Real.log n) + k (Real.log n))) = ∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    congr 1; funext n; rw [add_comm (k (-Real.log n))]
  have hg : (∫ τ : ℝ, paperFT k (-(τ : ℂ)) * (mu τ : ℂ)) = ∫ τ : ℝ, paperFT k τ * (mu τ : ℂ) := by
    rw [← integral_neg_eq_self (fun τ : ℝ => paperFT k τ * (mu τ : ℂ)) volume]
    congr 1; funext τ
    rw [gammaFacts.even, ofReal_neg]
  rw [hp, hn, hg]

/-- Reflecting the test leaves the zero sum unchanged. -/
lemma zeroSum_comp_neg {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hk' : ContDiff ℝ 2 (fun u => k (-u))) (hkc' : HasCompactSupport (fun u => k (-u))) :
    (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT (fun u => k (-u)) (gammaOf ρ)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT k (gammaOf ρ) := by
  rw [(Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hk' hkc').2,
    (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hk hkc).2, literatureRHS_comp_neg]

/-! ## The Landau formula at `−log x` -/

section Moment

variable {w : ℝ → ℂ}

lemma reflect_contDiff_supp (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ContDiff ℝ 2 (fun u => w (-u)) ∧ ∀ u, w (-u) ≠ 0 → |u| ≤ 1 :=
  ⟨hw.comp contDiff_neg, fun u hu => by simpa [abs_neg] using hsupp (-u) hu⟩

lemma landauTest_neg (w : ℝ → ℂ) (T y : ℝ) :
    landauTest w T (-y) = fun u => landauTest (fun v => w (-v)) T y (-u) := by
  funext u; unfold landauTest; congr 2; ring

/-- **Landau formula at `−log x`**: `|Σ_ρ m_ρ x^{−(ρ−½)} ŵ(γ_ρ/T) + T w(0) Λ(x)/√x| ≤
K(√x + √T / log x)` for integers `x ≥ 2` and `T ≥ x + 2`. -/
theorem exists_smoothedLandau_neg_le (hw : ContDiff ℝ 2 w) (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 2 ≤ x → ∀ T : ℝ, (x : ℝ) + 2 ≤ T →
      ‖(∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
          paperFT (landauTest w T (-Real.log x)) (gammaOf ρ)) +
        ((ArithmeticFunction.vonMangoldt x / Real.sqrt x : ℝ) : ℂ) * ((T : ℂ) * w 0)‖ ≤
        K * (Real.sqrt x + Real.sqrt T / Real.log x) := by
  obtain ⟨hw', hsupp'⟩ := reflect_contDiff_supp hw hsupp
  obtain ⟨K, hK⟩ := exists_smoothedLandau_le hw' hsupp'
  set c := 2 * Real.exp (1 / 2) * ∫ u, ‖w (-u)‖
  have hc : 0 ≤ c := by positivity
  refine ⟨max c K, le_max_of_le_left hc, fun x hx T hT => ?_⟩
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  obtain ⟨hkd, hkc⟩ := landauTest_contDiff_hasCompactSupport hw' hsupp' hTpos (Real.log x)
  obtain ⟨hkd', hkc'⟩ := landauTest_contDiff_hasCompactSupport hw hsupp hTpos (-Real.log x)
  rw [landauTest_neg] at hkd' hkc' ⊢
  rw [zeroSum_comp_neg hkd hkc hkd' hkc']
  have h := hK x hx T hT
  simp only [neg_zero] at h
  refine h.trans ?_
  have h1 : c * Real.sqrt x ≤ max c K * Real.sqrt x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
  have h2 : K * Real.sqrt T / Real.log x ≤ max c K * (Real.sqrt T / Real.log x) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  linarith

/-- `n^{−(ρ−½)} ŵ(γ_ρ/T)` is the transform of the Landau test at `−log n`. -/
lemma paperFT_landauTest_neg_log {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : n ≠ 0) (ρ : ℂ) :
    paperFT (landauTest w T (-Real.log n)) (gammaOf ρ) =
      paperFT w (gammaOf ρ / T) * (n : ℂ) ^ (-(ρ - 1 / 2)) := by
  rw [paperFT_landauTest w hT, mul_comm,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  congr 1; congr 1
  have hI : I * gammaOf ρ = ρ - 1 / 2 := by
    unfold gammaOf; field_simp
  simp only [Complex.natCast_log]
  linear_combination (-(Complex.log n)) * hI

/-- **Dirichlet polynomials over the zeros (smoothed Gonek lemma).**  For coefficients `a_n`,
`1 ≤ Y` and `T ≥ max 2 (Y + 2)`, over all nontrivial zeros with multiplicity,
`|Σ_ρ m_ρ ŵ(γ_ρ/T) Σ_{n≤Y} a_n n^{−(ρ−½)} − (a_1 (T w(0) log T + c_w T) −
T w(0) Σ_{2≤n≤Y} a_n Λ(n)/√n)| ≤ K Σ_{n≤Y} |a_n|(√n + √T)`. -/
theorem exists_zeroSum_dirichletPolynomial_le (hw : ContDiff ℝ 2 w)
    (hsupp : ∀ u, w u ≠ 0 → |u| ≤ 1) :
    ∃ K : ℝ, ∀ (a : ℕ → ℂ) (Y : ℕ), 1 ≤ Y → ∀ T : ℝ, 2 ≤ T → (Y : ℝ) + 2 ≤ T →
      ‖(∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * paperFT w (gammaOf ρ / T) *
          ∑ n ∈ Finset.Icc 1 Y, a n * (n : ℂ) ^ (-((ρ : ℂ) - 1 / 2))) -
        (a 1 * ((T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w) -
          (T : ℂ) * w 0 * ∑ n ∈ Finset.Icc 2 Y,
            a n * ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ))‖ ≤
        K * ∑ n ∈ Finset.Icc 1 Y, ‖a n‖ * (Real.sqrt n + Real.sqrt T) := by
  obtain ⟨K₀, hK₀⟩ := exists_smoothedZeroCount hw hsupp
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_smoothedLandau_neg_le hw hsupp
  refine ⟨max |K₀| (2 * K₁), fun a Y hY T hT2 hYT => ?_⟩
  have hTpos : 0 < T := by linarith
  set Z : ℕ → ℂ := fun n => ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
    paperFT (landauTest w T (-Real.log n)) (gammaOf ρ) with hZ
  have hsum : ∀ n : ℕ, Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) *
      paperFT (landauTest w T (-Real.log n)) (gammaOf ρ)) := fun n => by
    obtain ⟨hkd, hkc⟩ := landauTest_contDiff_hasCompactSupport hw hsupp hTpos (-Real.log n)
    exact (Zeta23.WeilEF.EF_lit_zetaZeroConfig _ hkd hkc).1
  -- exchange the zero sum with the finite sum over `n`
  have hswap : (∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
      paperFT w (gammaOf ρ / T) * ∑ n ∈ Finset.Icc 1 Y, a n * (n : ℂ) ^ (-((ρ : ℂ) - 1 / 2))) =
      ∑ n ∈ Finset.Icc 1 Y, a n * Z n := by
    have hterm : ∀ ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        paperFT w (gammaOf ρ / T) * ∑ n ∈ Finset.Icc 1 Y, a n * (n : ℂ) ^ (-((ρ : ℂ) - 1 / 2)) =
        ∑ n ∈ Finset.Icc 1 Y, a n * ((zetaZeroConfig.mult ρ : ℂ) *
          paperFT (landauTest w T (-Real.log n)) (gammaOf ρ)) := by
      intro ρ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      rw [paperFT_landauTest_neg_log hTpos hn0]
      ring
    rw [tsum_congr hterm, Summable.tsum_finsetSum (fun n _ => (hsum n).mul_left (a n))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [tsum_mul_left]
  -- split off `n = 1`
  have hsplit : ∀ f : ℕ → ℂ, ∑ n ∈ Finset.Icc 1 Y, f n = f 1 + ∑ n ∈ Finset.Icc 2 Y, f n := by
    intro f
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hY, Finset.sum_insert (by simp)]
  have hsplitR : ∀ f : ℕ → ℝ, ∑ n ∈ Finset.Icc 1 Y, f n = f 1 + ∑ n ∈ Finset.Icc 2 Y, f n := by
    intro f
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hY, Finset.sum_insert (by simp)]
  -- the `n = 1` term is the smoothed zero count
  have hZ1 : Z 1 = ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
      paperFT w (gammaOf ρ / T) := by
    simp only [hZ, Nat.cast_one, Real.log_one, neg_zero]
    congr 1; funext ρ; rw [paperFT_landauTest_zero hTpos]
  set M := (T : ℂ) * w 0 * (Real.log T : ℂ) + (T : ℂ) * zeroCountConst w
  set c : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
  have hdiff : (∑ n ∈ Finset.Icc 1 Y, a n * Z n) -
      (a 1 * M - (T : ℂ) * w 0 * ∑ n ∈ Finset.Icc 2 Y, a n * c n) =
      a 1 * (Z 1 - M) + ∑ n ∈ Finset.Icc 2 Y, a n * (Z n + c n * ((T : ℂ) * w 0)) := by
    rw [hsplit, Finset.mul_sum]
    have : ∑ n ∈ Finset.Icc 2 Y, a n * (Z n + c n * ((T : ℂ) * w 0)) =
        ∑ n ∈ Finset.Icc 2 Y, a n * Z n + ∑ n ∈ Finset.Icc 2 Y, (T : ℂ) * w 0 * (a n * c n) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [this]; ring
  rw [hswap, hdiff]
  set K := max |K₀| (2 * K₁)
  have hKK₀ : |K₀| ≤ K := le_max_left _ _
  have hKK₁ : 2 * K₁ ≤ K := le_max_right _ _
  have hb1 : ‖a 1 * (Z 1 - M)‖ ≤ K * (‖a 1‖ * (Real.sqrt (1 : ℕ) + Real.sqrt T)) := by
    rw [norm_mul, hZ1]
    have h := hK₀ T hT2
    have hs : 1 ≤ Real.sqrt ((1 : ℕ) : ℝ) + Real.sqrt T := by
      simp only [Nat.cast_one, Real.sqrt_one]; linarith [Real.sqrt_nonneg T]
    calc ‖a 1‖ * ‖_‖ ≤ ‖a 1‖ * |K₀| := mul_le_mul_of_nonneg_left (h.trans (le_abs_self _))
          (norm_nonneg _)
      _ ≤ ‖a 1‖ * (K * (Real.sqrt ((1 : ℕ) : ℝ) + Real.sqrt T)) := by
          gcongr
          calc |K₀| ≤ K := hKK₀
            _ = K * 1 := (mul_one K).symm
            _ ≤ K * (Real.sqrt ((1 : ℕ) : ℝ) + Real.sqrt T) :=
                mul_le_mul_of_nonneg_left hs ((abs_nonneg _).trans hKK₀)
      _ = _ := by ring
  have hbn : ∀ n ∈ Finset.Icc 2 Y, ‖a n * (Z n + c n * ((T : ℂ) * w 0))‖ ≤
      K * (‖a n‖ * (Real.sqrt n + Real.sqrt T)) := by
    intro n hn
    obtain ⟨hn2, hnY⟩ := Finset.mem_Icc.mp hn
    have hnT : (n : ℝ) + 2 ≤ T := by
      have : (n : ℝ) ≤ Y := by exact_mod_cast hnY
      linarith
    have h := hK₁ n hn2 T hnT
    have hlog : 1 / 2 < Real.log n := by
      have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
      linarith [Real.log_two_gt_d9]
    have hq : Real.sqrt T / Real.log n ≤ 2 * Real.sqrt T := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [Real.sqrt_nonneg T]
    rw [norm_mul]
    calc ‖a n‖ * ‖Z n + c n * ((T : ℂ) * w 0)‖
        ≤ ‖a n‖ * (K₁ * (Real.sqrt n + Real.sqrt T / Real.log n)) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ ‖a n‖ * (K₁ * (2 * (Real.sqrt n + Real.sqrt T))) := by
          gcongr; nlinarith [Real.sqrt_nonneg (n : ℝ)]
      _ = ‖a n‖ * ((2 * K₁) * (Real.sqrt n + Real.sqrt T)) := by ring
      _ ≤ ‖a n‖ * (K * (Real.sqrt n + Real.sqrt T)) := by gcongr
      _ = _ := by ring
  rw [hsplitR (fun n => ‖a n‖ * (Real.sqrt n + Real.sqrt T)), mul_add, Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add hb1 ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hbn)

end Moment

end RHTower

end
