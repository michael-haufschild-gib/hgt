import GaloisForLFunctions.RHTower.SiegelProductCoefficients
import GaloisForLFunctions.RHTower.SiegelGoldfeldInequality
import Zeta23.ThmE.LGrowth
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The biquadratic product `ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` and Goldfeld's bound for it

For Dirichlet characters `χ₁ mod N₁`, `χ₂ mod N₂` let `χ₁χ₂` be their product modulo `N₁N₂`
(`productChar`).  For `Re s > 1` the Dirichlet series with coefficients `siegelCoeff χ₁ χ₂` is
`F(s) = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` (`LSeries_siegelCoeff`).  When the three characters are
nontrivial, `H(s) = (s − 1) F(s)` is entire, `G = (H − H(1))/(s − 1)` is entire
(`differentiable_siegelG`), and `F(s) = G(s) + λ/(s − 1)` with `λ = H(1) = L(1,χ₁)L(1,χ₂)L(1,χ₁χ₂)`
(`LSeries_siegelCoeff_eq`).  For quadratic characters `λ` is a nonnegative real number
(`siegelRes_nonneg`), being a limit of `(σ − 1)F(σ) ≥ 0`.

On the circle `|s − 2| = 3/2` one has `|G| ≤ C₀ (N₁N₂)²` with an absolute constant `C₀`
(`exists_norm_siegelG_le`), from the uniform growth bound `|L(s,χ)| ≤ 8q(|Im s| + 3)`.  Goldfeld's
inequality then gives, for `7/8 ≤ σ < 1` (`siegel_goldfeld_bound`),

`F(σ) ≥ 1/2 − 2e λ (8 C₀ (N₁N₂)² + 8)^{4(1−σ)}/(1 − σ)`.
-/

open ArithmeticFunction DirichletCharacter Complex

noncomputable section

namespace RHTower

variable {N₁ N₂ : ℕ}

/-- The product of characters of moduli `N₁`, `N₂`, as a character modulo `N₁ N₂`. -/
def productChar (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    DirichletCharacter ℂ (N₁ * N₂) :=
  changeLevel (dvd_mul_right N₁ N₂) χ₁ * changeLevel (dvd_mul_left N₂ N₁) χ₂

lemma changeLevel_natCast {N M : ℕ} (χ : DirichletCharacter ℂ N) (h : N ∣ M) (n : ℕ)
    (hn : n.Coprime M) : changeLevel h χ (n : ZMod M) = χ (n : ZMod N) := by
  have hu : IsUnit (n : ZMod M) := (ZMod.isUnit_iff_coprime n M).mpr hn
  have := changeLevel_eq_cast_of_dvd χ h hu.unit
  rw [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_natCast h]

lemma productChar_apply (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (n : ℕ) :
    productChar χ₁ χ₂ n = χ₁ n * χ₂ n := by
  unfold productChar
  rw [MulChar.mul_apply]
  by_cases hc : n.Coprime (N₁ * N₂)
  · rw [changeLevel_natCast χ₁ _ n hc, changeLevel_natCast χ₂ _ n hc]
  · have hnu : ¬ IsUnit (n : ZMod (N₁ * N₂)) := by rwa [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_mul_iff_right, not_and_or] at hc
    have h1 : changeLevel (dvd_mul_right N₁ N₂) χ₁ (n : ZMod (N₁ * N₂)) = 0 :=
      MulChar.map_nonunit _ hnu
    rw [h1, zero_mul]
    rcases hc with h | h
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]

/-! ## The Dirichlet series -/

lemma LSeriesSummable_toArithmeticFunction_of_norm_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => toArithmeticFunction f n) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn => by
    simpa [toArithmeticFunction, hn] using hf n) hs

lemma LSeries_toArithmeticFunction (f : ℕ → ℂ) (s : ℂ) :
    LSeries (fun n => toArithmeticFunction f n) s = LSeries f s :=
  LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s

variable [NeZero N₁] [NeZero N₂]

/-- **The product identity.**  For `Re s > 1`,
`∑ siegelCoeff(n) n^{−s} = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)`. -/
theorem LSeries_siegelCoeff (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => siegelCoeff χ₁ χ₂ n) s
      = riemannZeta s * (LFunction χ₁ s * LFunction χ₂ s * LFunction (productChar χ₁ χ₂) s) := by
  have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) s := by
    simpa [ArithmeticFunction.natCoe_apply] using LSeriesSummable_zeta_iff.mpr hs
  have h1 := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₁.norm_le_one n) hs
  have h2 := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₂.norm_le_one n) hs
  have h12 := LSeriesSummable_toArithmeticFunction_of_norm_le
    (f := fun n : ℕ => χ₁ n * χ₂ n) (fun n => by
      rw [norm_mul]; exact mul_le_one₀ (χ₁.norm_le_one n) (norm_nonneg _) (χ₂.norm_le_one n)) hs
  unfold siegelCoeff
  rw [charTwist_zetaMul, DirichletCharacter.zetaMul,
    LSeries_mul' (LSeriesSummable_mul hz h1) (LSeriesSummable_mul h2 h12),
    LSeries_mul' hz h1, LSeries_mul' h2 h12, LSeries_toArithmeticFunction,
    LSeries_toArithmeticFunction, LSeries_toArithmeticFunction,
    LFunction_eq_LSeries χ₁ hs, LFunction_eq_LSeries χ₂ hs,
    LFunction_eq_LSeries (productChar χ₁ χ₂) hs]
  have hζ : LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) s
      = riemannZeta s := by
    rw [← LSeries_zeta_eq_riemannZeta hs]
    congr 1
  rw [hζ]
  have hp : LSeries (fun n : ℕ => χ₁ n * χ₂ n) s = LSeries (fun n : ℕ => productChar χ₁ χ₂ n) s := by
    congr 1; funext n; rw [productChar_apply]
  rw [hp]
  ring

omit [NeZero N₁] [NeZero N₂] in
lemma abscissaOfAbsConv_siegelCoeff_le (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    LSeries.abscissaOfAbsConv (fun n => siegelCoeff χ₁ χ₂ n) ≤ 1 := by
  have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    (f := fun n => siegelCoeff χ₁ χ₂ n) (x := 1) fun y hy => by
      have hs : 1 < ((y : ℂ)).re := by simpa using hy
      have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n)
          (y : ℂ) := by
        simpa [ArithmeticFunction.natCoe_apply] using LSeriesSummable_zeta_iff.mpr hs
      have h1 := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₁.norm_le_one n) hs
      have h2 := LSeriesSummable_toArithmeticFunction_of_norm_le (fun n => χ₂.norm_le_one n) hs
      have h12 := LSeriesSummable_toArithmeticFunction_of_norm_le
        (f := fun n : ℕ => χ₁ n * χ₂ n) (fun n => by
          rw [norm_mul]; exact mul_le_one₀ (χ₁.norm_le_one n) (norm_nonneg _) (χ₂.norm_le_one n))
          hs
      unfold siegelCoeff
      rw [charTwist_zetaMul, DirichletCharacter.zetaMul]
      exact LSeriesSummable_mul (LSeriesSummable_mul hz h1) (LSeriesSummable_mul h2 h12)
  simpa using this

/-! ## The pole and the entire part -/

/-- `H(s) = (s − 1) ζ(s) · L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)`, with its value at `s = 1`. -/
def siegelH (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (s : ℂ) : ℂ :=
  LFunctionTrivChar₁ 1 s * (LFunction χ₁ s * LFunction χ₂ s * LFunction (productChar χ₁ χ₂) s)

/-- The entire part `G(s) = (H(s) − H(1))/(s − 1)`. -/
def siegelG (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) : ℂ → ℂ :=
  dslope (siegelH χ₁ χ₂) 1

/-- The residue `λ = H(1) = L(1, χ₁) L(1, χ₂) L(1, χ₁χ₂)`. -/
def siegelRes (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) : ℂ :=
  siegelH χ₁ χ₂ 1

lemma LFunctionTrivChar₁_one_of_ne {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
  rw [LFunctionTrivChar₁, Function.update_of_ne hs, LFunctionTrivChar, LFunction_modOne_eq]

lemma LFunctionTrivChar₁_one_one : LFunctionTrivChar₁ 1 1 = 1 := by
  simp [LFunctionTrivChar₁]

lemma siegelRes_eq (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    siegelRes χ₁ χ₂ = LFunction χ₁ 1 * LFunction χ₂ 1 * LFunction (productChar χ₁ χ₂) 1 := by
  rw [siegelRes, siegelH, LFunctionTrivChar₁_one_one, one_mul]

lemma differentiable_siegelH {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : productChar χ₁ χ₂ ≠ 1) :
    Differentiable ℂ (siegelH χ₁ χ₂) := by
  have := differentiable_LFunctionTrivChar₁ 1
  have a1 := differentiable_LFunction h₁
  have a2 := differentiable_LFunction h₂
  have a3 := differentiable_LFunction h₁₂
  unfold siegelH
  fun_prop

lemma differentiable_siegelG {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (h₁₂ : productChar χ₁ χ₂ ≠ 1) :
    Differentiable ℂ (siegelG χ₁ χ₂) := by
  have hH := differentiable_siegelH h₁ h₂ h₁₂
  have := (Complex.differentiableOn_dslope (c := 1) (s := Set.univ) Filter.univ_mem).mpr
    hH.differentiableOn
  exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem

lemma siegelH_of_ne (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) {s : ℂ}
    (hs : s ≠ 1) : siegelH χ₁ χ₂ s
      = (s - 1) * (riemannZeta s * (LFunction χ₁ s * LFunction χ₂ s
          * LFunction (productChar χ₁ χ₂) s)) := by
  rw [siegelH, LFunctionTrivChar₁_one_of_ne hs]; ring

/-- `G(s) + λ/(s − 1) = ζ(s) L(s, χ₁) L(s, χ₂) L(s, χ₁χ₂)` for `s ≠ 1`. -/
lemma siegelG_add_res (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) {s : ℂ}
    (hs : s ≠ 1) :
    siegelG χ₁ χ₂ s + siegelRes χ₁ χ₂ / (s - 1)
      = riemannZeta s * (LFunction χ₁ s * LFunction χ₂ s * LFunction (productChar χ₁ χ₂) s) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [siegelG, dslope_of_ne _ hs, slope_def_field, siegelRes, siegelH_of_ne χ₁ χ₂ hs]
  field_simp
  ring

/-- For `Re s > 1`: `F(s) = G(s) + λ/(s − 1)`. -/
theorem LSeries_siegelCoeff_eq (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => siegelCoeff χ₁ χ₂ n) s = siegelG χ₁ χ₂ s + siegelRes χ₁ χ₂ / (s - 1) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  rw [siegelG_add_res χ₁ χ₂ hs1, LSeries_siegelCoeff χ₁ χ₂ hs]

open scoped ComplexOrder

/-- **The residue is a nonnegative real number** for quadratic characters. -/
theorem siegelRes_nonneg {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (hq₁ : χ₁ ^ 2 = 1) (hq₂ : χ₂ ^ 2 = 1) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1)
    (h₁₂ : productChar χ₁ χ₂ ≠ 1) : 0 ≤ siegelRes χ₁ χ₂ := by
  have hH := differentiable_siegelH h₁ h₂ h₁₂
  have hcont : Continuous fun σ : ℝ => siegelH χ₁ χ₂ (σ : ℂ) :=
    hH.continuous.comp Complex.continuous_ofReal
  have hnn : ∀ σ : ℝ, 1 < σ → 0 ≤ siegelH χ₁ χ₂ (σ : ℂ) := by
    intro σ hσ
    have hσ1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ.ne'
    have hF : 0 ≤ LSeries (fun n => siegelCoeff χ₁ χ₂ n) (σ : ℂ) := by
      have := LSeries.iteratedDeriv_alternating (a := fun n => siegelCoeff χ₁ χ₂ n)
        (fun n => siegelCoeff_nonneg hq₁ hq₂ n) (x := σ)
        (lt_of_le_of_lt (abscissaOfAbsConv_siegelCoeff_le χ₁ χ₂)
          (EReal.coe_lt_coe_iff.2 hσ)) 0
      simpa using this
    rw [siegelH_of_ne χ₁ χ₂ hσ1, ← LSeries_siegelCoeff χ₁ χ₂ (by simpa using hσ)]
    have hpos : (0 : ℂ) ≤ (σ : ℂ) - 1 := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.zero_le_real.mpr (by linarith)
    exact mul_nonneg hpos hF
  have ht : Filter.Tendsto (fun σ : ℝ => siegelH χ₁ χ₂ (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (siegelH χ₁ χ₂ 1)) := by
    have := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using this
  rw [siegelRes]
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun σ hσ => hnn σ hσ)

/-! ## The bound on the circle `|s − 2| = 3/2` and Goldfeld's inequality -/

/-- **Size of the entire part.**  There is an absolute constant `C₀` with
`|G(z)| ≤ C₀ (N₁N₂)²` on the circle `|z − 2| = 3/2`, for all nontrivial `χ₁`, `χ₂`, `χ₁χ₂`. -/
theorem exists_norm_siegelG_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂] (χ₁ : DirichletCharacter ℂ N₁)
      (χ₂ : DirichletCharacter ℂ N₂), χ₁ ≠ 1 → χ₂ ≠ 1 → productChar χ₁ χ₂ ≠ 1 →
      ∀ z ∈ Metric.sphere (2 : ℂ) (3 / 2), ‖siegelG χ₁ χ₂ z‖ ≤ C₀ * ((N₁ : ℝ) * N₂) ^ 2 := by
  obtain ⟨A, hA⟩ := (isCompact_sphere (2 : ℂ) (3 / 2)).exists_bound_of_continuousOn
    (differentiable_LFunctionTrivChar₁ 1).continuous.continuousOn
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA (2 + 3 / 2) (by simp))
  refine ⟨2 * (A * 36 ^ 3 + 24 ^ 3), by positivity, ?_⟩
  intro N₁ N₂ _ _ χ₁ χ₂ h₁ h₂ h₁₂ z hz
  have hz2 : ‖z - 2‖ = 3 / 2 := by simpa [dist_eq_norm] using hz
  have hre : (1 / 2 : ℝ) ≤ z.re := by
    have := Complex.abs_re_le_norm (z - 2)
    rw [hz2, Complex.sub_re] at this
    simp only [Complex.re_ofNat] at this
    linarith [(abs_le.mp this).1]
  have him : |z.im| ≤ 3 / 2 := by
    have := Complex.abs_im_le_norm (z - 2)
    rw [hz2, Complex.sub_im] at this
    simpa using this
  have hz1 : (1 / 2 : ℝ) ≤ ‖z - 1‖ := by
    have := norm_sub_norm_le (z - 2) (z - 1)
    rw [show z - 2 - (z - 1) = (-1 : ℂ) by ring, norm_neg, norm_one, hz2] at this
    linarith
  have hσ : (0.15 : ℝ) ≤ z.re := by linarith
  have hN₁ : (1 : ℝ) ≤ N₁ := by exact_mod_cast NeZero.one_le
  have hN₂ : (1 : ℝ) ≤ N₂ := by exact_mod_cast NeZero.one_le
  have hL : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ‖LFunction χ z‖ ≤ 36 * N := by
    intro N _ χ hχ
    have := Zeta23.ThmE.LFunction_growth_right_uniform hχ hσ
    calc ‖LFunction χ z‖ ≤ 8 * N * (|z.im| + 3) := this
      _ ≤ 8 * N * (3 / 2 + 3) := by gcongr
      _ = 36 * N := by ring
  have hL1 : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ‖LFunction χ 1‖ ≤ 24 * N := by
    intro N _ χ hχ
    have := Zeta23.ThmE.LFunction_growth_right_uniform hχ (s := 1) (by norm_num)
    simp only [Complex.one_im, abs_zero, zero_add] at this
    linarith
  have hHz : ‖siegelH χ₁ χ₂ z‖ ≤ A * 36 ^ 3 * ((N₁ : ℝ) * N₂) ^ 2 := by
    rw [siegelH, norm_mul, norm_mul, norm_mul]
    have e1 := hL χ₁ h₁
    have e2 := hL χ₂ h₂
    have e3 := hL (productChar χ₁ χ₂) h₁₂
    push_cast at e3
    calc ‖LFunctionTrivChar₁ 1 z‖ * (‖LFunction χ₁ z‖ * ‖LFunction χ₂ z‖
          * ‖LFunction (productChar χ₁ χ₂) z‖)
        ≤ A * ((36 * N₁) * (36 * N₂) * (36 * (N₁ * N₂))) := by
          gcongr
          exact hA z hz
      _ = A * 36 ^ 3 * ((N₁ : ℝ) * N₂) ^ 2 := by ring
  have hH1 : ‖siegelH χ₁ χ₂ 1‖ ≤ 24 ^ 3 * ((N₁ : ℝ) * N₂) ^ 2 := by
    rw [siegelH, LFunctionTrivChar₁_one_one, one_mul, norm_mul, norm_mul]
    have e1 := hL1 χ₁ h₁
    have e2 := hL1 χ₂ h₂
    have e3 := hL1 (productChar χ₁ χ₂) h₁₂
    push_cast at e3
    calc ‖LFunction χ₁ 1‖ * ‖LFunction χ₂ 1‖ * ‖LFunction (productChar χ₁ χ₂) 1‖
        ≤ (24 * N₁) * (24 * N₂) * (24 * (N₁ * N₂)) := by gcongr
      _ = 24 ^ 3 * ((N₁ : ℝ) * N₂) ^ 2 := by ring
  have hzne : z ≠ 1 := by
    intro h; rw [h] at hz1; norm_num at hz1
  rw [siegelG, dslope_of_ne _ hzne, slope_def_field, norm_div]
  rw [div_le_iff₀ (by linarith)]
  calc ‖siegelH χ₁ χ₂ z - siegelH χ₁ χ₂ 1‖ ≤ ‖siegelH χ₁ χ₂ z‖ + ‖siegelH χ₁ χ₂ 1‖ :=
        norm_sub_le _ _
    _ ≤ (A * 36 ^ 3 + 24 ^ 3) * ((N₁ : ℝ) * N₂) ^ 2 := by linarith
    _ = 2 * (A * 36 ^ 3 + 24 ^ 3) * ((N₁ : ℝ) * N₂) ^ 2 * (1 / 2) := by ring
    _ ≤ 2 * (A * 36 ^ 3 + 24 ^ 3) * ((N₁ : ℝ) * N₂) ^ 2 * ‖z - 1‖ := by
        gcongr

omit [NeZero N₁] [NeZero N₂] in
lemma siegelCoeff_one (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    siegelCoeff χ₁ χ₂ 1 = 1 :=
  (isMultiplicative_siegelCoeff χ₁ χ₂).map_one

/-- **Goldfeld's inequality for the biquadratic product.**  There is an absolute constant `C₀`
such that for quadratic characters `χ₁ mod N₁`, `χ₂ mod N₂` with `χ₁`, `χ₂`, `χ₁χ₂` nontrivial and
`7/8 ≤ σ < 1`,
`Re F(σ) ≥ 1/2 − 2e λ (8 C₀ (N₁N₂)² + 8)^{4(1−σ)}/(1 − σ)`,
where `F = ζ L(·, χ₁) L(·, χ₂) L(·, χ₁χ₂)` and `λ = L(1, χ₁) L(1, χ₂) L(1, χ₁χ₂) ≥ 0`. -/
theorem siegel_goldfeld_bound : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂] (χ₁ : DirichletCharacter ℂ N₁)
      (χ₂ : DirichletCharacter ℂ N₂), χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 →
      productChar χ₁ χ₂ ≠ 1 → ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
      1 / 2 - 2 * Real.exp 1 * (siegelRes χ₁ χ₂).re
          * (8 * (C₀ * ((N₁ : ℝ) * N₂) ^ 2) + 8) ^ (4 * (1 - σ)) / (1 - σ)
        ≤ (riemannZeta σ * (LFunction χ₁ σ * LFunction χ₂ σ
            * LFunction (productChar χ₁ χ₂) σ)).re := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_norm_siegelG_le
  refine ⟨C₀, hC₀, ?_⟩
  intro N₁ N₂ _ _ χ₁ χ₂ hq₁ hq₂ h₁ h₂ h₁₂ σ hσ1 hσ2
  have hres := siegelRes_nonneg hq₁ hq₂ h₁ h₂ h₁₂
  have hres_eq : siegelRes χ₁ χ₂ = (((siegelRes χ₁ χ₂).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hres).2.symm]
  have hM0 : 0 ≤ C₀ * ((N₁ : ℝ) * N₂) ^ 2 := by positivity
  have hG := goldfeld_lower_bound' (a := fun n => siegelCoeff χ₁ χ₂ n)
    (fun n => siegelCoeff_nonneg hq₁ hq₂ n) (siegelCoeff_one χ₁ χ₂)
    (abscissaOfAbsConv_siegelCoeff_le χ₁ χ₂) (differentiable_siegelG h₁ h₂ h₁₂)
    (Complex.nonneg_iff.mp hres).1 hM0
    (fun s hs => by rw [LSeries_siegelCoeff_eq χ₁ χ₂ hs, ← hres_eq])
    (hbound N₁ N₂ χ₁ χ₂ h₁ h₂ h₁₂) hσ1 hσ2
  have hσne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ2.ne
  rw [← siegelG_add_res χ₁ χ₂ hσne]
  have : (siegelG χ₁ χ₂ σ + siegelRes χ₁ χ₂ / ((σ : ℂ) - 1)).re
      = (siegelG χ₁ χ₂ σ).re - (siegelRes χ₁ χ₂).re / (1 - σ) := by
    rw [hres_eq, Complex.add_re, show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
    rw [show σ - 1 = -(1 - σ) by ring, div_neg]; ring
  rw [this]
  exact hG

end RHTower
