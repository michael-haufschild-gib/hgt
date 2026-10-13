import Zeta23.Poisson

/-!
# Twisted Poisson summation for the Gabor grid

For windows `φ₁, φ₂` vanishing outside `(-A, A)` and `(-B, B)`, the grid `τ_k = T + k·2π/L` and
`G(η) = L ∫ φ₁(u) φ₂(Lη − u) e^{i(τu + τ'(Lη − u) − TLη)} du`, Poisson summation gives

`Σ_{k∈ℤ} φ̂₁(τ − τ_k) φ̂₂(τ' − τ_k) = G(−1) + G(0) + G(1)`   whenever `A + B ≤ 2L`

(`hasSum_paperFT_mul_paperFT_two`): `G(η)` vanishes for `|Lη| ≥ A + B`, and `𝓕G(w) = φ̂₁(τ − τ_w) φ̂₂(τ' − τ_w)`.
The aliased terms `G(±1)` live on the overlap of the supports and are bounded by `L·M₁M₂·(A + B − L)`
(`norm_Gaux2_one_le`, `norm_Gaux2_neg_one_le`).

Applied to `φ₂ = φ(· + ξ)`, whose transform is `e^{−iξz} φ̂(z)`, this is the modulated Poisson identity

`Σ_k e^{iξτ_k} φ̂(τ − τ_k) φ̂(τ' − τ_k) = e^{iξτ'} (G_ξ(0) + R)`,   `|R| ≤ 2L M² |ξ|`

(`hasSum_twisted_phiHat`, `norm_twisted_alias_le`), with main term `G_ξ(0) = L ∫ φ(u) φ(ξ − u) e^{i(τ−τ')u} du`
(`Gaux2_zero_twist`).  Smooth weights on the grid are superpositions of such modulations, so this is the identity
that evaluates the weighted Gram matrix of the zeta grid.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics Zeta23
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace TwistedPoisson

variable (φ₁ φ₂ : ℝ → ℝ) (L T τ τ' : ℝ)

/-- Integrand of `G`: `(η,u) ↦ L φ₁(u) φ₂(Lη−u) e^{i(τu + τ'(Lη−u) − TLη)}`. -/
def gInt2 (η u : ℝ) : ℂ :=
  (L : ℂ) * ((φ₁ u : ℂ) * (φ₂ (L * η - u) : ℂ) *
    cexp (I * (τ * u + τ' * (L * η - u) - T * L * η)))

/-- `G(η) := L ∫ φ₁(u) φ₂(Lη−u) e^{i(τu + τ'(Lη−u) − TLη)} du`. -/
def Gaux2 (η : ℝ) : ℂ := ∫ u, gInt2 φ₁ φ₂ L T τ τ' η u

variable {φ₁ φ₂ L T τ τ'} {A B : ℝ}

theorem gInt2_eq_zero_of_not_mem (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0)
    {η u : ℝ} (h : ¬ (|L * η| < A + B ∧ |u| < A)) : gInt2 φ₁ φ₂ L T τ τ' η u = 0 := by
  unfold gInt2
  by_cases hu : |u| < A
  · have hη : A + B ≤ |L * η| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have : B ≤ |L * η - u| := by
      have h4 : |L * η| - |u| ≤ |L * η - u| := abs_sub_abs_le_abs_sub _ _
      linarith
    rw [h₂ _ this]
    simp
  · rw [h₁ u (not_lt.mp hu)]
    simp

theorem gInt2_continuous (h₁c : Continuous φ₁) (h₂c : Continuous φ₂) :
    Continuous (Function.uncurry (gInt2 φ₁ φ₂ L T τ τ')) := by
  unfold gInt2 Function.uncurry
  fun_prop

theorem gInt2_hasCompactSupport (hL : 0 < L) (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0)
    (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) :
    HasCompactSupport (Function.uncurry (gInt2 φ₁ φ₂ L T τ τ')) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc (a := -((A + B) / L)) (b := (A + B) / L)).prod
      (isCompact_Icc (a := -A) (b := A))) ?_
  rintro ⟨η, u⟩ hne
  rw [Function.mem_support, Function.uncurry_apply_pair] at hne
  by_contra hmem
  apply hne (gInt2_eq_zero_of_not_mem h₁ h₂ _)
  rintro ⟨hη, hu⟩
  apply hmem
  rw [abs_mul, abs_of_pos hL] at hη
  have hη' : |η| < (A + B) / L := by rw [lt_div_iff₀ hL]; linarith
  rw [mem_prod, mem_Icc, mem_Icc]
  exact ⟨⟨by linarith [neg_abs_le η], by linarith [le_abs_self η]⟩,
    ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩

/-- `G` is continuous. -/
theorem Gaux2_continuous (h₁c : Continuous φ₁) (h₂c : Continuous φ₂)
    (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) :
    Continuous (Gaux2 φ₁ φ₂ L T τ τ') := by
  have : Gaux2 φ₁ φ₂ L T τ τ' = fun η => ∫ u in Icc (-A) A, gInt2 φ₁ φ₂ L T τ τ' η u := by
    funext η
    unfold Gaux2
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply gInt2_eq_zero_of_not_mem h₁ h₂
    rintro ⟨-, h2⟩
    apply hu
    rw [mem_Icc]
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [this]
  exact continuous_parametric_integral_of_continuous (gInt2_continuous h₁c h₂c) isCompact_Icc

/-- `G(η) = 0` for `|Lη| ≥ A + B`. -/
theorem Gaux2_eq_zero (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) {η : ℝ}
    (hη : A + B ≤ |L * η|) : Gaux2 φ₁ φ₂ L T τ τ' η = 0 := by
  unfold Gaux2
  rw [← integral_zero]
  congr 1 with u
  apply gInt2_eq_zero_of_not_mem h₁ h₂
  rintro ⟨h1, -⟩
  linarith

/-- Fubini computation: `𝓕G(w) = φ̂₁(τ − τ_w) φ̂₂(τ' − τ_w)`, `τ_w = T + w·2π/L`. -/
theorem fourier_Gaux2 (hL : 0 < L) (h₁c : Continuous φ₁) (h₂c : Continuous φ₂)
    (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) (w : ℝ) :
    𝓕 (Gaux2 φ₁ φ₂ L T τ τ') w
      = paperFT (fun u => (φ₁ u : ℂ)) ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ₂ u : ℂ)) ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) := by
  set α : ℝ := τ - (T + w * (2 * π / L)) with hα
  set β : ℝ := τ' - (T + w * (2 * π / L)) with hβ
  set J : ℝ → ℝ → ℂ := fun η u => cexp (↑(-2 * π * η * w) * I) * gInt2 φ₁ φ₂ L T τ τ' η u
    with hJ
  have hJint : Integrable (Function.uncurry J) (volume.prod volume) := by
    have hc : Continuous (Function.uncurry J) := by
      have := gInt2_continuous (L := L) (T := T) (τ := τ) (τ' := τ') h₁c h₂c
      simp only [hJ]
      apply Continuous.mul _ this
      fun_prop
    apply hc.integrable_of_hasCompactSupport
    apply (gInt2_hasCompactSupport (T := T) (τ := τ) (τ' := τ') hL h₁ h₂).mono
    intro p hp
    rw [Function.mem_support] at hp ⊢
    intro h0
    apply hp
    simp only [hJ, Function.uncurry] at h0 ⊢
    rw [show p = (p.1, p.2) from rfl] at h0
    simp only at h0
    rw [h0, mul_zero]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have step1 : (fun η : ℝ => cexp (↑(-2 * π * η * w) * I) • Gaux2 φ₁ φ₂ L T τ τ' η)
      = fun η => ∫ u, J η u := by
    funext η
    rw [smul_eq_mul, Gaux2, hJ]
    beta_reduce
    rw [integral_const_mul_C]
  rw [step1, integral_integral_swap hJint]
  have step3 : ∀ u : ℝ, ∫ η, J η u
      = (φ₁ u : ℂ) * cexp (I * α * u) * paperFT (fun v => (φ₂ v : ℂ)) β := by
    intro u
    set F0 : ℝ → ℂ := fun v => (φ₂ v : ℂ) * cexp (I * β * (v : ℂ)) with hF0
    have hpt : ∀ η : ℝ, J η u = (φ₁ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * η))) := by
      intro η
      simp only [hJ, gInt2, hF0]
      have := Poisson.cexp_bookkeeping (T := T) (τ := τ) (τ' := τ') hL.ne' η u w
      rw [← hα, ← hβ] at this
      calc cexp (↑(-2 * π * η * w) * I) * (↑L * (↑(φ₁ u) * ↑(φ₂ (L * η - u))
              * cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑η - ↑u) - ↑T * ↑L * ↑η))))
          = ↑L * ↑(φ₁ u) * ↑(φ₂ (L * η - u)) * (cexp (I * (↑τ * ↑u + ↑τ' * (↑L * ↑η - ↑u)
              - ↑T * ↑L * ↑η)) * cexp (↑(-2 * π * η * w) * I)) := by ring
        _ = ↑L * ↑(φ₁ u) * ↑(φ₂ (L * η - u))
              * (cexp (I * ↑α * ↑u) * cexp (I * ↑β * ↑(L * η - u))) := by rw [this]
        _ = _ := by push_cast; ring
    have hint : ∫ η, J η u = ∫ η, (φ₁ u : ℂ) * cexp (I * α * u)
        * ((L : ℂ) * ((fun y : ℝ => F0 (y - u)) (L * η))) := by
      congr 1 with η; exact hpt η
    rw [hint, integral_const_mul_C, integral_const_mul_C,
      Measure.integral_comp_mul_left (fun y : ℝ => F0 (y - u)) L,
      integral_sub_right_eq_self F0 u, paperFT_def, abs_of_pos (inv_pos.mpr hL)]
    congr 1
    rw [← Complex.coe_smul, smul_eq_mul, ← mul_assoc, ofReal_inv,
      mul_inv_cancel₀ (ofReal_ne_zero.mpr hL.ne'), one_mul]
  simp_rw [step3]
  rw [integral_mul_const_C, paperFT_def, paperFT_def]

/-- **Two-window Poisson summation on the Gabor grid.**  If `φ₁, φ₂` vanish outside `(-A, A)`, `(-B, B)` with
`A + B ≤ 2L`, then `Σ_{k∈ℤ} φ̂₁(τ − τ_k) φ̂₂(τ' − τ_k) = G(−1) + G(0) + G(1)`. -/
theorem hasSum_paperFT_mul_paperFT_two (hL : 0 < L) (h₁c : Continuous φ₁) (h₂c : Continuous φ₂)
    (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) (hAB : A + B ≤ 2 * L)
    (hdecay₁ : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ₁ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hdecay₂ : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ₂ u : ℂ)) s‖ ≤ C) :
    HasSum (fun k : ℤ => paperFT (fun u => (φ₁ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
                        * paperFT (fun u => (φ₂ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (Gaux2 φ₁ φ₂ L T τ τ' (-1) + Gaux2 φ₁ φ₂ L T τ τ' 0 + Gaux2 φ₁ φ₂ L T τ τ' 1) := by
  obtain ⟨C₁, hC₁⟩ := hdecay₁
  obtain ⟨C₂, hC₂⟩ := hdecay₂
  set G := Gaux2 φ₁ φ₂ L T τ τ' with hG
  have hGc : Continuous G := Gaux2_continuous h₁c h₂c h₁ h₂
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, (2 : ℝ) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, Gaux2_eq_zero h₁ h₂]
    · simp
    · rw [Real.norm_eq_abs] at hx
      rw [abs_mul, abs_of_pos hL]
      nlinarith
  have hC₁0 : 0 ≤ C₁ := le_trans (by positivity) (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := le_trans (norm_nonneg _) (hC₂ 0)
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply Poisson.isBigO_of_decay (c := τ - T) (h := 2 * π / L) (C := C₁ * C₂) (by positivity)
    intro w
    rw [hG, fourier_Gaux2 hL h₁c h₂c h₁ h₂ w, norm_mul]
    have e1 : τ - T - w * (2 * π / L) = τ - (T + w * (2 * π / L)) := by ring
    rw [e1]
    calc ‖paperFT (fun u => (φ₁ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
          * ‖paperFT (fun u => (φ₂ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖
          * (1 + (τ - (T + w * (2 * π / L))) ^ 2)
        = (‖paperFT (fun u => (φ₁ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
            * (1 + (τ - (T + w * (2 * π / L))) ^ 2))
          * ‖paperFT (fun u => (φ₂ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ := by ring
      _ ≤ C₁ * C₂ := mul_le_mul (hC₁ _) (hC₂ _) (norm_nonneg _) hC₁0
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = G (-1) + G 0 + G 1 := by
    rw [tsum_eq_sum (s := ({-1, 0, 1} : Finset ℤ))]
    · simp only [zero_add]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      push_cast
      ring
    · intro n hn
      rw [zero_add, hG, Gaux2_eq_zero h₁ h₂]
      have hn2 : 2 ≤ |n| := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        rcases (show n ≤ -2 ∨ 2 ≤ n by omega) with h | h
        · rw [abs_of_neg (by omega)]; omega
        · rw [abs_of_pos (by omega)]; omega
      have hn2' : (2 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn2
      rw [abs_mul, abs_of_pos hL]
      nlinarith
  have rhs : ∑' n : ℤ, 𝓕 G n * fourier n ((0 : ℝ) : UnitAddCircle) = ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  have hs : HasSum (fun n : ℤ => 𝓕 G n) (G (-1) + G 0 + G 1) := by
    rw [key]; exact hsum.hasSum
  convert hs using 1
  funext k
  rw [hG, fourier_Gaux2 hL h₁c h₂c h₁ h₂]

theorem gInt2_eq_zero_left (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0) {η u : ℝ} (hu : A ≤ |u|) :
    gInt2 φ₁ φ₂ L T τ τ' η u = 0 := by
  unfold gInt2; rw [h₁ u hu]; simp

theorem gInt2_eq_zero_right (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) {η u : ℝ} (hv : B ≤ |L * η - u|) :
    gInt2 φ₁ φ₂ L T τ τ' η u = 0 := by
  unfold gInt2; rw [h₂ _ hv]; simp

theorem norm_gInt2_le {M₁ M₂ : ℝ} (hL : 0 < L) (hM₁ : ∀ u, |φ₁ u| ≤ M₁) (hM₂ : ∀ v, |φ₂ v| ≤ M₂)
    (η u : ℝ) : ‖gInt2 φ₁ φ₂ L T τ τ' η u‖ ≤ L * (M₁ * M₂) := by
  have he : ‖cexp (I * (τ * u + τ' * (L * η - u) - T * L * η))‖ = 1 := by
    rw [show I * ((τ : ℂ) * u + τ' * (L * η - u) - T * L * η)
        = ((τ * u + τ' * (L * η - u) - T * L * η : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  unfold gInt2
  rw [norm_mul, norm_mul, norm_mul, he, mul_one, Complex.norm_real, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hM₁ u) (hM₂ _) (abs_nonneg _)
    (le_trans (abs_nonneg _) (hM₁ u))) hL.le

/-- The aliased term at `η = 1` lives on the overlap `[L − B, A]`: `‖G(1)‖ ≤ L M₁ M₂ (A + B − L)`. -/
theorem norm_Gaux2_one_le (hL : 0 < L) (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0)
    (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) {M₁ M₂ : ℝ} (hM₁ : ∀ u, |φ₁ u| ≤ M₁) (hM₂ : ∀ v, |φ₂ v| ≤ M₂)
    (hover : L - B ≤ A) :
    ‖Gaux2 φ₁ φ₂ L T τ τ' 1‖ ≤ L * (M₁ * M₂) * (A - (L - B)) := by
  have hsupp : ∀ u ∉ Icc (L - B) A, gInt2 φ₁ φ₂ L T τ τ' 1 u = 0 := by
    intro u hu
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · exact gInt2_eq_zero_right h₂ (by rw [mul_one]; linarith [le_abs_self (L - u)])
    · exact gInt2_eq_zero_left h₁ (by linarith [le_abs_self u])
  unfold Gaux2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  refine (norm_setIntegral_le_of_norm_le_const (by simp)
    (fun u _ => norm_gInt2_le hL hM₁ hM₂ 1 u)).trans (le_of_eq ?_)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- The aliased term at `η = −1` lives on the overlap `[−A, B − L]`: `‖G(−1)‖ ≤ L M₁ M₂ (A + B − L)`. -/
theorem norm_Gaux2_neg_one_le (hL : 0 < L) (h₁ : ∀ u, A ≤ |u| → φ₁ u = 0)
    (h₂ : ∀ v, B ≤ |v| → φ₂ v = 0) {M₁ M₂ : ℝ} (hM₁ : ∀ u, |φ₁ u| ≤ M₁) (hM₂ : ∀ v, |φ₂ v| ≤ M₂)
    (hover : L - B ≤ A) :
    ‖Gaux2 φ₁ φ₂ L T τ τ' (-1)‖ ≤ L * (M₁ * M₂) * (A - (L - B)) := by
  have hsupp : ∀ u ∉ Icc (-A) (B - L), gInt2 φ₁ φ₂ L T τ τ' (-1) u = 0 := by
    intro u hu
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · exact gInt2_eq_zero_left h₁ (by linarith [neg_abs_le u])
    · exact gInt2_eq_zero_right h₂ (by
        rw [show L * -1 - u = -(L + u) by ring, abs_neg]; linarith [le_abs_self (L + u)])
  unfold Gaux2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  refine (norm_setIntegral_le_of_norm_le_const (by simp)
    (fun u _ => norm_gInt2_le hL hM₁ hM₂ (-1) u)).trans (le_of_eq ?_)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-! ### Modulation by `e^{iξτ_k}` -/

/-- The transform of the shifted window: `(φ(· + ξ))^(z) = e^{−iξz} φ̂(z)`. -/
theorem paperFT_shift (φ : ℝ → ℝ) (ξ : ℝ) (z : ℂ) :
    paperFT (fun v => (φ (v + ξ) : ℂ)) z = cexp (-(I * z * ξ)) * paperFT (fun u => (φ u : ℂ)) z := by
  rw [paperFT_def, paperFT_def, ← integral_const_mul_C,
    ← integral_add_right_eq_self (μ := volume)
      (fun u : ℝ => cexp (-(I * z * ξ)) * ((φ u : ℂ) * cexp (I * z * u))) ξ]
  congr 1 with v
  have h : cexp (-(I * z * ξ)) * cexp (I * z * ((v : ℂ) + ξ)) = cexp (I * z * v) := by
    rw [← Complex.exp_add]; congr 1; ring
  push_cast
  rw [← h]; ring

variable {φ : ℝ → ℝ} {ξ : ℝ}

/-- The shifted window vanishes outside `(−(L/2 + |ξ|), L/2 + |ξ|)`. -/
theorem shift_supp (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) :
    ∀ v, L / 2 + |ξ| ≤ |v| → φ (v + ξ) = 0 := by
  intro v hv
  apply hsupp
  have := abs_sub_abs_le_abs_sub v (-ξ)
  rw [abs_neg, sub_neg_eq_add] at this
  linarith

/-- **Modulated Poisson summation on the Gabor grid.**  For `|ξ| ≤ L`,
`Σ_k e^{iξτ_k} φ̂(τ − τ_k) φ̂(τ' − τ_k) = e^{iξτ'} (G_ξ(−1) + G_ξ(0) + G_ξ(1))`, `G_ξ = G[φ, φ(· + ξ)]`. -/
theorem hasSum_twisted_phiHat (hL : 0 < L) (hφc : Continuous φ) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (hξ : |ξ| ≤ L) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ))
        * paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1)) := by
  have hdecay₂ : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ (u + ξ) : ℂ)) s‖ ≤ C := by
    obtain ⟨C, hC⟩ := hdecay
    refine ⟨C, fun s => ?_⟩
    rw [paperFT_shift, norm_mul,
      show -(I * (s : ℂ) * ξ) = ((-(s * ξ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have h1 := hC s
    have h2 : ‖paperFT (fun u => (φ u : ℂ)) s‖ * 1
        ≤ ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) := by gcongr; nlinarith
    linarith
  have h := hasSum_paperFT_mul_paperFT_two (T := T) (τ := τ) (τ' := τ') hL hφc
    (hφc.comp (continuous_add_const ξ)) hsupp (shift_supp hsupp) (by linarith) hdecay hdecay₂
  have hf : (fun k : ℤ => cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ))
        * paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      = fun k : ℤ => cexp (I * ξ * τ')
        * (paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
          * paperFT (fun u => (φ (u + ξ) : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ)) := by
    funext k
    rw [paperFT_shift]
    have e : cexp (I * ξ * τ') * cexp (-(I * ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ) * ξ))
        = cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← e]; ring
  rw [hf]
  exact h.mul_left _

/-- The aliased part of the modulated sum is at most `2 L M² |ξ|` when `|φ| ≤ M`. -/
theorem norm_twisted_alias_le (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {M : ℝ}
    (hM : ∀ u, |φ u| ≤ M) (T τ τ' : ℝ) :
    ‖Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1) + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1‖
      ≤ 2 * L * M ^ 2 * |ξ| := by
  have hM' : ∀ v, |φ (v + ξ)| ≤ M := fun v => hM _
  have hov : L - (L / 2 + |ξ|) ≤ L / 2 := by linarith [abs_nonneg ξ]
  have h1 := norm_Gaux2_neg_one_le (T := T) (τ := τ) (τ' := τ') hL hsupp (shift_supp hsupp) hM hM' hov
  have h2 := norm_Gaux2_one_le (T := T) (τ := τ) (τ' := τ') hL hsupp (shift_supp hsupp) hM hM' hov
  refine (norm_add_le _ _).trans ?_
  have e : L * (M * M) * (L / 2 - (L - (L / 2 + |ξ|))) = L * M ^ 2 * |ξ| := by ring
  rw [e] at h1 h2
  linarith

/-- The main term of the modulated sum: `G_ξ(0) = L ∫ φ(u) φ(ξ − u) e^{i(τ − τ')u} du`. -/
theorem Gaux2_zero_twist (T τ τ' : ℝ) :
    Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0
      = L * ∫ u : ℝ, (φ u : ℂ) * (φ (ξ - u) : ℂ) * cexp (I * ((τ - τ' : ℝ) : ℂ) * u) := by
  unfold Gaux2 gInt2
  rw [integral_const_mul_C]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [show L * 0 - u + ξ = ξ - u by ring]
  congr 2
  push_cast
  ring

end TwistedPoisson

end RHTower
