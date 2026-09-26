import GaloisForLFunctions.RHTower.HalfWeightDualCoefficients
import GaloisForLFunctions.RHTower.HalfWeightTwistedEisenstein

/-!
# The regularised dual weight-½ Eisenstein series

For `ψ₀` mod a prime `q ∤ 4M'` with `ψ₀² ≠ 1`:

* `EhatStar`: `Ê*(z,w) = (1 + ψ₀(-1)) Σ_{n≠0} Φ(y,w,n) e(nx) D̂*_n(w)`. There is no `y^w` term (`κ(0) = 0`)
  and no `y^{1-w}` term (`D̂_0 = 0`).
* `EhatStar_eq`: `Ê* = L(4w-1, ψ₀²) Ê` for `Re w > 1`.
* **`differentiableAt_EhatStar`**: holomorphic on `Re w > 1/4`.
* **`EhatStar_smul`**: `Ê*(δz, w) = ψ₀(d) j(δ,z) Ê*(z,w)` on `Re w > 1/4` for `δ ∈ Γ₀(4M'q²)`.
* `EhatStar_growth`, `continuous_EhatStar`: moderate growth `C(y^A + y^{-A})` and continuity in `z`.

`Ê*` and the regularised series `E*_ψ` of Shimura's integral have the same automorphy on `Γ₀(4M'q²)`.
-/

open Real Complex Filter Topology Metric CongruenceSubgroup
open scoped FourierTransform MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.RHTower.SelbergPoincareKernel

noncomputable section

section DualRegularised

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q) (M' : ℕ) [NeZero M']

/-- The regulariser of the dual series `R̂(w) = L(4w-1, ψ₀²)`. -/
def RDual (w : ℂ) : ℂ := DirichletCharacter.LFunction (ψ₀⁻¹⁻¹ ^ 2) (4 * w - 1)

theorem differentiable_RDual (h2 : ψ₀ ^ 2 ≠ 1) : Differentiable ℂ (RDual ψ₀) := by
  unfold RDual
  exact (DirichletCharacter.differentiable_LFunction (inv_sq_ne_one ψ₀⁻¹ (inv_sq_ne_one ψ₀ h2))).comp
    ((differentiable_id.const_mul 4).sub_const 1)

/-- The regularised dual coefficients, total in `n` (`D̂*_0 = 0`). -/
def DhstZ (n : ℤ) (w : ℂ) : ℂ :=
  if h : n = 0 then 0 else Dhst ψ₀ h (Nat.pos_of_ne_zero (NeZero.ne M')) w

/-- The terms of the regularised dual Fourier expansion. -/
def aTermDual (z : UpperHalfPlane) (w : ℂ) (n : ℤ) : ℂ :=
  PhiK z.im 1 w n * cexp (2 * π * I * n * z.re) * DhstZ ψ₀ M' n w

/-- **The regularised dual Eisenstein series** `Ê*(z,w) = L(4w-1, ψ₀²) Ê(z,w)`. -/
def EhatStar (z : UpperHalfPlane) (w : ℂ) : ℂ :=
  (1 + ψ₀ (-1)) * ∑' n : ℤ, aTermDual ψ₀ M' z w n

theorem aTermDual_zero (z : UpperHalfPlane) (w : ℂ) : aTermDual ψ₀ M' z w 0 = 0 := by
  simp [aTermDual, DhstZ]

/-- `Ê*` continues `L(4w-1, ψ₀²) Ê` from `Re w > 1`. -/
theorem EhatStar_eq (h2 : ψ₀ ^ 2 ≠ 1) (hcop : q.Coprime (4 * M')) {w : ℂ} (hw : 1 < w.re)
    (z : UpperHalfPlane) :
    EhatStar ψ₀ M' z w = RDual ψ₀ w * eisDual ψ₀ M' w z := by
  rw [eisDual_eq_coeffs ψ₀ M' hw z, EhatStar]
  have hterm : ∀ n : ℤ, aTermDual ψ₀ M' z w n = RDual ψ₀ w * (𝓕 (kerH z.im w) n *
      cexp (2 * π * I * n * z.re) * DserK (M' * q) (kapQ ψ₀) n w) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [aTermDual_zero, DserK_dual_zero ψ₀ M' hcop]; ring
    · have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
      rw [aTermDual, DhstZ, dif_neg hn, ← fourier_kerH_eq_PhiK z.im_pos hξ 1 (by linarith),
        Dhst_eq ψ₀ hn _ h2 hcop (by linarith)]
      unfold RDual; ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  ring

/-- **Holomorphy of `Ê*`** on `Re w > 1/4`. -/
theorem differentiableAt_EhatStar (h2 : ψ₀ ^ 2 ≠ 1) (z : UpperHalfPlane) {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (EhatStar ψ₀ M' z) w₀ := by
  have hM : 0 < M' := Nat.pos_of_ne_zero (NeZero.ne M')
  have hy := z.im_pos
  set r := (w₀.re - 1 / 4) / 2 with hr
  have hr0 : 0 < r := by simp only [hr]; linarith
  have hl : 1 / 4 < w₀.re - r := by simp only [hr]; linarith
  set e := expTw (w₀.re - r)
  set K : ℕ := ⌈e⌉₊ + 2 with hK
  have hK1 : 1 ≤ K := by omega
  have heK : e - K ≤ -2 := by
    have := Nat.le_ceil e
    have : ((⌈e⌉₊ + 2 : ℕ) : ℝ) = (⌈e⌉₊ : ℝ) + 2 := by push_cast; ring
    rw [hK, this]; linarith
  obtain ⟨CP, hCP0, hCP⟩ := exists_bound_PhiK hy hK1 hr0 (by linarith)
  obtain ⟨CD, hCD0, hCD⟩ := exists_bound_Dhst ψ₀ h2 hM hl
  set u : ℤ → ℝ := fun n => CP * CD * |(n : ℝ)| ^ (-2 : ℝ)
  have hsu : Summable u := (Real.summable_abs_int_rpow (b := 2) (by norm_num)).mul_left _
  have hbound : ∀ (n : ℤ) (w : ℂ), w ∈ ball w₀ r → ‖aTermDual ψ₀ M' z w n‖ ≤ u n := by
    intro n w hw
    have hwc : w ∈ closedBall w₀ r := ball_subset_closedBall hw
    obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hwc
    simp only [u]
    by_cases hn : n = 0
    · subst hn; rw [aTermDual_zero, norm_zero]; positivity
    · have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
      have hPhi : PhiK z.im 1 w n = PhiK z.im K w n :=
        PhiK_eq_PhiK hy hξ hK1 (by push_cast; linarith)
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      rw [aTermDual, hPhi, norm_mul, norm_mul, continuous_cexp_mode, mul_one, DhstZ, dif_neg hn]
      have hP := hCP w hwc n hξ
      have hD := hCD w hwc n hn
      calc ‖PhiK z.im K w n‖ * ‖Dhst ψ₀ hn hM w‖
          ≤ (CP * |(n : ℝ)| ^ (-(K : ℝ))) * (CD * |(n : ℝ)| ^ e) :=
            mul_le_mul hP hD (norm_nonneg _) (by positivity)
        _ = CP * CD * |(n : ℝ)| ^ (e - K) := by
            rw [Real.rpow_sub (by linarith), Real.rpow_neg (by linarith)]; ring
        _ ≤ CP * CD * |(n : ℝ)| ^ (-2 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 heK) (by positivity)
  have hdiff : ∀ n : ℤ, DifferentiableOn ℂ (fun w => aTermDual ψ₀ M' z w n) (ball w₀ r) := by
    intro n w hw
    obtain ⟨hre1, _⟩ := re_ge_of_mem_closedBall (ball_subset_closedBall hw)
    refine DifferentiableAt.differentiableWithinAt ?_
    by_cases hn : n = 0
    · subst hn
      simp only [aTermDual_zero]
      exact differentiableAt_const _
    · simp only [aTermDual]
      have hP := differentiableAt_PhiK hy (n : ℝ) 1 (w₀ := w) (by push_cast; linarith)
      have hD : DifferentiableAt ℂ (fun w => DhstZ ψ₀ M' n w) w := by
        simp only [DhstZ, dif_neg hn]
        exact differentiableAt_Dhst ψ₀ hn hM h2 (by linarith)
      exact (hP.mul_const _).mul hD
  have hsum := Complex.differentiableOn_tsum_of_summable_norm hsu hdiff isOpen_ball hbound
  have hsumAt : DifferentiableAt ℂ (fun w => ∑' n : ℤ, aTermDual ψ₀ M' z w n) w₀ :=
    hsum.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))
  unfold EhatStar
  exact hsumAt.const_mul _

/-- **Automorphy of `Ê*`**: `Ê*(δz, w) = ψ₀(d) j(δ,z) Ê*(z,w)` on `Re w > 1/4`. -/
theorem EhatStar_smul (h2 : ψ₀ ^ 2 ≠ 1) (hcop : q.Coprime (4 * M')) (z : UpperHalfPlane)
    (δ : Gamma0 (4 * (M' * q ^ 2))) {w : ℂ} (hw : 1 / 4 < w.re) :
    EhatStar ψ₀ M' ((δ : SL(2, ℤ)) • z) w =
      ψ₀ (ent δ 1 1 : ZMod q) * jU δ z * EhatStar ψ₀ M' z w := by
  set U : Set ℂ := {w : ℂ | 1 / 4 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 4)).isPreconnected
  have hf : DifferentiableOn ℂ (fun w => EhatStar ψ₀ M' ((δ : SL(2, ℤ)) • z) w) U := fun w hw =>
    (differentiableAt_EhatStar ψ₀ M' h2 _ hw).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w => ψ₀ (ent δ 1 1 : ZMod q) * jU δ z *
      EhatStar ψ₀ M' z w) U := fun w hw =>
    ((differentiableAt_EhatStar ψ₀ M' h2 z hw).const_mul _).differentiableWithinAt
  have hw₁ : (9 / 8 : ℂ) ∈ U := by simp only [hU, Set.mem_setOf_eq]; norm_num
  have hev : (fun w => EhatStar ψ₀ M' ((δ : SL(2, ℤ)) • z) w) =ᶠ[𝓝 (9 / 8 : ℂ)]
      (fun w => ψ₀ (ent δ 1 1 : ZMod q) * jU δ z * EhatStar ψ₀ M' z w) := by
    have ho : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by norm_num)] with w hw
    rw [EhatStar_eq ψ₀ M' h2 hcop hw, EhatStar_eq ψ₀ M' h2 hcop hw, eisDual_smul ψ₀ M' w z δ δ.2]
    ring
  exact (hf.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd hUo) hUc hw₁ hev hw

/-- **Uniform bound for the terms of `Ê*`**: `‖a_n(z,w)‖ ≤ C |n|^{-2} (y^A + y^{-A})`. -/
theorem exists_aTermDual_bound (h2 : ψ₀ ^ 2 ≠ 1) {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    ∃ r > 0, ∃ C A : ℝ, 0 ≤ C ∧ w₀.re + r ≤ A ∧ ∀ w ∈ closedBall w₀ r, ∀ z : UpperHalfPlane, ∀ n : ℤ,
      ‖aTermDual ψ₀ M' z w n‖ ≤ C * |(n : ℝ)| ^ (-2 : ℝ) * (z.im ^ A + z.im ^ (-A)) := by
  have hM : 0 < M' := Nat.pos_of_ne_zero (NeZero.ne M')
  set r := (w₀.re - 1 / 4) / 2 with hr
  have hr0 : 0 < r := by simp only [hr]; linarith
  have hl : 1 / 4 < w₀.re - r := by simp only [hr]; linarith
  set e := expTw (w₀.re - r)
  set K : ℕ := ⌈e⌉₊ + 2 with hK
  have hK1 : 1 ≤ K := by omega
  have heK : e - K ≤ -2 := by
    have := Nat.le_ceil e
    have : ((⌈e⌉₊ + 2 : ℕ) : ℝ) = (⌈e⌉₊ : ℝ) + 2 := by push_cast; ring
    rw [hK, this]; linarith
  obtain ⟨CP, hCP0, hCP⟩ := exists_bound_PhiK_y hK1 hr0 (by linarith)
  obtain ⟨CD, hCD0, hCD⟩ := exists_bound_Dhst ψ₀ h2 hM hl
  set A : ℝ := w₀.re + r + K + 1
  refine ⟨r, hr0, CP * CD, A, by positivity,
    by simp only [A]; have : (0 : ℝ) ≤ K := Nat.cast_nonneg K; linarith, fun w hw z n => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  set y := z.im
  have hy : 0 < y := z.im_pos
  have hYpos : 0 ≤ y ^ A + y ^ (-A) := by positivity
  by_cases hn : n = 0
  · subst hn; rw [aTermDual_zero, norm_zero]; positivity
  · have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
    have hPhi : PhiK z.im 1 w n = PhiK z.im K w n :=
      PhiK_eq_PhiK hy hξ hK1 (by push_cast; linarith)
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    rw [aTermDual, hPhi, norm_mul, norm_mul, continuous_cexp_mode, mul_one, DhstZ, dif_neg hn]
    have hP := hCP w hw y hy n hξ
    have hD := hCD w hw n hn
    have hyt : y ^ (1 - w.re - K) ≤ y ^ A + y ^ (-A) := rpow_le_add_neg hy (by
      rw [abs_le]; constructor <;> linarith)
    calc ‖PhiK y K w n‖ * ‖Dhst ψ₀ hn hM w‖
        ≤ (CP * y ^ (1 - w.re - K) * |(n : ℝ)| ^ (-(K : ℝ))) * (CD * |(n : ℝ)| ^ e) :=
          mul_le_mul hP hD (norm_nonneg _) (by positivity)
      _ = CP * CD * y ^ (1 - w.re - K) * |(n : ℝ)| ^ (e - K) := by
          rw [Real.rpow_sub (show (0 : ℝ) < |(n : ℝ)| by linarith) e K,
            Real.rpow_neg (show (0 : ℝ) ≤ |(n : ℝ)| by linarith)]; ring
      _ ≤ CP * CD * (y ^ A + y ^ (-A)) * |(n : ℝ)| ^ (-2 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hyt (by positivity))
            (Real.rpow_le_rpow_of_exponent_le hn1 heK) (by positivity) (by positivity)
      _ = _ := by ring

/-- **Moderate growth of `Ê*`**, uniformly on a closed ball in `Re w > 1/4`. -/
theorem EhatStar_growth (h2 : ψ₀ ^ 2 ≠ 1) {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    ∃ r > 0, ∃ C A : ℝ, 0 ≤ C ∧ ∀ w ∈ closedBall w₀ r, ∀ z : UpperHalfPlane,
      ‖EhatStar ψ₀ M' z w‖ ≤ C * (z.im ^ A + z.im ^ (-A)) := by
  obtain ⟨r, hr0, C, A, hC0, hAr, hb⟩ := exists_aTermDual_bound ψ₀ M' h2 h1
  set u : ℤ → ℝ := fun n => C * |(n : ℝ)| ^ (-2 : ℝ)
  have hu : Summable u := (Real.summable_abs_int_rpow (b := 2) (by norm_num)).mul_left _
  set S : ℝ := ∑' n : ℤ, u n
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [u]; positivity
  have hS0 : 0 ≤ S := tsum_nonneg hu0
  set P : ℝ := ‖1 + ψ₀ (-1)‖
  refine ⟨r, hr0, P * S, A, by positivity, fun w hw z => ?_⟩
  obtain ⟨hre1, hre2⟩ := re_ge_of_mem_closedBall hw
  set y := z.im
  have hy : 0 < y := z.im_pos
  set Y := y ^ A + y ^ (-A)
  have hY : 0 ≤ Y := by positivity
  have hterm : ∀ n, ‖aTermDual ψ₀ M' z w n‖ ≤ u n * Y := fun n => hb w hw z n
  have hsn : Summable fun n : ℤ => ‖aTermDual ψ₀ M' z w n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hu.mul_right Y)
  have htsum : ‖∑' n : ℤ, aTermDual ψ₀ M' z w n‖ ≤ S * Y :=
    (norm_tsum_le_tsum_norm hsn).trans ((hsn.tsum_le_tsum hterm (hu.mul_right Y)).trans
      (le_of_eq (tsum_mul_right)))
  unfold EhatStar
  rw [norm_mul]
  calc P * ‖∑' n : ℤ, aTermDual ψ₀ M' z w n‖
      ≤ P * (S * Y) := by gcongr
    _ = _ := by ring

theorem continuous_aTermDual {w : ℂ} (h1 : 1 / 4 < w.re) (n : ℤ) :
    Continuous fun z : UpperHalfPlane => aTermDual ψ₀ M' z w n := by
  by_cases hn : n = 0
  · subst hn; simp only [aTermDual_zero]; exact continuous_const
  · simp only [aTermDual]
    have hξ : ((n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hn
    have e : (fun z : UpperHalfPlane => PhiK z.im 1 w n) =
        fun z => ((z.im : ℝ) : ℂ) ^ (1 - w) * PhiK 1 1 w (z.im * n) := by
      funext z; exact PhiK_scale z.im_pos 1 w n
    have hP : Continuous fun z : UpperHalfPlane => PhiK z.im 1 w n := by
      rw [e]
      refine (continuous_im_cpow _).mul ?_
      refine (continuousOn_PhiK_one 1 (by push_cast; linarith)).comp_continuous (by fun_prop) ?_
      intro z; exact mul_ne_zero z.im_pos.ne' hξ
    have hE : Continuous fun z : UpperHalfPlane => cexp (2 * π * I * n * z.re) := by fun_prop
    exact (hP.mul hE).mul continuous_const

/-- **Continuity of `Ê*` in `z`** for `Re w > 1/4`. -/
theorem continuous_EhatStar (h2 : ψ₀ ^ 2 ≠ 1) {w : ℂ} (h1 : 1 / 4 < w.re) :
    Continuous fun z : UpperHalfPlane => EhatStar ψ₀ M' z w := by
  obtain ⟨r, hr0, C, A, hC0, hAr, hb⟩ := exists_aTermDual_bound ψ₀ M' h2 h1
  have hw : w ∈ closedBall w r := mem_closedBall_self hr0.le
  have hA : 0 ≤ A := by have := hr0.le; linarith
  have htsum : Continuous fun z : UpperHalfPlane => ∑' n : ℤ, aTermDual ψ₀ M' z w n := by
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    set y₀ := z₀.im
    have hy₀ : 0 < y₀ := z₀.im_pos
    set U : Set UpperHalfPlane := {z | y₀ / 2 < z.im ∧ z.im < 2 * y₀}
    have hUo : IsOpen U :=
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im).inter
        (isOpen_lt UpperHalfPlane.continuous_im continuous_const)
    have hz₀ : z₀ ∈ U := ⟨by linarith, by linarith⟩
    set Ymax : ℝ := (2 * y₀) ^ A + (y₀ / 2) ^ (-A)
    have hbd : ∀ n : ℤ, ∀ z ∈ U, ‖aTermDual ψ₀ M' z w n‖ ≤ C * |(n : ℝ)| ^ (-2 : ℝ) * Ymax := by
      intro n z hz
      refine (hb w hw z n).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hy : 0 < z.im := z.im_pos
      have e1 : z.im ^ A ≤ (2 * y₀) ^ A := Real.rpow_le_rpow hy.le hz.2.le hA
      have e2 : z.im ^ (-A) ≤ (y₀ / 2) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hz.1.le (by linarith)
      linarith
    have hc := continuousOn_tsum (fun n => (continuous_aTermDual ψ₀ M' h1 n).continuousOn)
      (((Real.summable_abs_int_rpow (b := 2) (by norm_num)).mul_left C).mul_right Ymax) hbd
    exact hc.continuousAt (hUo.mem_nhds hz₀)
  unfold EhatStar
  exact continuous_const.mul htsum

end DualRegularised

end

end GaloisForLFunctions.RHTower.HalfWeight
