import GaloisForLFunctions.SquareRootThreshold.ZetaWindowPrimePolynomialStieltjesIdentity

/-!
# The window prime polynomial is a smoothed derivative of the zero-count remainder

Let `Π_ℓ(T)` be the prime polynomial of the bump window of aperture `ℓ > 0` at height `T`
(`windowPrime` is its real part), `ψ_ℓ = |Φ̂_ℓ|²` its spectral window and `S = N − M` the
remainder of the Riemann–von Mangoldt formula.  Unconditionally,

`Re Π_ℓ(T) = ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt − Corr_ℓ(T) + o(1)`   (`T → ∞`)

(`tendsto_windowPrime_add_offLineCorrection_sub`), where
`Corr_ℓ(T) = Σ_ρ m_ρ (Re K̂_ℓ(γ_ρ − T) − ψ_ℓ(Im ρ − T))` (`offLineCorrection`) collects the
displacement of the zeros off the critical line; it vanishes under RH.

**Proof.**  The zero side of the window (`windowPrime_eq`) and the Stieltjes identity on `[1, 2T]`
(`sum_zeroWindow_psi_sub_integral_eq`) give an exact identity
(`windowPrime_add_offLineCorrection_sub_eq`) whose five error terms vanish as `T → ∞`:
* the pole terms `K̂_ℓ(±i/2 − T)` decay like `T⁻⁴` (`tendsto_windowPole`);
* the zeros outside `(1, 2T]` see only the tail of `ψ_ℓ` (`tendsto_zeroTail`, dominated
  convergence against `Σ m_ρ (1 + |Im ρ|)⁻³ < ∞`);
* the archimedean density `μ` and `M' = log(t/2π)/2π` differ by `O(t⁻²)` (Stirling), so
  `∫ ψ_ℓ(τ − T) μ(τ) dτ − ∫_1^{2T} ψ_ℓ(t − T) M'(t) dt → 0` (`tendsto_archDifference`);
* the boundary terms `ψ_ℓ(T) S(2T)` and `ψ_ℓ(1 − T) S(1)` vanish since `S(t) = O(log t)`.
-/

open Complex MeasureTheory Real Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.Littlewood

/-! ### Elementary decay facts -/

theorem tendsto_abs_const_sub_atTop (c : ℝ) : Tendsto (fun T : ℝ => |c - T|) atTop atTop := by
  have h : Tendsto (fun T : ℝ => c + -T) atTop atBot :=
    tendsto_atBot_add_const_left _ c tendsto_neg_atTop_atBot
  exact tendsto_abs_atBot_atTop.comp (h.congr fun T => (sub_eq_add_neg c T).symm)

theorem tendsto_div_one_add_abs_pow {f : ℝ → ℝ} (hf : Tendsto (fun T => |f T|) atTop atTop)
    (C : ℝ) {n : ℕ} (hn : 0 < n) : Tendsto (fun T => C / (1 + |f T|) ^ n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hn.ne').comp (tendsto_atTop_add_const_left _ 1 hf))

theorem one_div_pow_four_le_pow_three (y : ℝ) : 1 / (1 + |y|) ^ 4 ≤ 1 / (1 + |y|) ^ 3 := by
  have h1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 (by norm_num))

theorem one_div_pow_three_le_inv_one_add_sq (y : ℝ) : 1 / (1 + |y|) ^ 3 ≤ (1 + y ^ 2)⁻¹ := by
  rw [one_div]
  refine inv_anti₀ (by positivity) ?_
  have h1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  calc 1 + y ^ 2 ≤ (1 + |y|) ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    _ ≤ (1 + |y|) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)

/-- `M'(t) = log(t/2π)/2π` for `t > 0`. -/
theorem smoothCountDensity_eq {t : ℝ} (ht : 0 < t) :
    smoothCountDensity t = 1 / (2 * π) * Real.log (|t| / (2 * π)) := by
  have h2π : 0 < 2 * π := by positivity
  rw [smoothCountDensity, routeKRVMBase, abs_of_pos ht,
    show t / (2 * π * Real.exp 1) = t / (2 * π) / Real.exp 1 by ring,
    Real.log_div (div_pos ht h2π).ne' (Real.exp_pos 1).ne', Real.log_exp]
  ring

/-! ### The off-line correction and the zero tail -/

/-- The off-line correction `Σ_ρ m_ρ (Re K̂_ℓ(γ_ρ − T) − ψ_ℓ(Im ρ − T))`. -/
def offLineCorrection (ℓ T : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) *
    ((paperFT (bumpKernel ℓ) (gammaOf ρ - T)).re - psi ℓ 0 ((ρ : ℂ).im - T))

/-- The zeros with ordinate outside `(1, 2T]`, weighted by `ψ_ℓ(Im ρ − T)`. -/
def zeroTail (ℓ T : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then 0 else
    (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)

section Limits

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

/-- `ψ_ℓ(y), |ψ_ℓ'(y)| ≤ C (1 + |y|)⁻⁴`. -/
theorem exists_psi_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
    psi ℓ 0 y ≤ C / (1 + |y|) ^ 4 ∧ |psiDeriv ℓ y| ≤ C / (1 + |y|) ^ 4 := by
  obtain ⟨C, hC, h⟩ := exists_abs_psi_le hℓ
  refine ⟨C, hC, fun y => ⟨?_, ?_⟩⟩ <;> rw [le_div_iff₀ (by positivity)]
  · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans (h y).1
  · exact (h y).2

theorem tendsto_psi_const_sub (c : ℝ) : Tendsto (fun T => psi ℓ 0 (c - T)) atTop (𝓝 0) := by
  obtain ⟨C, -, hd⟩ := exists_psi_decay hℓ
  refine squeeze_zero_norm (fun T => ?_) (tendsto_div_one_add_abs_pow
    (tendsto_abs_const_sub_atTop c) C (n := 4) (by norm_num))
  rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg _ _ _)]
  exact (hd _).1

/-- Summability of `m_ρ ψ_ℓ(Im ρ − T)`. -/
theorem summable_mult_psi (T : ℝ) : Summable fun ρ : zetaZeroConfig.carrier =>
    (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  obtain ⟨A₀, hA₀, hloc⟩ := RvM.zetaZeroConfig_local_count
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (psi_nonneg _ _ _))
    (fun ρ => ?_) (((window_tsum_le zetaZeroConfig hA₀ hloc T).1).mul_left C)
  have h1 := (hd ((ρ : ℂ).im - T)).1
  have h2 := one_div_pow_four_le_pow_three ((ρ : ℂ).im - T)
  calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (C * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (Nat.cast_nonneg _)
        rw [div_eq_mul_one_div C]
        exact mul_le_mul_of_nonneg_left h2 hC
    _ = C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - T|) ^ 3) := by ring

/-- **The exact identity.**  For `T ≥ 1`,
`Re Π_ℓ(T) + Corr_ℓ(T) − ∫_1^{2T} S ψ_ℓ'(· − T) = pole(T) + (∫ ψ_ℓ(τ − T) μ − ∫_1^{2T} ψ_ℓ(t − T) M')
  − tail(T) − ψ_ℓ(T) S(2T) + ψ_ℓ(1 − T) S(1)`. -/
theorem windowPrime_add_offLineCorrection_sub_eq {T : ℝ} (hT : 1 ≤ T) :
    windowPrime ℓ T + offLineCorrection ℓ T -
        ∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T) =
      windowPole ℓ T + ((∫ τ, psi ℓ 0 (τ - T) * mu τ) -
          ∫ t in (1 : ℝ)..(2 * T), psi ℓ 0 (t - T) * smoothCountDensity t) -
        zeroTail ℓ T - psi ℓ 0 T * rvmRemainder (2 * T) + psi ℓ 0 (1 - T) * rvmRemainder 1 := by
  obtain ⟨hsK, hW⟩ := windowPrime_eq hℓ T
  have hsψ := summable_mult_psi hℓ T
  have hcorr : offLineCorrection ℓ T = (∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * (paperFT (bumpKernel ℓ) (gammaOf ρ - T)).re) -
        ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) := by
    rw [offLineCorrection, ← hsK.tsum_sub hsψ]
    exact tsum_congr fun ρ => by ring
  have hle : ∀ ρ : zetaZeroConfig.carrier, 0 ≤ (zetaZeroConfig.mult ρ : ℝ) *
      psi ℓ 0 ((ρ : ℂ).im - T) := fun ρ => mul_nonneg (Nat.cast_nonneg _) (psi_nonneg _ _ _)
  have hin : Summable fun ρ : zetaZeroConfig.carrier =>
      if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) else 0 :=
    Summable.of_nonneg_of_le (fun ρ => by split_ifs; exacts [hle ρ, le_rfl])
      (fun ρ => by split_ifs; exacts [le_rfl, hle ρ]) hsψ
  have hout : Summable fun ρ : zetaZeroConfig.carrier =>
      if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then 0 else
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) :=
    Summable.of_nonneg_of_le (fun ρ => by split_ifs; exacts [le_rfl, hle ρ])
      (fun ρ => by split_ifs; exacts [hle ρ, le_rfl]) hsψ
  have hsplit : ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) =
      (∑' ρ : zetaZeroConfig.carrier, if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then
        (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) else 0) + zeroTail ℓ T := by
    rw [zeroTail, ← hin.tsum_add hout]
    exact tsum_congr fun ρ => by split_ifs <;> simp
  have hfin : (∑' ρ : zetaZeroConfig.carrier, if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) else 0) =
      ∑ ρ ∈ zeroWindowFinset 1 (2 * T), (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T) := by
    rw [tsum_eq_sum (s := zeroWindowFinset 1 (2 * T))]
    · exact Finset.sum_congr rfl fun ρ hρ => if_pos (mem_zeroWindowFinset.mp hρ)
    · intro ρ hρ; exact if_neg fun h => hρ (mem_zeroWindowFinset.mpr h)
  have hSt := sum_zeroWindow_psi_sub_integral_eq hℓ hT
  linarith

/-- The transform of `K_ℓ` decays like `(1 + |Re z|)⁻⁴` in horizontal strips. -/
theorem norm_paperFT_bumpKernel_le (z : ℂ) : ‖paperFT (bumpKernel ℓ) z‖ ≤
    2 ^ 4 * Real.exp (|z.im| * (2 * ℓ)) * ((∫ u, ‖bumpKernel ℓ u‖) +
      ∫ u, ‖iteratedDeriv 4 (bumpKernel ℓ) u‖) / (1 + |z.re|) ^ 4 := by
  rw [le_div_iff₀ (by positivity)]
  exact norm_paperFT_mul_one_add_pow_le (bumpKernel_contDiff hℓ (n := 4)) (bumpKernel_support hℓ) z

/-- The pole terms vanish at large height. -/
theorem tendsto_windowPole : Tendsto (windowPole ℓ) atTop (𝓝 0) := by
  set B := 2 ^ 4 * Real.exp (|(1 / 2 : ℝ)| * (2 * ℓ)) * ((∫ u, ‖bumpKernel ℓ u‖) +
      ∫ u, ‖iteratedDeriv 4 (bumpKernel ℓ) u‖) with hB
  refine squeeze_zero_norm (fun T => ?_) (tendsto_div_one_add_abs_pow
    (tendsto_abs_const_sub_atTop 0) (2 * B) (n := 4) (by norm_num))
  have h1 := norm_paperFT_bumpKernel_le hℓ (I / 2 - T)
  have h2 := norm_paperFT_bumpKernel_le hℓ (-I / 2 - T)
  have hre1 : (I / 2 - T : ℂ).re = 0 - T := by simp
  have hre2 : (-I / 2 - T : ℂ).re = 0 - T := by simp
  have him1 : |(I / 2 - T : ℂ).im| = |(1 / 2 : ℝ)| := by simp
  have him2 : |(-I / 2 - T : ℂ).im| = |(1 / 2 : ℝ)| := by simp; norm_num
  rw [hre1, him1, ← hB] at h1
  rw [hre2, him2, ← hB] at h2
  rw [Real.norm_eq_abs, windowPole]
  calc |(paperFT (bumpKernel ℓ) (I / 2 - T) + paperFT (bumpKernel ℓ) (-I / 2 - T)).re|
      ≤ ‖paperFT (bumpKernel ℓ) (I / 2 - T) + paperFT (bumpKernel ℓ) (-I / 2 - T)‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖paperFT (bumpKernel ℓ) (I / 2 - T)‖ + ‖paperFT (bumpKernel ℓ) (-I / 2 - T)‖ :=
        norm_add_le _ _
    _ ≤ 2 * B / (1 + |0 - T|) ^ 4 := by rw [mul_div_assoc]; linarith

/-- The boundary term at `2T`: `ψ_ℓ(T) S(2T) → 0`, since `S(t) = O(log t)`. -/
theorem tendsto_psi_mul_rvmRemainder_two_mul :
    Tendsto (fun T => psi ℓ 0 T * rvmRemainder (2 * T)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  obtain ⟨Cr, hCr, T₀, -, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  have hlim := tendsto_div_one_add_abs_pow (tendsto_abs_const_sub_atTop 0) (2 * C * Cr)
    (n := 3) (by norm_num)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max T₀ 1)] with T hT
  have hT1 : 1 ≤ T := le_of_max_le_right hT
  have hT0 : T₀ ≤ 2 * T := by linarith [le_of_max_le_left hT]
  have hS : |rvmRemainder (2 * T)| ≤ Cr * (2 * T) :=
    (hrem (2 * T) hT0).trans (mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) hCr.le)
  have hψ := (hd T).1
  have habs : |0 - T| = T := by rw [zero_sub, abs_neg, abs_of_pos (by linarith)]
  rw [habs]
  rw [abs_of_pos (by linarith : (0 : ℝ) < T)] at hψ
  have hfrac : T / (1 + T) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have heq : C / (1 + T) ^ 4 * (Cr * (2 * T)) = 2 * C * Cr / (1 + T) ^ 3 * (T / (1 + T)) := by
    field_simp
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psi_nonneg _ _ _)]
  calc psi ℓ 0 T * |rvmRemainder (2 * T)| ≤ C / (1 + T) ^ 4 * (Cr * (2 * T)) :=
        mul_le_mul hψ hS (abs_nonneg _) (by positivity)
    _ ≤ 2 * C * Cr / (1 + T) ^ 3 := by
        rw [heq]; exact mul_le_of_le_one_right (by positivity) hfrac

/-- The boundary term at `1`: `ψ_ℓ(1 − T) S(1) → 0`. -/
theorem tendsto_psi_one_sub_mul :
    Tendsto (fun T => psi ℓ 0 (1 - T) * rvmRemainder 1) atTop (𝓝 0) := by
  simpa using (tendsto_psi_const_sub hℓ 1).mul_const (rvmRemainder 1)

/-- The zeros outside `(1, 2T]` do not contribute in the limit. -/
theorem tendsto_zeroTail : Tendsto (zeroTail ℓ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  obtain ⟨A₀, hA₀, hloc⟩ := RvM.zetaZeroConfig_local_count
  have hs := ((window_tsum_le zetaZeroConfig hA₀ hloc 0).1).mul_left (8 * C)
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun T (ρ : zetaZeroConfig.carrier) => if 1 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T then 0 else
      (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T))
    (g := fun _ => (0 : ℝ)) hs ?_ ?_
  · simp only [tsum_zero] at h
    exact h
  · intro ρ
    by_cases h1 : 1 < (ρ : ℂ).im
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ((ρ : ℂ).im)] with T hT
      rw [if_pos ⟨h1, by linarith⟩]
    · have : Tendsto (fun T => (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)) atTop
          (𝓝 0) := by
        simpa using (tendsto_psi_const_sub hℓ ((ρ : ℂ).im)).const_mul (zetaZeroConfig.mult ρ : ℝ)
      exact this.congr' (Eventually.of_forall fun T => (if_neg fun h => h1 h.1).symm)
  · filter_upwards [eventually_ge_atTop 2] with T hT ρ
    have hb0 : 0 ≤ 8 * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - 0|) ^ 3) := by
      positivity
    split_ifs with hw
    · simpa using hb0
    · have hgeo : 1 + |(ρ : ℂ).im| ≤ 2 * (1 + |(ρ : ℂ).im - T|) := by
        have hcase : (ρ : ℂ).im ≤ 1 ∨ 2 * T < (ρ : ℂ).im := by
          by_contra hc
          push Not at hc
          exact hw ⟨hc.1, hc.2⟩
        rcases hcase with h | h <;> rcases abs_cases ((ρ : ℂ).im) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
          rcases abs_cases ((ρ : ℂ).im - T) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;> linarith
      have hpow : (1 + |(ρ : ℂ).im|) ^ 3 ≤ 8 * (1 + |(ρ : ℂ).im - T|) ^ 3 := by
        calc (1 + |(ρ : ℂ).im|) ^ 3 ≤ (2 * (1 + |(ρ : ℂ).im - T|)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hgeo 3
          _ = 8 * (1 + |(ρ : ℂ).im - T|) ^ 3 := by ring
      have hψ := (hd ((ρ : ℂ).im - T)).1
      have h43 := one_div_pow_four_le_pow_three ((ρ : ℂ).im - T)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (psi_nonneg _ _ _)),
        sub_zero]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
      calc (zetaZeroConfig.mult ρ : ℝ) * psi ℓ 0 ((ρ : ℂ).im - T)
          ≤ (zetaZeroConfig.mult ρ : ℝ) * (C * (1 / (1 + |(ρ : ℂ).im - T|) ^ 3)) := by
            refine mul_le_mul_of_nonneg_left (hψ.trans ?_) hm
            rw [div_eq_mul_one_div C]; exact mul_le_mul_of_nonneg_left h43 hC
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (C * (8 / (1 + |(ρ : ℂ).im|) ^ 3)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC) hm
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
        _ = 8 * C * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im|) ^ 3) := by ring

/-- `∫ (1 + s²)⁻¹`-domination of the shifted archimedean integrand. -/
theorem integrable_psi_mul_mu_shift (T : ℝ) :
    Integrable fun s : ℝ => psi ℓ 0 s * mu (s + T) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  obtain ⟨K₂, hK₂, hmu⟩ := EF.abs_mu_le_of_gammaFacts gammaFacts
  have hmuc : Continuous mu := gammaFacts.smooth.continuous
  refine (integrable_inv_one_add_sq.const_mul (C * K₂ * (1 + |T|))).mono'
    ((continuous_psi_zero hℓ).mul (hmuc.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  have hs1 : 1 ≤ 1 + |s| := by linarith [abs_nonneg s]
  have hmu' : |mu (s + T)| ≤ K₂ * ((1 + |T|) * (1 + |s|)) := by
    refine (hmu _).trans (mul_le_mul_of_nonneg_left ?_ hK₂)
    have hr : (1 + |s + T|) ^ (1 / 2 : ℝ) ≤ 1 + |s + T| := by
      calc (1 + |s + T|) ^ (1 / 2 : ℝ) ≤ (1 + |s + T|) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (s + T)]) (by norm_num)
        _ = 1 + |s + T| := Real.rpow_one _
    refine hr.trans ?_
    nlinarith [abs_add_le s T, abs_nonneg s, abs_nonneg T]
  have hψ := (hd s).1
  have h3 := one_div_pow_three_le_inv_one_add_sq s
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psi_nonneg _ _ _)]
  calc psi ℓ 0 s * |mu (s + T)| ≤ C / (1 + |s|) ^ 4 * (K₂ * ((1 + |T|) * (1 + |s|))) :=
        mul_le_mul hψ hmu' (abs_nonneg _) (by positivity)
    _ = C * K₂ * (1 + |T|) * (1 / (1 + |s|) ^ 3) := by field_simp
    _ ≤ C * K₂ * (1 + |T|) * (1 + s ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

omit hℓ in
theorem measurable_smoothCountDensity : Measurable smoothCountDensity := by
  unfold smoothCountDensity
  exact ((Real.measurable_log.comp (measurable_id.div_const _)).add_const 1).div_const _

/-- The archimedean density and the Riemann–von Mangoldt density give the same window mass. -/
theorem tendsto_archDifference :
    Tendsto (fun T => (∫ τ, psi ℓ 0 (τ - T) * mu τ) -
      ∫ t in (1 : ℝ)..(2 * T), psi ℓ 0 (t - T) * smoothCountDensity t) atTop (𝓝 0) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  obtain ⟨Cs, hCs, hst⟩ := exists_stirling
  obtain ⟨K₂, hK₂, hmu⟩ := EF.abs_mu_le_of_gammaFacts gammaFacts
  have hmuc : Continuous mu := gammaFacts.smooth.continuous
  have hψc := continuous_psi_zero hℓ
  -- the integrand after the shift `τ = s + T`
  let F : ℝ → ℝ → ℝ := fun T s => psi ℓ 0 s * mu (s + T) -
    (Ioc (1 - T) T).indicator (fun s => psi ℓ 0 s * smoothCountDensity (s + T)) s
  have hrep : ∀ T : ℝ, 1 ≤ T → (∫ τ, psi ℓ 0 (τ - T) * mu τ) -
      ∫ t in (1 : ℝ)..(2 * T), psi ℓ 0 (t - T) * smoothCountDensity t = ∫ s, F T s := by
    intro T hT
    have h1 : ∫ τ, psi ℓ 0 (τ - T) * mu τ = ∫ s, psi ℓ 0 s * mu (s + T) := by
      rw [← integral_add_right_eq_self (fun τ => psi ℓ 0 (τ - T) * mu τ) T]
      simp only [add_sub_cancel_right]
    have h2 : ∫ t in (1 : ℝ)..(2 * T), psi ℓ 0 (t - T) * smoothCountDensity t =
        ∫ s, (Ioc (1 - T) T).indicator (fun s => psi ℓ 0 s * smoothCountDensity (s + T)) s := by
      have hc := intervalIntegral.integral_comp_add_right
        (fun t => psi ℓ 0 (t - T) * smoothCountDensity t) T (a := 1 - T) (b := T)
      simp only [add_sub_cancel_right, sub_add_cancel] at hc
      rw [show T + T = 2 * T by ring] at hc
      rw [← hc, intervalIntegral.integral_of_le (by linarith), integral_indicator measurableSet_Ioc]
    have hcont : ContinuousOn (fun s => psi ℓ 0 s * smoothCountDensity (s + T)) (Icc (1 - T) T) :=
      hψc.continuousOn.mul (continuousOn_smoothCountDensity.comp
        (continuous_id.add continuous_const).continuousOn fun s hs => by
          simp only [mem_Ioi]; linarith [hs.1])
    have hint2 : Integrable ((Ioc (1 - T) T).indicator
        (fun s => psi ℓ 0 s * smoothCountDensity (s + T))) :=
      ((hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
    rw [h1, h2, ← integral_sub (integrable_psi_mul_mu_shift hℓ T) hint2]
  -- dominated convergence
  have hlim : Tendsto (fun T => ∫ s, F T s) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => C * (Cs + 2 * K₂) * (1 + s ^ 2)⁻¹) ?_ ?_
      (integrable_inv_one_add_sq.const_mul _) ?_
    · refine Eventually.of_forall fun T => ?_
      exact ((hψc.measurable.mul (hmuc.measurable.comp (measurable_id.add_const T))).sub
        ((hψc.measurable.mul (measurable_smoothCountDensity.comp (measurable_id.add_const T))
          ).indicator measurableSet_Ioc)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 2] with T hT
      refine Eventually.of_forall fun s => ?_
      have hψ := (hd s).1
      have h43 := one_div_pow_four_le_pow_three s
      have h3 := one_div_pow_three_le_inv_one_add_sq s
      have hψ0 := psi_nonneg ℓ 0 s
      have hs1 : 1 ≤ 1 + |s| := by linarith [abs_nonneg s]
      have hψ3 : psi ℓ 0 s * (1 + |s|) ≤ C * (1 / (1 + |s|) ^ 3) := by
        rw [le_div_iff₀ (by positivity)] at hψ
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        calc psi ℓ 0 s * (1 + |s|) * (1 + |s|) ^ 3 = psi ℓ 0 s * (1 + |s|) ^ 4 := by ring
          _ ≤ C := hψ
      have hψ3' : psi ℓ 0 s ≤ C * (1 / (1 + |s|) ^ 3) :=
        (le_mul_of_one_le_right hψ0 hs1).trans hψ3
      have hfin : C * (1 / (1 + |s|) ^ 3) ≤ C * (1 + s ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h3 hC
      simp only [F, Real.norm_eq_abs]
      by_cases hsI : s ∈ Ioc (1 - T) T
      · rw [indicator_of_mem hsI, ← mul_sub, abs_mul, abs_of_nonneg hψ0]
        have ht1 : 1 ≤ |s + T| := by
          rw [abs_of_pos (by linarith [hsI.1])]; linarith [hsI.1]
        have hdiff : |mu (s + T) - smoothCountDensity (s + T)| ≤ Cs := by
          rw [smoothCountDensity_eq (by linarith [hsI.1])]
          refine (hst (s + T) ht1).trans ?_
          rw [div_le_iff₀ (pow_pos (by linarith [hsI.1]) 2)]
          have : 1 ≤ (s + T) ^ 2 := by rw [← sq_abs]; nlinarith
          nlinarith
        calc psi ℓ 0 s * |mu (s + T) - smoothCountDensity (s + T)| ≤ psi ℓ 0 s * Cs :=
              mul_le_mul_of_nonneg_left hdiff hψ0
          _ ≤ C * (1 + s ^ 2)⁻¹ * Cs := mul_le_mul_of_nonneg_right (hψ3'.trans hfin) hCs
          _ ≤ C * (Cs + 2 * K₂) * (1 + s ^ 2)⁻¹ := by
              have : 0 ≤ C * (1 + s ^ 2)⁻¹ := by positivity
              nlinarith
      · rw [indicator_of_notMem hsI, sub_zero, abs_mul, abs_of_nonneg hψ0]
        have hTs : T ≤ 1 + |s| := by
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at hsI
          rcases hsI with h | h <;> rcases abs_cases s with ⟨h1, -⟩ | ⟨h1, -⟩ <;> linarith
        have hmu' : |mu (s + T)| ≤ 2 * K₂ * (1 + |s|) := by
          refine (hmu _).trans ?_
          have hr : (1 + |s + T|) ^ (1 / 2 : ℝ) ≤ 1 + |s + T| := by
            calc (1 + |s + T|) ^ (1 / 2 : ℝ) ≤ (1 + |s + T|) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (s + T)])
                    (by norm_num)
              _ = 1 + |s + T| := Real.rpow_one _
          have hst' : 1 + |s + T| ≤ 2 * (1 + |s|) := by
            have := abs_add_le s T
            rw [abs_of_pos (by linarith : (0 : ℝ) < T)] at this
            linarith
          calc K₂ * (1 + |s + T|) ^ (1 / 2 : ℝ) ≤ K₂ * (2 * (1 + |s|)) :=
                mul_le_mul_of_nonneg_left (hr.trans hst') hK₂
            _ = 2 * K₂ * (1 + |s|) := by ring
        calc psi ℓ 0 s * |mu (s + T)| ≤ psi ℓ 0 s * (2 * K₂ * (1 + |s|)) :=
              mul_le_mul_of_nonneg_left hmu' hψ0
          _ = 2 * K₂ * (psi ℓ 0 s * (1 + |s|)) := by ring
          _ ≤ 2 * K₂ * (C * (1 + s ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left (hψ3.trans hfin) (by positivity)
          _ ≤ C * (Cs + 2 * K₂) * (1 + s ^ 2)⁻¹ := by
              have : 0 ≤ C * (1 + s ^ 2)⁻¹ := by positivity
              nlinarith
    · refine Eventually.of_forall fun s => ?_
      have hbound : ∀ᶠ T in atTop, ‖F T s‖ ≤ psi ℓ 0 s * (Cs / (s + T) ^ 2) := by
        filter_upwards [eventually_ge_atTop (|s| + 2)] with T hT
        have hsI : s ∈ Ioc (1 - T) T := by
          constructor <;> linarith [neg_abs_le s, le_abs_self s]
        simp only [F, Real.norm_eq_abs]
        rw [indicator_of_mem hsI, ← mul_sub, abs_mul, abs_of_nonneg (psi_nonneg _ _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (psi_nonneg _ _ _)
        have hpos : 0 < s + T := by linarith [neg_abs_le s]
        rw [smoothCountDensity_eq hpos]
        exact hst (s + T) (by rw [abs_of_pos hpos]; linarith [neg_abs_le s])
      have hT2 : Tendsto (fun T => psi ℓ 0 s * (Cs / (s + T) ^ 2)) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := Cs)).div_atTop
          ((tendsto_pow_atTop (n := 2) (by norm_num)).comp
            (tendsto_atTop_add_const_left atTop s tendsto_id))
        simpa using this.const_mul (psi ℓ 0 s)
      exact squeeze_zero_norm' hbound hT2
  rw [integral_zero] at hlim
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop 1] with T hT
    exact (hrep T hT).symm)

/-- **The window prime polynomial reads the zero-count remainder.**  As `T → ∞`,
`Re Π_ℓ(T) + Corr_ℓ(T) − ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt → 0`. -/
theorem tendsto_windowPrime_add_offLineCorrection_sub :
    Tendsto (fun T => windowPrime ℓ T + offLineCorrection ℓ T -
      ∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T)) atTop (𝓝 0) := by
  have h := ((((tendsto_windowPole hℓ).add (tendsto_archDifference hℓ)).sub
    (tendsto_zeroTail hℓ)).sub (tendsto_psi_mul_rvmRemainder_two_mul hℓ)).add
    (tendsto_psi_one_sub_mul hℓ)
  simp only [add_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact (windowPrime_add_offLineCorrection_sub_eq hℓ hT).symm

end Limits

end GaloisForLFunctions.SquareRootThreshold
