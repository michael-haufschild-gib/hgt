import GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.ArchimedeanAndKernelFoundations
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount

/-!
# Unit-Window Self-Absorption of `Π_{F_{c log T}}` and the Explicit-Formula No-Go

For `F_L = heckeAvgBump L` at logarithmic scale `L = c log T` (`c > 0`), the prime polynomial
`Π_{F_L}(N*(L), -γ / 2π)` has `ℓ¹` envelope `≍ T^{2c} / log T ≫ T^c`. Integrating across `[T, T + 1)`
via Plancherel on near zeros and exact hyperbolic sinc decay on far zeros proves that
`Π_{F_{c log T}}` carries at most an `O(1 / log T)` fraction of the Hecke defect `E_γ(c log T)`:

1. **Sharp reflection bound** (`abs_re_W_le_collidedForm`, `norm_primePolynomial_heckeAvgBump_le`):
   `0 ≤ Δ_Z(f) ≤ 2 D_Z(f)` implies `|Re W_Z(f, f)| ≤ D_Z(f)` for every `ZeroConfig` `Z`, whence
   `‖Π_{F_L}(N*(L), -γ / 2π)‖ ≤ |Re A_{F_L}(-γ / 2π)| + D_ζ(twist γ F_L)`.
2. **Plancherel unit-window bound** (`sinh_sq_mul_le_four_depthKernel`,
   `unitWindow_integral_normSq_tr_twist_heckeAvgBump_le`):
   Pointwise `sinh²(δ u) ≤ 4 depthKernel L δ` on `|u| ≤ L + 1/4` (`L ≥ 1`, `|δ| ≤ 1/2`) and
   `integral_norm_sq_paperFT_of_memLp` yield
   `∫_{T}^{T+1} |tr(twist γ F_L)(s)|² dγ ≤ π / L + (8π / L) depthKernel L (Re s - 1/2)`.
3. **Unconditional unit-window self-absorption for `ζ`**
   (`exists_unitWindow_integral_norm_primePolynomial_le`):
   For every `c > 0`, there exist `C₁ > 0` and universal `C₂ > 0` such that eventually in `T`,
   `∫_{T}^{T+1} ‖Π_{F_{c log T}}(N*(c log T), -γ / 2π)‖ dγ ≤ C₁ + (C₂ / (c log T)) ∫_{T}^{T+1} E_γ(c log T) dγ`.
4. **Universal explicit-formula / `RiemannVonMangoldt` no-go**
   (`exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation`):
   On `Z' = superpose zetaZeroConfig clusterConfig` (which satisfies `RiemannVonMangoldt Z'` and
   retains all critical-line zeros of `ζ`), the explicit-formula prime functional fails to bound
   the Hecke defect up to any additive constant for every `c > 0` and `α ≥ 0`.
-/

set_option autoImplicit false

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators Real ComplexConjugate ContDiff
open _root_.RHTower _root_.Zeta23

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

open GaloisForLFunctions.ConjugateDiagonalGeometry
open ArithmeticPolarization SquareRootThreshold

/-! ## §1. Configuration-general Hecke defect, continuity, and `|Re W_Z| ≤ D_Z` -/

/-- Symmetric Hecke defect of a test profile `f : ℝ → ℂ` on an arbitrary `ZeroConfig` `Z`. -/
def configHeckeDefect (Z : ZeroConfig) (f : ℝ → ℂ) (L : ℝ) : ℝ :=
  ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ) * depthKernel L ((ρ : ℂ).re - 1 / 2)

theorem configHeckeDefect_zeta_eq (f : CompactTest) (L : ℝ) :
    configHeckeDefect zetaZeroConfig f.1 L = heckeDefect f L := by
  simp only [configHeckeDefect, heckeDefect, zetaWeight, zetaDepth]

theorem configHeckeDefect_zeta_twist_eq (γ L : ℝ) :
    configHeckeDefect zetaZeroConfig (twist γ baseBump) L = heckeDefect (baseTwistTest γ) L :=
  configHeckeDefect_zeta_eq (baseTwistTest γ) L

/-- Strip bound `|(ρ : ℂ).re - 1/2| ≤ 1/2` for any zero `ρ` of a `ZeroConfig`. -/
theorem abs_re_sub_half_le_of_zeroConfig (Z : ZeroConfig) (ρ : Z.carrier) :
    |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
  have h := Z.strip ρ ρ.2
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-- Summability of the collided form and Hecke defect on any `ZeroConfig` with summable Lorentzian
weight at `0`. -/
theorem summable_collided_of_lorentz {Z : ZeroConfig}
    (hsum0 : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  set a := max R 0
  have ha0 : 0 ≤ a := le_max_right _ _
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => by
    have : u ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport f hu)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  set K := Real.exp a * envelope f ^ 2
  refine Summable.of_nonneg_of_le
    (fun ρ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
    (fun ρ => ?_) (hsum0.mul_left K)
  have hstrip := Z.strip ρ ρ.2
  have htw0 : twist 0 f = f := by
    ext u; simp [twist]
  have hnorm := norm_tr_twist_le hf ha0 hsupp 0 hstrip
  rw [htw0, sub_zero] at hnorm
  have hsq : Complex.normSq (tr f ρ) ≤ K * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    rw [Complex.normSq_eq_norm_sq]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hden : 1 + (ρ : ℂ).im ^ 2 ≤ ((1 + |(ρ : ℂ).im|) ^ 2) ^ 2 := by
      have habs : 0 ≤ |(ρ : ℂ).im| := abs_nonneg _
      have hsq_im : (ρ : ℂ).im ^ 2 = |(ρ : ℂ).im| ^ 2 := (sq_abs _).symm
      rw [hsq_im]; nlinarith
    have hexp : (Real.exp (a / 2) * envelope f / (1 + |(ρ : ℂ).im|) ^ 2) ^ 2 =
        K * (1 / ((1 + |(ρ : ℂ).im|) ^ 2) ^ 2) := by
      dsimp [K]
      rw [div_pow, mul_pow, ← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (a / 2) = a by push_cast; ring]
      ring
    rw [hexp] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity) hden) (by positivity))
  have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  calc (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)
      ≤ (Z.mult ρ : ℝ) * (K * (1 / (1 + (ρ : ℂ).im ^ 2))) := mul_le_mul_of_nonneg_left hsq hm0
    _ = K * ((Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by ring

theorem summable_configHeckeDefect_of_lorentz {Z : ZeroConfig}
    (hsum0 : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)))
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (L : ℝ) :
    Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ) * depthKernel L ((ρ : ℂ).re - 1 / 2) := by
  refine Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
      (depthKernel_nonneg _ _))
    (fun ρ => mul_le_mul_of_nonneg_left
      (depthKernel_mono_depth L (by simpa using abs_re_sub_half_le_of_zeroConfig Z ρ))
      (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))
    ((summable_collided_of_lorentz hsum0 hf hfc).mul_right (depthKernel L (1 / 2)))

/-- Dictionary `tr (twist γ f) s = paperFT (u ↦ f u * e^{(Re s - 1/2) u}) (s.im - γ)`. -/
theorem tr_twist_eq_paperFT (f : ℝ → ℂ) (γ : ℝ) (s : ℂ) :
    tr (twist γ f) s =
      paperFT (fun u : ℝ => f u * Complex.exp (((s.re - 1 / 2 : ℝ) : ℂ) * (u : ℂ)))
        ((s.im - γ : ℝ) : ℂ) := by
  rw [tr_twist, tr_eq, paperFT]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;> simp

/-- Continuity of `γ ↦ tr (twist γ f) s` for any continuous compactly supported `f : ℝ → ℂ`. -/
theorem continuous_tr_twist {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (s : ℂ) :
    Continuous (fun γ : ℝ => tr (twist γ f) s) := by
  set h : ℝ → ℂ := fun u => f u * Complex.exp (((s.re - 1 / 2 : ℝ) : ℂ) * (u : ℂ))
  have hhc : HasCompactSupport h := hfc.mul_right
  have hcont_h : Continuous h :=
    hf.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hint1 : Integrable h := hcont_h.integrable_of_hasCompactSupport hhc
  have hint2 : Integrable (fun u : ℝ => (u : ℂ) * h u) :=
    (Complex.continuous_ofReal.mul hcont_h).integrable_of_hasCompactSupport hhc.mul_left
  have hcont_pft : Continuous (fun x : ℝ => paperFT h (x : ℂ)) :=
    continuous_iff_continuousAt.mpr fun x =>
      (KernelStrip.hasDerivAt_paperFT hint1 hint2 x).continuousAt
  have heq : (fun γ : ℝ => tr (twist γ f) s) =
      fun γ : ℝ => paperFT h ((s.im - γ : ℝ) : ℂ) :=
    funext fun γ => tr_twist_eq_paperFT f γ s
  rw [heq]
  exact hcont_pft.comp (continuous_const.sub continuous_id)

/-- Joint continuity of `(γ, L) ↦ configHeckeDefect Z (twist γ baseBump) L` for any `ZeroConfig`
with summable Lorentzian weight at `0`. -/
theorem continuous_configHeckeDefect_pair {Z : ZeroConfig}
    (hsum0 : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) :
    Continuous (fun p : ℝ × ℝ => configHeckeDefect Z (twist p.1 baseBump) p.2) := by
  obtain ⟨C₁, hC₁, hpw₁⟩ := exists_norm_tr_twist_baseBump_le_pow 1
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  set R : ℝ := ‖p₀‖ + 1
  have hR0 : 0 ≤ R := by positivity
  set M₀ : ℝ := max (2 * Real.exp (1 / 4)) (2 * C₁ ^ 2)
  set K_dom : ℝ := (2 + 2 * R ^ 2) * M₀ * depthKernel R (1 / 2)
  have hcont_on : ContinuousOn
      (fun p : ℝ × ℝ => configHeckeDefect Z (twist p.1 baseBump) p.2)
      (Metric.closedBall (0 : ℝ × ℝ) R) := by
    refine continuousOn_tsum
      (f := fun (ρ : Z.carrier) (p : ℝ × ℝ) =>
        (Z.mult ρ : ℝ) * Complex.normSq (tr (twist p.1 baseBump) ρ) *
          depthKernel p.2 ((ρ : ℂ).re - 1 / 2))
      (u := fun ρ : Z.carrier => K_dom * ((Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))))
      (fun ρ => ?_) (hsum0.mul_left K_dom) (fun ρ p hp => ?_)
    · refine ((continuous_const.mul
        (Complex.continuous_normSq.comp
          ((continuous_tr_twist (contDiff_baseBump (n := ⊤)).continuous
            hasCompactSupport_baseBump ρ).comp continuous_fst))).mul ?_).continuousOn
      unfold depthKernel
      exact (continuous_const.mul (Real.continuous_cosh.comp
        (continuous_const.mul continuous_snd))).sub continuous_const
    · rw [Metric.mem_closedBall, dist_zero_right] at hp
      have hp1 : |p.1| ≤ R := (Real.norm_eq_abs p.1 ▸ norm_fst_le p).trans hp
      have hp2 : |p.2| ≤ R := (Real.norm_eq_abs p.2 ▸ norm_snd_le p).trans hp
      have hstrip := abs_re_sub_half_le_of_zeroConfig Z ρ
      have hdk_le : depthKernel p.2 ((ρ : ℂ).re - 1 / 2) ≤ depthKernel R (1 / 2) := by
        unfold depthKernel
        have hcosh : Real.cosh (2 * ((ρ : ℂ).re - 1 / 2) * p.2) ≤ Real.cosh (2 * (1 / 2) * R) := by
          rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_mul, abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
            abs_of_nonneg hR0]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hstrip zero_le_two) hp2
            (abs_nonneg _) (by positivity)
        linarith
      have hnsq_diff : Complex.normSq (tr (twist p.1 baseBump) ρ) ≤
          M₀ * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) := by
        by_cases hd : |(ρ : ℂ).im - p.1| ≤ 1
        · have hb : Complex.normSq (tr (twist p.1 baseBump) ρ) ≤ Real.exp (1 / 4) := by
            rw [Complex.normSq_eq_norm_sq]
            refine (pow_le_pow_left₀ (norm_nonneg _)
              (norm_tr_twist_baseBump_le_exp p.1 hstrip) 2).trans_eq ?_
            rw [← Real.exp_nat_mul]; norm_num
          have hden : 1 + ((ρ : ℂ).im - p.1) ^ 2 ≤ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) hd 2
            rw [sq_abs] at this; linarith
          have hhalf : (1 / 2 : ℝ) ≤ 1 / (1 + ((ρ : ℂ).im - p.1) ^ 2) :=
            one_div_le_one_div_of_le (by positivity) hden
          have hM₀ : 2 * Real.exp (1 / 4) ≤ M₀ := le_max_left _ _
          calc Complex.normSq (tr (twist p.1 baseBump) ρ)
              ≤ Real.exp (1 / 4) := hb
            _ = (2 * Real.exp (1 / 4)) * (1 / 2) := by ring
            _ ≤ M₀ * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) :=
                mul_le_mul hM₀ hhalf (by norm_num) (by positivity)
        · have hd' : 1 < |(ρ : ℂ).im - p.1| := not_le.mp hd
          have hne : (ρ : ℂ).im ≠ p.1 := fun heq => by
            rw [heq, sub_self, abs_zero] at hd'; linarith
          have hpw := hpw₁ p.1 ρ hstrip hne
          rw [pow_one] at hpw
          have hsq := pow_le_pow_left₀ (norm_nonneg _) hpw 2
          rw [← Complex.normSq_eq_norm_sq, div_pow, sq_abs] at hsq
          have hd_sq : 1 ≤ ((ρ : ℂ).im - p.1) ^ 2 := by
            have := pow_le_pow_left₀ zero_le_one hd'.le 2
            simpa [sq_abs] using this
          have hfrac : 1 / ((ρ : ℂ).im - p.1) ^ 2 ≤ 2 * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            linarith
          have hM₀ : 2 * C₁ ^ 2 ≤ M₀ := le_max_right _ _
          calc Complex.normSq (tr (twist p.1 baseBump) ρ)
              ≤ C₁ ^ 2 * (1 / ((ρ : ℂ).im - p.1) ^ 2) := by
                simpa [div_eq_mul_inv] using hsq
            _ ≤ C₁ ^ 2 * (2 * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2))) :=
                mul_le_mul_of_nonneg_left hfrac (sq_nonneg C₁)
            _ = (2 * C₁ ^ 2) * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) := by ring
            _ ≤ M₀ * (1 / (1 + ((ρ : ℂ).im - p.1) ^ 2)) :=
                mul_le_mul_of_nonneg_right hM₀ (by positivity)
      have hshift : 1 / (1 + ((ρ : ℂ).im - p.1) ^ 2) ≤
          (2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hp1_sq : p.1 ^ 2 ≤ R ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hp1 2
          rwa [sq_abs] at this
        have hquad : (ρ : ℂ).im ^ 2 ≤ 2 * ((ρ : ℂ).im - p.1) ^ 2 + 2 * p.1 ^ 2 := by
          nlinarith [sq_nonneg (((ρ : ℂ).im - p.1) - p.1)]
        nlinarith [sq_nonneg ((ρ : ℂ).im - p.1)]
      have hnn : 0 ≤ (Z.mult ρ : ℝ) * Complex.normSq (tr (twist p.1 baseBump) ρ) *
          depthKernel p.2 ((ρ : ℂ).re - 1 / 2) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
          (depthKernel_nonneg _ _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
      have hM0_nn : 0 ≤ M₀ := le_trans (by positivity) (le_max_left _ _)
      calc (Z.mult ρ : ℝ) * Complex.normSq (tr (twist p.1 baseBump) ρ) *
            depthKernel p.2 ((ρ : ℂ).re - 1 / 2)
          ≤ (Z.mult ρ : ℝ) * (M₀ * ((2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)))) *
              depthKernel R (1 / 2) := by
            refine mul_le_mul
              (mul_le_mul_of_nonneg_left
                (hnsq_diff.trans (mul_le_mul_of_nonneg_left hshift hM0_nn)) hm0)
              hdk_le (depthKernel_nonneg _ _) (by positivity)
        _ = K_dom * ((Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by
            dsimp [K_dom]; ring
  exact hcont_on.continuousAt (Metric.closedBall_mem_nhds_of_mem
    (by simp [Metric.mem_ball, dist_zero_right, R]))

private theorem continuous_slice_left {F : ℝ × ℝ → ℝ} (hF : Continuous F) (L : ℝ) :
    Continuous (fun γ : ℝ => F (γ, L)) :=
  hF.comp (continuous_id.prodMk continuous_const)

/-- Joint continuity of `(γ, L) ↦ heckeDefect (baseTwistTest γ) L` for `ζ`. -/
theorem continuous_heckeDefect_pair :
    Continuous (fun p : ℝ × ℝ => heckeDefect (baseTwistTest p.1) p.2) := by
  have hsum0 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using
      ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
        (g := fun z : ℂ => 1 / (1 + (0 - z.im) ^ 2)) (fun _ => by positivity)
        (RHTower.summable_lorentzMassTerm 0)
  have heq : (fun p : ℝ × ℝ => heckeDefect (baseTwistTest p.1) p.2) =
      fun p : ℝ × ℝ => configHeckeDefect zetaZeroConfig (twist p.1 baseBump) p.2 :=
    funext fun p => (configHeckeDefect_zeta_twist_eq p.1 p.2).symm
  rw [heq]
  exact continuous_configHeckeDefect_pair hsum0

theorem continuous_heckeDefect_gamma (L : ℝ) :
    Continuous (fun γ : ℝ => heckeDefect (baseTwistTest γ) L) :=
  continuous_slice_left continuous_heckeDefect_pair L

theorem integrableOn_heckeDefect_Icc (T₁ T₂ L : ℝ) :
    IntegrableOn (fun γ : ℝ => heckeDefect (baseTwistTest γ) L) (Icc T₁ T₂) volume :=
  (continuous_heckeDefect_gamma L).continuousOn.integrableOn_compact isCompact_Icc

/-- Continuity of `γ ↦ ‖primePolynomial f N (-γ / 2π)‖` for any profile `f` and cutoff `N`. -/
theorem continuous_norm_primePolynomial (f : ℝ → ℂ) (N : ℕ) :
    Continuous (fun γ : ℝ => ‖primePolynomial f N (-γ / (2 * Real.pi))‖) :=
  ((continuous_expSum _ _ _).comp (continuous_neg.div_const _)).norm

/-- Continuity of `γ ↦ collidedForm Z (twist γ (heckeAvgBump L))` (`L > 0`) for any `ZeroConfig`
with summable Lorentzian weight at `0`. -/
theorem continuous_collidedForm_twist_heckeAvgBump {Z : ZeroConfig}
    (hsum0 : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)))
    {L : ℝ} (hL : 0 < L) :
    Continuous (fun γ : ℝ => collidedForm Z (twist γ (heckeAvgBump L))) := by
  refine continuous_iff_continuousAt.mpr fun γ₀ => ?_
  set R : ℝ := |γ₀| + 1
  set M_c : ℝ := (2 + 2 * R ^ 2) * (Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2)
  have hcont_on : ContinuousOn (fun γ : ℝ => collidedForm Z (twist γ (heckeAvgBump L)))
      (Metric.closedBall (0 : ℝ) R) := by
    refine continuousOn_tsum
      (f := fun (ρ : Z.carrier) (γ : ℝ) =>
        (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ))
      (u := fun ρ : Z.carrier => M_c * ((Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))))
      (fun ρ => (continuous_const.mul
        (Complex.continuous_normSq.comp
          (continuous_tr_twist (contDiff_heckeAvgBump L).continuous
            (hasCompactSupport_heckeAvgBump hL) ρ))).continuousOn)
      (hsum0.mul_left M_c) (fun ρ γ hγ => ?_)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hγ
    have hstrip := Z.strip ρ ρ.2
    have hsupp_a : ∀ u, heckeAvgBump L u ≠ 0 → |u| ≤ L + 1 / 4 := fun u hu => by
      by_contra h
      exact hu (heckeAvgBump_eq_zero_of_abs_ge hL (not_le.mp h).le)
    have hnorm := norm_tr_twist_le (contDiff_heckeAvgBump L) (by positivity) hsupp_a γ hstrip
    have hnsq : Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) ≤
        Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2 *
          (1 / (1 + ((ρ : ℂ).im - γ) ^ 2)) := by
      rw [Complex.normSq_eq_norm_sq]
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hden : 1 + ((ρ : ℂ).im - γ) ^ 2 ≤ ((1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2 := by
        have : ((ρ : ℂ).im - γ) ^ 2 = |(ρ : ℂ).im - γ| ^ 2 := (sq_abs _).symm
        rw [this]; nlinarith [abs_nonneg ((ρ : ℂ).im - γ)]
      have hexp : (Real.exp ((L + 1 / 4) / 2) * envelope (heckeAvgBump L) /
          (1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2 =
          Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2 *
            (1 / ((1 + |(ρ : ℂ).im - γ|) ^ 2) ^ 2) := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show ((2 : ℕ) : ℝ) * ((L + 1 / 4) / 2) = L + 1 / 4 by push_cast; ring]
        ring
      rw [hexp] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity) hden) (by positivity))
    have hshift : 1 / (1 + ((ρ : ℂ).im - γ) ^ 2) ≤
        (2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hγ_sq : γ ^ 2 ≤ R ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hγ 2
        rwa [sq_abs] at this
      nlinarith [sq_nonneg (((ρ : ℂ).im - γ) - γ), sq_nonneg ((ρ : ℂ).im - γ)]
    have hnn : 0 ≤ (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) :=
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    calc (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)
        ≤ (Z.mult ρ : ℝ) * (Real.exp (L + 1 / 4) * envelope (heckeAvgBump L) ^ 2 *
            ((2 + 2 * R ^ 2) * (1 / (1 + (ρ : ℂ).im ^ 2)))) :=
          mul_le_mul_of_nonneg_left
            (hnsq.trans (mul_le_mul_of_nonneg_left hshift (by positivity))) hm0
      _ = M_c * ((Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2))) := by dsimp [M_c]; ring
  exact hcont_on.continuousAt (Metric.closedBall_mem_nhds_of_mem
    (by simp [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, R]))

/-- Reflection domination `offLineDefect Z f ≤ 2 * collidedForm Z f` and sharp spectral bound
`|(Z.W f f).re| ≤ collidedForm Z f` for any `ZeroConfig` `Z`. -/
theorem offLineDefect_le_two_mul_collidedForm {Z : ZeroConfig} {f : ℝ → ℂ}
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) :
    offLineDefect Z f ≤ 2 * collidedForm Z f := by
  let g : Z.carrier → ℝ := fun ρ => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)
  have heq : (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ))) =
      fun ρ => g (reflEquiv Z ρ) := by
    ext ρ; simp only [g, mult_reflEquiv]; rfl
  have hbs : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ)) := by
    rw [heq]; exact (reflEquiv Z).summable_iff.mpr hs
  have hbt : (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ))) =
      collidedForm Z f := by
    rw [heq, (reflEquiv Z).tsum_eq g]; rfl
  have hptw : ∀ ρ : Z.carrier,
      (Z.mult ρ : ℝ) / 2 * Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) ≤
        (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ) +
          (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ)) := by
    intro ρ
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have hnsq : Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) ≤
        2 * (Complex.normSq (tr f ρ) + Complex.normSq (tr f (rosatiRefl ρ))) := by
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      have htri := norm_sub_le (tr f ρ) (tr f (rosatiRefl ρ))
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖tr f ρ‖ - ‖tr f (rosatiRefl ρ)‖)]
    nlinarith
  have hcs : Summable fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / 2 * Complex.normSq (tr f ρ - tr f (rosatiRefl ρ)) :=
    Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      hptw (hs.add hbs)
  calc offLineDefect Z f
      ≤ ∑' ρ : Z.carrier, ((Z.mult ρ : ℝ) * Complex.normSq (tr f ρ) +
          (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ))) :=
        hcs.tsum_le_tsum hptw (hs.add hbs)
    _ = collidedForm Z f +
          ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (tr f (rosatiRefl ρ)) :=
        hs.tsum_add hbs
    _ = 2 * collidedForm Z f := by rw [hbt]; ring

theorem abs_re_W_le_collidedForm {Z : ZeroConfig} {f : ℝ → ℂ}
    (hs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * Complex.normSq (tr f ρ)) :
    |(Z.W f f).re| ≤ collidedForm Z f := by
  have hcap := re_W_eq_collided_sub_defect (Z := Z) hs
  have hdef_nn : 0 ≤ offLineDefect Z f :=
    tsum_nonneg fun _ => mul_nonneg (by positivity) (Complex.normSq_nonneg _)
  have hdef_le := offLineDefect_le_two_mul_collidedForm hs
  rw [hcap, abs_le]
  constructor <;> linarith

/-- **Pointwise explicit-formula bound on `‖primePolynomial (heckeAvgBump L) ...‖`.** -/
theorem norm_primePolynomial_heckeAvgBump_le {L : ℝ} (hL : 0 < L) (γ : ℝ) :
    ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖ ≤
      |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re| +
        collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)) := by
  set ξ : ℝ := -γ / (2 * Real.pi)
  have hEF := re_archPart_sub_re_zetaZeroConfig_W_eq_re_primePolynomial
    (contDiff_heckeAvgBump L) (tsupport_heckeAvgBump_subset hL) ξ
  have htw : twist γ (heckeAvgBump L) = heightShift ξ (heckeAvgBump L) := twist_eq_heightShift γ _
  have hs := zeta_summable_collided (contDiff_twist (contDiff_heckeAvgBump L) γ)
    (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hL) γ)
  have hW := abs_re_W_le_collidedForm hs
  rw [← htw] at hEF
  rw [primePolynomial_eq_ofReal_re, Complex.norm_real, Real.norm_eq_abs, ← hEF]
  exact (abs_sub _ _).trans (add_le_add le_rfl hW)

/-! ## §2. Plancherel unit-window bound on `tr (twist γ (heckeAvgBump L)) s` -/

/-- Pointwise hyperbolic bound `sinh²(δ u) ≤ 4 depthKernel L δ` across the entire support
`|u| ≤ L + 1/4` whenever `L ≥ 1` and `|δ| ≤ 1/2`. -/
theorem sinh_sq_mul_le_four_depthKernel {L δ u : ℝ} (hL : 1 ≤ L) (hδ : |δ| ≤ 1 / 2)
    (hu : |u| ≤ L + 1 / 4) :
    Real.sinh (δ * u) ^ 2 ≤ 4 * depthKernel L δ := by
  rw [depthKernel_eq_four_sinh_sq, show (4 : ℝ) * (4 * Real.sinh (δ * L) ^ 2) =
    (4 * Real.sinh (|δ| * L)) ^ 2 by
      have : Real.sinh (δ * L) ^ 2 = Real.sinh (|δ| * L) ^ 2 := by
        rw [← sq_abs (Real.sinh (δ * L)), Real.abs_sinh, abs_mul, abs_of_pos (by linarith : 0 < L)]
      rw [this]; ring]
  rw [← sq_abs (Real.sinh (δ * u)), Real.abs_sinh, abs_mul]
  set x : ℝ := |δ| * L
  have hx0 : 0 ≤ x := mul_nonneg (abs_nonneg _) (by linarith)
  have hsinh_nn : 0 ≤ 4 * Real.sinh x := by
    have : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
    positivity
  refine pow_le_pow_left₀ (Real.sinh_nonneg_iff.mpr (mul_nonneg (abs_nonneg _) (abs_nonneg _))) ?_ 2
  rcases le_or_gt x (1 / 2) with hx | hx
  · have hu2L : |δ| * |u| ≤ 2 * x := by
      have hL2 : L + 1 / 4 ≤ 2 * L := by linarith
      calc |δ| * |u| ≤ |δ| * (2 * L) := mul_le_mul_of_nonneg_left (hu.trans hL2) (abs_nonneg _)
        _ = 2 * x := by dsimp [x]; ring
    have hs1 : Real.sinh (|δ| * |u|) ≤ Real.sinh (2 * x) := Real.sinh_le_sinh.mpr hu2L
    rw [Real.sinh_two_mul] at hs1
    have hcosh2 : Real.cosh x ≤ 2 := by
      rw [Real.cosh_eq]
      have hexp1 : Real.exp x ≤ 3 :=
        (Real.exp_le_exp.mpr (hx.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))).trans
          (by linarith [Real.exp_one_lt_d9])
      have hexp2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have hsx0 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx0
    calc Real.sinh (|δ| * |u|) ≤ 2 * Real.sinh x * Real.cosh x := hs1
      _ ≤ 2 * Real.sinh x * 2 := mul_le_mul_of_nonneg_left hcosh2 (by positivity)
      _ = 4 * Real.sinh x := by ring
  · have hux : |δ| * |u| ≤ x + 1 / 8 := by
      calc |δ| * |u| ≤ |δ| * (L + 1 / 4) := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        _ = x + |δ| * (1 / 4) := by dsimp [x]; ring
        _ ≤ x + (1 / 2) * (1 / 4) := by linarith
        _ = x + 1 / 8 := by norm_num
    have hs1 : Real.sinh (|δ| * |u|) ≤ Real.sinh (x + 1 / 8) := Real.sinh_le_sinh.mpr hux
    have hexp_18 : Real.exp (1 / 8 : ℝ) ≤ 2 := by
      have hlog2 : (1 / 8 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      exact (Real.exp_le_exp.mpr hlog2).trans_eq (Real.exp_log zero_lt_two)
    have hs2 : Real.sinh (x + 1 / 8) ≤ Real.exp x := by
      rw [Real.sinh_eq, Real.exp_add]
      have hpos : 0 < Real.exp (-(x + 1 / 8)) := Real.exp_pos _
      have hexp_pos : 0 < Real.exp x := Real.exp_pos x
      nlinarith
    have hexp_le_sinh : Real.exp x ≤ 4 * Real.sinh x := by
      rw [Real.sinh_eq]
      have h2x : Real.log 2 ≤ 2 * x := by linarith [Real.log_two_lt_d9]
      have hexp2x : 2 ≤ Real.exp (2 * x) :=
        (Real.exp_log zero_lt_two).symm.le.trans (Real.exp_le_exp.mpr h2x)
      have hprod : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by
        rw [← Real.exp_add]; congr 1; ring
      have hneg_le : Real.exp (-x) ≤ Real.exp x / 2 := by
        rw [le_div_iff₀ zero_lt_two]
        nlinarith [Real.exp_pos (-x)]
      linarith
    exact (hs1.trans hs2).trans hexp_le_sinh

/-- **Plancherel unit-window bound on `tr (twist γ (heckeAvgBump L)) s`.** For any `L ≥ 1`, `T ∈ ℝ`,
and `s ∈ ℂ` with `|s.re - 1/2| ≤ 1/2`,
`∫ γ in Icc T (T + 1), Complex.normSq (tr (twist γ (heckeAvgBump L)) s) ≤ π / L + (8π / L) depthKernel L (s.re - 1/2)`. -/
theorem unitWindow_integral_normSq_tr_twist_heckeAvgBump_le {L : ℝ} (hL : 1 ≤ L) (T : ℝ)
    {s : ℂ} (hs : |s.re - 1 / 2| ≤ 1 / 2) :
    (∫ γ in Icc T (T + 1), Complex.normSq (tr (twist γ (heckeAvgBump L)) s)) ≤
      Real.pi / L + (8 * Real.pi / L) * depthKernel L (s.re - 1 / 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  set δ : ℝ := s.re - 1 / 2
  set h : ℝ → ℂ := fun u => heckeAvgBump L u * Complex.exp ((δ : ℂ) * (u : ℂ))
  have hcont_h : Continuous h :=
    (contDiff_heckeAvgBump L).continuous.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hhc : HasCompactSupport h := (hasCompactSupport_heckeAvgBump hLpos).mul_right
  have hint_h : Integrable h := hcont_h.integrable_of_hasCompactSupport hhc
  have hmemLp2 : MemLp h 2 := hcont_h.memLp_of_hasCompactSupport hhc
  have hplanch := KernelStrip.integral_norm_sq_paperFT_of_memLp hint_h hmemLp2
  have hint_pft : Integrable (fun x : ℝ => ‖paperFT h x‖ ^ 2) := by
    by_contra hnot
    have h0 : ∫ x : ℝ, ‖paperFT h x‖ ^ 2 = 0 := integral_undef hnot
    rw [h0] at hplanch
    -- Verify `∫ u, ‖h u‖ ^ 2 > 0` or directly get integrability from `Plancherel`:
    -- Even simpler: `EF.integrable_paperFT_ofReal` gives `Integrable` directly!
    have hcd2_h : ContDiff ℝ 2 h :=
      (contDiff_heckeAvgBump L).mul
        (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
    have hkdh : ContDiff ℝ 2 (EF.weilTest h h) := EF.weilTest_contDiff hcd2_h hcont_h hhc
    have hkch : HasCompactSupport (EF.weilTest h h) := EF.weilTest_hasCompactSupport hhc hhc
    have hpft_wt := (EF.integrable_paperFT_ofReal
      (EF.integrable_fourier_of_contDiff_two hkdh hkch)).re
    exact hnot (hpft_wt.congr (Eventually.of_forall fun σ => by
      simp only [paperFT_weilTest_self_ofReal hcont_h hhc σ,
        RCLike.re_to_complex, Complex.ofReal_re]))
  have hint_shift : Integrable (fun γ : ℝ => ‖paperFT h ((s.im - γ : ℝ) : ℂ)‖ ^ 2) :=
    hint_pft.comp_sub_left s.im
  have hstep1 : (∫ γ in Icc T (T + 1), Complex.normSq (tr (twist γ (heckeAvgBump L)) s)) ≤
      2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := by
    have heq : (fun γ : ℝ => Complex.normSq (tr (twist γ (heckeAvgBump L)) s)) =
        fun γ : ℝ => ‖paperFT h ((s.im - γ : ℝ) : ℂ)‖ ^ 2 := by
      ext γ
      rw [Complex.normSq_eq_norm_sq, tr_twist_eq_paperFT]
    rw [heq]
    calc (∫ γ in Icc T (T + 1), ‖paperFT h ((s.im - γ : ℝ) : ℂ)‖ ^ 2)
        ≤ ∫ γ : ℝ, ‖paperFT h ((s.im - γ : ℝ) : ℂ)‖ ^ 2 :=
          setIntegral_le_integral hint_shift (Eventually.of_forall fun _ => sq_nonneg _)
      _ = ∫ x : ℝ, ‖paperFT h (x : ℂ)‖ ^ 2 :=
          integral_sub_left_eq_self (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2) volume s.im
      _ = 2 * Real.pi * ∫ u : ℝ, ‖h u‖ ^ 2 := hplanch
  -- Symmetrize `‖h u‖² = (heckeAvgReal L u)² e^{2 δ u}` via `u ↦ -u`
  have hnorm_h : ∀ u : ℝ, ‖h u‖ ^ 2 = heckeAvgReal L u ^ 2 * Real.exp (2 * δ * u) := by
    intro u
    dsimp [h]
    rw [norm_mul, mul_pow, Complex.norm_exp]
    have hre : ((δ : ℂ) * (u : ℂ)).re = δ * u := by simp
    have hF : ‖heckeAvgBump L u‖ = heckeAvgReal L u := by
      rw [heckeAvgBump, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heckeAvgReal_nonneg hLpos u)]
    rw [hre, hF, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hhc_prod : HasCompactSupport (fun u : ℝ => heckeAvgReal L u * heckeAvgReal L u) :=
    (hasCompactSupport_heckeAvgReal hLpos).mul_right
  have hhc_sq : HasCompactSupport (fun u : ℝ => heckeAvgReal L u ^ 2) := by
    convert hhc_prod using 1
    ext u
    exact sq (heckeAvgReal L u)
  have hint_pos : Integrable (fun u : ℝ => heckeAvgReal L u ^ 2 * Real.exp (2 * δ * u)) :=
    (((contDiff_heckeAvgReal L).continuous.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hhc_sq.mul_right
  have hint_neg : Integrable (fun u : ℝ => heckeAvgReal L u ^ 2 * Real.exp (-(2 * δ * u))) :=
    (((contDiff_heckeAvgReal L).continuous.pow 2).mul
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_const.mul continuous_id)))).integrable_of_hasCompactSupport
      hhc_sq.mul_right
  have hsym : (∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.exp (-(2 * δ * u))) =
      ∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.exp (2 * δ * u) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [heckeAvgReal_even, mul_neg, neg_neg]
  have hcosh_eq : (∫ u : ℝ, ‖h u‖ ^ 2) =
      ∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.cosh (2 * δ * u) := by
    simp_rw [hnorm_h]
    have hfun : (fun u : ℝ => heckeAvgReal L u ^ 2 * Real.cosh (2 * δ * u)) =
        fun u => (1 / 2 : ℝ) * (heckeAvgReal L u ^ 2 * Real.exp (2 * δ * u) +
          heckeAvgReal L u ^ 2 * Real.exp (-(2 * δ * u))) := by
      ext u; rw [Real.cosh_eq]; ring
    rw [hfun, integral_const_mul, integral_add hint_pos hint_neg, hsym]
    ring
  have hint_sq : Integrable (fun u : ℝ => heckeAvgReal L u ^ 2) :=
    ((contDiff_heckeAvgReal L).continuous.pow 2).integrable_of_hasCompactSupport hhc_sq
  have hint_sinh : Integrable (fun u : ℝ => 2 * (heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2)) :=
    (continuous_const.mul (((contDiff_heckeAvgReal L).continuous.pow 2).mul
      ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2))).integrable_of_hasCompactSupport
      (hhc_sq.mul_right).mul_left
  have hsplit_cosh : (∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.cosh (2 * δ * u)) =
      (∫ u : ℝ, heckeAvgReal L u ^ 2) +
        2 * ∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2 := by
    have hfun : (fun u : ℝ => heckeAvgReal L u ^ 2 * Real.cosh (2 * δ * u)) =
        fun u => heckeAvgReal L u ^ 2 + 2 * (heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2) := by
      ext u
      rw [show 2 * δ * u = 2 * (δ * u) by ring, Real.cosh_two_mul]
      nlinarith [Real.cosh_sq (δ * u)]
    rw [hfun, integral_add hint_sq hint_sinh, integral_const_mul]
  have hsq_eq : (∫ u : ℝ, heckeAvgReal L u ^ 2) = ∫ u : ℝ, ‖heckeAvgBump L u‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [heckeAvgBump]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hsinh_int : (∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2) ≤
      (4 * depthKernel L δ) * ∫ u : ℝ, heckeAvgReal L u ^ 2 := by
    rw [← integral_const_mul]
    have hint_lhs : Integrable (fun u : ℝ => heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2) :=
      (((contDiff_heckeAvgReal L).continuous.pow 2).mul
        ((Real.continuous_sinh.comp (continuous_const.mul continuous_id)).pow 2)).integrable_of_hasCompactSupport
        hhc_sq.mul_right
    refine integral_mono hint_lhs (hint_sq.const_mul _) fun u => ?_
    dsimp only
    by_cases hu : L + 1 / 4 ≤ |u|
    · rw [heckeAvgReal_eq_zero_of_abs_ge hLpos hu, zero_pow two_ne_zero, zero_mul, mul_zero]
    · rw [mul_comm (4 * depthKernel L δ)]
      exact mul_le_mul_of_nonneg_left
        (sinh_sq_mul_le_four_depthKernel hL hs (not_le.mp hu).le) (sq_nonneg _)
  have hL2 := integral_norm_sq_heckeAvgBump_le hLpos
  rw [← hsq_eq] at hL2
  have hdk_nn := depthKernel_nonneg L δ
  have hcomb : (∫ u : ℝ, ‖h u‖ ^ 2) ≤ 1 / (2 * L) + (4 / L) * depthKernel L δ := by
    rw [hcosh_eq, hsplit_cosh]
    have h2 : 2 * (∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2) ≤
        (4 / L) * depthKernel L δ := by
      calc 2 * (∫ u : ℝ, heckeAvgReal L u ^ 2 * Real.sinh (δ * u) ^ 2)
          ≤ 2 * ((4 * depthKernel L δ) * ∫ u : ℝ, heckeAvgReal L u ^ 2) := by linarith
        _ ≤ 2 * ((4 * depthKernel L δ) * (1 / (2 * L))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL2 (by positivity)) zero_le_two
        _ = (4 / L) * depthKernel L δ := by field_simp
    linarith
  calc (∫ γ in Icc T (T + 1), Complex.normSq (tr (twist γ (heckeAvgBump L)) s))
      ≤ 2 * Real.pi * (1 / (2 * L) + (4 / L) * depthKernel L δ) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hcomb Real.two_pi_pos.le)
    _ = Real.pi / L + (8 * Real.pi / L) * depthKernel L (s.re - 1 / 2) := by
        dsimp [δ]; field_simp; ring

/-! ## §3. Configuration-general unit-window self-absorption and specialization to `ζ` -/

/-- Five-unit-step bound `Z.N (T - 2) (T + 3) ≤ 10 * A₀ * log T` for `T ≥ 6` from `RiemannVonMangoldt Z`. -/
private theorem window_five_le_of_rvm {Z : ZeroConfig} (hrvm : RiemannVonMangoldt Z) :
    ∃ C_loc : ℝ, 0 < C_loc ∧ ∀ T : ℝ, 6 ≤ T →
      (Z.N (T - 2) (T + 3) : ℝ) ≤ C_loc * Real.log T := by
  obtain ⟨A₀, hA₀, hloc⟩ := hrvm.local_count
  refine ⟨10 * A₀, by positivity, fun T hT6 => ?_⟩
  have hadd : ∀ a b c : ℝ, a ≤ b → b ≤ c → Z.N a c = Z.N a b + Z.N b c := by
    intro a b c hab hbc
    have hdisj : Disjoint (Z.window a b) (Z.window b c) := by
      rw [Set.disjoint_left]
      rintro ρ ⟨_, _, h1⟩ ⟨_, h2, _⟩
      linarith
    have hunion : Z.window a c = Z.window a b ∪ Z.window b c := by
      ext ρ
      simp only [ZeroConfig.window, mem_inter_iff, mem_union, mem_setOf_eq]
      constructor
      · rintro ⟨hρ, ha, hc⟩
        rcases le_or_gt ρ.im b with hb | hb
        · exact Or.inl ⟨hρ, ha, hb⟩
        · exact Or.inr ⟨hρ, hb, hc⟩
      · rintro (⟨hρ, ha, hb⟩ | ⟨hρ, hb, hc⟩)
        · exact ⟨hρ, ha, hb.trans hbc⟩
        · exact ⟨hρ, lt_of_le_of_lt hab hb, hc⟩
    unfold ZeroConfig.N
    rw [hunion, finsum_mem_union hdisj (Z.finite_window a b) (Z.finite_window b c)]
  have hsplit : Z.N (T - 2) (T + 3) =
      Z.N (T - 2) (T - 1) + Z.N (T - 1) T + Z.N T (T + 1) +
        Z.N (T + 1) (T + 2) + Z.N (T + 2) (T + 3) := by
    rw [hadd (T - 2) (T + 2) (T + 3) (by linarith) (by linarith),
      hadd (T - 2) (T + 1) (T + 2) (by linarith) (by linarith),
      hadd (T - 2) T (T + 1) (by linarith) (by linarith),
      hadd (T - 2) (T - 1) T (by linarith) (by linarith)]
  have hstep_le : ∀ s : ℝ, -2 ≤ s → s ≤ 2 →
      (Z.N (T + s) (T + s + 1) : ℝ) ≤ 2 * A₀ * Real.log T := by
    intro s hs1 hs2
    have h1 := hloc (T + s)
    have habs : |T + s| + 3 ≤ T ^ 2 := by
      rw [abs_of_pos (by linarith)]
      nlinarith
    have hlog : Real.log (|T + s| + 3) ≤ 2 * Real.log T := by
      calc Real.log (|T + s| + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) habs
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
    nlinarith
  have h1 := hstep_le (-2) (by norm_num) (by norm_num)
  have h2 := hstep_le (-1) (by norm_num) (by norm_num)
  have h3 := hstep_le 0 (by norm_num) (by norm_num)
  have h4 := hstep_le 1 (by norm_num) (by norm_num)
  have h5 := hstep_le 2 (by norm_num) (by norm_num)
  rw [hsplit]
  push_cast
  rw [show T + (-2 : ℝ) = T - 2 by ring, show T - 2 + 1 = T - 1 by ring] at h1
  rw [show T + (-1 : ℝ) = T - 1 by ring, show T - 1 + 1 = T by ring] at h2
  rw [show T + (0 : ℝ) = T by ring] at h3
  rw [show T + (1 : ℝ) + 1 = T + 2 by ring] at h4
  rw [show T + (2 : ℝ) + 1 = T + 3 by ring] at h5
  linarith

/-- Positivity of `(Real.cos (3 / 4))²`. -/
theorem cos_three_quarters_sq_pos : 0 < Real.cos (3 / 4 : ℝ) ^ 2 := by
  have : 0 < Real.cos (3 / 4 : ℝ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  positivity

/-- Opaque finite carrier subset capturing `Z.window (T - 2) (T + 3)`. -/
private theorem exists_near_window_finset (Z : ZeroConfig) (T : ℝ) :
    ∃ S_near : Finset Z.carrier,
      (∀ ρ ∈ S_near, T - 2 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + 3) ∧
      (∀ ρ : Z.carrier, ρ ∉ S_near → ¬ (T - 2 < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T + 3)) ∧
      (∑ ρ ∈ S_near, (Z.mult ρ : ℝ)) = (Z.N (T - 2) (T + 3) : ℝ) := by
  classical
  let Wfin : Finset ℂ := (Z.finite_window (T - 2) (T + 3)).toFinset
  let emb : {z // z ∈ Wfin} → Z.carrier := fun z =>
    ⟨z.1, ((Set.Finite.mem_toFinset _).mp z.2).1⟩
  have hinj : Function.Injective emb := fun a b h =>
    Subtype.ext (congrArg (fun x : Z.carrier => (x : ℂ)) h)
  refine ⟨Wfin.attach.image emb, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨⟨z, hzW⟩, _, rfl⟩ := Finset.mem_image.mp hρ
    exact ((Set.Finite.mem_toFinset _).mp hzW).2
  · intro ρ hnot hw
    have hm : (ρ : ℂ) ∈ Wfin := (Set.Finite.mem_toFinset _).mpr ⟨ρ.2, hw⟩
    exact hnot (Finset.mem_image.mpr ⟨⟨(ρ : ℂ), hm⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩)
  · rw [Finset.sum_image (fun a _ b _ h => hinj h),
      Finset.sum_attach Wfin (fun z => (Z.mult z : ℝ)), ← Nat.cast_sum]
    congr 1
    exact (finsum_mem_eq_finite_toFinset_sum _ (Z.finite_window (T - 2) (T + 3))).symm

/-- **Configuration-general unit-window self-absorption of `collidedForm Z (twist γ (heckeAvgBump L))`.**
For any `ZeroConfig` `Z` satisfying `RiemannVonMangoldt Z` and logarithmic Lorentzian growth, and
every `c > 0`, there exist `C₁ > 0` and universal `C₂ = 8π / cos²(3/4) + 1` (independent of `Z` and
`c`) such that eventually in `T`,
`∫_{T}^{T+1} D_Z(twist γ F_{c log T}) dγ ≤ C₁ + (C₂ / (c log T)) ∫_{T}^{T+1} E_{Z,γ}(c log T) dγ`. -/
theorem exists_unitWindow_integral_collidedForm_heckeAvgBump_le_of_zeroConfig {Z : ZeroConfig}
    (hrvm : RiemannVonMangoldt Z)
    {C_lor : ℝ} (hClor : 0 < C_lor)
    (hlor : ∀ γ : ℝ,
      Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ∧
      (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ≤
        C_lor * (1 + Real.log (|γ| + 4)))
    {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ T : ℝ in atTop,
      (∫ γ in Icc T (T + 1), collidedForm Z (twist γ (heckeAvgBump (c * Real.log T)))) ≤
        C₁ + ((8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 + 1) / (c * Real.log T)) *
          ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) (c * Real.log T) := by
  classical
  obtain ⟨C_loc, hCloc, hN5⟩ := window_five_le_of_rvm hrvm
  have hsum0 : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using (hlor 0).1
  set C₁ : ℝ := Real.pi * C_loc / c + 5 * Real.exp (1 / 4) * C_lor / c + 1
  refine ⟨C₁, by positivity, ?_⟩
  have hlog_ev : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
  filter_upwards [hlog_ev, eventually_ge_atTop (6 : ℝ)] with T hL1 hT6
  set L : ℝ := c * Real.log T
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  obtain ⟨S_near, hS_in, hS_out, hcount_eq⟩ := exists_near_window_finset Z T
  let S_compl : Set Z.carrier := (↑S_near : Set Z.carrier)ᶜ
  -- Pointwise split of `collidedForm Z` into `S_near` and far `tsum`
  have hptw_coll : ∀ γ ∈ Icc T (T + 1),
      collidedForm Z (twist γ (heckeAvgBump L)) ≤
        (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)) +
          ((5 * Real.exp (1 / 4) * C_lor / c) +
            (1 / L) * configHeckeDefect Z (twist γ baseBump) L) := by
    intro γ hγ
    have hs_coll : Summable fun ρ : Z.carrier =>
        (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ) :=
      summable_collided_of_lorentz hsum0 (contDiff_twist (contDiff_heckeAvgBump L) γ)
        (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
    -- Every `ρ ∉ S_near` has `|(ρ : ℂ).im - γ| ≥ 2`
    have hsep_far : ∀ x : S_compl, 2 ≤ |(x.1 : ℂ).im - γ| := by
      intro x
      have hnot_win := hS_out x.1 (Finset.mem_coe.not.mp x.2)
      rw [not_and_or, not_lt, not_le] at hnot_win
      rcases hnot_win with hlow | hhigh
      · exact (by linarith [hγ.1] : 2 ≤ -((x.1 : ℂ).im - γ)).trans (neg_le_abs _)
      · exact (by linarith [hγ.2] : 2 ≤ (x.1 : ℂ).im - γ).trans (le_abs_self _)
    have hs_lor := (hlor γ).1
    have hs_def := summable_configHeckeDefect_of_lorentz hsum0
      (contDiff_twist (contDiff_baseBump (n := 2)) γ)
      (hasCompactSupport_twist hasCompactSupport_baseBump γ) L
    have hs_lor_c : Summable fun x : S_compl =>
        ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
          ((Z.mult x.1 : ℝ) * (1 / (1 + (γ - (x.1 : ℂ).im) ^ 2))) :=
      (hs_lor.subtype S_compl).mul_left _
    have hs_def_c : Summable fun x : S_compl =>
        (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) *
          ((Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) x.1) *
            depthKernel L ((x.1 : ℂ).re - 1 / 2)) :=
      (hs_def.subtype S_compl).mul_left _
    have hfar_le : (∑' x : S_compl,
        (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) x.1)) ≤
        ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
          (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) +
        (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) * configHeckeDefect Z (twist γ baseBump) L := by
      have hterm : ∀ x : S_compl,
          (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) x.1) ≤
            ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
              ((Z.mult x.1 : ℝ) * (1 / (1 + (γ - (x.1 : ℂ).im) ^ 2))) +
            (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) *
              ((Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) x.1) *
                depthKernel L ((x.1 : ℂ).re - 1 / 2)) := by
        intro x
        have hm0 : (0 : ℝ) ≤ Z.mult x.1 := Nat.cast_nonneg _
        have hsep := normSq_tr_twist_heckeAvgBump_le_of_sep_strip hLpos zero_lt_two γ
          (abs_re_sub_half_le_of_zeroConfig Z x.1) (hsep_far x)
        calc (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) x.1)
            ≤ (Z.mult x.1 : ℝ) * (((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2 *
                (1 / (1 + (γ - (x.1 : ℂ).im) ^ 2))) +
              1 / (4 * (2 : ℝ) ^ 2 * L ^ 2) *
                (Complex.normSq (tr (twist γ baseBump) x.1) * depthKernel L ((x.1 : ℂ).re - 1 / 2))) :=
              mul_le_mul_of_nonneg_left hsep hm0
          _ = _ := by ring
      calc (∑' x : S_compl,
            (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) x.1))
          ≤ ∑' x : S_compl,
              (((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
                ((Z.mult x.1 : ℝ) * (1 / (1 + (γ - (x.1 : ℂ).im) ^ 2))) +
              (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) *
                ((Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) x.1) *
                  depthKernel L ((x.1 : ℂ).re - 1 / 2))) :=
            (hs_coll.subtype S_compl).tsum_le_tsum hterm (hs_lor_c.add hs_def_c)
        _ = ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
              (∑' x : S_compl,
                (Z.mult x.1 : ℝ) * (1 / (1 + (γ - (x.1 : ℂ).im) ^ 2))) +
            (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) *
              (∑' x : S_compl,
                (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ baseBump) x.1) *
                  depthKernel L ((x.1 : ℂ).re - 1 / 2)) := by
            rw [hs_lor_c.tsum_add hs_def_c, tsum_mul_left, tsum_mul_left]
        _ ≤ ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
              (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) +
            (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) * configHeckeDefect Z (twist γ baseBump) L := by
            refine add_le_add
              (mul_le_mul_of_nonneg_left
                (Summable.tsum_subtype_le _ S_compl (fun _ => by positivity) hs_lor)
                (by positivity))
              (mul_le_mul_of_nonneg_left
                (Summable.tsum_subtype_le _ S_compl
                  (fun _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
                    (depthKernel_nonneg _ _))
                  hs_def)
                (by positivity))
    -- Simplify far-tail constants on `γ ∈ [T, T + 1)` with `T ≥ 6` and `L ≥ 1`
    have h1log : 1 + Real.log (|γ| + 4) ≤ 4 * Real.log T := by
      have habs : |γ| + 4 ≤ T ^ 2 := by
        rw [abs_of_pos (by linarith [hγ.1])]; nlinarith [hγ.2]
      have hlog : Real.log (|γ| + 4) ≤ 2 * Real.log T := by
        calc Real.log (|γ| + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) habs
          _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; rfl
      have hlogT1 : 1 ≤ 2 * Real.log T := by
        have : Real.log 2 ≤ Real.log T := Real.log_le_log zero_lt_two (by linarith)
        linarith [Real.log_two_gt_d9]
      linarith
    have hL_sq : L ≤ L ^ 2 := by nlinarith
    have hterm_lor : ((1 + (2 : ℝ)⁻¹ ^ 2) * Real.exp (1 / 4) / L ^ 2) *
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ≤
        5 * Real.exp (1 / 4) * C_lor / c := by
      have h54 : (1 + (2 : ℝ)⁻¹ ^ 2) = 5 / 4 := by norm_num
      rw [h54]
      calc (5 / 4 * Real.exp (1 / 4) / L ^ 2) *
            (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2)))
          ≤ (5 / 4 * Real.exp (1 / 4) / L) * (C_lor * (4 * Real.log T)) := by
            refine mul_le_mul
              (div_le_div_of_nonneg_left (by positivity) hLpos hL_sq)
              ((hlor γ).2.trans (mul_le_mul_of_nonneg_left h1log hClor.le))
              (tsum_nonneg fun _ => by positivity) (by positivity)
        _ = 5 * Real.exp (1 / 4) * C_lor * (Real.log T / (c * Real.log T)) := by
            dsimp [L]; ring
        _ = 5 * Real.exp (1 / 4) * C_lor / c := by
            have hlogT_ne : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
            field_simp
    have hdef_nn : 0 ≤ configHeckeDefect Z (twist γ baseBump) L :=
      tsum_nonneg fun _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
        (depthKernel_nonneg _ _)
    have hterm_def : (1 / (4 * (2 : ℝ) ^ 2 * L ^ 2)) * configHeckeDefect Z (twist γ baseBump) L ≤
        (1 / L) * configHeckeDefect Z (twist γ baseBump) L := by
      refine mul_le_mul_of_nonneg_right ?_ hdef_nn
      exact div_le_div_of_nonneg_left zero_le_one hLpos (by nlinarith)
    have hfar_tot : (∑' x : S_compl,
        (Z.mult x.1 : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) x.1)) ≤
        (5 * Real.exp (1 / 4) * C_lor / c) +
          (1 / L) * configHeckeDefect Z (twist γ baseBump) L := by
      linarith [hfar_le, hterm_lor, hterm_def]
    rw [collidedForm, ← Summable.sum_add_tsum_compl (s := S_near) hs_coll]
    exact add_le_add le_rfl hfar_tot
  -- Continuity and integrability on `Icc T (T + 1)`
  have hcont_coll : Continuous (fun γ : ℝ => collidedForm Z (twist γ (heckeAvgBump L))) :=
    continuous_collidedForm_twist_heckeAvgBump hsum0 hLpos
  have hcont_def : Continuous (fun γ : ℝ => configHeckeDefect Z (twist γ baseBump) L) :=
    continuous_slice_left (continuous_configHeckeDefect_pair hsum0) L
  have hint_lhs : IntegrableOn (fun γ : ℝ => collidedForm Z (twist γ (heckeAvgBump L)))
      (Icc T (T + 1)) volume :=
    hcont_coll.continuousOn.integrableOn_compact isCompact_Icc
  have hint_near_term : ∀ ρ ∈ S_near, IntegrableOn
      (fun γ : ℝ => (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ))
      (Icc T (T + 1)) volume := fun ρ _ =>
    (continuous_const.mul (Complex.continuous_normSq.comp
      (continuous_tr_twist (contDiff_heckeAvgBump L).continuous
        (hasCompactSupport_heckeAvgBump hLpos) ρ))).continuousOn.integrableOn_compact isCompact_Icc
  have hint_near : IntegrableOn
      (fun γ : ℝ => ∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ))
      (Icc T (T + 1)) volume :=
    integrable_finsetSum S_near hint_near_term
  have hint_def : IntegrableOn (fun γ : ℝ => configHeckeDefect Z (twist γ baseBump) L)
      (Icc T (T + 1)) volume :=
    hcont_def.continuousOn.integrableOn_compact isCompact_Icc
  have hint_far_c : IntegrableOn (fun _ : ℝ => 5 * Real.exp (1 / 4) * C_lor / c)
      (Icc T (T + 1)) volume :=
    integrableOn_const (by simp)
  have hint_far_rhs : IntegrableOn
      (fun γ : ℝ => (5 * Real.exp (1 / 4) * C_lor / c) +
        (1 / L) * configHeckeDefect Z (twist γ baseBump) L)
      (Icc T (T + 1)) volume :=
    hint_far_c.add (hint_def.const_mul _)
  have hint_int_le : (∫ γ in Icc T (T + 1), collidedForm Z (twist γ (heckeAvgBump L))) ≤
      (∫ γ in Icc T (T + 1),
        ∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)) +
      (∫ γ in Icc T (T + 1),
        ((5 * Real.exp (1 / 4) * C_lor / c) +
          (1 / L) * configHeckeDefect Z (twist γ baseBump) L)) := by
    rw [← integral_add hint_near hint_far_rhs]
    exact setIntegral_mono_on hint_lhs (hint_near.add hint_far_rhs) measurableSet_Icc hptw_coll
  have hvol1 : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hfar_int_eq : (∫ γ in Icc T (T + 1),
      ((5 * Real.exp (1 / 4) * C_lor / c) +
        (1 / L) * configHeckeDefect Z (twist γ baseBump) L)) =
      (5 * Real.exp (1 / 4) * C_lor / c) +
        (1 / L) * ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by
    rw [integral_add hint_far_c (hint_def.const_mul _),
      setIntegral_const, hvol1, one_smul, integral_const_mul]
  -- Evaluate and bound the `S_near` integral via Plancherel
  have hnear_int_le : (∫ γ in Icc T (T + 1),
      ∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)) ≤
      Real.pi * C_loc / c +
        (8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 / L) *
          ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by
    rw [integral_finsetSum S_near hint_near_term]
    have hpl_sum : (∑ ρ ∈ S_near, ∫ γ in Icc T (T + 1),
        (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ (heckeAvgBump L)) ρ)) ≤
        ∑ ρ ∈ S_near, (Z.mult ρ : ℝ) *
          (Real.pi / L + (8 * Real.pi / L) * depthKernel L ((ρ : ℂ).re - 1 / 2)) := by
      refine Finset.sum_le_sum fun ρ _ => ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (unitWindow_integral_normSq_tr_twist_heckeAvgBump_le hL1 T
          (abs_re_sub_half_le_of_zeroConfig Z ρ))
        (Nat.cast_nonneg _)
    have hsplit_pl : (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) *
        (Real.pi / L + (8 * Real.pi / L) * depthKernel L ((ρ : ℂ).re - 1 / 2))) =
        (Real.pi / L) * (∑ ρ ∈ S_near, (Z.mult ρ : ℝ)) +
          (8 * Real.pi / L) *
            ∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_mul, mul_comm]
      · refine Eq.trans ?_ (Finset.mul_sum _ _ _).symm
        refine Finset.sum_congr rfl fun ρ _ => by ring
    -- Bound `∑ ρ ∈ S_near, Z.mult ρ ≤ C_loc * log T`
    have hbase_part : (Real.pi / L) * (∑ ρ ∈ S_near, (Z.mult ρ : ℝ)) ≤ Real.pi * C_loc / c := by
      rw [hcount_eq]
      calc (Real.pi / L) * (Z.N (T - 2) (T + 3) : ℝ)
          ≤ (Real.pi / (c * Real.log T)) * (C_loc * Real.log T) :=
            mul_le_mul_of_nonneg_left (hN5 T hT6) (by positivity)
        _ = Real.pi * C_loc / c := by
            have hlog_ne : Real.log T ≠ 0 := (Real.log_pos (by linarith)).ne'
            field_simp
    -- Bound `∑ ρ ∈ S_near, mult * depthKernel` by `cos(3/4)⁻² ∫_{T}^{T+1} configHeckeDefect`
    have hcos_pos := cos_three_quarters_sq_pos
    have hptw_coerc : ∀ γ ∈ Icc T (T + 1),
        Real.cos (3 / 4 : ℝ) ^ 2 *
          (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)) ≤
          configHeckeDefect Z (twist γ baseBump) L := by
      intro γ hγ
      have hs_def := summable_configHeckeDefect_of_lorentz hsum0
        (contDiff_twist (contDiff_baseBump (n := 2)) γ)
        (hasCompactSupport_twist hasCompactSupport_baseBump γ) L
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun ρ hρ => ?_).trans
        (hs_def.sum_le_tsum S_near fun _ _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
            (depthKernel_nonneg _ _))
      obtain ⟨hz1, hz2⟩ := hS_in ρ hρ
      have him3 : |(ρ : ℂ).im - γ| ≤ 3 := by
        rw [abs_le]; constructor <;> linarith [hγ.1, hγ.2]
      have hcos := cos_quarter_mul_sq_le_normSq_tr_twist_baseBump (A := 3) (by norm_num)
        (by linarith [Real.pi_gt_three]) him3
      have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
      have hdk0 := depthKernel_nonneg L ((ρ : ℂ).re - 1 / 2)
      calc Real.cos (3 / 4 : ℝ) ^ 2 * ((Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2))
          = (Z.mult ρ : ℝ) * Real.cos (3 / 4 : ℝ) ^ 2 * depthKernel L ((ρ : ℂ).re - 1 / 2) := by ring
        _ ≤ (Z.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
              depthKernel L ((ρ : ℂ).re - 1 / 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcos hm0) hdk0
    have hint_coerc_c : IntegrableOn
        (fun _ : ℝ => Real.cos (3 / 4 : ℝ) ^ 2 *
          (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)))
        (Icc T (T + 1)) volume :=
      integrableOn_const (by simp)
    have hint_coerc := setIntegral_mono_on hint_coerc_c hint_def
      measurableSet_Icc hptw_coerc
    rw [setIntegral_const, hvol1, one_smul] at hint_coerc
    have hdk_sum_le : (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)) ≤
        (1 / Real.cos (3 / 4 : ℝ) ^ 2) *
          ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by
      rw [one_div_mul_eq_div, le_div_iff₀ hcos_pos, mul_comm]
      exact hint_coerc
    have hoff_part : (8 * Real.pi / L) *
        (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2)) ≤
        (8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 / L) *
          ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by
      calc (8 * Real.pi / L) *
            (∑ ρ ∈ S_near, (Z.mult ρ : ℝ) * depthKernel L ((ρ : ℂ).re - 1 / 2))
          ≤ (8 * Real.pi / L) * ((1 / Real.cos (3 / 4 : ℝ) ^ 2) *
              ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L) :=
            mul_le_mul_of_nonneg_left hdk_sum_le (by positivity)
        _ = (8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 / L) *
              ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by ring
    linarith [hpl_sum, hsplit_pl, hbase_part, hoff_part]
  -- Combine near and far bounds
  have hcomb : (8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 / L) *
        (∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L) +
      (1 / L) * (∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L) =
      ((8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 + 1) / (c * Real.log T)) *
        ∫ γ in Icc T (T + 1), configHeckeDefect Z (twist γ baseBump) L := by
    dsimp [L]; ring
  dsimp [C₁]
  linarith [hint_int_le, hfar_int_eq, hnear_int_le, hcomb]

/-- Lorentzian summability and `O(1 + log(|γ| + 4))` bound for `zetaZeroConfig`. -/
theorem exists_zetaZeroConfig_lorentz_le :
    ∃ C_lor : ℝ, 0 < C_lor ∧ ∀ γ : ℝ,
      Summable (fun ρ : zetaZeroConfig.carrier =>
        (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ∧
      (∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ≤
        C_lor * (1 + Real.log (|γ| + 4)) := by
  refine ⟨8 * (|RHTower.xiLineTwoLogDerivConstant| + 1), by positivity, fun γ => ?_⟩
  have hl_sum := RHTower.summable_lorentzMassTerm γ
  have hsum := ArithmeticCastelnuovoSeveri.summable_zetaCarrier_of_xiZeroCopy
    (g := fun z : ℂ => 1 / (1 + (γ - z.im) ^ 2)) (fun _ => by positivity) hl_sum
  have heq := (ArithmeticCastelnuovoSeveri.tsum_xiZeroCopy_eq_zetaCarrier
    (g := fun z : ℂ => 1 / (1 + (γ - z.im) ^ 2)) hl_sum).symm
  refine ⟨hsum, ?_⟩
  rw [heq]
  have hlorentz := RHTower.lorentzMass_le_log γ
  unfold RHTower.lorentzMass RHTower.lorentzMassTerm at hlorentz
  have hlog0 : 0 ≤ Real.log (|γ| + 4) := Real.log_nonneg (by linarith [abs_nonneg γ])
  have hc_le : RHTower.xiLineTwoLogDerivConstant ≤ |RHTower.xiLineTwoLogDerivConstant| :=
    le_abs_self _
  nlinarith [abs_nonneg RHTower.xiLineTwoLogDerivConstant]

/-- **Theorem 1a (`exists_unitWindow_integral_norm_primePolynomial_le` — Unconditional Unit-Window
Self-Absorption of `Π_{F_{c log T}}` for `ζ`).**
For every `c > 0`, there exist `C₁ > 0` (depending on `c`) and the universal constant
`C₂ = 8π / cos²(3/4) + 1 > 0` (independent of `c`) such that eventually in `T` (`atTop`),
`∫ γ in Icc T (T + 1), ‖Π_{F_{c log T}}(N*(c log T), -γ / 2π)‖ ≤ C₁ + (C₂ / (c log T)) ∫ γ in Icc T (T + 1), E_γ(c log T)`. -/
theorem exists_unitWindow_integral_norm_primePolynomial_le {c : ℝ} (hc : 0 < c) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ T : ℝ in atTop,
      (∫ γ in Icc T (T + 1),
        ‖primePolynomial (heckeAvgBump (c * Real.log T))
          ⌊Real.exp (2 * (c * Real.log T + 1 / 4))⌋₊ (-γ / (2 * Real.pi))‖) ≤
        C₁ + ((8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 + 1) / (c * Real.log T)) *
          ∫ γ in Icc T (T + 1), heckeDefect (baseTwistTest γ) (c * Real.log T) := by
  obtain ⟨C_arch, hCarch, harch_bd⟩ := exists_abs_re_archPart_heckeAvgBump_log_le hc
  obtain ⟨C_lor, hClor, hlor⟩ := exists_zetaZeroConfig_lorentz_le
  obtain ⟨C_coll, hCcoll, hev_coll⟩ :=
    exists_unitWindow_integral_collidedForm_heckeAvgBump_le_of_zeroConfig
      riemannVonMangoldt_zeta hClor hlor hc
  refine ⟨C_arch + C_coll, by positivity, ?_⟩
  have hlog_ev : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
  filter_upwards [hev_coll, hlog_ev, eventually_ge_atTop (2 : ℝ)] with T hcoll hL1 hT2
  set L : ℝ := c * Real.log T
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  -- Continuity of `primePolynomial` and `collidedForm` on `Icc T (T + 1)`
  have hcont_pp := continuous_norm_primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
  have hsum0 : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using (hlor 0).1
  have hcont_coll := continuous_collidedForm_twist_heckeAvgBump hsum0 hLpos
  have hint_pp : IntegrableOn
      (fun γ : ℝ => ‖primePolynomial (heckeAvgBump L) ⌊Real.exp (2 * (L + 1 / 4))⌋₊
        (-γ / (2 * Real.pi))‖) (Icc T (T + 1)) volume :=
    hcont_pp.continuousOn.integrableOn_compact isCompact_Icc
  have hint_coll : IntegrableOn
      (fun γ : ℝ => collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)))
      (Icc T (T + 1)) volume :=
    hcont_coll.continuousOn.integrableOn_compact isCompact_Icc
  have hint_arch_const : IntegrableOn (fun _ : ℝ => C_arch) (Icc T (T + 1)) volume :=
    integrableOn_const (by simp)
  have hint_rhs : IntegrableOn
      (fun γ : ℝ => C_arch + collidedForm zetaZeroConfig (twist γ (heckeAvgBump L)))
      (Icc T (T + 1)) volume :=
    hint_arch_const.add hint_coll
  have hvol1 : volume.real (Icc T (T + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hmono := setIntegral_mono_on hint_pp hint_rhs measurableSet_Icc fun γ hγ =>
    (norm_primePolynomial_heckeAvgBump_le hLpos γ).trans
      (add_le_add (harch_bd T γ hT2 hL1 hγ.1 hγ.2) le_rfl)
  rw [integral_add hint_arch_const hint_coll, setIntegral_const, hvol1,
    one_smul] at hmono
  have heq_def : (fun γ : ℝ => configHeckeDefect zetaZeroConfig (twist γ baseBump) L) =
      fun γ : ℝ => heckeDefect (baseTwistTest γ) L :=
    funext fun γ => configHeckeDefect_zeta_twist_eq γ L
  rw [heq_def] at hcoll
  linarith [hmono, hcoll]

/-! ## §4. Universal explicit-formula / `RiemannVonMangoldt` no-go -/

/-- Lorentzian summability and `O(1 + log(|γ| + 4))` bound for `LocalCountFalsifier.clusterConfig`. -/
private theorem exists_clusterConfig_lorentz_le :
    ∃ C_cl : ℝ, 0 < C_cl ∧ ∀ γ : ℝ,
      Summable (fun ρ : LocalCountFalsifier.clusterConfig.carrier =>
        (LocalCountFalsifier.clusterConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ∧
      (∑' ρ : LocalCountFalsifier.clusterConfig.carrier,
        (LocalCountFalsifier.clusterConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ≤
        C_cl * (1 + Real.log (|γ| + 4)) := by
  classical
  -- Map `ℕ × Bool` onto `clusterConfig.carrier` and bound by `8 log(|γ| + 4) + ∑_{k ≥ 0} 8 / 2^k`
  refine ⟨32, by norm_num, fun γ => ?_⟩
  set M_γ : ℝ := 2 * Real.log (|γ| + 4)
  have hMγ_pos : 1 < M_γ := by
    have : Real.log 2 < Real.log (|γ| + 4) :=
      Real.log_lt_log zero_lt_two (by linarith [abs_nonneg γ])
    linarith [Real.log_two_gt_d9]
  set K_γ : ℕ := ⌊Real.log M_γ⌋₊ + 1
  -- Every point of `clusterConfig.carrier` has the form `clusterPoint s k` (`s ∈ {1, -1}`, `k : ℕ`)
  let phi : ℕ × Bool → LocalCountFalsifier.clusterConfig.carrier := fun p =>
    ⟨LocalCountFalsifier.clusterPoint (if p.2 then 1 else -1) p.1,
      by cases p.2 <;> [exact Or.inr ⟨p.1, rfl⟩; exact Or.inl ⟨p.1, rfl⟩]⟩
  have hsurj : Function.Surjective phi := by
    rintro ⟨z, ⟨k, rfl⟩ | ⟨k, rfl⟩⟩
    · exact ⟨(k, true), Subtype.ext rfl⟩
    · exact ⟨(k, false), Subtype.ext rfl⟩
  -- Bound on `(phi p)` summands
  have hphi_bound : ∀ p : ℕ × Bool,
      (LocalCountFalsifier.clusterConfig.mult (phi p) : ℝ) *
        (1 / (1 + (γ - ((phi p : LocalCountFalsifier.clusterConfig.carrier) : ℂ).im) ^ 2)) ≤
      (if p.1 < K_γ then (⌊Real.exp p.1⌋₊ : ℝ) else 4 * (1 / 2 : ℝ) ^ p.1) := by
    intro ⟨k, b⟩
    have hmult : LocalCountFalsifier.clusterConfig.mult (phi (k, b)) = ⌊Real.exp k⌋₊ := by
      dsimp [phi]
      exact LocalCountFalsifier.clusterConfig_mult _ k
    have him : ((phi (k, b) : LocalCountFalsifier.clusterConfig.carrier) : ℂ).im =
        Real.exp (Real.exp k) := by
      dsimp [phi]
      exact LocalCountFalsifier.clusterPoint_im _ k
    rw [hmult, him]
    by_cases hk : k < K_γ
    · rw [if_pos hk]
      have hle1 : 1 / (1 + (γ - Real.exp (Real.exp k)) ^ 2) ≤ 1 :=
        div_le_one_of_le₀ (by nlinarith [sq_nonneg (γ - Real.exp (Real.exp k))]) (by positivity)
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hle1
    · rw [if_neg hk]
      have hk_ge : K_γ ≤ k := not_lt.mp hk
      have hlogM_lt : Real.log M_γ < (k : ℝ) := by
        have := Nat.lt_floor_add_one (Real.log M_γ)
        have hcast : (K_γ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
        dsimp [K_γ] at hcast
        push_cast at hcast
        linarith
      have hexpk_gt : M_γ < Real.exp k := by
        rw [← Real.exp_log (by linarith : 0 < M_γ)]
        exact Real.exp_lt_exp.mpr hlogM_lt
      have hexpexp_gt : (|γ| + 4) ^ 2 < Real.exp (Real.exp k) := by
        have hsq : Real.log ((|γ| + 4) ^ 2) = M_γ := by
          dsimp [M_γ]; rw [Real.log_pow]; push_cast; rfl
        rw [← Real.exp_log (by positivity : 0 < (|γ| + 4) ^ 2), hsq]
        exact Real.exp_lt_exp.mpr hexpk_gt
      have hdiff : Real.exp (Real.exp k) / 2 ≤ Real.exp (Real.exp k) - γ := by
        have h1 : 2 * |γ| + 16 ≤ (|γ| + 4) ^ 2 := by nlinarith [abs_nonneg γ]
        have h2 : γ ≤ |γ| := le_abs_self γ
        linarith
      -- `exp(u) ≥ u² / 2` for `u = exp k ≥ 0`: `(exp(exp k) / 2)² ≥ (exp k)⁴ / 16 ≥ exp(2k) / 4`
      have hexp_quad : Real.exp k ^ 2 / 2 ≤ Real.exp (Real.exp k) := by
        have hu0 : 0 ≤ Real.exp k := (Real.exp_pos k).le
        have h3 := Real.sum_le_exp_of_nonneg hu0 3
        simp [Finset.sum_range_succ] at h3
        linarith
      have hdiff_ge : Real.exp k ^ 2 / 4 ≤ Real.exp (Real.exp k) - γ := by linarith
      have hsq_den : (Real.exp k ^ 2 / 4) ^ 2 ≤ 1 + (γ - Real.exp (Real.exp k)) ^ 2 := by
        have h1 : (Real.exp k ^ 2 / 4) ^ 2 ≤ (Real.exp (Real.exp k) - γ) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hdiff_ge 2
        nlinarith
      have hfl_le : (⌊Real.exp k⌋₊ : ℝ) ≤ Real.exp k := Nat.floor_le (Real.exp_pos k).le
      have hexp2 : (2 : ℝ) ^ k ≤ Real.exp k := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        calc (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ zero_le_two h2e k
          _ = Real.exp k := by rw [← Real.exp_nat_mul]; simp
      have hexpk1 : 1 ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg k)
      calc (⌊Real.exp k⌋₊ : ℝ) * (1 / (1 + (γ - Real.exp (Real.exp k)) ^ 2))
          ≤ Real.exp k * (1 / (Real.exp k ^ 2 / 4) ^ 2) := by
            refine mul_le_mul hfl_le
              (one_div_le_one_div_of_le (by positivity) hsq_den)
              (by positivity) (Real.exp_pos k).le
        _ = 16 / Real.exp k ^ 3 := by field_simp; ring
        _ ≤ 4 * (1 / 2 : ℝ) ^ k := by
            -- Since `k ≥ K_γ ≥ 1`, `exp k ≥ 5 / 2`, so `4 * exp k ≤ exp k ^ 3`
            have hk1 : 1 ≤ k := by dsimp [K_γ] at hk_ge; omega
            have hexp_ge : (5 / 2 : ℝ) ≤ Real.exp k := by
              have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
              calc (5 / 2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
                _ ≤ Real.exp k := Real.exp_le_exp.mpr h1k
            have hsq4 : 4 * Real.exp k ≤ Real.exp k ^ 3 := by nlinarith
            have hdiv1 : 16 / Real.exp k ^ 3 ≤ 4 / Real.exp k := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              nlinarith
            refine hdiv1.trans ?_
            rw [one_div_pow, mul_one_div]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hexp2
  have hinj : Function.Injective phi := by
    rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
    have hval : LocalCountFalsifier.clusterPoint (if b₁ then 1 else -1) k₁ =
        LocalCountFalsifier.clusterPoint (if b₂ then 1 else -1) k₂ :=
      congrArg Subtype.val h
    have him_eq : Real.exp (Real.exp k₁) = Real.exp (Real.exp k₂) :=
      congrArg Complex.im hval
    have hk : k₁ = k₂ := Nat.cast_injective (Real.exp_injective (Real.exp_injective him_eq))
    subst hk
    have hre_eq : 1 / 2 + (if b₁ then (1 : ℝ) else -1) / ((k₁ : ℝ) + 3) =
        1 / 2 + (if b₂ then (1 : ℝ) else -1) / ((k₁ : ℝ) + 3) :=
      congrArg Complex.re hval
    have hden_pos : (0 : ℝ) < (k₁ : ℝ) + 3 := by positivity
    cases b₁ <;> cases b₂
    · rfl
    · exfalso
      have hp : (0 : ℝ) < 1 / ((k₁ : ℝ) + 3) := by positivity
      have hn : (-1 : ℝ) / ((k₁ : ℝ) + 3) < 0 := div_neg_of_neg_of_pos (by norm_num) hden_pos
      simp only [ite_true, Bool.false_eq_true, ite_false] at hre_eq; linarith
    · exfalso
      have hp : (0 : ℝ) < 1 / ((k₁ : ℝ) + 3) := by positivity
      have hn : (-1 : ℝ) / ((k₁ : ℝ) + 3) < 0 := div_neg_of_neg_of_pos (by norm_num) hden_pos
      simp only [ite_true, Bool.false_eq_true, ite_false] at hre_eq; linarith
    · rfl
  let e_cl : ℕ × Bool ≃ LocalCountFalsifier.clusterConfig.carrier :=
    Equiv.ofBijective phi ⟨hinj, hsurj⟩
  set v : ℕ → ℝ := fun k => (if k < K_γ then Real.exp k else 0) + 4 * (1 / 2 : ℝ) ^ k
  have hv_nn : ∀ k : ℕ, 0 ≤ v k := fun k => by
    dsimp [v]; split_ifs <;> positivity
  have hv_fin : Summable (fun k : ℕ => if k < K_γ then Real.exp k else 0) :=
    summable_of_ne_finset_zero (s := Finset.range K_γ) fun k hk =>
      if_neg (by simpa [Finset.mem_range] using hk)
  have hv_geo : Summable (fun k : ℕ => 4 * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left 4
  have hv_sum : Summable v := hv_fin.add hv_geo
  have hv_tsum_le : (∑' k : ℕ, v k) ≤ 2 * M_γ + 8 := by
    rw [hv_fin.tsum_add hv_geo,
      tsum_eq_sum (s := Finset.range K_γ) (fun k hk =>
        if_neg (by simpa [Finset.mem_range] using hk)),
      tsum_mul_left, tsum_geometric_two]
    have hsum_eq : (∑ k ∈ Finset.range K_γ, if k < K_γ then Real.exp k else 0) =
        ∑ k ∈ Finset.range K_γ, Real.exp k :=
      Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk)
    rw [hsum_eq]
    have hrange := LocalCountFalsifier.sum_range_exp_le K_γ
    have hexpK : Real.exp K_γ ≤ M_γ * Real.exp 1 := by
      have hlog0 : 0 ≤ Real.log M_γ := Real.log_nonneg hMγ_pos.le
      have hfl : (⌊Real.log M_γ⌋₊ : ℝ) ≤ Real.log M_γ := Nat.floor_le hlog0
      have hexpfl : Real.exp (⌊Real.log M_γ⌋₊ : ℝ) ≤ M_γ :=
        (Real.exp_le_exp.mpr hfl).trans_eq (Real.exp_log (by linarith))
      dsimp [K_γ]
      rw [Nat.cast_add, Nat.cast_one, Real.exp_add]
      exact mul_le_mul_of_nonneg_right hexpfl (Real.exp_pos 1).le
    have hdiv : 2 * Real.exp K_γ / Real.exp 1 ≤ 2 * M_γ := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith [Real.exp_pos 1]
    linarith
  have hw_sum : Summable (fun p : ℕ × Bool => v p.1) := by
    refine (summable_prod_of_nonneg fun p => hv_nn p.1).2 ⟨fun _ => Summable.of_finite, ?_⟩
    have heq : (fun k : ℕ => ∑' _b : Bool, v k) = fun k => 2 * v k := by
      ext k; rw [tsum_fintype, Fintype.sum_bool]; ring
    rw [heq]
    exact hv_sum.mul_left 2
  have hw_tsum : (∑' p : ℕ × Bool, v p.1) = 2 * ∑' k : ℕ, v k := by
    rw [hw_sum.tsum_prod]
    have heq : (fun k : ℕ => ∑' _b : Bool, v k) = fun k => 2 * v k := by
      ext k; rw [tsum_fintype, Fintype.sum_bool]; ring
    rw [heq, tsum_mul_left]
  set f_cl : LocalCountFalsifier.clusterConfig.carrier → ℝ := fun ρ =>
    (LocalCountFalsifier.clusterConfig.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))
  have hf_comp_le : ∀ p : ℕ × Bool, f_cl (e_cl p) ≤ v p.1 := by
    intro p
    refine (hphi_bound p).trans ?_
    dsimp [v]
    split_ifs with hp
    · have hfl : (⌊Real.exp p.1⌋₊ : ℝ) ≤ Real.exp p.1 := Nat.floor_le (Real.exp_pos _).le
      have hpos : (0 : ℝ) ≤ 4 * (1 / 2 : ℝ) ^ p.1 := by positivity
      linarith
    · linarith
  have hf_comp_sum : Summable (f_cl ∘ e_cl) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (Nat.cast_nonneg _) (by positivity))
      hf_comp_le hw_sum
  have hf_sum : Summable f_cl := e_cl.summable_iff.mp hf_comp_sum
  refine ⟨hf_sum, ?_⟩
  rw [← e_cl.tsum_eq f_cl]
  have htsum_le := hf_comp_sum.tsum_le_tsum hf_comp_le hw_sum
  rw [hw_tsum] at htsum_le
  have hlog_nn : 0 ≤ Real.log (|γ| + 4) := Real.log_nonneg (by linarith [abs_nonneg γ])
  dsimp [M_γ] at hv_tsum_le
  linarith

/-- Additive transfer of Lorentzian summability and `O(1 + log(|γ| + 4))` bounds across
`LocalCountFalsifier.superpose Z₁ Z₂`. -/
private theorem summable_and_tsum_superpose_le (Z₁ Z₂ : ZeroConfig) (w : ℂ → ℝ)
    (hs₁ : Summable fun ρ : Z₁.carrier => (Z₁.mult ρ : ℝ) * w ρ)
    (hs₂ : Summable fun ρ : Z₂.carrier => (Z₂.mult ρ : ℝ) * w ρ) :
    Summable (fun ρ : (LocalCountFalsifier.superpose Z₁ Z₂).carrier =>
      ((LocalCountFalsifier.superpose Z₁ Z₂).mult ρ : ℝ) * w ρ) ∧
    (∑' ρ : (LocalCountFalsifier.superpose Z₁ Z₂).carrier,
      ((LocalCountFalsifier.superpose Z₁ Z₂).mult ρ : ℝ) * w ρ) =
      (∑' ρ : Z₁.carrier, (Z₁.mult ρ : ℝ) * w ρ) +
      (∑' ρ : Z₂.carrier, (Z₂.mult ρ : ℝ) * w ρ) := by
  classical
  set S := LocalCountFalsifier.superpose Z₁ Z₂
  let emb₁ : Z₁.carrier → S.carrier := fun ρ => ⟨ρ.1, Or.inl ρ.2⟩
  let emb₂ : Z₂.carrier → S.carrier := fun ρ => ⟨ρ.1, Or.inr ρ.2⟩
  have hinj₁ : Function.Injective emb₁ := fun a b h =>
    Subtype.ext (congrArg (fun x : S.carrier => (x : ℂ)) h)
  have hinj₂ : Function.Injective emb₂ := fun a b h =>
    Subtype.ext (congrArg (fun x : S.carrier => (x : ℂ)) h)
  let g₁ : S.carrier → ℝ := fun y =>
    if (y : ℂ) ∈ Z₁.carrier then (Z₁.mult y : ℝ) * w y else 0
  let g₂ : S.carrier → ℝ := fun y =>
    if (y : ℂ) ∈ Z₂.carrier then (Z₂.mult y : ℝ) * w y else 0
  have hg₁_zero : ∀ y : S.carrier, y ∉ Set.range emb₁ → g₁ y = 0 := fun y hy => by
    dsimp [g₁]
    rw [if_neg]
    intro hm
    exact hy ⟨⟨y.1, hm⟩, Subtype.ext rfl⟩
  have hg₂_zero : ∀ y : S.carrier, y ∉ Set.range emb₂ → g₂ y = 0 := fun y hy => by
    dsimp [g₂]
    rw [if_neg]
    intro hm
    exact hy ⟨⟨y.1, hm⟩, Subtype.ext rfl⟩
  have hg₁_supp : Function.support g₁ ⊆ Set.range emb₁ := fun y hy => by
    by_contra hnr
    exact hy (hg₁_zero y hnr)
  have hg₂_supp : Function.support g₂ ⊆ Set.range emb₂ := fun y hy => by
    by_contra hnr
    exact hy (hg₂_zero y hnr)
  have hg₁_comp : g₁ ∘ emb₁ = fun ρ : Z₁.carrier => (Z₁.mult ρ : ℝ) * w ρ := by
    ext ρ; simp [g₁, emb₁, ρ.2]
  have hg₂_comp : g₂ ∘ emb₂ = fun ρ : Z₂.carrier => (Z₂.mult ρ : ℝ) * w ρ := by
    ext ρ; simp [g₂, emb₂, ρ.2]
  have hsum_g₁ : Summable g₁ := by
    rw [← hinj₁.summable_iff hg₁_zero, hg₁_comp]
    exact hs₁
  have hsum_g₂ : Summable g₂ := by
    rw [← hinj₂.summable_iff hg₂_zero, hg₂_comp]
    exact hs₂
  have hfun_eq : (fun ρ : S.carrier => (S.mult ρ : ℝ) * w ρ) = fun ρ => g₁ ρ + g₂ ρ := by
    ext ρ
    change (((if (ρ : ℂ) ∈ Z₁.carrier then Z₁.mult ρ else 0) +
      (if (ρ : ℂ) ∈ Z₂.carrier then Z₂.mult ρ else 0) : ℕ) : ℝ) * w ρ = g₁ ρ + g₂ ρ
    push_cast
    dsimp [g₁, g₂]
    split_ifs <;> ring
  rw [hfun_eq]
  refine ⟨hsum_g₁.add hsum_g₂, ?_⟩
  rw [hsum_g₁.tsum_add hsum_g₂, ← hinj₁.tsum_eq hg₁_supp, ← hinj₂.tsum_eq hg₂_supp]
  congr 1
  · exact tsum_congr fun ρ => by dsimp [g₁, emb₁]; rw [if_pos ρ.2]
  · exact tsum_congr fun ρ => by dsimp [g₂, emb₂]; rw [if_pos ρ.2]

/-- Opaque package of `superpose zetaZeroConfig clusterConfig` properties so analytic tactics never
unfold `superpose` or `zetaZeroConfig`. -/
private theorem exists_superpose_zeta_cluster_spec :
    ∃ (Z' : ZeroConfig) (C_lor : ℝ),
      0 < C_lor ∧
      RiemannVonMangoldt Z' ∧
      (∀ T₁ T₂ : ℝ, Z'.N0 T₁ T₂ = zetaZeroConfig.N0 T₁ T₂) ∧
      (∀ γ : ℝ,
        Summable (fun ρ : Z'.carrier => (Z'.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ∧
        (∑' ρ : Z'.carrier, (Z'.mult ρ : ℝ) * (1 / (1 + (γ - (ρ : ℂ).im) ^ 2))) ≤
          C_lor * (1 + Real.log (|γ| + 4))) ∧
      (∀ k : ℕ, LocalCountFalsifier.clusterPoint 1 k ∈ Z'.carrier) := by
  obtain ⟨C_z, hCz, hlor_z⟩ := exists_zetaZeroConfig_lorentz_le
  obtain ⟨C_cl, hCcl, hlor_cl⟩ := exists_clusterConfig_lorentz_le
  refine ⟨LocalCountFalsifier.superpose zetaZeroConfig LocalCountFalsifier.clusterConfig,
    C_z + C_cl, add_pos hCz hCcl,
    LocalCountFalsifier.riemannVonMangoldt_superpose riemannVonMangoldt_zeta,
    fun T₁ T₂ => ?_, fun γ => ?_, fun k => Or.inr (Or.inl ⟨k, rfl⟩)⟩
  · rw [LocalCountFalsifier.N0_superpose, LocalCountFalsifier.clusterConfig_N0, add_zero]
  · obtain ⟨hs, heq⟩ := summable_and_tsum_superpose_le zetaZeroConfig
      LocalCountFalsifier.clusterConfig (fun z : ℂ => 1 / (1 + (γ - z.im) ^ 2))
      (hlor_z γ).1 (hlor_cl γ).1
    refine ⟨hs, ?_⟩
    rw [heq]
    have hz := (hlor_z γ).2
    have hcl := (hlor_cl γ).2
    linarith

/-- **Theorem 1b (`exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation` — Universal
Explicit-Formula / `RiemannVonMangoldt` No-Go).**
There exists a `ZeroConfig` `Z'` (`superpose zetaZeroConfig clusterConfig`) such that:
1. `RiemannVonMangoldt Z'` holds;
2. `Z'` has the exact same critical-line zero counts as `ζ` on every window (`Z'.N0 = zetaZeroConfig.N0`);
3. `collidedForm Z' f` converges absolutely for every `C_c²` profile `f`;
4. Yet for EVERY `c > 0`, `α ≥ 0`, and `C ∈ ℝ`, it is FALSE that eventually in `T` (`atTop`),
   for all `γ ∈ [T, T + 1)`, the Hecke defect `configHeckeDefect Z' (twist γ baseBump) (c * log T)`
   is bounded by `α * |(archPart F_L (-γ / 2π)).re - (Z'.W (twist γ F_L) (twist γ F_L)).re| + C`
   (the exact spectral-deviation expression equal to `α ‖Π_{F_L}(-γ / 2π)‖ + C` on `ζ`). -/
theorem exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation :
    ∃ Z' : ZeroConfig,
      RiemannVonMangoldt Z' ∧
      (∀ T₁ T₂ : ℝ, Z'.N0 T₁ T₂ = zetaZeroConfig.N0 T₁ T₂) ∧
      (∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        Summable (fun ρ : Z'.carrier => (Z'.mult ρ : ℝ) * Complex.normSq (tr f ρ))) ∧
      ∀ (c : ℝ), 0 < c → ∀ (α : ℝ), 0 ≤ α → ∀ (C : ℝ),
        ¬ (∀ᶠ T : ℝ in atTop, ∀ γ ∈ Icc T (T + 1),
          configHeckeDefect Z' (twist γ baseBump) (c * Real.log T) ≤
            α * |(archPart (heckeAvgBump (c * Real.log T)) (-γ / (2 * Real.pi))).re -
              (Z'.W (twist γ (heckeAvgBump (c * Real.log T)))
                (twist γ (heckeAvgBump (c * Real.log T)))).re| + C) := by
  classical
  obtain ⟨Z', C_lor, hClor, hrvm, hN0, hlor_Z', hcl_mem⟩ := exists_superpose_zeta_cluster_spec
  have hsum0 : Summable fun ρ : Z'.carrier => (Z'.mult ρ : ℝ) * (1 / (1 + (ρ : ℂ).im ^ 2)) := by
    simpa only [zero_sub, neg_sq] using (hlor_Z' 0).1
  refine ⟨Z', hrvm, hN0, fun f hf hfc => summable_collided_of_lorentz hsum0 hf hfc,
    fun c hc α hα C hhyp => ?_⟩
  obtain ⟨C_arch, hCarch, harch_bd⟩ := exists_abs_re_archPart_heckeAvgBump_log_le hc
  obtain ⟨C₁, hC₁, hev_sa⟩ :=
    exists_unitWindow_integral_collidedForm_heckeAvgBump_le_of_zeroConfig hrvm hClor hlor_Z' hc
  set C₂ : ℝ := 8 * Real.pi / Real.cos (3 / 4 : ℝ) ^ 2 + 1
  have hC₂_pos : 0 < C₂ := by
    have := cos_three_quarters_sq_pos
    dsimp [C₂]; positivity
  have hlog_ev1 : ∀ᶠ T : ℝ in atTop, 1 ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop 1
  have hlog_ev2 : ∀ᶠ T : ℝ in atTop, 2 * α * C₂ ≤ c * Real.log T :=
    (Real.tendsto_log_atTop.const_mul_atTop hc).eventually_ge_atTop (2 * α * C₂)
  obtain ⟨T_0, hT_0⟩ := eventually_atTop.mp
    (hhyp.and (hev_sa.and (hlog_ev1.and (hlog_ev2.and (eventually_ge_atTop (6 : ℝ))))))
  -- Uniform cap on `∫ γ in Icc T (T + 1), configHeckeDefect Z' ...` for all `T ≥ T_0`
  set M_cap : ℝ := 2 * (α * C_arch + |C| + α * C₁ + 1)
  have hcap_le : ∀ T : ℝ, T_0 ≤ T →
      (∫ γ in Icc T (T + 1), configHeckeDefect Z' (twist γ baseBump) (c * Real.log T)) ≤ M_cap := by
    intro T hT
    obtain ⟨hhypT, hsaT, hL1, hsmall, hT6⟩ := hT_0 T hT
    set L : ℝ := c * Real.log T
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    -- Pointwise bound `configHeckeDefect ≤ (α C_arch + |C|) + α * collidedForm`
    have hptw : ∀ γ ∈ Icc T (T + 1),
        configHeckeDefect Z' (twist γ baseBump) L ≤
          (α * C_arch + |C|) + α * collidedForm Z' (twist γ (heckeAvgBump L)) := by
      intro γ hγ
      have hs_coll := summable_collided_of_lorentz hsum0
        (contDiff_twist (contDiff_heckeAvgBump L) γ)
        (hasCompactSupport_twist (hasCompactSupport_heckeAvgBump hLpos) γ)
      have hW := abs_re_W_le_collidedForm hs_coll
      have harch := harch_bd T γ (by linarith) hL1 hγ.1 hγ.2
      have hdev : |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re -
          (Z'.W (twist γ (heckeAvgBump L)) (twist γ (heckeAvgBump L))).re| ≤
          C_arch + collidedForm Z' (twist γ (heckeAvgBump L)) :=
        (abs_sub _ _).trans (add_le_add harch hW)
      calc configHeckeDefect Z' (twist γ baseBump) L
          ≤ α * |(archPart (heckeAvgBump L) (-γ / (2 * Real.pi))).re -
              (Z'.W (twist γ (heckeAvgBump L)) (twist γ (heckeAvgBump L))).re| + C := hhypT γ hγ
        _ ≤ α * (C_arch + collidedForm Z' (twist γ (heckeAvgBump L))) + |C| :=
            add_le_add (mul_le_mul_of_nonneg_left hdev hα) (le_abs_self C)
        _ = (α * C_arch + |C|) + α * collidedForm Z' (twist γ (heckeAvgBump L)) := by ring
    -- Continuity and integrability on `Icc T (T + 1)`
    have hcont_def : Continuous (fun γ : ℝ => configHeckeDefect Z' (twist γ baseBump) L) :=
      continuous_slice_left (continuous_configHeckeDefect_pair hsum0) L
    have hcont_coll := continuous_collidedForm_twist_heckeAvgBump hsum0 hLpos
    have hint_def : IntegrableOn (fun γ : ℝ => configHeckeDefect Z' (twist γ baseBump) L)
        (Icc T (T + 1)) volume :=
      hcont_def.continuousOn.integrableOn_compact isCompact_Icc
    have hint_coll : IntegrableOn
        (fun γ : ℝ => collidedForm Z' (twist γ (heckeAvgBump L)))
        (Icc T (T + 1)) volume :=
      hcont_coll.continuousOn.integrableOn_compact isCompact_Icc
    have hint_c : IntegrableOn (fun _ : ℝ => α * C_arch + |C|) (Icc T (T + 1)) volume :=
      integrableOn_const (by simp)
    have hint_rhs : IntegrableOn
        (fun γ : ℝ => (α * C_arch + |C|) + α * collidedForm Z' (twist γ (heckeAvgBump L)))
        (Icc T (T + 1)) volume :=
      hint_c.add (hint_coll.const_mul α)
    have hvol1 : volume.real (Icc T (T + 1)) = 1 := by
      rw [Real.volume_real_Icc_of_le (by linarith)]; ring
    have hint_mono := setIntegral_mono_on hint_def hint_rhs measurableSet_Icc hptw
    rw [integral_add hint_c (hint_coll.const_mul α),
      setIntegral_const, hvol1, one_smul, integral_const_mul] at hint_mono
    set I_E := ∫ γ in Icc T (T + 1), configHeckeDefect Z' (twist γ baseBump) L
    have hIE_nn : 0 ≤ I_E := setIntegral_nonneg measurableSet_Icc fun γ _ =>
      tsum_nonneg fun _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
        (depthKernel_nonneg _ _)
    have hα_sa : α * (∫ γ in Icc T (T + 1), collidedForm Z' (twist γ (heckeAvgBump L))) ≤
        α * C₁ + (α * (C₂ / L)) * I_E := by
      have := mul_le_mul_of_nonneg_left hsaT hα
      dsimp [C₂, L, I_E] at this ⊢
      linarith
    have hcoeff_half : α * (C₂ / L) ≤ 1 / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ hLpos zero_lt_two]
      dsimp [L]; linarith
    have hhalf_IE : (α * (C₂ / L)) * I_E ≤ (1 / 2) * I_E :=
      mul_le_mul_of_nonneg_right hcoeff_half hIE_nn
    dsimp [M_cap]
    linarith
  -- Evaluate at `T_k = exp(exp k)` for `k` large enough that both `T_k ≥ T_0` and the single
  -- cluster zero `clusterPoint 1 k` exceeds `M_cap`.
  set k : ℕ := max (⌈|T_0|⌉₊ + 3) (⌈4 * Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) / c⌉₊ + 3)
  set T_k : ℝ := Real.exp (Real.exp k)
  have hk3 : 3 ≤ k := le_trans (by omega) (le_max_left _ _)
  have hTk_ge : T_0 ≤ T_k := by
    have h1 : T_0 ≤ |T_0| := le_abs_self T_0
    have h2 : |T_0| ≤ (⌈|T_0|⌉₊ : ℝ) := Nat.le_ceil |T_0|
    have h3 : (⌈|T_0|⌉₊ + 3 : ℕ) ≤ k := le_max_left _ _
    have h4 : (⌈|T_0|⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : ⌈|T_0|⌉₊ ≤ k)
    have h5 := LocalCountFalsifier.le_exp_exp k
    dsimp [T_k]; linarith
  have hcap_k := hcap_le T_k hTk_ge
  -- Lower bound `configHeckeDefect` on `Icc T_k (T_k + 1)` via `clusterPoint 1 k`
  let z_k : ℂ := LocalCountFalsifier.clusterPoint 1 k
  have hz_mem : z_k ∈ Z'.carrier := hcl_mem k
  let ρ_k : Z'.carrier := ⟨z_k, hz_mem⟩
  set L_k : ℝ := c * Real.log T_k
  have hLk_eq : L_k = c * Real.exp k := by
    dsimp [L_k, T_k]; rw [Real.log_exp]
  have hptw_low : ∀ γ ∈ Icc T_k (T_k + 1),
      Real.cos (1 / 4 : ℝ) ^ 2 * depthKernel L_k (1 / ((k : ℝ) + 3)) ≤
        configHeckeDefect Z' (twist γ baseBump) L_k := by
    intro γ hγ
    have hs_def := summable_configHeckeDefect_of_lorentz hsum0
      (contDiff_twist (contDiff_baseBump (n := 2)) γ)
      (hasCompactSupport_twist hasCompactSupport_baseBump γ) L_k
    have hsingle : (Z'.mult ρ_k : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ_k) *
        depthKernel L_k ((ρ_k : ℂ).re - 1 / 2) ≤
        configHeckeDefect Z' (twist γ baseBump) L_k := by
      unfold configHeckeDefect
      rw [← Finset.sum_singleton (f := fun ρ : Z'.carrier =>
        (Z'.mult ρ : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ) *
          depthKernel L_k ((ρ : ℂ).re - 1 / 2)) (a := ρ_k)]
      exact hs_def.sum_le_tsum {ρ_k} fun _ _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))
          (depthKernel_nonneg _ _)
    refine le_trans ?_ hsingle
    have hm1 : (1 : ℝ) ≤ (Z'.mult ρ_k : ℝ) := by exact_mod_cast Z'.one_le_mult z_k hz_mem
    have him1 : |(ρ_k : ℂ).im - γ| ≤ 1 := by
      have him_eq : (ρ_k : ℂ).im = T_k := LocalCountFalsifier.clusterPoint_im 1 k
      rw [him_eq, abs_le]; constructor <;> linarith [hγ.1, hγ.2]
    have hcos := cos_quarter_mul_sq_le_normSq_tr_twist_baseBump (A := 1) zero_le_one
      (by linarith [Real.pi_gt_three]) him1
    have hre_eq : (ρ_k : ℂ).re - 1 / 2 = 1 / ((k : ℝ) + 3) := by
      have hre_z : (ρ_k : ℂ).re = 1 / 2 + 1 / ((k : ℝ) + 3) :=
        LocalCountFalsifier.clusterPoint_re 1 k
      rw [hre_z]; ring
    rw [hre_eq]
    have hdk0 := depthKernel_nonneg L_k (1 / ((k : ℝ) + 3))
    calc Real.cos (1 / 4 : ℝ) ^ 2 * depthKernel L_k (1 / ((k : ℝ) + 3))
        = 1 * Real.cos (1 / 4 : ℝ) ^ 2 * depthKernel L_k (1 / ((k : ℝ) + 3)) := by ring
      _ ≤ (Z'.mult ρ_k : ℝ) * Complex.normSq (tr (twist γ baseBump) ρ_k) *
            depthKernel L_k (1 / ((k : ℝ) + 3)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hm1 hcos (sq_nonneg _) (Nat.cast_nonneg _)) hdk0
  have hcont_def_k : Continuous (fun γ : ℝ => configHeckeDefect Z' (twist γ baseBump) L_k) :=
    continuous_slice_left (continuous_configHeckeDefect_pair hsum0) L_k
  have hint_def_k : IntegrableOn (fun γ : ℝ => configHeckeDefect Z' (twist γ baseBump) L_k)
      (Icc T_k (T_k + 1)) volume :=
    hcont_def_k.continuousOn.integrableOn_compact isCompact_Icc
  have hint_low_c : IntegrableOn
      (fun _ : ℝ => Real.cos (1 / 4 : ℝ) ^ 2 * depthKernel L_k (1 / ((k : ℝ) + 3)))
      (Icc T_k (T_k + 1)) volume :=
    integrableOn_const (by simp)
  have hint_low := setIntegral_mono_on hint_low_c hint_def_k
    measurableSet_Icc hptw_low
  have hvol_k : volume.real (Icc T_k (T_k + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [setIntegral_const, hvol_k, one_smul] at hint_low
  -- `depthKernel L_k (1 / (k + 3)) ≥ 4 * L_k² / (k + 3)² > M_cap / cos²(1/4)`
  have hquad := quadratic_le_depthKernel L_k (1 / ((k : ℝ) + 3))
  have hexp_quad : (k : ℝ) ^ 2 / 2 ≤ Real.exp k := by
    have h3 := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg k) 3
    simp [Finset.sum_range_succ] at h3
    linarith
  have hk_real3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have hratio_ge : (k : ℝ) / 4 ≤ Real.exp k / ((k : ℝ) + 3) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hprod_ge : c * (k : ℝ) / 4 ≤ L_k * (1 / ((k : ℝ) + 3)) := by
    rw [hLk_eq]
    calc c * (k : ℝ) / 4 = c * ((k : ℝ) / 4) := by ring
      _ ≤ c * (Real.exp k / ((k : ℝ) + 3)) := mul_le_mul_of_nonneg_left hratio_ge hc.le
      _ = (c * Real.exp k) * (1 / ((k : ℝ) + 3)) := by ring
  have hk_large : 4 * Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) / c < (k : ℝ) := by
    have hle : ⌈4 * Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) / c⌉₊ + 3 ≤ k :=
      le_max_right _ _
    have hcast : (⌈4 * Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) / c⌉₊ : ℝ) + 3 ≤ (k : ℝ) := by
      exact_mod_cast hle
    linarith [Nat.le_ceil (4 * Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) / c)]
  have hprod_gt : Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) <
      L_k * (1 / ((k : ℝ) + 3)) := by
    have h1 : Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1) < c * (k : ℝ) / 4 := by
      rw [div_lt_iff₀ hc] at hk_large
      linarith
    linarith
  have hM_nn : 0 ≤ M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1 := by
    have hcos_pos := cos_quarter_sq_pos
    have hM_pos : 0 < M_cap := by dsimp [M_cap]; positivity
    positivity
  have hdk_gt : M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1 <
      depthKernel L_k (1 / ((k : ℝ) + 3)) := by
    have hsq_lt : (Real.sqrt (M_cap / Real.cos (1 / 4 : ℝ) ^ 2 + 1)) ^ 2 <
        (L_k * (1 / ((k : ℝ) + 3))) ^ 2 :=
      pow_lt_pow_left₀ hprod_gt (Real.sqrt_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hM_nn] at hsq_lt
    have h4 : (L_k * (1 / ((k : ℝ) + 3))) ^ 2 ≤ 4 * L_k ^ 2 * (1 / ((k : ℝ) + 3)) ^ 2 := by
      nlinarith [sq_nonneg (L_k * (1 / ((k : ℝ) + 3)))]
    linarith [hquad]
  have hcos_pos := cos_quarter_sq_pos
  have hgt_M : M_cap < Real.cos (1 / 4 : ℝ) ^ 2 * depthKernel L_k (1 / ((k : ℝ) + 3)) := by
    have := mul_lt_mul_of_pos_left hdk_gt hcos_pos
    rw [mul_add, mul_div_cancel₀ _ hcos_pos.ne', mul_one] at this
    linarith
  linarith [hint_low, hcap_k, hgt_M]

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect

end

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.abs_re_W_le_collidedForm
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.unitWindow_integral_normSq_tr_twist_heckeAvgBump_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_unitWindow_integral_norm_primePolynomial_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect.exists_rvm_zeroConfig_not_heckeDefect_le_spectralDeviation
