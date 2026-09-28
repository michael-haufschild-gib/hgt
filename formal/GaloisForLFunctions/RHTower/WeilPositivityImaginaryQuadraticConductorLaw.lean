import GaloisForLFunctions.RHTower.WeilPositivityQuadraticConductorLaw
import GaloisForLFunctions.RHTower.DirichletOddThetaAxisKernel
import GaloisForLFunctions.HTGeometry.GammaLogDeriv
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly

/-!
# Weil positivity and the conductor of every quadratic field

Let `χ` be a real primitive Dirichlet character of conductor `q > 1`.  The module completes the
quadratic conductor law with the odd characters, the characters of imaginary quadratic fields.

* **Archimedean mismatch** (`re_digamma_threeQuarter_sub_quarter`).
  `Re ψ(3/4 + ir/2) - Re ψ(1/4 + ir/2) = π / cosh(πr)`, from the digamma reflection formula at
  `s = 1/4 - ir/2` and `Re cot(π/4 - iy) = 1/cosh(2y)`.
* **Explicit formula of an odd `L(s, χ)` in symbol form**
  (`integral_weilAtomSymbol_dirichlet_odd`).  For a `C²` test supported in `[-a, a]`,
  `∫ |h_f|² S_{Λχ} = 2π Re W_χ(f) - ∫ |h_f(τ)|² (log q + π / cosh(πτ)) dτ`.
* **Joint radical tests** (section `JointRadical`).  For any kernel `Ψ` with super-exponential
  decay whose transform vanishes at the zeros of a configuration `Z`, the tests
  `g_R = f_R ⋆ Ψ_{≤4R}` have both zero sides `O(R e^{-R/2})` and `∫ |h_{g_R}|²` bounded below,
  provided `Ψ̂(-3i/4) ≠ 0`.  Hence an energy bound `2π(1-t) Re W_ζ + t(2π Re W_Z - c₀ ∫|h|²)` with
  `t, c₀ > 0` forces a violation (`weilAtomSymbol_not_nonneg_of_joint_radical`).
* **Theorems.**
  - `dirichletMix_weilAtomSymbol_not_nonneg_odd`: for odd real primitive `χ` and `t > 0`, the
    weights `Λ(n)(1 - t + tχ(n))` violate Weil positivity; the defect is
    `t ∫ |h|² (log q + π sech(πτ))`.
  - `quadraticMix_weilAtomSymbol_not_nonneg`: the same for every real primitive `χ`, even or odd.
    For `χ` the character of `ℚ(i)` (`q = 4`) and `t = 1/2`, the weights keep the primes
    `p ≡ 1 (mod 4)`, delete the odd powers of the primes `p ≡ 3 (mod 4)`, and halve the powers of `2`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

local notation "Φ" => riemannPhiKernel

/-! ### The archimedean mismatch of an odd character -/

theorem re_cot_quarter_sub (y : ℝ) :
    ((Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * (1 / 4 - I * (y / Real.pi))) /
      Complex.sin ((Real.pi : ℂ) * (1 / 4 - I * (y / Real.pi))))).re =
      Real.pi / Real.cosh (2 * y) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have harg : (Real.pi : ℂ) * (1 / 4 - I * (y / Real.pi)) = ((Real.pi / 4 : ℝ) : ℂ) - (y : ℂ) * I := by
    field_simp; push_cast; ring
  rw [harg, Complex.cos_sub, Complex.sin_sub, Complex.cos_mul_I, Complex.sin_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  set c := Real.cosh y
  set s := Real.sinh y
  have hs2 : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hq : (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (c : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((s : ℂ) * I)) /
      (((Real.sqrt 2 / 2 : ℝ) : ℂ) * (c : ℂ) - ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((s : ℂ) * I)) =
      ((c : ℂ) + (s : ℂ) * I) / ((c : ℂ) - (s : ℂ) * I) := by
    have hne : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs2.ne'
    rw [← mul_add, ← mul_sub, mul_div_mul_left _ _ hne]
  rw [hq]
  have hc : 0 < c := Real.cosh_pos y
  have h1 : c ^ 2 - s ^ 2 = 1 := by rw [Real.cosh_sq y]; ring
  have h2 : Real.cosh (2 * y) = c ^ 2 + s ^ 2 := by rw [Real.cosh_two_mul]
  rw [Complex.re_ofReal_mul, Complex.div_re]
  have hnorm : Complex.normSq ((c : ℂ) - (s : ℂ) * I) = c ^ 2 + s ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hnorm, h2]
  simp
  have hpos : 0 < c ^ 2 + s ^ 2 := by positivity
  field_simp
  nlinarith [h1]

theorem re_digamma_threeQuarter_sub_quarter (r : ℝ) :
    (Complex.digamma (1 / 4 + (1 : ℂ) / 2 + I * r / 2)).re -
      (Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2)).re =
      Real.pi / Real.cosh (Real.pi * r) := by
  set s : ℂ := 1 / 4 - I * ((Real.pi * r / 2) / Real.pi) with hs
  have hsr : s = 1 / 4 - I * r / 2 := by
    rw [hs]; field_simp
  have hns : ∀ k : ℤ, s ≠ (k : ℂ) := by
    intro k h
    have := congrArg Complex.re h
    rw [hsr] at this
    simp at this
    have h4 : (4 : ℝ) * k = 1 := by linarith
    have : (4 * k : ℤ) = 1 := by exact_mod_cast h4
    omega
  have href := HTGeometry.digamma_reflection s hns
  have h1s : 1 - s = 1 / 4 + (1 : ℂ) / 2 + I * r / 2 := by rw [hsr]; ring
  have hconj : s = conj (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2) := by
    rw [hsr]
    simp only [map_add, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_one,
      map_ofNat, Nat.cast_zero, map_zero]
    ring
  have hψ : (Complex.digamma s).re = (Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2)).re := by
    rw [hconj, ReflectedDigammaAnomaly.digamma_conj, Complex.conj_re]
  rw [h1s] at href
  have hre := congrArg Complex.re href
  rw [Complex.sub_re, hψ] at hre
  have hc := re_cot_quarter_sub (Real.pi * r / 2)
  push_cast at hc
  rw [hre, hs, hc]
  congr 2; ring


/-! ### Joint radical tests for `ζ` and a second zero configuration -/

section JointRadical

variable {Ψ : ℝ → ℂ}

/-- `g_R = f_R ⋆ Ψ_{≤4R}`: radical for `ζ`, and for every `L`-function whose zeros `Ψ̂` kills,
up to truncation. -/
def jointRadicalTest (Ψ : ℝ → ℂ) (R : ℝ) : ℝ → ℂ :=
  convolution (weilRadicalTest R) (kernelCore Ψ (4 * R))
    (ContinuousLinearMap.mul ℝ ℂ) volume

theorem contDiff_jointRadicalTest (hΨc : Continuous Ψ) (R : ℝ) :
    ContDiff ℝ 2 (jointRadicalTest Ψ R) :=
  (hasCompactSupport_weilRadicalTest R).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ)
    (n := 2) (contDiff_weilRadicalTest R)
    (integrable_kernelCore (hΨc) _).locallyIntegrable

theorem jointRadicalTest_eq_zero (Ψ : ℝ → ℂ) {R x : ℝ} (hx : 5 * R < |x|) :
    jointRadicalTest Ψ R x = 0 := by
  unfold jointRadicalTest
  rw [convolution_def]
  have : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (weilRadicalTest R t)
      (kernelCore Ψ (4 * R) (x - t)) = 0 := by
    intro t
    simp only [ContinuousLinearMap.mul_apply']
    by_cases ht : R < |t|
    · rw [weilRadicalTest_eq_zero ht, zero_mul]
    · push Not at ht
      have hxt : 4 * R < |x - t| := by have := abs_sub_abs_le_abs_sub x t; linarith
      have : x - t ∉ Icc (-(4 * R)) (4 * R) := fun hm => by
        have := abs_le.mpr ⟨hm.1, hm.2⟩; linarith
      simp [kernelCore, indicator, this]
  simp [this]

theorem tsupport_jointRadicalTest (Ψ : ℝ → ℂ) (R : ℝ) :
    tsupport (jointRadicalTest Ψ R) ⊆ Icc (-(5 * R)) (5 * R) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h : ¬ 5 * R < |x| := fun h => hx (jointRadicalTest_eq_zero Ψ h)
  push Not at h
  exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

theorem paperFT_jointRadicalTest (hΨc : Continuous Ψ) (R : ℝ) (z : ℂ) :
    paperFT (jointRadicalTest Ψ R) z =
      paperFT (weilRadicalTest R) z * paperFT (kernelCore Ψ (4 * R)) z :=
  paperFT_convolution
    (((contDiff_weilRadicalTest R).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_weilRadicalTest R).mul_right)
    (integrable_kernelCore_mul_exp (hΨc) _ z)

theorem paperFT_jointRadicalTest_half_I (hΨc : Continuous Ψ) (R : ℝ) :
    paperFT (jointRadicalTest Ψ R) (I / 2) = 0 := by
  rw [paperFT_jointRadicalTest hΨc, paperFT_weilRadicalTest_half_I, zero_mul]

theorem paperFT_jointRadicalTest_neg_half_I (hΨc : Continuous Ψ) (R : ℝ) :
    paperFT (jointRadicalTest Ψ R) (-(I / 2)) = 0 := by
  rw [paperFT_jointRadicalTest hΨc, paperFT_weilRadicalTest_neg_half_I, zero_mul]


/-- **The `ζ` zero side of the joint radical test decays** like `R e^{-R/2}`. -/
theorem exists_norm_W_zeta_jointRadicalTest_le (hΨc : Continuous Ψ) {CΨ : ℝ}
    (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|)) : ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      ‖zetaZeroConfig.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)‖ ≤
        K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set BΨ := ∫ u : ℝ, ‖Ψ u‖ * Real.exp (1 / 2 * |u|) with hBΨ
  have hBΨ0 : 0 ≤ BΨ := integral_nonneg fun _ => by positivity
  set SZ := ∑' ρ : zetaZeroConfig.carrier,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * SZ * (E₀ * C₆ * Real.exp (1 / 4) * A * BΨ * (K₀ * BΨ)), by positivity,
    fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ε := ∫ u : ℝ, ‖riemannPhiTail R u‖ * Real.exp (1 / 2 * |u|) with hε
  have hε0 : 0 ≤ ε := integral_nonneg fun _ => by positivity
  have hεle : ε ≤ E₀ * C₆ * Real.exp (-(R - 1 / 4)) :=
    riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)
  have h := norm_zeroConfig_W_le_of_pointwise zetaZeroConfig summable_zetaZeroConfig
    (f := jointRadicalTest Ψ R) (P := ε * A * BΨ) (Q := Real.exp (R / 2) * (R * K₀) * BΨ)
    (by positivity) (by positivity) ?_ ?_
  · rw [← hSZ] at h
    refine h.trans ?_
    have hexp : Real.exp (-(R - 1 / 4)) * Real.exp (R / 2) =
        Real.exp (1 / 4) * Real.exp (-(R / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc 5 / 4 * SZ * (ε * A * BΨ * (Real.exp (R / 2) * (R * K₀) * BΨ))
        ≤ 5 / 4 * SZ * ((E₀ * C₆ * Real.exp (-(R - 1 / 4))) * A * BΨ *
            (Real.exp (R / 2) * (R * K₀) * BΨ)) := by gcongr
      _ = 5 / 4 * SZ * (E₀ * C₆ * A * BΨ * (K₀ * BΨ)) * R *
            (Real.exp (-(R - 1 / 4)) * Real.exp (R / 2)) := by ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    obtain ⟨hc1, -⟩ := paperFT_riemannPhiCore_at_zero hmem R
    rw [paperFT_jointRadicalTest hΨc, norm_mul, paperFT_weilRadicalTest, hc1, norm_mul, norm_neg]
    exact mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiTail_le (by norm_num) hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hε0)
      (norm_paperFT_kernelCore_le hΨc hΨd _ hIm) (norm_nonneg _) (by positivity)
  · intro ρ
    have hmem := ρ.2
    have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
      have h : IsNontrivialZero (ρ : ℂ) := hmem
      exact ⟨h.2.1, h.2.2⟩
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    rw [paperFT_jointRadicalTest hΨc, norm_mul]
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (kernelCore Ψ (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * BΨ :=
          mul_le_mul (norm_paperFT_weilRadicalTest_conj_le hK hR0 hIm)
            (norm_paperFT_kernelCore_le hΨc hΨd _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * BΨ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-- **The zero side of a second configuration `Z` decays** like `R e^{-R/2}` on the joint radical
tests, when `Ψ̂` vanishes at every zero of `Z`. -/
theorem exists_norm_W_jointRadicalTest_le (Z : ZeroConfig)
    (hZs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
    (hZstrip : ∀ ρ : Z.carrier, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1)
    (hΨc : Continuous Ψ) {CΨ : ℝ} (hCΨ : 0 ≤ CΨ) (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|))
    (hΨz : ∀ ρ : Z.carrier, paperFT Ψ (gammaOf ρ) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      ‖Z.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)‖ ≤ K * (R * Real.exp (-(R / 2))) := by
  obtain ⟨K₀, hK₀, hK⟩ := exists_weilRadicalTest_norms_le
  obtain ⟨Ct, hCt0, hCt⟩ := exists_integral_kernelTail_le hCΨ hΨd
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set BΨ := ∫ u : ℝ, ‖Ψ u‖ * Real.exp (1 / 2 * |u|) with hBΨ
  have hBΨ0 : 0 ≤ BΨ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  set SZ := ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hSZ
  have hSZ0 : 0 ≤ SZ := tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by have := Complex.normSq_nonneg (gammaOf (ρ : ℂ)); linarith)
  refine ⟨5 / 4 * SZ * (BΦ * A * Ct * (K₀ * BΨ)), by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have htail : ∫ u : ℝ, ‖kernelTail Ψ (4 * R) u‖ * Real.exp (1 / 2 * |u|) ≤
      Ct * Real.exp (-R) := by
    have := hCt (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have h := norm_zeroConfig_W_le_of_pointwise Z hZs
    (f := jointRadicalTest Ψ R) (P := BΦ * A * (Ct * Real.exp (-R)))
    (Q := Real.exp (R / 2) * (R * K₀) * BΨ) (by positivity) (by positivity) ?_ ?_
  · rw [← hSZ] at h
    refine h.trans (le_of_eq ?_)
    have hexp : Real.exp (-R) * Real.exp (R / 2) = Real.exp (-(R / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc 5 / 4 * SZ * (BΦ * A * (Ct * Real.exp (-R)) * (Real.exp (R / 2) * (R * K₀) * BΨ))
        = 5 / 4 * SZ * (BΦ * A * Ct * (K₀ * BΨ)) * R * (Real.exp (-R) * Real.exp (R / 2)) := by
          ring
      _ = _ := by rw [hexp]; ring
  · intro ρ
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt (hZstrip ρ)).le
    rw [paperFT_jointRadicalTest hΨc, norm_mul, paperFT_weilRadicalTest, norm_mul,
      paperFT_kernelCore_eq hΨc hΨd _ hIm, hΨz ρ, zero_sub, norm_neg]
    refine mul_le_mul (mul_le_mul (norm_paperFT_riemannPhiCore_le R hIm)
      (norm_paperFT_weilBumpPolarFree_le (by linarith)) (norm_nonneg _) hBΦ0)
      ((norm_paperFT_kernelTail_le hΨc hΨd _ hIm).trans htail) (norm_nonneg _) (by positivity)
  · intro ρ
    have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt (hZstrip ρ)).le
    have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
      rw [Complex.conj_im, abs_neg]; exact hIm
    rw [paperFT_jointRadicalTest hΨc, norm_mul]
    calc ‖paperFT (weilRadicalTest R) ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (kernelCore Ψ (4 * R)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (Real.exp (R / 2) * (R * K₀) * (1 / (1 + |(ρ : ℂ).im|) ^ 2)) * BΨ :=
          mul_le_mul (norm_paperFT_weilRadicalTest_conj_le hK hR0 hIm)
            (norm_paperFT_kernelCore_le hΨc hΨd _ hIm') (norm_nonneg _) (by positivity)
      _ = Real.exp (R / 2) * (R * K₀) * BΨ * (1 / (1 + |(ρ : ℂ).im|) ^ 2) := by ring

/-! #### The limit transform and its mass on the real line -/

/-- The limit transform `Φ̂(z) κ̂₂(z) Ψ̂(z)` of the joint radical tests. -/
def jointRadicalLimit (Ψ : ℝ → ℂ) (z : ℂ) : ℂ :=
  radicalLimit z * paperFT Ψ z

theorem differentiable_jointRadicalLimit (hΨs : SuperExpDecay Ψ) :
    Differentiable ℂ (jointRadicalLimit Ψ) :=
  differentiable_radicalLimit.mul hΨs.differentiable_paperFT

theorem jointRadicalLimit_ne_zero (hΨ0 : paperFT Ψ (-(3 / 4 * I)) ≠ 0) :
    jointRadicalLimit Ψ (-(3 / 4 * I)) ≠ 0 := by
  have h := conductorLimit_ne_zero
  unfold conductorLimit at h
  unfold jointRadicalLimit radicalLimit
  exact mul_ne_zero (left_ne_zero_of_mul h) hΨ0

/-- The limit transform does not vanish identically on the real line. -/
theorem exists_real_jointRadicalLimit_ne_zero (hΨs : SuperExpDecay Ψ)
    (hΨ0 : paperFT Ψ (-(3 / 4 * I)) ≠ 0) : ∃ τ₀ : ℝ, jointRadicalLimit Ψ τ₀ ≠ 0 := by
  by_contra h
  push Not at h
  have han : AnalyticOnNhd ℂ (jointRadicalLimit Ψ) univ :=
    (differentiable_jointRadicalLimit hΨs).differentiableOn.analyticOnNhd isOpen_univ
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), jointRadicalLimit Ψ z = 0 := by
    have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
    exact htend.frequently (Eventually.frequently (Eventually.of_forall fun t => h t))
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ 0) hfreq
  exact jointRadicalLimit_ne_zero hΨ0 (hzero (mem_univ _))

/-- On the real line the joint radical tests converge uniformly to the limit transform. -/
theorem exists_norm_paperFT_jointRadicalTest_sub_le (hΨc : Continuous Ψ) {CΨ : ℝ}
    (hCΨ : 0 ≤ CΨ) (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ τ : ℝ,
      ‖paperFT (jointRadicalTest Ψ R) τ - jointRadicalLimit Ψ τ‖ ≤ K * Real.exp (-R) := by
  obtain ⟨C₆, hC₆0, hC₆⟩ := exists_superexp_le 6
  obtain ⟨Ct, hCt0, hCt⟩ := exists_integral_kernelTail_le hCΨ hΨd
  set E₀ := 40 * jacobiThetaTailConstant * Real.exp π / (6 * π - 6) with hE₀
  have hE0 : 0 ≤ E₀ := by
    have hM : 0 ≤ jacobiThetaTailConstant := jacobiThetaTailConstant_nonneg
    have hc : 0 < 6 * π - 6 := by nlinarith [Real.pi_gt_three]
    rw [hE₀]; positivity
  set A := Real.exp (3 / 4) * ∫ u : ℝ, ‖weilBumpPolarFree u‖ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => norm_nonneg _)
  set BΨ := ∫ u : ℝ, ‖Ψ u‖ * Real.exp (1 / 2 * |u|) with hBΨ
  have hBΨ0 : 0 ≤ BΨ := integral_nonneg fun _ => by positivity
  set BΦ := ∫ u : ℝ, ‖Φ u‖ * Real.exp (1 / 2 * |u|) with hBΦ
  have hBΦ0 : 0 ≤ BΦ := integral_nonneg fun _ => by positivity
  refine ⟨A * (BΦ * Ct + E₀ * C₆ * Real.exp (1 / 4) * BΨ), by positivity, fun R hR τ => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  have hτ : |((τ : ℂ)).im| ≤ 1 / 2 := by simp
  set TΨ := paperFT (kernelTail Ψ (4 * R)) τ with hTΨ
  set Tζ := paperFT (riemannPhiTail R) τ with hTζ
  have hTΨb : ‖TΨ‖ ≤ Ct * Real.exp (-R) := by
    refine (norm_paperFT_kernelTail_le hΨc hΨd _ hτ).trans ?_
    have := hCt (4 * R) (by linarith)
    rwa [show 4 * R / 4 = R by ring] at this
  have hTζb : ‖Tζ‖ ≤ E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) := by
    refine (norm_paperFT_riemannPhiTail_le (by norm_num) hτ).trans
      ((riemannPhiTail_bound_le E₀ C₆ hE₀ hC₆ hR (by norm_num)).trans (le_of_eq ?_))
    rw [mul_assoc (E₀ * C₆), ← Real.exp_add]; congr 2; ring
  have hK : ‖paperFT Ψ τ‖ ≤ BΨ :=
    norm_paperFT_le_of_norm_le_kernel hΨc hΨd hΨc.aestronglyMeasurable (fun u => le_rfl) hτ
  have hcoreζ : ‖paperFT (riemannPhiCore R) τ‖ ≤ BΦ := norm_paperFT_riemannPhiCore_le R hτ
  have hκ : ‖paperFT weilBumpPolarFree τ‖ ≤ A :=
    norm_paperFT_weilBumpPolarFree_le (by simp only [Complex.ofReal_im, abs_zero]; norm_num)
  have hΦ : paperFT Φ τ = paperFT (riemannPhiCore R) τ + Tζ := by
    rw [paperFT_riemannPhiCore_eq, paperFT_riemannPhiKernel]; ring
  have hdiff : paperFT (jointRadicalTest Ψ R) τ - jointRadicalLimit Ψ τ =
      -(paperFT weilBumpPolarFree τ * (paperFT (riemannPhiCore R) τ * TΨ +
        Tζ * paperFT Ψ τ)) := by
    unfold jointRadicalLimit radicalLimit
    rw [paperFT_jointRadicalTest hΨc, paperFT_weilRadicalTest,
      paperFT_kernelCore_eq hΨc hΨd _ hτ, hΦ]
    ring
  rw [hdiff, norm_neg, norm_mul]
  calc ‖paperFT weilBumpPolarFree τ‖ * ‖paperFT (riemannPhiCore R) τ * TΨ +
        Tζ * paperFT Ψ τ‖
      ≤ A * (BΦ * (Ct * Real.exp (-R)) + E₀ * C₆ * Real.exp (1 / 4) * Real.exp (-R) * BΨ) := by
        refine mul_le_mul hκ ((norm_add_le _ _).trans ?_) (norm_nonneg _) hA0
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul hcoreζ hTΨb (norm_nonneg _) hBΦ0)
          (mul_le_mul hTζb hK (norm_nonneg _) (by positivity))
    _ = A * (BΦ * Ct + E₀ * C₆ * Real.exp (1 / 4) * BΨ) * Real.exp (-R) := by ring

/-- **Mass of the joint radical tests.**  `∫ |h_{g_R}|² ≥ c > 0` for all large `R`. -/
theorem exists_integral_normSq_jointRadicalTest_ge (hΨs : SuperExpDecay Ψ)
    (hΨ0 : paperFT Ψ (-(3 / 4 * I)) ≠ 0) {CΨ : ℝ} (hCΨ : 0 ≤ CΨ)
    (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|)) : ∃ c R₀ : ℝ, 0 < c ∧ 1 ≤ R₀ ∧
      ∀ R : ℝ, R₀ ≤ R → c ≤ ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 := by
  have hΨc : Continuous Ψ := hΨs.1
  obtain ⟨τ₀, hτ₀⟩ := exists_real_jointRadicalLimit_ne_zero hΨs hΨ0
  obtain ⟨K, hK0, hK⟩ := exists_norm_paperFT_jointRadicalTest_sub_le hΨc hCΨ hΨd
  set m := ‖jointRadicalLimit Ψ τ₀‖ with hm
  have hm0 : 0 < m := norm_pos_iff.mpr hτ₀
  have hcont : ContinuousAt (fun τ : ℝ => jointRadicalLimit Ψ τ) τ₀ :=
    ((differentiable_jointRadicalLimit hΨs).continuous.comp Complex.continuous_ofReal).continuousAt
  obtain ⟨η, hη0, hη⟩ := Metric.continuousAt_iff.mp hcont (m / 2) (by linarith)
  have hev : ∀ᶠ R in atTop, K * Real.exp (-R) ≤ m / 4 := by
    have ht : Tendsto (fun R : ℝ => K * Real.exp (-R)) atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
    exact ht.eventually (ge_mem_nhds (by linarith))
  obtain ⟨R₁, hR₁⟩ := hev.exists_forall_of_atTop
  refine ⟨η * (m / 4) ^ 2, max R₁ 1, by positivity, le_max_right _ _, fun R hR => ?_⟩
  have hR1 : 1 ≤ R := le_trans (le_max_right _ _) hR
  have herr := hR₁ R (le_trans (le_max_left _ _) hR)
  have hlow : ∀ τ ∈ Icc (τ₀ - η / 2) (τ₀ + η / 2),
      (m / 4) ^ 2 ≤ ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 := by
    intro τ hτ
    have hd : dist τ τ₀ < η := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
    have h1 := hη hd
    rw [dist_eq_norm] at h1
    have h2 : m / 2 ≤ ‖jointRadicalLimit Ψ τ‖ := by
      have := norm_sub_norm_le (jointRadicalLimit Ψ τ₀) (jointRadicalLimit Ψ τ)
      rw [norm_sub_rev] at h1
      linarith
    have h3 := (hK R hR1 τ).trans herr
    have h4 : m / 4 ≤ ‖paperFT (jointRadicalTest Ψ R) τ‖ := by
      have := norm_sub_norm_le (jointRadicalLimit Ψ τ) (paperFT (jointRadicalTest Ψ R) τ)
      rw [norm_sub_rev] at h3
      linarith
    exact pow_le_pow_left₀ (by positivity) h4 2
  have hint := integrable_normSq_paperFT (contDiff_jointRadicalTest hΨc R)
    (tsupport_jointRadicalTest Ψ R)
  calc η * (m / 4) ^ 2 = ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), (m / 4) ^ 2 := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith)]; ring
    _ ≤ ∫ τ in Icc (τ₀ - η / 2) (τ₀ + η / 2), ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn
          measurableSet_Icc hlow
    _ ≤ ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ => by positivity)

end JointRadical

/-! ### The explicit formula of an odd `L(s, χ)` in symbol form -/

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
theorem parity_of_odd {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) :
    Zeta23.ThmE.parity χ = 1 := by
  have hne : ¬ χ.Even := fun he => by
    have h1 := he; have h2 := hodd
    unfold DirichletCharacter.Even at h1
    unfold DirichletCharacter.Odd at h2
    rw [h1] at h2; norm_num at h2
  unfold Zeta23.ThmE.parity; rw [if_neg hne]

/-- **Twisted Weil energy of an odd character.**  For an odd real primitive character `χ` mod `q`
and a `C²` test supported in `[-a, a]`,
`∫ |h_f|² S_{Λχ} = 2π Re W_χ(f) - ∫ |h_f(τ)|² (log q + π / cosh(πτ)) dτ`. -/
theorem integral_weilAtomSymbol_dirichlet_odd (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * ((dirichletZeros hq hprim).W f f).re - Real.log q * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) -
        ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (π / Real.cosh (π * τ)) := by
  obtain ⟨hfc, hkd, hks, hki, hFk⟩ := weilTest_self_data hf hfs
  set k := EF.weilTest f f with hk
  set N := ⌊Real.exp (2 * a)⌋₊ with hN
  obtain ⟨-, hEF⟩ := Zeta23.ThmE.EF_lit_chi_L (q := q) (χ := χ) hq hprim k hkd
    (EF.hasCompactSupport_of_tsupport_subset hks)
  have hW : (dirichletZeros hq hprim).W f f = ∑' ρ : (dirichletZeros hq hprim).carrier,
      ((dirichletZeros hq hprim).mult ρ : ℂ) * paperFT k (gammaOf ρ) := by
    unfold ZeroConfig.W
    congr 1; funext ρ
    simp only [ZeroConfig.Wsummand, hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      mul_assoc]
  have hk0 : ∀ y : ℝ, 2 * a < |y| → k y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨this.1, this.2⟩
      linarith
  have hprime : ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (Zeta23.ThmE.coeff χ n * k (Real.log n) +
        (starRingEnd ℂ) (Zeta23.ThmE.coeff χ n) * k (-Real.log n)) =
      ∑ n ∈ Finset.Icc 2 N, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (χ (n : ZMod q)).re : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N)]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [coeff_of_real hreal, Complex.conj_ofReal]; push_cast; ring
    · intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have : n = 0 ∨ n = 1 := by omega
        rcases this with rfl | rfl <;> simp
      · push Not at hn
        have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn
        have hlog : 2 * a < Real.log n := by
          rw [← Real.log_exp (2 * a)]; exact Real.log_lt_log (Real.exp_pos _) hexp
        have hl0 : 0 ≤ Real.log n := le_trans (by linarith) hlog.le
        rw [hk0 _ (by rw [abs_of_nonneg hl0]; exact hlog),
          hk0 _ (by rw [abs_neg, abs_of_nonneg hl0]; exact hlog)]
        simp
  have hq0 : 0 < q := by omega
  have harch : ∫ r : ℝ, paperFT k r * ((((Complex.digamma (1 / 4 + ((1 : ℕ) : ℂ) / 2 +
      I * r / 2)).re + Real.log ((q : ℝ) / π) : ℝ)) : ℂ) =
      ((∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log q +
        π / Real.cosh (π * r)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext r
    have hd := re_digamma_threeQuarter_sub_quarter r
    rw [hk, paperFT_weilTest_self_ofReal hf.continuous hfc, archimedeanWeilSymbol_div_conductor q hq0,
      Nat.cast_one]
    rw [show (Complex.digamma (1 / 4 + (1 : ℂ) / 2 + I * r / 2)).re =
      (Complex.digamma (1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * r / 2)).re + π / Real.cosh (π * r) by
        linarith]
    push_cast; ring
  have hEF' : ∑' ρ : (dirichletZeros hq hprim).carrier,
      ((dirichletZeros hq hprim).mult ρ : ℂ) * paperFT k (gammaOf ρ) =
      Zeta23.ThmE.literatureRHSchi (Zeta23.ThmE.parity χ) q (Zeta23.ThmE.coeff χ) k := hEF
  clear hEF
  rw [← hW, Zeta23.ThmE.literatureRHSchi, parity_of_odd hodd, hprime, harch] at hEF'
  have hEF := hEF'
  have hre := congrArg Complex.re hEF
  simp only [Complex.add_re, Complex.neg_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hre
  have hdiv : ((1 / (2 * π) : ℂ)).re = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have hdivim : ((1 / (2 * π) : ℂ)).im = 0 := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_im]
  rw [hdiv, hdivim, zero_mul, sub_zero] at hre
  rw [integral_weilAtomSymbol_eq_arch_sub hf hfs]
  have hsech : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * (π / Real.cosh (π * r)) := by
    refine ((integrable_normSq_paperFT hf hfs).mul_const π).mono'
      ((integrable_normSq_paperFT hf hfs).aestronglyMeasurable.mul
        (continuous_const.div (by fun_prop) fun r => (Real.cosh_pos (π * r)).ne' :
          Continuous fun r : ℝ => π / Real.cosh (π * r)).aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    have hc : 1 ≤ Real.cosh (π * r) := Real.one_le_cosh _
    have hq' : π / Real.cosh (π * r) ≤ π := div_le_self Real.pi_pos.le hc
    have hp' : 0 ≤ π / Real.cosh (π * r) := div_nonneg Real.pi_pos.le (by linarith)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hp')]
    exact mul_le_mul_of_nonneg_left hq' (sq_nonneg _)
  have hI2 : ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) + Real.log q +
      π / Real.cosh (π * r)) =
      (∫ r : ℝ, ‖paperFT f r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π))) +
        Real.log q * (∫ r : ℝ, ‖paperFT f r‖ ^ 2) +
        ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (π / Real.cosh (π * r)) := by
    have e : (fun r : ℝ => ‖paperFT f r‖ ^ 2 * (archimedeanWeilSymbol (r / (2 * π)) +
        Real.log q + π / Real.cosh (π * r))) = fun r : ℝ =>
        (‖paperFT f r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π)) +
          Real.log q * ‖paperFT f r‖ ^ 2) + ‖paperFT f r‖ ^ 2 * (π / Real.cosh (π * r)) := by
      funext r; ring
    have i1 : Integrable fun r : ℝ => ‖paperFT f r‖ ^ 2 * archimedeanWeilSymbol (r / (2 * π)) +
        Real.log q * ‖paperFT f r‖ ^ 2 :=
      (integrable_normSq_paperFT_mul_arch hf hfs).add
        ((integrable_normSq_paperFT hf hfs).const_mul _)
    have i2 : Integrable fun r : ℝ => Real.log q * ‖paperFT f r‖ ^ 2 :=
      (integrable_normSq_paperFT hf hfs).const_mul _
    rw [e, integral_add i1 hsech, integral_add (integrable_normSq_paperFT_mul_arch hf hfs) i2,
      integral_const_mul]
  rw [hI2] at hre
  set J := ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (π / Real.cosh (π * r)) with hJ
  set M := ∫ r : ℝ, ‖paperFT f r‖ ^ 2 with hM
  have hsum : ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re) /
      Real.sqrt n * (k (Real.log n) + k (-Real.log n)).re =
      ∑ n ∈ Finset.Icc 2 N, (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (χ (n : ZMod q)).re) * (k (Real.log n) + k (-Real.log n)).re :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hsum]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  simp only [Complex.add_re]
  rw [hre]
  field_simp
  ring


/-! ### Tilting the von Mangoldt weights towards an imaginary quadratic character -/

/-- **Exact energy of the tilted weights, odd case.**  For an odd real primitive character `χ` mod
`q` and a polar-constrained level-`a` test,
`∫ |h_f|² S_{Λ(1-t+tχ)} = 2π(1-t) Re W_ζ(f) + t (2π Re W_χ(f) - ∫ |h_f|² (log q + π sech(πτ)))`. -/
theorem integral_weilAtomSymbol_dirichletMix_odd (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hm : paperFT f (-(I / 2)) = 0) (t : ℝ) :
    ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      2 * π * (1 - t) * (zetaZeroConfig.W f f).re +
        t * (2 * π * ((dirichletZeros hq hprim).W f f).re -
          Real.log q * (∫ τ : ℝ, ‖paperFT f τ‖ ^ 2) -
          ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * (π / Real.cosh (π * τ))) := by
  have hΛ := integrable_normSq_paperFT_mul_weilAtomSymbol hf hfs
  have hχ := integrable_normSq_paperFT_mul_weilAtomSymbol_of hf hfs
    (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re)
  have hpt : ∀ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
      (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
      ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) =
      (1 - t) * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) +
      t * (‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (χ (n : ZMod q)).re) ⌊Real.exp (2 * a)⌋₊
          (τ / (2 * π))) := by
    intro τ; rw [weilAtomSymbol_dirichletMix]; ring
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add (hΛ.const_mul _)
    (hχ.const_mul _), integral_const_mul, integral_const_mul,
    integral_weilAtomSymbol_dirichlet_odd hq hprim hodd hreal ha hf hfs]
  have hW := zeta_W_eq_integral_weilAtomSymbol_vonMangoldt hf hfs hp hm
  have hWre : (zetaZeroConfig.W f f).re = 1 / (2 * π) * ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
      weilAtomSymbol (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ⌊Real.exp (2 * a)⌋₊
        (τ / (2 * π)) := by
    rw [hW, Complex.ofReal_re]
  rw [hWre]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- **The generic tilt violation.**  Let `Ψ` be a super-exponentially decaying kernel whose
transform vanishes at every zero of a configuration `Z` and not at `-3i/4`.  If the energy of the
weights `λ` on the joint radical tests is at most
`2π(1-t) Re W_ζ + t (2π Re W_Z - c₀ ∫ |h|²)` with `t, c₀ > 0`, then Weil positivity fails for `λ`. -/
theorem weilAtomSymbol_not_nonneg_of_joint_radical (Z : ZeroConfig)
    (hZs : Summable fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
    (hZstrip : ∀ ρ : Z.carrier, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1)
    {Ψ : ℝ → ℂ} (hΨs : SuperExpDecay Ψ) {CΨ : ℝ} (hCΨ : 0 ≤ CΨ)
    (hΨd : ∀ u, ‖Ψ u‖ ≤ CΨ * Real.exp (-|u|))
    (hΨz : ∀ ρ : Z.carrier, paperFT Ψ (gammaOf ρ) = 0) (hΨ0 : paperFT Ψ (-(3 / 4 * I)) ≠ 0)
    (lam : ℕ → ℝ) {t c₀ : ℝ} (ht : 0 < t) (hc₀ : 0 < c₀)
    (henergy : ∀ R : ℝ, 1 ≤ R →
      ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2 * weilAtomSymbol lam
        ⌊Real.exp (2 * (5 * R))⌋₊ (τ / (2 * π)) ≤
      2 * π * (1 - t) * (zetaZeroConfig.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re +
        t * (2 * π * (Z.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re -
          c₀ * ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2)) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  have hΨc : Continuous Ψ := hΨs.1
  obtain ⟨c, R₀, hc, hR₀, hmass⟩ := exists_integral_normSq_jointRadicalTest_ge hΨs hΨ0 hCΨ hΨd
  obtain ⟨KW, hKW0, hKW⟩ := exists_norm_W_zeta_jointRadicalTest_le hΨc hΨd
  obtain ⟨KL, hKL0, hKL⟩ := exists_norm_W_jointRadicalTest_le Z hZs hZstrip hΨc hCΨ hΨd hΨz
  set M := 2 * π * |1 - t| * KW + 2 * π * t * KL with hM
  have hM0 : 0 ≤ M := by positivity
  have hlim : Tendsto (fun R : ℝ => M * (R * Real.exp (-(R / 2)))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
    have h2 := (h.const_mul 2).const_mul M
    simp only [mul_zero] at h2
    refine h2.congr fun R => ?_
    simp only [Function.comp_apply, id, pow_one]; ring
  obtain ⟨R, hRsmall, hRbig⟩ := ((hlim.eventually (gt_mem_nhds (by positivity :
    (0 : ℝ) < t * c₀ * c))).and (eventually_ge_atTop R₀)).exists
  have hR1 : 1 ≤ R := hR₀.trans hRbig
  have hR0 : 0 ≤ R := by linarith
  refine ⟨5 * R, by linarith, jointRadicalTest Ψ R, contDiff_jointRadicalTest hΨc R,
    tsupport_jointRadicalTest Ψ R, paperFT_jointRadicalTest_half_I hΨc R,
    paperFT_jointRadicalTest_neg_half_I hΨc R, ?_⟩
  refine lt_of_le_of_lt (henergy R hR1) ?_
  have hW1 : (1 - t) * (zetaZeroConfig.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re ≤
      |1 - t| * (KW * (R * Real.exp (-(R / 2)))) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hKW R hR1))
      (abs_nonneg _)
  have hW2 : (Z.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re ≤
      KL * (R * Real.exp (-(R / 2))) :=
    (Complex.re_le_norm _).trans (hKL R hR1)
  have hm := hmass R hRbig
  have hπ : 0 < π := Real.pi_pos
  have key : 2 * π * (1 - t) * (zetaZeroConfig.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re +
      t * (2 * π * (Z.W (jointRadicalTest Ψ R) (jointRadicalTest Ψ R)).re) ≤
      M * (R * Real.exp (-(R / 2))) := by
    have h1 := mul_le_mul_of_nonneg_left hW1 (by positivity : (0 : ℝ) ≤ 2 * π)
    have h2 := mul_le_mul_of_nonneg_left hW2 (by positivity : (0 : ℝ) ≤ 2 * π * t)
    rw [hM]
    nlinarith
  have hcq : t * c₀ * c ≤ t * (c₀ * ∫ τ : ℝ, ‖paperFT (jointRadicalTest Ψ R) τ‖ ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hc₀.le) ht.le
  nlinarith

/-- **Weil positivity fails when the von Mangoldt weights are tilted towards an imaginary quadratic
character.**  Let `χ` be an odd real primitive Dirichlet character of conductor `q`.  For every
`t > 0` the weights `Λ(n)(1 - t + tχ(n))` give negative finite-atom Weil symbol energy on some
polar-constrained `C²` test.  At `t = 1/2` these are the von Mangoldt weights on the split primes of
the imaginary quadratic field of discriminant `-q`, with half weight on the ramified primes; the
inert primes are deleted with their odd powers.  The defect is `t ∫ |h|² (log q + π sech(πτ))`. -/
theorem dirichletMix_weilAtomSymbol_not_nonneg_odd (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  obtain ⟨CΨ, hCΨ, hΨd⟩ := exists_norm_dirichletOddAxisKernel_le χ (B := 1) (by norm_num)
  have hΨd' : ∀ u, ‖dirichletOddAxisKernel χ u‖ ≤ CΨ * Real.exp (-|u|) := fun u => by
    simpa using hΨd u
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine weilAtomSymbol_not_nonneg_of_joint_radical (dirichletZeros hq hprim)
    (summable_dirichletZeros hq hprim)
    (fun ρ => by
      have h : Zeta23.ThmE.IsNontrivialZeroL χ (ρ : ℂ) := ρ.2
      exact ⟨h.2.1, h.2.2⟩)
    (superExpDecay_dirichletOddAxisKernel χ) hCΨ hΨd'
    (fun ρ => paperFT_dirichletOddAxisKernel_gammaOf_eq_zero hq hodd ρ.2)
    (paperFT_dirichletOddAxisKernel_ne_zero hq hodd) _ ht hlogq (fun R hR => ?_)
  have hΨc := continuous_dirichletOddAxisKernel χ
  rw [integral_weilAtomSymbol_dirichletMix_odd hq hprim hodd hreal (by linarith)
    (contDiff_jointRadicalTest hΨc R) (tsupport_jointRadicalTest _ R)
    (paperFT_jointRadicalTest_half_I hΨc R) (paperFT_jointRadicalTest_neg_half_I hΨc R)]
  have hJ : 0 ≤ ∫ τ : ℝ, ‖paperFT (jointRadicalTest (dirichletOddAxisKernel χ) R) τ‖ ^ 2 *
      (π / Real.cosh (π * τ)) :=
    integral_nonneg fun τ => mul_nonneg (sq_nonneg _)
      (div_nonneg Real.pi_pos.le (Real.cosh_pos _).le)
  nlinarith

/-- **The quadratic conductor law.**  For every real primitive Dirichlet character `χ` of
conductor `q > 1`, even or odd, and every `t > 0`, the weights `Λ(n)(1 - t + tχ(n))` violate Weil
positivity with the archimedean term of `ζ`.  Every quadratic field's splitting law is load-bearing:
weighting down its inert primes costs at least `t log q ∫ |h|²` on joint radical tests. -/
theorem quadraticMix_weilAtomSymbol_not_nonneg (hq : 1 < q) {χ : DirichletCharacter ℂ q}
    (hprim : χ.IsPrimitive) (hreal : ∀ a : ZMod q, (χ a).im = 0) {t : ℝ} (ht : 0 < t) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0 ∧
      ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol
        (fun n => ArithmeticFunction.vonMangoldt n * (1 - t + t * (χ (n : ZMod q)).re))
        ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) < 0 := by
  rcases χ.even_or_odd with heven | hodd
  · exact dirichletMix_weilAtomSymbol_not_nonneg hq hprim heven hreal ht
  · exact dirichletMix_weilAtomSymbol_not_nonneg_odd hq hprim hodd hreal ht

end RHTower
