import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SymmetricDualVaughanBilinearizationAndPrimeAlmostPrimeAnnihilation

/-!
# Zeta-Free Balanced Bilinear Dirichlet-Polynomial Reduction, Divisor-Cube Coefficient Bounds, Critical-Line Residue Extraction, and Disjunctive Off-Line/Critical-Line Forcing on `Ω_open`

In `CriticalLineVaughanTypeIIAbscissaEliminationAndShellLocalization`, shifting the direct Type-II
pairing onto `Re = 1 / 2` still leaves `ζ(1 / 2 + i t)` inside the critical-line integral at length
`Y = |Im s|^{3 + η}`. Conversely, in
`SymmetricDualVaughanBilinearizationAndPrimeAlmostPrimeAnnihilation`, passing to the dual side
produces the finite symmetric balanced bilinear band `balancedDualBilinearBandSum U V K_hi s x` at
shorter length `K_hi = ⌈|Im s|^{2 + η + δ}⌉₊` weighted by `smoothAFEZetaDualCoefficientGeneral`.

This module combines both reductions by shifting `smoothAFEZetaDualCoefficientGeneral s (k x) 0`
from `Re w = -1` rightward across the simple pole `w = 0` onto the critical line
`Re w = 1 / 2 - Re s > 0`, where `‖zetaChi (linePt t)‖ = 1` identically and **no `ζ` factor
appears anywhere**, reducing witness certification across all of
`Ω_open = {s : ℂ | 3001 / 24000 ≤ Re s ∧ Re s < 1 / 2 ∧ 184 < |Im s|}` to pure unweighted finite
divisor-bounded prime-free Dirichlet polynomials:

1. **Divisor-cube bounds on `vaughanDualBilinear` and `parityClearedVaughanDualBilinear`
   (`abs_vaughanDualBilinear_le_four_mul_divisors_cube`,
   `norm_parityClearedVaughanDualBilinear_le_eight_mul_divisors_cube`):**
   Every factor `a ∣ k` satisfies `d(a) ≤ d(k)`, sharpening the coarse `O(k^2)` bound to the exact
   divisor-cube bound `|vaughanDualBilinear U V k| ≤ 4 · d(k)^3` and
   `‖parityClearedVaughanDualBilinear U V k‖ ≤ 8 · d(k)^3` (`O_ε(k^ε)`) for all `k ≥ 1`.

2. **Exact critical-line residue extraction for `smoothAFEZetaDualCoefficientGeneral`
   (`smoothAFEZetaDualCoefficientGeneral_zero_eq_neg_zetaChi_add_criticalLine`,
   `smoothAFEZetaDualCoefficientGeneral_eq_neg_zetaChi_mul_add_criticalLine`):**
   On `-1 ≤ Re w ≤ 1 / 2 - Re s` (`0 < Re s < 1 / 2`), `zetaChi (s + w)` is holomorphic because
   `Re(1 - (s + w)) ≥ 1 / 2 > 0`. Cauchy's integral formula on `[-1, 1 / 2 - Re s] × [-T, T]`
   across the unique simple pole `w = 0` expresses `smoothAFEZetaDualCoefficientGeneral s x (k - 1)`
   as `-zetaChi s · k^{-(1 - s)}` plus a Gaussian-weighted critical-line integral of
   `zetaChi (linePt (Im s + v)) · k^{-conj (linePt (Im s + v))}`.

3. **Exact `ζ`-free decomposition of `balancedDualBilinearBandSum`
   (`balancedBilinearDirichletPoly`, `balancedDualBilinearBandSum_eq_zetaFree_offLine_add_criticalLine`,
   `norm_balancedDualBilinearBandSum_add_zetaChi_mul_dirPoly_le`):**
   Commuting the finite sum `(U + 1)(V + 1) ≤ k ≤ K_hi` with `∫ v : ℝ` expresses
   `balancedDualBilinearBandSum` purely in terms of the unweighted finite Dirichlet polynomial
   `balancedBilinearDirichletPoly U V K_hi` at `1 - s` and along `conj (linePt (Im s + v))`, with
   `‖zetaChi (linePt t)‖ = 1` eliminating all Gamma growth on the critical line.

4. **Disjunctive `ζ`-free Dirichlet-polynomial forcing and `HasStrictPrimeGasWitness` production
   across all of `Ω_open`
   (`zetaFree_balancedBilinearDirichletPoly_disjunctive_forcing_and_witness_on_remaining_strip`):**
   At **every** `s ∈ Ω_open` and for **all** `1 ≤ U, V` with `U * V ≤ |Im s|^{η - 1 / 2}`, any zero
   `ζ(s) = 0` forces **either** `‖balancedBilinearDirichletPoly U V K_hi (1 - s)‖ > 1 / 8` on
   `Re(1 - s) > 1 / 2` **or** the Gaussian-localized critical-line moment of
   `‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (Im s + v)))‖` strictly above order
   `(1 / 2 - Re s) · |Im s|^{(2 + η)(1/2 - Re s)}`; conversely, bounding both pure unweighted
   Dirichlet polynomial quantities yields an unconditional `HasStrictPrimeGasWitness` at `s`.
-/

noncomputable section

open Complex Filter Set MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate Topology ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open GaloisForLFunctions.ArithmeticPositiveDuality
open _root_.RHTower

/-! ### Part 1: Divisor-Cube Coefficient Bounds (`O_ε(k^ε)`) on `vaughanDualBilinear` -/

section Part1DivisorCubeBounds

private lemma card_divisors_le_of_dvd {a k : ℕ} (hk : 1 ≤ k) (hdvd : a ∣ k) :
    a.divisors.card ≤ k.divisors.card := by
  have hk_ne0 : k ≠ 0 := by omega
  refine Finset.card_le_card fun d hd => ?_
  exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hd) hdvd, hk_ne0⟩

private lemma one_le_card_divisors {k : ℕ} (hk : 1 ≤ k) :
    1 ≤ k.divisors.card := by
  have hmem : 1 ∈ k.divisors := Nat.mem_divisors.mpr ⟨one_dvd k, by omega⟩
  exact Finset.card_pos.mpr ⟨1, hmem⟩

/-- **Exact divisor-cube bound on `vaughanDualBilinear`:**
for all `U, V : ℕ` and every `k ≥ 1`, `|vaughanDualBilinear U V k| ≤ 4 * (k.divisors.card : ℝ) ^ 3`. -/
theorem abs_vaughanDualBilinear_le_four_mul_divisors_cube
    (U V : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    |vaughanDualBilinear U V k| ≤ 4 * (k.divisors.card : ℝ) ^ (3 : ℕ) := by
  have h1_le_dk : (1 : ℝ) ≤ (k.divisors.card : ℝ) := by exact_mod_cast one_le_card_divisors hk
  unfold vaughanDualBilinear
  rw [ArithmeticFunction.mul_apply]
  have hpt : ∀ p ∈ k.divisorsAntidiagonal,
      |_root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2| ≤
        4 * (k.divisors.card : ℝ) ^ (2 : ℕ) := by
    intro p hp
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hd1 : p.1 ∣ k := ⟨p.2, hprod.symm⟩
    have hd2 : p.2 ∣ k := ⟨p.1, by rw [mul_comm]; exact hprod.symm⟩
    have hc1 : (p.1.divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_le_of_dvd hk hd1
    have hc2 : (p.2.divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_le_of_dvd hk hd2
    have hb1 : |_root_.RHTower.Sieve.typeIIShort U p.1| ≤ 2 * (k.divisors.card : ℝ) := by
      have h := _root_.RHTower.Sieve.abs_one_sub_zeta_mul_moebius_le U p.1
      change |_root_.RHTower.Sieve.typeIIShort U p.1| ≤ 1 + (p.1.divisors.card : ℝ) at h
      linarith
    have hb2 : |_root_.RHTower.Sieve.typeIIShort V p.2| ≤ 2 * (k.divisors.card : ℝ) := by
      have h := _root_.RHTower.Sieve.abs_one_sub_zeta_mul_moebius_le V p.2
      change |_root_.RHTower.Sieve.typeIIShort V p.2| ≤ 1 + (p.2.divisors.card : ℝ) at h
      linarith
    rw [abs_mul]
    calc |_root_.RHTower.Sieve.typeIIShort U p.1| * |_root_.RHTower.Sieve.typeIIShort V p.2|
        ≤ (2 * (k.divisors.card : ℝ)) * (2 * (k.divisors.card : ℝ)) :=
          mul_le_mul hb1 hb2 (abs_nonneg _) (by positivity)
      _ = 4 * (k.divisors.card : ℝ) ^ (2 : ℕ) := by ring
  calc |∑ p ∈ k.divisorsAntidiagonal,
          _root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2|
      ≤ ∑ p ∈ k.divisorsAntidiagonal,
          |_root_.RHTower.Sieve.typeIIShort U p.1 * _root_.RHTower.Sieve.typeIIShort V p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ k.divisorsAntidiagonal, 4 * (k.divisors.card : ℝ) ^ (2 : ℕ) := Finset.sum_le_sum hpt
    _ = (k.divisorsAntidiagonal.card : ℝ) * (4 * (k.divisors.card : ℝ) ^ (2 : ℕ)) := by simp
    _ = 4 * (k.divisors.card : ℝ) ^ (3 : ℕ) := by
        rw [_root_.RHTower.Sieve.card_divisorsAntidiagonal]; ring

/-- **Exact divisor-cube bound on `parityClearedVaughanDualBilinear`:**
for all `U, V : ℕ` and every `k ≥ 1`,
`‖parityClearedVaughanDualBilinear U V k‖ ≤ 8 * (k.divisors.card : ℝ) ^ 3`. -/
theorem norm_parityClearedVaughanDualBilinear_le_eight_mul_divisors_cube
    (U V : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ‖parityClearedVaughanDualBilinear U V k‖ ≤ 8 * (k.divisors.card : ℝ) ^ (3 : ℕ) := by
  unfold parityClearedVaughanDualBilinear
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖((vaughanDualBilinear U V k : ℝ) : ℂ)‖ ≤ 4 * (k.divisors.card : ℝ) ^ (3 : ℕ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_vaughanDualBilinear_le_four_mul_divisors_cube U V hk
  have h2 : ‖if 2 ∣ k then ((vaughanDualBilinear U V (k / 2) : ℝ) : ℂ) else 0‖ ≤
      4 * (k.divisors.card : ℝ) ^ (3 : ℕ) := by
    split_ifs with h2k
    · obtain ⟨q, hq⟩ := h2k
      have hk2_pos : 1 ≤ k / 2 := by omega
      have hdvd : (k / 2) ∣ k := ⟨2, by omega⟩
      have hc_le : ((k / 2).divisors.card : ℝ) ≤ (k.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_le_of_dvd hk hdvd
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_vaughanDualBilinear_le_four_mul_divisors_cube U V hk2_pos).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc_le 3) (by norm_num))
    · rw [norm_zero]; positivity
  linarith

end Part1DivisorCubeBounds


/-! ### Part 2: Critical-Line Residue Extraction for `smoothAFEZetaDualCoefficientGeneral` -/

section Part2CriticalLineDualResidueExtraction

/-- **Exact critical-line residue extraction for `smoothAFEZetaDualCoefficientGeneral s y 0`:**
for every `0 < Re s < 1 / 2` and `y > 0`, shifting `Re w = -1` rightward across the unique simple
pole `w = 0` onto `Re w = 1 / 2 - Re s > 0` (`s + w = linePt (Im s + v)`) extracts `-zetaChi s`
plus an exact critical-line Gaussian integral where `‖zetaChi (linePt (Im s + v))‖ = 1`. -/
theorem smoothAFEZetaDualCoefficientGeneral_zero_eq_neg_zetaChi_add_criticalLine
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {y : ℝ} (hy : 0 < y) :
    smoothAFEZetaDualCoefficientGeneral s y 0 =
      -zetaChi s +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            zetaChi (linePt (s.im + v)) *
              (y : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hs1 : s.re < 1 := by linarith
  set a : ℝ := 1 / 2 - s.re
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have ha_lt_half : a < 1 / 2 := by dsimp only [a]; linarith
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
    simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
  -- Step 1: Write `smoothAFEZetaReflectedTerm s y 0 w = g w * (w - 0)⁻¹` on `U = {Re(s + w) < 7 / 8}`.
  set U_dom : Set ℂ := {w : ℂ | (s + w).re < 7 / 8}
  have hU_open : IsOpen U_dom :=
    isOpen_lt (Complex.continuous_re.comp (continuous_const.add continuous_id)) continuous_const
  set g : ℂ → ℂ := fun w => zetaChi (s + w) * (y : ℂ) ^ w * Complex.exp (w ^ (2 : ℕ))
  have hg_diff : DifferentiableOn ℂ g U_dom := by
    intro w hw
    have hre_pos : 0 < (1 - (s + w)).re := by
      have hw' : (s + w).re < 7 / 8 := hw
      simp only [Complex.sub_re, Complex.one_re]; linarith
    haveI : NeZero (y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hy.ne'⟩
    have hd1 : DifferentiableAt ℂ (fun u => zetaChi (s + u)) w :=
      (zetaChi_analyticAt (Complex.Gammaℝ_ne_zero_of_re_pos hre_pos)).differentiableAt.comp w
        (differentiableAt_const s |>.add differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun u => (y : ℂ) ^ u) w :=
      (differentiable_const_cpow_of_neZero (y : ℂ)).differentiableAt
    have hd3 : DifferentiableAt ℂ (fun u => Complex.exp (u ^ (2 : ℕ))) w :=
      (differentiable_exp.comp (differentiable_pow 2)).differentiableAt
    exact ((hd1.mul hd2).mul hd3).differentiableWithinAt
  have hg_an : AnalyticOnNhd ℂ g U_dom := hg_diff.analyticOnNhd hU_open
  have hg_zero : g 0 = zetaChi s := by dsimp only [g]; simp
  have hH_eq : smoothAFEZetaReflectedTerm s y 0 = fun w => g w * (w - 0)⁻¹ := by
    funext w
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    dsimp only [g, smoothAFEGaussianKernel]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one, sub_zero, div_eq_mul_inv]
    ring
  -- Step 2: Cauchy integral formula on `[-1, a] × [-T, T]` for `T > 0`.
  have hrect : ∀ T : ℝ, 0 < T →
      ((∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * zetaChi s := by
    intro T hT
    set z₁ : ℂ := (-1 : ℂ) - (T : ℂ) * I
    set z₂ : ℂ := (a : ℂ) + (T : ℂ) * I
    have hz₁_re : z₁.re = -1 := by simp [z₁]
    have hz₁_im : z₁.im = -T := by simp [z₁]
    have hz₂_re : z₂.re = a := by simp [z₂]
    have hz₂_im : z₂.im = T := by simp [z₂]
    have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U_dom := by
      intro w hw
      rw [Complex.mem_reProdIm, hz₁_re, hz₂_re, uIcc_of_le (by linarith)] at hw
      show (s + w).re < 7 / 8
      rw [Complex.add_re]
      have hw_hi : w.re ≤ 1 / 2 - s.re := hw.1.2
      linarith
    have hbox := rectIntegral_cauchyFormula_analyticOnNhd hsub hg_an
      (p := 0) (by rw [hz₁_re]; norm_num) (by rw [hz₂_re]; simpa using ha_pos)
      (by rw [hz₁_im]; simp; linarith) (by rw [hz₂_im]; simp; linarith)
    rw [← hH_eq, hg_zero] at hbox
    simpa [rectIntegral, z₁, z₂, sub_eq_add_neg] using hbox
  -- Step 3: Horizontal edges `(-1)..a` at `± i T` vanish as `T → +∞`.
  obtain ⟨T₀_s, N_s, C_s, hCs_pos, hchi_strip⟩ :=
    hasStripPolyGrowthOffReal_zetaChi (s.re - 1) (1 / 2)
  have hhoriz : ∀ ε : ℝ, |ε| = 1 →
      Tendsto (fun T : ℝ =>
        ∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) + ((ε * T : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro ε hε
    set Y_bd : ℝ := max (y ^ (-1 : ℝ)) (y ^ a)
    set K_sh : ℝ := C_s * Y_bd * Real.exp 1
    refine GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun T => K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))))
      (hgt := fun T => ε * T) ?_
      (by simpa using (tendsto_shifted_pow_mul_exp_neg_sq (1 + |s.im|) N_s).const_mul K_sh)
    filter_upwards [eventually_ge_atTop (max 1 (|T₀_s| + |s.im| + 2))] with T hT u hu
    rw [Set.uIoc_of_le (by linarith : (-1 : ℝ) ≤ a)] at hu
    have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
    have hT_big : |T₀_s| + |s.im| + 2 ≤ T := (le_max_right _ _).trans hT
    have habsv : |ε * T| = T := by rw [abs_mul, hε, one_mul, abs_of_pos (zero_lt_one.trans_le hT1)]
    set w : ℂ := (u : ℂ) + ((ε * T : ℝ) : ℂ) * I
    have hsw_re1 : s.re - 1 ≤ (s + w).re := by simp [w]; linarith [hu.1.le]
    have hsw_re2 : (s + w).re ≤ 1 / 2 := by
      simp [w]; have : u ≤ 1 / 2 - s.re := hu.2; linarith
    have hsw_im_ge : T₀_s ≤ |(s + w).im| := by
      rw [Complex.add_im, show w.im = ε * T by simp [w]]
      have htri : |ε * T| - |s.im| ≤ |s.im + ε * T| := by
        have h := abs_sub_abs_le_abs_sub (ε * T) (-s.im)
        simpa [abs_neg, sub_neg_eq_add, add_comm] using h
      linarith [le_abs_self T₀_s]
    have hsw_im_le : 1 + |(s + w).im| ≤ (1 + |s.im|) + T := by
      calc 1 + |(s + w).im|
          = 1 + |s.im + ε * T| := by rw [Complex.add_im, show w.im = ε * T by simp [w]]
        _ ≤ 1 + (|s.im| + |ε * T|) := by linarith [abs_add_le s.im (ε * T)]
        _ = (1 + |s.im|) + T := by rw [habsv]; ring
    have hchi_bd : ‖zetaChi (s + w)‖ ≤ C_s * ((1 + |s.im|) + T) ^ N_s :=
      (hchi_strip (s + w) hsw_re1 hsw_re2 hsw_im_ge).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsw_im_le N_s) hCs_pos)
    have hy_le : ‖(y : ℂ) ^ w‖ ≤ Y_bd := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, show w.re = u by simp [w]]
      rcases le_total 1 y with h1y | h1y
      · exact (Real.rpow_le_rpow_of_exponent_le h1y hu.2).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hy h1y hu.1.le).trans (le_max_left _ _)
    have hker_le : ‖smoothAFEGaussianKernel w‖ ≤ Real.exp 1 * Real.exp (-(T ^ (2 : ℕ))) := by
      rw [smoothAFEGaussianKernel, norm_div, Complex.norm_exp]
      have hw_re_sq : (w ^ 2).re = u ^ 2 - T ^ (2 : ℕ) := by
        dsimp only [w]
        simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have hε2 : ε * ε = 1 := by have := sq_abs ε; rw [hε] at this; nlinarith
        nlinarith
      have hu2 : u ^ 2 ≤ 1 := by
        have h1 : -1 ≤ u := hu.1.le
        have h2 : u ≤ 1 := hu.2.trans (by linarith)
        nlinarith
      have hwnorm1 : 1 ≤ ‖w‖ := by
        calc (1 : ℝ) ≤ T := hT1
          _ = |w.im| := by simp [w, habsv]
          _ ≤ ‖w‖ := Complex.abs_im_le_norm w
      rw [hw_re_sq]
      exact (div_le_self (Real.exp_nonneg _) hwnorm1).trans
        (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith))
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul]
    calc ‖zetaChi (s + w)‖ * ‖(y : ℂ) ^ w‖ * ‖smoothAFEGaussianKernel w‖
        ≤ (C_s * ((1 + |s.im|) + T) ^ N_s) * Y_bd * (Real.exp 1 * Real.exp (-(T ^ (2 : ℕ)))) := by
          refine mul_le_mul (mul_le_mul hchi_bd hy_le (norm_nonneg _) (by positivity))
            hker_le (norm_nonneg _) ?_
          exact mul_nonneg (by positivity) ((Real.rpow_nonneg hy.le (-1)).trans (le_max_left _ _))
      _ = K_sh * (((1 + |s.im|) + T) ^ N_s * Real.exp (-(T ^ (2 : ℕ)))) := by
          dsimp only [K_sh]; ring
  -- Step 4: Right vertical edge `Re w = a` integrability via `‖zetaChi (linePt (s.im + v))‖ = 1`.
  have hsw_lp : ∀ v : ℝ, s + ((a : ℂ) + (v : ℂ) * I) = linePt (s.im + v) := fun v => by
    unfold linePt; dsimp only [a]; apply Complex.ext <;> simp
  have hpt_right : ∀ v : ℝ,
      ‖smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I)‖ ≤
        (y ^ a * (Real.exp (a ^ (2 : ℕ)) / a)) * Real.exp (-(v ^ 2)) := by
    intro v
    have hchi_v : ‖zetaChi (s + ((a : ℂ) + (v : ℂ) * I))‖ = 1 := by
      rw [hsw_lp v]; exact norm_zetaChi_line (s.im + v)
    have hker_v := norm_smoothAFEGaussianKernel_vertical_le ha_pos v
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one]
    rw [norm_mul, norm_mul, hchi_v, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy,
      show (((a : ℂ) + (v : ℂ) * I).re) = a by simp]
    exact (mul_le_mul_of_nonneg_left hker_v (by positivity)).trans_eq (by ring)
  have hright_int : Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I)) := by
    refine Integrable.mono' (hgauss_int.const_mul (y ^ a * (Real.exp (a ^ (2 : ℕ)) / a))) ?_
      (Filter.Eventually.of_forall hpt_right)
    have hcont : Continuous (fun v : ℝ =>
        smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I)) := by
      rw [hH_eq]
      have hpath : Continuous (fun v : ℝ => (a : ℂ) + (v : ℂ) * I) := by fun_prop
      have hg_v : Continuous (fun v : ℝ => g ((a : ℂ) + (v : ℂ) * I)) := by
        refine hg_an.continuousOn.comp_continuous hpath fun v => ?_
        show (s + ((a : ℂ) + (v : ℂ) * I)).re < 7 / 8
        simp [a]; norm_num
      have hinv_v : Continuous (fun v : ℝ => (((a : ℂ) + (v : ℂ) * I) - 0)⁻¹) :=
        (hpath.sub continuous_const).inv₀ fun v h0 => by
          have := congrArg Complex.re h0; simp at this; exact ha_ne this
      exact hg_v.mul hinv_v
    exact hcont.aestronglyMeasurable
  have hleft_int : Integrable (fun v : ℝ =>
      smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I)) := by
    simpa using smoothAFEZetaReflectedTerm_general_left_one_integrable hy hs0 hs1 0
  -- Step 5: Pass `T → +∞` and identify `smoothAFEZetaDualCoefficientGeneral s y 0`.
  have hlim_r : Tendsto (fun T : ℝ =>
      ∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hright_int tendsto_neg_atTop_atBot tendsto_id
  have hlim_l : Tendsto (fun T : ℝ =>
      ∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I))
      atTop (𝓝 (∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hleft_int tendsto_neg_atTop_atBot tendsto_id
  have htop : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) + (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz 1 (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hbot : Tendsto (fun T : ℝ =>
      ∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) - (T : ℂ) * I))
      atTop (𝓝 0) := by
    refine (hhoriz (-1) (by norm_num)).congr fun T => ?_
    refine intervalIntegral.integral_congr fun u _ => ?_
    congr 1; push_cast; ring
  have hcomb := ((hbot.sub htop).add (hlim_r.const_smul I)).sub (hlim_l.const_smul I)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) - (T : ℂ) * I)) -
          (∫ u : ℝ in (-1 : ℝ)..a, smoothAFEZetaReflectedTerm s y 0 ((u : ℂ) + (T : ℂ) * I)) +
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I))) -
        I • (∫ v : ℝ in (-T)..T, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        2 * Real.pi * I * zetaChi s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hrect T hT
  have hinf := tendsto_nhds_unique (hcomb.congr' hev) tendsto_const_nhds
  have hcancel :
      (∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I)) -
        (∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I)) =
        (2 * Real.pi : ℂ) * zetaChi s := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    simpa [smul_eq_mul, mul_sub, mul_assoc, mul_left_comm, mul_comm] using hinf
  have hm1_eq : smoothAFEZetaDualCoefficientGeneral s y 0 =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I) := by
    unfold smoothAFEZetaDualCoefficientGeneral smoothAFEZetaDualCutoffGeneral
    rw [Complex.real_smul, show (((-1 : ℝ) : ℂ)) = (-1 : ℂ) by norm_num]
    calc (zetaChi s * (((0 : ℕ) : ℂ) + 1) ^ (s - 1)) *
          ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((((0 : ℕ) : ℝ) + 1) * y))
              ((-1 : ℂ) + (v : ℂ) * I))
        = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ((zetaChi s * (((0 : ℕ) : ℂ) + 1) ^ (s - 1)) *
              ∫ v : ℝ, smoothAFEDualRatioIntegrand s (1 / ((((0 : ℕ) : ℝ) + 1) * y))
                ((-1 : ℂ) + (v : ℂ) * I)) := by ring
      _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((-1 : ℂ) + (v : ℂ) * I) := by
          rw [integral_smoothAFEZetaReflectedTerm_general_left_one_eq hy hs0 hs1]
  have hint_a_eq :
      (∫ v : ℝ, smoothAFEZetaReflectedTerm s y 0 ((a : ℂ) + (v : ℂ) * I)) =
        ∫ v : ℝ,
          zetaChi (linePt (s.im + v)) *
            (y : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [smoothAFEZetaReflectedTerm_eq_cpow]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, mul_one]
    have hlp := hsw_lp v
    dsimp only [a] at hlp ⊢
    rw [hlp]
  have hpi_ne : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hinv_pi : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (2 * Real.pi : ℂ) = 1 := by
    push_cast
    exact one_div_mul_cancel hpi_ne
  rw [hm1_eq, ← hint_a_eq]
  linear_combination
    -((((1 / (2 * Real.pi) : ℝ) : ℂ)) * hcancel) - zetaChi s * hinv_pi

/-- **Exact critical-line residue extraction for `smoothAFEZetaDualCoefficientGeneral s x (k - 1)` (`k ≥ 1`):**
combining `smoothAFEZetaDualCoefficientGeneral_mul_scale` with
`smoothAFEZetaDualCoefficientGeneral_zero_eq_neg_zetaChi_add_criticalLine` cancels `Re s` inside
`k^{-(1 - s)} * (k x)^{(1/2 - Re s) + i v} = x^{(1/2 - Re s) + i v} * k^{-conj (linePt (Im s + v))}`. -/
theorem smoothAFEZetaDualCoefficientGeneral_eq_neg_zetaChi_mul_add_criticalLine
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {x : ℝ} (hx : 0 < x)
    {k : ℕ} (hk1 : 1 ≤ k) :
    smoothAFEZetaDualCoefficientGeneral s x (k - 1) =
      -zetaChi s * (k : ℂ) ^ (-(1 - s)) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              zetaChi (linePt (s.im + v)) *
              (k : ℂ) ^ (-conj (linePt (s.im + v))) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_ne0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hscale := smoothAFEZetaDualCoefficientGeneral_mul_scale hk1 hx hs0 hhi 0
  rw [zero_add, mul_one] at hscale
  rw [← hscale,
    smoothAFEZetaDualCoefficientGeneral_zero_eq_neg_zetaChi_add_criticalLine hs0 hhi (mul_pos hk_pos hx)]
  have hpull :
      (k : ℂ) ^ (-(1 - s)) *
        (-zetaChi s +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ v : ℝ,
              zetaChi (linePt (s.im + v)) *
                (((k : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) =
        -zetaChi s * (k : ℂ) ^ (-(1 - s)) +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ((k : ℂ) ^ (-(1 - s)) *
              ∫ v : ℝ,
                zetaChi (linePt (s.im + v)) *
                  (((k : ℝ) * x : ℝ) : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                  smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)) := by ring
  rw [hpull, ← MeasureTheory.integral_const_mul]
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  set z : ℂ := ((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I
  have hkx : (((k : ℝ) * x : ℝ) : ℂ) ^ z = (k : ℂ) ^ z * (x : ℂ) ^ z := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk_pos.le hx.le z]
    simp
  have hk_comb : (k : ℂ) ^ (-(1 - s)) * (k : ℂ) ^ z = (k : ℂ) ^ (-conj (linePt (s.im + v))) := by
    rw [← Complex.cpow_add _ _ hk_ne0]
    congr 1
    rw [conj_linePt]
    unfold linePt
    dsimp only [z]
    apply Complex.ext <;> simp
  rw [hkx]
  calc (k : ℂ) ^ (-(1 - s)) *
          (zetaChi (linePt (s.im + v)) * ((k : ℂ) ^ z * (x : ℂ) ^ z) * smoothAFEGaussianKernel z)
      = (x : ℂ) ^ z * smoothAFEGaussianKernel z * zetaChi (linePt (s.im + v)) *
          ((k : ℂ) ^ (-(1 - s)) * (k : ℂ) ^ z) := by ring
    _ = (x : ℂ) ^ z * smoothAFEGaussianKernel z * zetaChi (linePt (s.im + v)) *
          (k : ℂ) ^ (-conj (linePt (s.im + v))) := by rw [hk_comb]

end Part2CriticalLineDualResidueExtraction


/-! ### Part 3: Zeta-Free Decomposition of `balancedDualBilinearBandSum` and Disjunctive Forcing on `Ω_open` -/

section Part3ZetaFreeBalancedBilinearReduction

/-- Pure unweighted finite balanced bilinear Dirichlet polynomial on `(U + 1)(V + 1) ≤ k ≤ K_hi`,
whose coefficients `parityClearedVaughanDualBilinear U V k` are bounded by `8 · d(k)^3` and vanish
identically on every prime `p` and every `m * p` (`m ≤ min U V`). -/
def balancedBilinearDirichletPoly (U V K_hi : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
    parityClearedVaughanDualBilinear U V k * (k : ℂ) ^ (-z)

/-- **Exact `ζ`-free decomposition of `balancedDualBilinearBandSum`:**
for all `U, V, K_hi : ℕ`, `x > 0`, and `0 < Re s < 1 / 2`, `balancedDualBilinearBandSum U V K_hi s x`
equals `-zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)` plus the Gaussian-weighted
critical-line integral of `zetaChi (linePt (Im s + v)) * balancedBilinearDirichletPoly U V K_hi (conj (linePt (Im s + v)))`,
with **no `riemannZeta` factor anywhere**. -/
theorem balancedDualBilinearBandSum_eq_zetaFree_offLine_add_criticalLine
    (U V K_hi : ℕ) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    balancedDualBilinearBandSum U V K_hi s x =
      -zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              zetaChi (linePt (s.im + v)) *
              balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v))) := by
  set a : ℝ := 1 / 2 - s.re
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ 2))) := by
    simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
  set Ψ : ℝ → ℂ := fun v =>
    (x : ℂ) ^ (((a : ℝ) : ℂ) + (v : ℂ) * I) *
      smoothAFEGaussianKernel (((a : ℝ) : ℂ) + (v : ℂ) * I) *
      zetaChi (linePt (s.im + v))
  have hΨ_cont : Continuous Ψ := by
    haveI : NeZero (x : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hx.ne'⟩
    have hpath : Continuous (fun v : ℝ => ((a : ℝ) : ℂ) + (v : ℂ) * I) := by fun_prop
    have hlp : Continuous (fun v : ℝ => linePt (s.im + v)) := by unfold linePt; fun_prop
    have hx_c : Continuous (fun v : ℝ => (x : ℂ) ^ (((a : ℝ) : ℂ) + (v : ℂ) * I)) :=
      (continuous_const_cpow (x : ℂ)).comp hpath
    have hker_c : Continuous (fun v : ℝ => smoothAFEGaussianKernel (((a : ℝ) : ℂ) + (v : ℂ) * I)) := by
      unfold smoothAFEGaussianKernel
      exact (Complex.continuous_exp.comp (hpath.pow 2)).div hpath fun v h0 => by
        have hre := congrArg Complex.re h0; simp at hre; exact ha_pos.ne' hre
    have hchi_c : Continuous (fun v : ℝ => zetaChi (linePt (s.im + v))) := by
      rw [continuous_iff_continuousAt]; intro v
      refine (zetaChi_analyticAt ?_).continuousAt.comp hlp.continuousAt
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      rw [Complex.sub_re, Complex.one_re, linePt_re]; norm_num
    exact (hx_c.mul hker_c).mul hchi_c
  have hΨ_bd : ∀ v : ℝ, ‖Ψ v‖ ≤ (x ^ a * (Real.exp (a ^ (2 : ℕ)) / a)) * Real.exp (-(v ^ 2)) := by
    intro v
    dsimp only [Ψ]
    rw [norm_mul, norm_mul, norm_zetaChi_line (s.im + v), mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hx,
      show ((((a : ℝ) : ℂ) + (v : ℂ) * I).re) = a by simp]
    exact (mul_le_mul_of_nonneg_left (norm_smoothAFEGaussianKernel_vertical_le ha_pos v)
      (by positivity)).trans_eq (by ring)
  set f_int : ℕ → ℝ → ℂ := fun k v =>
    parityClearedVaughanDualBilinear U V k *
      (Ψ v * (k : ℂ) ^ (-conj (linePt (s.im + v))))
  have hf_int : ∀ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi, Integrable (f_int k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)).trans_le (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    haveI : NeZero (k : ℂ) := ⟨by exact_mod_cast (by omega : k ≠ 0)⟩
    have hlp : Continuous (fun v : ℝ => -conj (linePt (s.im + v))) := by
      have hc : Continuous (fun v : ℝ => linePt (s.im + v)) := by unfold linePt; fun_prop
      exact (Complex.continuous_conj.comp hc).neg
    have hcont : Continuous (f_int k) :=
      continuous_const.mul (hΨ_cont.mul ((continuous_const_cpow (k : ℂ)).comp hlp))
    refine Integrable.mono'
      (hgauss_int.const_mul (‖parityClearedVaughanDualBilinear U V k‖ *
        (x ^ a * (Real.exp (a ^ (2 : ℕ)) / a))))
      hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    dsimp only [f_int]
    have hk_le1 : ‖(k : ℂ) ^ (-conj (linePt (s.im + v)))‖ ≤ 1 := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hk_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; simp [linePt_re]; norm_num]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk1) (by norm_num)
    rw [norm_mul, norm_mul]
    calc ‖parityClearedVaughanDualBilinear U V k‖ *
            (‖Ψ v‖ * ‖(k : ℂ) ^ (-conj (linePt (s.im + v)))‖)
        ≤ ‖parityClearedVaughanDualBilinear U V k‖ *
            (((x ^ a * (Real.exp (a ^ (2 : ℕ)) / a)) * Real.exp (-(v ^ 2))) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hΨ_bd v) hk_le1 (norm_nonneg _) (by positivity))
            (norm_nonneg _)
      _ = (‖parityClearedVaughanDualBilinear U V k‖ *
            (x ^ a * (Real.exp (a ^ (2 : ℕ)) / a))) * Real.exp (-(v ^ 2)) := by ring
  unfold balancedDualBilinearBandSum
  have hterm : ∀ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
      parityClearedVaughanDualBilinear U V k * smoothAFEZetaDualCoefficientGeneral s x (k - 1) =
        (-zetaChi s) * (parityClearedVaughanDualBilinear U V k * (k : ℂ) ^ (-(1 - s))) +
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ v : ℝ, f_int k v := by
    intro k hk
    have hk1 : 1 ≤ k := (Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)).trans_le (Finset.mem_Icc.mp hk).1
    rw [smoothAFEZetaDualCoefficientGeneral_eq_neg_zetaChi_mul_add_criticalLine hs0 hhi hx hk1]
    have hpull :
        parityClearedVaughanDualBilinear U V k *
          (-zetaChi s * (k : ℂ) ^ (-(1 - s)) +
            (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
              ∫ v : ℝ,
                (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                  smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
                  zetaChi (linePt (s.im + v)) *
                  (k : ℂ) ^ (-conj (linePt (s.im + v)))) =
          (-zetaChi s) * (parityClearedVaughanDualBilinear U V k * (k : ℂ) ^ (-(1 - s))) +
            (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
              (parityClearedVaughanDualBilinear U V k *
                ∫ v : ℝ, Ψ v * (k : ℂ) ^ (-conj (linePt (s.im + v)))) := by
      dsimp only [Ψ, a]; ring
    rw [hpull, ← MeasureTheory.integral_const_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← integral_finsetSum _ hf_int]
  unfold balancedBilinearDirichletPoly
  congr 2
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only [f_int, Ψ, a]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Quantitative critical-line Gaussian moment bound on the `ζ`-free decomposition:**
using `‖zetaChi (linePt t)‖ = 1` identically on `Re = 1 / 2`, the critical-line remainder between
`balancedDualBilinearBandSum U V K_hi s x` and
`-zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)` is bounded above by
`(exp(1 / 4) / (2 * π * (1 / 2 - Re s))) * x^{1/2 - Re s}` times the Gaussian `L¹` moment of
`‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (Im s + v)))‖`. -/
theorem norm_balancedDualBilinearBandSum_add_zetaChi_mul_dirPoly_le
    (U V K_hi : ℕ) {x : ℝ} (hx : 0 < x)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    ‖balancedDualBilinearBandSum U V K_hi s x +
        zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)‖ ≤
      (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) *
        ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
          ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖ := by
  set a : ℝ := 1 / 2 - s.re
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have ha_lt_half : a < 1 / 2 := by dsimp only [a]; linarith
  have hgauss_int : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ)))) := by
    simpa only [pow_zero, one_mul] using integrable_shifted_pow_mul_exp_neg_sq 1 0
  have hD_cont : Continuous (fun v : ℝ =>
      balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))) := by
    unfold balancedBilinearDirichletPoly
    refine continuous_finsetSum _ fun k hk => ?_
    have hk1 : 1 ≤ k := (Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)).trans_le (Finset.mem_Icc.mp hk).1
    haveI : NeZero (k : ℂ) := ⟨by exact_mod_cast (by omega : k ≠ 0)⟩
    have hlp : Continuous (fun v : ℝ => -conj (linePt (s.im + v))) := by
      have hc : Continuous (fun v : ℝ => linePt (s.im + v)) := by unfold linePt; fun_prop
      exact (Complex.continuous_conj.comp hc).neg
    exact continuous_const.mul ((continuous_const_cpow (k : ℂ)).comp hlp)
  set M_D : ℝ := ∑ k ∈ Finset.Icc ((U + 1) * (V + 1)) K_hi,
    ‖parityClearedVaughanDualBilinear U V k‖
  have hD_bd : ∀ v : ℝ,
      ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖ ≤ M_D := by
    intro v
    unfold balancedBilinearDirichletPoly
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hk1 : 1 ≤ k := (Nat.mul_pos (Nat.succ_pos U) (Nat.succ_pos V)).trans_le (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hk_le1 : ‖(k : ℂ) ^ (-conj (linePt (s.im + v)))‖ ≤ 1 := by
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos hk_pos,
        show (-conj (linePt (s.im + v))).re = -(1 / 2 : ℝ) by
          rw [conj_linePt]; simp [linePt_re]; norm_num]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk1) (by norm_num)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hk_le1
  have hmom_int : Integrable (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ))) *
      ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) := by
    have hcont : Continuous (fun v : ℝ => Real.exp (-(v ^ (2 : ℕ))) *
        ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) :=
      (Real.continuous_exp.comp (by fun_prop)).mul hD_cont.norm
    refine Integrable.mono' (hgauss_int.const_mul M_D) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hD_bd v) (Real.exp_nonneg _)).trans_eq (mul_comm _ _)
  have hsub_eq :
      balancedDualBilinearBandSum U V K_hi s x +
        zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ v : ℝ,
          (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
            zetaChi (linePt (s.im + v)) *
            balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v))) := by
    rw [balancedDualBilinearBandSum_eq_zetaFree_offLine_add_criticalLine U V K_hi hx hs0 hhi]
    ring
  rw [hsub_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  set C_pref : ℝ := x ^ a * (Real.exp (1 / 4) / a)
  have hpt : ∀ v : ℝ,
      ‖(x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
          smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
          zetaChi (linePt (s.im + v)) *
          balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖ ≤
        C_pref * (Real.exp (-(v ^ (2 : ℕ))) *
          ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) := by
    intro v
    have hx_eq : ‖(x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)‖ = x ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp [a]
    have hker : ‖smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤
        (Real.exp (1 / 4) / a) * Real.exp (-(v ^ (2 : ℕ))) := by
      have hk := norm_smoothAFEGaussianKernel_vertical_le ha_pos v
      have hexp_a : Real.exp (a ^ (2 : ℕ)) ≤ Real.exp (1 / 4) := by
        refine Real.exp_le_exp.mpr ?_
        have hsq : a ^ (2 : ℕ) ≤ (1 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ ha_pos.le ha_lt_half.le 2
        linarith
      dsimp only [a] at hk ⊢
      exact hk.trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hexp_a ha_pos.le) (Real.exp_nonneg _))
    rw [norm_mul, norm_mul, norm_mul, hx_eq, norm_zetaChi_line (s.im + v), mul_one]
    calc x ^ a * ‖smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I)‖ *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖
        ≤ x ^ a * ((Real.exp (1 / 4) / a) * Real.exp (-(v ^ (2 : ℕ)))) *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hker (by positivity)) (norm_nonneg _)
      _ = C_pref * (Real.exp (-(v ^ (2 : ℕ))) *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) := by
          dsimp only [C_pref]; ring
  have hint_le := norm_integral_le_of_norm_le (hmom_int.const_mul C_pref)
    (Filter.Eventually.of_forall hpt)
  rw [MeasureTheory.integral_const_mul] at hint_le
  calc (1 / (2 * Real.pi)) *
          ‖∫ v : ℝ,
            (x : ℂ) ^ (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              smoothAFEGaussianKernel (((1 / 2 - s.re : ℝ) : ℂ) + (v : ℂ) * I) *
              zetaChi (linePt (s.im + v)) *
              balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖
      ≤ (1 / (2 * Real.pi)) *
          (C_pref * ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) *
          ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖ := by
        dsimp only [C_pref, a]
        set I_v : ℝ := ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
          ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖
        calc (1 / (2 * Real.pi)) * (x ^ (1 / 2 - s.re) * (Real.exp (1 / 4) / (1 / 2 - s.re)) * I_v)
            = ((1 / (2 * Real.pi)) * (Real.exp (1 / 4) / (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) * I_v := by ring
          _ = (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) * I_v := by
              rw [div_mul_div_comm, one_mul]

/-- **Disjunctive `ζ`-free balanced bilinear Dirichlet-polynomial forcing and `HasStrictPrimeGasWitness`
production across ALL of `Ω_open`:**
given `exists_balancedDualBilinearBand_duality_on_remaining_strip`, at **every** point
`s ∈ Ω_open` (`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`) and for **all** `1 ≤ U, V` with
`U * V ≤ |Im s|^{η - 1 / 2}`, setting `K_hi = ⌈|Im s|^{2 + η + δ}⌉₊`:
1. If `ζ(s) = 0`, then **either** the off-line pure unweighted Dirichlet polynomial satisfies
   `1 / 8 < ‖balancedBilinearDirichletPoly U V K_hi (1 - s)‖` (`Re(1 - s) > 1 / 2`), **or**
   the Gaussian-localized critical-line moment of
   `‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (Im s + v)))‖` exceeds
   `(2 * π * (1 / 2 - Re s) / exp(1 / 4)) * |Im s|^{(1 + η)(1/2 - Re s)} * ((1 / 8) * (|Im s| / 7)^{1/2 - Re s} - C_band * |Im s|^{-1 / 4})`.
2. Conversely, whenever **both** pure unweighted Dirichlet polynomial quantities do not exceed
   those explicit thresholds, `s` admits an unconditional `HasStrictPrimeGasWitness`. -/
theorem zetaFree_balancedBilinearDirichletPoly_disjunctive_forcing_and_witness_on_remaining_strip
    {η δ C_band : ℝ}
    (hband : ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
      let x : ℝ := |s.im| ^ (-(1 + η))
      let Y : ℝ := |s.im| ^ (3 + η)
      let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
      ∀ {U V : ℕ}, 1 ≤ U → 1 ≤ V → ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2) →
        ‖(riemannZeta s * smoothOuterMoebiusSeries Y (1 - s) -
            (1 - (2 : ℂ) ^ (-(1 - s))) * riemannZeta s *
              smoothOuterVaughanTypeIISeries U V Y (1 - s)) -
          ((1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s +
            balancedDualBilinearBandSum U V K_hi s x)‖ ≤
          C_band * |s.im| ^ (-(1 / 4 : ℝ)))
    {s : ℂ} (hlo : 3001 / 24000 ≤ s.re) (hhi : s.re < 1 / 2) (him : 184 < |s.im|)
    {U V : ℕ} (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV_bd : ((U * V : ℕ) : ℝ) ≤ |s.im| ^ (η - 1 / 2)) :
    let K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
    let thresh_line : ℝ :=
      (2 * Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
        |s.im| ^ ((1 + η) * (1 / 2 - s.re)) *
        ((1 / 8 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ)))
    (riemannZeta s = 0 →
      (1 / 8 : ℝ) < ‖balancedBilinearDirichletPoly U V K_hi (1 - s)‖ ∨
        thresh_line <
          ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
            ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) ∧
    (∀ {L_hor : ℝ}, 0 < L_hor →
      ‖balancedBilinearDirichletPoly U V K_hi (1 - s)‖ ≤ 1 / 8 →
      (∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
        ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖) ≤ thresh_line →
      HasStrictPrimeGasWitness s (by linarith) L_hor) := by
  dsimp only
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have hτ_pos : 0 < |s.im| := by linarith
  have ha_pos : 0 < 1 / 2 - s.re := by linarith
  set x : ℝ := |s.im| ^ (-(1 + η))
  set K_hi : ℕ := Nat.ceil (|s.im| ^ (2 + η + δ))
  have hx_pos : 0 < x := Real.rpow_pos_of_pos hτ_pos _
  have hpref := one_quarter_lt_norm_one_sub_two_cpow_neg_one_sub hhi
  obtain ⟨_, _, hchi_ge⟩ := norm_zetaChi_ge_rpow_above_oneHundredEightyFour hs0 hhi him
  have hchi_pos : 0 < ‖zetaChi s‖ := lt_of_lt_of_le (by positivity) hchi_ge
  have hmom := norm_balancedDualBilinearBandSum_add_zetaChi_mul_dirPoly_le U V K_hi hx_pos hs0 hhi
  set M_D : ℝ := ∫ v : ℝ, Real.exp (-(v ^ (2 : ℕ))) *
    ‖balancedBilinearDirichletPoly U V K_hi (conj (linePt (s.im + v)))‖
  set K_pos : ℝ := (2 * Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
    |s.im| ^ ((1 + η) * (1 / 2 - s.re))
  have hK_pos : 0 < K_pos := by dsimp only [K_pos]; positivity
  have hKx_cancel :
      K_pos * ((Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re)) = 1 := by
    have hx_pow : x ^ (1 / 2 - s.re) = |s.im| ^ (-((1 + η) * (1 / 2 - s.re))) := by
      dsimp only [x]; rw [← Real.rpow_mul hτ_pos.le]; congr 1; ring
    have hrpow_inv :
        |s.im| ^ ((1 + η) * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re))) = 1 := by
      rw [← Real.rpow_add hτ_pos, add_neg_cancel, Real.rpow_zero]
    have h2pi_a_ne : 2 * Real.pi * (1 / 2 - s.re) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ha_pos.ne'
    have hexp_ne : Real.exp (1 / 4) ≠ 0 := (Real.exp_pos _).ne'
    have hprod1 :
        (2 * Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
          (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) = 1 := by
      rw [div_mul_div_comm, mul_comm (Real.exp (1 / 4)) (2 * Real.pi * (1 / 2 - s.re))]
      exact div_self (mul_ne_zero h2pi_a_ne hexp_ne)
    dsimp only [K_pos]
    rw [hx_pow]
    calc (2 * Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) * |s.im| ^ ((1 + η) * (1 / 2 - s.re)) *
            (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re))))
        = ((2 * Real.pi * (1 / 2 - s.re) / Real.exp (1 / 4)) *
            (Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re)))) *
            (|s.im| ^ ((1 + η) * (1 / 2 - s.re)) * |s.im| ^ (-((1 + η) * (1 / 2 - s.re)))) := by ring
      _ = 1 * 1 := by rw [hprod1, hrpow_inv]
      _ = 1 := mul_one 1
  -- Key contradiction if `ζ(s) = 0` AND both bounds hold simultaneously.
  have hcontra :
      riemannZeta s = 0 →
      ‖balancedBilinearDirichletPoly U V K_hi (1 - s)‖ ≤ 1 / 8 →
      M_D ≤ K_pos * ((1 / 8 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ))) →
      False := by
    intro hζ0 hD_le hM_le
    have herr := hband s hlo hhi him hU1 hV1 hUV_bd
    rw [hζ0, zero_mul, mul_zero, zero_mul, sub_zero, zero_sub, norm_neg] at herr
    -- Rewrite `(1 - 2^{-(1 - s)}) * zetaChi s + balancedDualBilinearBandSum` via `balancedDualBilinearBandSum + zetaChi s * D`.
    have hsplit_vac :
        (1 - (2 : ℂ) ^ (-(1 - s))) * zetaChi s + balancedDualBilinearBandSum U V K_hi s x =
          zetaChi s * ((1 - (2 : ℂ) ^ (-(1 - s))) - balancedBilinearDirichletPoly U V K_hi (1 - s)) +
            (balancedDualBilinearBandSum U V K_hi s x +
              zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)) := by ring
    rw [hsplit_vac] at herr
    have hlow1 :
        (1 / 8 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) <
          ‖zetaChi s * ((1 - (2 : ℂ) ^ (-(1 - s))) -
            balancedBilinearDirichletPoly U V K_hi (1 - s))‖ := by
      rw [norm_mul]
      have hdiff_gt : (1 / 8 : ℝ) <
          ‖(1 - (2 : ℂ) ^ (-(1 - s))) - balancedBilinearDirichletPoly U V K_hi (1 - s)‖ := by
        have ht := norm_sub_norm_le (1 - (2 : ℂ) ^ (-(1 - s)))
          (balancedBilinearDirichletPoly U V K_hi (1 - s))
        linarith
      calc (1 / 8 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re)
          ≤ (1 / 8 : ℝ) * ‖zetaChi s‖ := mul_le_mul_of_nonneg_left hchi_ge (by norm_num)
        _ < ‖(1 - (2 : ℂ) ^ (-(1 - s))) - balancedBilinearDirichletPoly U V K_hi (1 - s)‖ *
              ‖zetaChi s‖ := mul_lt_mul_of_pos_right hdiff_gt hchi_pos
        _ = ‖zetaChi s‖ *
              ‖(1 - (2 : ℂ) ^ (-(1 - s))) - balancedBilinearDirichletPoly U V K_hi (1 - s)‖ :=
            mul_comm _ _
    have htri := norm_sub_norm_le
      (zetaChi s * ((1 - (2 : ℂ) ^ (-(1 - s))) - balancedBilinearDirichletPoly U V K_hi (1 - s)))
      (-(balancedDualBilinearBandSum U V K_hi s x +
        zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)))
    rw [sub_neg_eq_add, norm_neg] at htri
    have hrem_gt :
        (1 / 8 : ℝ) * (|s.im| / 7) ^ (1 / 2 - s.re) - C_band * |s.im| ^ (-(1 / 4 : ℝ)) <
          ‖balancedDualBilinearBandSum U V K_hi s x +
            zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)‖ := by
      linarith
    have hK_rem_le_M :
        K_pos * ‖balancedDualBilinearBandSum U V K_hi s x +
            zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)‖ ≤ M_D := by
      calc K_pos * ‖balancedDualBilinearBandSum U V K_hi s x +
              zetaChi s * balancedBilinearDirichletPoly U V K_hi (1 - s)‖
          ≤ K_pos * ((Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re) * M_D) :=
            mul_le_mul_of_nonneg_left hmom hK_pos.le
        _ = (K_pos * ((Real.exp (1 / 4) / (2 * Real.pi * (1 / 2 - s.re))) * x ^ (1 / 2 - s.re))) * M_D := by
            ring
        _ = M_D := by rw [hKx_cancel, one_mul]
    have hstrict := (mul_lt_mul_of_pos_left hrem_gt hK_pos).trans_le hK_rem_le_M
    linarith
  refine ⟨fun hζ0 => ?_, fun {L_hor} hL_hor hD_le hM_le => ?_⟩
  · by_contra hnot
    push Not at hnot
    exact hcontra hζ0 hnot.1 hnot.2
  · refine (hasStrictPrimeGasWitness_iff_zeta_ne_zero hs0 hs1 hL_hor).mpr fun hζ0 => ?_
    exact hcontra hζ0 hD_le hM_le

end Part3ZetaFreeBalancedBilinearReduction

#print axioms abs_vaughanDualBilinear_le_four_mul_divisors_cube
#print axioms norm_parityClearedVaughanDualBilinear_le_eight_mul_divisors_cube
#print axioms smoothAFEZetaDualCoefficientGeneral_zero_eq_neg_zetaChi_add_criticalLine
#print axioms smoothAFEZetaDualCoefficientGeneral_eq_neg_zetaChi_mul_add_criticalLine
#print axioms balancedDualBilinearBandSum_eq_zetaFree_offLine_add_criticalLine
#print axioms norm_balancedDualBilinearBandSum_add_zetaChi_mul_dirPoly_le
#print axioms zetaFree_balancedBilinearDirichletPoly_disjunctive_forcing_and_witness_on_remaining_strip

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
