import GaloisForLFunctions.RHTower.StripFactorXiDivisibleBlindTest
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindFamily
import GaloisForLFunctions.RHTower.XiHorizontalStripDecay

/-!
# The shifted-Gamma family of `Ξ`-divisible tests

For `j ∈ ℕ` let `Q_j(z) = ∏_{k<j} (k + ¼ + iz/2) = Γ(j + ¼ + iz/2)/Γ(¼ + iz/2)` (`shiftedGammaPoly`)
and `Φ_j = Ξ·Q_j` (`xiShiftedGamma`).  In the variable `s = ½ + iz`,
`Φ_j = (s(s−1)/2) π^{−s/2} Γ(s/2 + j) ζ(s)`: the completed zeta function with its Gamma factor
shifted by `j`.

* `‖Q_j(z)‖ ≤ ∏_{k<j} (k + 1 + |Re z|/2) ≤ 3 · j! (3/2)^j · 3^{|Re z|/2}` on `|Im z| ≤ 3/2`
  (`norm_shiftedGammaPoly_le_factorial`): compare with the integer ceiling `m` of `|Re z|/2`; the
  product is then `j!·C(j+m, j)`, and the binomial theorem for `(2/3 + 1/3)^{j+m}` bounds
  `C(j+m, j) ≤ (3/2)^j 3^m`.
* With the exponential decay of `Ξ` on horizontal lines (rate `3/4`, which exceeds `(log 3)/2`), each
  `Φ_j` is holomorphic on `|Im z| ≤ 3/4` with `‖Φ_j(z)‖ ≤ C_Ξ j! (3/2)^j e^{−ε|Re z|}`,
  `ε = 3/4 − (log 3)/2 > 0`, with one constant `C_Ξ` for all `j` (`exists_stripDecay_xiShiftedGamma`).
* The strip tests `F_j` with `F̂_j = Φ_j` (`xiShiftedGammaTest`) therefore satisfy uniform decay
  bounds `|F_j|, |F_j'| ≤ C_Ξ' j! (3/2)^j e^{−(3/4)|x|}` (`exists_decayBound_xiShiftedGammaTest`).
  Their Fourier transforms vanish at every nontrivial zero of `ζ`, `F̂_0 = Ξ` vanishes on the real
  line only at critical ordinates, and `(F_j ⋆ F̃_j)(y) = (1/2π) ∫ Ξ(r)² |Q_j(r)|² cos(ry) dr`.

These are the members of the family `(N1)` of `WeilConeXiDivisibleBlindFamily` attached to a
spectral density `Σ_j w_j |Q_j|²`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate Nat
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-- `Q_j(z) = ∏_{k<j} (k + ¼ + iz/2)`. -/
def shiftedGammaPoly (j : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range j, ((k : ℂ) + 1 / 4 + I * z / 2)

/-- `Φ_j = Ξ·Q_j`. -/
def xiShiftedGamma (j : ℕ) (z : ℂ) : ℂ := RHTower.XiC z * shiftedGammaPoly j z

theorem norm_shiftedGammaPoly_factor_le (k : ℕ) {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    ‖(k : ℂ) + 1 / 4 + I * z / 2‖ ≤ (k : ℝ) + 1 + |z.re| / 2 := by
  have e : (k : ℂ) + 1 / 4 + I * z / 2 =
      (((k : ℝ) + 1 / 4 - z.im / 2 : ℝ) : ℂ) + ((z.re / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.mul_re]; ring
    · simp [Complex.mul_im]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : |(k : ℝ) + 1 / 4 - z.im / 2| ≤ (k : ℝ) + 1 := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp hz |>.1, abs_le.mp hz |>.2]
  linarith

theorem norm_shiftedGammaPoly_le (j : ℕ) {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    ‖shiftedGammaPoly j z‖ ≤ ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + |z.re| / 2) := by
  unfold shiftedGammaPoly
  rw [norm_prod]
  exact Finset.prod_le_prod (fun k _ => norm_nonneg _)
    fun k _ => norm_shiftedGammaPoly_factor_le k hz

/-- `C(n, j) ≤ (3/2)^j 3^{n−j}`, from `(2/3 + 1/3)^n = 1`. -/
theorem choose_le_three_halves_pow (n j : ℕ) (hj : j ≤ n) :
    (n.choose j : ℝ) ≤ (3 / 2 : ℝ) ^ j * 3 ^ (n - j) := by
  have hsum := add_pow (2 / 3 : ℝ) (1 / 3) n
  have h1 : (2 / 3 : ℝ) + 1 / 3 = 1 := by norm_num
  have hterm : (2 / 3 : ℝ) ^ j * (1 / 3) ^ (n - j) * (n.choose j) ≤ 1 := by
    have hle := Finset.single_le_sum
      (f := fun m => (2 / 3 : ℝ) ^ m * (1 / 3) ^ (n - m) * (n.choose m))
      (fun m _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    rw [← hsum, h1, one_pow] at hle
    exact hle
  have hpos : (0 : ℝ) < (2 / 3 : ℝ) ^ j * (1 / 3) ^ (n - j) := by positivity
  have e : (3 / 2 : ℝ) ^ j * 3 ^ (n - j) = ((2 / 3 : ℝ) ^ j * (1 / 3) ^ (n - j))⁻¹ := by
    rw [mul_inv, ← inv_pow, ← inv_pow]; norm_num
  rw [e, le_inv_comm₀ (by exact_mod_cast Nat.choose_pos hj) hpos]
  rw [mul_comm] at hterm
  calc (2 / 3 : ℝ) ^ j * (1 / 3) ^ (n - j) = ((n.choose j : ℝ))⁻¹ *
        ((n.choose j : ℝ) * ((2 / 3 : ℝ) ^ j * (1 / 3) ^ (n - j))) := by
          have : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
          field_simp
    _ ≤ ((n.choose j : ℝ))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- `∏_{k<j} (k + 1 + m) = j! · C(j + m, j)` for natural `m`. -/
theorem prod_range_add_natCast (j m : ℕ) :
    ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + m) = (j ! : ℝ) * ((j + m).choose j : ℝ) := by
  have h1 : ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + m) = ((m + 1).ascFactorial j : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  have h2 := Nat.factorial_mul_ascFactorial m j
  have h3 := Nat.add_choose_mul_factorial_mul_factorial m j
  rw [h1]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have e : ((m + 1).ascFactorial j : ℝ) * m ! = (j ! : ℝ) * ((j + m).choose j : ℝ) * m ! := by
    have h2' : (m ! : ℝ) * ((m + 1).ascFactorial j : ℝ) = ((m + j)! : ℝ) := by exact_mod_cast h2
    have h3' : (((m + j).choose j : ℕ) : ℝ) * (m ! : ℝ) * (j ! : ℝ) = ((m + j)! : ℝ) := by
      exact_mod_cast h3
    rw [add_comm j m]
    nlinarith [h2', h3']
  exact mul_right_cancel₀ hm e

/-- **The factorial–exponential bound** `∏_{k<j} (k + 1 + t) ≤ 3 · j! (3/2)^j 3^t`, `t ≥ 0`. -/
theorem prod_range_add_le_factorial_exp {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + t) ≤
      3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 * t) := by
  set m := ⌈t⌉₊ with hm
  have htm : t ≤ m := Nat.le_ceil t
  have hmt : (m : ℝ) < t + 1 := Nat.ceil_lt_add_one ht
  have h1 : ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + t) ≤ ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + m) :=
    Finset.prod_le_prod (fun k _ => by positivity) fun k _ => by linarith
  rw [prod_range_add_natCast] at h1
  have h2 := choose_le_three_halves_pow (j + m) j (by omega)
  rw [show j + m - j = m by omega] at h2
  have h3 : (3 : ℝ) ^ m ≤ 3 * Real.exp (Real.log 3 * t) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    calc Real.exp (Real.log 3 * m) ≤ Real.exp (Real.log 3 * (t + 1)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmt.le (Real.log_nonneg (by norm_num)))
      _ = 3 * Real.exp (Real.log 3 * t) := by
          rw [mul_add, mul_one, Real.exp_add, Real.exp_log (by norm_num)]; ring
  calc ∏ k ∈ Finset.range j, ((k : ℝ) + 1 + t) ≤ (j ! : ℝ) * ((j + m).choose j : ℝ) := h1
    _ ≤ (j ! : ℝ) * ((3 / 2 : ℝ) ^ j * 3 ^ m) := by gcongr
    _ ≤ (j ! : ℝ) * ((3 / 2 : ℝ) ^ j * (3 * Real.exp (Real.log 3 * t))) := by gcongr
    _ = _ := by ring

theorem norm_shiftedGammaPoly_le_factorial (j : ℕ) {z : ℂ} (hz : |z.im| ≤ 3 / 2) :
    ‖shiftedGammaPoly j z‖ ≤
      3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 / 2 * |z.re|) := by
  refine (norm_shiftedGammaPoly_le j hz).trans ?_
  have h := prod_range_add_le_factorial_exp (t := |z.re| / 2) (by positivity) j
  refine h.trans (le_of_eq ?_)
  congr 2
  ring

/-- The decay rate `3/4 − (log 3)/2` of the family. -/
def xiShiftedGammaRate : ℝ := 3 / 4 - Real.log 3 / 2

theorem xiShiftedGammaRate_pos : 0 < xiShiftedGammaRate := by
  unfold xiShiftedGammaRate
  have h : Real.log 3 < 3 / 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (x := 3 / 2) (by norm_num)
    linarith
  linarith

/-- **Uniform strip decay of the shifted-Gamma family.** -/
theorem exists_stripDecay_xiShiftedGamma :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      StripDecay (xiShiftedGamma j) (3 / 4) xiShiftedGammaRate
        (C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) := by
  have hpi : 2 * (3 / 4 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨CΞ, hCΞ, hΞ⟩ := RHTower.exists_norm_XiC_horizontal_le (A := 3 / 4) (δ := 3 / 4)
    (by norm_num) (by norm_num) hpi
  refine ⟨3 * CΞ, by positivity, fun j => ⟨fun z _ => ?_, fun z hz => ?_⟩⟩
  · unfold xiShiftedGamma shiftedGammaPoly
    exact (RHTower.XiC_differentiable z).mul (by fun_prop)
  · have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have hX : ‖RHTower.XiC z‖ ≤ CΞ * Real.exp (-(3 / 4 * |z.re|)) := by
      have := hΞ z.re z.im hz
      rwa [← hz'] at this
    have hQ := norm_shiftedGammaPoly_le_factorial j (z := z) (by linarith)
    unfold xiShiftedGamma
    rw [norm_mul]
    have hJ : 0 ≤ (j ! : ℝ) * (3 / 2 : ℝ) ^ j := by positivity
    calc ‖RHTower.XiC z‖ * ‖shiftedGammaPoly j z‖ ≤
        (CΞ * Real.exp (-(3 / 4 * |z.re|))) *
          (3 * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) * Real.exp (Real.log 3 / 2 * |z.re|)) :=
          mul_le_mul hX hQ (norm_nonneg _) (by positivity)
      _ = 3 * CΞ * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) *
            (Real.exp (-(3 / 4 * |z.re|)) * Real.exp (Real.log 3 / 2 * |z.re|)) := by ring
      _ = 3 * CΞ * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) *
            Real.exp (-(xiShiftedGammaRate * |z.re|)) := by
          rw [← Real.exp_add]; unfold xiShiftedGammaRate; ring_nf

/-- Reality: `Φ_j(−r) = conj Φ_j(r)` on the real line. -/
theorem xiShiftedGamma_neg_ofReal (j : ℕ) (r : ℝ) :
    xiShiftedGamma j (-(r : ℂ)) = conj (xiShiftedGamma j r) := by
  unfold xiShiftedGamma shiftedGammaPoly
  rw [map_mul, map_prod, RHTower.XiC_even, ← RHTower.XiC_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_add, map_natCast, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-! ### The strip tests -/

/-- The decay constant `(∫ e^{−ε|r|} + (2/ε + b) ∫ e^{−ε|r|/2}) / 2π` of a strip test. -/
def stripDecayConst (b ε : ℝ) : ℝ :=
  ((∫ r : ℝ, Real.exp (-(ε * |r|))) + (2 / ε + b) * ∫ r : ℝ, Real.exp (-(ε / 2 * |r|))) /
    (2 * Real.pi)

theorem stripDecayConst_nonneg {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) : 0 ≤ stripDecayConst b ε := by
  unfold stripDecayConst
  have h1 : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
  have h2 : 0 ≤ ∫ r : ℝ, Real.exp (-(ε / 2 * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
  positivity

/-- **Explicit decay bounds for a strip test**, linear in the strip constant. -/
theorem decayBound_stripTest {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 1 / 2 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) : DecayBound (stripTest Φ) (b - 1 / 2) (C * stripDecayConst b ε) := by
  have hb0 : 0 ≤ b := by linarith
  have hC := hΦ.const_nonneg hb0
  have hΦ1 := hΦ.neg_I_mul_id hb0 hε
  have h1 : 0 ≤ ∫ r : ℝ, Real.exp (-(ε * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
  have h2 : 0 ≤ ∫ r : ℝ, Real.exp (-(ε / 2 * |r|)) := integral_nonneg fun r => (Real.exp_pos _).le
  have hpi : 0 < 2 * Real.pi := by positivity
  refine ⟨contDiff_stripTest hb0 hε hΦ, mul_nonneg hC (stripDecayConst_nonneg hb0 hε),
    fun x => ⟨?_, ?_⟩⟩
  · rw [show 1 / 2 + (b - 1 / 2) = b by ring]
    calc |stripTest Φ x| ≤ ‖stripInvFT Φ x‖ := Complex.abs_re_le_norm _
      _ ≤ C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) * Real.exp (-(b * |x|)) :=
          norm_stripInvFT_le hb0 hε hΦ x
      _ ≤ C * stripDecayConst b ε * Real.exp (-(b * |x|)) := by
          gcongr
          unfold stripDecayConst
          rw [mul_div_assoc]
          gcongr
          have : 0 ≤ (2 / ε + b) * ∫ r : ℝ, Real.exp (-(ε / 2 * |r|)) := by positivity
          linarith
  · rw [show 1 / 2 + (b - 1 / 2) = b by ring, deriv_stripTest hb0 hε hΦ]
    calc |(stripInvFT (fun z => -I * z * Φ z) x).re| ≤ ‖stripInvFT (fun z => -I * z * Φ z) x‖ :=
          Complex.abs_re_le_norm _
      _ ≤ C * (2 / ε + b) * (∫ r : ℝ, Real.exp (-(ε / 2 * |r|))) / (2 * Real.pi) *
            Real.exp (-(b * |x|)) := norm_stripInvFT_le hb0 (half_pos hε) hΦ1 x
      _ ≤ C * stripDecayConst b ε * Real.exp (-(b * |x|)) := by
          gcongr
          unfold stripDecayConst
          rw [mul_assoc, mul_div_assoc]
          gcongr
          linarith

/-- The test `F_j` with `F̂_j = Ξ·Q_j`. -/
def xiShiftedGammaTest (j : ℕ) : ℝ → ℝ := stripTest (xiShiftedGamma j)

/-- **Uniform decay bounds for the shifted-Gamma tests:** `|F_j|, |F_j'| ≤ C j! (3/2)^j e^{−(3/4)|x|}`. -/
theorem exists_decayBound_xiShiftedGammaTest :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      DecayBound (xiShiftedGammaTest j) (1 / 4) (C * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j)) := by
  obtain ⟨C, hC, hj⟩ := exists_stripDecay_xiShiftedGamma
  have hK := stripDecayConst_nonneg (b := 3 / 4) (by norm_num) xiShiftedGammaRate_pos
  refine ⟨C * stripDecayConst (3 / 4) xiShiftedGammaRate, mul_nonneg hC hK, fun j => ?_⟩
  have h := decayBound_stripTest (by norm_num) xiShiftedGammaRate_pos (hj j)
  rw [show (3 / 4 : ℝ) - 1 / 2 = 1 / 4 by norm_num] at h
  unfold xiShiftedGammaTest
  convert h using 1
  ring

theorem paperFT_xiShiftedGammaTest (j : ℕ) {z : ℂ} (hz : |z.im| < 3 / 4) :
    Zeta23.paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) z = xiShiftedGamma j z := by
  obtain ⟨C, -, hj⟩ := exists_stripDecay_xiShiftedGamma
  exact paperFT_stripTest (by norm_num) xiShiftedGammaRate_pos (hj j)
    (xiShiftedGamma_neg_ofReal j) hz

/-- Every `F̂_j` vanishes at the spectral point of every nontrivial zero of `ζ`. -/
theorem paperFT_xiShiftedGammaTest_gammaOf (j : ℕ) (ρ : zetaZeroConfig.carrier) :
    Zeta23.paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (Zeta23.gammaOf ρ) = 0 := by
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(Zeta23.gammaOf (ρ : ℂ)).im| < 1 / 2 :=
    WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  rw [paperFT_xiShiftedGammaTest j (by linarith)]
  have hpt : (1 / 2 : ℂ) + Zeta23.gammaOf (ρ : ℂ) * I = ρ := by
    unfold Zeta23.gammaOf
    field_simp
    ring
  have hne : (ρ : ℂ) ≠ 1 := by
    intro h
    have := hmem.2.2
    rw [h, Complex.one_re] at this
    exact lt_irrefl 1 this
  have hxi : RHTower.xi (ρ : ℂ) = 0 := (RHTower.xi_eq_zero_iff hmem.2.1 hne).mpr hmem.1
  unfold xiShiftedGamma
  rw [show RHTower.XiC (Zeta23.gammaOf (ρ : ℂ)) = RHTower.xi (ρ : ℂ) by
    rw [RHTower.XiC, hpt], hxi, zero_mul]

/-- `F̂_0 = Ξ` vanishes on the real line only at critical ordinates. -/
theorem riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero {r : ℝ}
    (hr : Zeta23.paperFT (fun u => (xiShiftedGammaTest 0 u : ℂ)) r = 0) :
    riemannZeta ((1 / 2 : ℂ) + r * I) = 0 := by
  rw [paperFT_xiShiftedGammaTest 0 (by simp)] at hr
  have hX : RHTower.XiC r = 0 := by simpa [xiShiftedGamma, shiftedGammaPoly] using hr
  have hre : 0 < ((1 / 2 : ℂ) + r * I).re := by simp
  have hne : (1 / 2 : ℂ) + r * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact (RHTower.xi_eq_zero_iff hre hne).mp hX

/-- `(F_j ⋆ F̃_j)(y) = (1/2π) ∫ |Ξ(r) Q_j(r)|² cos(ry) dr`. -/
theorem crossCorr_xiShiftedGammaTest (j : ℕ) (y : ℝ) :
    crossCorr (xiShiftedGammaTest j) (xiShiftedGammaTest j) y =
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * y) := by
  obtain ⟨C, -, hj⟩ := exists_stripDecay_xiShiftedGamma
  exact crossCorr_stripTest (by norm_num) xiShiftedGammaRate_pos (hj j)
    (xiShiftedGamma_neg_ofReal j) y

/-! ### (N1) for the shifted-Gamma dictionary -/

/-- **RH is prime-blind positivity as soon as the shifted-Gamma dictionary carries a blind positive
combination.**  Let `w_j ≥ 0` with `w_0 > 0` and `Σ_j w_j (j!)² (9/4)^j < ∞`.  If for every `n ≥ 2`

`Σ_j w_j ∫ |Ξ(r) Q_j(r)|² cos(r log n) dr = 0`,

then RH is equivalent to prime-blind positivity.  This is a linear condition on `w` in the cone
of nonnegative sequences: (N1) in this dictionary is a conic feasibility problem. -/
theorem riemannHypothesis_iff_primeBlindPositive_of_shiftedGamma_weights {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hw0 : 0 < w 0)
    (hsum : Summable fun j => w j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2)
    (hblind : ∀ n : ℕ, 2 ≤ n →
      ∑' j, w j * ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n) = 0) :
    RiemannHypothesis ↔ WeilOneSided.PrimeBlindPositive := by
  obtain ⟨C, hC, hF⟩ := exists_decayBound_xiShiftedGammaTest
  refine riemannHypothesis_iff_primeBlindPositive_of_xiDivisibleBlindFamily (by norm_num : (0 : ℝ) < 1 / 4)
    hF hw ?_ (fun j ρ => paperFT_xiShiftedGammaTest_gammaOf j ρ) ?_ hw0
    (fun r hr => riemannZeta_eq_zero_of_paperFT_xiShiftedGammaTest_zero hr)
  · refine (hsum.mul_left (C ^ 2)).congr fun j => ?_
    ring
  · intro n hn
    simp_rw [crossCorr_xiShiftedGammaTest]
    have e : ∀ j, w j * (1 / (2 * Real.pi) *
        ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) =
        1 / (2 * Real.pi) * (w j *
          ∫ r : ℝ, ‖xiShiftedGamma j r‖ ^ 2 * Real.cos (r * Real.log n)) := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, hblind n hn, mul_zero]

end RHTower.WeilSpectral
