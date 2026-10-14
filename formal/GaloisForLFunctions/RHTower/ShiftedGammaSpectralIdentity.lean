import GaloisForLFunctions.RHTower.XiShiftedGammaFamily
import GaloisForLFunctions.RHTower.TwistedArcMomentN1Reduction
import GaloisForLFunctions.RHTower.DivisorTransferAbscissa

/-!
# The arc spectrum in the shifted-Gamma dictionary

On the critical line the archimedean factor `G(s) = s(s−1)Γ_ℝ(s)/2` of `ξ` and the shifted-Gamma
polynomials `Q_j(τ) = ∏_{k<j}(k + ¼ + iτ/2)` combine with the cosine transforms
`C_j(τ) = ∫ cos(τv)(cosh v)^{−1/2−2j} dv` as

`|G(½+iτ)|² |Q_j(τ)|² = λ_j (¼ + τ²)² C_j(τ)`,  `λ_j = π^{−1/2} Γ(½+2j) 2^{1/2−2j} / 4`
(`norm_archXi_sq_mul_norm_shiftedGammaPoly_sq`),

because `C_j(τ) = 2^{2j−1/2} |Γ(¼ + j + iτ/2)|² / Γ(½ + 2j)` (`integral_cos_mul_cosh_rpow_neg_eq`) and
`Γ(¼ + j + iτ/2) = Γ(¼ + iτ/2) Q_j(τ)`.  With `C(−½, 2j) = Γ(2j + ½)/(√π (2j)!)`
(`ringChoose_neg_half_eq`), the arc spectrum
`(¼+τ²)² Σ_j 2 C(−½, 2j) C_j(τ) m_j` of a weighted twisted arc witness becomes

`|G(½+iτ)|² Σ_j w_j |Q_j(τ)|²`,  `w_j = 4√2 · 4^j m_j / (2j)!`   (`arcGammaWeight`).

For an arc density with `|m_j| ≤ 4^{−j} M` the weights satisfy
`w_j (j!)² (9/4)^j ≤ 4√2 M (2j+1) (9/16)^j`, which is summable (`summable_arcGammaWeight`).
-/

open Complex MeasureTheory
open scoped Nat ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

/-- `∫ cos(τ v) (cosh v)^{−s} dv = 2^{s−1} |Γ((s + iτ)/2)|² / Γ(s)`. -/
theorem integral_cos_mul_cosh_rpow_neg_eq {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    ∫ v : ℝ, Real.cos (τ * v) * Real.cosh v ^ (-s) =
      (2 : ℝ) ^ (s - 1) * ‖Complex.Gamma (((s : ℂ) + (τ : ℂ) * I) / 2)‖ ^ 2 / Real.Gamma s := by
  have h := GaloisForLFunctions.HTGeometry.integral_cosh_rpow_neg_mul_cexp_complex hs
    (z := (τ : ℂ)) (by simpa using hs)
  have hint : Integrable (fun v : ℝ => (((Real.cosh v) ^ (-s) : ℝ) : ℂ) *
      Complex.exp (-((τ : ℂ) * (v : ℂ)) * I)) := by
    by_contra hni
    rw [integral_undef hni] at h
    have hG : Complex.Gamma (((s : ℂ) - (τ : ℂ) * I) / 2) *
        Complex.Gamma (((s : ℂ) + (τ : ℂ) * I) / 2) / Complex.Gamma (s : ℂ) ≠ 0 := by
      refine div_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> apply Complex.Gamma_ne_zero <;> intro m hm
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
      · have := congrArg Complex.re hm; simp at this; nlinarith [m.cast_nonneg (α := ℝ)]
    have h2 : ((2 : ℝ) ^ (s - 1) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
    exact absurd h.symm (mul_ne_zero (by exact_mod_cast h2) hG)
  have hcos0 : (fun v : ℝ => ((((Real.cosh v) ^ (-s) : ℝ) : ℂ) *
      Complex.exp (-((τ : ℂ) * (v : ℂ)) * I)).re) =
      fun v => Real.cos (τ * v) * Real.cosh v ^ (-s) := by
    funext v
    rw [show -((τ : ℂ) * (v : ℂ)) * I = ((-(τ * v) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    ring
  have hkey : ∫ v : ℝ, Real.cos (τ * v) * Real.cosh v ^ (-s) =
      (((2 : ℝ) ^ (s - 1) : ℝ) * (Complex.Gamma (((s : ℂ) - (τ : ℂ) * I) / 2) *
        Complex.Gamma (((s : ℂ) + (τ : ℂ) * I) / 2) / Complex.Gamma (s : ℂ))).re := by
    rw [← h, ← hcos0]
    exact integral_re hint
  rw [hkey]
  set w : ℂ := ((s : ℂ) + (τ : ℂ) * I) / 2 with hw
  have hconj : ((s : ℂ) - (τ : ℂ) * I) / 2 = conj w := by
    rw [hw, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    ring
  rw [hconj, Complex.Gamma_conj, Complex.Gamma_ofReal, Complex.conj_mul']
  rw [show (‖Complex.Gamma w‖ : ℂ) ^ 2 = ((‖Complex.Gamma w‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- `Γ(w + j) = Γ(w) ∏_{k<j} (w + k)` for `Re w > 0`. -/
theorem Gamma_add_nat_eq_mul_prod {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    Complex.Gamma (w + j) = Complex.Gamma w * ∏ k ∈ Finset.range j, (w + k) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hne : w + j ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    rw [Finset.prod_range_succ, show w + ((j + 1 : ℕ) : ℂ) = (w + j) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hne, ih]
    ring

theorem shiftedGammaPoly_ofReal_eq_prod (j : ℕ) (τ : ℝ) :
    shiftedGammaPoly j τ = ∏ k ∈ Finset.range j, ((1 / 4 + (τ : ℂ) * I / 2) + k) := by
  unfold shiftedGammaPoly
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

/-- `|Γ(¼ + j + iτ/2)| = |Γ(¼ + iτ/2)| |Q_j(τ)|`. -/
theorem norm_Gamma_shift_eq (j : ℕ) (τ : ℝ) :
    ‖Complex.Gamma ((1 / 4 + (τ : ℂ) * I / 2) + j)‖ =
      ‖Complex.Gamma (1 / 4 + (τ : ℂ) * I / 2)‖ * ‖shiftedGammaPoly j τ‖ := by
  have hre : 0 < (1 / 4 + (τ : ℂ) * I / 2).re := by norm_num
  rw [Gamma_add_nat_eq_mul_prod hre j, norm_mul, shiftedGammaPoly_ofReal_eq_prod]

/-- `|G(½ + iτ)|² = ((¼ + τ²)²/4) π^{−1/2} |Γ(¼ + iτ/2)|²`. -/
theorem norm_archXi_criticalLine_sq (τ : ℝ) :
    ‖ExactNullDivisorTransfer.archXi (1 / 2 + (τ : ℂ) * I)‖ ^ 2 =
      (1 / 4 + τ ^ 2) ^ 2 / 4 * Real.pi ^ (-(1 / 2 : ℝ)) *
        ‖Complex.Gamma (1 / 4 + (τ : ℂ) * I / 2)‖ ^ 2 := by
  unfold ExactNullDivisorTransfer.archXi
  rw [Complex.Gammaℝ_def, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : ‖(1 / 2 + (τ : ℂ) * I) * (1 / 2 + (τ : ℂ) * I - 1) / 2‖ = (1 / 4 + τ ^ 2) / 2 := by
    have e : (1 / 2 + (τ : ℂ) * I) * (1 / 2 + (τ : ℂ) * I - 1) / 2 =
        ((-(1 / 4 + τ ^ 2) / 2 : ℝ) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by nlinarith [sq_nonneg τ])]
    ring
  have h2 : (-(1 / 2 + (τ : ℂ) * I) / 2).re = -(1 / 4) := by simp; norm_num
  have h3 : (1 / 2 + (τ : ℂ) * I) / 2 = 1 / 4 + (τ : ℂ) * I / 2 := by ring
  rw [h1, h2, h3, mul_pow, mul_pow]
  have h4 : (Real.pi ^ (-(1 / 4) : ℝ)) ^ 2 = Real.pi ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    norm_num
  rw [h4]
  ring

/-- **The spectral identity of the shifted-Gamma dictionary.** -/
theorem norm_archXi_sq_mul_norm_shiftedGammaPoly_sq (j : ℕ) (τ : ℝ) :
    ‖ExactNullDivisorTransfer.archXi (1 / 2 + (τ : ℂ) * I)‖ ^ 2 * ‖shiftedGammaPoly j τ‖ ^ 2 =
      Real.pi ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2 + 2 * j) /
        (4 * (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1)) *
        ((1 / 4 + τ ^ 2) ^ 2 * coshPowerTransform j τ) := by
  have hs : (0 : ℝ) < 1 / 2 + 2 * j := by positivity
  have hC : coshPowerTransform j τ = (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1) *
      ‖Complex.Gamma ((1 / 4 + (τ : ℂ) * I / 2) + j)‖ ^ 2 / Real.Gamma (1 / 2 + 2 * j) := by
    unfold coshPowerTransform
    rw [integral_cos_mul_cosh_rpow_neg_eq hs τ]
    congr 3
    push_cast
    ring_nf
  rw [hC, norm_Gamma_shift_eq, norm_archXi_criticalLine_sq]
  have hG : 0 < Real.Gamma (1 / 2 + 2 * j) := Real.Gamma_pos_of_pos hs
  have hP : 0 < (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1) := Real.rpow_pos_of_pos two_pos _
  field_simp

/-! ### Binomial coefficients and weights -/

/-- `C(−½, n) = (−1)^n Γ(n + ½)/(√π n!)`. -/
theorem ringChoose_neg_half_eq (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n = (-1) ^ n * Real.Gamma (n + 1 / 2) / (Real.sqrt Real.pi * n !) := by
  induction n with
  | zero =>
    simp only [Ring.choose_zero_right, pow_zero, Nat.cast_zero, zero_add, Nat.factorial_zero,
      Nat.cast_one, mul_one, one_mul]
    rw [Real.Gamma_one_half_eq, div_self (Real.sqrt_pos.mpr Real.pi_pos).ne']
  | succ n ih =>
    rw [GaloisForLFunctions.HTGeometry.ringChoose_succ_real, ih, Nat.factorial_succ,
      show ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity)]
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hf : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
    push_cast
    field_simp
    ring

/-- `C(−½, 2j) = Γ(2j + ½)/(√π (2j)!)`. -/
theorem ringChoose_neg_half_even_eq (j : ℕ) :
    Ring.choose (-1 / 2 : ℝ) (2 * j) = Real.Gamma (2 * j + 1 / 2) / (Real.sqrt Real.pi * (2 * j)!) := by
  rw [ringChoose_neg_half_eq, pow_mul, neg_one_sq, one_pow, one_mul]
  push_cast
  ring_nf

/-- The weight `w_j = 4√2 · 4^j m / (2j)!` of the shifted-Gamma dictionary. -/
def arcGammaWeight (m : ℝ) (j : ℕ) : ℝ := 4 * Real.sqrt 2 * 4 ^ j * m / (2 * j)!

/-- `w_j λ_j = 2 C(−½, 2j) m`. -/
theorem arcGammaWeight_mul_lambda (m : ℝ) (j : ℕ) :
    arcGammaWeight m j * (Real.pi ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2 + 2 * j) /
      (4 * (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1))) = 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * m := by
  rw [ringChoose_neg_half_even_eq, arcGammaWeight]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hf : (0 : ℝ) < (2 * j)! := by exact_mod_cast Nat.factorial_pos _
  have hP : 0 < (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1) := Real.rpow_pos_of_pos two_pos _
  have h1 : Real.pi ^ (-(1 / 2 : ℝ)) = (Real.sqrt Real.pi)⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg Real.pi_pos.le]
  have h2 : (4 : ℝ) ^ j = Real.sqrt 2 * (2 : ℝ) ^ ((1 / 2 + 2 * j : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add two_pos,
      show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [h1, h2, show 1 / 2 + 2 * (j : ℝ) = 2 * j + 1 / 2 by ring]
  field_simp
  rw [sq, h3]

theorem arcGammaWeight_nonneg {m : ℝ} (hm : 0 ≤ m) (j : ℕ) : 0 ≤ arcGammaWeight m j := by
  unfold arcGammaWeight; positivity

/-- `(j!)² 4^j ≤ (2j+1) (2j)!`. -/
theorem factorial_sq_mul_four_pow_le (j : ℕ) :
    ((j ! : ℝ)) ^ 2 * 4 ^ j ≤ (2 * j + 1) * (2 * j)! := by
  have h := Nat.four_pow_le_two_mul_add_one_mul_central_binom j
  have hc : (2 * j).choose j * j ! * j ! = (2 * j)! := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 2 * j) (k := j) (by omega)
    rwa [show 2 * j - j = j by omega] at this
  have h' : ((4 : ℕ) ^ j : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) * ((2 * j).choose j : ℝ) := by exact_mod_cast h
  have hc' : (((2 * j).choose j : ℕ) : ℝ) * (j ! : ℝ) * (j ! : ℝ) = ((2 * j)! : ℝ) := by
    exact_mod_cast hc
  have hf : (0 : ℝ) ≤ (j ! : ℝ) := by positivity
  push_cast at h' hc'
  calc ((j ! : ℝ)) ^ 2 * 4 ^ j ≤ ((j ! : ℝ)) ^ 2 * ((2 * j + 1) * ((2 * j).choose j : ℝ)) :=
        mul_le_mul_of_nonneg_left h' (sq_nonneg _)
    _ = (2 * j + 1) * (((2 * j).choose j : ℝ) * (j ! : ℝ) * (j ! : ℝ)) := by ring
    _ = (2 * j + 1) * (2 * j)! := by rw [hc']

/-- **Summability of the arc weights** in the growth class of `XiShiftedGammaFamily`. -/
theorem summable_arcGammaWeight {m : ℕ → ℝ} {M : ℝ} (hm : ∀ j, 0 ≤ m j)
    (hM : ∀ j, m j ≤ M * (1 / 4 : ℝ) ^ j) :
    Summable fun j => arcGammaWeight (m j) j * ((j ! : ℝ) * (3 / 2 : ℝ) ^ j) ^ 2 := by
  have hM0 : 0 ≤ M := by
    have := (hm 0).trans (hM 0); simpa using this
  have hgeo : Summable fun j : ℕ => (j : ℝ) * (9 / 16 : ℝ) ^ j :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (9 / 16 : ℝ)) (by norm_num)).congr
      fun j => by simp
  have hgeo0 : Summable fun j : ℕ => (9 / 16 : ℝ) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable fun j : ℕ => 4 * Real.sqrt 2 * M * ((2 * j + 1) * (9 / 16 : ℝ) ^ j) := by
    refine Summable.mul_left _ ?_
    have := (hgeo.mul_left 2).add hgeo0
    refine this.congr fun j => ?_
    ring
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum
  · exact mul_nonneg (arcGammaWeight_nonneg (hm j) j) (sq_nonneg _)
  · unfold arcGammaWeight
    have hf : (0 : ℝ) < (2 * j)! := by exact_mod_cast Nat.factorial_pos _
    have hfs := factorial_sq_mul_four_pow_le j
    have h4 : (4 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
    have h9 : ((3 / 2 : ℝ) ^ j) ^ 2 = (9 / 4 : ℝ) ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h916 : (9 / 4 : ℝ) ^ j = 4 ^ j * (9 / 16 : ℝ) ^ j := by rw [← mul_pow]; norm_num
    rw [div_mul_eq_mul_div, div_le_iff₀ hf, mul_pow, h9]
    have hmj := hM j
    have hs2 : 0 ≤ 4 * Real.sqrt 2 := by positivity
    calc 4 * Real.sqrt 2 * 4 ^ j * m j * ((j ! : ℝ) ^ 2 * (9 / 4 : ℝ) ^ j) ≤
        4 * Real.sqrt 2 * 4 ^ j * (M * (1 / 4 : ℝ) ^ j) * ((j ! : ℝ) ^ 2 * (9 / 4 : ℝ) ^ j) := by
          gcongr
      _ = 4 * Real.sqrt 2 * M * (9 / 16 : ℝ) ^ j * ((j ! : ℝ) ^ 2 * 4 ^ j) *
            ((4 : ℝ) ^ j * (1 / 4 : ℝ) ^ j) := by rw [h916]; ring
      _ = 4 * Real.sqrt 2 * M * (9 / 16 : ℝ) ^ j * ((j ! : ℝ) ^ 2 * 4 ^ j) := by
          rw [h4, mul_one]
      _ ≤ 4 * Real.sqrt 2 * M * (9 / 16 : ℝ) ^ j * ((2 * j + 1) * (2 * j)!) := by
          gcongr
      _ = _ := by ring

end RHTower.WeilSpectral
