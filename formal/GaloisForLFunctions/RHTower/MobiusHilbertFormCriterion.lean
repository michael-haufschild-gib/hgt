import GaloisForLFunctions.RHTower.MobiusGammaHankelSubOrthogonality

/-!
# The Möbius Hilbert form and the Riemann hypothesis

The Hilbert matrix `[1/(m+n)]` is the Gamma--Hankel matrix at the boundary exponent `r = 1`.  Its
Möbius quadratic form is

`E_N = Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) = ∫_0^∞ F_N(x)² dx`,   `F_N(x) = Σ_{n ≤ N} μ(n) e^{-nx}`.

**Criterion.**  If `E_N = O_ε((N+1)^ε)` for every `ε > 0`, then the Riemann hypothesis holds.  In
particular **Hilbert sub-orthogonality**, the nonpositivity of the off-diagonal part
`Σ_{m ≠ n ≤ N} μ(m)μ(n)/(m+n) ≤ 0` for every `N`, implies RH, because the diagonal
`Σ_{n ≤ N} μ(n)²/(2n)` is only logarithmic.

The proof converts the single boundary exponent into uniform energy bounds on every line
`r = 2σ > 1`.

* **Tail energy.**  For `0 < y ≤ 1` compare `F_N` with `F_M`, `M = ⌈y^{-2}⌉`.  The difference is
  at most `e^{-(M+1)x}/(1 - e^{-x})`, whose square has mass at most `1` on `(y, ∞)`.  Hence
  `∫_y^∞ F_N² ≤ (2C·3^ε + 2) y^{-2ε}`, uniformly in `N`.
* **Dyadic summation.**  On `(2^{-k-1}, 2^{-k}]` the weight `x^{r-1}` is at most `2^{-k(r-1)}`, so
  the tail bound sums geometrically once `2ε < r - 1`.  Near `0` the weight kills the finite
  energy, and on `(1, ∞)` the pencil is at most `2e^{-x}`.

The uniform bounds feed the Fatou step of the sub-orthogonality module, giving finite Laplace
energy on lines arbitrarily close to `1/2`, hence RH.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

/-- **Subpower growth of the Möbius Hilbert form.** -/
def MobiusHilbertFormSubpower : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
    finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ ε

private theorem shiftedMobiusRealCoefficient_abs_le_one (n : ℕ) :
    |shiftedMobiusRealCoefficient n| ≤ 1 := by
  unfold shiftedMobiusRealCoefficient
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem finiteMobiusLaplacePencil_eq (N : ℕ) (x : ℝ) :
    finiteMobiusLaplacePencil N x =
      ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n * Real.exp (-x) ^ (n + 1) := by
  unfold finiteMobiusLaplacePencil finiteRealLaplacePencil
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **Geometric tail.**  For `M ≤ N` and `x > 0`,
`|F_N(x) - F_M(x)| ≤ e^{-x(M+1)}/(1 - e^{-x})`. -/
theorem abs_finiteMobiusLaplacePencil_sub_le {M N : ℕ} (hMN : M ≤ N) {x : ℝ} (hx : 0 < x) :
    |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ≤
      Real.exp (-x) ^ (M + 1) / (1 - Real.exp (-x)) := by
  set q := Real.exp (-x) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => shiftedMobiusRealCoefficient n * q ^ (n + 1)) hMN
  rw [finiteMobiusLaplacePencil_eq, finiteMobiusLaplacePencil_eq, ← hsplit, add_sub_cancel_left]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ n ∈ Finset.Ico M N,
      |shiftedMobiusRealCoefficient n * q ^ (n + 1)| ≤ q * q ^ n := by
    intro n _
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _), pow_succ, mul_comm (q ^ n) q]
    exact mul_le_of_le_one_left (by positivity) (shiftedMobiusRealCoefficient_abs_le_one n)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  calc q * ∑ n ∈ Finset.Ico M N, q ^ n ≤ q * (q ^ M / (1 - q)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq0 hq1) hq0
    _ = q ^ (M + 1) / (1 - q) := by rw [pow_succ]; ring

theorem finiteMobiusLaplacePencil_zero (x : ℝ) : finiteMobiusLaplacePencil 0 x = 0 := by
  simp [finiteMobiusLaplacePencil, finiteRealLaplacePencil]

theorem abs_finiteMobiusLaplacePencil_le (N : ℕ) {x : ℝ} (hx : 0 < x) :
    |finiteMobiusLaplacePencil N x| ≤ Real.exp (-x) / (1 - Real.exp (-x)) := by
  have h := abs_finiteMobiusLaplacePencil_sub_le (Nat.zero_le N) hx
  rwa [finiteMobiusLaplacePencil_zero, sub_zero, zero_add, pow_one] at h

theorem integrableOn_sq_finiteMobiusLaplacePencil (N : ℕ) :
    IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2) (Ioi 0) := by
  have h := integrableOn_finiteRealLaplacePencil_sq shiftedMobiusRealCoefficient N
    (by norm_num : (0 : ℝ) < 1)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp [finiteMobiusLaplacePencil]

theorem integral_sq_finiteMobiusLaplacePencil (N : ℕ) :
    ∫ x in Ioi 0, finiteMobiusLaplacePencil N x ^ 2 = finiteMobiusGammaHankelEnergy N 1 := by
  have h := integral_finiteMobiusLaplacePencil_sq N (by norm_num : (0 : ℝ) < 1)
  simpa using h

theorem finiteMobiusGammaHankelEnergy_zero (r : ℝ) : finiteMobiusGammaHankelEnergy 0 r = 0 := by
  simp [finiteMobiusGammaHankelEnergy, finiteGammaHankelEnergy]

/-- `e^{-y} ≤ 1 - y/2` on `[0, 1]`. -/
theorem exp_neg_le_one_sub_half {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (-y) ≤ 1 - y / 2 := by
  have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hpos : 0 < 1 + y := by linarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos y)]
  nlinarith

/-- **Tail energy.**  A subpower Hilbert bound controls the energy of every finite pencil beyond
`y`, uniformly in the cutoff. -/
theorem setIntegral_Ioi_sq_finiteMobiusLaplacePencil_le {C ε : ℝ} (hε : 0 < ε)
    (hC : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ ε)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (N : ℕ) :
    ∫ x in Ioi y, finiteMobiusLaplacePencil N x ^ 2 ≤ (2 * C * 3 ^ ε + 2) * y ^ (-(2 * ε)) := by
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    rw [finiteMobiusGammaHankelEnergy_zero] at h0
    simpa using h0
  have hy2 : 0 < y ^ 2 := by positivity
  set Y : ℝ := (y ^ 2)⁻¹ with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef]
    exact one_le_inv₀ hy2 |>.mpr (by nlinarith)
  set M : ℕ := ⌈Y⌉₊ with hMdef
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hM1 : (M : ℝ) + 1 ≤ 3 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y)
    linarith
  have hYpow : Y ^ ε = y ^ (-(2 * ε)) := by
    rw [hYdef, Real.inv_rpow hy2.le, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le,
      Real.rpow_neg hy0.le]
    norm_num
  have hpowM : ((M : ℝ) + 1) ^ ε ≤ 3 ^ ε * y ^ (-(2 * ε)) := by
    calc ((M : ℝ) + 1) ^ ε ≤ (3 * Y) ^ ε := Real.rpow_le_rpow (by positivity) hM1 hε.le
      _ = 3 ^ ε * Y ^ ε := Real.mul_rpow (by norm_num) (by linarith)
      _ = 3 ^ ε * y ^ (-(2 * ε)) := by rw [hYpow]
  have hEM : ∀ N' : ℕ, N' ≤ M →
      finiteMobiusGammaHankelEnergy N' 1 ≤ C * 3 ^ ε * y ^ (-(2 * ε)) := by
    intro N' hN'
    have hN'R : (N' : ℝ) ≤ M := by exact_mod_cast hN'
    calc finiteMobiusGammaHankelEnergy N' 1 ≤ C * ((N' : ℝ) + 1) ^ ε := hC N'
      _ ≤ C * ((M : ℝ) + 1) ^ ε :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) hε.le) hC0
      _ ≤ C * (3 ^ ε * y ^ (-(2 * ε))) := mul_le_mul_of_nonneg_left hpowM hC0
      _ = C * 3 ^ ε * y ^ (-(2 * ε)) := by ring
  have hmono : ∀ N' : ℕ,
      ∫ x in Ioi y, finiteMobiusLaplacePencil N' x ^ 2 ≤ finiteMobiusGammaHankelEnergy N' 1 := by
    intro N'
    rw [← integral_sq_finiteMobiusLaplacePencil]
    exact setIntegral_mono_set (integrableOn_sq_finiteMobiusLaplacePencil N')
      (ae_of_all _ fun x => sq_nonneg _) (Ioi_subset_Ioi hy0.le).eventuallyLE
  have hypow1 : 1 ≤ y ^ (-(2 * ε)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy1 (by linarith)
  have h3 : 0 ≤ (3 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
  have hC3 : 0 ≤ C * 3 ^ ε := mul_nonneg hC0 h3
  rcases le_total N M with hNM | hMN
  · calc ∫ x in Ioi y, finiteMobiusLaplacePencil N x ^ 2
        ≤ finiteMobiusGammaHankelEnergy N 1 := hmono N
      _ ≤ C * 3 ^ ε * y ^ (-(2 * ε)) := hEM N hNM
      _ ≤ (2 * C * 3 ^ ε + 2) * y ^ (-(2 * ε)) := by nlinarith
  · set a : ℝ := 2 * ((M : ℝ) + 1) with ha
    have ha0 : 0 < a := by positivity
    have hpt : ∀ x ∈ Ioi y, finiteMobiusLaplacePencil N x ^ 2 ≤
        2 * finiteMobiusLaplacePencil M x ^ 2 + 2 * ((4 / y ^ 2) * Real.exp (-a * x)) := by
      intro x hx
      have hx0 : 0 < x := lt_trans hy0 hx
      have hD := abs_finiteMobiusLaplacePencil_sub_le hMN hx0
      have hq1 : y / 2 ≤ 1 - Real.exp (-x) := by
        have h1 := exp_neg_le_one_sub_half hy0.le hy1
        have h2 : Real.exp (-x) ≤ Real.exp (-y) :=
          Real.exp_le_exp.mpr (by linarith [(show y < x from hx)])
        linarith
      have h1 : |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ≤
          Real.exp (-x) ^ (M + 1) / (y / 2) :=
        hD.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hq1)
      have hexp : (Real.exp (-x) ^ (M + 1)) ^ 2 = Real.exp (-a * x) := by
        rw [← pow_mul, ← Real.exp_nat_mul]
        congr 1
        rw [ha]
        push_cast
        ring
      have hDsq : (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) ^ 2 ≤
          (4 / y ^ 2) * Real.exp (-a * x) := by
        calc (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) ^ 2
            = |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ^ 2 :=
              (sq_abs _).symm
          _ ≤ (Real.exp (-x) ^ (M + 1) / (y / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = (4 / y ^ 2) * Real.exp (-a * x) := by
              rw [div_pow, hexp]
              field_simp
              ring
      nlinarith [sq_nonneg (finiteMobiusLaplacePencil M x -
        (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x))]
    have hint_maj : IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi y) :=
      exp_neg_integrableOn_Ioi y ha0
    have hintM : IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil M x ^ 2) (Ioi y) :=
      (integrableOn_sq_finiteMobiusLaplacePencil M).mono_set (Ioi_subset_Ioi hy0.le)
    have hint_lhs : IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2) (Ioi y) :=
      (integrableOn_sq_finiteMobiusLaplacePencil N).mono_set (Ioi_subset_Ioi hy0.le)
    have hint_rhs : IntegrableOn (fun x : ℝ => 2 * finiteMobiusLaplacePencil M x ^ 2 +
        2 * ((4 / y ^ 2) * Real.exp (-a * x))) (Ioi y) :=
      (hintM.const_mul 2).add ((hint_maj.const_mul (4 / y ^ 2)).const_mul 2)
    have hexpint : ∫ x in Ioi y, Real.exp (-a * x) = Real.exp (-a * y) / a := by
      have h := integral_exp_mul_Ioi (a := -a) (by linarith) y
      rw [h]
      field_simp
    have htail : (4 / y ^ 2) * (Real.exp (-a * y) / a) ≤ 1 := by
      have hMy : 1 / y ≤ ((M : ℝ) + 1) * y := by
        have hYy : Y * y = 1 / y := by
          rw [hYdef]
          field_simp
        have : Y * y ≤ ((M : ℝ) + 1) * y := mul_le_mul_of_nonneg_right (by linarith) hy0.le
        linarith
      have hexp1 : Real.exp (-a * y) ≤ Real.exp (-(2 / y)) := by
        apply Real.exp_le_exp.mpr
        rw [ha]
        have : 2 / y = 2 * (1 / y) := by ring
        nlinarith
      have hexp2 : Real.exp (-(2 / y)) ≤ y ^ 2 / 2 := by
        have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / y)
        have hbig : 2 / y ^ 2 ≤ Real.exp (2 / y) := by
          have : (2 / y) ^ 2 / 2 = 2 / y ^ 2 := by field_simp
          have h2y : 0 ≤ 2 / y := by positivity
          nlinarith
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
        calc (y ^ 2 / 2)⁻¹ = 2 / y ^ 2 := by field_simp
          _ ≤ Real.exp (2 / y) := hbig
      have ha2 : 2 ≤ a := by
        rw [ha]
        have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        linarith
      calc (4 / y ^ 2) * (Real.exp (-a * y) / a) ≤ (4 / y ^ 2) * ((y ^ 2 / 2) / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc Real.exp (-a * y) / a ≤ Real.exp (-a * y) / 2 :=
                  div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) ha2
              _ ≤ (y ^ 2 / 2) / 2 := by linarith
        _ = 1 := by field_simp; ring
    calc ∫ x in Ioi y, finiteMobiusLaplacePencil N x ^ 2
        ≤ ∫ x in Ioi y, (2 * finiteMobiusLaplacePencil M x ^ 2 +
            2 * ((4 / y ^ 2) * Real.exp (-a * x))) :=
          setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi hpt
      _ = 2 * (∫ x in Ioi y, finiteMobiusLaplacePencil M x ^ 2) +
            2 * ((4 / y ^ 2) * (Real.exp (-a * y) / a)) := by
          rw [integral_add (hintM.const_mul 2) ((hint_maj.const_mul (4 / y ^ 2)).const_mul 2),
            integral_const_mul, integral_const_mul, integral_const_mul, hexpint]
      _ ≤ 2 * (C * 3 ^ ε * y ^ (-(2 * ε))) + 2 * 1 := by
          have := (hmono M).trans (hEM M le_rfl)
          linarith
      _ ≤ (2 * C * 3 ^ ε + 2) * y ^ (-(2 * ε)) := by nlinarith

/-- On `[1, ∞)` the pencil is at most `2e^{-x}`. -/
theorem sq_finiteMobiusLaplacePencil_le_of_one_le (N : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    finiteMobiusLaplacePencil N x ^ 2 ≤ 4 * Real.exp (-(2 * x)) := by
  have hx0 : 0 < x := by linarith
  have h := abs_finiteMobiusLaplacePencil_le N hx0
  have he : Real.exp (-x) ≤ 1 / 2 := by
    have h1 : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  have hpos := Real.exp_pos (-x)
  have hbound : |finiteMobiusLaplacePencil N x| ≤ 2 * Real.exp (-x) := by
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc finiteMobiusLaplacePencil N x ^ 2 = |finiteMobiusLaplacePencil N x| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * Real.exp (-x)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ = 4 * Real.exp (-(2 * x)) := by
        have he2 : Real.exp (-x) ^ 2 = Real.exp (-(2 * x)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
        rw [mul_pow, he2]
        norm_num

theorem integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil (N : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2) (Ioi 0) :=
  integrableOn_finiteRealLaplacePencil_sq shiftedMobiusRealCoefficient N hr

/-- The far part of the energy. -/
theorem setIntegral_Ioi_one_rpow_mul_sq_pencil_le (N : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      4 * ((1 / 2) ^ r * Real.Gamma r) := by
  have hmaj : IntegrableOn (fun x : ℝ => x ^ (r - 1) * (4 * Real.exp (-(2 * x)))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := r - 1) (p := 1) (b := 2)
      (by linarith) le_rfl (by norm_num)
    refine IntegrableOn.congr_fun (h.const_mul 4) (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    ring_nf
  calc ∫ x in Ioi 1, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
      ≤ ∫ x in Ioi 1, x ^ (r - 1) * (4 * Real.exp (-(2 * x))) := by
        refine setIntegral_mono_on
          ((integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hr).mono_set
            (Ioi_subset_Ioi zero_le_one))
          (hmaj.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi (fun x hx => ?_)
        have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
        exact mul_le_mul_of_nonneg_left (sq_finiteMobiusLaplacePencil_le_of_one_le N hx1)
          (Real.rpow_nonneg (by linarith) _)
    _ ≤ ∫ x in Ioi 0, x ^ (r - 1) * (4 * Real.exp (-(2 * x))) := by
        refine setIntegral_mono_set hmaj ?_ (Ioi_subset_Ioi zero_le_one).eventuallyLE
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (by positivity)
    _ = 4 * ((1 / 2) ^ r * Real.Gamma r) := by
        have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := r) (r := 2) hr (by norm_num)
        rw [← h, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
        ring_nf

/-- One dyadic piece `(u, 2u]` of the weighted energy. -/
theorem intervalIntegral_dyadic_rpow_mul_sq_pencil_le {C ε r : ℝ} (hε : 0 < ε) (hr : 1 < r)
    (hC : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ ε)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (N : ℕ) :
    ∫ x in u..(2 * u), x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      (2 * C * 3 ^ ε + 2) * 2 ^ (r - 1) * u ^ (r - 1 - 2 * ε) := by
  have h2u : u ≤ 2 * u := by linarith
  rw [intervalIntegral.integral_of_le h2u]
  have hsub : Ioc u (2 * u) ⊆ Ioi 0 := fun x hx => lt_trans hu0 hx.1
  have hint := (integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N
    (by linarith : (0 : ℝ) < r)).mono_set hsub
  have hintg : IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2) (Ioc u (2 * u)) :=
    (integrableOn_sq_finiteMobiusLaplacePencil N).mono_set hsub
  have hw : 0 ≤ (2 * u) ^ (r - 1) := Real.rpow_nonneg (by linarith) _
  calc ∫ x in Ioc u (2 * u), x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
      ≤ ∫ x in Ioc u (2 * u), (2 * u) ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_on hint (hintg.const_mul _) measurableSet_Ioc (fun x hx =>
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (le_of_lt (lt_trans hu0 hx.1)) hx.2 (by linarith)) (sq_nonneg _))
    _ = (2 * u) ^ (r - 1) * ∫ x in Ioc u (2 * u), finiteMobiusLaplacePencil N x ^ 2 :=
        integral_const_mul _ _
    _ ≤ (2 * u) ^ (r - 1) * ∫ x in Ioi u, finiteMobiusLaplacePencil N x ^ 2 :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set
          ((integrableOn_sq_finiteMobiusLaplacePencil N).mono_set (Ioi_subset_Ioi hu0.le))
          (ae_of_all _ fun x => sq_nonneg _) Ioc_subset_Ioi_self.eventuallyLE) hw
    _ ≤ (2 * u) ^ (r - 1) * ((2 * C * 3 ^ ε + 2) * u ^ (-(2 * ε))) :=
        mul_le_mul_of_nonneg_left
          (setIntegral_Ioi_sq_finiteMobiusLaplacePencil_le hε hC hu0 hu1 N) hw
    _ = (2 * C * 3 ^ ε + 2) * 2 ^ (r - 1) * u ^ (r - 1 - 2 * ε) := by
        rw [Real.mul_rpow (by norm_num) hu0.le, sub_eq_add_neg (r - 1), Real.rpow_add hu0]
        ring

/-- The part of the weighted energy near `0` is controlled by the Hilbert energy. -/
theorem intervalIntegral_zero_rpow_mul_sq_pencil_le (N : ℕ) {r : ℝ} (hr : 1 < r) {a : ℝ}
    (ha : 0 < a) :
    ∫ x in (0 : ℝ)..a, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      a ^ (r - 1) * finiteMobiusGammaHankelEnergy N 1 := by
  rw [intervalIntegral.integral_of_le ha.le]
  have hsub : Ioc 0 a ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hint := (integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N
    (by linarith : (0 : ℝ) < r)).mono_set hsub
  have hintg : IntegrableOn (fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2) (Ioc 0 a) :=
    (integrableOn_sq_finiteMobiusLaplacePencil N).mono_set hsub
  have hw : 0 ≤ a ^ (r - 1) := Real.rpow_nonneg ha.le _
  calc ∫ x in Ioc 0 a, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2
      ≤ ∫ x in Ioc 0 a, a ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_on hint (hintg.const_mul _) measurableSet_Ioc (fun x hx =>
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1.le hx.2 (by linarith)) (sq_nonneg _))
    _ = a ^ (r - 1) * ∫ x in Ioc 0 a, finiteMobiusLaplacePencil N x ^ 2 := integral_const_mul _ _
    _ ≤ a ^ (r - 1) * ∫ x in Ioi 0, finiteMobiusLaplacePencil N x ^ 2 :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set (integrableOn_sq_finiteMobiusLaplacePencil N)
          (ae_of_all _ fun x => sq_nonneg _) hsub.eventuallyLE) hw
    _ = a ^ (r - 1) * finiteMobiusGammaHankelEnergy N 1 := by
        rw [integral_sq_finiteMobiusLaplacePencil]

theorem sum_range_pow_sub_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (J : ℕ) :
    ∑ k ∈ Finset.range J, ρ ^ (J - k) ≤ ρ / (1 - ρ) := by
  rw [← Finset.sum_range_reflect]
  have hre : ∀ j ∈ Finset.range J, ρ ^ (J - (J - 1 - j)) = ρ * ρ ^ j := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show J - (J - 1 - j) = j + 1 by omega, pow_succ, mul_comm]
  rw [Finset.sum_congr rfl hre, ← Finset.mul_sum, Finset.range_eq_Ico]
  calc ρ * ∑ j ∈ Finset.Ico 0 J, ρ ^ j ≤ ρ * (ρ ^ 0 / (1 - ρ)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hρ0 hρ1) hρ0
    _ = ρ / (1 - ρ) := by rw [pow_zero]; ring

/-- **Uniform energy on every line `r > 1 + 2ε`** from the power bound `E_N ≤ C(N+1)^ε` at the
boundary exponent. -/
theorem exists_forall_finiteMobiusGammaHankelEnergy_le_of_hilbert_power {C ε r : ℝ} (hε : 0 < ε)
    (hC : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * ((N : ℝ) + 1) ^ ε)
    (hr2 : 1 + 2 * ε < r) :
    ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ B := by
  have hr : 1 < r := by linarith
  have hC0 : 0 ≤ C := by
    have h0 := hC 0
    rw [finiteMobiusGammaHankelEnergy_zero] at h0
    simpa using h0
  set K : ℝ := 2 * C * 3 ^ ε + 2 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ (3 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
    rw [hK]
    positivity
  set δ : ℝ := r - 1 - 2 * ε with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set ρ : ℝ := (1 / 2 : ℝ) ^ δ with hρdef
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hδ
  have h2r : 0 ≤ (2 : ℝ) ^ (r - 1) := Real.rpow_nonneg (by norm_num) _
  refine ⟨1 + K * 2 ^ (r - 1) * (ρ / (1 - ρ)) + 4 * ((1 / 2) ^ r * Real.Gamma r), fun N => ?_⟩
  set E1 := finiteMobiusGammaHankelEnergy N 1 with hE1def
  have hE1 : 0 ≤ E1 := finiteMobiusGammaHankelEnergy_nonneg N one_pos
  set θ : ℝ := (1 / 2 : ℝ) ^ (r - 1) with hθdef
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by norm_num) _
  have hθ1 : θ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (E1 + 1) by positivity) hθ1
  set a : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ (J - k) with hadef
  have hapos : ∀ k, 0 < a k := fun k => by rw [hadef]; positivity
  have haJ : a J = 1 := by simp [hadef]
  have hsucc : ∀ k < J, a (k + 1) = 2 * a k := by
    intro k hk
    simp only [hadef]
    rw [show J - k = (J - (k + 1)) + 1 by omega, pow_succ]
    ring
  have hale : ∀ k < J, a k ≤ 1 := fun k _ => by
    rw [hadef]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  set f : ℝ → ℝ := fun x => x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 with hfdef
  have hF : IntegrableOn f (Ioi 0) :=
    integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N (by linarith)
  have hII : ∀ u v : ℝ, 0 ≤ u → u ≤ v → IntervalIntegrable f volume u v := fun u v hu huv =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr
      (hF.mono_set fun x hx => lt_of_le_of_lt hu hx.1)
  have hamono : ∀ k < J, a k ≤ a (k + 1) := fun k hk => by
    rw [hsucc k hk]
    linarith [hapos k]
  have ha01 : a 0 ≤ 1 := by
    rw [hadef]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  -- the three pieces
  have hsplit1 : finiteMobiusGammaHankelEnergy N r =
      (∫ x in Ioc 0 1, f x) + ∫ x in Ioi 1, f x := by
    rw [← integral_finiteMobiusLaplacePencil_sq N (by linarith : (0 : ℝ) < r),
      ← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi zero_le_one))
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume) (a := a)
    (n := J) (fun k hk => hII _ _ (hapos k).le (hamono k hk))
  have hsplit2 : ∫ x in Ioc 0 1, f x =
      (∫ x in (0 : ℝ)..(a 0), f x) + ∑ k ∈ Finset.range J, ∫ x in (a k)..(a (k + 1)), f x := by
    rw [← intervalIntegral.integral_of_le zero_le_one, hsum, haJ,
      intervalIntegral.integral_add_adjacent_intervals (hII 0 (a 0) le_rfl (hapos 0).le)
        (hII (a 0) 1 (hapos 0).le ha01)]
  have hrem : ∫ x in (0 : ℝ)..(a 0), f x ≤ 1 := by
    have h1 := intervalIntegral_zero_rpow_mul_sq_pencil_le N hr (hapos 0)
    have hpow : a 0 ^ (r - 1) = θ ^ J := by
      simp only [hadef, Nat.sub_zero]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    rw [hpow] at h1
    have h2 : θ ^ J * E1 ≤ 1 := by
      have hlt : θ ^ J * E1 ≤ 1 / (E1 + 1) * E1 := mul_le_mul_of_nonneg_right hJ.le hE1
      have : 1 / (E1 + 1) * E1 ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
        linarith
      linarith
    exact h1.trans h2
  have hpieces : ∑ k ∈ Finset.range J, ∫ x in (a k)..(a (k + 1)), f x ≤
      K * 2 ^ (r - 1) * (ρ / (1 - ρ)) := by
    have hterm : ∀ k ∈ Finset.range J, ∫ x in (a k)..(a (k + 1)), f x ≤
        K * 2 ^ (r - 1) * ρ ^ (J - k) := by
      intro k hk
      have hkJ := Finset.mem_range.mp hk
      rw [hsucc k hkJ]
      have h1 := intervalIntegral_dyadic_rpow_mul_sq_pencil_le hε hr hC (hapos k) (hale k hkJ) N
      have hpow : a k ^ (r - 1 - 2 * ε) = ρ ^ (J - k) := by
        rw [← hδdef]
        simp only [hadef]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast]
      rw [hpow] at h1
      exact h1
    calc ∑ k ∈ Finset.range J, ∫ x in (a k)..(a (k + 1)), f x
        ≤ ∑ k ∈ Finset.range J, K * 2 ^ (r - 1) * ρ ^ (J - k) := Finset.sum_le_sum hterm
      _ = K * 2 ^ (r - 1) * ∑ k ∈ Finset.range J, ρ ^ (J - k) := by rw [Finset.mul_sum]
      _ ≤ K * 2 ^ (r - 1) * (ρ / (1 - ρ)) :=
          mul_le_mul_of_nonneg_left (sum_range_pow_sub_le hρ0 hρ1 J) (by positivity)
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N (by linarith : (0 : ℝ) < r)
  rw [hsplit1, hsplit2]
  linarith

/-- **Uniform energy on every line `r > 1`** from subpower growth at the boundary exponent. -/
theorem exists_forall_finiteMobiusGammaHankelEnergy_le_of_hilbertSubpower
    (h : MobiusHilbertFormSubpower) {r : ℝ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ N : ℕ, finiteMobiusGammaHankelEnergy N r ≤ B := by
  obtain ⟨C, hC⟩ := h ((r - 1) / 4) (by linarith)
  exact exists_forall_finiteMobiusGammaHankelEnergy_le_of_hilbert_power (by linarith) hC
    (by linarith)

/-- **Hilbert criterion.**  Subpower growth of the Möbius Hilbert form implies the Riemann
hypothesis. -/
theorem riemannHypothesis_of_mobiusHilbertFormSubpower (h : MobiusHilbertFormSubpower) :
    RiemannHypothesis := by
  apply mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis
  intro ε hε
  refine ⟨1 / 2 + ε / 2, by linarith, by linarith, ?_⟩
  obtain ⟨B, hB⟩ := exists_forall_finiteMobiusGammaHankelEnergy_le_of_hilbertSubpower h
    (r := 2 * (1 / 2 + ε / 2)) (by linarith)
  exact (memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (by linarith) hB).1

/-- The Hilbert diagonal `Σ_{n ≤ N} μ(n)²/(2n)` is at most `(1 + log N)/2`. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_one_le (N : ℕ) :
    finiteMobiusGammaHankelDiagonalEnergy N 1 ≤ (1 + Real.log N) / 2 := by
  unfold finiteMobiusGammaHankelDiagonalEnergy
  rw [Real.Gamma_one, one_mul]
  have hterm : ∀ n ∈ Finset.range N,
      shiftedMobiusRealCoefficient n ^ 2 / (((2 * (n + 1) : ℕ) : ℝ) ^ (1 : ℝ)) ≤
        (1 / 2) * (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n _
    rw [Real.rpow_one]
    have hsq : shiftedMobiusRealCoefficient n ^ 2 ≤ 1 := by
      have := shiftedMobiusRealCoefficient_abs_le_one n
      nlinarith [abs_nonneg (shiftedMobiusRealCoefficient n), sq_abs (shiftedMobiusRealCoefficient n)]
    have hpos : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) := by positivity
    calc shiftedMobiusRealCoefficient n ^ 2 / ((2 * (n + 1) : ℕ) : ℝ)
        ≤ 1 / ((2 * (n + 1) : ℕ) : ℝ) := div_le_div_of_nonneg_right hsq hpos.le
      _ = (1 / 2) * (((n + 1 : ℕ) : ℝ))⁻¹ := by push_cast; field_simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hharm : ∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ))⁻¹ = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun n : ℕ => (((n : ℕ) : ℝ))⁻¹) 0 N 1]
    simp only [zero_add]
    rw [Finset.Ico_add_one_right_eq_Icc]
    push_cast
    rfl
  rw [hharm]
  have := harmonic_le_one_add_log N
  linarith

/-- A logarithm is dominated by every positive power. -/
theorem one_add_log_le_rpow {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    (1 + Real.log N) / 2 ≤ ((1 + 1 / ε) / 2) * ((N : ℝ) + 1) ^ ε := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hpow1 : 1 ≤ ((N : ℝ) + 1) ^ ε := Real.one_le_rpow hN1 hε.le
  have hlog : Real.log N ≤ ((N : ℝ) + 1) ^ ε / ε := by
    have h1 : Real.log N ≤ Real.log ((N : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        simp
      · exact Real.log_le_log (by exact_mod_cast hpos) (by linarith)
    have h2 : ε * Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ ε - 1 := by
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < N + 1) ε)
      rwa [Real.log_rpow (by linarith)] at this
    rw [le_div_iff₀ hε]
    nlinarith
  have hkey : 1 + Real.log N ≤ (1 + 1 / ε) * ((N : ℝ) + 1) ^ ε := by
    have : ((N : ℝ) + 1) ^ ε / ε = (1 / ε) * ((N : ℝ) + 1) ^ ε := by ring
    nlinarith
  linarith

/-- **Hilbert sub-orthogonality implies RH.**  If the off-diagonal Möbius Hilbert form
`Σ_{m ≠ n ≤ N} μ(m)μ(n)/(m+n)` is nonpositive for every `N`, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_mobiusHilbertSubOrthogonal
    (h : ∀ N : ℕ, finiteMobiusGammaHankelOffDiagonalCovariance N 1 ≤ 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_mobiusHilbertFormSubpower
  intro ε hε
  refine ⟨(1 + 1 / ε) / 2, fun N => ?_⟩
  rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
  have h1 := finiteMobiusGammaHankelDiagonalEnergy_one_le N
  have h2 := one_add_log_le_rpow hε N
  linarith [h N]

end RHTower
