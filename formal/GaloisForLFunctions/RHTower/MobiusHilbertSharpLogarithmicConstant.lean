import GaloisForLFunctions.RHTower.MobiusHilbertLogarithmicOmega

/-!
# The sharp logarithmic constant of the Möbius Hilbert form

Let `E_N = Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) = ∫_0^∞ F_N²`, with `F_N(x) = Σ_{n ≤ N} μ(n) e^{−nx}`.

**Theorem** (`sum_normSq_gamma_div_deriv_zeta_le_of_hilbert_log`). Suppose
`E_N ≤ c log(N+1) + C` for every `N`. Then every zero `½ + iγ` of `ζ` on the critical line is
simple, and every finite set `S` of such ordinates satisfies
`Σ_{γ ∈ S} |Γ(½+iγ)|² / |ζ'(½+iγ)|² ≤ c`.

Equivalently (`exists_hilbert_gt_log_of_lt_sum`): if some finite set of critical zeros has
`Σ |Γ/ζ'|² > c`, then `E_N > c log(N+1) + C` for some `N`, for every `C`. Under RH and simple
zeros the expected asymptotic is `E_N ∼ (Σ_ρ |Γ(ρ)/ζ'(ρ)|²) log N`, since the log-mean of
`x F(x)²` is the Parseval sum of the residues `Γ(ρ)/ζ'(ρ)`. So the constant is sharp.

* **Lossless tail.** Compare `F_N` with `F_M` for `M ≈ (3 + 2 log(1/y))/y`. On `[y, 1]` they
  differ by at most `2`, and `log M = (1 + o(1)) log(1/y)`. With `(a+b)² ≤ (1+η)a² + (1+1/η)b²`
  this gives `∫_y^1 F_N² ≤ (1+η)² c log(1/y) + O_η(1)`
  (`intervalIntegral_sq_pencil_le_of_hilbert_log_sharp`).
* **Line energy.** The layer cake and Fatou give `∫ |Γ/ζ|²(½+r+it) dt ≤ π(1+η)²c/r + O_η(1)`
  (`mobiusMellin_line_le_of_tail`).
* **Local floor.** Near a critical zero `ρ`, `|Γ(s)/ζ(s)| ≥ K/|s − ρ|` for every
  `K < |Γ(ρ)|/|ζ'(ρ)|`, and for every `K` if `ζ'(ρ) = 0` (`exists_floor_near_zero`).
* **Windows.** `∫_{|t−γ| ≤ δ} K²/(r² + (t−γ)²) dt ≥ K²(π/r − 2/δ)`. Disjoint windows add up
  (`sum_sq_le_of_line_bound`). Letting `r → 0`, `η → 0` and `K ↑ |Γ(ρ)/ζ'(ρ)|` gives the theorem.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## Elementary inequalities -/

/-- `log(1 + x) ≤ ηx + log(1/η)` for `0 < η ≤ 1`, `x ≥ 0`. -/
theorem log_one_add_le_mul_add_log_inv {η x : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ η * x + Real.log η⁻¹ := by
  have h := Real.log_le_sub_one_of_pos (show 0 < η * (1 + x) by positivity)
  rw [Real.log_mul hη.ne' (by positivity)] at h
  rw [Real.log_inv]
  nlinarith

/-- `(a + b)² ≤ (1 + η)a² + (1 + η⁻¹)b²` for `η > 0`. -/
theorem sq_add_le_one_add_mul_sq {a b η : ℝ} (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2 := by
  have h1 : 0 ≤ (η * a - b) ^ 2 / η := by positivity
  have h2 : (η * a - b) ^ 2 / η = η * a ^ 2 - 2 * a * b + η⁻¹ * b ^ 2 := by
    field_simp; ring
  nlinarith

/-- `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_id_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := integral_one_div_one_add_sq (a := 0) (b := x)
  rw [Real.arctan_zero, sub_zero] at h
  rw [← h]
  have hle : ∫ t in (0 : ℝ)..x, 1 / (1 + t ^ 2) ≤ ∫ _t in (0 : ℝ)..x, (1 : ℝ) := by
    refine intervalIntegral.integral_mono_on hx ?_ intervalIntegrable_const fun t _ => ?_
    · exact (continuous_const.div (continuous_const.add (continuous_pow 2))
        fun t => (by positivity : (0 : ℝ) < 1 + t ^ 2).ne').intervalIntegrable _ _
    · rw [div_le_one (by positivity)]; nlinarith [sq_nonneg t]
  simpa using hle

/-! ## The lossless logarithmic tail -/

/-- **Lossless tail.** A logarithmic Hilbert bound `E_N ≤ c log(N+1) + C` gives, for every
`0 < η ≤ 1` and uniformly in `N`, `∫_y^1 F_N² ≤ (1+η)² c log(1/y) + B_η`. -/
theorem intervalIntegral_sq_pencil_le_of_hilbert_log_sharp {c C η : ℝ} (hc : 0 ≤ c)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) (N : ℕ) :
    ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
      (1 + η) ^ 2 * c * (-Real.log y) +
        ((1 + η) * (c * (Real.log 5 + Real.log η⁻¹) + C) + 4 * (1 + η⁻¹)) := by
  have hC : 0 ≤ C := by
    have h0 := hH 0
    rw [finiteMobiusGammaHankelEnergy_zero] at h0
    simpa using h0
  set L : ℝ := -Real.log y with hL
  have hL0 : 0 ≤ L := by
    have := Real.log_nonpos hy0.le hy1
    linarith
  have hK0 : 0 ≤ Real.log 5 + Real.log η⁻¹ := by
    have h5 := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    have hi := Real.log_nonneg (one_le_inv₀ hη |>.mpr hη1)
    linarith
  set Y : ℝ := (3 + 2 * L) / y with hYdef
  have hY0 : 0 ≤ Y := by positivity
  set M : ℕ := ⌈Y⌉₊ with hMdef
  have hYM : Y ≤ (M : ℝ) := Nat.le_ceil Y
  have hM1 : (M : ℝ) + 1 ≤ (5 + 2 * L) / y := by
    have h1 := Nat.ceil_lt_add_one hY0
    have h2 : 2 ≤ 2 / y := by rw [le_div_iff₀ hy0]; linarith
    have h3 : (5 + 2 * L) / y = Y + 2 / y := by rw [hYdef]; field_simp; ring
    rw [h3]
    linarith
  have hlogM : Real.log ((M : ℝ) + 1) ≤ (1 + η) * L + (Real.log 5 + Real.log η⁻¹) := by
    have h := Real.log_le_log (by positivity) hM1
    rw [Real.log_div (by positivity) hy0.ne'] at h
    have h5 : Real.log (5 + 2 * L) ≤ Real.log 5 + η * L + Real.log η⁻¹ := by
      have e : 5 + 2 * L = 5 * (1 + 2 / 5 * L) := by ring
      rw [e, Real.log_mul (by norm_num) (by positivity)]
      have := log_one_add_le_mul_add_log_inv hη hη1 (show 0 ≤ 2 / 5 * L by positivity)
      nlinarith
    linarith
  have hcM := mul_le_mul_of_nonneg_left hlogM hc
  rcases le_or_gt N M with hNM | hMN
  · have h1 := intervalIntegral_sq_pencil_le_energy N hy0 hy1
    have h2 := hH N
    have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hNM 1)
    have h4 := mul_le_mul_of_nonneg_left h3 hc
    have hη2 : (1 + η) * L ≤ (1 + η) ^ 2 * L := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + η) hη.le) hL0]
    have h5 := mul_le_mul_of_nonneg_left hη2 hc
    have h6 : c * (Real.log 5 + Real.log η⁻¹) + C ≤
        (1 + η) * (c * (Real.log 5 + Real.log η⁻¹) + C) := by
      have : 0 ≤ c * (Real.log 5 + Real.log η⁻¹) + C := by positivity
      nlinarith
    have h7 : 0 ≤ 4 * (1 + η⁻¹) := by positivity
    nlinarith
  · have hpt : ∀ x ∈ Icc y 1, finiteMobiusLaplacePencil N x ^ 2 ≤
        (1 + η) * finiteMobiusLaplacePencil M x ^ 2 + (1 + η⁻¹) * 4 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hy0 hx.1
      have hdiff := abs_finiteMobiusLaplacePencil_sub_le hMN.le hx0
      have hden : x / 2 ≤ 1 - Real.exp (-x) := by
        have := exp_neg_le_one_sub_half hx0.le hx.2
        linarith
      have hnum : Real.exp (-x) ^ (M + 1) ≤ y ^ 2 := by
        rw [← Real.exp_nat_mul]
        have hge : 3 + 2 * L ≤ ((M + 1 : ℕ) : ℝ) * x := by
          push_cast
          have hYy : Y * y = 3 + 2 * L := by rw [hYdef]; field_simp
          calc 3 + 2 * L = Y * y := hYy.symm
            _ ≤ ((M : ℝ) + 1) * x := mul_le_mul (by linarith) hx.1 hy0.le (by positivity)
        have hy2 : Real.exp (-(2 * L)) = y ^ 2 := by
          rw [hL, show -(2 * -Real.log y) = 2 * Real.log y by ring,
            show 2 * Real.log y = Real.log (y ^ 2) by rw [Real.log_pow]; push_cast; ring,
            Real.exp_log (by positivity)]
        calc Real.exp (((M + 1 : ℕ) : ℝ) * -x) ≤ Real.exp (-(2 * L)) :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = y ^ 2 := hy2
      have hbound : |finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x| ≤ 2 := by
        refine hdiff.trans ?_
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hx.1]
      have hsq : (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) ^ 2 ≤ 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x)]
      have key := sq_add_le_one_add_mul_sq (a := finiteMobiusLaplacePencil M x)
        (b := finiteMobiusLaplacePencil N x - finiteMobiusLaplacePencil M x) hη
      rw [add_sub_cancel] at key
      have hi : 0 ≤ 1 + η⁻¹ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq hi]
    have hcontN := continuous_finiteMobiusLaplacePencil N
    have hcontM := continuous_finiteMobiusLaplacePencil M
    have hc2 : Continuous fun x : ℝ => (1 + η) * finiteMobiusLaplacePencil M x ^ 2 :=
      continuous_const.mul (hcontM.pow 2)
    have hmono : ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤
        ∫ x in y..1, ((1 + η) * finiteMobiusLaplacePencil M x ^ 2 + (1 + η⁻¹) * 4) :=
      intervalIntegral.integral_mono_on hy1 ((hcontN.pow 2).intervalIntegrable _ _)
        ((hc2.add continuous_const).intervalIntegrable _ _) hpt
    have heval : ∫ x in y..1, ((1 + η) * finiteMobiusLaplacePencil M x ^ 2 + (1 + η⁻¹) * 4) =
        (1 + η) * (∫ x in y..1, finiteMobiusLaplacePencil M x ^ 2) + (1 - y) * ((1 + η⁻¹) * 4) := by
      rw [intervalIntegral.integral_add (hc2.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    have hM := intervalIntegral_sq_pencil_le_energy M hy0 hy1
    have hHM := hH M
    have hη0 : 0 ≤ 1 + η := by linarith
    have hfin : (1 - y) * ((1 + η⁻¹) * 4) ≤ 4 * (1 + η⁻¹) := by
      have : 0 ≤ (1 + η⁻¹) * 4 := by positivity
      nlinarith
    have hEM : ∫ x in y..1, finiteMobiusLaplacePencil M x ^ 2 ≤
        c * ((1 + η) * L + (Real.log 5 + Real.log η⁻¹)) + C := by linarith
    have hmul := mul_le_mul_of_nonneg_left hEM hη0
    have e : (1 + η) * (c * ((1 + η) * L + (Real.log 5 + Real.log η⁻¹)) + C) =
        (1 + η) ^ 2 * c * L + (1 + η) * (c * (Real.log 5 + Real.log η⁻¹) + C) := by ring
    linarith

/-! ## From the tail to the line energy -/

/-- A logarithmic tail bound `∫_y^1 F_N² ≤ A log(1/y) + B` gives `E_N(1+2r) ≤ A/(2r) + B + 4`. -/
theorem finiteMobiusGammaHankelEnergy_le_of_tail {A B : ℝ} (hA : 0 ≤ A)
    (htail : ∀ N : ℕ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤ A * (-Real.log y) + B)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) (N : ℕ) :
    finiteMobiusGammaHankelEnergy N (1 + 2 * r) ≤ A / (2 * r) + B + 4 := by
  have hpos : 0 < 1 + 2 * r := by linarith
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hpos
  rw [← integral_finiteMobiusLaplacePencil_sq N hpos,
    ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hInt.mono_set Ioc_subset_Ioi_self) (hInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hfar := setIntegral_Ioi_one_rpow_mul_sq_pencil_le N hpos
  have hfar4 : 4 * ((1 / 2) ^ (1 + 2 * r) * Real.Gamma (1 + 2 * r)) ≤ 4 := by
    have hG := gamma_le_one_of_mem_Icc (by linarith : (1 : ℝ) ≤ 1 + 2 * r) (by linarith)
    have hG0 : 0 ≤ Real.Gamma (1 + 2 * r) := (Real.Gamma_pos_of_pos hpos).le
    have hh : (1 / 2 : ℝ) ^ (1 + 2 * r) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) hpos.le
    have hh0 : 0 ≤ (1 / 2 : ℝ) ^ (1 + 2 * r) := Real.rpow_nonneg (by norm_num) _
    nlinarith
  have hexp : (1 + 2 * r) - 1 = 2 * r := by ring
  have hcont : Continuous fun x : ℝ => finiteMobiusLaplacePencil N x ^ 2 :=
    (continuous_finiteMobiusLaplacePencil N).pow 2
  have hnear : ∫ x in Ioc (0 : ℝ) 1, x ^ ((1 + 2 * r) - 1) * finiteMobiusLaplacePencil N x ^ 2 ≤
      A / (2 * r) + B := by
    rw [hexp, ← intervalIntegral.integral_of_le zero_le_one]
    apply le_of_forall_pos_le_add
    intro δ hδ
    set ε : ℝ := min 1 (δ / ((N : ℝ) ^ 2 + 1)) with hεdef
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεδ : ε * ((N : ℝ) ^ 2 + 1) ≤ δ := by
      have := min_le_right 1 (δ / ((N : ℝ) ^ 2 + 1))
      rw [← hεdef] at this
      calc ε * ((N : ℝ) ^ 2 + 1) ≤ δ / ((N : ℝ) ^ 2 + 1) * ((N : ℝ) ^ 2 + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = δ := by field_simp
    have hfcont : ContinuousOn (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        (uIcc 0 1) := fun x _ =>
      ((Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))).mul
        hcont.continuousAt).continuousWithinAt
    have hi1 : IntervalIntegrable (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        volume 0 ε :=
      (hfcont.mono (uIcc_subset_uIcc (by simp) (by simp [hε0.le, hε1]))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun x : ℝ => x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2)
        volume ε 1 :=
      (hfcont.mono (uIcc_subset_uIcc (by simp [hε0.le, hε1]) (by simp))).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hsmall : ∫ x in (0 : ℝ)..ε, x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2 ≤
        ε * ((N : ℝ) ^ 2 + 1) := by
      have hb : ∀ x ∈ Icc (0 : ℝ) ε, x ^ (2 * r) * finiteMobiusLaplacePencil N x ^ 2 ≤
          (N : ℝ) ^ 2 + 1 := by
        intro x hx
        have hx1 : x ≤ 1 := hx.2.trans hε1
        have hp : x ^ (2 * r) ≤ 1 := Real.rpow_le_one hx.1 hx1 (by linarith)
        have hp0 : 0 ≤ x ^ (2 * r) := Real.rpow_nonneg hx.1 _
        have hF := abs_finiteMobiusLaplacePencil_le_card N hx.1
        have hF2 : finiteMobiusLaplacePencil N x ^ 2 ≤ (N : ℝ) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hF 2
        nlinarith [sq_nonneg (finiteMobiusLaplacePencil N x)]
      have := intervalIntegral.integral_mono_on hε0.le hi1 intervalIntegrable_const hb
      rw [intervalIntegral.integral_const] at this
      simpa using this
    have hlayer := intervalIntegral_rpow_mul_le_of_tail_log hcont (A := A) (B := B)
      hA (by linarith : 0 < 2 * r) hε0 hε1
      (fun y hy => htail N y (lt_of_lt_of_le hε0 hy.1) hy.2)
    linarith
  linarith

/-- **Line energy from a logarithmic tail.** Under the tail bound, on `Re s = ½ + r` the Mellin
transform `Γ/ζ` of the Möbius–Laplace source has energy `≤ 2π (A/(2r) + B + 4)`, and the canonical
identity `mellin F · (s−1)ζ(s) = Γ(s)(s−1)` holds on `Re s > ½ + r/2`. -/
theorem mobiusMellin_line_le_of_tail {A B : ℝ} (hA : 0 ≤ A)
    (htail : ∀ N : ℕ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤ A * (-Real.log y) + B)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 2) :
    Integrable (fun t : ℝ =>
        ‖mellin mobiusDiscreteLaplaceTransform (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
      (∫ t : ℝ, ‖mellin mobiusDiscreteLaplaceTransform (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
        ≤ 2 * Real.pi * (A / (2 * r) + B + 4) ∧
      ∀ s : ℂ, 1 / 2 + r / 2 < s.re →
        mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s =
          Complex.Gamma s * (s - 1) := by
  obtain ⟨hbase, -⟩ := memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (sigma := 1 / 2 + r / 2) (B := A / (2 * (r / 2)) + B + 4) (by positivity) fun N => by
      rw [show 2 * (1 / 2 + r / 2) = 1 + 2 * (r / 2) by ring]
      exact finiteMobiusGammaHankelEnergy_le_of_tail hA htail (half_pos hr) (by linarith) N
  obtain ⟨h2, hint⟩ := memLp_and_integral_norm_sq_mobiusLaplaceLogMellinLineSource_le_of_energy_le
    (sigma := 1 / 2 + r) (B := A / (2 * r) + B + 4) (by positivity) fun N => by
      rw [show 2 * (1 / 2 + r) = 1 + 2 * r by ring]
      exact finiteMobiusGammaHankelEnergy_le_of_tail hA htail hr hr1 N
  have h1 : Integrable (mobiusLaplaceLogMellinLineSource (1 / 2 + r)) := by
    have := integrable_mobiusLaplaceLogMellinLineSource_of_base hbase (half_pos hr)
    rwa [show 1 / 2 + r / 2 + r / 2 = 1 / 2 + r by ring] at this
  refine ⟨integrable_norm_sq_mellin_line_of_logMellinLineSource h1 h2, ?_, fun s hs =>
    mellin_mobiusDiscreteLaplaceTransform_mul_zetaResidueUnit_eq_of_base (by positivity) hbase s hs⟩
  rw [integral_norm_sq_mellin_mobiusDiscreteLaplaceTransform_line_eq h1 h2]
  exact mul_le_mul_of_nonneg_left hint (by positivity)

/-! ## The local floor at a critical zero -/

/-- **Local floor.** At a zero `ρ` of `ζ` with `Re ρ > 0`, `ρ ≠ 1`, and for every `K ≥ 0` with
`K |ζ'(ρ)| < |Γ(ρ)|`, there is `δ > 0` with `K |ζ(s)| ≤ |Γ(s)| |s − ρ|` on `|s − ρ| ≤ δ`. -/
theorem exists_floor_near_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρre : 0 < ρ.re)
    (hz : riemannZeta ρ = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K * ‖deriv riemannZeta ρ‖ < ‖Complex.Gamma ρ‖) :
    ∃ δ > 0, ∀ s : ℂ, ‖s - ρ‖ ≤ δ →
      K * ‖riemannZeta s‖ ≤ ‖Complex.Gamma s‖ * ‖s - ρ‖ := by
  set a := ‖Complex.Gamma ρ‖ with ha
  set b := ‖deriv riemannZeta ρ‖ with hb
  set ε := (a - K * b) / (K + 1) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  have hKε : K * (b + ε) + ε = a := by rw [hε]; field_simp; ring
  have hd : HasDerivAt riemannZeta (deriv riemannZeta ρ) ρ :=
    (differentiableAt_riemannZeta hρ1).hasDerivAt
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.bound hε0)
  have hG : ContinuousAt Complex.Gamma ρ := by
    refine (Complex.differentiableAt_Gamma ρ fun m hm => ?_).continuousAt
    have := congrArg Complex.re hm
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.mp hG ε hε0
  refine ⟨min δ₁ δ₂ / 2, by positivity, fun s hs => ?_⟩
  have hsd : dist s ρ ≤ min δ₁ δ₂ / 2 := by rwa [dist_eq_norm]
  have hs1 : dist s ρ < δ₁ := by
    have := min_le_left δ₁ δ₂; linarith
  have hs2 : dist s ρ < δ₂ := by
    have := min_le_right δ₁ δ₂; linarith
  have hζs : ‖riemannZeta s‖ ≤ (b + ε) * ‖s - ρ‖ := by
    have h := h₁ hs1
    rw [hz, sub_zero, smul_eq_mul] at h
    calc ‖riemannZeta s‖ = ‖(riemannZeta s - (s - ρ) * deriv riemannZeta ρ) +
          (s - ρ) * deriv riemannZeta ρ‖ := by ring_nf
      _ ≤ ‖riemannZeta s - (s - ρ) * deriv riemannZeta ρ‖ + ‖(s - ρ) * deriv riemannZeta ρ‖ :=
          norm_add_le _ _
      _ ≤ ε * ‖s - ρ‖ + ‖s - ρ‖ * b := by rw [norm_mul]; linarith
      _ = (b + ε) * ‖s - ρ‖ := by ring
  have hΓs : a - ε ≤ ‖Complex.Gamma s‖ := by
    have h := h₂ hs2
    rw [dist_eq_norm] at h
    have := norm_sub_norm_le (Complex.Gamma ρ) (Complex.Gamma s)
    rw [norm_sub_rev] at this
    linarith
  have hn := norm_nonneg (s - ρ)
  calc K * ‖riemannZeta s‖ ≤ K * ((b + ε) * ‖s - ρ‖) := mul_le_mul_of_nonneg_left hζs hK0
    _ = (K * (b + ε)) * ‖s - ρ‖ := by ring
    _ ≤ (a - ε) * ‖s - ρ‖ := mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ ‖Complex.Gamma s‖ * ‖s - ρ‖ := mul_le_mul_of_nonneg_right hΓs hn

/-! ## Windows -/

/-- `∫_{γ−δ}^{γ+δ} K²/(r² + (t−γ)²) dt = (2K²/r) arctan(δ/r)`. -/
theorem integral_window_eq {r δ K γ : ℝ} (hr : 0 < r) :
    ∫ t in (γ - δ)..(γ + δ), K ^ 2 / (r ^ 2 + (t - γ) ^ 2) =
      2 * K ^ 2 / r * Real.arctan (δ / r) := by
  have e1 : ∀ t : ℝ, K ^ 2 / (r ^ 2 + (t - γ) ^ 2) =
      K ^ 2 / r ^ 2 * (fun u : ℝ => (fun v : ℝ => 1 / (1 + v ^ 2)) (u / r)) (t - γ) := by
    intro t
    simp only
    field_simp
  simp_rw [e1]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => 1 / (1 + (u / r) ^ 2)) γ,
    show γ - δ - γ = -δ by ring, show γ + δ - γ = δ by ring,
    intervalIntegral.integral_comp_div (fun v : ℝ => 1 / (1 + v ^ 2)) hr.ne',
    integral_one_div_one_add_sq, neg_div, Real.arctan_neg, smul_eq_mul]
  field_simp
  ring

/-- `∫_{γ−δ}^{γ+δ} K²/(r² + (t−γ)²) dt ≥ K²(π/r − 2/δ)`. -/
theorem le_integral_window {r δ K γ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    K ^ 2 * (Real.pi / r - 2 / δ) ≤ ∫ t in (γ - δ)..(γ + δ), K ^ 2 / (r ^ 2 + (t - γ) ^ 2) := by
  rw [integral_window_eq hr]
  have h1 : Real.arctan (δ / r) = Real.pi / 2 - Real.arctan (r / δ) := by
    rw [← Real.arctan_inv_of_pos (by positivity), inv_div]
  have h2 := arctan_le_id_of_nonneg (show 0 ≤ r / δ by positivity)
  rw [h1]
  have hK := sq_nonneg K
  have e : 2 * K ^ 2 / r * (Real.pi / 2 - r / δ) = K ^ 2 * (Real.pi / r - 2 / δ) := by
    field_simp
  have hmono : 2 * K ^ 2 / r * (Real.pi / 2 - r / δ) ≤
      2 * K ^ 2 / r * (Real.pi / 2 - Real.arctan (r / δ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- Distinct elements of a finite set of reals are uniformly separated. -/
theorem exists_pos_forall_two_mul_lt_abs_sub (S : Finset ℝ) :
    ∃ δ > 0, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * δ < |a - b| := by
  classical
  set D := (S ×ˢ S).filter (fun p : ℝ × ℝ => p.1 ≠ p.2) with hD
  by_cases hne : D.Nonempty
  · set m := (D.image fun p : ℝ × ℝ => |p.1 - p.2|).min' (hne.image _) with hm
    have hmpos : 0 < m := by
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp
        ((D.image fun p : ℝ × ℝ => |p.1 - p.2|).min'_mem (hne.image _))
      rw [← hm] at hpm
      rw [← hpm]
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
    refine ⟨m / 3, by positivity, fun a ha b hb hab => ?_⟩
    have hmem : (a, b) ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
    have := Finset.min'_le _ _ (Finset.mem_image_of_mem (fun p : ℝ × ℝ => |p.1 - p.2|) hmem)
    rw [← hm] at this
    linarith
  · refine ⟨1, one_pos, fun a ha b hb hab => absurd ⟨(a, b), ?_⟩ hne⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩

/-- A property that is inherited by smaller radii holds with one radius on a finite set. -/
theorem exists_pos_forall_mem_of_antitone (S : Finset ℝ) {P : ℝ → ℝ → Prop}
    (hmono : ∀ γ δ δ', 0 < δ' → δ' ≤ δ → P γ δ → P γ δ')
    (h : ∀ γ ∈ S, ∃ δ > 0, P γ δ) : ∃ δ > 0, ∀ γ ∈ S, P γ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun γ hγ => absurd hγ (Finset.notMem_empty γ)⟩
  | insert a S ha ih =>
    obtain ⟨δ₁, hδ₁, h₁⟩ := ih fun γ hγ => h γ (Finset.mem_insert_of_mem hγ)
    obtain ⟨δ₂, hδ₂, h₂⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun γ hγ => ?_⟩
    rcases Finset.mem_insert.mp hγ with rfl | hγ
    · exact hmono γ δ₂ _ (lt_min hδ₁ hδ₂) (min_le_right _ _) h₂
    · exact hmono γ δ₁ _ (lt_min hδ₁ hδ₂) (min_le_left _ _) (h₁ γ hγ)

/-- **Disjoint windows.** If the energy of `G` on `Re s = ½ + r` is at most `πA/r + B`, and `G` has
a floor `K_γ²/(r² + (t−γ)²)` near each point of a separated finite set `S`, then `Σ K_γ² ≤ A`. -/
theorem sum_sq_le_of_line_bound {G : ℂ → ℂ} {A B : ℝ}
    (hline : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      Integrable (fun t : ℝ => ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
      ∫ t : ℝ, ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ Real.pi * A / r + B)
    (S : Finset ℝ) (K : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 2 * δ < |a - b|)
    (hfloor : ∀ γ ∈ S, ∀ r : ℝ, 0 < r → r < δ → ∀ t : ℝ, |t - γ| ≤ δ →
      K γ ^ 2 ≤ ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (r ^ 2 + (t - γ) ^ 2)) :
    ∑ γ ∈ S, K γ ^ 2 ≤ A := by
  classical
  set Q := ∑ γ ∈ S, K γ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun γ _ => sq_nonneg _
  -- the inequality at every small `r`
  have hkey : ∀ r : ℝ, 0 < r → r < δ → Q * (Real.pi / r - 2 / δ) ≤ Real.pi * A / r + B := by
    intro r hr hrδ
    obtain ⟨hint, hle⟩ := hline r hr (by linarith)
    set f : ℝ → ℝ := fun t => ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hf
    have hf0 : ∀ t, 0 ≤ f t := fun t => sq_nonneg _
    set W : ℝ → Set ℝ := fun γ => Ioc (γ - δ) (γ + δ) with hW
    have hwin : ∀ γ ∈ S, K γ ^ 2 * (Real.pi / r - 2 / δ) ≤ ∫ t in W γ, f t := by
      intro γ hγ
      refine (le_integral_window (K := K γ) (γ := γ) hr hδ).trans ?_
      rw [intervalIntegral.integral_of_le (by linarith)]
      refine setIntegral_mono_on ?_ hint.integrableOn measurableSet_Ioc fun t ht => ?_
      · refine (Continuous.integrableOn_Icc (μ := volume) ?_).mono_set Ioc_subset_Icc_self
        exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
          fun t => (by positivity : (0 : ℝ) < r ^ 2 + (t - γ) ^ 2).ne'
      · have habs : |t - γ| ≤ δ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        have h := hfloor γ hγ r hr hrδ t habs
        have hpos : 0 < r ^ 2 + (t - γ) ^ 2 := by positivity
        rw [div_le_iff₀ hpos]
        exact h
    have hsumle : ∑ γ ∈ S, ∫ t in W γ, f t ≤ ∫ t, f t := by
      have hind : ∀ γ ∈ S, ∫ t in W γ, f t = ∫ t, (W γ).indicator f t := fun γ _ =>
        (integral_indicator measurableSet_Ioc).symm
      rw [Finset.sum_congr rfl hind,
        ← integral_finsetSum S fun γ _ => (hint.indicator measurableSet_Ioc)]
      refine integral_mono_of_nonneg (Eventually.of_forall fun t =>
        Finset.sum_nonneg fun γ _ => indicator_nonneg (fun t _ => hf0 t) t) hint
        (Eventually.of_forall fun t => ?_)
      have hcard : (S.filter fun γ => t ∈ W γ).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        by_contra hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        have := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
        simp only [hW, mem_Ioc] at ha' hb'
        rcases lt_abs.mp this with h | h <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
      have heq : ∑ γ ∈ S, (W γ).indicator f t =
          ((S.filter fun γ => t ∈ W γ).card : ℝ) * f t := by
        rw [← Finset.sum_boole, Finset.sum_mul]
        refine Finset.sum_congr rfl fun γ _ => ?_
        by_cases h : t ∈ W γ
        · rw [indicator_of_mem h, if_pos h, one_mul]
        · rw [indicator_of_notMem h, if_neg h, zero_mul]
      simp only
      rw [heq]
      have hc : ((S.filter fun γ => t ∈ W γ).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [hf0 t]
    have hsum : Q * (Real.pi / r - 2 / δ) ≤ ∑ γ ∈ S, ∫ t in W γ, f t := by
      rw [hQ, Finset.sum_mul]
      exact Finset.sum_le_sum hwin
    linarith
  by_contra hlt
  push Not at hlt
  set g := Q - A with hg
  have hg0 : 0 < g := by linarith
  set D := 2 * Q / (Real.pi * δ) + |B| / Real.pi + 1 with hDdef
  have hD : 0 < D := by positivity
  set r := min (δ / 2) (g / (2 * D)) with hrdef
  have hr : 0 < r := lt_min (by linarith) (by positivity)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrg : r * D ≤ g / 2 := by
    have := min_le_right (δ / 2) (g / (2 * D))
    rw [← hrdef] at this
    calc r * D ≤ g / (2 * D) * D := mul_le_mul_of_nonneg_right this hD.le
      _ = g / 2 := by field_simp
  have h := hkey r hr hrδ
  have hpi := Real.pi_pos
  -- multiply by `r / π`
  have hmul : Q - 2 * Q * r / (Real.pi * δ) ≤ A + B * r / Real.pi := by
    have e1 : Q * (Real.pi / r - 2 / δ) * (r / Real.pi) = Q - 2 * Q * r / (Real.pi * δ) := by
      field_simp
    have e2 : (Real.pi * A / r + B) * (r / Real.pi) = A + B * r / Real.pi := by
      field_simp
    have := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ r / Real.pi)
    rw [e1, e2] at this
    exact this
  have hBr : B * r / Real.pi ≤ |B| * r / Real.pi := by
    have := le_abs_self B
    have : B * r ≤ |B| * r := mul_le_mul_of_nonneg_right this hr.le
    exact div_le_div_of_nonneg_right this hpi.le
  have hexp : r * D = 2 * Q * r / (Real.pi * δ) + |B| * r / Real.pi + r := by
    rw [hDdef]; field_simp
  nlinarith

/-! ## The theorem -/

/-- The point `½ + iγ`. -/
def criticalOrdinatePoint (γ : ℝ) : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * I

theorem criticalOrdinatePoint_re (γ : ℝ) : (criticalOrdinatePoint γ).re = 1 / 2 := by simp [criticalOrdinatePoint]

theorem criticalOrdinatePoint_ne_one (γ : ℝ) : criticalOrdinatePoint γ ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [criticalOrdinatePoint_re] at this
  norm_num at this

/-- The floor of `Γ/ζ` on `Re s = ½ + r` near a critical zero, for every `K` below `|Γ(ρ)/ζ'(ρ)|`. -/
theorem exists_line_floor {γ : ℝ} (hz : riemannZeta (criticalOrdinatePoint γ) = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : K * ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ < ‖Complex.Gamma (criticalOrdinatePoint γ)‖) :
    ∃ δ > 0, ∀ G : ℂ → ℂ, ∀ r : ℝ, 0 < r → r < δ →
      (∀ s : ℂ, 1 / 2 + r / 2 < s.re → G s * zetaResidueUnit s = Complex.Gamma s * (s - 1)) →
      ∀ t : ℝ, |t - γ| ≤ δ →
        K ^ 2 ≤ ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (r ^ 2 + (t - γ) ^ 2) := by
  obtain ⟨δ₀, hδ₀, hfl⟩ := exists_floor_near_zero (criticalOrdinatePoint_ne_one γ)
    (by rw [criticalOrdinatePoint_re]; norm_num) hz hK0 hK
  refine ⟨min (δ₀ / 2) (1 / 4), lt_min (by positivity) (by norm_num),
    fun G r hr hrδ' hid t ht' => ?_⟩
  have hrδ : r < δ₀ / 2 := lt_of_lt_of_le hrδ' (min_le_left _ _)
  have hr4 : r < 1 / 4 := lt_of_lt_of_le hrδ' (min_le_right _ _)
  have ht : |t - γ| ≤ δ₀ / 2 := ht'.trans (min_le_left _ _)
  set s : ℂ := ((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + r := by simp [hs]
  have hsρ : s - criticalOrdinatePoint γ = (r : ℂ) + ((t - γ : ℝ) : ℂ) * I := by
    simp only [hs, criticalOrdinatePoint]; push_cast; ring
  have hnormsq : ‖s - criticalOrdinatePoint γ‖ ^ 2 = r ^ 2 + (t - γ) ^ 2 := by
    rw [hsρ, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hnorm : ‖s - criticalOrdinatePoint γ‖ ≤ δ₀ := by
    rw [hsρ]
    calc ‖(r : ℂ) + ((t - γ : ℝ) : ℂ) * I‖ ≤ ‖(r : ℂ)‖ + ‖((t - γ : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = r + |t - γ| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
      _ ≤ δ₀ := by linarith
  have h1 := hfl s hnorm
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    simp at this
    linarith
  have hspos : 0 < s.re := by rw [hsre]; linarith
  have hids := hid s (by rw [hsre]; linarith)
  simp only [zetaResidueUnit, Function.update_of_ne hs1] at hids
  have hGζ : G s * riemannZeta s = Complex.Gamma s := by
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have : (s - 1) * (G s * riemannZeta s - Complex.Gamma s) = 0 := by
      linear_combination hids
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hs1'
    · exact sub_eq_zero.mp h
  have hζne : riemannZeta s ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hGζ
    exact Complex.Gamma_ne_zero_of_re_pos hspos hGζ.symm
  have hζpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hζne
  have hΓ : ‖Complex.Gamma s‖ = ‖G s‖ * ‖riemannZeta s‖ := by rw [← hGζ, norm_mul]
  rw [hΓ] at h1
  have hK1 : K ≤ ‖G s‖ * ‖s - criticalOrdinatePoint γ‖ := by
    have : K * ‖riemannZeta s‖ ≤ (‖G s‖ * ‖s - criticalOrdinatePoint γ‖) * ‖riemannZeta s‖ := by
      linarith [h1]
    exact le_of_mul_le_mul_right this hζpos
  calc K ^ 2 ≤ (‖G s‖ * ‖s - criticalOrdinatePoint γ‖) ^ 2 := pow_le_pow_left₀ hK0 hK1 2
    _ = ‖G s‖ ^ 2 * (r ^ 2 + (t - γ) ^ 2) := by rw [mul_pow, hnormsq]

/-- From finite families of floors to a bound `Σ K_γ² ≤ (1+η)² c`. -/
theorem sum_sq_le_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (S : Finset ℝ) (hS : ∀ γ ∈ S, riemannZeta (criticalOrdinatePoint γ) = 0) (K : ℝ → ℝ)
    (hK0 : ∀ γ ∈ S, 0 ≤ K γ)
    (hK : ∀ γ ∈ S, K γ * ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ <
      ‖Complex.Gamma (criticalOrdinatePoint γ)‖) :
    ∑ γ ∈ S, K γ ^ 2 ≤ (1 + η) ^ 2 * c := by
  set B' := (1 + η) * (c * (Real.log 5 + Real.log η⁻¹) + C) + 4 * (1 + η⁻¹) with hB'
  have hA : 0 ≤ (1 + η) ^ 2 * c := by positivity
  have htail : ∀ N : ℕ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ∫ x in y..1, finiteMobiusLaplacePencil N x ^ 2 ≤ (1 + η) ^ 2 * c * (-Real.log y) + B' :=
    fun N y hy0 hy1 => intervalIntegral_sq_pencil_le_of_hilbert_log_sharp hc hη hη1 hH hy0 hy1 N
  have hline : ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      Integrable (fun t : ℝ =>
        ‖mellin mobiusDiscreteLaplaceTransform (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ∧
      ∫ t : ℝ, ‖mellin mobiusDiscreteLaplaceTransform (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ Real.pi * ((1 + η) ^ 2 * c) / r + 2 * Real.pi * (B' + 4) := by
    intro r hr hr1
    obtain ⟨hi, hle, -⟩ := mobiusMellin_line_le_of_tail hA htail hr hr1
    refine ⟨hi, hle.trans (le_of_eq ?_)⟩
    field_simp
    ring
  obtain ⟨δ₁, hδ₁, hfl⟩ := exists_pos_forall_mem_of_antitone S
    (P := fun γ δ => ∀ G : ℂ → ℂ, ∀ r : ℝ, 0 < r → r < δ →
      (∀ s : ℂ, 1 / 2 + r / 2 < s.re → G s * zetaResidueUnit s = Complex.Gamma s * (s - 1)) →
      ∀ t : ℝ, |t - γ| ≤ δ →
        K γ ^ 2 ≤ ‖G (((1 / 2 + r : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 * (r ^ 2 + (t - γ) ^ 2))
    (fun γ δ δ' _ hle hP G r hr hrδ hid t ht => hP G r hr (lt_of_lt_of_le hrδ hle) hid t
      (ht.trans hle))
    (fun γ hγ => exists_line_floor (hS γ hγ) (hK0 γ hγ) (hK γ hγ))
  obtain ⟨δ₂, hδ₂, hsep⟩ := exists_pos_forall_two_mul_lt_abs_sub S
  set δ := min (min δ₁ δ₂) (1 / 2) with hδdef
  have hδ : 0 < δ := lt_min (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδδ₁ : δ ≤ δ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₂ : δ ≤ δ₂ := (min_le_left _ _).trans (min_le_right _ _)
  refine sum_sq_le_of_line_bound hline S K hδ hδ1
    (fun a ha b hb hab => lt_of_le_of_lt (by linarith) (hsep a ha b hb hab)) ?_
  intro γ hγ r hr hrδ t ht
  have hr1 : r ≤ 1 / 2 := by linarith
  obtain ⟨-, -, hid⟩ := mobiusMellin_line_le_of_tail hA htail hr hr1
  exact hfl γ hγ _ r hr (lt_of_lt_of_le hrδ hδδ₁) hid t (ht.trans hδδ₁)

/-- If `(1 − η)² Q ≤ (1 + η)² c` for all `0 < η < 1`, then `Q ≤ c`. -/
theorem le_of_forall_one_sub_sq_mul_le {Q c : ℝ}
    (h : ∀ η : ℝ, 0 < η → η < 1 → (1 - η) ^ 2 * Q ≤ (1 + η) ^ 2 * c) : Q ≤ c := by
  have hcont : Continuous fun η : ℝ => (1 + η) ^ 2 * c - (1 - η) ^ 2 * Q := by fun_prop
  have hlim : Tendsto (fun η : ℝ => (1 + η) ^ 2 * c - (1 - η) ^ 2 * Q) (𝓝[>] 0)
      (𝓝 ((1 + 0) ^ 2 * c - (1 - 0) ^ 2 * Q)) :=
    (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 ≤ (1 + η) ^ 2 * c - (1 - η) ^ 2 * Q := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with η hη
    linarith [h η hη.1 hη.2]
  have := ge_of_tendsto hlim hev
  norm_num at this
  linarith

/-- **The sharp logarithmic constant.** If `Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) ≤ c log(N+1) + C` for every
`N`, then every zero `½ + iγ` (`γ ∈ S`) is simple and `Σ_{γ∈S} |Γ(½+iγ)|²/|ζ'(½+iγ)|² ≤ c`. -/
theorem sum_normSq_gamma_div_deriv_zeta_le_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    (S : Finset ℝ) (hS : ∀ γ ∈ S, riemannZeta (criticalOrdinatePoint γ) = 0) :
    (∀ γ ∈ S, deriv riemannZeta (criticalOrdinatePoint γ) ≠ 0) ∧
      ∑ γ ∈ S, ‖Complex.Gamma (criticalOrdinatePoint γ)‖ ^ 2 /
        ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ ^ 2 ≤ c := by
  have hΓpos : ∀ γ : ℝ, 0 < ‖Complex.Gamma (criticalOrdinatePoint γ)‖ := fun γ =>
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by rw [criticalOrdinatePoint_re]; norm_num))
  have hsimple : ∀ γ ∈ S, deriv riemannZeta (criticalOrdinatePoint γ) ≠ 0 := by
    intro γ₀ hγ₀ h0
    have h := sum_sq_le_of_hilbert_log hc hH (η := 1) one_pos le_rfl {γ₀}
      (fun γ hγ => by rw [Finset.mem_singleton.mp hγ]; exact hS γ₀ hγ₀)
      (fun _ => Real.sqrt (4 * c + 1)) (fun _ _ => Real.sqrt_nonneg _)
      (fun γ hγ => by rw [Finset.mem_singleton.mp hγ, h0, norm_zero, mul_zero]; exact hΓpos γ₀)
    rw [Finset.sum_singleton, Real.sq_sqrt (by positivity)] at h
    linarith
  refine ⟨hsimple, le_of_forall_one_sub_sq_mul_le fun η hη hη1 => ?_⟩
  have h := sum_sq_le_of_hilbert_log hc hH hη hη1.le S hS
    (fun γ => (1 - η) * ‖Complex.Gamma (criticalOrdinatePoint γ)‖ / ‖deriv riemannZeta (criticalOrdinatePoint γ)‖)
    (fun γ _ => by have := hΓpos γ; positivity)
    (fun γ hγ => by
      have hd : 0 < ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ := norm_pos_iff.mpr (hsimple γ hγ)
      rw [div_mul_cancel₀ _ hd.ne']
      have := hΓpos γ
      nlinarith)
  rw [Finset.mul_sum]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun γ hγ => ?_)) h
  have hd : 0 < ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ := norm_pos_iff.mpr (hsimple γ hγ)
  field_simp

/-- **Sharp Ω form.** If a finite set of critical zeros has `Σ |Γ(½+iγ)|²/|ζ'(½+iγ)|² > c ≥ 0`,
then for every `C` some `N` has `Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) > c log(N+1) + C`. -/
theorem exists_hilbert_gt_log_of_lt_sum {c : ℝ} (hc : 0 ≤ c) (S : Finset ℝ)
    (hS : ∀ γ ∈ S, riemannZeta (criticalOrdinatePoint γ) = 0)
    (hlt : c < ∑ γ ∈ S, ‖Complex.Gamma (criticalOrdinatePoint γ)‖ ^ 2 /
      ‖deriv riemannZeta (criticalOrdinatePoint γ)‖ ^ 2) (C : ℝ) :
    ∃ N : ℕ, c * Real.log ((N : ℝ) + 1) + C < finiteMobiusGammaHankelEnergy N 1 := by
  by_contra hcon
  push Not at hcon
  have := (sum_normSq_gamma_div_deriv_zeta_le_of_hilbert_log hc hcon S hS).2
  linarith

/-- **A logarithmic Hilbert bound forces simple critical zeros.** -/
theorem deriv_riemannZeta_ne_zero_of_hilbert_log {c C : ℝ} (hc : 0 ≤ c)
    (hH : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ c * Real.log ((N : ℝ) + 1) + C)
    {γ : ℝ} (hz : riemannZeta (criticalOrdinatePoint γ) = 0) :
    deriv riemannZeta (criticalOrdinatePoint γ) ≠ 0 :=
  (sum_normSq_gamma_div_deriv_zeta_le_of_hilbert_log hc hH {γ}
    (fun γ' hγ' => by rw [Finset.mem_singleton.mp hγ']; exact hz)).1 γ (Finset.mem_singleton_self γ)

end RHTower
