import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelopeDecay

/-!
# Sharp vertical lower bound for the Gamma function

For `0 ≤ σ ≤ 1` and `|t| ≥ 1`,

  `|Γ(σ+it)|⁻¹ ≤ C |t|^{1/2-σ} e^{π|t|/2}`.

The function `g(z) = Γ(z)⁻¹ (z+2)^{z-1/2}` is holomorphic on `Re z > -2`.  On the lines `Re z = 0` and
`Re z = 1` the exact moduli `|Γ(it)|² = π/(|t| |sinh πt|)` and `|Γ(1+it)|² = π|t|/|sinh πt|`, together with
`t·arg(c+it) = |t| arctan(|t|/c) ≥ π|t|/2 - c`, bound `g`; it has order one in the strip, so
Phragmén–Lindelöf bounds it on `0 ≤ Re z ≤ 1`.  Dividing by `|(z+2)^{z-1/2}| = |z+2|^{σ-1/2} e^{-t arg(z+2)}`
gives the claim.
-/

open Complex Real Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `arctan y ≤ y` for `y ≥ 0`. -/
theorem arctan_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) : Real.arctan y ≤ y := by
  have h := Real.le_tan (Real.arctan_nonneg.mpr hy) (Real.arctan_lt_pi_div_two y)
  rwa [Real.tan_arctan] at h

/-- `arctan u ≥ π/2 - 1/u` for `u > 0`. -/
theorem pi_div_two_sub_inv_le_arctan {u : ℝ} (hu : 0 < u) : π / 2 - 1 / u ≤ Real.arctan u := by
  have h := Real.arctan_inv_of_pos hu
  have h2 := arctan_le_self_of_nonneg (inv_nonneg.mpr hu.le)
  rw [one_div]; linarith

/-- `arg(c + it) = arctan(t/c)` for `c > 0`. -/
theorem arg_ofReal_add_mul_I {c t : ℝ} (hc : 0 < c) :
    Complex.arg ((c : ℂ) + (t : ℂ) * I) = Real.arctan (t / c) := by
  set z : ℂ := (c : ℂ) + (t : ℂ) * I with hz
  have hre : z.re = c := by simp [hz]
  have him : z.im = t := by simp [hz]
  have habs := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hc))
  have htan := Complex.tan_arg z
  rw [hre, him] at htan
  rw [← htan, Real.arctan_tan (by linarith [(abs_lt.mp habs).1]) (abs_lt.mp habs).2]

/-- `t · arg(c + it) ≥ π|t|/2 - c` for `c > 0`, `t ≠ 0`. -/
theorem mul_arg_ge {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    π * |t| / 2 - c ≤ t * Complex.arg ((c : ℂ) + (t : ℂ) * I) := by
  rw [arg_ofReal_add_mul_I hc]
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hkey : t * Real.arctan (t / c) = |t| * Real.arctan (|t| / c) := by
    rcases lt_or_gt_of_ne ht with h | h
    · rw [abs_of_neg h, show -t / c = -(t / c) by ring, Real.arctan_neg, neg_mul_neg]
    · rw [abs_of_pos h]
  rw [hkey]
  have hb := pi_div_two_sub_inv_le_arctan (show 0 < |t| / c by positivity)
  have : |t| * (π / 2 - 1 / (|t| / c)) = π * |t| / 2 - c := by field_simp
  nlinarith

/-- `|sinh x| ≤ e^{|x|}/2`. -/
private theorem abs_sinh_le_exp_abs (x : ℝ) : |Real.sinh x| ≤ Real.exp |x| / 2 := by
  rw [Real.sinh_eq]
  have h1 := Real.exp_pos x
  have h2 := Real.exp_pos (-x)
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos hx]
    have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith)]; linarith

/-- The Phragmén–Lindelöf test function `Γ(z)⁻¹ (z+2)^{z-1/2}`. -/
def gammaVerticalTest (z : ℂ) : ℂ := (Complex.Gamma z)⁻¹ * (z + 2) ^ (z - 1 / 2)

theorem norm_cpow_shift (z : ℂ) (hz : 0 < (z + 2).re) :
    ‖(z + 2) ^ (z - 1 / 2)‖ = ‖z + 2‖ ^ (z.re - 1 / 2) / Real.exp (Complex.arg (z + 2) * z.im) := by
  have hne : z + 2 ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [Complex.norm_cpow_of_ne_zero hne]
  simp

theorem differentiableOn_gammaVerticalTest :
    DifferentiableOn ℂ gammaVerticalTest {z : ℂ | -2 < z.re} := by
  intro z hz
  have hz' : -2 < z.re := hz
  have hslit : z + 2 ∈ Complex.slitPlane := Or.inl (by simp; linarith)
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold gammaVerticalTest
  exact (Complex.differentiable_one_div_Gamma z).mul
    ((differentiableAt_id.add_const 2).cpow (differentiableAt_id.sub_const _) hslit)

/-- The boundary bound on `Re z = 0`, `|t| ≥ 1`. -/
theorem norm_gammaVerticalTest_zero_le {t : ℝ} (ht : 1 ≤ |t|) :
    ‖gammaVerticalTest ((t : ℂ) * I)‖ ≤ Real.exp 2 := by
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  have htpos : 0 < |t| := abs_pos.mpr ht0
  set z : ℂ := (t : ℂ) * I with hz
  have hz2 : z + 2 = (2 : ℝ) + (t : ℂ) * I := by rw [hz]; push_cast; ring
  have hre : 0 < (z + 2).re := by rw [hz2]; simp
  have hzre : z.re = 0 := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  -- `|Γ(it)|² = π/(|t| |sinh πt|)`
  have hG1 := GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_I_sq ht0
  have hstep : Complex.Gamma (1 + (t : ℂ) * I) = (t : ℂ) * I * Complex.Gamma ((t : ℂ) * I) := by
    rw [add_comm]; exact Complex.Gamma_add_one _ (by simp [Complex.ext_iff, ht0])
  have hnormI : ‖(t : ℂ) * I‖ = |t| := by simp
  have hsinh : 0 < |Real.sinh (π * t)| := abs_pos.mpr (by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht0)
  have hGsq : ‖Complex.Gamma z‖ ^ 2 = π / (|t| * |Real.sinh (π * t)|) := by
    rw [hstep, norm_mul, hnormI, mul_pow] at hG1
    rw [hz]
    field_simp at hG1 ⊢
    nlinarith [hG1]
  have hGpos : 0 < ‖Complex.Gamma z‖ := by
    refine norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m h => ?_)
    have him := congrArg Complex.im h
    rw [hz] at him; simp at him; exact ht0 him
  unfold gammaVerticalTest
  rw [norm_mul, norm_inv, norm_cpow_shift z hre, hzre, hzim, hz2]
  have harg := mul_arg_ge (c := 2) (by norm_num) ht0
  have hmod : ‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ) ≤ |t| ^ (-(1 / 2 : ℝ)) := by
    have hge : |t| ≤ ‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
      have := Complex.abs_im_le_norm (((2 : ℝ) : ℂ) + (t : ℂ) * I); simpa using this
    rw [show (0 - 1 / 2 : ℝ) = -(1 / 2) by norm_num]
    exact Real.rpow_le_rpow_of_nonpos htpos hge (by norm_num)
  have hexp : (Real.exp (Complex.arg (((2 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹ ≤ Real.exp (-(π * |t| / 2 - 2)) := by
    rw [← Real.exp_neg]; apply Real.exp_le_exp.mpr; linarith
  -- `‖Γ(it)‖⁻¹ ≤ √(|t|/(2π)) e^{π|t|/2}` in squared form
  have hinvsq : (‖Complex.Gamma z‖⁻¹) ^ 2 ≤ |t| * Real.exp (π * |t|) / (2 * π) := by
    rw [inv_pow, hGsq, inv_div]
    have hs := abs_sinh_le_exp_abs (π * t)
    rw [abs_mul, abs_of_pos Real.pi_pos] at hs
    rw [div_le_div_iff₀ Real.pi_pos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ |t| * (2 * π) by positivity)]
  have hprod_sq : (‖Complex.Gamma z‖⁻¹ * (‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ) /
      Real.exp (Complex.arg (((2 : ℝ) : ℂ) + (t : ℂ) * I) * t))) ^ 2 ≤ Real.exp 2 ^ 2 := by
    have hA : 0 ≤ ‖Complex.Gamma z‖⁻¹ := by positivity
    have hB : 0 ≤ ‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    rw [div_eq_mul_inv, mul_pow, mul_pow]
    have hB2 : (‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ)) ^ 2 ≤ |t|⁻¹ := by
      calc (‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ)) ^ 2 ≤ (|t| ^ (-(1 / 2 : ℝ))) ^ 2 :=
            pow_le_pow_left₀ hB hmod 2
        _ = |t|⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]; norm_num
            rw [Real.rpow_neg_one]
    have hC2 : ((Real.exp (Complex.arg (((2 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹) ^ 2 ≤
        Real.exp (-(π * |t| / 2 - 2)) ^ 2 := pow_le_pow_left₀ (by positivity) hexp 2
    calc (‖Complex.Gamma z‖⁻¹) ^ 2 * ((‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ)) ^ 2 *
          ((Real.exp (Complex.arg (((2 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹) ^ 2)
        ≤ (|t| * Real.exp (π * |t|) / (2 * π)) * (|t|⁻¹ * Real.exp (-(π * |t| / 2 - 2)) ^ 2) := by
          gcongr
      _ = Real.exp 4 / (2 * π) := by
          have hsq : Real.exp (-(π * |t| / 2 - 2)) ^ 2 = Real.exp (-(π * |t|) + 4) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          have he : Real.exp (π * |t|) * Real.exp (-(π * |t|) + 4) = Real.exp 4 := by
            rw [← Real.exp_add]; congr 1; ring
          have hti : |t| * |t|⁻¹ = 1 := mul_inv_cancel₀ htpos.ne'
          rw [hsq]
          calc |t| * Real.exp (π * |t|) / (2 * π) * (|t|⁻¹ * Real.exp (-(π * |t|) + 4))
              = (|t| * |t|⁻¹) * (Real.exp (π * |t|) * Real.exp (-(π * |t|) + 4)) / (2 * π) := by ring
            _ = Real.exp 4 / (2 * π) := by rw [hti, he, one_mul]
      _ ≤ Real.exp 2 ^ 2 := by
          rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * 2 = 4 by norm_num]
          rw [div_le_iff₀ (by positivity)]
          have : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
          have h4 := Real.exp_pos 4
          nlinarith
  have hnn : 0 ≤ ‖Complex.Gamma z‖⁻¹ * (‖((2 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (0 - 1 / 2 : ℝ) /
      Real.exp (Complex.arg (((2 : ℝ) : ℂ) + (t : ℂ) * I) * t)) := by positivity
  exact (pow_le_pow_iff_left₀ hnn (Real.exp_pos 2).le (by norm_num)).mp hprod_sq

/-- The boundary bound on `Re z = 1`, `|t| ≥ 1`. -/
theorem norm_gammaVerticalTest_one_le {t : ℝ} (ht : 1 ≤ |t|) :
    ‖gammaVerticalTest (1 + (t : ℂ) * I)‖ ≤ Real.exp 3 := by
  have ht0 : t ≠ 0 := fun h => by rw [h, abs_zero] at ht; linarith
  have htpos : 0 < |t| := abs_pos.mpr ht0
  set z : ℂ := 1 + (t : ℂ) * I with hz
  have hz2 : z + 2 = (3 : ℝ) + (t : ℂ) * I := by rw [hz]; push_cast; ring
  have hre : 0 < (z + 2).re := by rw [hz2]; simp
  have hzre : z.re = 1 := by simp [hz]
  have hzim : z.im = t := by simp [hz]
  have hG1 := GaloisForLFunctions.HTGeometry.norm_Gamma_one_add_I_sq ht0
  have hsinh : 0 < |Real.sinh (π * t)| := abs_pos.mpr (by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht0)
  have hGpos : 0 < ‖Complex.Gamma z‖ := by
    have : 0 < ‖Complex.Gamma z‖ ^ 2 := by rw [hz, hG1]; positivity
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (by simpa using this)
  unfold gammaVerticalTest
  rw [norm_mul, norm_inv, norm_cpow_shift z hre, hzre, hzim, hz2]
  have harg := mul_arg_ge (c := 3) (by norm_num) ht0
  have hexp : (Real.exp (Complex.arg (((3 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹ ≤ Real.exp (-(π * |t| / 2 - 3)) := by
    rw [← Real.exp_neg]; apply Real.exp_le_exp.mpr; linarith
  have hmod : ‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ 4 * |t| := by
    calc ‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ≤ ‖((3 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 3 + |t| := by simp
      _ ≤ 4 * |t| := by linarith
  have hinvsq : (‖Complex.Gamma z‖⁻¹) ^ 2 ≤ Real.exp (π * |t|) / (2 * π * |t|) := by
    rw [inv_pow, hz, hG1, inv_div]
    have hs := abs_sinh_le_exp_abs (π * t)
    rw [abs_mul, abs_of_pos Real.pi_pos] at hs
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * π * |t| by positivity)]
  have hB0 : 0 ≤ ‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (1 - 1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hB2 : (‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (1 - 1 / 2 : ℝ)) ^ 2 ≤ 4 * |t| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num; exact hmod
  have hprod_sq : (‖Complex.Gamma z‖⁻¹ * (‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (1 - 1 / 2 : ℝ) /
      Real.exp (Complex.arg (((3 : ℝ) : ℂ) + (t : ℂ) * I) * t))) ^ 2 ≤ Real.exp 3 ^ 2 := by
    rw [div_eq_mul_inv, mul_pow, mul_pow]
    have hC2 : ((Real.exp (Complex.arg (((3 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹) ^ 2 ≤
        Real.exp (-(π * |t| / 2 - 3)) ^ 2 := pow_le_pow_left₀ (by positivity) hexp 2
    have hsq : Real.exp (-(π * |t| / 2 - 3)) ^ 2 = Real.exp (-(π * |t|) + 6) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have he : Real.exp (π * |t|) * Real.exp (-(π * |t|) + 6) = Real.exp 6 := by
      rw [← Real.exp_add]; congr 1; ring
    calc (‖Complex.Gamma z‖⁻¹) ^ 2 * ((‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (1 - 1 / 2 : ℝ)) ^ 2 *
          ((Real.exp (Complex.arg (((3 : ℝ) : ℂ) + (t : ℂ) * I) * t))⁻¹) ^ 2)
        ≤ (Real.exp (π * |t|) / (2 * π * |t|)) * (4 * |t| * Real.exp (-(π * |t| / 2 - 3)) ^ 2) := by
          gcongr
      _ = 2 / π * Real.exp 6 := by
          rw [hsq, ← he]; field_simp; ring
      _ ≤ Real.exp 3 ^ 2 := by
          rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * 3 = 6 by norm_num]
          have : 2 / π ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
          have h6 := Real.exp_pos 6
          nlinarith
  have hnn : 0 ≤ ‖Complex.Gamma z‖⁻¹ * (‖((3 : ℝ) : ℂ) + (t : ℂ) * I‖ ^ (1 - 1 / 2 : ℝ) /
      Real.exp (Complex.arg (((3 : ℝ) : ℂ) + (t : ℂ) * I) * t)) := by positivity
  exact (pow_le_pow_iff_left₀ hnn (Real.exp_pos 3).le (by norm_num)).mp hprod_sq

theorem continuousOn_gammaVerticalTest :
    ContinuousOn gammaVerticalTest {z : ℂ | -2 < z.re} :=
  differentiableOn_gammaVerticalTest.continuousOn

/-- A bound for `g` on the part `|Im z| ≤ 1` of the closed strip. -/
theorem exists_bound_gammaVerticalTest_compact :
    ∃ C₁ : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → |z.im| ≤ 1 → ‖gammaVerticalTest z‖ ≤ C₁ := by
  set K : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ 1} with hK
  have hclosed : IsClosed K :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
    rw [mem_closedBall_zero_iff]
    obtain ⟨h0, h1, h2⟩ := hz
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 := by rw [abs_of_nonneg h0]; linarith
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn
    (continuousOn_gammaVerticalTest.mono fun z hz => by
      show -2 < z.re; linarith [hz.1])
  exact ⟨C₁, fun z h0 h1 him => hC₁ z ⟨h0, h1, him⟩⟩

/-- **Phragmén–Lindelöf bound for `g` on the strip `0 ≤ Re z ≤ 1`.** -/
theorem exists_bound_gammaVerticalTest :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖gammaVerticalTest z‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_bound_gammaVerticalTest_compact
  obtain ⟨B, hB, hGinv⟩ := exists_bound_norm_inv_Gamma_strip 0 1
  set C : ℝ := max C₁ (Real.exp 3) with hC
  refine ⟨C, fun z hz0 hz1 => ?_⟩
  have hsub : closure (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ⊆ {z : ℂ | -2 < z.re} := by
    rw [Complex.closure_preimage_re, closure_Ioo (by norm_num)]
    intro w hw; show -2 < w.re; linarith [hw.1]
  have hdc : DiffContOnCl ℂ gammaVerticalTest (Complex.re ⁻¹' Ioo (0 : ℝ) 1) :=
    (differentiableOn_gammaVerticalTest.mono hsub).diffContOnCl
  have hgrowth : ∃ c < π / (1 - 0), ∃ B' : ℝ, gammaVerticalTest =O[Filter.comap (abs ∘ Complex.im) atTop ⊓
      Filter.principal (Complex.re ⁻¹' Ioo (0 : ℝ) 1)] fun z => Real.exp (B' * Real.exp (c * |z.im|)) := by
    refine ⟨1, by rw [sub_zero]; linarith [Real.pi_gt_three], |Real.log (4 * B)| + 7, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    have h1 : ∀ᶠ z in Filter.comap (abs ∘ Complex.im) atTop, 1 ≤ |z.im| := by
      rw [Filter.eventually_comap]
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy z hz
      have hz' : |z.im| = y := hz
      rw [hz']; exact hy
    filter_upwards [h1.filter_mono inf_le_left,
      Filter.mem_inf_of_right (Filter.mem_principal_self (Complex.re ⁻¹' Ioo (0 : ℝ) 1))]
      with z hzim hzs
    have hzs' : 0 < z.re ∧ z.re < 1 := hzs
    set t := z.im
    have hre2 : 0 < (z + 2).re := by simp; linarith [hzs'.1]
    have hnorm2 : 1 ≤ ‖z + 2‖ := by
      have := Complex.re_le_norm (z + 2); simp at this ⊢; linarith [hzs'.1]
    have hnorm2' : ‖z + 2‖ ≤ 3 + |t| := by
      calc ‖z + 2‖ ≤ |(z + 2).re| + |(z + 2).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 3 + |t| := by
            simp only [Complex.add_re, Complex.add_im, Complex.re_ofNat, Complex.im_ofNat, add_zero]
            rw [abs_of_pos (by linarith [hzs'.1])]; linarith [hzs'.2]
    have hargt : -(Complex.arg (z + 2) * t) ≤ π / 2 * |t| := by
      have hab := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
      have := abs_mul (Complex.arg (z + 2)) t
      have h2 : |Complex.arg (z + 2) * t| ≤ π / 2 * |t| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hab.le (abs_nonneg _)
      linarith [neg_abs_le (Complex.arg (z + 2) * t)]
    unfold gammaVerticalTest
    rw [norm_mul, norm_inv, norm_cpow_shift z hre2]
    have hG := hGinv z hzs'.1.le hzs'.2.le hzim
    rw [norm_inv] at hG
    have hpow : ‖z + 2‖ ^ (z.re - 1 / 2) ≤ 4 * Real.exp |t| := by
      calc ‖z + 2‖ ^ (z.re - 1 / 2) ≤ ‖z + 2‖ ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hnorm2 (by linarith [hzs'.2])
        _ = ‖z + 2‖ := Real.rpow_one _
        _ ≤ 3 + |t| := hnorm2'
        _ ≤ 4 * Real.exp |t| := by
            have := Real.add_one_le_exp |t|; nlinarith [Real.one_le_exp (abs_nonneg t)]
    have hdiv : ‖z + 2‖ ^ (z.re - 1 / 2) / Real.exp (Complex.arg (z + 2) * t) ≤
        4 * Real.exp |t| * Real.exp (π / 2 * |t|) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      exact mul_le_mul hpow (Real.exp_le_exp.mpr hargt) (Real.exp_pos _).le (by positivity)
    have hmain : ‖Complex.Gamma z‖⁻¹ * (‖z + 2‖ ^ (z.re - 1 / 2) / Real.exp (Complex.arg (z + 2) * t)) ≤
        (4 * B) * Real.exp (7 * |t|) := by
      calc ‖Complex.Gamma z‖⁻¹ * (‖z + 2‖ ^ (z.re - 1 / 2) / Real.exp (Complex.arg (z + 2) * t))
          ≤ (B * Real.exp (Real.pi * |t|)) * (4 * Real.exp |t| * Real.exp (π / 2 * |t|)) :=
            mul_le_mul hG hdiv (by positivity) (by positivity)
        _ = (4 * B) * Real.exp ((π + 1 + π / 2) * |t|) := by
            rw [show (π + 1 + π / 2) * |t| = π * |t| + |t| + π / 2 * |t| by ring,
              Real.exp_add, Real.exp_add]; ring
        _ ≤ (4 * B) * Real.exp (7 * |t|) := by
            gcongr; nlinarith [Real.pi_lt_four, abs_nonneg t]
    have hlog : (4 * B) * Real.exp (7 * |t|) ≤
        Real.exp ((|Real.log (4 * B)| + 7) * Real.exp (1 * |t|)) := by
      have h4B : 0 < 4 * B := by positivity
      set L := Real.log (4 * B) with hL
      have h4 : 4 * B = Real.exp L := (Real.exp_log h4B).symm
      rw [h4, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have he : |t| ≤ Real.exp (1 * |t|) := by
        rw [one_mul]; have := Real.add_one_le_exp |t|; linarith
      have he1 : 1 ≤ Real.exp (1 * |t|) := Real.one_le_exp (by positivity)
      have hla := le_abs_self L
      nlinarith [abs_nonneg L]
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hmain.trans hlog
  have hbd0 : ∀ z : ℂ, z.re = 0 → ‖gammaVerticalTest z‖ ≤ C := by
    intro w hw
    by_cases hwim : |w.im| ≤ 1
    · exact (hC₁ w (by rw [hw]) (by rw [hw]; norm_num) hwim).trans (le_max_left _ _)
    · have hw' : w = (w.im : ℂ) * I := by
        apply Complex.ext <;> simp [hw]
      rw [hw']
      refine (norm_gammaVerticalTest_zero_le (le_of_lt (not_le.mp hwim))).trans ?_
      exact (Real.exp_le_exp.mpr (by norm_num)).trans (le_max_right _ _)
  have hbd1 : ∀ z : ℂ, z.re = 1 → ‖gammaVerticalTest z‖ ≤ C := by
    intro w hw
    by_cases hwim : |w.im| ≤ 1
    · exact (hC₁ w (by rw [hw]; norm_num) (by rw [hw]) hwim).trans (le_max_left _ _)
    · have hw' : w = 1 + (w.im : ℂ) * I := by
        apply Complex.ext <;> simp [hw]
      rw [hw']
      exact (norm_gammaVerticalTest_one_le (le_of_lt (not_le.mp hwim))).trans (le_max_right _ _)
  exact PhragmenLindelof.vertical_strip hdc hgrowth hbd0 hbd1 hz0 hz1

/-- **Sharp vertical lower bound for `Γ`.** For `0 ≤ σ ≤ 1` and `|t| ≥ 1`,
`|Γ(σ+it)|⁻¹ ≤ C |t|^{1/2-σ} e^{π|t|/2}`. -/
theorem exists_norm_inv_Gamma_le_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * I))⁻¹‖ ≤ C * |t| ^ (1 / 2 - σ) * Real.exp (π * |t| / 2) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_gammaVerticalTest
  refine ⟨2 * (|C₀| + 1), by positivity, fun σ t hσ0 hσ1 ht => ?_⟩
  set z : ℂ := (σ : ℂ) + (t : ℂ) * I with hz
  have hre : z.re = σ := by simp [hz]
  have him : z.im = t := by simp [hz]
  have htpos : 0 < |t| := by linarith
  have hre2 : 0 < (z + 2).re := by simp [hz]; linarith
  have hne : z + 2 ≠ 0 := fun h => by rw [h] at hre2; simp at hre2
  have hg := hC₀ z (by rw [hre]; exact hσ0) (by rw [hre]; exact hσ1)
  unfold gammaVerticalTest at hg
  rw [norm_mul, norm_cpow_shift z hre2, hre, him] at hg
  have hnorm_lo : |t| ≤ ‖z + 2‖ := by
    have := Complex.abs_im_le_norm (z + 2); simpa [hz] using this
  have hnorm_hi : ‖z + 2‖ ≤ 4 * |t| := by
    have hre' : (z + 2).re = σ + 2 := by simp [hz]
    have him' : (z + 2).im = t := by simp [hz]
    calc ‖z + 2‖ ≤ |(z + 2).re| + |(z + 2).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = σ + 2 + |t| := by rw [hre', him', abs_of_pos (by linarith)]
      _ ≤ 4 * |t| := by linarith
  have hnpos : 0 < ‖z + 2‖ := by linarith
  have hQ : 0 < ‖z + 2‖ ^ (σ - 1 / 2) / Real.exp (Complex.arg (z + 2) * t) := by positivity
  have hinv : ‖(Complex.Gamma z)⁻¹‖ ≤ C₀ / (‖z + 2‖ ^ (σ - 1 / 2) / Real.exp (Complex.arg (z + 2) * t)) := by
    rw [le_div_iff₀ hQ]; exact hg
  refine hinv.trans ?_
  rw [div_div_eq_mul_div, div_eq_mul_inv]
  have hargt : Complex.arg (z + 2) * t ≤ π * |t| / 2 := by
    have hab := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
    have h2 : |Complex.arg (z + 2) * t| ≤ π / 2 * |t| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hab.le (abs_nonneg _)
    linarith [le_abs_self (Complex.arg (z + 2) * t)]
  have hpw : (‖z + 2‖ ^ (σ - 1 / 2))⁻¹ ≤ 2 * |t| ^ (1 / 2 - σ) := by
    rw [← Real.rpow_neg hnpos.le, neg_sub]
    rcases le_total 0 (1 / 2 - σ) with hp | hp
    · calc ‖z + 2‖ ^ (1 / 2 - σ) ≤ (4 * |t|) ^ (1 / 2 - σ) := Real.rpow_le_rpow hnpos.le hnorm_hi hp
        _ = 4 ^ (1 / 2 - σ) * |t| ^ (1 / 2 - σ) := Real.mul_rpow (by norm_num) htpos.le
        _ ≤ 2 * |t| ^ (1 / 2 - σ) := by
            gcongr
            calc (4 : ℝ) ^ (1 / 2 - σ) ≤ 4 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 2 := by rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    · calc ‖z + 2‖ ^ (1 / 2 - σ) ≤ |t| ^ (1 / 2 - σ) := Real.rpow_le_rpow_of_nonpos htpos hnorm_lo hp
        _ ≤ 2 * |t| ^ (1 / 2 - σ) := by
            have := Real.rpow_nonneg htpos.le (1 / 2 - σ); linarith
  have hE : Real.exp (Complex.arg (z + 2) * t) ≤ Real.exp (π * |t| / 2) := Real.exp_le_exp.mpr hargt
  calc C₀ * Real.exp (Complex.arg (z + 2) * t) * (‖z + 2‖ ^ (σ - 1 / 2))⁻¹
      ≤ (|C₀| + 1) * Real.exp (π * |t| / 2) * (2 * |t| ^ (1 / 2 - σ)) := by
        gcongr
        · linarith [le_abs_self C₀]
    _ = 2 * (|C₀| + 1) * |t| ^ (1 / 2 - σ) * Real.exp (π * |t| / 2) := by ring

end

end GaloisForLFunctions.HTGeometry
