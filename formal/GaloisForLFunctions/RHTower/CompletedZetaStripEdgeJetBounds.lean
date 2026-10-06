import GaloisForLFunctions.RHTower.ArchimedeanGenusZeroSum
import GaloisForLFunctions.RHTower.XiThetaExplicitBounds
import GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound

/-!
# The strip-edge jet of the completed zeta function

Two explicit bounds on the jet of `Λ₀ = completedRiemannZeta₀` at the strip edge `s = 1`.

* **Value.**  `Λ₀(1) = 1 + (γ − log 4π)/2`, and the half-shifted harmonic bound
  `γ ≤ H₁₃ − log(27/2)` together with artanh floors for `log 2`, `log 3` and `log(π/3)` give
  `Λ₀(1) ≤ 93/4000`.
* **Derivative.**  `Λ₀(s) = M(s/2)/2` with `M` the Mellin transform of the modified theta kernel,
  so `Λ₀'(1) = M'(1/2)/4` and `M'(1/2) = ∫₀^∞ t^{−1/2} log t f_modif(t) dt`.  The theta
  functional equation and the inversion `t ↦ 1/t` fold the inner half-line onto the outer one:
  `M'(1/2) = ∫₁^∞ (x^{−1/2} − x^{−1}) log x (θ(x) − 1) dx`.  With `θ(x) − 1 ≥ 2e^{−πx}` and the
  elementary floor `(x^{−1/2} − x^{−1}) log x ≥ (2/5)(x−1)² e^{−9(x−1)/8}`, a Gamma integral gives
  `Re Λ₀'(1) ≥ (2/5) e^{−π}/(π + 9/8)³ ≥ 111/500000`.

Both bounds are certified from the theta representation and classical constants alone; no zero of
`ζ` is located.
-/

open Complex MeasureTheory HurwitzZeta Set

namespace RHTower

noncomputable section

/-! ## The Mellin form of `Λ₀'(1)` -/

/-- The logarithmically weighted theta kernel is Mellin convergent at `1/2`, and its Mellin
transform is the derivative of the Mellin transform of the modified kernel. -/
theorem mellin_log_f_modif_half :
    MellinConvergent (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) (1 / 2) ∧
      HasDerivAt (mellin (hurwitzEvenFEPair 0).f_modif)
        (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) (1 / 2)) (1 / 2) :=
  mellin_hasDerivAt_of_isBigO_rpow (hurwitzEvenFEPair 0).hf_modif_int
    ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hf_top (-1)) (by norm_num)
    ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hf_zero (-0)) (by norm_num)

/-- `Λ₀'(1)` is a quarter of the log-weighted Mellin transform at `1/2`. -/
theorem hasDerivAt_completedRiemannZeta₀_one_mellin :
    HasDerivAt completedRiemannZeta₀
      (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) (1 / 2) / 4) 1 := by
  have hg : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) 1 :=
    ((hasDerivAt_id' (1 : ℂ)).div_const 2)
  have h := (mellin_log_f_modif_half.2.comp (1 : ℂ) hg).div_const 2
  have hfun : completedRiemannZeta₀ =
      fun s : ℂ => mellin (hurwitzEvenFEPair 0).f_modif (s / 2) / 2 := rfl
  rw [hfun]
  exact h.congr_deriv (by ring)

/-- The modified theta kernel is real and nonnegative on `(0, ∞)`. -/
theorem f_modif_eq_ofReal_norm {t : ℝ} (ht : 0 < t) :
    (hurwitzEvenFEPair 0).f_modif t = ((‖(hurwitzEvenFEPair 0).f_modif t‖ : ℝ) : ℂ) := by
  obtain ⟨hre, him⟩ := f_modif_nonneg ht
  set z := (hurwitzEvenFEPair 0).f_modif t
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre]

/-- The real log-weighted theta integrand of the strip-edge derivative. -/
def stripEdgeLogThetaIntegrand (t : ℝ) : ℝ :=
  t ^ ((1 / 2 : ℝ) - 1) * Real.log t * ‖(hurwitzEvenFEPair 0).f_modif t‖

theorem mellin_integrand_eq_ofReal {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ ((1 / 2 : ℂ) - 1) • (Real.log t • (hurwitzEvenFEPair 0).f_modif t) =
      ((stripEdgeLogThetaIntegrand t : ℝ) : ℂ) := by
  rw [f_modif_eq_ofReal_norm ht, stripEdgeLogThetaIntegrand, smul_eq_mul, Complex.real_smul]
  have hc : (t : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((t ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    push_cast
    rfl
  rw [hc]
  push_cast
  ring

theorem integrableOn_stripEdgeLogThetaIntegrand :
    IntegrableOn stripEdgeLogThetaIntegrand (Ioi 0) := by
  have h := mellin_log_f_modif_half.1
  have h' : IntegrableOn (fun t : ℝ => ((stripEdgeLogThetaIntegrand t : ℝ) : ℂ)) (Ioi 0) :=
    h.congr_fun (fun t ht => mellin_integrand_eq_ofReal ht) measurableSet_Ioi
  exact h'.re

theorem mellin_log_f_modif_half_eq :
    mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) (1 / 2) =
      ((∫ t in Ioi (0 : ℝ), stripEdgeLogThetaIntegrand t : ℝ) : ℂ) := by
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun t ht => mellin_integrand_eq_ofReal ht),
    integral_complex_ofReal]

theorem image_inv_Ioi_one : (fun x : ℝ => x⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext y
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ hx⟩
  · rintro ⟨hy0, hy1⟩
    exact ⟨y⁻¹, (one_lt_inv₀ hy0).mpr hy1, inv_inv y⟩

theorem hasDerivWithinAt_inv_Ioi_one :
    ∀ x ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(x ^ 2)⁻¹) (Ioi 1) x :=
  fun x hx => (hasDerivAt_inv (by linarith [mem_Ioi.mp hx] : x ≠ 0)).hasDerivWithinAt

theorem injOn_inv_Ioi_one : InjOn (fun x : ℝ => x⁻¹) (Ioi 1) :=
  fun a _ b _ hab => by simpa using congrArg (fun y : ℝ => y⁻¹) hab

/-- The reflected inner integrand: for `x > 1` the substitution `t = 1/x` turns the inner piece
into `−x⁻¹ log x (θ(x) − 1)`. -/
theorem abs_deriv_smul_inner_eq {x : ℝ} (hx : 1 < x) :
    |(-(x ^ 2)⁻¹)| • stripEdgeLogThetaIntegrand x⁻¹ =
      -(x⁻¹ * Real.log x * (evenKernel 0 x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hi0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹), smul_eq_mul,
    stripEdgeLogThetaIntegrand, norm_f_modif_eq_of_lt_one hi0 hi1,
    show (1 : ℝ) / x⁻¹ = x by rw [one_div, inv_inv], Real.log_inv]
  have hpow : x⁻¹ ^ ((1 / 2 : ℝ) - 1) * x⁻¹ ^ (-(1 / 2) : ℝ) = x := by
    rw [← Real.rpow_add hi0, show (1 / 2 : ℝ) - 1 + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      inv_inv]
  calc (x ^ 2)⁻¹ * (x⁻¹ ^ ((1 / 2 : ℝ) - 1) * -Real.log x *
        (x⁻¹ ^ (-(1 / 2) : ℝ) * (evenKernel 0 x - 1)))
      = (x ^ 2)⁻¹ * (x⁻¹ ^ ((1 / 2 : ℝ) - 1) * x⁻¹ ^ (-(1 / 2) : ℝ)) *
          (-Real.log x) * (evenKernel 0 x - 1) := by ring
    _ = -(x⁻¹ * Real.log x * (evenKernel 0 x - 1)) := by
        rw [hpow]
        field_simp

theorem integrableOn_inner_reflected :
    IntegrableOn (fun x : ℝ => -(x⁻¹ * Real.log x * (evenKernel 0 x - 1))) (Ioi 1) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    hasDerivWithinAt_inv_Ioi_one injOn_inv_Ioi_one stripEdgeLogThetaIntegrand).mp
    (by rw [image_inv_Ioi_one]
        exact integrableOn_stripEdgeLogThetaIntegrand.mono_set Ioo_subset_Ioi_self)
  exact h.congr_fun (fun x hx => abs_deriv_smul_inner_eq hx) measurableSet_Ioi

theorem integral_inner_reflected :
    ∫ t in Ioo (0 : ℝ) 1, stripEdgeLogThetaIntegrand t =
      ∫ x in Ioi (1 : ℝ), -(x⁻¹ * Real.log x * (evenKernel 0 x - 1)) := by
  rw [← image_inv_Ioi_one, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hasDerivWithinAt_inv_Ioi_one injOn_inv_Ioi_one]
  exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => abs_deriv_smul_inner_eq hx)

theorem outer_eq {x : ℝ} (hx : 1 < x) :
    stripEdgeLogThetaIntegrand x = x ^ ((1 / 2 : ℝ) - 1) * Real.log x * (evenKernel 0 x - 1) := by
  rw [stripEdgeLogThetaIntegrand, norm_f_modif_eq_of_one_lt hx]

/-- **Inversion of the inner half-line.**  The log-weighted Mellin integral at `1/2` is
`∫_1^∞ (x^{−1/2} − x^{−1}) log x (θ(x) − 1) dx`. -/
theorem integral_stripEdgeLogThetaIntegrand_eq :
    ∫ t in Ioi (0 : ℝ), stripEdgeLogThetaIntegrand t =
      ∫ x in Ioi (1 : ℝ), (x ^ ((1 / 2 : ℝ) - 1) - x⁻¹) * Real.log x * (evenKernel 0 x - 1) := by
  have hsplit : Ioo (0 : ℝ) 1 ∪ Ici 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioo, mem_Ici, mem_Ioi]
    constructor
    · rintro (⟨h0, _⟩ | h1)
      · exact h0
      · linarith
    · intro h0
      rcases lt_or_ge x 1 with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr h
  have hdisj : Disjoint (Ioo (0 : ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_le.mpr hx.2)
  have hint := integrableOn_stripEdgeLogThetaIntegrand
  rw [← hsplit, setIntegral_union hdisj measurableSet_Ici
    (hint.mono_set (by rw [← hsplit]; exact subset_union_left))
    (hint.mono_set (by rw [← hsplit]; exact subset_union_right)),
    integral_Ici_eq_integral_Ioi, integral_inner_reflected,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => outer_eq hx)]
  have hout : IntegrableOn
      (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) * Real.log x * (evenKernel 0 x - 1)) (Ioi 1) :=
    (hint.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun x hx => outer_eq hx)
      measurableSet_Ioi
  rw [add_comm, ← integral_add hout integrableOn_inner_reflected]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  ring

/-- The comparison integrand `2e^{−πx}·(2/5)(x−1)²e^{−9(x−1)/8}`. -/
def stripEdgeComparison (x : ℝ) : ℝ :=
  2 * Real.exp (-Real.pi * x) * (2 / 5 * (x - 1) ^ 2 * Real.exp (-(9 / 8 * (x - 1))))

/-- `∫_1^∞ 2e^{−πx}(2/5)(x−1)²e^{−9(x−1)/8} dx = (8/5) e^{−π}/(π + 9/8)³`. -/
theorem integral_stripEdgeComparison :
    ∫ x in Ioi (1 : ℝ), stripEdgeComparison x =
      8 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 := by
  have himg : (fun v : ℝ => v + 1) '' Ioi (0 : ℝ) = Ioi 1 := by
    rw [Set.image_add_const_Ioi, zero_add]
  have hderiv : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun v : ℝ => v + 1) 1 (Ioi 0) v :=
    fun v _ => ((hasDerivAt_id' v).add_const 1).hasDerivWithinAt
  have hinj : InjOn (fun v : ℝ => v + 1) (Ioi 0) := fun a _ b _ h => by simpa using h
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have hr : 0 < Real.pi + 9 / 8 := by positivity
  have hcongr : ∀ v ∈ Ioi (0 : ℝ), |(1 : ℝ)| • stripEdgeComparison (v + 1) =
      4 / 5 * Real.exp (-Real.pi) *
        (v ^ ((3 : ℝ) - 1) * Real.exp (-((Real.pi + 9 / 8) * v))) := by
    intro v hv
    have hv0 : 0 < v := hv
    rw [abs_one, one_smul, stripEdgeComparison, show (3 : ℝ) - 1 = (2 : ℕ) by norm_num,
      Real.rpow_natCast, show v + 1 - 1 = v by ring]
    have he : Real.exp (-Real.pi * (v + 1)) * Real.exp (-(9 / 8 * v)) =
        Real.exp (-Real.pi) * Real.exp (-((Real.pi + 9 / 8) * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc 2 * Real.exp (-Real.pi * (v + 1)) * (2 / 5 * v ^ 2 * Real.exp (-(9 / 8 * v)))
        = 4 / 5 * v ^ 2 * (Real.exp (-Real.pi * (v + 1)) * Real.exp (-(9 / 8 * v))) := by ring
      _ = _ := by rw [he]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hr,
    show (3 : ℝ) = ((2 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial,
    show ((2 : ℕ) : ℝ) + 1 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [Nat.factorial, one_div, inv_pow]
  field_simp
  norm_num

/-- The logarithmic weight floor: for `x > 1`,
`(2/5)(x−1)²e^{−9(x−1)/8} ≤ (x^{−1/2} − x^{−1}) log x`. -/
theorem logWeight_floor {x : ℝ} (hx : 1 < x) :
    2 / 5 * (x - 1) ^ 2 * Real.exp (-(9 / 8 * (x - 1))) ≤
      (x ^ ((1 / 2 : ℝ) - 1) - x⁻¹) * Real.log x := by
  set v := x - 1 with hvdef
  have hv : 0 < v := by rw [hvdef]; linarith
  have hx0 : 0 < x := by linarith
  have hxv : x = v + 1 := by rw [hvdef]; ring
  have hlog : 2 * v / (v + 2) ≤ Real.log x := by
    have h := GaloisForLFunctions.HTGeometry.two_mul_sub_one_div_add_one_le_log hx.le
    rwa [show x + 1 = v + 2 by rw [hxv]; ring] at h
  have hsqrt : (4 + 3 * v) / (4 + v) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_le_iff₀ (by positivity), hxv]
    nlinarith [pow_pos hv 3]
  have hrpow : x ^ ((1 / 2 : ℝ) - 1) = Real.sqrt x / x := by
    rw [Real.rpow_sub hx0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hw : 2 * v / ((4 + v) * x) ≤ x ^ ((1 / 2 : ℝ) - 1) - x⁻¹ := by
    rw [hrpow, div_sub' hx0.ne', le_div_iff₀ hx0]
    have : 2 * v / ((4 + v) * x) * x = (4 + 3 * v) / (4 + v) - 1 := by
      field_simp
      ring
    rw [this, mul_inv_cancel₀ hx0.ne']
    linarith
  have hT := Real.sum_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 9 / 8 * v) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.succ_eq_add_one, Nat.cast_mul, pow_zero, pow_one] at hT
  norm_num at hT
  set T := Real.exp (9 / 8 * v)
  have hTpos : 0 < T := Real.exp_pos _
  have hexp : Real.exp (-(9 / 8 * v)) = T⁻¹ := Real.exp_neg _
  have hpoly : (v + 1) * (v + 2) * (v + 4) ≤
      10 * (1 + 9 / 8 * v + (9 / 8 * v) ^ 2 / 2 + (9 / 8 * v) ^ 3 / 6 + (9 / 8 * v) ^ 4 / 24) := by
    nlinarith [sq_nonneg (v - 4 / 5), sq_nonneg (v ^ 2 - 1 / 2),
      mul_nonneg hv.le (sq_nonneg (v - 4 / 5)),
      mul_nonneg (mul_nonneg hv.le hv.le) (sq_nonneg (v - 4 / 5)), pow_nonneg hv.le 3,
      pow_nonneg hv.le 4]
  have hlow : 2 / 5 * v ^ 2 * T⁻¹ ≤ 2 * v / ((4 + v) * x) * (2 * v / (v + 2)) := by
    rw [hxv]
    rw [show 2 * v / ((4 + v) * (v + 1)) * (2 * v / (v + 2)) =
      4 * v ^ 2 / ((v + 1) * (v + 2) * (v + 4)) by field_simp; ring]
    have hD : (v + 1) * (v + 2) * (v + 4) / 10 ≤ T := by linarith
    have hDpos : 0 < (v + 1) * (v + 2) * (v + 4) / 10 := by positivity
    calc 2 / 5 * v ^ 2 * T⁻¹ = 2 / 5 * v ^ 2 / T := (div_eq_mul_inv _ _).symm
      _ ≤ 2 / 5 * v ^ 2 / ((v + 1) * (v + 2) * (v + 4) / 10) :=
          div_le_div_of_nonneg_left (by positivity) hDpos hD
      _ = 4 * v ^ 2 / ((v + 1) * (v + 2) * (v + 4)) := by field_simp; ring
  rw [hexp]
  calc 2 / 5 * v ^ 2 * T⁻¹ ≤ 2 * v / ((4 + v) * x) * (2 * v / (v + 2)) := hlow
    _ ≤ (x ^ ((1 / 2 : ℝ) - 1) - x⁻¹) * Real.log x :=
        mul_le_mul hw hlog (by positivity) (le_trans (by positivity) hw)

theorem integrableOn_stripEdgeKernelIntegrand :
    IntegrableOn
      (fun x : ℝ => (x ^ ((1 / 2 : ℝ) - 1) - x⁻¹) * Real.log x * (evenKernel 0 x - 1)) (Ioi 1) := by
  have hint := integrableOn_stripEdgeLogThetaIntegrand
  have hout : IntegrableOn
      (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) * Real.log x * (evenKernel 0 x - 1)) (Ioi 1) :=
    (hint.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun (fun x hx => outer_eq hx)
      measurableSet_Ioi
  refine (hout.add integrableOn_inner_reflected).congr_fun (fun x _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- **Lower bound for the log-weighted theta integral.** -/
theorem integral_stripEdgeLogThetaIntegrand_ge :
    8 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 ≤
      ∫ t in Ioi (0 : ℝ), stripEdgeLogThetaIntegrand t := by
  rw [integral_stripEdgeLogThetaIntegrand_eq, ← integral_stripEdgeComparison]
  refine integral_mono_of_nonneg ?_ integrableOn_stripEdgeKernelIntegrand ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x _ => ?_)
    simp only [Pi.zero_apply, stripEdgeComparison]
    positivity
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx1 : (1 : ℝ) < x := hx
    have hK := two_exp_le_evenKernel_zero_sub_one (by linarith : (0 : ℝ) < x)
    have hW := logWeight_floor hx1
    have hl0 : 0 ≤ 2 / 5 * (x - 1) ^ 2 * Real.exp (-(9 / 8 * (x - 1))) := by positivity
    simp only [stripEdgeComparison]
    calc 2 * Real.exp (-Real.pi * x) * (2 / 5 * (x - 1) ^ 2 * Real.exp (-(9 / 8 * (x - 1))))
        = (2 / 5 * (x - 1) ^ 2 * Real.exp (-(9 / 8 * (x - 1)))) *
            (2 * Real.exp (-Real.pi * x)) := by ring
      _ ≤ ((x ^ ((1 / 2 : ℝ) - 1) - x⁻¹) * Real.log x) * (evenKernel 0 x - 1) :=
          mul_le_mul hW hK (by positivity) (hl0.trans hW)

/-- **The strip-edge derivative floor**: `Re Λ₀'(1) ≥ (2/5) e^{−π}/(π + 9/8)³`. -/
theorem completedRiemannZeta₀_deriv_one_re_ge :
    2 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 ≤
      (deriv completedRiemannZeta₀ 1).re := by
  rw [hasDerivAt_completedRiemannZeta₀_one_mellin.deriv, mellin_log_f_modif_half_eq]
  have h4 : ((((∫ t in Ioi (0 : ℝ), stripEdgeLogThetaIntegrand t) : ℝ) : ℂ) / 4).re =
      (∫ t in Ioi (0 : ℝ), stripEdgeLogThetaIntegrand t) / 4 := by
    rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [h4]
  have := integral_stripEdgeLogThetaIntegrand_ge
  have hq : 2 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 =
      8 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 / 4 := by ring
  linarith

/-! ## Numerical constants -/

/-- `e^π ≤ 23.15`. -/
theorem exp_pi_le_twentyThree_fifteen : Real.exp Real.pi ≤ 23.15 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 3 < 2.7182818286 ^ 3 := by
    have he : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    exact pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
  have hx : |(0.141593 : ℝ)| ≤ 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hb := Real.exp_bound hx (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  have hb' := (abs_le.mp hb).2
  have hsplit : Real.exp 3.141593 = Real.exp 3 * Real.exp 0.141593 := by
    rw [← Real.exp_add]; norm_num
  have hmono : Real.exp Real.pi ≤ Real.exp 3.141593 :=
    Real.exp_le_exp.mpr Real.pi_lt_d6.le
  rw [hsplit] at hmono
  have hpos := Real.exp_pos 0.141593
  nlinarith [Real.exp_pos 3]

/-- **Certified strip-edge derivative floor**: `Re Λ₀'(1) ≥ 111/500000`. -/
theorem completedRiemannZeta₀_deriv_one_re_ge_num :
    (111 / 500000 : ℝ) ≤ (deriv completedRiemannZeta₀ 1).re := by
  refine le_trans ?_ completedRiemannZeta₀_deriv_one_re_ge
  have he : 1 / 23.15 ≤ Real.exp (-Real.pi) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) exp_pi_le_twentyThree_fifteen
  have hd : (Real.pi + 9 / 8) ^ 3 ≤ (3.141593 + 9 / 8) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.pi_lt_d6]) 3
  have hd0 : 0 < (Real.pi + 9 / 8) ^ 3 := by positivity
  calc (111 / 500000 : ℝ) ≤ 2 / 5 * (1 / 23.15) / (3.141593 + 9 / 8) ^ 3 := by norm_num
    _ ≤ 2 / 5 * Real.exp (-Real.pi) / (Real.pi + 9 / 8) ^ 3 :=
        div_le_div₀ (by positivity) (by linarith) hd0 hd

/-! ## The value `Λ₀(1)` -/

theorem harmonic_thirteen : (harmonic 13 : ℝ) = 1145993 / 360360 := by
  have h : harmonic 13 = 1145993 / 360360 := by
    simp [harmonic, Finset.sum_range_succ]
    norm_num
  rw [h]
  push_cast
  ring

/-- `log 3 ≥ log 2 + 2(1/5 + (1/5)³/3 + (1/5)⁵/5)`, from `log(3/2) = 2 artanh(1/5)`. -/
theorem log_three_ge_artanh :
    Real.log 2 + 2 * (1 / 5 + (1 / 5) ^ 3 / 3 + (1 / 5) ^ 5 / 5) ≤ Real.log 3 := by
  have h := GaloisForLFunctions.HTGeometry.sum_range_artanh_le_log_sub_log
    (x := 1 / 5) (by norm_num) (by norm_num) 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  have hl : Real.log (1 + 1 / 5) - Real.log (1 - 1 / 5) = Real.log 3 - Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num), ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  rw [hl] at h
  norm_num at h ⊢
  linarith

theorem completedRiemannZeta₀_one_eq_ofReal :
    completedRiemannZeta₀ 1 =
      ((1 + (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 : ℝ) : ℂ) := by
  rw [completedRiemannZeta₀_one, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_log (by positivity)]
  push_cast
  ring

theorem completedRiemannZeta₀_one_im : (completedRiemannZeta₀ 1).im = 0 := by
  rw [completedRiemannZeta₀_one_eq_ofReal, Complex.ofReal_im]

/-- **Certified strip-edge value**: `Λ₀(1) ≤ 93/4000`. -/
theorem completedRiemannZeta₀_one_re_le : (completedRiemannZeta₀ 1).re ≤ 93 / 4000 := by
  rw [completedRiemannZeta₀_one_eq_ofReal, Complex.ofReal_re]
  have hγ := GaloisForLFunctions.HTGeometry.eulerMascheroniConstant_le_harmonic_sub_log_add_half 13
  rw [harmonic_thirteen] at hγ
  have h27 : Real.log ((13 : ℕ) + 1 / 2 : ℝ) = 3 * Real.log 3 - Real.log 2 := by
    rw [show ((13 : ℕ) + 1 / 2 : ℝ) = 3 ^ 3 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h4π : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hπ : Real.log 3 + (2 - 12 / (Real.pi + 3)) ≤ Real.log Real.pi := by
    have h := GaloisForLFunctions.HTGeometry.two_mul_sub_one_div_add_one_le_log
      (x := Real.pi / 3) (by linarith [Real.pi_gt_three])
    rw [Real.log_div Real.pi_pos.ne' (by norm_num)] at h
    have he : 2 * (Real.pi / 3 - 1) / (Real.pi / 3 + 1) = 2 - 12 / (Real.pi + 3) := by
      field_simp
      ring
    linarith
  have hpi12 : 12 / (Real.pi + 3) ≤ 12 / (3.141592 + 3) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d6])
  have h3 := log_three_ge_artanh
  have h2 := Real.log_two_gt_d9
  rw [h27] at hγ
  rw [h4π]
  norm_num at hpi12 h3 h2 hγ ⊢
  linarith

end

end RHTower
