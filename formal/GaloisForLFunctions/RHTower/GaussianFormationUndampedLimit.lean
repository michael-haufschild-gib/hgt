import GaloisForLFunctions.RHTower.GaussianFormationZeroField
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# The undamped limit of the Gaussian zero field

The Gaussian formation `Φₓ` satisfies the exact zero-field law
`Φₓ'/Φₓ(s) = A(s) − A_{πx,2}(s) + Σ_ρ [e^{-πx}/(ρ−½) + E(πx, ρ−s)]`, with `A = h∞'/h∞` and
`E(y,a) = ∫₁^∞ e^{-yu²} u^{a-1} du`.  This file computes the limit `x → 0⁺` term by term.

* **Archimedean side** (`tendsto_gaussianArchimedeanCurrent_sub_MB`).  The Gauss series of the
  digamma function gives `A(z) = ½ − (log π)/2 − γ/2 + Σ_{n≥0} [1/(2n+4) − 1/(z+2n+2)]`
  (`hasSum_archimedeanSeriesTerm`): the trivial zeros `−2(n+1)` enter as poles.  Its Gaussian
  Mellin–Barnes transform is the same sum with every pole replaced by its germ
  `e^{-y}/(2n+4) − E(y, −s−2n−2)` (`hasSum_archimedeanMBTerm`).  Two steps of the recursion
  `E(y,a) = −e^{-y}/a + (2y/a) E(y,a+2)` bound each germ defect by `O(y^{1/2}/n²)`
  (`norm_germDefect_le`), so `A(s) − A_{y,c}(s) → 0` for `Re s > 0`.
* **Unconditional asymptotics** (`tendsto_logDeriv_gaussianFormation_sub_zeroGermField`).  For
  `Re s > 0`, `Φₓ'/Φₓ(s)` minus its nontrivial zero-germ field tends to `0`.
* **Zeros to the left** (`tendsto_tsum_zeroGerm`).  If every zero has `Re ρ ≤ θ < Re s < 2`, the
  germ field converges to `Σ_ρ [1/(ρ−½) + 1/(s−ρ)] = ξ'/ξ(s)`, by dominated convergence with the
  same two-step defect bound against `Σ |ρ−½|⁻²`.
* **Exact passage** (`tendsto_logDeriv_gaussianFormation_of_zeroFree`,
  `tendsto_logDeriv_gaussianFormation_of_riemannHypothesis`).  Hence `Φₓ'/Φₓ(s) → ξ'/ξ(s)` on
  `max θ 0 < Re s < 2`; under RH on `½ < Re s < 2`.
* **Uniformity** (`eventually_norm_logDeriv_gaussianFormation_sub_logDeriv_xi_le`).  Both defect
  bounds are explicit (`norm_gaussianArchimedeanCurrent_sub_MB_le`,
  `norm_tsum_zeroGerm_sub_logDeriv_xi_le`) and monotone in `‖s‖`, `1/(Re s − θ)`,
  `1/(2 − Re s)`, so the convergence is uniform on every bounded set kept away from `Re s = θ`
  and `Re s = 2`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- `∫₁^∞ e^{-yu²} u^r du ≤ ½ Γ((r+1)/2) y^{-(r+1)/2}` for `r > -1`. -/
theorem integral_exp_neg_sq_rpow_Ioi_one_le {y r : ℝ} (hy : 0 < y) (hr : -1 < r) :
    ∫ u in Ioi (1 : ℝ), u ^ r * Real.exp (-y * u ^ 2) ≤
      y ^ (-(r + 1) / 2) * (1 / 2) * Real.Gamma ((r + 1) / 2) := by
  have hfull := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := r) (b := y) (by norm_num) hr hy
  have hint : IntegrableOn (fun u : ℝ => u ^ r * Real.exp (-y * u ^ (2 : ℝ))) (Ioi 0) := by
    have := integrable_rpow_mul_exp_neg_mul_sq hy hr
    refine (this.integrableOn).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [Real.rpow_two]
  rw [← hfull]
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  calc ∫ u in Ioi (1 : ℝ), u ^ r * Real.exp (-y * u ^ 2)
      = ∫ u in Ioi (1 : ℝ), u ^ r * Real.exp (-y * u ^ (2 : ℝ)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        simp only [Real.rpow_two]
    _ ≤ ∫ u in Ioi (0 : ℝ), u ^ r * Real.exp (-y * u ^ (2 : ℝ)) := by
        refine setIntegral_mono_set hint ?_ hsub.eventuallyLE
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (Real.exp_pos _).le

/-- Uniform bound `‖E(y, b)‖ ≤ ½ Γ((r+1)/2) y^{-(r+1)/2}` whenever `Re b - 1 ≤ r`, `r > -1`. -/
theorem norm_gaussianIncompleteMellin_le {y r : ℝ} (hy : 0 < y) (hr : -1 < r) {b : ℂ}
    (hb : b.re - 1 ≤ r) :
    ‖gaussianIncompleteMellin y b‖ ≤ y ^ (-(r + 1) / 2) * (1 / 2) * Real.Gamma ((r + 1) / 2) := by
  refine le_trans ?_ (integral_exp_neg_sq_rpow_Ioi_one_le hy hr)
  rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine setIntegral_mono_on ?_ ((integrableOn_rpow_mul_exp_neg_sq_Ioi_one hy r))
    measurableSet_Ioi fun u hu => ?_
  · exact (integrableOn_gaussian_cpow_Ioi_one hy b).norm
  · have hu0 : 0 < u := lt_trans one_pos hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hu0, mul_comm]
    simp only [Complex.sub_re, Complex.one_re]
    gcongr
    exact le_of_lt hu


/-- **Zero-germ defect bound.**  For `0 < y ≤ 1`, `0 < η ≤ 1`, `Re a ≤ -η`, `a + 2 ≠ 0`, `κ ≠ 0`:
`‖(e^{-y}-1)/κ + E(y,a) + 1/a‖ ≤ y‖κ-a‖/(‖κ‖‖a‖) + (2y + 2Γ((4-η)/2) y^{η/2})/(‖a‖‖a+2‖)`.
Two steps of the incomplete-Gamma recursion. -/
theorem norm_germDefect_le {y η : ℝ} (hy : 0 < y) (hη : 0 < η) (hη1 : η ≤ 1)
    {κ a : ℂ} (hκ : κ ≠ 0) (ha : a.re ≤ -η) (ha2 : a + 2 ≠ 0) :
    ‖((Real.exp (-y) : ℂ) - 1) / κ + gaussianIncompleteMellin y a + a⁻¹‖ ≤
      y * ‖κ - a‖ / (‖κ‖ * ‖a‖) +
        (2 * y + 2 * Real.Gamma ((4 - η) / 2) * y ^ (η / 2)) / (‖a‖ * ‖a + 2‖) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; linarith
  have hrec1 := gaussianIncompleteMellin_recursion hy ha0
  have hrec2 := gaussianIncompleteMellin_recursion hy ha2
  set E4 := gaussianIncompleteMellin y (a + 2 + 2) with hE4
  set e : ℂ := (Real.exp (-y) : ℂ) with he
  have hident : (e - 1) / κ + gaussianIncompleteMellin y a + a⁻¹ =
      (1 - e) * (κ - a) / (κ * a) - 2 * y * e / (a * (a + 2)) +
        4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2)) := by
    rw [hrec1, hrec2]
    field_simp
    ring
  rw [hident]
  -- the three pieces
  have hey : ‖1 - e‖ ≤ y := by
    rw [he, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [Real.exp_le_one_iff.2 (by linarith : -y ≤ 0)])]
    linarith [Real.add_one_le_exp (-y)]
  have he1 : ‖e‖ ≤ 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hE4bound : ‖E4‖ ≤ y ^ (-((3 - η) + 1) / 2) * (1 / 2) * Real.Gamma (((3 - η) + 1) / 2) :=
    norm_gaussianIncompleteMellin_le hy (by linarith) (by simp; linarith)
  have hpow : (y : ℝ) ^ 2 * y ^ (-((3 - η) + 1) / 2) = y ^ (η / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 1; push_cast; ring
  have hG : Real.Gamma (((3 - η) + 1) / 2) = Real.Gamma ((4 - η) / 2) := by
    congr 1; ring
  have hGpos : 0 < Real.Gamma ((4 - η) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have ha0n : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have ha2n : 0 < ‖a + 2‖ := norm_pos_iff.2 ha2
  have hκn : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
  have t1 : ‖(1 - e) * (κ - a) / (κ * a)‖ ≤ y * ‖κ - a‖ / (‖κ‖ * ‖a‖) := by
    rw [norm_div, norm_mul, norm_mul]
    gcongr
  have t2 : ‖2 * (y : ℂ) * e / (a * (a + 2))‖ ≤ 2 * y / (‖a‖ * ‖a + 2‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, Complex.norm_two]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    calc 2 * y * ‖e‖ ≤ 2 * y * 1 := by gcongr
      _ = 2 * y := mul_one _
  have t3 : ‖4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2))‖ ≤
      2 * Real.Gamma ((4 - η) / 2) * y ^ (η / 2) / (‖a‖ * ‖a + 2‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    calc 4 * y ^ 2 * ‖E4‖ ≤ 4 * y ^ 2 *
          (y ^ (-((3 - η) + 1) / 2) * (1 / 2) * Real.Gamma (((3 - η) + 1) / 2)) := by
          gcongr
      _ = 2 * Real.Gamma ((4 - η) / 2) * y ^ (η / 2) := by
          rw [hG, ← hpow]; ring
  calc ‖(1 - e) * (κ - a) / (κ * a)‖ + ‖2 * (y : ℂ) * e / (a * (a + 2))‖ +
        ‖4 * (y : ℂ) ^ 2 * E4 / (a * (a + 2))‖
      ≤ y * ‖κ - a‖ / (‖κ‖ * ‖a‖) + 2 * y / (‖a‖ * ‖a + 2‖) +
          2 * Real.Gamma ((4 - η) / 2) * y ^ (η / 2) / (‖a‖ * ‖a + 2‖) := by
        gcongr
    _ = _ := by rw [add_assoc, ← add_div]


/-- `‖κ - w‖⁻¹ ≤ max 2 (2‖w‖/m) · ‖κ‖⁻¹` whenever `‖κ - w‖ ≥ m > 0`. -/
theorem inv_norm_sub_le_of_ge {κ w : ℂ} {m : ℝ} (hm : 0 < m) (hκ : 0 < ‖κ‖)
    (hge : m ≤ ‖κ - w‖) :
    ‖κ - w‖⁻¹ ≤ max 2 (2 * ‖w‖ / m) * ‖κ‖⁻¹ := by
  have hpos : 0 < ‖κ - w‖ := lt_of_lt_of_le hm hge
  by_cases hcase : 2 * ‖w‖ ≤ ‖κ‖
  · have hlow : ‖κ‖ / 2 ≤ ‖κ - w‖ := by
      have := norm_sub_norm_le κ w
      linarith
    calc ‖κ - w‖⁻¹ ≤ (‖κ‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 * ‖κ‖⁻¹ := by field_simp
      _ ≤ max 2 (2 * ‖w‖ / m) * ‖κ‖⁻¹ := by gcongr; exact le_max_left _ _
  · push Not at hcase
    calc ‖κ - w‖⁻¹ ≤ m⁻¹ := inv_anti₀ hm hge
      _ = (‖κ‖ / m) * ‖κ‖⁻¹ := by field_simp
      _ ≤ (2 * ‖w‖ / m) * ‖κ‖⁻¹ := by gcongr
      _ ≤ max 2 (2 * ‖w‖ / m) * ‖κ‖⁻¹ := by gcongr; exact le_max_right _ _

/-- **Quantitative zero-germ convergence.**  If every zero of `ξ` has `Re ρ ≤ θ`, `0 < η ≤ 1`,
`θ + η ≤ Re s ≤ 2 − δ` and `y > 0`, the germ field differs from `ξ'/ξ(s)` by at most
`(y‖s−½‖C₁ + (2y + 2Γ((4−η)/2)y^{η/2})C₁C₂) Σ_ρ |ρ−½|^{-2}`, where `C₁ = max 2 (2‖s−½‖/η)` and
`C₂ = max 2 (2‖s−5/2‖/δ)`. -/
theorem norm_tsum_zeroGerm_sub_logDeriv_xi_le {θ η δ y : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ) (hy : 0 < y)
    {s : ℂ} (hs : θ + η ≤ s.re) (hs2 : s.re ≤ 2 - δ) :
    ‖(∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin y (xiZero q - s))) - logDeriv xi s‖ ≤
      (y * ‖s - 1 / 2‖ * max 2 (2 * ‖s - 1 / 2‖ / η) +
        (2 * y + 2 * Real.Gamma ((4 - η) / 2) * y ^ (η / 2)) *
          (max 2 (2 * ‖s - 1 / 2‖ / η) * max 2 (2 * ‖s - 5 / 2‖ / δ))) *
        ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  have hxis : xi s ≠ 0 := by
    intro h; have := hθ s h; linarith
  rw [logDeriv_xi_eq_partialFraction hxis]
  have hre : ∀ q : XiZeroCopy, (xiZero q - s).re ≤ -η := by
    intro q
    have := hθ _ (xi_xiZero q)
    simp; linarith
  have hκ : ∀ q : XiZeroCopy, 0 < ‖xiZero q - 1 / 2‖ := fun q =>
    lt_trans one_pos (one_lt_norm_xiZero_sub_half q)
  have hm1 : ∀ q : XiZeroCopy, η ≤ ‖(xiZero q - 1 / 2) - (s - 1 / 2)‖ := by
    intro q
    rw [show (xiZero q - 1 / 2) - (s - 1 / 2) = xiZero q - s by ring]
    have h1 := Complex.abs_re_le_norm (xiZero q - s)
    have h2 := hre q
    have : |(xiZero q - s).re| ≥ η := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hm2 : ∀ q : XiZeroCopy, δ ≤ ‖(xiZero q - 1 / 2) - (s - 5 / 2)‖ := by
    intro q
    rw [show (xiZero q - 1 / 2) - (s - 5 / 2) = xiZero q - s + 2 by ring]
    have hρ : 0 < (xiZero q).re := (xi_divisor_support_re_mem_open_unit q.1).1
    have h1 := Complex.re_le_norm (xiZero q - s + 2)
    simp at h1
    linarith
  set C1 : ℝ := max 2 (2 * ‖s - 1 / 2‖ / η) with hC1
  set C2 : ℝ := max 2 (2 * ‖s - 5 / 2‖ / δ) with hC2
  have hC1pos : 0 ≤ C1 := le_trans (by norm_num) (le_max_left _ _)
  have hC2pos : 0 ≤ C2 := le_trans (by norm_num) (le_max_left _ _)
  have hinv1 : ∀ q : XiZeroCopy, ‖xiZero q - s‖⁻¹ ≤ C1 * ‖xiZero q - 1 / 2‖⁻¹ := by
    intro q
    have := inv_norm_sub_le_of_ge hη0 (hκ q) (hm1 q)
    rwa [show (xiZero q - 1 / 2) - (s - 1 / 2) = xiZero q - s by ring] at this
  have hinv2 : ∀ q : XiZeroCopy, ‖xiZero q - s + 2‖⁻¹ ≤ C2 * ‖xiZero q - 1 / 2‖⁻¹ := by
    intro q
    have := inv_norm_sub_le_of_ge hδ (hκ q) (hm2 q)
    rwa [show (xiZero q - 1 / 2) - (s - 5 / 2) = xiZero q - s + 2 by ring] at this
  set G : ℝ := Real.Gamma ((4 - η) / 2) with hGdef
  have hG0 : 0 ≤ G := (Real.Gamma_pos_of_pos (by linarith)).le
  set W : ℝ := y * ‖s - 1 / 2‖ * C1 + (2 * y + 2 * G * y ^ (η / 2)) * (C1 * C2) with hW
  have ha2 : ∀ q : XiZeroCopy, xiZero q - s + 2 ≠ 0 := by
    intro q h; have := hm2 q
    rw [show (xiZero q - 1 / 2) - (s - 5 / 2) = xiZero q - s + 2 by ring, h, norm_zero] at this
    linarith
  set target : XiZeroCopy → ℂ := fun q => (xiZero q - 1 / 2)⁻¹ + (s - xiZero q)⁻¹
    with htarget_def
  set defect : XiZeroCopy → ℂ := fun q => ((Real.exp (-y) : ℂ) - 1) / (xiZero q - 1 / 2) +
      gaussianIncompleteMellin y (xiZero q - s) + (xiZero q - s)⁻¹ with hdefect_def
  have hsplit : ∀ q : XiZeroCopy,
      (Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s) =
        target q + defect q := by
    intro q
    simp only [htarget_def, hdefect_def]
    have hsρ : s - xiZero q = -(xiZero q - s) := by ring
    rw [hsρ, inv_neg]
    ring
  have hdefect : ∀ q : XiZeroCopy, ‖defect q‖ ≤ W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    have hd := norm_germDefect_le hy hη0 hη1 (κ := xiZero q - 1 / 2) (a := xiZero q - s)
      (by intro h; have := hκ q; rw [h, norm_zero] at this; linarith) (hre q) (ha2 q)
    have hκa : xiZero q - 1 / 2 - (xiZero q - s) = s - 1 / 2 := by ring
    rw [hκa] at hd
    refine hd.trans ?_
    have ha := hinv1 q
    have hb := hinv2 q
    have hsimp1 : y * ‖s - 1 / 2‖ / (‖xiZero q - 1 / 2‖ * ‖xiZero q - s‖) =
        y * ‖s - 1 / 2‖ * ‖xiZero q - 1 / 2‖⁻¹ * ‖xiZero q - s‖⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]; ring
    have hsimp2 : (2 * y + 2 * G * y ^ (η / 2)) / (‖xiZero q - s‖ * ‖xiZero q - s + 2‖) =
        (2 * y + 2 * G * y ^ (η / 2)) * ‖xiZero q - s‖⁻¹ * ‖xiZero q - s + 2‖⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]; ring
    rw [hsimp1, hsimp2, norm_inv]
    have hpow0 : 0 ≤ y ^ (η / 2) := Real.rpow_nonneg hy.le _
    have hA : 0 ≤ 2 * y + 2 * G * y ^ (η / 2) := by positivity
    calc y * ‖s - 1 / 2‖ * ‖xiZero q - 1 / 2‖⁻¹ * ‖xiZero q - s‖⁻¹ +
          (2 * y + 2 * G * y ^ (η / 2)) * ‖xiZero q - s‖⁻¹ * ‖xiZero q - s + 2‖⁻¹
        ≤ y * ‖s - 1 / 2‖ * ‖xiZero q - 1 / 2‖⁻¹ * (C1 * ‖xiZero q - 1 / 2‖⁻¹) +
          (2 * y + 2 * G * y ^ (η / 2)) * (C1 * ‖xiZero q - 1 / 2‖⁻¹) *
            (C2 * ‖xiZero q - 1 / 2‖⁻¹) := by
          gcongr
      _ = _ := by rw [hW]; ring
  have htarget : ∀ q : XiZeroCopy,
      ‖target q‖ ≤ ‖s - 1 / 2‖ * C1 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
    intro q
    have hk0 : xiZero q - 1 / 2 ≠ 0 := by
      intro h; have := hκ q; rw [h, norm_zero] at this; linarith
    have hs0 : xiZero q - s ≠ 0 := by
      intro h; have := hm1 q
      rw [show (xiZero q - 1 / 2) - (s - 1 / 2) = xiZero q - s by ring, h, norm_zero] at this
      linarith
    have heq : target q = (s - 1 / 2) * (xiZero q - 1 / 2)⁻¹ * (xiZero q - s)⁻¹ * (-1) := by
      simp only [htarget_def]
      have h1 : s - xiZero q = -(xiZero q - s) := by ring
      have h2 : s - 1 / 2 = (xiZero q - 1 / 2) - (xiZero q - s) := by ring
      rw [h1, h2]
      generalize xiZero q - 1 / 2 = κ at hk0 ⊢
      generalize xiZero q - s = a at hs0 ⊢
      field_simp
      ring
    rw [heq, norm_mul, norm_mul, norm_mul, norm_neg, norm_one, mul_one, norm_inv, norm_inv]
    have := hinv1 q
    calc ‖s - 1 / 2‖ * ‖xiZero q - 1 / 2‖⁻¹ * ‖xiZero q - s‖⁻¹
        ≤ ‖s - 1 / 2‖ * ‖xiZero q - 1 / 2‖⁻¹ * (C1 * ‖xiZero q - 1 / 2‖⁻¹) := by gcongr
      _ = ‖s - 1 / 2‖ * C1 * ‖xiZero q - 1 / 2‖⁻¹ ^ 2 := by ring
  have hw := summable_norm_inv_xiZero_sub_half_sq
  have hsumT : Summable target := Summable.of_norm_bounded (hw.mul_left _) htarget
  have hsumDn : Summable (fun q => ‖defect q‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hdefect (hw.mul_left W)
  have hsumD : Summable defect := hsumDn.of_norm
  rw [tsum_congr hsplit, hsumT.tsum_add hsumD]
  change ‖∑' q, target q + ∑' q, defect q - ∑' q, target q‖ ≤ _
  rw [add_sub_cancel_left]
  calc ‖∑' q, defect q‖ ≤ ∑' q, ‖defect q‖ := norm_tsum_le_tsum_norm hsumDn
    _ ≤ ∑' q, W * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := hsumDn.tsum_le_tsum hdefect (hw.mul_left W)
    _ = W * ∑' q, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := tsum_mul_left

private theorem tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun y : ℝ => y ^ p) (𝓝[>] 0) (𝓝 0) := by
  have hc := Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rwa [Real.zero_rpow hp.ne'] at this

/-- **Undamped limit of the nontrivial zero germs.**  If every zero of `ξ` has `Re ρ ≤ θ` and
`θ < Re s < 2`, then `Σ_ρ [e^{-y}/(ρ-½) + E(y,ρ-s)] → Σ_ρ [1/(ρ-½) + 1/(s-ρ)] = ξ'/ξ(s)` as
`y → 0⁺`. -/
theorem tendsto_tsum_zeroGerm {θ : ℝ} (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {s : ℂ}
    (hs : θ < s.re) (hs2 : s.re < 2) :
    Tendsto (fun y : ℝ => ∑' q : XiZeroCopy,
        ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s)))
      (𝓝[>] 0) (𝓝 (logDeriv xi s)) := by
  set η : ℝ := min (s.re - θ) 1 with hη
  have hη0 : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hsη : θ + η ≤ s.re := by have := min_le_left (s.re - θ) 1; linarith
  have hδ : 0 < 2 - s.re := by linarith
  set C1 : ℝ := max 2 (2 * ‖s - 1 / 2‖ / η)
  set C2 : ℝ := max 2 (2 * ‖s - 5 / 2‖ / (2 - s.re))
  set G : ℝ := Real.Gamma ((4 - η) / 2)
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _)
    (g := fun y => (y * ‖s - 1 / 2‖ * C1 + (2 * y + 2 * G * y ^ (η / 2)) * (C1 * C2)) * S) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact norm_tsum_zeroGerm_sub_logDeriv_xi_le hθ hη0 hη1 hδ hy hsη (by linarith)
  · have h0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    have h1 := tendsto_rpow_nhdsGT_zero (p := η / 2) (by positivity)
    have := ((((h0.mul_const ‖s - 1 / 2‖).mul_const C1).add
      (((h0.const_mul 2).add (h1.const_mul (2 * G))).mul_const (C1 * C2))).mul_const S)
    simpa using this

/-! ## The archimedean side: trivial zeros -/

/-- `1/(2n+4) − 1/(z+2n+2)`: the partial fraction of the trivial zero `−2(n+1)`. -/
def trivialZeroPoleTerm (z : ℂ) (n : ℕ) : ℂ := 1 / (2 * (n : ℂ) + 4) - 1 / (z + 2 * n + 2)

/-- The constant `½ − (log π)/2 − γ/2` of the archimedean partial-fraction expansion. -/
def gaussianArchimedeanConstant : ℂ :=
  1 / 2 - Complex.log (Real.pi : ℂ) / 2 - (Real.eulerMascheroniConstant : ℂ) / 2

/-- Terms of the archimedean partial-fraction expansion: the constant, then the trivial zeros. -/
def archimedeanSeriesTerm (z : ℂ) : ℕ → ℂ
  | 0 => gaussianArchimedeanConstant
  | n + 1 => trivialZeroPoleTerm z n

theorem trivialZeroPoleTerm_eq_half_gauss (z : ℂ) (n : ℕ) :
    trivialZeroPoleTerm z n = gaussDigammaSeriesTerm (z / 2) (n + 1) / 2 := by
  unfold trivialZeroPoleTerm gaussDigammaSeriesTerm
  have h1 : z + 2 * (n : ℂ) + 2 = 2 * (z / 2 + ((n + 1 : ℕ) : ℂ)) := by push_cast; ring
  have h2 : 2 * (n : ℂ) + 4 = 2 * (((n + 1 : ℕ) : ℂ) + 1) := by push_cast; ring
  rw [h1, h2]
  simp only [one_div, mul_inv]
  ring

/-- **Archimedean partial fractions.**  On `Re z > 0`,
`A(z) = ½ − (log π)/2 − γ/2 + Σ_{n≥0} [1/(2n+4) − 1/(z+2n+2)]`. -/
theorem hasSum_archimedeanSeriesTerm {z : ℂ} (hz : 0 < z.re) :
    HasSum (archimedeanSeriesTerm z) (gaussianArchimedeanCurrent z) := by
  have hhalf : 0 < (z / 2).re := by
    rw [Complex.div_ofNat_re]; linarith
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hsum := summable_gaussDigammaSeriesTerm hhalf
  have htail : HasSum (fun n : ℕ => archimedeanSeriesTerm z (n + 1))
      ((∑' n : ℕ, gaussDigammaSeriesTerm (z / 2) (n + 1)) / 2) := by
    simp only [archimedeanSeriesTerm, trivialZeroPoleTerm_eq_half_gauss]
    exact ((summable_nat_add_iff 1).2 hsum).hasSum.div_const 2
  have hval : gaussianArchimedeanCurrent z =
      gaussianArchimedeanConstant + (∑' n : ℕ, gaussDigammaSeriesTerm (z / 2) (n + 1)) / 2 := by
    rw [gaussianArchimedeanCurrent, ← logDeriv_gaussianArchimedeanHalfFactor_eq_gammaReal hz,
      logDeriv_gaussianArchimedeanHalfFactor_eq hz, digamma_eq_neg_euler_add_tsum_gauss hhalf,
      hsum.tsum_eq_zero_add]
    unfold gaussianArchimedeanConstant gaussDigammaSeriesTerm
    push_cast
    simp only [zero_add, add_zero, div_one, one_div]
    field_simp
    ring
  rw [hval]
  exact htail.zero_add

theorem norm_trivialZeroPoleTerm_le {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖trivialZeroPoleTerm z n‖ ≤ ‖z - 2‖ / ((n : ℝ) + 1) ^ 2 := by
  have hD1r : (2 * (n : ℂ) + 4) = ((2 * (n : ℝ) + 4 : ℝ) : ℂ) := by push_cast; ring
  have hD1 : (2 * (n : ℂ) + 4) ≠ 0 := by
    rw [hD1r]; exact_mod_cast (by positivity : (2 * (n : ℝ) + 4) ≠ 0)
  have hD2re : (n : ℝ) + 1 ≤ (z + 2 * (n : ℂ) + 2).re := by simp; linarith
  have hD2 : z + 2 * (n : ℂ) + 2 ≠ 0 := by
    intro h; rw [h] at hD2re; simp at hD2re; linarith
  have heq : trivialZeroPoleTerm z n = (z - 2) / ((2 * (n : ℂ) + 4) * (z + 2 * n + 2)) := by
    unfold trivialZeroPoleTerm; field_simp; ring
  rw [heq, norm_div, norm_mul]
  have hn1 : ‖(2 * (n : ℂ) + 4)‖ = 2 * n + 4 := by
    rw [hD1r, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hn2 : (n : ℝ) + 1 ≤ ‖z + 2 * (n : ℂ) + 2‖ := hD2re.trans (Complex.re_le_norm _)
  rw [hn1]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem norm_archimedeanSeriesTerm_le {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ‖archimedeanSeriesTerm z m‖ ≤
      (‖gaussianArchimedeanConstant‖ + 4 * ‖z - 2‖) / ((m : ℝ) + 1) ^ 2 := by
  cases m with
  | zero =>
    simp only [archimedeanSeriesTerm, Nat.cast_zero, zero_add, one_pow, div_one]
    exact le_add_of_nonneg_right (by positivity)
  | succ n =>
    simp only [archimedeanSeriesTerm]
    refine (norm_trivialZeroPoleTerm_le hz n).trans ?_
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ ‖z - 2‖ := norm_nonneg _
    have hC : 0 ≤ ‖gaussianArchimedeanConstant‖ := norm_nonneg _
    nlinarith [mul_nonneg h0 (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ) ^ 2 + 4 * n),
      mul_nonneg hC (sq_nonneg ((n : ℝ) + 1))]

/-- Archimedean Mellin–Barnes terms: `e^{-y}·const`, then `e^{-y}/(2n+4) − E(y, −s−2n−2)`. -/
def archimedeanMBTerm (y : ℝ) (s : ℂ) : ℕ → ℂ
  | 0 => (Real.exp (-y) : ℂ) * gaussianArchimedeanConstant
  | n + 1 => (Real.exp (-y) : ℂ) / (2 * (n : ℂ) + 4) - gaussianIncompleteMellin y (-s - 2 * n - 2)

private theorem summable_one_div_nat_add_one_sq : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

/-- **Archimedean Mellin–Barnes expansion.**  For `y, c > 0` and `Re s + c > 0`, the archimedean
transform is the sum of `e^{-y}·const` and the trivial-zero germs `e^{-y}/(2n+4) − E(y,−s−2n−2)`. -/
theorem hasSum_archimedeanMBTerm {y c : ℝ} (hy : 0 < y) (hc : 0 < c) {s : ℂ} (hs : 0 < s.re + c) :
    HasSum (archimedeanMBTerm y s) (gaussianArchimedeanMB y c s) := by
  set K : ℝ → ℂ := fun v => gaussianMBKernel y (c + v * I) with hK
  set F : ℕ → ℝ → ℂ := fun m v => K v * archimedeanSeriesTerm (s + (c + v * I)) m with hF
  have hzre : ∀ v : ℝ, 0 < (s + (c + v * I)).re := by intro v; simp; linarith
  set A : ℝ := ‖s + c - 2‖ with hA
  have hzb : ∀ v : ℝ, ‖s + (c + v * I) - 2‖ ≤ (A + 1) * (1 + |v|) := by
    intro v
    have h0 : s + (c + v * I) - 2 = (s + c - 2) + v * I := by ring
    rw [h0]
    have h1 : ‖(s + c - 2) + v * I‖ ≤ A + |v| := by
      refine (norm_add_le _ _).trans ?_
      rw [hA, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hA0 : 0 ≤ A := norm_nonneg _
    nlinarith [abs_nonneg v]
  set B : ℝ := ‖gaussianArchimedeanConstant‖ + 4 * (A + 1) with hB
  have hFbound : ∀ m v, ‖F m v‖ ≤ B * (1 / ((m : ℝ) + 1) ^ 2) * (‖K v‖ * (1 + |v|) ^ 1) := by
    intro m v
    simp only [hF, norm_mul]
    have h := norm_archimedeanSeriesTerm_le (hzre v) m
    have hb : ‖gaussianArchimedeanConstant‖ + 4 * ‖s + (c + v * I) - 2‖ ≤ B * (1 + |v|) := by
      rw [hB]
      have := hzb v
      have hC : 0 ≤ ‖gaussianArchimedeanConstant‖ := norm_nonneg _
      nlinarith [abs_nonneg v]
    have hm : 0 < ((m : ℝ) + 1) ^ 2 := by positivity
    calc ‖K v‖ * ‖archimedeanSeriesTerm (s + (c + v * I)) m‖
        ≤ ‖K v‖ * ((‖gaussianArchimedeanConstant‖ + 4 * ‖s + (c + v * I) - 2‖) /
            ((m : ℝ) + 1) ^ 2) := by gcongr
      _ ≤ ‖K v‖ * (B * (1 + |v|) / ((m : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by ring
  have hKcont : Continuous K := continuous_gaussianMBKernel_line hy hc
  have hFcont : ∀ m, Continuous (F m) := by
    intro m
    refine hKcont.mul ?_
    cases m with
    | zero => exact continuous_const
    | succ n =>
      simp only [archimedeanSeriesTerm, trivialZeroPoleTerm]
      refine continuous_const.sub (continuous_const.div (by fun_prop) fun v => ?_)
      intro h0
      have h1 := hzre v
      have hre := congrArg Complex.re h0
      simp at hre
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp at h1
      linarith
  have hKint := integrable_norm_gaussianMBKernel_mul_pow hy hc 1
  have hFint : ∀ m, Integrable (F m) := fun m =>
    (hKint.const_mul (B * (1 / ((m : ℝ) + 1) ^ 2))).mono' (hFcont m).aestronglyMeasurable
      (Eventually.of_forall (hFbound m))
  set I1 : ℝ := ∫ v : ℝ, ‖K v‖ * (1 + |v|) ^ 1 with hI1
  have hsumm : Summable (fun m => ∫ v : ℝ, ‖F m v‖) := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun v => norm_nonneg _)
      (fun m => ?_) ((summable_one_div_nat_add_one_sq.mul_left B).mul_right I1)
    calc ∫ v : ℝ, ‖F m v‖ ≤ ∫ v : ℝ, B * (1 / ((m : ℝ) + 1) ^ 2) * (‖K v‖ * (1 + |v|) ^ 1) :=
          integral_mono (hFint m).norm (hKint.const_mul _) (hFbound m)
      _ = B * (1 / ((m : ℝ) + 1) ^ 2) * I1 := integral_const_mul _ _
  have hhas := hasSum_integral_of_summable_integral_norm hFint hsumm
  have hpoint : ∀ v : ℝ, ∑' m, F m v = K v * gaussianArchimedeanCurrent (s + (c + v * I)) :=
    fun v => ((hasSum_archimedeanSeriesTerm (hzre v)).mul_left (K v)).tsum_eq
  have hint_eq : ∫ v : ℝ, ∑' m, F m v =
      ∫ v : ℝ, gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I)) :=
    integral_congr_ae (Eventually.of_forall hpoint)
  rw [hint_eq] at hhas
  have hMB := hhas.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  rw [← gaussianArchimedeanMB] at hMB
  have hKint1 : Integrable K := integrable_gaussianMBKernel_line hy hc
  have hterm : ∀ m, ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, F m v = archimedeanMBTerm y s m := by
    intro m
    cases m with
    | zero =>
      simp only [archimedeanMBTerm, hF, archimedeanSeriesTerm]
      rw [integral_mul_const, ← mul_assoc, gaussianMBKernel_line_integral hy hc]
    | succ n =>
      set a : ℂ := -s - 2 * n - 2 with ha_def
      have ha : a.re < c := by
        rw [ha_def]; simp
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hFn : F (n + 1) = fun v => K v * (2 * (n : ℂ) + 4)⁻¹ - K v / ((c + v * I) - a) := by
        funext v
        simp only [hF, archimedeanSeriesTerm, trivialZeroPoleTerm]
        have : (c : ℂ) + v * I - a = s + (c + v * I) + 2 * n + 2 := by rw [ha_def]; ring
        rw [this]; ring
      have hint2 : Integrable (fun v : ℝ => K v / ((c + v * I) - a)) := by
        have : (fun v : ℝ => K v / ((c + v * I) - a)) =
            fun v => K v * (2 * (n : ℂ) + 4)⁻¹ - F (n + 1) v := by
          rw [hFn]; funext v; ring
        rw [this]
        exact (hKint1.mul_const _).sub (hFint (n + 1))
      rw [hFn, integral_sub (hKint1.mul_const _) hint2, integral_mul_const, mul_sub, ← mul_assoc,
        gaussianMBKernel_line_integral hy hc]
      simp only [archimedeanMBTerm]
      rw [← ha_def, gaussianIncompleteMellin_eq_line_integral hy hc ha,
        div_eq_mul_inv (Real.exp (-y) : ℂ)]
  have hfun : (fun m => ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, F m v) = archimedeanMBTerm y s :=
    funext hterm
  rw [hfun] at hMB
  exact hMB


/-- **Quantitative archimedean defect.**  For `c, y > 0` and `Re s > 0`,
`‖A(s) − A_{y,c}(s)‖ ≤ (y‖const‖ + y‖s−2‖ + (2y + 2Γ(3/2)y^{1/2})/μ) Σ_m (m+1)^{-2}` with
`μ = min(Re s, 1)/2`: the constant `(1 − e^{-y})·const` plus the trivial-zero germ defects at
`−2(n+1)`, each `O(y^{1/2}/n²)`. -/
theorem norm_gaussianArchimedeanCurrent_sub_MB_le {c y : ℝ} (hc : 0 < c) (hy : 0 < y) {s : ℂ}
    (hs : 0 < s.re) :
    ‖gaussianArchimedeanCurrent s - gaussianArchimedeanMB y c s‖ ≤
      (y * ‖gaussianArchimedeanConstant‖ + y * ‖s - 2‖ +
        (2 * y + 2 * Real.Gamma ((4 - 1) / 2) * y ^ ((1 : ℝ) / 2)) / (min s.re 1 / 2)) *
        ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
  have hhas := (hasSum_archimedeanSeriesTerm hs).sub (hasSum_archimedeanMBTerm hy hc (by linarith))
  set μ : ℝ := min s.re 1 / 2 with hμ
  have hμ0 : 0 < μ := by rw [hμ]; exact half_pos (lt_min hs one_pos)
  have hμs : μ ≤ s.re / 2 := by rw [hμ]; gcongr; exact min_le_left _ _
  have hμ1 : μ ≤ 1 / 2 := by rw [hμ]; gcongr; exact min_le_right _ _
  set G : ℝ := Real.Gamma ((4 - 1) / 2) with hG
  have hG0 : 0 ≤ G := (Real.Gamma_pos_of_pos (by norm_num)).le
  have hpow0 : 0 ≤ y ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy.le _
  set b : ℝ := y * ‖gaussianArchimedeanConstant‖ + y * ‖s - 2‖ +
    (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / μ with hb
  have hbound : ∀ m : ℕ, ‖archimedeanSeriesTerm s m - archimedeanMBTerm y s m‖ ≤
      b * (1 / ((m : ℝ) + 1) ^ 2) := by
    intro m
    have he : 0 < Real.exp (-y) := Real.exp_pos _
    have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hey : 1 - Real.exp (-y) ≤ y := by linarith [Real.add_one_le_exp (-y)]
    cases m with
    | zero =>
      simp only [archimedeanSeriesTerm, archimedeanMBTerm, Nat.cast_zero, zero_add, one_pow,
        div_one, mul_one]
      have h1 : gaussianArchimedeanConstant - (Real.exp (-y) : ℂ) * gaussianArchimedeanConstant =
          ((1 - Real.exp (-y) : ℝ) : ℂ) * gaussianArchimedeanConstant := by push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      have hC := norm_nonneg gaussianArchimedeanConstant
      have h2 : 0 ≤ y * ‖s - 2‖ + (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / μ := by positivity
      have h3 := mul_le_mul_of_nonneg_right hey hC
      rw [hb]; linarith
    | succ n =>
      have hsplit : archimedeanSeriesTerm s (n + 1) - archimedeanMBTerm y s (n + 1) =
          ((Real.exp (-y) : ℂ) - 1) / (-(2 * (n : ℂ) + 4)) +
            gaussianIncompleteMellin y (-s - 2 * n - 2) + (-s - 2 * n - 2)⁻¹ := by
        simp only [archimedeanSeriesTerm, archimedeanMBTerm, trivialZeroPoleTerm]
        have h1 : (-s - 2 * (n : ℂ) - 2)⁻¹ = -(1 / (s + 2 * n + 2)) := by
          rw [show -s - 2 * (n : ℂ) - 2 = -(s + 2 * n + 2) by ring, inv_neg, one_div]
        rw [h1, div_neg]
        ring
      rw [hsplit]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hκr : -(2 * (n : ℂ) + 4) = ((-(2 * (n : ℝ) + 4) : ℝ) : ℂ) := by push_cast; ring
      have hκ : -(2 * (n : ℂ) + 4) ≠ 0 := by
        rw [hκr]; exact_mod_cast (by linarith : -(2 * (n : ℝ) + 4) ≠ 0)
      have ha : (-s - 2 * (n : ℂ) - 2).re ≤ -1 := by simp; linarith
      have ha2 : -s - 2 * (n : ℂ) - 2 + 2 ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hd := norm_germDefect_le hy one_pos le_rfl hκ ha ha2
      rw [← hG] at hd
      refine hd.trans ?_
      have hκa : -(2 * (n : ℂ) + 4) - (-s - 2 * n - 2) = s - 2 := by ring
      rw [hκa]
      have hnκ : ‖-(2 * (n : ℂ) + 4)‖ = 2 * n + 4 := by
        rw [hκr, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
      have hna : (n : ℝ) + 2 ≤ ‖-s - 2 * (n : ℂ) - 2‖ := by
        have h := Complex.abs_re_le_norm (-s - 2 * (n : ℂ) - 2)
        have hre : (-s - 2 * (n : ℂ) - 2).re = -(s.re + 2 * n + 2) := by simp; ring
        rw [hre, abs_neg, abs_of_pos (by linarith)] at h
        linarith
      have hna2 : μ * ((n : ℝ) + 2) ≤ ‖-s - 2 * (n : ℂ) - 2 + 2‖ := by
        have h := Complex.abs_re_le_norm (-s - 2 * (n : ℂ) - 2 + 2)
        have hre : (-s - 2 * (n : ℂ) - 2 + 2).re = -(s.re + 2 * n) := by simp; ring
        rw [hre, abs_neg, abs_of_pos (by linarith)] at h
        nlinarith
      have hcast : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      have hn2 : 0 < (n : ℝ) + 2 := by linarith
      have hden1 : ((n : ℝ) + 2) ^ 2 ≤ ‖-(2 * (n : ℂ) + 4)‖ * ‖-s - 2 * (n : ℂ) - 2‖ := by
        rw [hnκ]; nlinarith
      have hden2 : μ * ((n : ℝ) + 2) ^ 2 ≤
          ‖-s - 2 * (n : ℂ) - 2‖ * ‖-s - 2 * (n : ℂ) - 2 + 2‖ := by
        have := mul_le_mul hna hna2 (by positivity) (by linarith)
        nlinarith
      have hnum0 : 0 ≤ 2 * y + 2 * G * y ^ ((1 : ℝ) / 2) := by positivity
      have t1 : y * ‖s - 2‖ / (‖-(2 * (n : ℂ) + 4)‖ * ‖-s - 2 * (n : ℂ) - 2‖) ≤
          y * ‖s - 2‖ / ((n : ℝ) + 2) ^ 2 := by
        have h0 : 0 ≤ ‖s - 2‖ := norm_nonneg _
        gcongr
      have t2 : (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) /
            (‖-s - 2 * (n : ℂ) - 2‖ * ‖-s - 2 * (n : ℂ) - 2 + 2‖) ≤
          (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / (μ * ((n : ℝ) + 2) ^ 2) := by
        gcongr
      have hsplit2 : b * (1 / ((n : ℝ) + 2) ^ 2) =
          y * ‖gaussianArchimedeanConstant‖ / ((n : ℝ) + 2) ^ 2 +
            (y * ‖s - 2‖ / ((n : ℝ) + 2) ^ 2 +
              (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / (μ * ((n : ℝ) + 2) ^ 2)) := by
        rw [hb]; field_simp; ring
      have hC : 0 ≤ y * ‖gaussianArchimedeanConstant‖ / ((n : ℝ) + 2) ^ 2 := by positivity
      calc _ ≤ y * ‖s - 2‖ / ((n : ℝ) + 2) ^ 2 +
            (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / (μ * ((n : ℝ) + 2) ^ 2) := add_le_add t1 t2
        _ ≤ b * (1 / ((n : ℝ) + 2) ^ 2) := by rw [hsplit2]; linarith
  have hsum : Summable (fun m : ℕ => b * (1 / ((m : ℝ) + 1) ^ 2)) :=
    summable_one_div_nat_add_one_sq.mul_left b
  have hsumDn : Summable (fun m : ℕ => ‖archimedeanSeriesTerm s m - archimedeanMBTerm y s m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound hsum
  rw [← hhas.tsum_eq]
  calc ‖∑' m : ℕ, (archimedeanSeriesTerm s m - archimedeanMBTerm y s m)‖
      ≤ ∑' m : ℕ, ‖archimedeanSeriesTerm s m - archimedeanMBTerm y s m‖ :=
        norm_tsum_le_tsum_norm hsumDn
    _ ≤ ∑' m : ℕ, b * (1 / ((m : ℝ) + 1) ^ 2) := hsumDn.tsum_le_tsum hbound hsum
    _ = b * ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := tsum_mul_left

/-- **The archimedean factor leaves no trace in the undamped limit.**  For `c > 0` and
`Re s > 0`, `A(s) − A_{y,c}(s) → 0` as `y → 0⁺`. -/
theorem tendsto_gaussianArchimedeanCurrent_sub_MB {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun y : ℝ => gaussianArchimedeanCurrent s - gaussianArchimedeanMB y c s)
      (𝓝[>] 0) (𝓝 0) := by
  set μ : ℝ := min s.re 1 / 2
  set G : ℝ := Real.Gamma ((4 - 1) / 2)
  set S₀ : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _)
    (g := fun y => (y * ‖gaussianArchimedeanConstant‖ + y * ‖s - 2‖ +
      (2 * y + 2 * G * y ^ ((1 : ℝ) / 2)) / μ) * S₀) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact norm_gaussianArchimedeanCurrent_sub_MB_le hc hy hs
  · have h0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    have h1 := tendsto_rpow_nhdsGT_zero (p := (1 : ℝ) / 2) (by norm_num)
    have := (((h0.mul_const ‖gaussianArchimedeanConstant‖).add (h0.mul_const ‖s - 2‖)).add
      (((h0.const_mul 2).add (h1.const_mul (2 * G))).div_const μ)).mul_const S₀
    simpa using this

theorem tendsto_pi_mul_nhdsGT_zero :
    Tendsto (fun x : ℝ => Real.pi * x) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun x : ℝ => Real.pi * x) (𝓝 0) (𝓝 (Real.pi * 0)) :=
      (continuous_const_mul Real.pi).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos Real.pi_pos hx

/-- **The Gaussian formation is asymptotically its zero-germ field.**  For `Re s > 0`,
`Φₓ'/Φₓ(s) − Σ_ρ [e^{-πx}/(ρ−½) + E(πx, ρ−s)] → 0` as `x → 0⁺`: the archimedean factor and the
trivial zeros leave no trace in the undamped limit. -/
theorem tendsto_logDeriv_gaussianFormation_sub_zeroGermField {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s -
        ∑' q : XiZeroCopy, ((Real.exp (-(Real.pi * x)) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin (Real.pi * x) (xiZero q - s)))
      (𝓝[>] 0) (𝓝 0) := by
  have hA := (tendsto_gaussianArchimedeanCurrent_sub_MB (c := 2) two_pos hs).comp
    tendsto_pi_mul_nhdsGT_zero
  refine hA.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp]
  rw [logDeriv_gaussianFormation_eq_zeroField hx hs]
  ring

/-- **Exact undamped passage beyond the zero abscissa.**  If every zero of `ξ` has `Re ρ ≤ θ`, then
at every `s` with `0 < Re s`, `θ < Re s < 2`, the Gaussian formation's logarithmic derivative
converges to `ξ'/ξ(s)` as `x → 0⁺`. -/
theorem tendsto_logDeriv_gaussianFormation_of_zeroFree {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {s : ℂ} (hs0 : 0 < s.re) (hs : θ < s.re)
    (hs2 : s.re < 2) :
    Tendsto (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s) (𝓝[>] 0)
      (𝓝 (logDeriv xi s)) := by
  have hG := (tendsto_tsum_zeroGerm hθ hs hs2).comp tendsto_pi_mul_nhdsGT_zero
  have h := (tendsto_logDeriv_gaussianFormation_sub_zeroGermField hs0).add hG
  rw [zero_add] at h
  refine h.congr' (Eventually.of_forall fun x => ?_)
  simp only [Function.comp]
  ring

/-- Under RH the Gaussian passage is exact on `½ < Re s < 2`. -/
theorem tendsto_logDeriv_gaussianFormation_of_riemannHypothesis (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs2 : s.re < 2) :
    Tendsto (fun x : ℝ => logDeriv (gaussianEulerContinuumFormation x) s) (𝓝[>] 0)
      (𝓝 (logDeriv xi s)) := by
  have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := by
    intro ρ hρ
    by_contra h
    push Not at h
    exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
  exact tendsto_logDeriv_gaussianFormation_of_zeroFree hθ (by linarith) hs hs2

/-- **Uniform undamped passage.**  Let every zero of `ξ` have `Re ρ ≤ θ`.  On any set `K` on which
`θ + η ≤ Re s`, `η ≤ Re s ≤ 2 − δ` and `‖s‖ ≤ M` (`0 < η ≤ 1`, `δ > 0`), `Φₓ'/Φₓ → ξ'/ξ`
uniformly as `x → 0⁺`. -/
theorem eventually_norm_logDeriv_gaussianFormation_sub_logDeriv_xi_le {θ η δ M ε : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) (hη0 : 0 < η) (hη1 : η ≤ 1) (hδ : 0 < δ) (hε : 0 < ε)
    {K : Set ℂ} (hK : ∀ s ∈ K, θ + η ≤ s.re ∧ η ≤ s.re ∧ s.re ≤ 2 - δ ∧ ‖s‖ ≤ M) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ s ∈ K,
      ‖logDeriv (gaussianEulerContinuumFormation x) s - logDeriv xi s‖ ≤ ε := by
  set G₁ : ℝ := Real.Gamma ((4 - 1) / 2) with hG₁def
  set G : ℝ := Real.Gamma ((4 - η) / 2) with hGdef
  have hG₁ : 0 ≤ G₁ := (Real.Gamma_pos_of_pos (by norm_num)).le
  have hG : 0 ≤ G := (Real.Gamma_pos_of_pos (by linarith)).le
  set S₀ : ℝ := ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 with hS₀def
  set S : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hSdef
  have hS₀ : 0 ≤ S₀ := tsum_nonneg fun m => by positivity
  have hS : 0 ≤ S := tsum_nonneg fun q => by positivity
  set C1 : ℝ := max 2 (2 * (M + 1) / η) with hC1def
  set C2 : ℝ := max 2 (2 * (M + 3) / δ) with hC2def
  have hC1pos : 0 ≤ C1 := le_trans (by norm_num) (le_max_left _ _)
  have hC2pos : 0 ≤ C2 := le_trans (by norm_num) (le_max_left _ _)
  set F : ℝ → ℝ := fun y =>
    (y * ‖gaussianArchimedeanConstant‖ + y * (M + 2) +
        (2 * y + 2 * G₁ * y ^ ((1 : ℝ) / 2)) / (η / 2)) * S₀ +
      (y * (M + 1) * C1 + (2 * y + 2 * G * y ^ (η / 2)) * (C1 * C2)) * S with hF
  have hFlim : Tendsto F (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
    have h1 := tendsto_rpow_nhdsGT_zero (p := (1 : ℝ) / 2) (by norm_num)
    have h2 := tendsto_rpow_nhdsGT_zero (p := η / 2) (by positivity)
    have := ((((h0.mul_const ‖gaussianArchimedeanConstant‖).add (h0.mul_const (M + 2))).add
      (((h0.const_mul 2).add (h1.const_mul (2 * G₁))).div_const (η / 2))).mul_const S₀).add
      ((((h0.mul_const (M + 1)).mul_const C1).add
        (((h0.const_mul 2).add (h2.const_mul (2 * G))).mul_const (C1 * C2))).mul_const S)
    rw [hF]
    simpa using this
  have hev := (hFlim.comp tendsto_pi_mul_nhdsGT_zero).eventually (Iic_mem_nhds hε)
  filter_upwards [hev, self_mem_nhdsWithin] with x hxF hx s hs
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hK s hs
  have hy : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hy0 := hy.le
  have hspos : 0 < s.re := by linarith
  have hM : 0 ≤ M := (norm_nonneg s).trans hs4
  have hsplit : logDeriv (gaussianEulerContinuumFormation x) s - logDeriv xi s =
      (gaussianArchimedeanCurrent s - gaussianArchimedeanMB (Real.pi * x) 2 s) +
        ((∑' q : XiZeroCopy, ((Real.exp (-(Real.pi * x)) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin (Real.pi * x) (xiZero q - s))) - logDeriv xi s) := by
    rw [logDeriv_gaussianFormation_eq_zeroField hx hspos]; ring
  rw [hsplit]
  have hA := norm_gaussianArchimedeanCurrent_sub_MB_le two_pos hy hspos
  rw [← hG₁def, ← hS₀def] at hA
  have hZ := norm_tsum_zeroGerm_sub_logDeriv_xi_le hθ hη0 hη1 hδ hy hs1 hs3
  rw [← hGdef, ← hSdef] at hZ
  have hn2 : ‖s - 2‖ ≤ M + 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have hnh : ‖s - 1 / 2‖ ≤ M + 1 := (norm_sub_le _ _).trans (by norm_num; linarith)
  have hn5 : ‖s - 5 / 2‖ ≤ M + 3 := (norm_sub_le _ _).trans (by norm_num; linarith)
  have hμ : η / 2 ≤ min s.re 1 / 2 := by gcongr; exact le_min hs2 hη1
  have hC1 : max 2 (2 * ‖s - 1 / 2‖ / η) ≤ C1 := max_le_max le_rfl (by gcongr)
  have hC2 : max 2 (2 * ‖s - 5 / 2‖ / δ) ≤ C2 := max_le_max le_rfl (by gcongr)
  have hC1n : 0 ≤ max 2 (2 * ‖s - 1 / 2‖ / η) := le_trans (by norm_num) (le_max_left _ _)
  have hC2n : 0 ≤ max 2 (2 * ‖s - 5 / 2‖ / δ) := le_trans (by norm_num) (le_max_left _ _)
  have hp1 : 0 ≤ (Real.pi * x) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hy0 _
  have hp2 : 0 ≤ (Real.pi * x) ^ (η / 2) := Real.rpow_nonneg hy0 _
  have hN1 : 0 ≤ 2 * (Real.pi * x) + 2 * G₁ * (Real.pi * x) ^ ((1 : ℝ) / 2) := by
    have := mul_nonneg (mul_nonneg zero_le_two hG₁) hp1; linarith
  have hN2 : 0 ≤ 2 * (Real.pi * x) + 2 * G * (Real.pi * x) ^ (η / 2) := by
    have := mul_nonneg (mul_nonneg zero_le_two hG) hp2; linarith
  have hA' : ‖gaussianArchimedeanCurrent s - gaussianArchimedeanMB (Real.pi * x) 2 s‖ ≤
      ((Real.pi * x) * ‖gaussianArchimedeanConstant‖ + (Real.pi * x) * (M + 2) +
        (2 * (Real.pi * x) + 2 * G₁ * (Real.pi * x) ^ ((1 : ℝ) / 2)) / (η / 2)) * S₀ := by
    refine hA.trans (mul_le_mul_of_nonneg_right ?_ hS₀)
    have e1 := mul_le_mul_of_nonneg_left hn2 hy0
    have e2 := div_le_div_of_nonneg_left hN1 (by positivity : 0 < η / 2) hμ
    linarith
  have hZ' : ‖(∑' q : XiZeroCopy, ((Real.exp (-(Real.pi * x)) : ℂ) / (xiZero q - 1 / 2) +
        gaussianIncompleteMellin (Real.pi * x) (xiZero q - s))) - logDeriv xi s‖ ≤
      ((Real.pi * x) * (M + 1) * C1 +
        (2 * (Real.pi * x) + 2 * G * (Real.pi * x) ^ (η / 2)) * (C1 * C2)) * S := by
    refine hZ.trans (mul_le_mul_of_nonneg_right ?_ hS)
    have e1 : Real.pi * x * ‖s - 1 / 2‖ * max 2 (2 * ‖s - 1 / 2‖ / η) ≤
        Real.pi * x * (M + 1) * C1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnh hy0) hC1 hC1n (by positivity)
    have e2 := mul_le_mul_of_nonneg_left (mul_le_mul hC1 hC2 hC2n hC1pos) hN2
    linarith
  have hsum := add_le_add hA' hZ'
  simp only [Function.comp, hF] at hxF
  exact (norm_add_le _ _).trans (hsum.trans hxF)

end

end RHTower
