import GaloisForLFunctions.RHTower.DeBruijnNegativeTimeContour
import GaloisForLFunctions.RHTower.GaussianDirichletSeries
import GaloisForLFunctions.RHTower.ArchimedeanFactorVerticalModel
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Negative heat times: the Gaussian-damped Dirichlet model

Write `A_τ(s) = H_{−τ}(z)` at `s = ½ + iz` (`negHeatS`). Along the vertical line `Re w = Re s + a`,

`A_τ(s) = ∫ g_τ(u − ia) ξ(s + a + iu) du`   (`negHeatS_eq_integral`),

and on `Re(s + a) > 1` the factorization `ξ = G ζ` with the log-linear model
`G(w₁ + iu) ≈ G(w₁) e^{iuL}` (`w₁ = s + a`) integrates exactly, term by term in the Dirichlet series
of `ζ`, because `∫ g_τ(u − ia) e^{iuk} du = e^{−ak−τk²}` (`integral_cgauss_shift_mul_exp`):

`∫ g_τ(u − ia) G(w₁) e^{iuL} ζ(w₁ + iu) du = G(w₁) e^{−aL−τL²} F_τ(s − 2τL)`   (`integral_model_eq`),

with `F_τ(w) = Σ e^{−τ log²m} m^{−w}` the Gaussian-damped zeta series.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- `A_τ(s) = H_{−τ}(z)` at `s = ½ + iz`. -/
def negHeatS (τ : ℝ) (s : ℂ) : ℂ := riemannHeat (-τ) (-I * (s - 1 / 2))

/-- **The vertical average along any line.** -/
theorem negHeatS_eq_integral {τ : ℝ} (hτ : 0 < τ) (s : ℂ) (a : ℝ) :
    negHeatS τ s = ∫ u : ℝ, cgauss τ ((u : ℂ) - a * I) * xi (s + a + u * I) := by
  rw [negHeatS, riemannHeat_neg_eq_integral_shift hτ _ a]
  congr 1; funext u
  rw [riemannHeat_zero]
  congr 2
  ring_nf
  rw [I_sq]
  ring

theorem cgauss_shift_mul_exp_eq {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (k : ℂ) (u : ℝ) :
    cgauss τ ((u : ℂ) - a * I) * Complex.exp (u * I * k) =
      (((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(1 / (4 * τ) : ℂ) * (u : ℂ) ^ 2 + (a * I / (2 * τ) + I * k) * u +
          (a ^ 2 / (4 * τ) : ℂ)) := by
  have h4 : (4 * (τ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (4 * τ : ℝ) ≠ 0)
  have h2 : (2 * (τ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * τ : ℝ) ≠ 0)
  rw [cgauss, mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Gaussian integral with a complex frequency along a shifted line.**
`∫ g_τ(u − ia) e^{iuk} du = e^{−ak − τk²}`. -/
theorem integral_cgauss_shift_mul_exp {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (k : ℂ) :
    ∫ u : ℝ, cgauss τ ((u : ℂ) - a * I) * Complex.exp (u * I * k) =
      Complex.exp (-(a * k) - τ * k ^ 2) := by
  have hb : (-(1 / (4 * τ) : ℂ)).re < 0 := by
    rw [Complex.neg_re, ← Complex.ofReal_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_div, Complex.ofReal_re]
    have : 0 < 1 / (4 * τ) := by positivity
    linarith
  have hquad := integral_cexp_quadratic hb (a * I / (2 * τ) + I * k) (a ^ 2 / (4 * τ) : ℂ)
  have h4 : (4 * (τ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (4 * τ : ℝ) ≠ 0)
  have h2 : (2 * (τ : ℂ)) ≠ 0 := by exact_mod_cast (by positivity : (2 * τ : ℝ) ≠ 0)
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hfun := cgauss_shift_mul_exp_eq hτ a k
  simp_rw [hfun]
  rw [integral_const_mul, hquad]
  have hexp : (a ^ 2 / (4 * τ) : ℂ) - (a * I / (2 * τ) + I * k) ^ 2 / (4 * -(1 / (4 * τ))) =
      -(a * k) - τ * k ^ 2 := by
    rw [show (a * I / (2 * τ) + I * k : ℂ) = I * (a / (2 * τ) + k) by ring, mul_pow, I_sq]
    field_simp
    ring
  rw [hexp, ← mul_assoc]
  have hpi : (Real.pi : ℂ) / -(-(1 / (4 * τ) : ℂ)) = ((4 * Real.pi * τ : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hpi, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  norm_num

theorem integrable_cgauss_shift_mul_exp {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (k : ℂ) :
    Integrable (fun u : ℝ => cgauss τ ((u : ℂ) - a * I) * Complex.exp (u * I * k)) := by
  have hb : 0 < ((1 / (4 * τ) : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; positivity
  refine ((integrable_cexp_quadratic hb (a * I / (2 * τ) + I * k) (a ^ 2 / (4 * τ) : ℂ)).const_mul
    (((4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [cgauss_shift_mul_exp_eq hτ a k u]
  push_cast
  ring_nf

/-! ## The exact model sum -/

theorem natCast_succ_cpow_eq (n : ℕ) (w : ℂ) :
    ((n + 1 : ℕ) : ℂ) ^ (-w) = Complex.exp (-(w * Real.log ((n : ℝ) + 1))) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)]
  congr 1
  rw [show (((n + 1 : ℕ) : ℂ)) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_log (by positivity)]
  ring

/-- The `n`-th Dirichlet term of the model integrand. -/
def modelTerm (τ : ℝ) (s : ℂ) (a : ℝ) (L : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  cgauss τ ((u : ℂ) - a * I) * (archG (s + a) * Complex.exp (u * I * L) *
    ((n + 1 : ℕ) : ℂ) ^ (-(s + a + u * I)))

theorem modelTerm_eq (τ : ℝ) (s : ℂ) (a : ℝ) (L : ℂ) (n : ℕ) (u : ℝ) :
    modelTerm τ s a L n u = archG (s + a) * ((n + 1 : ℕ) : ℂ) ^ (-(s + a)) *
      (cgauss τ ((u : ℂ) - a * I) *
        Complex.exp (u * I * (L - Real.log ((n : ℝ) + 1)))) := by
  rw [modelTerm, natCast_succ_cpow_eq, natCast_succ_cpow_eq]
  rw [show Complex.exp (u * I * (L - Real.log ((n : ℝ) + 1))) =
      Complex.exp (u * I * L) * Complex.exp (-(u * I * Real.log ((n : ℝ) + 1))) by
    rw [← Complex.exp_add]; congr 1; ring]
  rw [show Complex.exp (-((s + a + u * I) * Real.log ((n : ℝ) + 1))) =
      Complex.exp (-((s + a) * Real.log ((n : ℝ) + 1))) *
        Complex.exp (-(u * I * Real.log ((n : ℝ) + 1))) by
    rw [← Complex.exp_add]; congr 1; ring]
  ring

theorem integral_modelTerm {τ : ℝ} (hτ : 0 < τ) (s : ℂ) (a : ℝ) (L : ℂ) (n : ℕ) :
    ∫ u, modelTerm τ s a L n u =
      archG (s + a) * Complex.exp (-(a * L) - τ * L ^ 2) * gaussDirichletTerm τ n (s - 2 * τ * L) := by
  simp_rw [modelTerm_eq]
  rw [integral_const_mul, integral_cgauss_shift_mul_exp hτ, gaussDirichletTerm,
    natCast_succ_cpow_eq, natCast_succ_cpow_eq]
  set l : ℝ := Real.log ((n : ℝ) + 1)
  calc archG (s + a) * Complex.exp (-((s + a) * l)) *
        Complex.exp (-(a * (L - l)) - τ * (L - l) ^ 2)
      = archG (s + a) * Complex.exp (-((s + a) * l) + (-(a * (L - l)) - τ * (L - l) ^ 2)) := by
        rw [mul_assoc, ← Complex.exp_add]
    _ = archG (s + a) * Complex.exp ((-(a * L) - τ * L ^ 2) +
          (-(τ * (l : ℂ) ^ 2) + -((s - 2 * τ * L) * l))) := by congr 2; ring
    _ = _ := by
        rw [Complex.exp_add, Complex.exp_add, Complex.ofReal_exp]
        push_cast
        ring

theorem norm_modelTerm_le (τ : ℝ) (s : ℂ) (a : ℝ) (L : ℂ) (n : ℕ) (u : ℝ) :
    ‖modelTerm τ s a L n u‖ ≤
      ‖archG (s + a)‖ * ((n : ℝ) + 1) ^ (-(s + a).re) *
        (‖cgauss τ ((u : ℂ) - a * I)‖ * Real.exp (-(u * L.im))) := by
  rw [modelTerm_eq, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), Complex.norm_exp]
  push_cast
  apply le_of_eq
  congr 3
  simp [Complex.mul_re]

theorem integrable_norm_cgauss_mul_exp {τ : ℝ} (hτ : 0 < τ) (a : ℝ) (c : ℝ) :
    Integrable (fun u : ℝ => ‖cgauss τ ((u : ℂ) - a * I)‖ * Real.exp (-(u * c))) := by
  have h := (integrable_cgauss_shift_mul_exp hτ a ((c : ℂ) * I)).norm
  refine h.congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem summable_succ_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
  have h := (Real.summable_nat_rpow (p := -σ)).mpr (by linarith)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

/-- **The exact model sum.** -/
theorem integral_model_eq {τ : ℝ} (hτ : 0 < τ) (s : ℂ) (a : ℝ) (L : ℂ) (h1 : 1 < (s + a).re) :
    ∫ u : ℝ, cgauss τ ((u : ℂ) - a * I) *
        (archG (s + a) * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)) =
      archG (s + a) * Complex.exp (-(a * L) - τ * L ^ 2) * gaussDirichlet τ (s - 2 * τ * L) := by
  have hzeta : ∀ u : ℝ, cgauss τ ((u : ℂ) - a * I) *
      (archG (s + a) * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)) =
      ∑' n : ℕ, modelTerm τ s a L n u := by
    intro u
    have hre : 1 < (s + a + u * I).re := by simpa using h1
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre, ← tsum_mul_left, ← tsum_mul_left]
    congr 1; funext n
    rw [modelTerm, one_div, ← Complex.cpow_neg]
    push_cast
    ring
  simp_rw [hzeta]
  have hint : ∀ n, Integrable (modelTerm τ s a L n) := by
    intro n
    have e : modelTerm τ s a L n = fun u : ℝ => archG (s + a) * ((n + 1 : ℕ) : ℂ) ^ (-(s + a)) *
        (cgauss τ ((u : ℂ) - a * I) * Complex.exp (u * I * (L - Real.log ((n : ℝ) + 1)))) :=
      funext (modelTerm_eq τ s a L n)
    rw [e]
    exact (integrable_cgauss_shift_mul_exp hτ a _).const_mul _
  have hsumint : Summable (fun n => ∫ u, ‖modelTerm τ s a L n u‖) := by
    have hK := integrable_norm_cgauss_mul_exp hτ a L.im
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _)
      (fun n => integral_mono (hint n).norm ((hK.const_mul _)) fun u => norm_modelTerm_le τ s a L n u)
      ?_
    simp_rw [integral_const_mul]
    exact ((summable_succ_rpow_neg h1).mul_left _).mul_right _
  rw [← integral_tsum_of_summable_integral_norm hint hsumint]
  simp_rw [integral_modelTerm hτ]
  rw [tsum_mul_left, gaussDirichlet]

/-! ## The error of the model -/

theorem rexp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-x)
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  nlinarith [Real.exp_pos x]

theorem neg_mul_le_mul_abs {c : ℝ} (hc : 0 ≤ c) (u : ℝ) : -(u * c) ≤ c * |u| := by
  have := mul_le_mul_of_nonneg_left (neg_le_abs u) hc
  linarith

theorem integrable_exp_neg_sq_add_abs {c : ℝ} (hc : 0 < c) (β : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-(c * u ^ 2) + β * |u|)) := by
  refine ((integrable_exp_neg_mul_sq (b := c / 2) (by positivity)).const_mul
    (Real.exp (β ^ 2 / (2 * c)))).mono' (by fun_prop) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ c / 2 * (|u| - β / c) ^ 2 := by positivity
  have e : c / 2 * (|u| - β / c) ^ 2 = c / 2 * u ^ 2 - β * |u| + β ^ 2 / (2 * c) := by
    rw [sub_sq, sq_abs]; field_simp
  linarith

theorem integrable_abs_mul_exp_neg_sq_add_abs {c : ℝ} (hc : 0 < c) (β : ℝ) :
    Integrable (fun u : ℝ => |u| * Real.exp (-(c * u ^ 2) + β * |u|)) := by
  refine (integrable_exp_neg_sq_add_abs hc (β + 1)).mono' (by fun_prop)
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : |u| ≤ Real.exp |u| := by linarith [Real.add_one_le_exp |u|]
  calc |u| * Real.exp (-(c * u ^ 2) + β * |u|)
      ≤ Real.exp |u| * Real.exp (-(c * u ^ 2) + β * |u|) := by gcongr
    _ = Real.exp (-(c * u ^ 2) + (β + 1) * |u|) := by rw [← Real.exp_add]; ring_nf

/-- `‖ξ(w)‖ ≤ ∫ Φ(x) e^{2|x|} dx` on `−3/2 ≤ Re w ≤ 5/2`. -/
theorem norm_xi_le_of_re {w : ℂ} (h1 : -3 / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) :
    ‖xi w‖ ≤ ∫ x, riemannKernelReal x * Real.exp (2 * |x|) := by
  have e : xi w = riemannHeat 0 (-I * (w - 1 / 2)) := by
    rw [riemannHeat_zero]; congr 1; ring_nf; rw [I_sq]; ring
  rw [e]
  refine (norm_riemannHeat_zero_le _).trans (integral_riemannKernel_mul_exp_mono ?_)
  have : (-I * (w - 1 / 2)).im = -(w.re - 1 / 2) := by simp [Complex.mul_im]
  rw [this, abs_neg, abs_le]
  constructor <;> linarith

theorem xi_eq_riemannHeat_zero (w : ℂ) : xi w = riemannHeat 0 (-I * (w - 1 / 2)) := by
  rw [riemannHeat_zero]; congr 1; ring_nf; rw [I_sq]; ring

theorem continuous_xi : Continuous xi := by
  have : xi = fun w => riemannHeat 0 (-I * (w - 1 / 2)) := funext xi_eq_riemannHeat_zero
  rw [this]
  exact (differentiable_riemannHeat le_rfl).continuous.comp (by fun_prop)

theorem norm_cgauss_shift {τ : ℝ} (hτ : 0 < τ) (a u : ℝ) :
    ‖cgauss τ ((u : ℂ) - a * I)‖ =
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp ((a ^ 2 - u ^ 2) / (4 * τ)) := by
  rw [norm_cgauss hτ]
  simp

/-- **The model error.** With `w₁ = s + a = σ₁ + iX₁`, `3/2 ≤ σ₁ ≤ 5/2`, `L = L_T`, `T ≥ 48`,
`|X₁ − T| + V ≤ T/2` and `η = (12 + |X₁ − T| + V)/T ≤ 1`:
`‖A_τ(s) − G(w₁) e^{−aL−τL²} F_τ(s − 2τL)‖ ≤
 c_τ e^{a²/(4τ)} (3‖G(w₁)‖ η K₁ + e^{−V²/(8τ)} (M₂ K₂ + 3‖G(w₁)‖ K₃))`. -/
theorem norm_negHeatS_sub_model_le {τ : ℝ} (hτ : 0 < τ) {σ₁ X₁ T V : ℝ} (hσ₁ : 3 / 2 ≤ σ₁)
    (hσ₁' : σ₁ ≤ 5 / 2) (hT : 48 ≤ T) (hV0 : 0 ≤ V) (hV : |X₁ - T| + V ≤ T / 2)
    (hη : (12 + |X₁ - T| + V) / T ≤ 1) {s : ℂ} {a : ℝ} (hw : s + a = (σ₁ : ℂ) + X₁ * I) :
    ‖negHeatS τ s - archG (s + a) * Complex.exp (-(a * horizontalSlope T) -
        τ * horizontalSlope T ^ 2) * gaussDirichlet τ (s - 2 * τ * horizontalSlope T)‖ ≤
      (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ)) * Real.exp (a ^ 2 / (4 * τ)) *
        (3 * ‖archG (s + a)‖ * ((12 + |X₁ - T| + V) / T) *
            (∫ u, |u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|)) +
          Real.exp (-(V ^ 2 / (8 * τ))) *
            ((∫ x, riemannKernelReal x * Real.exp (2 * |x|)) *
                (∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|)) +
              3 * ‖archG (s + a)‖ *
                (∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|)))) := by
  set L := horizontalSlope T with hL
  set G₁ := archG (s + a)
  set η := (12 + |X₁ - T| + V) / T
  set cτ := (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))
  set M₂ := ∫ x, riemannKernelReal x * Real.exp (2 * |x|)
  have hsa : s.re + a = σ₁ := by have := congrArg Complex.re hw; simpa using this
  have hre' : ∀ u : ℝ, (s + a + u * I).re = σ₁ := fun u => by simp [hsa]
  have h1 : 1 < (s + a).re := by simp [hsa]; linarith
  have hLim : L.im = Real.pi / 4 := by simp [hL, horizontalSlope]
  have hη0 : 0 ≤ η := by positivity
  have hM₂ : 0 ≤ M₂ := integral_nonneg fun x => by have := riemannKernelReal_pos x; positivity
  have hcτ : 0 ≤ cτ := by positivity
  -- the two integrands
  have hIA : Integrable (fun u : ℝ => cgauss τ ((u : ℂ) - a * I) * xi (s + a + u * I)) := by
    refine ((integrable_exp_neg_sq_add_abs (c := 1 / (4 * τ)) (by positivity) 0).const_mul
      (cτ * Real.exp (a ^ 2 / (4 * τ)) * M₂)).mono' ?_ (Eventually.of_forall fun u => ?_)
    · refine ((differentiable_cgauss τ).continuous.comp (by fun_prop)).mul ?_ |>.aestronglyMeasurable
      exact (continuous_xi.comp (by fun_prop))
    · rw [norm_mul, norm_cgauss_shift hτ]
      have hx := norm_xi_le_of_re (w := s + a + u * I) (by rw [hre']; linarith)
        (by rw [hre']; linarith)
      have e : Real.exp ((a ^ 2 - u ^ 2) / (4 * τ)) =
          Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2) + 0 * |u|) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring
      rw [e]
      calc cτ * (Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2) + 0 * |u|)) *
            ‖xi (s + a + u * I)‖
          ≤ cτ * (Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2) + 0 * |u|)) * M₂ := by
            gcongr
        _ = _ := by ring
  have hIM : Integrable (fun u : ℝ => cgauss τ ((u : ℂ) - a * I) *
      (G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I))) := by
    have hK := integrable_norm_cgauss_mul_exp hτ a L.im
    refine (hK.const_mul (‖G₁‖ * 3)).mono' ?_ (Eventually.of_forall fun u => ?_)
    · refine ((differentiable_cgauss τ).continuous.comp (by fun_prop)).mul ?_ |>.aestronglyMeasurable
      refine continuous_const.mul (by fun_prop) |>.mul ?_
      refine continuous_iff_continuousAt.mpr fun u => ?_
      refine ((differentiableAt_riemannZeta ?_).continuousAt).comp (by fun_prop)
      intro h; have := congrArg Complex.re h; rw [hre'] at this; simp at this; linarith
    · have hz := RHTower.Sieve.norm_riemannZeta_le (s := s + a + u * I) (by simpa using h1)
      have hz3 : ‖riemannZeta (s + a + u * I)‖ ≤ 3 := by
        refine hz.trans ?_
        rw [hre']
        have : 1 / (σ₁ - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
      have : (u * I * L : ℂ).re = -(u * L.im) := by simp [Complex.mul_re]
      rw [this]
      calc ‖cgauss τ ((u : ℂ) - a * I)‖ * (‖G₁‖ * Real.exp (-(u * L.im)) *
            ‖riemannZeta (s + a + u * I)‖)
          ≤ ‖cgauss τ ((u : ℂ) - a * I)‖ * (‖G₁‖ * Real.exp (-(u * L.im)) * 3) := by gcongr
        _ = _ := by ring
  rw [negHeatS_eq_integral hτ s a, ← integral_model_eq hτ s a L h1, ← integral_sub hIA hIM]
  -- the majorant
  set ψ : ℝ → ℝ := fun u => cτ * Real.exp (a ^ 2 / (4 * τ)) *
    (3 * ‖G₁‖ * η * (|u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|)) +
      Real.exp (-(V ^ 2 / (8 * τ))) *
        (M₂ * Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|) +
          3 * ‖G₁‖ * Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|))) with hψ
  have hψint : Integrable ψ := by
    refine Integrable.const_mul ?_ _
    refine Integrable.add ?_ ?_
    · exact (integrable_abs_mul_exp_neg_sq_add_abs (by positivity) _).const_mul _
    · refine Integrable.const_mul (Integrable.add ?_ ?_) _
      · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
      · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
  have hψ_eq : ∫ u, ψ u = cτ * Real.exp (a ^ 2 / (4 * τ)) *
      (3 * ‖G₁‖ * η * (∫ u, |u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|)) +
        Real.exp (-(V ^ 2 / (8 * τ))) *
          (M₂ * (∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|)) +
            3 * ‖G₁‖ * (∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|)))) := by
    rw [hψ, integral_const_mul, integral_add, integral_const_mul, integral_const_mul,
      integral_add, integral_const_mul, integral_const_mul]
    · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
    · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
    · exact (integrable_abs_mul_exp_neg_sq_add_abs (by positivity) _).const_mul _
    · refine Integrable.const_mul (Integrable.add ?_ ?_) _
      · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
      · exact (integrable_exp_neg_sq_add_abs (by positivity) _).const_mul _
  rw [← hψ_eq]
  refine norm_integral_le_of_norm_le hψint (Eventually.of_forall fun u => ?_)
  -- pointwise estimate
  have hre : (s + a + u * I).re = σ₁ := hre' u
  have hne1 : s + a + u * I ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hxi : xi (s + a + u * I) = archG (s + a + u * I) * riemannZeta (s + a + u * I) :=
    xi_eq_archG_mul_zeta (by rw [hre]; linarith)
  have hz3 : ‖riemannZeta (s + a + u * I)‖ ≤ 3 := by
    refine (RHTower.Sieve.norm_riemannZeta_le (by rw [hre]; linarith)).trans ?_
    rw [hre]
    have : 1 / (σ₁ - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    linarith
  have hexpL : ‖Complex.exp (u * I * L)‖ = Real.exp (-(u * (Real.pi / 4))) := by
    rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re, hLim]
  have hcg := norm_cgauss_shift hτ a u
  have hsplit : cgauss τ ((u : ℂ) - a * I) * xi (s + a + u * I) -
      cgauss τ ((u : ℂ) - a * I) * (G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)) =
      cgauss τ ((u : ℂ) - a * I) *
        (xi (s + a + u * I) - G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)) := by
    ring
  rw [hsplit, norm_mul, hcg]
  have hgauss : Real.exp ((a ^ 2 - u ^ 2) / (4 * τ)) =
      Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [hgauss]
  have hA0 : 0 ≤ 3 * ‖G₁‖ * η * (|u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|)) := by
    positivity
  have hB0 : 0 ≤ Real.exp (-(V ^ 2 / (8 * τ))) *
      (M₂ * Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|) +
        3 * ‖G₁‖ * Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|)) := by positivity
  rcases le_or_gt |u| V with hu | hu
  · -- the model region
    have hmod := norm_archG_vertical_sub_model_le (σ := σ₁) (X₁ := X₁) (T := T) (V := V) (u := u)
      (by linarith) (by linarith) hT hV hu
    rw [← hw] at hmod
    have hdiff : xi (s + a + u * I) - G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I) =
        (archG (s + a + u * I) - G₁ * Complex.exp (u * I * L)) * riemannZeta (s + a + u * I) := by
      rw [hxi]; ring
    have hmod' : ‖archG (s + a + u * I) - G₁ * Complex.exp (u * I * L)‖ ≤
        ‖G₁‖ * Real.exp (-(u * (Real.pi / 4))) * (Real.exp (η * |u|) - 1) := by
      have e : (u : ℂ) * I * horizontalSlope T = u * I * L := by rw [hL]
      rw [e] at hmod
      exact hmod
    have hexp1 : Real.exp (η * |u|) - 1 ≤ η * |u| * Real.exp |u| := by
      have h4 : 0 ≤ η * |u| := by positivity
      have hm : η * |u| ≤ |u| := by
        have := mul_le_mul_of_nonneg_right hη (abs_nonneg u); linarith
      exact (rexp_sub_one_le_mul_exp _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hm) h4)
    have hpi : Real.exp (-(u * (Real.pi / 4))) ≤ Real.exp (Real.pi / 4 * |u|) :=
      Real.exp_le_exp.mpr (neg_mul_le_mul_abs (by positivity) u)
    have hb : ‖archG (s + a + u * I) - G₁ * Complex.exp (u * I * L)‖ ≤
        ‖G₁‖ * Real.exp (Real.pi / 4 * |u|) * (η * |u| * Real.exp |u|) := by
      refine hmod'.trans ?_
      have : 0 ≤ Real.exp (η * |u|) - 1 := by
        have := Real.one_le_exp (show 0 ≤ η * |u| by positivity); linarith
      gcongr
    have hK0 : 0 ≤ cτ * Real.exp (a ^ 2 / (4 * τ)) := by positivity
    rw [hdiff, norm_mul]
    calc cτ * (Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2))) *
          (‖archG (s + a + u * I) - G₁ * Complex.exp (u * I * L)‖ * ‖riemannZeta (s + a + u * I)‖)
        ≤ cτ * (Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2))) *
          ((‖G₁‖ * Real.exp (Real.pi / 4 * |u|) * (η * |u| * Real.exp |u|)) * 3) := by
          gcongr
      _ = cτ * Real.exp (a ^ 2 / (4 * τ)) *
          (3 * ‖G₁‖ * η * (|u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|))) := by
          rw [show -(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u| =
            -(1 / (4 * τ) * u ^ 2) + Real.pi / 4 * |u| + |u| by ring, Real.exp_add, Real.exp_add]
          ring
      _ ≤ ψ u := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB0) hK0
  · -- the tail
    have hxiM : ‖xi (s + a + u * I)‖ ≤ M₂ :=
      norm_xi_le_of_re (by rw [hre]; linarith) (by rw [hre]; linarith)
    have hmodel : ‖G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)‖ ≤
        3 * ‖G₁‖ * Real.exp (Real.pi / 4 * |u|) := by
      rw [norm_mul, norm_mul, hexpL]
      have hpi : Real.exp (-(u * (Real.pi / 4))) ≤ Real.exp (Real.pi / 4 * |u|) :=
        Real.exp_le_exp.mpr (neg_mul_le_mul_abs (by positivity) u)
      calc ‖G₁‖ * Real.exp (-(u * (Real.pi / 4))) * ‖riemannZeta (s + a + u * I)‖
          ≤ ‖G₁‖ * Real.exp (Real.pi / 4 * |u|) * 3 := by gcongr
        _ = _ := by ring
    have htail : Real.exp (-(1 / (4 * τ) * u ^ 2)) ≤
        Real.exp (-(V ^ 2 / (8 * τ))) * Real.exp (-(1 / (8 * τ) * u ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hu2 : V ^ 2 ≤ u ^ 2 := by
        rw [← sq_abs u]; exact pow_le_pow_left₀ hV0 hu.le 2
      have hc : 1 / (4 * τ) = 2 * (1 / (8 * τ)) := by field_simp; ring
      have hV2 : V ^ 2 / (8 * τ) = 1 / (8 * τ) * V ^ 2 := by ring
      have hc0 : 0 < 1 / (8 * τ) := by positivity
      rw [hc, hV2]
      have := mul_le_mul_of_nonneg_left hu2 hc0.le
      linarith
    calc cτ * (Real.exp (a ^ 2 / (4 * τ)) * Real.exp (-(1 / (4 * τ) * u ^ 2))) *
          ‖xi (s + a + u * I) - G₁ * Complex.exp (u * I * L) * riemannZeta (s + a + u * I)‖
        ≤ cτ * (Real.exp (a ^ 2 / (4 * τ)) *
            (Real.exp (-(V ^ 2 / (8 * τ))) * Real.exp (-(1 / (8 * τ) * u ^ 2)))) *
          (M₂ + 3 * ‖G₁‖ * Real.exp (Real.pi / 4 * |u|)) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hxiM hmodel)
      _ = cτ * Real.exp (a ^ 2 / (4 * τ)) * (Real.exp (-(V ^ 2 / (8 * τ))) *
          (M₂ * Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|) +
            3 * ‖G₁‖ * Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|))) := by
          rw [Real.exp_add, Real.exp_add, zero_mul, Real.exp_zero]
          ring
      _ ≤ ψ u := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA0) (by positivity)

end

end RHTower.DeBruijn
