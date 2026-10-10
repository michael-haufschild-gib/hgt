import GaloisForLFunctions.RHTower.GaussianPassageSinglePointAbscissa
import GaloisForLFunctions.RHTower.LiouvilleTriangularHeadOscillation
import GaloisForLFunctions.RHTower.LaplaceAbscissaExists
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# The one-sided Gaussian prime budget law

For real `σ > 0` and `y > 0` write the Gaussian prime mass and its continuum
`P_σ(y) = Σ Λ(n) n^{-σ} e^{-yn²}`, `C_σ(y) = ∫₁^∞ u^{-σ} e^{-yu²} du`.  Their difference is the
prime-minus-continuum gap of the Gaussian formation at the real point `σ`.

* **Unconditional size** (`norm_gaussianPrimeContinuumGap_le`).  `|P_σ − C_σ|(y) ≤ (e² + Γ(½)) y^{-2}`
  on `0 < y ≤ 1`, from `Σ n e^{-yn} = e^{-y}/(1−e^{-y})²` and the incomplete-Gamma bound.
* **One-sided law** (`xi_ne_zero_of_gaussianPrimeBudget`).  If `P_σ(y) ≤ C_σ(y) + B` for all
  `0 < y ≤ 1`, then `ξ` has no zero with `Re z > σ`.  In the logarithmic variable `y = e^{-u}` the
  deficit `B − (P_σ − C_σ)(e^{-u})` is a nonnegative density; thickened by `e^{-u}` it is a Laplace
  carrier (`expThickenedCarrier`) whose transform equals `B/z − Γ(z)(A − ξ'/ξ)(σ + 2z) + T(z) + 1/(z+1)`
  with `T` entire (`complexLaplace_expThickenedCarrier`, `integral_gaussianBudgetProfile_mul_cexp`).  This is
  analytic at every positive real point because `ξ` has no real zeros, so Landau's theorem puts the
  abscissa at or below `0`; the transform is then holomorphic on `Re z > 0`, which continues
  `ξ'/ξ(σ + 2z)` holomorphically there.
* **Integrated excess law** (`xi_ne_zero_of_gaussianPrimeExcess`).  It suffices that the positive
  excess `(P_σ − C_σ − B)⁺` has finite weighted integral `∫₀¹ (·)(y) y^{τ−1} dy` for every `τ > 0`:
  the carrier of the negative part of the deficit then has abscissa `≤ 0` and enters the
  continuation as a holomorphic term.
* **Both signs** (`xi_ne_zero_of_gaussianPrimeBudget_lower`).  The profile carries a sign `η = ±1`;
  a lower budget `P_σ ≥ C_σ − B` forces the same zero-free half-plane.
* **Abscissa law** (`xi_zero_re_le_iff_gaussianPrimeBudget`).  For `θ ≥ 0`, all zeros satisfy
  `Re ρ ≤ θ` iff the upper budget holds at every `σ ∈ (θ, 2)`: the budget abscissa is `sup Re ρ`.
* **Growth law** (`xi_ne_zero_of_gaussianPrimeGrowthBudget`).  `η(P_σ − C_σ)(y) ≤ B y^{-a}` on
  `(0, 1]` forces `ξ ≠ 0` on `Re z > σ + 2a`: the reference term `B e^{au}` has transform `B/(z − a)`,
  so Landau stops at `a`.
* **Unconditional Ω±** (`exists_gaussianWeightedGap_gt_rpow`, `exists_gaussianWeightedGap_lt_neg_rpow`).
  For `σ + 2a < ½` the gap `P_σ − C_σ` exceeds `B y^{-a}` and falls below `−B y^{-a}` on `(0, 1]` for
  every `B`, because Hardy's theorem supplies critical-line zeros.
* **RH as a budget** (`riemannHypothesis_iff_gaussianPrimeBudget`,
  `riemannHypothesis_iff_gaussianPrimeExcess`).  RH holds iff for every `σ ∈ (½, 1)` the Gaussian prime
  mass exceeds its continuum by at most a constant on `(0, 1]`, iff the excess over some constant
  has finite weighted integral at every positive weight.
-/

open Complex Filter Topology Set MeasureTheory Asymptotics
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceMass complexLaplace IsAbscissa exists_isAbscissa
  differentiableOn_complexLaplace)

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-! ## Mellin transforms in the logarithmic variable -/

private theorem rexp_neg_image : (Real.exp ∘ Neg.neg) '' univ = Ioi (0 : ℝ) := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_deriv :
    ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_injOn : (univ : Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

theorem abs_neg_exp_smul_cpow (u : ℝ) (z : ℂ) :
    |(-Real.exp (-u))| • (((Real.exp (-u) : ℝ) : ℂ) ^ (z - 1)) = Complex.exp (-z * u) := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.real_smul, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∫₀^∞ t^{z-1} f(t) dt = ∫_ℝ e^{-zu} f(e^{-u}) du`. -/
theorem mellin_eq_integral_exp_neg (f : ℝ → ℂ) (z : ℂ) :
    mellin f z = ∫ u : ℝ, Complex.exp (-z * u) * f (Real.exp (-u)) := by
  rw [mellin, ← rexp_neg_image, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    rexp_neg_deriv rexp_neg_injOn, Measure.restrict_univ]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Function.comp, smul_eq_mul]
  rw [← smul_mul_assoc, abs_neg_exp_smul_cpow]

/-! ## Real Gaussian prime and continuum masses -/

/-- The Gaussian prime mass `Σ Λ(n) n^{-σ} e^{-yn²}`. -/
def gaussianWeightedPrimeMass (σ y : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) * Real.exp (-(y * (n : ℝ) ^ 2))

/-- The Gaussian continuum mass `∫₁^∞ u^{-σ} e^{-yu²} du`. -/
def gaussianWeightedContinuumMass (σ y : ℝ) : ℝ :=
  ∫ u in Ioi (1 : ℝ), u ^ (-σ) * Real.exp (-(y * u ^ 2))

theorem gaussianPrimeContinuumGap_ofReal (σ y : ℝ) :
    gaussianPrimeContinuumGap (σ : ℂ) y =
      ((gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y : ℝ) : ℂ) := by
  rw [gaussianPrimeContinuumGap, gaussianDampedPrimeSum, gaussianIncompleteMellin,
    integral_Ici_eq_integral_Ioi, Complex.ofReal_sub, gaussianWeightedPrimeMass, gaussianWeightedContinuumMass,
    Complex.ofReal_tsum, ← integral_complex_ofReal]
  congr 1
  · refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h
      rw [LSeries.term_of_ne_zero h.ne', Real.rpow_neg hn0.le]
      push_cast
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hn0.le]
      push_cast
      ring
  · refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
    rw [show (1 : ℂ) - σ - 1 = ((-σ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hu0.le]
    push_cast
    ring_nf

/-! ## An unconditional power bound near `y = 0` -/

theorem tsum_nat_mul_exp_neg_le {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∑' n : ℕ, (n : ℝ) * Real.exp (-y) ^ n ≤ Real.exp 2 * y ^ (-(2 : ℝ)) := by
  have hr : ‖Real.exp (-y)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := Real.exp_lt_exp.2 (show -y < 0 by linarith)
    rwa [Real.exp_zero] at this
  rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
  have he : 0 < Real.exp (-y) := Real.exp_pos _
  have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- `1 - e^{-y} ≥ y e^{-1}`
  have hgap : y * Real.exp (-1) ≤ 1 - Real.exp (-y) := by
    have h1 : y * Real.exp (-y) ≤ 1 - Real.exp (-y) := by
      have := Real.add_one_le_exp y
      have hmul := mul_le_mul_of_nonneg_left this he.le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
      nlinarith
    have h2 : Real.exp (-1) ≤ Real.exp (-y) := Real.exp_le_exp.2 (by linarith)
    nlinarith
  have hpos : 0 < y * Real.exp (-1) := by positivity
  have hsq : (y * Real.exp (-1)) ^ 2 ≤ (1 - Real.exp (-y)) ^ 2 := by
    gcongr
  have hy2 : y ^ (-(2 : ℝ)) = (y ^ 2)⁻¹ := by
    rw [Real.rpow_neg hy.le]; norm_cast
  rw [hy2, div_le_iff₀ (by nlinarith)]
  have hexp : Real.exp 2 * Real.exp (-1) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  calc Real.exp (-y) ≤ 1 := he1
    _ = Real.exp 2 * Real.exp (-1) ^ 2 := hexp.symm
    _ = Real.exp 2 * (y ^ 2)⁻¹ * (y * Real.exp (-1)) ^ 2 := by
        rw [mul_pow]
        field_simp
    _ ≤ Real.exp 2 * (y ^ 2)⁻¹ * (1 - Real.exp (-y)) ^ 2 := by gcongr

/-- **Unconditional bound.**  For `Re s ≥ 0` and `0 < y ≤ 1`,
`‖Σ Λ(n) n^{-s} e^{-yn²} − E(y, 1−s)‖ ≤ (e² + Γ(½)) y^{-2}`. -/
theorem norm_gaussianPrimeContinuumGap_le {s : ℂ} (hs : 0 ≤ s.re) {y : ℝ} (hy : 0 < y)
    (hy1 : y ≤ 1) :
    ‖gaussianPrimeContinuumGap s y‖ ≤ (Real.exp 2 + Real.Gamma (1 / 2)) * y ^ (-(2 : ℝ)) := by
  have hprime : ‖gaussianDampedPrimeSum s y‖ ≤ Real.exp 2 * y ^ (-(2 : ℝ)) := by
    have hsn := summable_norm_vonMangoldt_term_mul_gaussian hs hy
    have hbound : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
        (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ ≤ (n : ℝ) * Real.exp (-y) ^ n := by
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        ← Real.exp_nat_mul]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      refine mul_le_mul (norm_vonMangoldt_term_le hs n) (Real.exp_le_exp.2 ?_) (by positivity) hn0
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h
        have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq hy.le]
    have hsg : Summable fun n : ℕ => (n : ℝ) * Real.exp (-y) ^ n := by
      refine (Real.summable_pow_mul_exp_neg_nat_mul 1 hy).congr fun n => ?_
      rw [pow_one, ← Real.exp_nat_mul]; ring_nf
    have hsn' : Summable fun n => ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
        (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsg
    calc ‖gaussianDampedPrimeSum s y‖ ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
          (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ)‖ := norm_tsum_le_tsum_norm hsn'
      _ ≤ ∑' n : ℕ, (n : ℝ) * Real.exp (-y) ^ n := hsn'.tsum_le_tsum hbound hsg
      _ ≤ _ := tsum_nat_mul_exp_neg_le hy hy1
  have hE : ‖gaussianIncompleteMellin y (1 - s)‖ ≤ Real.Gamma (1 / 2) * y ^ (-(2 : ℝ)) := by
    have h := norm_gaussianIncompleteMellin_le hy (r := 0) (by norm_num) (b := 1 - s)
      (by simp; linarith)
    have hG : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have hpow : y ^ (-(0 + 1) / 2 : ℝ) ≤ y ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num)
    calc ‖gaussianIncompleteMellin y (1 - s)‖ ≤
          y ^ (-(0 + 1) / 2 : ℝ) * (1 / 2) * Real.Gamma ((0 + 1) / 2) := h
      _ ≤ y ^ (-(2 : ℝ)) * 1 * Real.Gamma (1 / 2) := by
          rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num]
          gcongr
          norm_num
      _ = _ := by ring
  calc ‖gaussianPrimeContinuumGap s y‖ ≤ ‖gaussianDampedPrimeSum s y‖ +
        ‖gaussianIncompleteMellin y (1 - s)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

theorem gaussianPrimeContinuumGap_isBigO_nhdsGT_two {s : ℂ} (hs : 0 ≤ s.re) :
    gaussianPrimeContinuumGap s =O[𝓝[>] 0] (fun y : ℝ => y ^ (-(2 : ℝ))) := by
  refine IsBigO.of_bound (Real.exp 2 + Real.Gamma (1 / 2)) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy.1 _)]
  exact norm_gaussianPrimeContinuumGap_le hs hy.1 hy.2.le

/-! ## Splitting the gap at `y = 1` -/

theorem locallyIntegrableOn_gap {s : ℂ} (hs : 0 < s.re) :
    LocallyIntegrableOn (gaussianPrimeContinuumGap s) (Ioi 0) :=
  (continuousOn_gaussianPrimeContinuumGap hs).locallyIntegrableOn (μ := volume) measurableSet_Ioi

theorem mellinConvergent_gap {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : 2 < z.re) :
    MellinConvergent (gaussianPrimeContinuumGap s) z :=
  mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_gap hs)
    (gaussianPrimeContinuumGap_isBigO_atTop hs (z.re + 1)) (by linarith)
    (gaussianPrimeContinuumGap_isBigO_nhdsGT_two hs.le) hz

/-- The part of the gap beyond `y = 1` has an entire Mellin transform. -/
theorem differentiable_mellin_indicator_gap {s : ℂ} (hs : 0 < s.re) :
    Differentiable ℂ (mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap s))) := by
  intro z
  have hloc : LocallyIntegrableOn ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap s))
      (Ioi 0) := fun x hx => by
    obtain ⟨U, hU, hint⟩ := locallyIntegrableOn_gap hs x hx
    exact ⟨U, hU, hint.indicator measurableSet_Ioi⟩
  refine mellin_differentiableAt_of_isBigO_rpow (a := z.re + 1) (b := z.re - 1) hloc ?_
    (by linarith) ?_ (by linarith)
  · refine (gaussianPrimeContinuumGap_isBigO_atTop hs (z.re + 1)).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    rw [indicator_of_mem (show y ∈ Ioi (1 : ℝ) from hy)]
  · refine IsBigO.of_bound 0 ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    rw [indicator_of_notMem (show y ∉ Ioi (1 : ℝ) by simp; exact hy.2.le), norm_zero, zero_mul]

theorem mellin_gap_eq_add_indicator {s : ℂ} (hs : 0 < s.re) {z : ℂ} (hz : 2 < z.re) :
    mellin (gaussianPrimeContinuumGap s) z =
      mellin ((Ioc (0 : ℝ) 1).indicator (gaussianPrimeContinuumGap s)) z +
        mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap s)) z := by
  have hconv := mellinConvergent_gap hs hz
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) •
      (Ioc (0 : ℝ) 1).indicator (gaussianPrimeContinuumGap s) t) (Ioi 0) := by
    refine (hconv.indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) •
      (Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap s) t) (Ioi 0) := by
    refine (hconv.indicator (measurableSet_Ioi (a := (1 : ℝ)))).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht]
  rw [mellin, mellin, mellin, ← integral_add h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht0, ht1⟩),
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) by simp; exact ht1), smul_zero, add_zero]
  · push Not at ht1
    rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 by simp; intro _; exact ht1),
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht1), smul_zero, zero_add]

theorem mellin_indicator_Ioc_rpow (B : ℂ) (a : ℝ) {z : ℂ} (hz : a < z.re) :
    mellin ((Ioc (0 : ℝ) 1).indicator (fun y : ℝ => B * ((y ^ (-a) : ℝ) : ℂ))) z = B / (z - a) := by
  have hz0 : z - a ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (g := (Ioc (0 : ℝ) 1).indicator
    (fun t : ℝ => (t : ℂ) ^ (z - a - 1) * B)) (fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      by_cases ht1 : t ∈ Ioc (0 : ℝ) 1
      · simp only [indicator_of_mem ht1, smul_eq_mul]
        rw [Complex.ofReal_cpow ht0.le, show z - a - 1 = (z - 1) + ((-a : ℝ) : ℂ) by push_cast; ring,
          Complex.cpow_add _ _ (by exact_mod_cast ht0.ne')]
        ring
      · simp [ht1]),
    setIntegral_indicator measurableSet_Ioc,
    show Ioi (0 : ℝ) ∩ Ioc 0 1 = Ioc 0 1 from inter_eq_right.2 Ioc_subset_Ioi_self,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_mul_const,
    integral_cpow (Or.inl (by simp; linarith))]
  rw [show z - a - 1 + 1 = z - a by ring, Complex.ofReal_one, Complex.one_cpow,
    Complex.ofReal_zero, Complex.zero_cpow hz0]
  field_simp
  ring

/-! ## The budget profile and its Laplace carrier -/

/-- The signed budget profile `h(u) = B e^{au} − η (prime mass − continuum mass)(e^{-u})`. -/
def gaussianBudgetProfile (η σ a B u : ℝ) : ℝ :=
  B * Real.exp (a * u) - η * (gaussianWeightedPrimeMass σ (Real.exp (-u)) -
    gaussianWeightedContinuumMass σ (Real.exp (-u)))

theorem abs_gaussianWeightedGap_le {σ : ℝ} (hσ : 0 ≤ σ) {u : ℝ} (hu : 0 ≤ u) :
    |gaussianWeightedPrimeMass σ (Real.exp (-u)) - gaussianWeightedContinuumMass σ (Real.exp (-u))|
      ≤ (Real.exp 2 + Real.Gamma (1 / 2)) * Real.exp (2 * u) := by
  have hy : 0 < Real.exp (-u) := Real.exp_pos _
  have hy1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h := norm_gaussianPrimeContinuumGap_le (s := (σ : ℂ)) (by simpa using hσ) hy hy1
  rw [gaussianPrimeContinuumGap_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  rwa [← Real.exp_mul, show -u * -(2 : ℝ) = 2 * u by ring] at h

theorem continuous_gaussianBudgetProfile {σ : ℝ} (hσ : 0 < σ) (η a B : ℝ) :
    Continuous (gaussianBudgetProfile η σ a B) := by
  have hc := (continuousOn_gaussianPrimeContinuumGap (s := (σ : ℂ)) (by simpa using hσ)).comp_continuous
    (by fun_prop : Continuous fun u : ℝ => Real.exp (-u)) (fun u => Real.exp_pos _)
  have heq : gaussianBudgetProfile η σ a B =
      fun u => B * Real.exp (a * u) - η * (gaussianPrimeContinuumGap (σ : ℂ) (Real.exp (-u))).re := by
    funext u
    rw [gaussianBudgetProfile, gaussianPrimeContinuumGap_ofReal, Complex.ofReal_re]
  rw [heq]
  exact (continuous_const.mul (by fun_prop)).sub
    (continuous_const.mul (Complex.continuous_re.comp hc))

theorem abs_gaussianBudgetProfile_le {σ : ℝ} (hσ : 0 ≤ σ) {η : ℝ} (hη : |η| ≤ 1) {a : ℝ}
    (ha : a ≤ 2) (B : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |gaussianBudgetProfile η σ a B u| ≤
      (|B| + (Real.exp 2 + Real.Gamma (1 / 2))) * Real.exp (2 * u) := by
  rw [gaussianBudgetProfile]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := abs_gaussianWeightedGap_le hσ hu
  have h2 := mul_le_mul hη h1 (abs_nonneg _) zero_le_one
  have h3 : Real.exp (a * u) ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by nlinarith)
  have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg B)
  linarith

theorem integrableOn_gaussianBudgetProfile_mul_cexp {σ : ℝ} (hσ : 0 < σ) {η : ℝ} (hη : |η| ≤ 1)
    {a : ℝ} (ha : a ≤ 2) (B : ℝ) {z : ℂ} (hz : 3 < z.re) :
    IntegrableOn (fun u : ℝ => (gaussianBudgetProfile η σ a B u : ℂ) * Complex.exp (-z * u))
      (Ioi 0) := by
  set C₀ : ℝ := Real.exp 2 + Real.Gamma (1 / 2) with hC₀
  have hmaj : IntegrableOn (fun u : ℝ => (|B| + C₀) * Real.exp (-(z.re - 2) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < z.re - 2)).const_mul _
  refine hmaj.mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp (continuous_gaussianBudgetProfile hσ η a B)).mul
      (by fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
    have hbd := abs_gaussianBudgetProfile_le hσ.le hη ha B hu0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-z * (u : ℂ)).re = -z.re * u := by simp
    rw [hre]
    have he1 : Real.exp (-z.re * u) ≤ Real.exp (-(z.re - 2) * u) :=
      Real.exp_le_exp.2 (by nlinarith)
    have he2 : Real.exp (2 * u) * Real.exp (-z.re * u) = Real.exp (-(z.re - 2) * u) := by
      rw [← Real.exp_add]; ring_nf
    have hC0 : 0 ≤ C₀ := by
      have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
      positivity
    calc |gaussianBudgetProfile η σ a B u| * Real.exp (-z.re * u)
        ≤ ((|B| + C₀) * Real.exp (2 * u)) * Real.exp (-z.re * u) :=
          mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
      _ = (|B| + C₀) * Real.exp (-(z.re - 2) * u) := by rw [← he2]; ring

/-! ## Exponentially thickened Laplace carriers -/

/-- The Laplace carrier with density `f(u) + e^{-u}`.  The reference density `e^{-u}` makes the
Laplace mass diverge left of `-1`, so a convergence abscissa exists. -/
def expThickenedCarrier (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun u => ENNReal.ofReal (f u + Real.exp (-u))

theorem measurable_expThickenedDensity {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun u => ENNReal.ofReal (f u + Real.exp (-u)) :=
  ENNReal.measurable_ofReal.comp (hf.add (by fun_prop)).measurable

theorem laplaceMass_expThickenedCarrier {f : ℝ → ℝ} (hf : Continuous f) (τ : ℝ) :
    laplaceMass (expThickenedCarrier f) τ =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (f u + Real.exp (-u)) *
        ENNReal.ofReal (Real.exp (-τ * u)) := by
  rw [laplaceMass, expThickenedCarrier, setLIntegral_withDensity_eq_setLIntegral_mul _
    (measurable_expThickenedDensity hf) (by fun_prop) measurableSet_Ioi]
  rfl

theorem laplaceMass_expThickenedCarrier_ne_top {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) {τ : ℝ} (hτ : -1 < τ)
    (hint : IntegrableOn (fun u : ℝ => f u * Real.exp (-τ * u)) (Ioi 0)) :
    laplaceMass (expThickenedCarrier f) τ ≠ ⊤ := by
  rw [laplaceMass_expThickenedCarrier hf]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-u) * Real.exp (-τ * u)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 (show (0 : ℝ) < τ + 1 by linarith)).congr_fun
      (fun u _ => ?_) measurableSet_Ioi
    rw [← Real.exp_add]; ring_nf
  have hsum : IntegrableOn (fun u : ℝ => (f u + Real.exp (-u)) * Real.exp (-τ * u)) (Ioi 0) := by
    refine (hint.add h2).congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]
    ring
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hsum.lintegral_lt_top)
  refine setLIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [← ENNReal.ofReal_mul (by have := hf0 u hu; positivity)]

theorem laplaceMass_expThickenedCarrier_eq_top {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) :
    laplaceMass (expThickenedCarrier f) (-2) = ⊤ := by
  rw [laplaceMass_expThickenedCarrier hf]
  refine top_le_iff.1 ?_
  calc (⊤ : ℝ≥0∞) = ∫⁻ u in Ioi (0 : ℝ), 1 := by
        rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioi]
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi (fun u hu => ?_)
        have hu0 : (0 : ℝ) < u := hu
        rw [← ENNReal.ofReal_mul (by have := hf0 u hu; positivity), ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 1 ≤ Real.exp (-(-2) * u) := Real.one_le_exp (by linarith)
        have h2 : Real.exp (-u) * Real.exp (-(-2) * u) = Real.exp u := by
          rw [← Real.exp_add]; ring_nf
        have h3 : 1 ≤ Real.exp u := Real.one_le_exp hu0.le
        have := hf0 u hu
        nlinarith [Real.exp_pos (-u), Real.exp_pos (-(-2) * u)]

theorem complexLaplace_expThickenedCarrier {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) {z : ℂ} (hz : -1 < z.re)
    (hint : IntegrableOn (fun u : ℝ => (f u : ℂ) * Complex.exp (-z * u)) (Ioi 0)) :
    complexLaplace (expThickenedCarrier f) z =
      (∫ u in Ioi (0 : ℝ), (f u : ℂ) * Complex.exp (-z * u)) + 1 / (z + 1) := by
  have hz1 : z + 1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hre : (-(z + 1)).re < 0 := by simp; linarith
  rw [complexLaplace, expThickenedCarrier, restrict_withDensity measurableSet_Ioi,
    integral_withDensity_eq_integral_toReal_smul (measurable_expThickenedDensity hf)
      (Eventually.of_forall fun u => ENNReal.ofReal_lt_top)]
  have hpt : ∀ u ∈ Ioi (0 : ℝ), (ENNReal.ofReal (f u + Real.exp (-u))).toReal •
      Complex.exp (-z * u) = (f u : ℂ) * Complex.exp (-z * u) + Complex.exp (-(z + 1) * u) := by
    intro u hu
    rw [ENNReal.toReal_ofReal (by have := hf0 u hu; positivity), Complex.real_smul]
    push_cast
    rw [add_mul, ← Complex.exp_add]
    congr 2
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add hint
      (integrableOn_exp_mul_complex_Ioi hre 0), integral_exp_mul_complex_Ioi hre 0]
  congr 1
  push_cast
  field_simp
  simp

/-- If `f ≥ 0` has finite Laplace mass at every exponent `τ > a ≥ 0`, the thickened carrier has an
abscissa `≤ a`. -/
theorem exists_isAbscissa_expThickenedCarrier_le {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ u : ℝ, 0 < u → 0 ≤ f u) {a : ℝ} (ha : 0 ≤ a)
    (hint : ∀ τ : ℝ, a < τ → IntegrableOn (fun u : ℝ => f u * Real.exp (-τ * u)) (Ioi 0)) :
    ∃ c : ℝ, IsAbscissa (expThickenedCarrier f) c ∧ c ≤ a := by
  obtain ⟨c, hc⟩ := exists_isAbscissa
    ⟨a + 1, laplaceMass_expThickenedCarrier_ne_top hf hf0 (by linarith) (hint (a + 1) (by linarith))⟩
    ⟨-2, laplaceMass_expThickenedCarrier_eq_top hf hf0⟩
  refine ⟨c, hc, ?_⟩
  by_contra hcpos
  push Not at hcpos
  exact laplaceMass_expThickenedCarrier_ne_top hf hf0 (by linarith)
    (hint ((a + c) / 2) (by linarith)) (hc.2 ((a + c) / 2) (by linarith))

theorem integrableOn_ofReal_mul_cexp_of_abs_le {f g : ℝ → ℝ} (hg : Continuous g) {z : ℂ}
    (hint : IntegrableOn (fun u : ℝ => (f u : ℂ) * Complex.exp (-z * u)) (Ioi 0))
    (hle : ∀ u, |g u| ≤ |f u|) :
    IntegrableOn (fun u : ℝ => (g u : ℂ) * Complex.exp (-z * u)) (Ioi 0) := by
  refine hint.norm.mono' ((Complex.continuous_ofReal.comp hg).mul
    (by fun_prop)).aestronglyMeasurable.restrict (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hle u) (norm_nonneg _)

theorem integrableOn_real_mul_exp_of_cexp {f : ℝ → ℝ} (hf : Continuous f) {τ : ℝ}
    (hint : IntegrableOn (fun u : ℝ => (f u : ℂ) * Complex.exp (-(τ : ℂ) * u)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => f u * Real.exp (-τ * u)) (Ioi 0) := by
  refine hint.norm.mono' (hf.mul (by fun_prop)).aestronglyMeasurable.restrict
    (Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Complex.norm_exp, abs_of_pos (Real.exp_pos _)]
  simp

theorem integral_gaussianBudgetProfile_mul_cexp {σ : ℝ} (hσ : 0 < σ) (η : ℝ) {a : ℝ}
    (ha : a ≤ 2) (B : ℝ) {z : ℂ} (hz : 3 < z.re) :
    ∫ u in Ioi (0 : ℝ), (gaussianBudgetProfile η σ a B u : ℂ) * Complex.exp (-z * u) =
      B / (z - a) - η * (mellin (gaussianPrimeContinuumGap (σ : ℂ)) z -
        mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ : ℂ))) z) := by
  set G : ℝ → ℂ := gaussianPrimeContinuumGap (σ : ℂ) with hGdef
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  set f₀ : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator
    (fun y : ℝ => (B : ℂ) * ((y ^ (-a) : ℝ) : ℂ) - η * G y) with hf₀
  have h1 : mellin f₀ z =
      ∫ u in Ioi (0 : ℝ), (gaussianBudgetProfile η σ a B u : ℂ) * Complex.exp (-z * u) := by
    rw [mellin_eq_integral_exp_neg, ← integral_Ici_eq_integral_Ioi,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici (0 : ℝ))]
    · refine setIntegral_congr_fun measurableSet_Ici fun u hu => ?_
      have hu0 : (0 : ℝ) ≤ u := hu
      rw [hf₀, indicator_of_mem (show Real.exp (-u) ∈ Ioc (0 : ℝ) 1 from
        ⟨Real.exp_pos _, Real.exp_le_one_iff.2 (by linarith)⟩), hGdef,
        gaussianPrimeContinuumGap_ofReal, gaussianBudgetProfile, ← Real.exp_mul,
        show -u * -a = a * u by ring]
      push_cast
      ring
    · intro u hu
      have hu0 : u < 0 := not_le.1 hu
      rw [hf₀, indicator_of_notMem (show Real.exp (-u) ∉ Ioc (0 : ℝ) 1 by
        intro h
        have h1 := h.2
        have h2 := Real.one_lt_exp_iff.2 (show 0 < -u by linarith)
        linarith), mul_zero]
  have hconvG := mellinConvergent_gap hs (show 2 < z.re by linarith)
  have hiG : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • (Ioc (0 : ℝ) 1).indicator G t)
      (Ioi 0) := by
    refine (hconvG.indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht, hGdef]
  have hiB : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) •
      (Ioc (0 : ℝ) 1).indicator (fun y : ℝ => (B : ℂ) * ((y ^ (-a) : ℝ) : ℂ)) t) (Ioi 0) := by
    have hI : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - a - 1) * B) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        ((intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).mul_const _)
    have hI' : IntegrableOn ((Ioc (0 : ℝ) 1).indicator
        (fun t : ℝ => (t : ℂ) ^ (z - a - 1) * B)) (Ioi 0) := by
      rw [integrableOn_indicator_iff measurableSet_Ioc,
        inter_eq_left.2 Ioc_subset_Ioi_self]
      exact hI
    refine hI'.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    by_cases ht1 : t ∈ Ioc (0 : ℝ) 1
    · simp only [indicator_of_mem ht1, smul_eq_mul]
      rw [Complex.ofReal_cpow ht0.le, show z - a - 1 = (z - 1) + ((-a : ℝ) : ℂ) by push_cast; ring,
        Complex.cpow_add _ _ (by exact_mod_cast ht0.ne')]
      ring
    · simp [ht1]
  have h2 : mellin f₀ z = mellin ((Ioc (0 : ℝ) 1).indicator
      (fun y : ℝ => (B : ℂ) * ((y ^ (-a) : ℝ) : ℂ))) z -
      η * mellin ((Ioc (0 : ℝ) 1).indicator G) z := by
    rw [mellin, mellin, mellin, ← integral_const_mul, ← integral_sub hiB (hiG.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [hf₀, ht]
    ring
  rw [← h1, h2, mellin_indicator_Ioc_rpow _ _ (by linarith),
    mellin_gap_eq_add_indicator hs (by linarith)]
  ring

/-! ## The one-sided budget law -/

theorem mellin_gap_eq_gamma_mul {σ : ℝ} (hσ : 0 < σ) {w : ℂ} (hw : 3 < w.re) :
    mellin (gaussianPrimeContinuumGap (σ : ℂ)) w = Complex.Gamma w *
      (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) - logDeriv xi ((σ : ℂ) + 2 * w)) := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hz1 : 1 < ((σ : ℂ) + 2 * w).re := by simp; linarith
  have hz1' : (σ : ℂ) + 2 * w - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [mellin_gaussianPrimeContinuumGap hs (a := 2) (by norm_num)
    (gaussianPrimeContinuumGap_isBigO_nhdsGT_two hs.le) (by linarith) (by simp; linarith),
    logDeriv_xi_eq_arithmetic hz1, gaussianArchimedeanCurrent]
  ring

/-- **Carrier identity.**  For `Re w > 3` the Laplace transform of the positive part of the budget
profile equals `B/(w − a) − η(Γ(w)(A − ξ'/ξ)(σ + 2w) − T(w))` plus the transform of the negative
part, where `T` is the Mellin transform of the gap beyond `y = 1`. -/
theorem complexLaplace_gaussianBudgetCarrier_eq {σ : ℝ} (hσ : 0 < σ) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {a : ℝ} (ha1 : a ≤ 1) (B : ℝ) {w : ℂ} (hw : 3 < w.re) :
    complexLaplace (expThickenedCarrier fun u => max (gaussianBudgetProfile η σ a B u) 0) w =
      B / (w - a) - η * (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
        logDeriv xi ((σ : ℂ) + 2 * w)) -
          mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ : ℂ))) w) +
      complexLaplace (expThickenedCarrier fun u => max (-gaussianBudgetProfile η σ a B u) 0) w := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hηabs : |η| ≤ 1 := by rcases hη with h | h <;> simp [h]
  set h : ℝ → ℝ := gaussianBudgetProfile η σ a B with hhdef
  have hc : Continuous h := continuous_gaussianBudgetProfile hσ η a B
  set hP : ℝ → ℝ := fun u => max (h u) 0 with hPdef
  set hN : ℝ → ℝ := fun u => max (-h u) 0 with hNdef
  have hPc : Continuous hP := hc.max continuous_const
  have hNc : Continuous hN := hc.neg.max continuous_const
  have hP0 : ∀ u : ℝ, 0 < u → 0 ≤ hP u := fun u _ => le_max_right _ _
  have hN0 : ∀ u : ℝ, 0 < u → 0 ≤ hN u := fun u _ => le_max_right _ _
  have hPle : ∀ u, |hP u| ≤ |h u| := by
    intro u; simp only [hPdef]
    rcases le_total 0 (h u) with h0 | h0
    · rw [max_eq_left h0]
    · rw [max_eq_right h0, abs_zero]; exact abs_nonneg _
  have hsplit : ∀ u, h u = hP u - hN u := by
    intro u; simp only [hPdef, hNdef]
    rcases le_total 0 (h u) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  have hNle : ∀ u, |hN u| ≤ |h u| := by
    intro u; simp only [hNdef]
    rcases le_total 0 (h u) with h0 | h0
    · rw [max_eq_right (by linarith), abs_zero]; exact abs_nonneg _
    · rw [max_eq_left (by linarith), abs_neg]
  have hiH := integrableOn_gaussianBudgetProfile_mul_cexp hσ hηabs (a := a) (by linarith) B hw
  have hiP := integrableOn_ofReal_mul_cexp_of_abs_le hPc hiH hPle
  have hiN := integrableOn_ofReal_mul_cexp_of_abs_le hNc hiH hNle
  rw [complexLaplace_expThickenedCarrier hPc hP0 (by linarith) hiP,
    complexLaplace_expThickenedCarrier hNc hN0 (by linarith) hiN]
  have hH : ∫ u in Ioi (0 : ℝ), (h u : ℂ) * Complex.exp (-w * u) =
      (∫ u in Ioi (0 : ℝ), (hP u : ℂ) * Complex.exp (-w * u)) -
        ∫ u in Ioi (0 : ℝ), (hN u : ℂ) * Complex.exp (-w * u) := by
    rw [← integral_sub hiP hiN]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [hsplit u]
    push_cast
    ring
  have hI := integral_gaussianBudgetProfile_mul_cexp hσ η (a := a) (by linarith) B hw
  rw [← hhdef] at hI
  rw [mellin_gap_eq_gamma_mul hσ hw] at hI
  linear_combination hI - hH

/-- **Landau for the budget carrier.**  If the negative part of the budget profile has finite
Laplace mass at every exponent `τ > a`, the positive carrier has an abscissa `≤ a`. -/
theorem exists_isAbscissa_gaussianBudgetCarrier_le {σ : ℝ} (hσ : 0 < σ) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (B : ℝ)
    (hexc : ∀ τ : ℝ, a < τ → IntegrableOn
      (fun u : ℝ => max (-gaussianBudgetProfile η σ a B u) 0 * Real.exp (-τ * u)) (Ioi 0)) :
    ∃ c₀ : ℝ, IsAbscissa (expThickenedCarrier fun u => max (gaussianBudgetProfile η σ a B u) 0)
      c₀ ∧ c₀ ≤ a := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hηabs : |η| ≤ 1 := by rcases hη with h | h <;> simp [h]
  set h : ℝ → ℝ := gaussianBudgetProfile η σ a B with hhdef
  have hc : Continuous h := continuous_gaussianBudgetProfile hσ η a B
  set hP : ℝ → ℝ := fun u => max (h u) 0 with hPdef
  set hN : ℝ → ℝ := fun u => max (-h u) 0 with hNdef
  have hPc : Continuous hP := hc.max continuous_const
  have hNc : Continuous hN := hc.neg.max continuous_const
  have hP0 : ∀ u : ℝ, 0 < u → 0 ≤ hP u := fun u _ => le_max_right _ _
  have hN0 : ∀ u : ℝ, 0 < u → 0 ≤ hN u := fun u _ => le_max_right _ _
  have hPle : ∀ u, |hP u| ≤ |h u| := by
    intro u; simp only [hPdef]
    rcases le_total 0 (h u) with h0 | h0
    · rw [max_eq_left h0]
    · rw [max_eq_right h0, abs_zero]; exact abs_nonneg _
  set νP : Measure ℝ := expThickenedCarrier hP with hνP
  set νN : Measure ℝ := expThickenedCarrier hN with hνN
  set T : ℂ → ℂ := mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ : ℂ))) with hT
  have hTd : Differentiable ℂ T := differentiable_mellin_indicator_gap hs
  obtain ⟨cN, hcN, hcN0⟩ := exists_isAbscissa_expThickenedCarrier_le hNc hN0 ha hexc
  have hLNd : DifferentiableOn ℂ (complexLaplace νN) {w : ℂ | a < w.re} :=
    (differentiableOn_complexLaplace hcN).mono fun w hw => lt_of_le_of_lt hcN0 hw
  have hfarL : ∀ w : ℂ, 3 < w.re → complexLaplace νP w =
      B / (w - a) - η * (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
        logDeriv xi ((σ : ℂ) + 2 * w)) - T w) + complexLaplace νN w :=
    fun w hw => complexLaplace_gaussianBudgetCarrier_eq hσ hη ha1 B hw
  set Ψ : ℂ → ℂ := fun w => B / (w - a) - η * (Complex.Gamma w *
      (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) - logDeriv xi ((σ : ℂ) + 2 * w)) - T w) +
      complexLaplace νN w with hΨ
  set V : Set ℂ := {w : ℂ | a < w.re} ∩ {w : ℂ | xi ((σ : ℂ) + 2 * w) ≠ 0} with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_ne_fun (xi_differentiable.continuous.comp (by fun_prop)) continuous_const)
  have hΨd : DifferentiableOn ℂ Ψ V := by
    intro w hw
    have hwa : a < w.re := hw.1
    have hw0 : 0 < w.re := lt_of_le_of_lt ha hwa
    have hxw : xi ((σ : ℂ) + 2 * w) ≠ 0 := hw.2
    have hw0' : w - a ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hre : 0 < ((σ : ℂ) + 2 * w).re := by simp; linarith
    have hΓ : DifferentiableAt ℂ Complex.Gamma w := Complex.differentiableAt_Gamma w (fun m h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    have hA : DifferentiableAt ℂ (fun w : ℂ => gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w)) w :=
      (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w
        (by fun_prop)
    have hL : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi ((σ : ℂ) + 2 * w)) w := by
      have hd : DifferentiableAt ℂ (fun ζ => deriv xi ζ / xi ζ) ((σ : ℂ) + 2 * w) :=
        ((xi_differentiable.analyticAt _).deriv.differentiableAt).div
          (xi_differentiable _) hxw
      exact hd.comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w (by fun_prop)
    have hN' : DifferentiableAt ℂ (complexLaplace νN) w :=
      hLNd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hwa)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_const _).div (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - (a : ℂ)) w) hw0').sub
      ((differentiableAt_const _).mul ((hΓ.mul (hA.sub hL)).sub (hTd w)))).add hN'
  have hΨan : ∀ t : ℝ, a < t → AnalyticAt ℂ Ψ (t : ℂ) := by
    intro t ht
    have hmem : (t : ℂ) ∈ V := by
      refine ⟨by simpa using ht, ?_⟩
      have hcast : (σ : ℂ) + 2 * (t : ℂ) = ((σ + 2 * t : ℝ) : ℂ) := by push_cast; ring
      rw [Set.mem_setOf_eq, hcast]
      exact xi_ne_zero_of_real _
    exact hΨd.analyticAt (hVo.mem_nhds hmem)
  -- the positive part: Landau puts the abscissa `≤ a`
  have hiP4 : IntegrableOn (fun u : ℝ => hP u * Real.exp (-4 * u)) (Ioi 0) :=
    integrableOn_real_mul_exp_of_cexp hPc (by
      have := integrableOn_ofReal_mul_cexp_of_abs_le hPc
        (integrableOn_gaussianBudgetProfile_mul_cexp hσ hηabs (a := a) (by linarith) B (z := (4 : ℝ))
          (by simp; norm_num))
        hPle
      simpa using this)
  obtain ⟨c, hcP⟩ := exists_isAbscissa
    ⟨4, laplaceMass_expThickenedCarrier_ne_top hPc hP0 (by norm_num) hiP4⟩
    ⟨-2, laplaceMass_expThickenedCarrier_eq_top hPc hP0⟩
  by_cases hc0 : c ≤ a
  · exact ⟨c, hcP, hc0⟩
  · push Not at hc0
    refine ⟨a, RHTower.LiouvilleTriangularHeadOscillation.isAbscissa_eq_of_analyticAt_real hcP
      hc0.le (le_max_left c 4) (fun t ht => hΨan t ht) (fun w hw => ?_), le_rfl⟩
    have hw3 : 3 < w.re := lt_of_le_of_lt (by have := le_max_right c 4; linarith) hw
    exact hfarL w hw3

/-- **Integrated one-sided excess law.**  Let `σ > 0`, `0 ≤ a ≤ 1`, `B` real and `η = ±1`.  If the
excess `(η(P_σ − C_σ)(y) − B y^{-a})⁺` has finite weighted integral `∫₀¹ (·)(y) y^{τ−1} dy < ∞` for
every `τ > a` (written in the logarithmic variable `y = e^{-u}`), then `ξ` has no zero with
`Re z > σ + 2a`.

Split the deficit `h = B − (P_σ − C_σ)(e^{-u})` as `h⁺ − h⁻`.  The thickened carrier of `h⁻` has
abscissa `≤ 0` by hypothesis; the carrier of `h⁺` has transform
`B/z − Γ(z)(A − ξ'/ξ)(σ + 2z) + T(z) + L⁻(z)`, analytic at every positive real point, so Landau's
theorem puts its abscissa `≤ 0` as well.  Hence `ξ'/ξ(σ + 2z)` continues holomorphically to
`Re z > 0`. -/
theorem xi_ne_zero_of_gaussianPrimeExcess {σ : ℝ} (hσ : 0 < σ) {η : ℝ} (hη : η = 1 ∨ η = -1)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (B : ℝ)
    (hexc : ∀ τ : ℝ, a < τ → IntegrableOn
      (fun u : ℝ => max (-gaussianBudgetProfile η σ a B u) 0 * Real.exp (-τ * u)) (Ioi 0))
    {z : ℂ} (hz : σ + 2 * a < z.re) : xi z ≠ 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hη2 : (η : ℂ) * η = 1 := by rcases hη with h | h <;> simp [h]
  have hc : Continuous (gaussianBudgetProfile η σ a B) := continuous_gaussianBudgetProfile hσ η a B
  set νP : Measure ℝ := expThickenedCarrier fun u => max (gaussianBudgetProfile η σ a B u) 0
    with hνP
  set νN : Measure ℝ := expThickenedCarrier fun u => max (-gaussianBudgetProfile η σ a B u) 0
    with hνN
  set T : ℂ → ℂ := mellin ((Ioi (1 : ℝ)).indicator (gaussianPrimeContinuumGap (σ : ℂ))) with hT
  have hTd : Differentiable ℂ T := differentiable_mellin_indicator_gap hs
  obtain ⟨cN, hcN, hcN0⟩ := exists_isAbscissa_expThickenedCarrier_le
    (hc.neg.max continuous_const) (fun u _ => le_max_right _ _) ha hexc
  have hLNd : DifferentiableOn ℂ (complexLaplace νN) {w : ℂ | a < w.re} :=
    (differentiableOn_complexLaplace hcN).mono fun w hw => lt_of_le_of_lt hcN0 hw
  obtain ⟨c₀, hc₀, hc₀0⟩ := exists_isAbscissa_gaussianBudgetCarrier_le hσ hη ha ha1 B hexc
  have hfarL : ∀ w : ℂ, 3 < w.re → complexLaplace νP w =
      B / (w - a) - η * (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
        logDeriv xi ((σ : ℂ) + 2 * w)) - T w) + complexLaplace νN w :=
    fun w hw => complexLaplace_gaussianBudgetCarrier_eq hσ hη ha1 B hw
  have hLPd : DifferentiableOn ℂ (complexLaplace νP) {w : ℂ | a < w.re} :=
    (differentiableOn_complexLaplace hc₀).mono fun w hw => lt_of_le_of_lt hc₀0 hw
  -- the continuation of `ξ'/ξ(σ + 2w)`
  set K : ℂ → ℂ := fun w => gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
    (η * (B / (w - a) + complexLaplace νN w - complexLaplace νP w) + T w) * (Complex.Gamma w)⁻¹
    with hK
  have hKd : DifferentiableOn ℂ K {w : ℂ | a < w.re} := by
    intro w hw
    have hwa : a < w.re := hw
    have hw0 : 0 < w.re := lt_of_le_of_lt ha hwa
    have hw0' : w - a ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hre : 0 < ((σ : ℂ) + 2 * w).re := by simp; linarith
    have hA : DifferentiableAt ℂ (fun w : ℂ => gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w)) w :=
      (differentiableAt_gaussianArchimedeanCurrent hre).comp (f := fun w : ℂ => (σ : ℂ) + 2 * w) w
        (by fun_prop)
    have hopen : IsOpen {w : ℂ | a < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hPw : DifferentiableAt ℂ (complexLaplace νP) w := hLPd.differentiableAt (hopen.mem_nhds hw)
    have hNw : DifferentiableAt ℂ (complexLaplace νN) w := hLNd.differentiableAt (hopen.mem_nhds hw)
    refine DifferentiableAt.differentiableWithinAt ?_
    exact hA.sub (((differentiableAt_const _).mul ((((differentiableAt_const _).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w - (a : ℂ)) w) hw0').add hNw).sub hPw)).add (hTd w) |>.mul
        (Complex.differentiable_one_div_Gamma w))
  have hfar : ∀ w : ℂ, 3 < w.re → deriv xi ((σ : ℂ) + 2 * w) =
      xi ((σ : ℂ) + 2 * w) * K w := by
    intro w hw
    have hz1 : 1 < ((σ : ℂ) + 2 * w).re := by simp; linarith
    have hxi : xi ((σ : ℂ) + 2 * w) ≠ 0 := xi_ne_zero_of_one_lt_re hz1
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hKw : K w = logDeriv xi ((σ : ℂ) + 2 * w) := by
      simp only [hK]
      rw [hfarL w hw]
      have hcore : (η : ℂ) * (B / (w - a) + complexLaplace νN w - (B / (w - a) - η * (Complex.Gamma w *
          (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) - logDeriv xi ((σ : ℂ) + 2 * w)) - T w) +
            complexLaplace νN w)) + T w = Complex.Gamma w *
          (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) - logDeriv xi ((σ : ℂ) + 2 * w)) := by
        linear_combination (Complex.Gamma w * (gaussianArchimedeanCurrent ((σ : ℂ) + 2 * w) -
          logDeriv xi ((σ : ℂ) + 2 * w)) - T w) * hη2
      rw [hcore]
      field_simp
      ring
    rw [hKw, logDeriv_apply]
    field_simp
  exact xi_ne_zero_of_deriv_eq_mul_holomorphic (s := (σ : ℂ)) (a := a) (R := 3) hKd
    (by linarith) hfar (by simpa using hz)

/-- **One-sided Gaussian prime budget law.**  Let `σ > 0`.  If the Gaussian prime mass
`Σ Λ(n) n^{-σ} e^{-yn²}` never exceeds the continuum mass `∫₁^∞ u^{-σ} e^{-yu²} du` by more than a
constant on `0 < y ≤ 1`, then `ξ` has no zero with `Re z > σ`. -/
theorem xi_ne_zero_of_gaussianPrimeBudget {σ : ℝ} (hσ : 0 < σ) {B : ℝ}
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y ≤ B)
    {z : ℂ} (hz : σ < z.re) : xi z ≠ 0 := by
  refine xi_ne_zero_of_gaussianPrimeExcess hσ (Or.inl rfl) le_rfl zero_le_one B (fun τ _ => ?_)
    (by simpa using hz)
  refine (integrableOn_zero (μ := volume) (s := Ioi (0 : ℝ))).congr_fun (fun u hu => ?_)
    measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  have := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
  rw [gaussianBudgetProfile, zero_mul, Real.exp_zero, mul_one, one_mul,
    max_eq_right (by linarith), zero_mul]

/-- **Lower budget law.**  Let `σ > 0`.  If the Gaussian prime mass never falls below the continuum
mass by more than a constant on `0 < y ≤ 1`, then `ξ` has no zero with `Re z > σ`. -/
theorem xi_ne_zero_of_gaussianPrimeBudget_lower {σ : ℝ} (hσ : 0 < σ) {B : ℝ}
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 →
      -B ≤ gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y)
    {z : ℂ} (hz : σ < z.re) : xi z ≠ 0 := by
  refine xi_ne_zero_of_gaussianPrimeExcess hσ (Or.inr rfl) le_rfl zero_le_one B (fun τ _ => ?_)
    (by simpa using hz)
  refine (integrableOn_zero (μ := volume) (s := Ioi (0 : ℝ))).congr_fun (fun u hu => ?_)
    measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  have := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
  rw [gaussianBudgetProfile, zero_mul, Real.exp_zero, mul_one, max_eq_right (by linarith),
    zero_mul]

/-- Under a zero bound `Re ρ ≤ θ`, the gap is bounded on `(0, 1]` at every `σ ∈ (max θ 0, 2)`. -/
theorem exists_abs_gaussianWeightedGap_le_of_zero_bound {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) {σ : ℝ} (hσθ : θ < σ) (hσ0 : 0 < σ) (hσ2 : σ < 2) :
    ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      |gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y| ≤ B := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ0
  have hconv := tendsto_logDeriv_gaussianFormation_of_zeroFree hθ (s := (σ : ℂ)) hs
    (by simpa using hσθ) (by simpa using hσ2)
  set G : ℝ → ℂ := gaussianPrimeContinuumGap (σ : ℂ) with hGdef
  have hGlim : Tendsto G (𝓝[>] 0)
      (𝓝 (gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ))) := by
    have h1 := (tendsto_const_nhds (x := gaussianArchimedeanCurrent (σ : ℂ))).sub
      (hconv.comp tendsto_div_pi_nhdsGT_zero)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Function.comp]
    rw [logDeriv_gaussianFormation_eq_sub_gap (div_pos hy Real.pi_pos) hs,
      mul_div_cancel₀ _ Real.pi_ne_zero]
    ring
  set L : ℂ := gaussianArchimedeanCurrent (σ : ℂ) - logDeriv xi (σ : ℂ)
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), ‖G y‖ < ‖L‖ + 1 :=
    hGlim.norm.eventually (gt_mem_nhds (by linarith [norm_nonneg L]))
  obtain ⟨y₁, hy₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  set C₀ : ℝ := Real.exp 2 + Real.Gamma (1 / 2)
  refine ⟨max (‖L‖ + 1) (C₀ * y₁ ^ (-(2 : ℝ))), fun y hy hy1 => ?_⟩
  have habs : |gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y| = ‖G y‖ := by
    rw [hGdef, gaussianPrimeContinuumGap_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  by_cases hyy : y < y₁
  · exact (le_of_lt (hsub ⟨hy, hyy⟩)).trans (le_max_left _ _)
  · push Not at hyy
    refine le_trans ?_ (le_max_right _ _)
    refine (norm_gaussianPrimeContinuumGap_le (by simp; linarith) hy hy1).trans ?_
    have hC₀ : 0 ≤ C₀ := by
      have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num); positivity
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy₁ hyy (by norm_num)) hC₀

/-- **Abscissa law of the Gaussian prime budget.**  For `θ ≥ 0`, every zero of `ξ` has
`Re ρ ≤ θ` iff the upper budget `P_σ ≤ C_σ + B` holds on `(0, 1]` at every `σ ∈ (θ, 2)`. -/
theorem xi_zero_re_le_iff_gaussianPrimeBudget {θ : ℝ} (hθ0 : 0 ≤ θ) :
    (∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) ↔
      ∀ σ : ℝ, θ < σ → σ < 2 → ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
        gaussianWeightedPrimeMass σ y ≤ gaussianWeightedContinuumMass σ y + B := by
  constructor
  · intro hθ σ hσ hσ2
    obtain ⟨B, hB⟩ := exists_abs_gaussianWeightedGap_le_of_zero_bound hθ hσ (by linarith) hσ2
    refine ⟨B, fun y hy hy1 => ?_⟩
    have := (le_abs_self _).trans (hB y hy hy1)
    linarith
  · intro h ρ hρ
    by_contra hlt
    push Not at hlt
    have hρ1 : ρ.re < 1 := by
      by_contra h1; push Not at h1; exact xi_ne_zero_of_one_le_re h1 hρ
    obtain ⟨B, hB⟩ := h ((θ + ρ.re) / 2) (by linarith) (by linarith)
    exact xi_ne_zero_of_gaussianPrimeBudget (σ := (θ + ρ.re) / 2) (by linarith) (B := B)
      (fun y hy hy1 => by linarith [hB y hy hy1]) (by linarith) hρ

/-- **Growth budget law.**  Let `σ > 0`, `0 ≤ a ≤ 1`, `η = ±1`.  If
`η (P_σ − C_σ)(y) ≤ B y^{-a}` on `(0, 1]`, then `ξ` has no zero with `Re z > σ + 2a`. -/
theorem xi_ne_zero_of_gaussianPrimeGrowthBudget {σ : ℝ} (hσ : 0 < σ) {η : ℝ}
    (hη : η = 1 ∨ η = -1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) {B : ℝ}
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 →
      η * (gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y) ≤ B * y ^ (-a))
    {z : ℂ} (hz : σ + 2 * a < z.re) : xi z ≠ 0 := by
  refine xi_ne_zero_of_gaussianPrimeExcess hσ hη ha ha1 B (fun τ _ => ?_) hz
  refine (integrableOn_zero (μ := volume) (s := Ioi (0 : ℝ))).congr_fun (fun u hu => ?_)
    measurableSet_Ioi
  have hu0 : (0 : ℝ) < u := hu
  have h := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
  rw [← Real.exp_mul, show -u * -a = a * u by ring] at h
  rw [gaussianBudgetProfile, max_eq_right (by linarith), zero_mul]

theorem exists_xi_zero_re_eq_half : ∃ ρ : ℂ, xi ρ = 0 ∧ ρ.re = 1 / 2 := by
  obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
  have h1 : XiC (t : ℂ) = 0 := by rw [XiC_ofReal, ht, Complex.ofReal_zero]
  rw [XiC] at h1
  exact ⟨_, h1, by simp⟩

/-- **Unconditional quantitative Ω₊.**  For `0 < σ` and `0 ≤ a` with `σ + 2a < ½`, the gap
`P_σ − C_σ` exceeds `B y^{-a}` somewhere on `(0, 1]`, for every `B`. -/
theorem exists_gaussianWeightedGap_gt_rpow {σ : ℝ} (hσ : 0 < σ) {a : ℝ} (ha : 0 ≤ a)
    (haσ : σ + 2 * a < 1 / 2) (B : ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
      B * y ^ (-a) < gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y := by
  by_contra h
  push Not at h
  obtain ⟨ρ, hρ, hρre⟩ := exists_xi_zero_re_eq_half
  exact xi_ne_zero_of_gaussianPrimeGrowthBudget hσ (Or.inl rfl) ha (by linarith) (B := B)
    (fun y hy hy1 => by rw [one_mul]; exact h y hy hy1) (by linarith) hρ

/-- **Unconditional quantitative Ω₋.**  For `0 < σ` and `0 ≤ a` with `σ + 2a < ½`, the gap
`P_σ − C_σ` falls below `−B y^{-a}` somewhere on `(0, 1]`, for every `B`. -/
theorem exists_gaussianWeightedGap_lt_neg_rpow {σ : ℝ} (hσ : 0 < σ) {a : ℝ} (ha : 0 ≤ a)
    (haσ : σ + 2 * a < 1 / 2) (B : ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
      gaussianWeightedPrimeMass σ y - gaussianWeightedContinuumMass σ y < -(B * y ^ (-a)) := by
  by_contra h
  push Not at h
  obtain ⟨ρ, hρ, hρre⟩ := exists_xi_zero_re_eq_half
  refine xi_ne_zero_of_gaussianPrimeGrowthBudget (η := -1) hσ (Or.inr rfl) ha (by linarith)
    (B := B) (fun y hy hy1 => ?_) (by linarith) hρ
  have := h y hy hy1
  linarith

/-- **Unconditional Ω₊ below the critical line.**  For `0 < σ < ½` the Gaussian prime mass exceeds
its continuum by arbitrarily large amounts on `(0, 1]`. -/
theorem exists_gaussianWeightedPrimeMass_gt {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 1 / 2) (B : ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
      gaussianWeightedContinuumMass σ y + B < gaussianWeightedPrimeMass σ y := by
  obtain ⟨y, hy, hy1, h⟩ := exists_gaussianWeightedGap_gt_rpow hσ le_rfl (by linarith) B
  refine ⟨y, hy, hy1, ?_⟩
  rw [neg_zero, Real.rpow_zero, mul_one] at h
  linarith

/-- **Unconditional Ω₋ below the critical line.**  For `0 < σ < ½` the Gaussian prime mass falls
below its continuum by arbitrarily large amounts on `(0, 1]`. -/
theorem exists_gaussianWeightedPrimeMass_lt {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ < 1 / 2) (B : ℝ) :
    ∃ y : ℝ, 0 < y ∧ y ≤ 1 ∧
      gaussianWeightedPrimeMass σ y < gaussianWeightedContinuumMass σ y - B := by
  obtain ⟨y, hy, hy1, h⟩ := exists_gaussianWeightedGap_lt_neg_rpow hσ le_rfl (by linarith) B
  refine ⟨y, hy, hy1, ?_⟩
  rw [neg_zero, Real.rpow_zero, mul_one] at h
  linarith

/-- **RH as a one-sided Gaussian prime budget.**  RH holds iff for every `σ ∈ (½, 1)` there is a
constant `B` with `Σ Λ(n) n^{-σ} e^{-yn²} ≤ ∫₁^∞ u^{-σ} e^{-yu²} du + B` for all `0 < y ≤ 1`. -/
theorem riemannHypothesis_iff_gaussianPrimeBudget :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      gaussianWeightedPrimeMass σ y ≤ gaussianWeightedContinuumMass σ y + B := by
  rw [rh_iff_xi_ne_zero_right]
  constructor
  · intro h σ hσ hσ1
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := by
      intro ρ hρ
      by_contra hlt
      push Not at hlt
      exact h ρ (mem_rightHalf.mpr hlt) hρ
    exact (xi_zero_re_le_iff_gaussianPrimeBudget (by norm_num)).1 hθ σ hσ (by linarith)
  · intro h s hs hzero
    rw [mem_rightHalf] at hs
    set σ₀ : ℝ := (1 / 2 + min s.re 1) / 2 with hσ₀
    have hm : 1 / 2 < min s.re 1 := lt_min hs (by norm_num)
    have hm1 : min s.re 1 ≤ 1 := min_le_right _ _
    have hms : min s.re 1 ≤ s.re := min_le_left _ _
    obtain ⟨B, hB⟩ := h σ₀ (by linarith) (by linarith)
    exact xi_ne_zero_of_gaussianPrimeBudget (σ := σ₀) (by linarith) (B := B)
      (fun y hy hy1 => by linarith [hB y hy hy1]) (by linarith) hzero

/-- **RH as an integrated one-sided excess law.**  RH holds iff for every `σ ∈ (½, 1)` there is `B`
such that the excess of the Gaussian prime mass over `continuum + B` has finite weighted integral
`∫₀¹ (P_σ − C_σ − B)⁺(y) y^{τ−1} dy` for every `τ > 0` (in the variable `y = e^{-u}`). -/
theorem riemannHypothesis_iff_gaussianPrimeExcess :
    RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → ∃ B : ℝ, ∀ τ : ℝ, 0 < τ →
      IntegrableOn (fun u : ℝ => max (-gaussianBudgetProfile 1 σ 0 B u) 0 * Real.exp (-τ * u))
        (Ioi 0) := by
  constructor
  · intro hRH σ hσ hσ1
    obtain ⟨B, hB⟩ := riemannHypothesis_iff_gaussianPrimeBudget.1 hRH σ hσ hσ1
    refine ⟨B, fun τ _ => (integrableOn_zero (μ := volume) (s := Ioi (0 : ℝ))).congr_fun
      (fun u hu => ?_) measurableSet_Ioi⟩
    have hu0 : (0 : ℝ) < u := hu
    have := hB (Real.exp (-u)) (Real.exp_pos _) (Real.exp_le_one_iff.2 (by linarith))
    rw [gaussianBudgetProfile, zero_mul, Real.exp_zero, mul_one, one_mul,
      max_eq_right (by linarith), zero_mul]
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    rw [mem_rightHalf] at hs
    set σ₀ : ℝ := (1 / 2 + min s.re 1) / 2 with hσ₀
    have hm : 1 / 2 < min s.re 1 := lt_min hs (by norm_num)
    have hm1 : min s.re 1 ≤ 1 := min_le_right _ _
    have hms : min s.re 1 ≤ s.re := min_le_left _ _
    obtain ⟨B, hB⟩ := h σ₀ (by linarith) (by linarith)
    exact xi_ne_zero_of_gaussianPrimeExcess (σ := σ₀) (by linarith) (Or.inl rfl) le_rfl
      zero_le_one B (fun τ hτ => hB τ hτ) (by simp; linarith) hzero

end

end RHTower
