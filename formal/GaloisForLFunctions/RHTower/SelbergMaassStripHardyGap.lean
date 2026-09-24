import GaloisForLFunctions.RHTower.SelbergMaassStripGap

/-!
# Vertical Hardy energy in the Selberg strip argument

`SelbergMaassStripGap` bounds the strip energy using only the horizontal Fourier gap
`κ = 2π/(N+1)`, giving `α² ≤ 2λ` with `α = κ·√3/2`. This module keeps the vertical
energy too. For `h(y) = α/y - κ` (zero at the strip floor), the square
`‖∂_y g - h g‖² ≥ 0` combined with the horizontal gap gives, after summing over the deck,

  `G ≥ (h S)' + (α(1-α)/y² + 2ακ/y) S`,

where `S` is the unit-strip trace mass and `G` the unit-strip gradient. Integrating from
the floor to `R`, using cusp decay of the trace and letting `R → ∞`, proves
`α(1+α)·M_strip ≤ E_strip`. The corpus strip/cell comparison then gives `α(1+α) ≤ 2λ`.
The bound is of order `1/(N+1)`, not `1/(N+1)²`, and it rules out exceptional eigenvalues
at every principal level one through fourteen. It does not prove the uniform Selberg
conjecture.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap
open SelbergMaassCongruenceTrace SelbergMaassTraceEnergy SelbergMaassFullGradient
  SelbergMaassTraceMass SelbergMaassFullCurvatureBudget SelbergMaassCellCurvature
  SelbergMaassMean SelbergModularDomainSlices SelbergMaassCurvatureTransport
  SelbergModularStripComparison SelbergMaassStripSlice SelbergMaassStripGap
  SelbergMaassFlux SelbergMaassParseval SelbergMaassFourier
noncomputable section

section component

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Period-normalized horizontal derivative energy of one actual Maass slice. -/
def horizontalEnergy (y : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) (directional 1 (f.1.1 ∘ ofComplex))
    (directional 1 (f.1.1 ∘ ofComplex)) y

/-- Period-normalized vertical derivative energy of one actual Maass slice. -/
def verticalEnergy (y : ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * pairing (N + 1 : ℕ) (directional Complex.I (f.1.1 ∘ ofComplex))
    (directional Complex.I (f.1.1 ∘ ofComplex)) y

theorem gradientEnergy_eq_add (y : ℝ) :
    gradientEnergy N f y = horizontalEnergy N f y + verticalEnergy N f y := by
  unfold gradientEnergy horizontalEnergy verticalEnergy
  ring

private theorem normSq_sub_smul (a b : ℂ) (c : ℝ) :
    Complex.normSq (a - (c : ℂ) * b) =
      (a * (starRingEnd ℂ) a).re - 2 * c * (a * (starRingEnd ℂ) b).re +
        c ^ 2 * (b * (starRingEnd ℂ) b).re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Ground-state square: for every real shift the shifted vertical energy is nonnegative. -/
theorem vertical_ground_state (c : ℝ) {y : ℝ} (hy : 0 < y) :
    0 ≤ verticalEnergy N f y - 2 * c * flux N f y + c ^ 2 * mass N f y := by
  let F := f.1.1 ∘ ofComplex
  have hf : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im} := f.2.2.1.1
  have hA := (directional_contDiffOn hf (m := 1) le_rfl Complex.I).continuousOn
  have hB := hf.continuousOn
  set A := directional Complex.I F
  have hAc := slice_continuous hA hy
  have hBc := slice_continuous hB hy
  have hAA := pairing_eq_integral (N + 1 : ℕ) hA hA hy
  have hAB := pairing_eq_integral (N + 1 : ℕ) hA hB hy
  have hBB := pairing_eq_integral (N + 1 : ℕ) hB hB hy
  have iAA : IntegrableOn (fun x => (A (point x y) * (starRingEnd ℂ) (A (point x y))).re)
      (Ioc 0 ((N + 1 : ℕ) : ℝ)) :=
    (Complex.continuous_re.comp (hAc.mul (Complex.continuous_conj.comp hAc))).integrableOn_Ioc
  have iAB : IntegrableOn (fun x => (A (point x y) * (starRingEnd ℂ) (F (point x y))).re)
      (Ioc 0 ((N + 1 : ℕ) : ℝ)) :=
    (Complex.continuous_re.comp (hAc.mul (Complex.continuous_conj.comp hBc))).integrableOn_Ioc
  have iBB : IntegrableOn (fun x => (F (point x y) * (starRingEnd ℂ) (F (point x y))).re)
      (Ioc 0 ((N + 1 : ℕ) : ℝ)) :=
    (Complex.continuous_re.comp (hBc.mul (Complex.continuous_conj.comp hBc))).integrableOn_Ioc
  have hexp : pairing (N + 1 : ℕ) A A y - 2 * c * pairing (N + 1 : ℕ) A F y +
      c ^ 2 * pairing (N + 1 : ℕ) F F y =
      ∫ x in Ioc 0 ((N + 1 : ℕ) : ℝ), Complex.normSq (A (point x y) - (c : ℂ) * F (point x y)) := by
    have hs := integral_add (iAA.sub (iAB.const_mul (2 * c))) (iBB.const_mul (c ^ 2))
    simp only [Pi.sub_apply] at hs
    rw [hAA, hAB, hBB, ← integral_const_mul, ← integral_const_mul, ← integral_sub iAA
      (iAB.const_mul _), ← hs]
    apply integral_congr_ae
    filter_upwards with x
    rw [normSq_sub_smul]
  have hnn : 0 ≤ ∫ x in Ioc 0 ((N + 1 : ℕ) : ℝ),
      Complex.normSq (A (point x y) - (c : ℂ) * F (point x y)) :=
    setIntegral_nonneg measurableSet_Ioc (fun x _ => Complex.normSq_nonneg _)
  have hw : 0 ≤ ((N + 1 : ℕ) : ℝ)⁻¹ := by positivity
  have key : verticalEnergy N f y - 2 * c * flux N f y + c ^ 2 * mass N f y =
      ((N + 1 : ℕ) : ℝ)⁻¹ * (pairing (N + 1 : ℕ) A A y - 2 * c * pairing (N + 1 : ℕ) A F y +
        c ^ 2 * pairing (N + 1 : ℕ) F F y) := by
    unfold verticalEnergy flux mass
    ring
  rw [key, hexp]
  exact mul_nonneg hw hnn

end component

section horizontal

/-- Zero constant term and the integer frequency gap bound the horizontal energy alone. -/
theorem horizontalEnergy_ge_first_frequency (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {y : ℝ} (hy : 0 < y) :
    (2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ) * mass N f y ≤ horizontalEnergy N f y := by
  have hz : maassCoefficient N f 0 y = 0 := by
    rw [maassCoefficient_zero]
    have hp : 0 < (point 0 y).im := by simpa [point] using hy
    have h := SelbergEulerDecay.maassMean_subquarter_zero N lam f ⟨point 0 y, hp⟩
    have hm : maassMean N f y = 0 := by simpa [UpperHalfPlane.im, point] using h
    rw [hm, mul_zero]
  have hH : horizontalEnergy N f y = ((N + 1 : ℕ) : ℝ)⁻¹ * ∫ x in (0 : ℝ)..(N + 1 : ℕ),
      Complex.normSq (directional 1 (f.1.1 ∘ ofComplex) (point x y)) := by
    have hf : ContDiffOn ℝ 2 (f.1.1 ∘ ofComplex) {z : ℂ | 0 < z.im} := f.2.2.1.1
    have hd := (directional_contDiffOn hf (m := 1) le_rfl (1 : ℂ)).continuousOn
    rw [horizontalEnergy, pairing_self _ hd hy,
      intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (N + 1 : ℕ))]
  rw [hH]
  apply hasSum_le (f := fun n : ℤ => (2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ) *
      Complex.normSq (maassCoefficient N f n y)) ?_
    ((mass_hasSum N f hy).mul_left ((2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ)))
    (maass_horizontal_hasSum N f hy)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [hz, Complex.normSq_zero, mul_zero, le_refl]
  · have hn2 : (1 : ℤ) ≤ n ^ (2 : ℕ) := Int.add_one_le_iff.mpr (sq_pos_of_ne_zero hn)
    have hnR : (1 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by exact_mod_cast hn2
    have he : signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) =
        (2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ) := by
      unfold signedFrequency
      ring
    rw [he]
    have hle := mul_le_mul_of_nonneg_left hnR (sq_nonneg (2 * Real.pi / (N + 1 : ℕ)))
    have hle' := mul_le_mul_of_nonneg_right hle (Complex.normSq_nonneg (maassCoefficient N f n y))
    nlinarith

end horizontal

section deck

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Unit-strip trace mass at one height. -/
def sliceMass (y : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y))

/-- Unit-strip trace gradient at one height. -/
def sliceGradient (y : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, gradientDensity N f (point x y)

theorem sliceMass_nonneg (y : ℝ) : 0 ≤ sliceMass N f y :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => density_nonneg N f _)

/-- Deck-summed ground-state inequality: horizontal gap plus shifted vertical square. -/
theorem slice_ground_state (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    (c : ℝ) {y : ℝ} (hy : 0 < y) :
    ((2 * Real.pi / (N + 1 : ℕ)) ^ (2 : ℕ) - c ^ 2) * sliceMass N f y +
        c * (2 * ∑ q : Deck N, flux N (quotientForm N f q) y) ≤ sliceGradient N f y := by
  rw [sliceMass, density_integral_eq_sum_mass N f hy, sliceGradient,
    gradient_integral_eq_sum N f hy]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q _
  have h1 := horizontalEnergy_ge_first_frequency N lam (quotientForm N f q) hy
  have h2 := vertical_ground_state N (quotientForm N f q) c hy
  rw [gradientEnergy_eq_add]
  nlinarith

/-- The strip gradient slice in rectangle coordinates is the unit-strip gradient. -/
theorem gslice_eq {y : ℝ} (hy : 0 < y) :
    (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y)) = sliceGradient N f y := by
  simp only [planarGradient]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hG := (gradient_slice_periodic N f hy).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hG
  simpa [sliceGradient] using hG

/-- The strip mass slice in rectangle coordinates is the unit-strip mass over height squared. -/
theorem mslice_eq {y : ℝ} (hy : 0 < y) :
    (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)) =
      sliceMass N f y / y ^ (2 : ℕ) := by
  simp only [massDensity]
  rw [integral_div, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hD := (density_slice_periodic N f hy).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at hD
  rw [sliceMass, hD]

end deck

/-- Cusp decay of the actual trace sends the unit-strip mass to zero. -/
theorem sliceMass_tendsto (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Tendsto (sliceMass N f) atTop (𝓝 0) := by
  have hd : Tendsto (density N f) atImInfty (𝓝 0) := density_decay N f
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmem := hd (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hmem
  refine ⟨max A 1, fun R hR => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos ((le_max_right A 1).trans hR)
  have hpt : ∀ x : ℝ, density N f (ofComplex (point x R)) ≤ ε / 2 := by
    intro x
    have hp : 0 < (point x R).im := by simpa [point] using hR0
    have hz := hA (ofComplex (point x R)) (by
      rw [ofComplex_apply_of_im_pos hp]
      change A ≤ (point x R).im
      simpa [point] using (le_max_left A 1).trans hR)
    have hz' : dist (density N f (ofComplex (point x R))) 0 < ε / 2 := hz
    rw [Real.dist_eq, sub_zero] at hz'
    exact (le_abs_self _).trans hz'.le
  have hup : sliceMass N f R ≤ ε / 2 := by
    have h := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
      ((density_slice_continuous N f hR0).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume) (c := ε / 2)) (fun x _ => hpt x)
    simpa [sliceMass] using h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (sliceMass_nonneg N f R)]
  linarith

/-- The Hardy exponent `α = κ Y₀` attached to the strip floor. -/
def hardyExponent (N : ℕ) : ℝ := 2 * Real.pi / (N + 1 : ℕ) * arcFloor

theorem hardyExponent_nonneg (N : ℕ) : 0 ≤ hardyExponent N :=
  mul_nonneg (by positivity) arcFloor_pos.le

/-- Finite-height Hardy balance on the strip, with the cusp boundary term retained. -/
theorem finite_hardy_balance (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {R : ℝ} (hR : arcFloor ≤ R) :
    hardyExponent N * (1 + hardyExponent N) *
        (∫ y in arcFloor..R, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)) ≤
      (∫ y in Ioi arcFloor, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y)) +
        2 * Real.pi / (N + 1 : ℕ) * sliceMass N f R := by
  set κ : ℝ := 2 * Real.pi / (N + 1 : ℕ) with hκdef
  set α : ℝ := hardyExponent N with hαdef
  set Y : ℝ := arcFloor with hYdef
  have hY : 0 < Y := arcFloor_pos
  have hκ : 0 ≤ κ := by positivity
  have hα : 0 ≤ α := hardyExponent_nonneg N
  have hαY : α = κ * Y := rfl
  set g : ℝ → ℝ := fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y)
  set m : ℝ → ℝ := fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)
  have hg : IntegrableOn g (Ici Y) :=
    rectangle_slices_integrable (rectangle_gradient_integrable N lam f)
  have hm : IntegrableOn m (Ici Y) :=
    rectangle_slices_integrable (rectangle_mass_integrable N lam f)
  have hg0 : ∀ y, 0 ≤ g y := fun y =>
    setIntegral_nonneg measurableSet_Icc (fun x _ => gradientDensity_nonneg N f _)
  have hm0 : ∀ y, 0 ≤ m y := fun y =>
    setIntegral_nonneg measurableSet_Icc (fun x _ => massDensity_nonneg N f _)
  let Q : ℝ → ℝ := fun y => α * (1 - α) + 2 * α * κ * y
  let h : ℝ → ℝ := fun y => α / y - κ
  let G : ℝ → ℝ := fun y => h y * sliceMass N f y
  let G' : ℝ → ℝ := fun y => α * -(y ^ 2)⁻¹ * sliceMass N f y +
    h y * (2 * ∑ q : Deck N, flux N (quotientForm N f q) y)
  let φ : ℝ → ℝ := fun y => g y - Q y * m y
  have hGd : ∀ y, 0 < y → HasDerivAt G (G' y) y := by
    intro y hy
    have hh : HasDerivAt h (α * -(y ^ 2)⁻¹) y := by
      have := ((hasDerivAt_inv hy.ne').const_mul α).sub_const κ
      simpa [h, div_eq_mul_inv] using this
    exact hh.mul (density_slice_mass_hasDerivAt N f hy)
  have hIcc : Icc Y R ⊆ Ici Y := Icc_subset_Ici_self
  have hφi : IntegrableOn φ (Icc Y R) := by
    have hQm : IntegrableOn (fun y => Q y * m y) (Icc Y R) :=
      (hm.mono_set hIcc).continuousOn_mul (by fun_prop) isCompact_Icc
    exact (hg.mono_set hIcc).sub hQm
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (g := G) (g' := G')
    (φ := φ) hR
    (fun y hy => (hGd y (hY.trans_le hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => (hGd y (hY.trans hy.1)).hasDerivWithinAt) hφi
    (by
      intro y hy
      have hy0 : 0 < y := hY.trans hy.1
      have hs := slice_ground_state N lam f (h y) hy0
      have hgy : g y = sliceGradient N f y := gslice_eq N f hy0
      have hmy : m y = sliceMass N f y / y ^ (2 : ℕ) := mslice_eq N f hy0
      have hid : Q y * m y = (κ ^ 2 - h y ^ 2 + α / y ^ 2) * sliceMass N f y := by
        rw [hmy]
        simp only [Q, h]
        field_simp
        ring
      simp only [φ, G']
      rw [hid, hgy]
      have hr : α * -(y ^ 2)⁻¹ * sliceMass N f y = -(α / y ^ 2 * sliceMass N f y) := by
        ring
      rw [hr]
      nlinarith [hs])
  have hGY : G Y = 0 := by
    simp only [G, h, hαY]
    field_simp
    ring
  have hGR : -(κ * sliceMass N f R) ≤ G R := by
    have hR0 : 0 < R := hY.trans_le hR
    have hS := sliceMass_nonneg N f R
    have : 0 ≤ α / R * sliceMass N f R := mul_nonneg (div_nonneg hα hR0.le) hS
    simp only [G, h]
    nlinarith
  have hgi : IntervalIntegrable g volume Y R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr (hg.mono_set hIcc)
  have hQmi : IntervalIntegrable (fun y => Q y * m y) volume Y R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr
      ((hm.mono_set hIcc).continuousOn_mul (by fun_prop) isCompact_Icc)
  have hmi : IntervalIntegrable m volume Y R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).mpr (hm.mono_set hIcc)
  have hsplit : (∫ y in Y..R, φ y) = (∫ y in Y..R, g y) - ∫ y in Y..R, Q y * m y :=
    intervalIntegral.integral_sub hgi hQmi
  have hlow : α * (1 + α) * (∫ y in Y..R, m y) ≤ ∫ y in Y..R, Q y * m y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR (hmi.const_mul _) hQmi
    intro y hy
    have hQ : α * (1 + α) ≤ Q y := by
      simp only [Q]
      have : α * κ * Y ≤ α * κ * y := mul_le_mul_of_nonneg_left hy.1 (mul_nonneg hα hκ)
      nlinarith
    exact mul_le_mul_of_nonneg_right hQ (hm0 y)
  have hgle : (∫ y in Y..R, g y) ≤ ∫ y in Ioi Y, g y := by
    rw [intervalIntegral.integral_of_le hR]
    exact setIntegral_mono_set (hg.mono_set Ioi_subset_Ici_self)
      (Eventually.of_forall hg0) (Ioc_subset_Ioi_self.eventuallyLE)
  rw [hsplit, hGY, sub_zero] at hmain
  linarith

/-- Vertical Hardy energy improves the strip energy constant from `α²` to `α(1+α)`. -/
theorem rectangle_energy_lower_hardy (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    hardyExponent N * (1 + hardyExponent N) * (∫ p in rectangle, massDensity N f p) ≤
      ∫ p in rectangle, planarGradient N f p := by
  rw [rectangle_integral (rectangle_mass_integrable N lam f),
    rectangle_integral (rectangle_gradient_integrable N lam f),
    integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi]
  have hm : IntegrableOn (fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y))
      (Ioi arcFloor) :=
    (rectangle_slices_integrable (rectangle_mass_integrable N lam f)).mono_set Ioi_subset_Ici_self
  have hlim : Tendsto (fun R => hardyExponent N * (1 + hardyExponent N) *
      (∫ y in arcFloor..R, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)) -
        2 * Real.pi / (N + 1 : ℕ) * sliceMass N f R) atTop
      (𝓝 (hardyExponent N * (1 + hardyExponent N) *
        (∫ y in Ioi arcFloor, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y)) -
          2 * Real.pi / (N + 1 : ℕ) * 0)) :=
    ((intervalIntegral_tendsto_integral_Ioi arcFloor hm tendsto_id).const_mul _).sub
      ((sliceMass_tendsto N f).const_mul _)
  rw [mul_zero, sub_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop arcFloor] with R hR
  have := finite_hardy_balance N lam f hR
  linarith

/-- Unconditional Hardy strip bound: `α(1+α) ≤ 2λ` with `α = π√3/(N+1)`. -/
theorem hardy_eigenvalue_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) :
    hardyExponent N * (1 + hardyExponent N) ≤ 2 * (lam : ℝ) := by
  have hupper := integral_strip_le_twice (cell_gradient_integrable N lam f)
    (hyperbolicGradient_nonneg N f) (hyperbolicGradient_invariant N f S)
  rw [strip_gradient_identity, cell_gradient_identity] at hupper
  have hmass := setIntegral_mono_set
    (integrable_strip (cell_mass_integrable N lam f) (density_invariant N f S))
    (Eventually.of_forall (density_nonneg N f)) (Eventually.of_forall fd_subset_strip)
  change (∫ z : ℍ in fd, density N f z) ≤ ∫ z in strip, density N f z at hmass
  rw [cell_mass_identity, strip_mass_identity] at hmass
  have hc : 0 ≤ hardyExponent N * (1 + hardyExponent N) :=
    mul_nonneg (hardyExponent_nonneg N) (by linarith [hardyExponent_nonneg N])
  have hlow := (mul_le_mul_of_nonneg_left hmass hc).trans (rectangle_energy_lower_hardy N lam f)
  apply le_of_mul_le_mul_right (a := ∫ p in fullDomain, massDensity N f p) ?_
    (full_mass_pos N lam f)
  simpa only [mul_assoc] using hlow.trans hupper

/-- The exceptional-source type is empty at every principal level one through fourteen. -/
theorem level_le_fourteen_no_exceptional (n : Fin 14) (l : Ioo (0 : ℝ) (1 / 4)) :
    IsEmpty (MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (n.val + 1))) (l : ℝ)) := by
  constructor
  intro g
  have hb := hardy_eigenvalue_bound n.val l g
  have hn : ((n.val + 1 : ℕ) : ℝ) ≤ 14 := by exact_mod_cast (show n.val + 1 ≤ 14 from n.isLt)
  have hn0 : (0 : ℝ) < ((n.val + 1 : ℕ) : ℝ) := by positivity
  have hpi := Real.pi_gt_three
  have hκ : (3 / 7 : ℝ) ≤ 2 * Real.pi / (n.val + 1 : ℕ) := by
    rw [le_div_iff₀ hn0]
    nlinarith
  have hsq : hardyExponent n.val ^ (2 : ℕ) = (2 * Real.pi / (n.val + 1 : ℕ)) ^ (2 : ℕ) * (3 / 4) := by
    rw [hardyExponent, mul_pow, arcFloor_sq]
  have hα0 := hardyExponent_nonneg n.val
  have hα2 : (27 / 196 : ℝ) ≤ hardyExponent n.val ^ (2 : ℕ) := by
    rw [hsq]
    have := mul_le_mul hκ hκ (by norm_num) (by linarith)
    nlinarith
  have hα : (37 / 100 : ℝ) ≤ hardyExponent n.val := by
    by_contra hlt
    have hlt' := lt_of_not_ge hlt
    nlinarith
  have hl := l.2.2
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap
