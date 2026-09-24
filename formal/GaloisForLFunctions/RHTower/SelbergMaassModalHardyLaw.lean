import GaloisForLFunctions.RHTower.SelbergMaassStripHardyGap

/-!
# Modal Hardy law for exceptional congruence Maass forms

`SelbergMaassStripHardyGap` uses one ground-state weight for every Fourier mode. Here each mode
`n` of each deck component gets its own weight `h_n(y) = t_n/y - |k_n|`, with `k_n = 2πn/(N+1)`
and `t_n = |k_n|·√3/2`. The one-dimensional identity `|c' - h c|² ≥ 0` on `[√3/2, R]`, cusp decay
of the modal coefficient and `R → ∞` give per mode `t_n(1+t_n)·M_{q,n} ≤ E_{q,n}`. Summing
over modes and deck with Tonelli, and using the corpus strip/cell comparison, gives the
**modal Hardy law** `Σ t_n(1+t_n)·M_{q,n} ≤ 2λ·Σ M_{q,n}`.

For `λ < 1/4` this forces **low-mode dominance**: `Σ (t_n(1+t_n) - 1/2)·M_{q,n} < 0`, so the
strip mass of an exceptional form must be concentrated in modes with `|n| ≲ 0.0673·(N+1)`.
This is an unconditional necessary condition, not an exclusion. Selberg's conjecture for
`Γ(N+1)` is reduced to showing that no Maass cusp form concentrates its strip mass there.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
namespace GaloisForLFunctions.RHTower.SelbergMaassModalHardyLaw
open SelbergMaassCongruenceTrace SelbergMaassFlux SelbergMaassFourier SelbergMaassStripHardyGap
  SelbergModularDomainSlices SelbergMaassStripGap SelbergMaassTraceMass SelbergMaassFullGradient
  SelbergMaassStripSlice SelbergMaassMean SelbergMaassTraceEnergy
noncomputable section

/-- One-dimensional ground-state Hardy inequality on `[Y, R]` for a frequency `κ`.
The weight `h(y) = κY/y - κ` vanishes at the floor; the cusp end keeps `κ‖c R‖²`. -/
theorem hardy_interval {c c' : ℝ → ℂ} {κ Y R : ℝ} (hY : 0 < Y) (hκ : 0 ≤ κ) (hR : Y ≤ R)
    (hc : ∀ y, 0 < y → HasDerivAt c (c' y) y) (hc' : ContinuousOn c' (Ioi 0)) :
    κ * Y * (1 + κ * Y) * (∫ y in Y..R, ‖c y‖ ^ 2 / y ^ 2) ≤
      (∫ y in Y..R, (κ ^ 2 * ‖c y‖ ^ 2 + ‖c' y‖ ^ 2)) + κ * ‖c R‖ ^ 2 := by
  set α := κ * Y with hαdef
  have hα : 0 ≤ α := mul_nonneg hκ hY.le
  let h : ℝ → ℝ := fun y => α / y - κ
  let Q : ℝ → ℝ := fun y => α * (1 - α) + 2 * α * κ * y
  let G : ℝ → ℝ := fun y => h y * ‖c y‖ ^ 2
  let G' : ℝ → ℝ := fun y => α * -(y ^ 2)⁻¹ * ‖c y‖ ^ 2 + h y * (2 * inner ℝ (c y) (c' y))
  let φ : ℝ → ℝ := fun y => (κ ^ 2 * ‖c y‖ ^ 2 + ‖c' y‖ ^ 2) - Q y * (‖c y‖ ^ 2 / y ^ 2)
  have hsub : Icc Y R ⊆ Ioi 0 := fun y hy => hY.trans_le hy.1
  have hcc : ContinuousOn c (Icc Y R) := fun y hy =>
    (hc y (hsub hy)).continuousAt.continuousWithinAt
  have hc'c : ContinuousOn c' (Icc Y R) := hc'.mono hsub
  have hinv : ContinuousOn (fun y : ℝ => (y ^ 2)⁻¹) (Icc Y R) :=
    (continuousOn_pow 2).inv₀ (fun y hy => pow_ne_zero 2 (hsub hy).ne')
  have hGd : ∀ y, 0 < y → HasDerivAt G (G' y) y := by
    intro y hy
    have hh : HasDerivAt h (α * -(y ^ 2)⁻¹) y := by
      have := ((hasDerivAt_inv hy.ne').const_mul α).sub_const κ
      simpa [h, div_eq_mul_inv] using this
    exact hh.mul (hc y hy).norm_sq
  have hφc : ContinuousOn φ (Icc Y R) := by
    have h1 : ContinuousOn (fun y => ‖c y‖ ^ 2) (Icc Y R) := (continuous_norm.comp_continuousOn hcc).pow 2
    have h2 : ContinuousOn (fun y => ‖c' y‖ ^ 2) (Icc Y R) := (continuous_norm.comp_continuousOn hc'c).pow 2
    have h3 : ContinuousOn (fun y => ‖c y‖ ^ 2 / y ^ 2) (Icc Y R) :=
      h1.div (continuousOn_pow 2) (fun y hy => pow_ne_zero 2 (hsub hy).ne')
    exact ((continuousOn_const.mul h1).add h2).sub ((by fun_prop : Continuous Q).continuousOn.mul h3)
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (g := G) (g' := G')
    (φ := φ) hR
    (fun y hy => (hGd y (hsub hy)).continuousAt.continuousWithinAt)
    (fun y hy => (hGd y (hY.trans hy.1)).hasDerivWithinAt) (hφc.integrableOn_Icc)
    (by
      intro y hy
      have hy0 : 0 < y := hY.trans hy.1
      have hsq := norm_sub_sq_real (c' y) (h y • c y)
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsq
      have hnn : 0 ≤ ‖c' y - h y • c y‖ ^ 2 := sq_nonneg _
      have hcomm : inner ℝ (c' y) (c y) = inner ℝ (c y) (c' y) := real_inner_comm _ _
      have hid : Q y * (‖c y‖ ^ 2 / y ^ 2) =
          (κ ^ 2 - h y ^ 2 + α / y ^ 2) * ‖c y‖ ^ 2 := by
        simp only [Q, h]
        field_simp
        ring
      have hr : α * -(y ^ 2)⁻¹ * ‖c y‖ ^ 2 = -(α / y ^ 2 * ‖c y‖ ^ 2) := by ring
      simp only [φ, G']
      rw [hid, hr]
      rw [hcomm] at hsq
      rw [hsq] at hnn
      have e : (κ ^ 2 - h y ^ 2 + α / y ^ 2) * ‖c y‖ ^ 2 =
          κ ^ 2 * ‖c y‖ ^ 2 - h y ^ 2 * ‖c y‖ ^ 2 + α / y ^ 2 * ‖c y‖ ^ 2 := by ring
      rw [e]
      linarith)
  have hGY : G Y = 0 := by
    simp only [G, h, hαdef]
    field_simp
    ring
  have hGR : -(κ * ‖c R‖ ^ 2) ≤ G R := by
    have hR0 : 0 < R := hY.trans_le hR
    have : 0 ≤ α / R * ‖c R‖ ^ 2 := mul_nonneg (div_nonneg hα hR0.le) (sq_nonneg _)
    simp only [G, h]
    nlinarith
  have hE : IntervalIntegrable (fun y => κ ^ 2 * ‖c y‖ ^ 2 + ‖c' y‖ ^ 2) volume Y R :=
    (ContinuousOn.intervalIntegrable_of_Icc hR
      ((continuousOn_const.mul ((continuous_norm.comp_continuousOn hcc).pow 2)).add
        ((continuous_norm.comp_continuousOn hc'c).pow 2)))
  have hM : ContinuousOn (fun y => ‖c y‖ ^ 2 / y ^ 2) (Icc Y R) :=
    ((continuous_norm.comp_continuousOn hcc).pow 2).div (continuousOn_pow 2)
      (fun y hy => pow_ne_zero 2 (hsub hy).ne')
  have hQM : IntervalIntegrable (fun y => Q y * (‖c y‖ ^ 2 / y ^ 2)) volume Y R :=
    ContinuousOn.intervalIntegrable_of_Icc hR ((by fun_prop : Continuous Q).continuousOn.mul hM)
  have hMi : IntervalIntegrable (fun y => ‖c y‖ ^ 2 / y ^ 2) volume Y R :=
    ContinuousOn.intervalIntegrable_of_Icc hR hM
  have hsplit : (∫ y in Y..R, φ y) = (∫ y in Y..R, (κ ^ 2 * ‖c y‖ ^ 2 + ‖c' y‖ ^ 2)) -
      ∫ y in Y..R, Q y * (‖c y‖ ^ 2 / y ^ 2) := intervalIntegral.integral_sub hE hQM
  have hlow : α * (1 + α) * (∫ y in Y..R, ‖c y‖ ^ 2 / y ^ 2) ≤
      ∫ y in Y..R, Q y * (‖c y‖ ^ 2 / y ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hR (hMi.const_mul _) hQM
    intro y hy
    have hQ : α * (1 + α) ≤ Q y := by
      simp only [Q]
      have : α * κ * Y ≤ α * κ * y := mul_le_mul_of_nonneg_left hy.1 (mul_nonneg hα hκ)
      nlinarith
    exact mul_le_mul_of_nonneg_right hQ (div_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hsplit, hGY, sub_zero] at hmain
  linarith

/-- Absolute modal frequency `2π|n|/(N+1)`. -/
def modalFrequency (N : ℕ) (n : ℤ) : ℝ := |signedFrequency (N + 1 : ℕ) n|

/-- Modal Hardy weight `t(1+t)` with `t = |k_n|·√3/2`. -/
def hardyWeight (N : ℕ) (n : ℤ) : ℝ :=
  modalFrequency N n * arcFloor * (1 + modalFrequency N n * arcFloor)

theorem hardyWeight_nonneg (N : ℕ) (n : ℤ) : 0 ≤ hardyWeight N n := by
  have h : 0 ≤ modalFrequency N n * arcFloor := mul_nonneg (abs_nonneg _) arcFloor_pos.le
  exact mul_nonneg h (by linarith)

section modes

variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Hyperbolic strip mass of one Fourier mode of one deck component. -/
def modalMass (q : Deck N) (n : ℤ) : ℝ :=
  ∫ y in Ioi arcFloor, Complex.normSq (maassCoefficient N (quotientForm N f q) n y) / y ^ 2

/-- Pointwise Dirichlet energy density of one Fourier mode of one deck component. -/
def modalEnergyDensity (q : Deck N) (n : ℤ) (y : ℝ) : ℝ :=
  signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) *
      Complex.normSq (maassCoefficient N (quotientForm N f q) n y) +
    Complex.normSq (deriv (maassCoefficient N (quotientForm N f q) n) y)

/-- Strip Dirichlet energy of one Fourier mode of one deck component. -/
def modalEnergy (q : Deck N) (n : ℤ) : ℝ := ∫ y in Ioi arcFloor, modalEnergyDensity N f q n y

theorem modalMass_nonneg (q : Deck N) (n : ℤ) : 0 ≤ modalMass N f q n :=
  setIntegral_nonneg measurableSet_Ioi (fun _ _ => div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

theorem modalEnergyDensity_nonneg (q : Deck N) (n : ℤ) (y : ℝ) : 0 ≤ modalEnergyDensity N f q n y :=
  add_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)

theorem coefficient_continuousOn (q : Deck N) (n : ℤ) :
    ContinuousOn (maassCoefficient N (quotientForm N f q) n) (Ioi 0) := fun _ hy =>
  (maassCoefficient_hasDerivAt N (quotientForm N f q) n hy).continuousAt.continuousWithinAt

theorem coefficient_deriv_continuousOn (q : Deck N) (n : ℤ) :
    ContinuousOn (deriv (maassCoefficient N (quotientForm N f q) n)) (Ioi 0) := fun _ hy =>
  (maassCoefficient_second_hasDerivAt N (quotientForm N f q) n hy).continuousAt.continuousWithinAt

theorem modalEnergyDensity_continuousOn (q : Deck N) (n : ℤ) :
    ContinuousOn (modalEnergyDensity N f q n) (Ioi 0) := by
  unfold modalEnergyDensity
  exact (continuousOn_const.mul (Complex.continuous_normSq.comp_continuousOn
    (coefficient_continuousOn N f q n))).add
    (Complex.continuous_normSq.comp_continuousOn (coefficient_deriv_continuousOn N f q n))

theorem modalMassDensity_continuousOn (q : Deck N) (n : ℤ) :
    ContinuousOn (fun y => Complex.normSq (maassCoefficient N (quotientForm N f q) n y) / y ^ 2)
      (Ioi 0) :=
  (Complex.continuous_normSq.comp_continuousOn (coefficient_continuousOn N f q n)).div
    (continuousOn_pow 2) (fun _ hy => pow_ne_zero 2 (ne_of_gt hy))

/-- A single mode never exceeds the total modal gradient energy of its component. -/
theorem modalEnergyDensity_le (q : Deck N) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    modalEnergyDensity N f q n y ≤ gradientEnergy N (quotientForm N f q) y :=
  le_hasSum (gradientEnergy_hasSum N (quotientForm N f q) hy) n
    (fun j _ => modalEnergyDensity_nonneg N f q j y)

theorem coefficient_normSq_le_mass (q : Deck N) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    Complex.normSq (maassCoefficient N (quotientForm N f q) n y) ≤ mass N (quotientForm N f q) y :=
  le_hasSum (mass_hasSum N (quotientForm N f q) hy) n (fun _ _ => Complex.normSq_nonneg _)

theorem gradientEnergy_nonneg' (q : Deck N) {y : ℝ} (hy : 0 < y) :
    0 ≤ gradientEnergy N (quotientForm N f q) y :=
  (modalEnergyDensity_nonneg N f q 0 y).trans (modalEnergyDensity_le N f q 0 hy)

theorem mass_nonneg' (q : Deck N) {y : ℝ} (hy : 0 < y) : 0 ≤ mass N (quotientForm N f q) y :=
  (Complex.normSq_nonneg _).trans (coefficient_normSq_le_mass N f q 0 hy)

/-- Component gradient energy is bounded by the unit-strip gradient slice. -/
theorem gradientEnergy_le_gslice (q : Deck N) {y : ℝ} (hy : 0 < y) :
    gradientEnergy N (quotientForm N f q) y ≤
      ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y) := by
  rw [gslice_eq N f hy, sliceGradient, gradient_integral_eq_sum N f hy]
  exact Finset.single_le_sum (fun j _ => gradientEnergy_nonneg' N f j hy) (Finset.mem_univ q)

/-- Component mass density is bounded by the unit-strip mass slice. -/
theorem mass_div_le_mslice (q : Deck N) {y : ℝ} (hy : 0 < y) :
    mass N (quotientForm N f q) y / y ^ 2 ≤
      ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y) := by
  rw [mslice_eq N f hy, SelbergMaassStripHardyGap.sliceMass, density_integral_eq_sum_mass N f hy]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact Finset.single_le_sum (fun j _ => mass_nonneg' N f j hy) (Finset.mem_univ q)

end modes

section exceptional

variable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))

theorem gslice_integrable :
    IntegrableOn (fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), planarGradient N f (x, y))
      (Ioi arcFloor) :=
  (rectangle_slices_integrable (rectangle_gradient_integrable N lam f)).mono_set Ioi_subset_Ici_self

theorem mslice_integrable :
    IntegrableOn (fun y => ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y))
      (Ioi arcFloor) :=
  (rectangle_slices_integrable (rectangle_mass_integrable N lam f)).mono_set Ioi_subset_Ici_self

theorem modalEnergyDensity_integrable (q : Deck N) (n : ℤ) :
    IntegrableOn (modalEnergyDensity N f q n) (Ioi arcFloor) := by
  refine Integrable.mono' (gslice_integrable N lam f) ?_ ?_
  · exact ((modalEnergyDensity_continuousOn N f q n).mono
      (Ioi_subset_Ioi arcFloor_pos.le)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := arcFloor_pos.trans hy
    rw [Real.norm_eq_abs, abs_of_nonneg (modalEnergyDensity_nonneg N f q n y)]
    exact (modalEnergyDensity_le N f q n hy0).trans (gradientEnergy_le_gslice N f q hy0)

theorem modalMassDensity_integrable (q : Deck N) (n : ℤ) :
    IntegrableOn (fun y => Complex.normSq (maassCoefficient N (quotientForm N f q) n y) / y ^ 2)
      (Ioi arcFloor) := by
  refine Integrable.mono' (mslice_integrable N lam f) ?_ ?_
  · exact ((modalMassDensity_continuousOn N f q n).mono
      (Ioi_subset_Ioi arcFloor_pos.le)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := arcFloor_pos.trans hy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
    exact (div_le_div_of_nonneg_right (coefficient_normSq_le_mass N f q n hy0) (sq_nonneg _)).trans
      (mass_div_le_mslice N f q hy0)

/-- Modal Hardy inequality: each Fourier mode of each deck component carries strip
energy at least `t(1+t)` times its strip mass, with `t = |k_n|·√3/2`. -/
theorem modal_hardy (q : Deck N) (n : ℤ) :
    hardyWeight N n * modalMass N f q n ≤ modalEnergy N f q n := by
  set c := maassCoefficient N (quotientForm N f q) n
  set κ := modalFrequency N n
  have hκ : 0 ≤ κ := abs_nonneg _
  have hκ2 : κ ^ 2 = signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) := sq_abs _
  have hfin : ∀ R, arcFloor ≤ R →
      hardyWeight N n * (∫ y in arcFloor..R, Complex.normSq (c y) / y ^ 2) ≤
        modalEnergy N f q n + κ * mass N (quotientForm N f q) R := by
    intro R hR
    have hH := hardy_interval (c := c) (c' := deriv c) (κ := κ) arcFloor_pos hκ hR
      (fun y hy => maassCoefficient_hasDerivAt N (quotientForm N f q) n hy)
      (coefficient_deriv_continuousOn N f q n)
    simp only [Complex.sq_norm, hκ2] at hH
    have hE : (∫ y in arcFloor..R, (signedFrequency (N + 1 : ℕ) n ^ (2 : ℕ) * Complex.normSq (c y) +
        Complex.normSq (deriv c y))) ≤ modalEnergy N f q n := by
      rw [intervalIntegral.integral_of_le hR]
      exact setIntegral_mono_set (modalEnergyDensity_integrable N lam f q n)
        (Eventually.of_forall (fun y => modalEnergyDensity_nonneg N f q n y))
        (Ioc_subset_Ioi_self.eventuallyLE)
    have hR0 : 0 < R := arcFloor_pos.trans_le hR
    have hc := coefficient_normSq_le_mass N f q n hR0
    have hw : hardyWeight N n = κ * arcFloor * (1 + κ * arcFloor) := rfl
    rw [hw]
    nlinarith [mul_le_mul_of_nonneg_left hc hκ]
  have hlim : Tendsto (fun R => hardyWeight N n *
      (∫ y in arcFloor..R, Complex.normSq (c y) / y ^ 2) - κ * mass N (quotientForm N f q) R)
      atTop (𝓝 (hardyWeight N n * modalMass N f q n - κ * 0)) :=
    ((intervalIntegral_tendsto_integral_Ioi arcFloor (modalMassDensity_integrable N lam f q n)
      tendsto_id).const_mul _).sub ((mass_decay N (quotientForm N f q)).const_mul _)
  rw [mul_zero, sub_zero] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop arcFloor] with R hR
  have := hfin R hR
  linarith

/-- Finite modal energy sums never exceed the strip energy. -/
theorem modal_energy_partial_le (s : Finset ℤ) :
    ∑ q : Deck N, ∑ n ∈ s, modalEnergy N f q n ≤ ∫ p in rectangle, planarGradient N f p := by
  rw [rectangle_integral (rectangle_gradient_integrable N lam f), integral_Ici_eq_integral_Ioi]
  have hi : ∀ q : Deck N, ∀ n ∈ s, Integrable (modalEnergyDensity N f q n)
      (volume.restrict (Ioi arcFloor)) := fun q n _ => modalEnergyDensity_integrable N lam f q n
  have heq : ∑ q : Deck N, ∑ n ∈ s, modalEnergy N f q n =
      ∫ y in Ioi arcFloor, ∑ q : Deck N, ∑ n ∈ s, modalEnergyDensity N f q n y := by
    rw [integral_finsetSum _ (fun q _ => integrable_finsetSum _ (hi q))]
    exact Finset.sum_congr rfl (fun q _ => (integral_finsetSum _ (hi q)).symm)
  rw [heq]
  apply setIntegral_mono_on (integrable_finsetSum _ (fun q _ => integrable_finsetSum _ (hi q)))
    (gslice_integrable N lam f) measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := arcFloor_pos.trans hy
  rw [gslice_eq N f hy0, sliceGradient, gradient_integral_eq_sum N f hy0]
  apply Finset.sum_le_sum
  intro q _
  exact sum_le_hasSum s (fun j _ => modalEnergyDensity_nonneg N f q j y)
    (gradientEnergy_hasSum N (quotientForm N f q) hy0)

/-- The corpus strip/cell comparison: strip energy is at most `2λ` times strip mass. -/
theorem strip_energy_le_two_lam :
    (∫ p in rectangle, planarGradient N f p) ≤
      2 * (lam : ℝ) * ∫ p in rectangle, massDensity N f p := by
  have hupper := SelbergModularStripComparison.integral_strip_le_twice (cell_gradient_integrable N lam f)
    (hyperbolicGradient_nonneg N f) (hyperbolicGradient_invariant N f ModularGroup.S)
  rw [strip_gradient_identity, cell_gradient_identity] at hupper
  have hmass := setIntegral_mono_set
    (SelbergModularStripComparison.integrable_strip (cell_mass_integrable N lam f)
      (density_invariant N f ModularGroup.S))
    (Eventually.of_forall (density_nonneg N f))
    (Eventually.of_forall SelbergModularStripComparison.fd_subset_strip)
  change (∫ z : ℍ in ModularGroup.fd, density N f z) ≤
    ∫ z in SelbergModularStripComparison.strip, density N f z at hmass
  rw [cell_mass_identity, strip_mass_identity] at hmass
  have hl : 0 ≤ (lam : ℝ) := lam.2.1.le
  nlinarith [mul_le_mul_of_nonneg_left hmass hl]

/-- Every component's modal masses are summable with sum its strip mass. -/
theorem modalMass_hasSum (q : Deck N) :
    HasSum (modalMass N f q)
      (∫ y in Ioi arcFloor, mass N (quotientForm N f q) y / y ^ 2) := by
  have hint := modalMassDensity_integrable N lam f q
  have hbound : ∀ s : Finset ℤ, ∑ n ∈ s, modalMass N f q n ≤
      ∫ y in Ioi arcFloor, ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), massDensity N f (x, y) := by
    intro s
    unfold modalMass
    rw [← integral_finsetSum _ (fun n _ => hint n)]
    apply setIntegral_mono_on (integrable_finsetSum _ (fun n _ => hint n))
      (mslice_integrable N lam f) measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := arcFloor_pos.trans hy
    rw [← Finset.sum_div]
    exact (div_le_div_of_nonneg_right (sum_le_hasSum s (fun j _ => Complex.normSq_nonneg _)
      (mass_hasSum N (quotientForm N f q) hy0)) (sq_nonneg _)).trans (mass_div_le_mslice N f q hy0)
  have hsum : Summable (modalMass N f q) :=
    summable_of_sum_le (fun n => modalMass_nonneg N f q n) hbound
  have hnorm : Summable fun n => ∫ y in Ioi arcFloor,
      ‖Complex.normSq (maassCoefficient N (quotientForm N f q) n y) / y ^ 2‖ := by
    refine hsum.congr (fun n => ?_)
    unfold modalMass
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))]
  have htsum := integral_tsum_of_summable_integral_norm hint hnorm
  have hpt : (∫ y in Ioi arcFloor, ∑' n : ℤ,
      Complex.normSq (maassCoefficient N (quotientForm N f q) n y) / y ^ 2) =
      ∫ y in Ioi arcFloor, mass N (quotientForm N f q) y / y ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0 < y := arcFloor_pos.trans hy
    exact ((mass_hasSum N (quotientForm N f q) hy0).div_const (y ^ 2)).tsum_eq
  rw [hpt] at htsum
  rw [← htsum]
  exact hsum.hasSum

/-- The strip mass is the complete modal mass. -/
theorem strip_mass_eq_modal :
    (∫ p in rectangle, massDensity N f p) = ∑ q : Deck N, ∑' n, modalMass N f q n := by
  have hq : ∀ q : Deck N, IntegrableOn (fun y => mass N (quotientForm N f q) y / y ^ 2)
      (Ioi arcFloor) := by
    intro q
    refine Integrable.mono' (mslice_integrable N lam f) ?_ ?_
    · have hc : ContinuousOn (fun y => mass N (quotientForm N f q) y / y ^ 2) (Ioi arcFloor) :=
        fun y hy => by
          have hy0 : 0 < y := arcFloor_pos.trans hy
          exact ((mass_hasDerivAt N (quotientForm N f q) hy0).continuousAt.div
            (continuousAt_id.pow 2) (pow_ne_zero 2 hy0.ne')).continuousWithinAt
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 < y := arcFloor_pos.trans hy
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mass_nonneg' N f q hy0) (sq_nonneg _))]
      exact mass_div_le_mslice N f q hy0
  rw [rectangle_integral (rectangle_mass_integrable N lam f), integral_Ici_eq_integral_Ioi]
  simp_rw [fun q => (modalMass_hasSum N lam f q).tsum_eq]
  rw [← integral_finsetSum _ (fun q _ => hq q)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  have hy0 : 0 < y := arcFloor_pos.trans hy
  simp only
  rw [mslice_eq N f hy0, SelbergMaassStripHardyGap.sliceMass, density_integral_eq_sum_mass N f hy0,
    Finset.sum_div]

/-- **Modal Hardy law.** For every exceptional Maass cusp eigenform on `Γ(N+1)`,
`Σ_q Σ_n t_n(1+t_n)·M_{q,n} ≤ 2λ·Σ_q Σ_n M_{q,n}`, where `M_{q,n}` is the strip mass of
Fourier mode `n` of deck component `q` and `t_n = (2π|n|/(N+1))·√3/2`. -/
theorem modal_hardy_law :
    (∑ q : Deck N, ∑' n, hardyWeight N n * modalMass N f q n) ≤
      2 * (lam : ℝ) * ∑ q : Deck N, ∑' n, modalMass N f q n := by
  have hW : ∀ q : Deck N, ∀ s : Finset ℤ, ∑ n ∈ s, hardyWeight N n * modalMass N f q n ≤
      ∑ n ∈ s, modalEnergy N f q n := fun q s =>
    Finset.sum_le_sum (fun n _ => modal_hardy N lam f q n)
  have hE0 : ∀ q n, 0 ≤ modalEnergy N f q n := fun q n =>
    setIntegral_nonneg measurableSet_Ioi (fun y _ => modalEnergyDensity_nonneg N f q n y)
  have hnn : ∀ q, 0 ≤ fun n => hardyWeight N n * modalMass N f q n := fun q n =>
    mul_nonneg (hardyWeight_nonneg N n) (modalMass_nonneg N f q n)
  have hsingle : ∀ q : Deck N, ∀ s : Finset ℤ, ∑ n ∈ s, modalEnergy N f q n ≤
      ∫ p in rectangle, planarGradient N f p := by
    intro q s
    refine le_trans ?_ (modal_energy_partial_le N lam f s)
    exact Finset.single_le_sum (f := fun q => ∑ n ∈ s, modalEnergy N f q n)
      (fun j _ => Finset.sum_nonneg (fun n _ => hE0 j n)) (Finset.mem_univ q)
  have hsum : ∀ q, Summable fun n => hardyWeight N n * modalMass N f q n := fun q =>
    summable_of_sum_le (hnn q) (fun s => (hW q s).trans (hsingle q s))
  rw [← (strip_mass_eq_modal N lam f)]
  refine le_trans ?_ (strip_energy_le_two_lam N lam f)
  rw [← Summable.tsum_finsetSum (fun q _ => hsum q)]
  apply Real.tsum_le_of_sum_le (fun n => Finset.sum_nonneg (fun q _ => hnn q n))
  intro s
  rw [Finset.sum_comm]
  refine le_trans (Finset.sum_le_sum (fun q _ => hW q s)) ?_
  exact modal_energy_partial_le N lam f s

/-- **Low-mode dominance.** An exceptional eigenform has strictly negative net Hardy excess:
the strip mass carried by modes with weight `t_n(1+t_n) < 1/2` must outweigh the excess of all
other modes. With `t_n = π√3|n|/(N+1)`, the deficient modes are exactly
`|n| < 0.3660…·(N+1)/(π√3)`, i.e. `|n| ≲ 0.0673·(N+1)`. -/
theorem low_mode_dominance :
    (∑ q : Deck N, ∑' n, (hardyWeight N n - 1 / 2) * modalMass N f q n) < 0 := by
  have hpos : 0 < ∫ p in rectangle, massDensity N f p := by
    have hmass := setIntegral_mono_set
      (SelbergModularStripComparison.integrable_strip (cell_mass_integrable N lam f)
        (density_invariant N f ModularGroup.S))
      (Eventually.of_forall (density_nonneg N f))
      (Eventually.of_forall SelbergModularStripComparison.fd_subset_strip)
    change (∫ z : ℍ in ModularGroup.fd, density N f z) ≤
      ∫ z in SelbergModularStripComparison.strip, density N f z at hmass
    rw [cell_mass_identity, strip_mass_identity] at hmass
    exact (full_mass_pos N lam f).trans_le hmass
  have hlaw := modal_hardy_law N lam f
  rw [← strip_mass_eq_modal N lam f] at hlaw
  have hM : ∀ q, Summable (modalMass N f q) := fun q => (modalMass_hasSum N lam f q).summable
  have hWsum : ∀ q, Summable fun n => hardyWeight N n * modalMass N f q n := fun q =>
    summable_of_sum_le (fun n => mul_nonneg (hardyWeight_nonneg N n) (modalMass_nonneg N f q n))
      (fun s => (Finset.sum_le_sum (fun n _ => modal_hardy N lam f q n)).trans
        ((Finset.single_le_sum (f := fun q => ∑ n ∈ s, modalEnergy N f q n)
          (fun j _ => Finset.sum_nonneg (fun n _ => setIntegral_nonneg measurableSet_Ioi
            (fun y _ => modalEnergyDensity_nonneg N f j n y))) (Finset.mem_univ q)).trans
          (modal_energy_partial_le N lam f s)))
  have hsplit : ∀ q, (∑' n, (hardyWeight N n - 1 / 2) * modalMass N f q n) =
      (∑' n, hardyWeight N n * modalMass N f q n) - 1 / 2 * ∑' n, modalMass N f q n := by
    intro q
    rw [← tsum_mul_left, ← (hWsum q).tsum_sub ((hM q).mul_left _)]
    congr 1
    funext n
    ring
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← strip_mass_eq_modal N lam f]
  have hl := lam.2.2
  nlinarith

end exceptional

end
end GaloisForLFunctions.RHTower.SelbergMaassModalHardyLaw
