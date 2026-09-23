import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

/-!
# Finite congruence trace of actual Maass eigenforms

The actual integral pullbacks descend to the finite principal-congruence quotient.
Their squared norms sum to a nonzero C² density invariant under the full integral
modular group. Its unit-period mass equals the sum of the width-normalized actual
Maass masses; its two height derivatives are the corresponding physical flux and
energy sums.

The existing Bessel identities therefore give an exact boundary decomposition for
the literal unit-strip tail mass of this finite trace. The cosets need not enumerate
distinct cusps once. No compact-core Green identity or quarter bound is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace
open SelbergMaassCuspTransport
noncomputable section

/-- The finite quotient by the positive-level principal congruence subgroup. -/
abbrev Deck (N : ℕ) := SL2Z ⧸ CongruenceSubgroup.Gamma (N + 1)

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-- The group structure on the actual congruence quotient. -/
instance deckGroup (N : ℕ) : Group (Deck N) := inferInstance

/-- Positive congruence level gives a finite quotient without enumerating matrices. -/
instance deckFintype (N : ℕ) : Fintype (Deck N) :=
  Subgroup.fintypeQuotientOfFiniteIndex

/-- The actual translated Maass family descends to the congruence quotient. -/
def quotientForm (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Deck N → MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam :=
  Quotient.lift (fun A => translate (N + 1) A f) (by
    intro A B h
    have hm : A⁻¹ * B ∈ CongruenceSubgroup.Gamma (N + 1) :=
      QuotientGroup.leftRel_apply.mp h
    have ht := translate_congruence (N + 1) (A⁻¹ * B) hm (translate (N + 1) A f)
    rw [translate_mul, mul_inv_cancel_left] at ht
    exact ht.symm)

/-- The quotient family at a matrix class is its literal translated Maass form. -/
@[simp] theorem quotientForm_mk (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (A : SL2Z) :
    quotientForm N f (QuotientGroup.mk A) = translate (N + 1) A f := rfl

/-- Right multiplication in the quotient is actual integral pullback of its Maass family. -/
theorem quotientForm_mul (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (q : Deck N) (A : SL2Z) :
    quotientForm N f (q * QuotientGroup.mk A) = translate (N + 1) A (quotientForm N f q) := by
  induction q using Quotient.inductionOn with
  | h B =>
    simpa only [← QuotientGroup.mk_mul, quotientForm_mk] using (translate_mul (N + 1) B A f).symm

/-- Sum of the literal squared norms over the finite congruence quotient. -/
def density (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) : ℝ :=
  ∑ q : Deck N, Complex.normSq ((quotientForm N f q).1.1 z)

/-- The actual finite trace density is invariant under every integral modular matrix. -/
theorem density_invariant (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (A : SL2Z) (z : ℍ) : density N f (A • z) = density N f z := by
  unfold density
  simp_rw [← translate_apply (N + 1) A, ← quotientForm_mul]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => Complex.normSq ((quotientForm N f q).1.1 z))

/-- Every actual squared norm in the finite trace is nonnegative. -/
theorem density_nonneg (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    0 ≤ density N f z :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

/-- The identity coset bounds the original squared norm by the finite trace. -/
theorem normSq_le_density (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (z : ℍ) :
    Complex.normSq (f.1.1 z) ≤ density N f z := by
  have h := Finset.single_le_sum (f := fun q : Deck N => Complex.normSq ((quotientForm N f q).1.1 z))
    (s := Finset.univ) (fun q _ => Complex.normSq_nonneg _) (Finset.mem_univ (QuotientGroup.mk (1 : SL2Z)))
  simpa only [quotientForm_mk, translate_one, density] using h

/-- Original Maass nonvanishing makes the actual modular trace positive somewhere. -/
theorem density_pos_somewhere (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ∃ z : ℍ, 0 < density N f z := by
  by_contra hn
  apply f.2.1
  apply Subtype.ext
  funext z
  have hzero : Complex.normSq (f.1.1 z) = 0 := le_antisymm
    ((normSq_le_density N f z).trans (le_of_not_gt (fun h => hn ⟨z, h⟩)))
    (Complex.normSq_nonneg _)
  exact Complex.normSq_eq_zero.mp hzero

private theorem normSq_contDiffOn {F : ℂ → ℂ}
    (hF : ContDiffOn ℝ 2 F {z : ℂ | 0 < z.im}) :
    ContDiffOn ℝ 2 (fun z => Complex.normSq (F z)) {z : ℂ | 0 < z.im} := by
  have hr := Complex.reCLM.contDiff.comp_contDiffOn hF
  have hi := Complex.imCLM.contDiff.comp_contDiffOn hF
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.normSq_apply] using (hr.mul hr).add (hi.mul hi)

/-- The finite trace retains real C² chart regularity. -/
theorem density_contDiffOn (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ContDiffOn ℝ 2 (density N f ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  exact ContDiffOn.sum (fun q _ => normSq_contDiffOn (quotientForm N f q).2.2.1.1)

/-- The actual finite trace tends uniformly to zero at infinity. -/
theorem density_decay (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    IsZeroAtImInfty (density N f) := by
  have hq (q : Deck N) : Tendsto (fun z => Complex.normSq ((quotientForm N f q).1.1 z))
      atImInfty (𝓝 (0 : ℝ)) := by
    have h := (quotientForm N f q).2.2.2 (1 : SL2Z)
    have h' : Tendsto (quotientForm N f q).1.1 atImInfty (𝓝 (0 : ℂ)) := by
      simpa only [IsZeroAtImInfty, ZeroAtFilter, map_one, one_smul] using h
    simpa only [Complex.normSq_zero, Function.comp_def] using (Complex.continuous_normSq.tendsto 0).comp h'
  change Tendsto (fun z => ∑ q : Deck N, Complex.normSq ((quotientForm N f q).1.1 z)) atImInfty (𝓝 0)
  simpa only [density, Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun q _ => hq q)

open MeasureTheory SelbergMaassMean SelbergMaassFlux

/-- Each positive-height horizontal slice of the trace is continuous. -/
theorem density_slice_continuous (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => density N f (ofComplex (point x y))) := by
  exact continuous_finsetSum Finset.univ (fun q _ => Complex.continuous_normSq.comp
    (slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy))

/-- Full modular invariance gives period one to each actual horizontal trace slice. -/
theorem density_slice_periodic (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => density N f (ofComplex (point x y))) 1 := by
  intro x
  have hp : 0 < (point x y).im := by simpa [point] using hy
  let z : ℍ := ⟨point x y, hp⟩
  have hi := density_invariant N f ModularGroup.T z
  have hz : ofComplex (point (x + 1) y) = ModularGroup.T • z := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy), UpperHalfPlane.modular_T_smul]
    simp only [UpperHalfPlane.coe_vadd, z, point]
    push_cast
    ring
  change density N f (ofComplex (point (x + 1) y)) = density N f (ofComplex (point x y))
  rw [hz, ofComplex_apply_of_im_pos hp]
  exact hi

/-- The unit-period trace integral equals the sum of the width-normalized actual Maass masses. -/
theorem density_integral_eq_sum_mass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y))) =
      ∑ q : Deck N, mass N (quotientForm N f q) y := by
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun x => density N f (ofComplex (point x y))) volume a b :=
    (density_slice_continuous N f hy).intervalIntegrable
  have hper := (density_slice_periodic N f hy).intervalIntegral_add_zsmul_eq
    ((N + 1 : ℕ) : ℤ) 0 hint
  have hscale : (∫ x in (0 : ℝ)..(N + 1 : ℕ), density N f (ofComplex (point x y))) =
      ((N + 1 : ℕ) : ℝ) * ∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y)) := by
    simpa only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] using hper
  simp_rw [mass_eq_integral N _ hy]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
  · change _ = ((N + 1 : ℕ) : ℝ)⁻¹ *
      ∫ x in (0 : ℝ)..(N + 1 : ℕ), density N f (ofComplex (point x y))
    rw [hscale]
    field_simp
  · intro q _
    exact (Complex.continuous_normSq.comp
      (slice_continuous (quotientForm N f q).2.2.1.1.continuousOn hy)).intervalIntegrable _ _

/-- The actual unit-period trace mass differentiates to twice the total physical flux. -/
theorem density_slice_mass_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => ∫ x in (0 : ℝ)..1, density N f (ofComplex (point x t)))
      (2 * ∑ q : Deck N, flux N (quotientForm N f q) y) y := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Deck N)))
    (fun q _ => mass_hasDerivAt N (quotientForm N f q) hy)
  rw [← Finset.mul_sum] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact density_integral_eq_sum_mass N f ht

/-- The second derivative of the actual trace mass retains all gradient energies and spectral masses. -/
theorem density_slice_mass_second_hasDerivAt (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (fun t => ∫ x in (0 : ℝ)..1, density N f (ofComplex (point x t))))
      (2 * ∑ q : Deck N, (gradientEnergy N (quotientForm N f q) y -
        lam / y ^ (2 : ℕ) * mass N (quotientForm N f q) y)) y := by
  have h := (HasDerivAt.fun_sum (u := (Finset.univ : Finset (Deck N)))
    (fun q _ => flux_hasDerivAt N (quotientForm N f q) hy)).const_mul 2
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hy] with t ht
  exact (density_slice_mass_hasDerivAt N f ht).deriv

open SelbergMaassTailEnergy SelbergMaassBoundaryForm SelbergMaassTrace SelbergBoundaryOperator

/-- The unit-strip hyperbolic trace mass is integrable above every positive height in the exceptional interval. -/
theorem density_tail_mass_integrable (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y => (∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y))) / y ^ (2 : ℕ))
      (Ioi Y) := by
  apply (integrable_finsetSum Finset.univ
    (fun q _ => hyperbolicMass_tail_integrable N lam (quotientForm N f q) hY)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [density_integral_eq_sum_mass N f (hY.trans hy), Finset.sum_div]

/-- Literal hyperbolic mass of the trace on the infinite unit-period strip. -/
def tailMass (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (Y : ℝ) : ℝ :=
  ∫ y in Ioi Y, (∫ x in (0 : ℝ)..1, density N f (ofComplex (point x y))) / y ^ (2 : ℕ)

/-- The literal trace tail mass equals the finite sum of actual normalized Maass tail masses. -/
theorem tailMass_eq_sum (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ))
    {Y : ℝ} (hY : 0 < Y) :
    tailMass N f Y = ∑ q : Deck N, ∫ y in Ioi Y, mass N (quotientForm N f q) y / y ^ (2 : ℕ) := by
  unfold tailMass
  rw [← integral_finsetSum Finset.univ (fun q _ =>
    hyperbolicMass_tail_integrable N lam (quotientForm N f q) hY)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [density_integral_eq_sum_mass N f (hY.trans hy), Finset.sum_div]

/-- Sum of the actual Bessel boundary forms on the congruence quotient family. -/
def boundarySum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (T : ℝ) : ℝ :=
  ∑ q : Deck N, boundaryForm (Real.log (N + 1 : ℕ)) T (formTrace N (quotientForm N f q) T)

/-- Finite sum of the actual convergent nonnegative Fourier square-remainder series. -/
def squareSum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (T : ℝ) : ℝ :=
  ∑ q : Deck N, ∑' n : ℤ, modeSquareTail N (quotientForm N f q) T n

/-- The complete trace square remainder is nonnegative. -/
theorem squareSum_nonneg (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (T : ℝ) :
    0 ≤ squareSum N f T :=
  Finset.sum_nonneg (fun q _ => tsum_nonneg (modeSquareTail_nonneg N (quotientForm N f q) T))

/-- Actual total flux and unit-strip spectral tail mass equal the full trace Bessel form plus squares. -/
theorem trace_flux_boundary_identity (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    -(∑ q : Deck N, flux N (quotientForm N f q) (Real.exp T)) +
      ((lam : ℝ) - 1 / 4) * tailMass N f (Real.exp T) = boundarySum N f T + squareSum N f T := by
  rw [tailMass_eq_sum N lam f (Real.exp_pos T)]
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Deck N))) rfl
    (fun q _ => maass_flux_boundary_identity N lam (quotientForm N f q) T)
  simpa only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    boundarySum, squareSum] using h

/-- The actual trace Bessel form bounds the total flux and unit-strip spectral mass expression below. -/
theorem trace_flux_boundary_lower_bound (N : ℕ) (lam : Ioo (0 : ℝ) (1 / 4))
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) (lam : ℝ)) (T : ℝ) :
    boundarySum N f T ≤ -(∑ q : Deck N, flux N (quotientForm N f q) (Real.exp T)) +
      ((lam : ℝ) - 1 / 4) * tailMass N f (Real.exp T) := by
  rw [trace_flux_boundary_identity N lam f T]
  exact le_add_of_nonneg_right (squareSum_nonneg N f T)

end
end GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace
