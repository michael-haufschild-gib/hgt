import GaloisForLFunctions.RHTower.WeilDeletionCCMSource
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeCCMScalingBridge
import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundEnergy
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# Single-prime deletion inside the restricted Weil operator: a forced sign change

The Connes–Consani–Moscovici restricted Weil form at aperture `a` contains exactly the prime powers
`n ≤ e^{2a}`.  Removing one prime `p` from its finite prime block gives the *deleted* restricted
Weil form.  Below the visibility threshold `e^{2a} < p` the deleted form is the literal one, so its
ground energy is positive at small apertures.  At the aperture `a = ½ log p + s + 1` the deleted
form is negative on the two-bump source of the uniform deletion theorem, because the literal source
quadratic there is bounded by the explicit zero-side constant while the removed prime block equals
`(log p / √p) · (−2 ∫ φ²)`.

Consequently the ground energy of the deleted family changes sign between the small apertures and
`½ log p + s + 1`, for every prime `p ≥ e^{18}`.  Any argument for `ker A_a = 0` at every aperture
that uses the prime block only through properties shared with the block of `Λ − log p · 1_p`
(nonnegativity, boundedness, self-adjointness, atomic jump structure) would apply to the deleted
family and is therefore invalid.
-/

open Complex MeasureTheory Set
open scoped Convolution
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilDeletion

/-! ## The visible prime block and the deleted remainder -/

/-- The prime-transport block of `p` at aperture `a`, present exactly when `p ≤ e^{2a}`. -/
noncomputable def ccmVisiblePrimeBlock (a : SuzukiPositiveAperture) (p : ℕ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  if p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) then
    ((ArithmeticFunction.vonMangoldt p : ℝ) : ℂ) • ccmPrimeTransportOperator a p
  else 0

theorem ccmVisiblePrimeBlock_isSelfAdjoint (a : SuzukiPositiveAperture) (p : ℕ) :
    IsSelfAdjoint (ccmVisiblePrimeBlock a p) := by
  unfold ccmVisiblePrimeBlock
  split_ifs with h
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    have hself := ccmPrimeTransportOperator_isSelfAdjoint a p
    rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hself
    rw [ContinuousLinearMap.adjoint.map_smulₛₗ, hself, Complex.conj_ofReal]
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp

theorem ccmVisiblePrimeBlock_of_invisible (a : SuzukiPositiveAperture) {p : ℕ}
    (h : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    ccmVisiblePrimeBlock a p = 0 := by
  unfold ccmVisiblePrimeBlock
  exact if_neg h

/-- The bounded remainder of the restricted Weil form with the prime `p` removed from the finite
prime block (removal is adding the block back, since the block enters with a minus sign). -/
noncomputable def ccmDeletedRemainder (a : SuzukiPositiveAperture) (p : ℕ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a + ccmVisiblePrimeBlock a p

theorem ccmDeletedRemainder_isSelfAdjoint (a : SuzukiPositiveAperture) (p : ℕ) :
    IsSelfAdjoint (ccmDeletedRemainder a p) := by
  unfold ccmDeletedRemainder
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  have h2 := ccmVisiblePrimeBlock_isSelfAdjoint a p
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [ContinuousLinearMap.adjoint.map_add, h1, h2]

theorem ccmDeletedRemainder_of_invisible (a : SuzukiPositiveAperture) {p : ℕ}
    (h : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    ccmDeletedRemainder a p = ccmRestrictedWeilBoundedRemainder a := by
  unfold ccmDeletedRemainder
  rw [ccmVisiblePrimeBlock_of_invisible a h, add_zero]

/-! ## The deleted ground energy -/

/-- Bottom spectral value of the deleted restricted Weil operator, through its covariance. -/
noncomputable def ccmDeletedGroundEnergy (a : SuzukiPositiveAperture) (p : ℕ) : ℝ :=
  ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a)
      (ccmDeletedRemainder a p) (ccmDeletedRemainder_isSelfAdjoint a p)‖⁻¹ -
    boundedPerturbedFormShift (ccmDeletedRemainder a p)

theorem boundedPerturbedFormCovariance_congr {H V : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (J : V →L[ℂ] H) {B B' : H →L[ℂ] H} (h : B = B') (hB : IsSelfAdjoint B)
    (hB' : IsSelfAdjoint B') :
    boundedPerturbedFormCovariance J B hB = boundedPerturbedFormCovariance J B' hB' := by
  subst h
  rfl

/-- Below the visibility threshold the deleted ground energy is the literal one. -/
theorem ccmDeletedGroundEnergy_of_invisible (a : SuzukiPositiveAperture) {p : ℕ}
    (h : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    ccmDeletedGroundEnergy a p = ccmRestrictedWeilGroundEnergy a := by
  have he := ccmDeletedRemainder_of_invisible a h
  unfold ccmDeletedGroundEnergy ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) he _
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), he]

/-- Rayleigh bound for the deleted ground energy: the source quadratic plus the removed block. -/
theorem ccmDeletedGroundEnergy_mul_formNorm_sq_le (a : SuzukiPositiveAperture) (p : ℕ)
    (u : CCMArchimedeanFormDomain a) :
    ccmDeletedGroundEnergy a p * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u +
        (inner ℂ (ccmVisiblePrimeBlock a p (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  have hfloor := boundedPerturbedForm_ground_mul_norm_sq_le
    (ccmArchimedeanFormToAperture a) (ccmDeletedRemainder a p)
    (ccmDeletedRemainder_isSelfAdjoint a p)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a) u
  have hsplit : (inner ℂ u u + inner ℂ (ccmDeletedRemainder a p (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re =
      (ccmRestrictedWeilForm a u u).re +
        (inner ℂ (ccmVisiblePrimeBlock a p (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
    show (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u) +
      ccmVisiblePrimeBlock a p (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re = _
    rw [inner_add_left, ← add_assoc, Complex.add_re]
    rfl
  change ccmDeletedGroundEnergy a p * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤ _ at hfloor
  rw [hsplit, ccmRestrictedWeilForm_self_re_eq_source] at hfloor
  exact hfloor

/-! ## The translation pairing of a real source is its autocorrelation -/

theorem inner_logTranslation_eq_autocorr {g : ℝ → ℝ} (f : SoninL2)
    (hf : (f : ℝ → ℂ) =ᵐ[volume] fun x => (g x : ℂ)) (h : ℝ) :
    inner ℂ (logTranslationCLM h f) f = ((autocorr g h : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hT := logTranslationCLM_ae h f
  have hshift : (fun x : ℝ => (f : ℝ → ℂ) (x + h)) =ᵐ[volume] fun x => (g (x + h) : ℂ) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hf
  have hpt : (fun x : ℝ => inner ℂ ((logTranslationCLM h f : ℝ → ℂ) x) ((f : ℝ → ℂ) x)) =ᵐ[volume]
      fun x : ℝ => ((g (x + h) * g x : ℝ) : ℂ) := by
    filter_upwards [hT, hshift, hf] with x h1 h2 h3
    rw [h1, h2, h3, RCLike.inner_apply, Complex.conj_ofReal]
    push_cast
    ring
  rw [integral_congr_ae hpt, integral_complex_ofReal]
  congr 1
  -- `∫ g(x+h) g(x) dx = ∫ g(t) g(t−h) dt = (g ⋆ g̃)(h)`
  unfold autocorr
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, reflectFn]
  have := integral_add_right_eq_self (μ := volume) (fun t : ℝ => g t * g (t - h)) h
  simp only [add_sub_cancel_right] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring_nf

/-! ## The removed block on the two-bump source -/

theorem re_inner_visiblePrimeBlock_twoBumpSource {p : ℕ} (hp : p.Prime) (n : ℕ)
    (hu2 : 2 * sN n < Real.log p) (a : SuzukiPositiveAperture)
    (ha : Real.log p / 2 + sN n < a.1)
    (hvis : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1)))) :
    let u := twoBumpSource n (by linarith [sN_pos n] : 0 ≤ Real.log p) a ha
    (inner ℂ (ccmVisiblePrimeBlock a p (ccmArchimedeanFormToAperture a u.toCCMFormVector))
      (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re =
      Real.log p * (1 / Real.sqrt p) * (-2 * ∫ x, phiN n x ^ 2) := by
  intro u
  have hu0 : (0 : ℝ) ≤ Real.log p := by linarith [sN_pos n]
  set f := ccmArchimedeanFormToAperture a u.toCCMFormVector with hf
  have hfae : ((f : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun x => (twoBump (phiN n) (Real.log p) x : ℂ) :=
    u.toCCMFormVector_physical_coeFn
  unfold ccmVisiblePrimeBlock
  rw [if_pos hvis, smul_apply, inner_smul_left, Complex.conj_ofReal,
    inner_ccmPrimeTransportOperator, ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [inner_logTranslation_eq_autocorr _ hfae, inner_logTranslation_eq_autocorr _ hfae]
  rw [autocorr_twoBump_apply (sN_pos n).le (support_phiN_subset n) hu2,
    autocorr_twoBump_apply_neg (sN_pos n).le (support_phiN_subset n) hu2]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

/-! ## The two-bump source is nonzero -/

theorem exists_phiN_ne_zero (n : ℕ) : ∃ x : ℝ, phiN n x ≠ 0 := by
  by_contra h
  have h' : ∀ x, phiN n x = 0 := fun x => by
    by_contra hx
    exact h ⟨x, hx⟩
  have h0 : ∫ x, phiN n x ^ 2 = 0 := by
    simp [h']
  have hle := integral_phiN_sq_ge n
  rw [h0] at hle
  have hs := sN_pos n
  have : (0 : ℝ) < 1 / (2 * sN n) := by positivity
  linarith

theorem exists_twoBump_ne_zero (n : ℕ) {u₀ : ℝ} (hu2 : 2 * sN n < u₀) :
    ∃ x : ℝ, twoBump (phiN n) u₀ x ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_phiN_ne_zero n
  have hxmem : x ∈ Icc (-sN n) (sN n) := support_phiN_subset n hx
  refine ⟨x + u₀ / 2, ?_⟩
  unfold twoBump
  have h1 : x + u₀ / 2 - u₀ / 2 = x := by ring
  have h2 : phiN n (x + u₀ / 2 + u₀ / 2) = 0 := by
    have hnot : x + u₀ / 2 + u₀ / 2 ∉ Icc (-sN n) (sN n) := by
      intro hmem
      have := hmem.2
      have := hxmem.1
      linarith
    exact Function.notMem_support.mp fun hs => hnot (support_phiN_subset n hs)
  rw [h1, h2, sub_zero]
  exact hx

/-! ## Main theorems -/

/-- **Below the threshold the deleted ground energy is positive**: the deleted and literal
restricted Weil operators coincide at every aperture with `e^{2a} < p`, and the literal ground
energy is positive at small apertures. -/
theorem exists_small_aperture_ccmDeletedGroundEnergy_pos {p : ℕ} (hp : p.Prime) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ → 0 < ccmDeletedGroundEnergy a p := by
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  refine ⟨min δ₀ (Real.log p / 2), lt_min hδ₀ (by linarith), fun a ha => ?_⟩
  have ha0 : a.1 < δ₀ := lt_of_lt_of_le ha (min_le_left _ _)
  have ha1 : a.1 < Real.log p / 2 := lt_of_lt_of_le ha (min_le_right _ _)
  have hinv : p ∉ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
    rw [Finset.mem_Icc]
    rintro ⟨-, hle⟩
    have hfl : Nat.floor (Real.exp (2 * a.1)) < p := by
      rw [Nat.floor_lt (Real.exp_pos _).le]
      have : 2 * a.1 < Real.log p := by linarith
      rw [Real.lt_log_iff_exp_lt (by linarith)] at this
      exact this
    omega
  rw [ccmDeletedGroundEnergy_of_invisible a hinv]
  exact hpos a ha0

/-- **At aperture `½ log p + s + 1` the deleted ground energy is negative**, for every prime
`p ≥ e^{18}`, witnessed by the two-bump source of the uniform deletion theorem. -/
theorem ccmDeletedGroundEnergy_neg_of_large {p : ℕ} (hp : p.Prime) (hp18 : Real.exp 18 ≤ p) :
    ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log p + 1 ∧ ccmDeletedGroundEnergy a p < 0 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (Real.exp_pos _) hp18
  have hu18 : 18 ≤ Real.log p := by
    rw [Real.le_log_iff_exp_le hp0]
    exact hp18
  have hu0 : 0 ≤ Real.log p := by linarith
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hexp_half : Real.exp (Real.log p / 2) = Real.sqrt p := by
    have hsq : Real.exp (Real.log p / 2) ^ 2 = p := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (Real.log p / 2) = Real.log p by ring, Real.exp_log hp0]
    have h := Real.sqrt_sq (Real.exp_pos (Real.log p / 2)).le
    rw [hsq] at h
    exact h.symm
  obtain ⟨h2s, hexpo⟩ := params_ok hu18
  set n : ℕ := ⌊(Real.log p - 4 / 5) / (39 / 25)⌋₊ - 2 with hn
  have hsN := sN_pos n
  -- the aperture
  set a : SuzukiPositiveAperture := ⟨Real.log p / 2 + sN n + 1, by positivity⟩ with ha_def
  have ha : Real.log p / 2 + sN n < a.1 := by
    show Real.log p / 2 + sN n < Real.log p / 2 + sN n + 1
    linarith
  have hale : a.1 ≤ Real.log p + 1 := by
    show Real.log p / 2 + sN n + 1 ≤ Real.log p + 1
    linarith
  -- the prime is visible at this aperture
  have hvis : p ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) := by
    rw [Finset.mem_Icc]
    refine ⟨hp.two_le, Nat.le_floor ?_⟩
    have h2a : (2 : ℝ) * a.1 = Real.log p + (2 * sN n + 2) := by
      show (2 : ℝ) * (Real.log p / 2 + sN n + 1) = _
      ring
    rw [h2a, Real.exp_add, Real.exp_log hp0]
    have : 1 ≤ Real.exp (2 * sN n + 2) := Real.one_le_exp (by linarith)
    nlinarith
  refine ⟨a, hale, ?_⟩
  -- the two-bump source and its form vector
  set u := twoBumpSource n hu0 a ha with hu_def
  set v := ccmArchimedeanFormToAperture a u.toCCMFormVector with hv
  have hv0 : v ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_twoBump_ne_zero n h2s
    exact ccmArchimedeanFormToAperture_toCCMFormVector_ne_zero_of_apply_ne_zero u
      (x := x) (by rw [twoBumpSource_apply]; exact Complex.ofReal_ne_zero.mpr hx)
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  -- the Rayleigh bound
  have hray := ccmDeletedGroundEnergy_mul_formNorm_sq_le a p u.toCCMFormVector
  rw [← hv] at hray
  -- the source quadratic is bounded by the zero-side constant
  set X : ℝ := (1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n with hX
  have hXpos : 0 < X := by rw [hX]; positivity
  have hsource := abs_ccmRestrictedWeilSourceQuadratic_twoBumpSource_le n hu0 hexp_half a ha
  rw [← hX] at hsource
  have hsource' : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      4 * Real.sqrt p * (3 / 2) * X * (33 / 100) := le_trans (le_abs_self _) hsource
  -- the removed block
  have hblock := re_inner_visiblePrimeBlock_twoBumpSource hp n h2s a ha hvis
  simp only at hblock
  rw [← hv] at hblock
  have hint : 1 / (2 * sN n) ≤ ∫ x, phiN n x ^ 2 := integral_phiN_sq_ge n
  have hint' : 1 / Real.log p ≤ ∫ x, phiN n x ^ 2 := by
    refine le_trans ?_ hint
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    linarith
  have hprod : Real.log p * (1 / Real.sqrt p) * (-2 * ∫ x, phiN n x ^ 2) ≤ -(2 / Real.sqrt p) := by
    have h1 : Real.log p * (1 / Real.sqrt p) * (-2 * ∫ x, phiN n x ^ 2) ≤
        Real.log p * (1 / Real.sqrt p) * (-2 * (1 / Real.log p)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : Real.log p * (1 / Real.sqrt p) * (-2 * (1 / Real.log p)) = -(2 / Real.sqrt p) := by
      field_simp
    linarith
  have hpX : (p : ℝ) * X ≤ 1 := by
    have := exp_mul_X_le_one n hexpo
    rwa [Real.exp_log hp0] at this
  have hC : 4 * Real.sqrt p * (3 / 2) * X * (33 / 100) < 2 / Real.sqrt p := by
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    rw [lt_div_iff₀ hsqrt_pos]
    calc 4 * Real.sqrt p * (3 / 2) * X * (33 / 100) * Real.sqrt p
        = (99 / 50) * ((Real.sqrt p * Real.sqrt p) * X) := by ring
      _ = (99 / 50) * ((p : ℝ) * X) := by rw [hsq]
      _ ≤ 99 / 50 := by linarith
      _ < 2 := by norm_num
  have hneg : ccmDeletedGroundEnergy a p * ‖v‖ ^ 2 < 0 := by
    rw [hblock] at hray
    linarith
  rcases lt_or_ge (ccmDeletedGroundEnergy a p) 0 with hlt | hge
  · exact hlt
  · exfalso
    have := mul_nonneg hge hvpos.le
    linarith

/-- **Forced sign change of the deleted family.**  For every prime `p ≥ e^{18}`, the ground
energy of the restricted Weil operator with `p` removed is positive on an initial aperture range
and negative at an aperture below `log p + 1`. -/
theorem ccmDeletedGroundEnergy_sign_change {p : ℕ} (hp : p.Prime) (hp18 : Real.exp 18 ≤ p) :
    (∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ → 0 < ccmDeletedGroundEnergy a p) ∧
      ∃ a : SuzukiPositiveAperture, a.1 ≤ Real.log p + 1 ∧ ccmDeletedGroundEnergy a p < 0 :=
  ⟨exists_small_aperture_ccmDeletedGroundEnergy_pos hp, ccmDeletedGroundEnergy_neg_of_large hp hp18⟩

end RHTower.WeilDeletion
