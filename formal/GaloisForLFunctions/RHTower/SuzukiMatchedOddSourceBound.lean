import GaloisForLFunctions.RHTower.CCMFiniteNeumannFormDecay
import GaloisForLFunctions.RHTower.SuzukiMatchedEvenSourceBound


open Filter
open scoped InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem physical_remainder_norm (a : SuzukiPositiveAperture) :
    ‖ccmRestrictedWeilBoundedRemainder a‖ ≤
      ‖suzukiWeilIntervalBoundedRemainder a‖ := by
  apply (ccmRestrictedWeilBoundedRemainder a).opNorm_le_bound (norm_nonneg _)
  intro f
  let e := suzukiApertureL2Equiv a
  have hmap : e.symm (ccmRestrictedWeilBoundedRemainder a f) =
      suzukiWeilIntervalBoundedRemainder a (e.symm f) := by
    change e.symm (ccmRestrictedWeilBoundedRemainder a f) =
      e.symm (ccmRestrictedWeilBoundedRemainder a (e (e.symm f)))
    rw [e.apply_symm_apply]
  calc
    _ = ‖e.symm (ccmRestrictedWeilBoundedRemainder a f)‖ := (e.symm.norm_map _).symm
    _ = ‖suzukiWeilIntervalBoundedRemainder a (e.symm f)‖ := congrArg norm hmap
    _ ≤ ‖suzukiWeilIntervalBoundedRemainder a‖ * ‖e.symm f‖ :=
      (suzukiWeilIntervalBoundedRemainder a).le_opNorm _
    _ = _ := by rw [e.symm.norm_map]

theorem ccmShiftedBoundedWeil_re_inner (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmShiftedBoundedWeil a f) f).re =
    boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) * ‖f‖ ^ 2 +
        (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re := by
  have hself : (inner ℂ f f).re = ‖f‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
  change (inner ℂ ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • f +
    ccmRestrictedWeilBoundedRemainder a f) f).re = _
  rw [inner_add_left, inner_smul_left f f
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ),
    Complex.conj_ofReal, Complex.add_re,
    Complex.re_ofReal_mul, hself]

private theorem remainder_quadratic (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    |(inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re| ≤
      ‖suzukiWeilIntervalBoundedRemainder a‖ * ‖f‖ ^ 2 := by
  calc
    _ ≤ ‖inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ccmRestrictedWeilBoundedRemainder a f‖ * ‖f‖ :=
      norm_inner_le_norm (ccmRestrictedWeilBoundedRemainder a f) f
    _ ≤ (‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖) * ‖f‖ := by
      gcongr; exact (ccmRestrictedWeilBoundedRemainder a).le_opNorm f
    _ ≤ ‖suzukiWeilIntervalBoundedRemainder a‖ * ‖f‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_right (physical_remainder_norm a) (sq_nonneg ‖f‖)
      nlinarith only [h]

theorem ccmShiftedBoundedWeil_coercive (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ‖f‖ ^ 2 ≤ (inner ℂ (ccmShiftedBoundedWeil a f) f).re := by
  rw [ccmShiftedBoundedWeil_re_inner, boundedPerturbedFormShift]
  have h := (abs_le.mp (remainder_quadratic a f)).1
  linarith

private theorem shifted_upper (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmShiftedBoundedWeil a f) f).re ≤
      2 * boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) * ‖f‖ ^ 2 := by
  rw [ccmShiftedBoundedWeil_re_inner, boundedPerturbedFormShift]
  have h := (abs_le.mp (remainder_quadratic a f)).2
  nlinarith only [h, sq_nonneg ‖f‖]

private theorem shifted_cross (a : SuzukiPositiveAperture) (f u : suzukiApertureHilbert a) :
    2 * (inner ℂ (ccmShiftedBoundedWeil a u) f).re ≤
      (inner ℂ (ccmShiftedBoundedWeil a f) f).re +
        (inner ℂ (ccmShiftedBoundedWeil a u) u).re := by
  let A := ccmShiftedBoundedWeil a
  have hsym : inner ℂ (A f) u = inner ℂ f (A u) := by
    have hB : inner ℂ (ccmRestrictedWeilBoundedRemainder a f) u =
        inner ℂ f (ccmRestrictedWeilBoundedRemainder a u) :=
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric f u
    change inner ℂ ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • f +
      ccmRestrictedWeilBoundedRemainder a f) u =
      inner ℂ f ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • u +
        ccmRestrictedWeilBoundedRemainder a u)
    rw [inner_add_left, inner_add_right,
      inner_smul_left f u (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ),
      inner_smul_right f u (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ),
      Complex.conj_ofReal, hB]
  have hs : (inner ℂ (A f) u).re = (inner ℂ (A u) f).re := by
    rw [hsym, ← inner_conj_symm f (A u), Complex.conj_re]
  have h := ccmShiftedBoundedWeil_coercive a (f - u)
  change ‖f - u‖ ^ 2 ≤ (inner ℂ (A (f - u)) (f - u)).re at h
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
    Complex.sub_re, Complex.sub_re, Complex.sub_re, hs] at h
  nlinarith only [h, sq_nonneg ‖f - u‖]

theorem suzukiTa_energy_decomposition (a : SuzukiPositiveAperture) (w : SuzukiTaHilbert a) :
    let u := suzukiTaToFormCLM a w
    let f := ccmArchimedeanFormToAperture a u
    ‖w‖ ^ 2 = ‖u‖ ^ 2 + (inner ℂ (ccmShiftedBoundedWeil a f) f).re := by
  let u := suzukiTaToFormCLM a w
  let f := ccmArchimedeanFormToAperture a u
  have he := congrArg Complex.re (inner_suzukiTa_eq a w w)
  rw [suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm] at he
  change (inner ℂ w w).re =
    (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        inner ℂ (suzukiTaPhysicalEmbedding a w) (suzukiTaPhysicalEmbedding a w)).re at he
  have hphys : ‖suzukiTaPhysicalEmbedding a w‖ = ‖f‖ :=
    (suzukiApertureL2Equiv a).symm.norm_map f
  have hw : (inner ℂ w w).re = ‖w‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  have hu : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hv : (inner ℂ (suzukiTaPhysicalEmbedding a w)
      (suzukiTaPhysicalEmbedding a w)).re = ‖suzukiTaPhysicalEmbedding a w‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (suzukiTaPhysicalEmbedding a w)).symm
  simp only [Complex.add_re, Complex.re_ofReal_mul, hw, hu, hv, hphys] at he
  dsimp only
  rw [ccmShiftedBoundedWeil_re_inner]
  linarith only [he]

private theorem odd_source_pairing (a : SuzukiPositiveAperture) (z : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaRawCoalescingOdd a (1 / 2)) z =
      inner ℂ (ccmMatchedOddPoleSource a)
        (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)) := by
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  let e := suzukiApertureL2Equiv a
  have hp (s : ℝ) : e (suzukiTaExponentialL2 a s) = ccmPolarApertureVector a s := by
    apply Subtype.ext
    exact suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector a s
  have hs : (suzukiApertureCoordinate a.2.le).sinhVecC (1 / 2) =
      (1 / 2 : ℂ) • (suzukiTaExponentialL2 a (1 / 2) - suzukiTaExponentialL2 a (-1 / 2)) := by
    rw [suzukiTaExponentialL2_eq_cosh_add_sinh,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, suzukiTaExponentialL2_neg_eq_cosh_sub_sinh]
    module
  have hsource : e ((suzukiApertureCoordinate a.2.le).sinhVecC (1 / 2)) =
      ccmMatchedOddPoleSource a := by
    rw [hs, map_smul, map_sub, hp, hp]
    rfl
  have hf : f = e (suzukiTaPhysicalEmbedding a z) := by
    change f = e (e.symm f)
    rw [e.apply_symm_apply]
  change inner ℂ (suzukiTaRawCoalescingOdd a (1 / 2)) z = inner ℂ (ccmMatchedOddPoleSource a) f
  rw [← hsource, hf, e.inner_map_map, suzukiTaRawCoalescingOdd_inner]

private theorem odd_source_eq (a : SuzukiPositiveAperture) :
    let w := suzukiTaRawCoalescingOdd a (1 / 2)
    let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w)
    (inner ℂ (ccmMatchedOddPoleSource a) f).re = ‖w‖ ^ 2 := by
  dsimp only
  rw [← odd_source_pairing]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm

private theorem physical_odd_norm_le (a : SuzukiPositiveAperture) :
    let w := suzukiTaRawCoalescingOdd a (1 / 2)
    ‖ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w)‖ ≤ ‖w‖ := by
  have he := suzukiTa_energy_decomposition a (suzukiTaRawCoalescingOdd a (1 / 2))
  dsimp only at he ⊢
  have hc := ccmShiftedBoundedWeil_coercive a
    (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a (suzukiTaRawCoalescingOdd a (1 / 2))))
  nlinarith [sq_nonneg ‖suzukiTaToFormCLM a (suzukiTaRawCoalescingOdd a (1 / 2))‖,
    norm_nonneg (suzukiTaRawCoalescingOdd a (1 / 2))]

/-- Global source-only energy bound, also controlling all bounded aperture ranges. -/
theorem suzukiTaCoalescingOddEnergy_half_le_exp (a : SuzukiPositiveAperture) :
    suzukiTaCoalescingOddEnergy a (1 / 2) ≤ Real.exp a.1 := by
  let w := suzukiTaRawCoalescingOdd a (1 / 2)
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w)
  have hs : (inner ℂ (ccmMatchedOddPoleSource a) f).re = ‖w‖ ^ 2 := odd_source_eq a
  have hf : ‖f‖ ≤ ‖w‖ := physical_odd_norm_le a
  have hcs := re_inner_le_norm (𝕜 := ℂ) (ccmMatchedOddPoleSource a) f
  change (inner ℂ (ccmMatchedOddPoleSource a) f).re ≤ ‖ccmMatchedOddPoleSource a‖ * ‖f‖ at hcs
  have hpn := norm_nonneg (ccmMatchedOddPoleSource a)
  have hw := norm_nonneg w
  have hmul := mul_le_mul_of_nonneg_left hf hpn
  have hwp : ‖w‖ ≤ ‖ccmMatchedOddPoleSource a‖ := by nlinarith
  have hp := norm_ccmMatchedOddPoleSource_le a
  have he : (Real.exp (a.1 / 2)) ^ 2 = Real.exp a.1 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [suzukiTaCoalescingOddEnergy_eq_norm_sq]
  change ‖w‖ ^ 2 ≤ _
  nlinarith [Real.exp_pos (a.1 / 2)]

/-- The literal odd covariance energy at the matched pole anchor is bounded
uniformly over every positive aperture, with no source or response premise. -/
theorem exists_suzukiTaCoalescingOddEnergy_half_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : SuzukiPositiveAperture,
      suzukiTaCoalescingOddEnergy a (1 / 2) ≤ C := by
  obtain ⟨M, R, hM, hR, happ⟩ := eventually_ccmMatchedOddPoleSource_neumann_approximation
  let C := 8 * M ^ 2 + 4 * R ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hevent : ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      suzukiTaCoalescingOddEnergy ⟨a, ha⟩ (1 / 2) ≤ C := by
    filter_upwards [happ] with a happa
    intro ha
    let ap : SuzukiPositiveAperture := ⟨a, ha⟩
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder ap)
    let w := suzukiTaRawCoalescingOdd ap (1 / 2)
    let f := ccmArchimedeanFormToAperture ap (suzukiTaToFormCLM ap w)
    let p := ccmMatchedOddPoleSource ap
    obtain ⟨u, hu, hr⟩ := happa ha
    let r := p - ccmShiftedBoundedWeil ap u
    have hc : 0 < c := boundedPerturbedFormShift_pos _
    have hscale : Real.exp a / c ≤ 2 :=
      (div_le_iff₀ hc).2 (exp_aperture_le_twice_suzukiWeilIntervalShift ap)
    have he : (Real.exp (a / 2)) ^ 2 = Real.exp a := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have husq : ‖u‖ ^ 2 ≤ (M * Real.exp (a / 2) / c) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg u) hu
    have hquad : (inner ℂ (ccmShiftedBoundedWeil ap u) u).re ≤ 4 * M ^ 2 := by
      calc
        _ ≤ 2 * c * ‖u‖ ^ 2 := shifted_upper ap u
        _ ≤ 2 * c * (M * Real.exp (a / 2) / c) ^ 2 :=
          mul_le_mul_of_nonneg_left husq (by positivity)
        _ = (2 * M ^ 2) * (Real.exp a / c) := by
          rw [div_pow, mul_pow, he]
          field_simp
        _ ≤ (2 * M ^ 2) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = _ := by ring
    have henergy : ‖w‖ ^ 2 = ‖suzukiTaToFormCLM ap w‖ ^ 2 +
        (inner ℂ (ccmShiftedBoundedWeil ap f) f).re := suzukiTa_energy_decomposition ap w
    have hsource : (inner ℂ p f).re = ‖w‖ ^ 2 := odd_source_eq ap
    have hfnorm : ‖f‖ ≤ ‖w‖ := physical_odd_norm_le ap
    have hcross := shifted_cross ap f u
    have hsplit : (inner ℂ p f).re = (inner ℂ (ccmShiftedBoundedWeil ap u) f).re +
        (inner ℂ r f).re := by
      dsimp only [r]
      rw [inner_sub_left, Complex.sub_re]
      ring
    have hcs := re_inner_le_norm (𝕜 := ℂ) r f
    change (inner ℂ r f).re ≤ ‖r‖ * ‖f‖ at hcs
    have hproduct : ‖r‖ * ‖f‖ ≤ R * ‖w‖ :=
      mul_le_mul hr hfnorm (norm_nonneg f) hR.le
    rw [suzukiTaCoalescingOddEnergy_eq_norm_sq]
    change ‖w‖ ^ 2 ≤ C
    dsimp only [C]
    nlinarith only [henergy, hsource, hcross, hsplit, hcs, hproduct, hquad,
      sq_nonneg ‖suzukiTaToFormCLM ap w‖, sq_nonneg (‖w‖ - 2 * R)]
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.1 hevent
  refine ⟨C + Real.exp a₀ + 1, by positivity, ?_⟩
  intro ap
  by_cases ha : a₀ ≤ ap.1
  · have h := ha₀ ap.1 ha ap.2
    linarith [Real.exp_pos a₀]
  · have h := suzukiTaCoalescingOddEnergy_half_le_exp ap
    have hm := Real.exp_le_exp.mpr (le_of_not_ge ha)
    linarith

private theorem gamma_embedding_norm (a : SuzukiPositiveAperture)
    (g : CCMArchimedeanFormDomain a) : ‖ccmArchimedeanFormToAperture a g‖ ≤ ‖g‖ := by
  have hop : ‖ccmArchimedeanWeightedToL2‖ ≤ 1 := by
    unfold ccmArchimedeanWeightedToL2
    exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  change ‖fourierUnitary.symm (ccmArchimedeanWeightedToL2 g.1)‖ ≤ ‖g.1‖
  rw [fourierUnitary.symm.norm_map]
  exact (ccmArchimedeanWeightedToL2.le_opNorm g.1).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hop (norm_nonneg g.1))

private theorem fromForm_inner (a : SuzukiPositiveAperture)
    (g : CCMArchimedeanFormDomain a) (z : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaFromFormCLM a g) z =
      inner ℂ g (suzukiTaToFormCLM a z) +
        inner ℂ (ccmShiftedBoundedWeil a (ccmArchimedeanFormToAperture a g))
          (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)) := by
  let u := ccmArchimedeanFormToAperture a g
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  have hphys : inner ℂ (suzukiTaPhysicalEmbedding a (suzukiTaFromFormCLM a g))
      (suzukiTaPhysicalEmbedding a z) = inner ℂ u f :=
    (suzukiApertureL2Equiv a).symm.inner_map_map u f
  rw [inner_suzukiTa_eq, suzukiWeilIntervalForm_eq_ccmRestrictedWeilForm]
  change inner ℂ g (suzukiTaToFormCLM a z) +
      inner ℂ (ccmRestrictedWeilBoundedRemainder a u) f +
      (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) *
        inner ℂ (suzukiTaPhysicalEmbedding a (suzukiTaFromFormCLM a g))
          (suzukiTaPhysicalEmbedding a z) = _
  rw [hphys]
  change _ = inner ℂ g (suzukiTaToFormCLM a z) +
    inner ℂ ((boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ) • u +
      ccmRestrictedWeilBoundedRemainder a u) f
  rw [inner_add_left, inner_smul_left u f
    (boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) : ℂ), Complex.conj_ofReal]
  ring

/-- Exact source equation controls the Ta norm of the response-minus-test
vector, retaining both the physical residual and Gamma energy. -/
theorem suzukiTaMatchedOdd_form_residual_norm_le (a : SuzukiPositiveAperture)
    (g : CCMArchimedeanFormDomain a) :
    ‖suzukiTaRawCoalescingOdd a (1 / 2) - suzukiTaFromFormCLM a g‖ ≤
      ‖ccmMatchedOddPoleSource a -
        ccmShiftedBoundedWeil a (ccmArchimedeanFormToAperture a g)‖ + ‖g‖ := by
  let w := suzukiTaRawCoalescingOdd a (1 / 2)
  let z := w - suzukiTaFromFormCLM a g
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  let u := ccmArchimedeanFormToAperture a g
  let r := ccmMatchedOddPoleSource a - ccmShiftedBoundedWeil a u
  have heq : inner ℂ z z = inner ℂ r f - inner ℂ g (suzukiTaToFormCLM a z) := by
    calc
      _ = inner ℂ w z - inner ℂ (suzukiTaFromFormCLM a g) z := inner_sub_left _ _ _
      _ = _ := by
        rw [odd_source_pairing, fromForm_inner]
        dsimp only [r]
        rw [inner_sub_left]
        ring
  have hself : (inner ℂ z z).re = ‖z‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) z).symm
  have hres := congrArg Complex.re heq
  rw [hself, Complex.sub_re] at hres
  have he := suzukiTa_energy_decomposition a z
  have hc := ccmShiftedBoundedWeil_coercive a f
  change ‖z‖ ^ 2 = ‖suzukiTaToFormCLM a z‖ ^ 2 +
    (inner ℂ (ccmShiftedBoundedWeil a f) f).re at he
  have hf : ‖f‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖suzukiTaToFormCLM a z‖, norm_nonneg z]
  have ht : ‖suzukiTaToFormCLM a z‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖f‖, norm_nonneg z]
  have hr : (inner ℂ r f).re ≤ ‖r‖ * ‖f‖ := re_inner_le_norm (𝕜 := ℂ) r f
  have hg : -(inner ℂ g (suzukiTaToFormCLM a z)).re ≤
      ‖g‖ * ‖suzukiTaToFormCLM a z‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (-g) (suzukiTaToFormCLM a z)
    change (inner ℂ (-g) (suzukiTaToFormCLM a z)).re ≤ _ at h
    simpa only [inner_neg_left, Complex.neg_re, norm_neg] using h
  have hrf := mul_le_mul_of_nonneg_left hf (norm_nonneg r)
  have hgt := mul_le_mul_of_nonneg_left ht (norm_nonneg g)
  have hz : ‖z‖ ≤ ‖r‖ + ‖g‖ := by
    nlinarith only [hres, hr, hg, hrf, hgt, norm_nonneg z, norm_nonneg r, norm_nonneg g]
  exact hz

private theorem physical_odd_form_residual (a : SuzukiPositiveAperture)
    (g : CCMArchimedeanFormDomain a) :
    ‖suzukiTaPhysicalEmbedding a (suzukiTaRawCoalescingOdd a (1 / 2))‖ ^ 2 ≤
      2 * ‖ccmMatchedOddPoleSource a -
        ccmShiftedBoundedWeil a (ccmArchimedeanFormToAperture a g)‖ ^ 2 + 8 * ‖g‖ ^ 2 := by
  let w := suzukiTaRawCoalescingOdd a (1 / 2)
  let z := w - suzukiTaFromFormCLM a g
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a z)
  let u := ccmArchimedeanFormToAperture a g
  let r := ccmMatchedOddPoleSource a - ccmShiftedBoundedWeil a u
  have hz : ‖z‖ ≤ ‖r‖ + ‖g‖ := suzukiTaMatchedOdd_form_residual_norm_le a g
  have he := suzukiTa_energy_decomposition a z
  have hc := ccmShiftedBoundedWeil_coercive a f
  change ‖z‖ ^ 2 = ‖suzukiTaToFormCLM a z‖ ^ 2 +
    (inner ℂ (ccmShiftedBoundedWeil a f) f).re at he
  have hf : ‖f‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖suzukiTaToFormCLM a z‖, norm_nonneg z]
  have hsplit : ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w) = f + u := by
    dsimp only [f, z, u]
    rw [map_sub, suzukiTaToFormCLM_fromForm, map_sub, sub_add_cancel]
  have hphys : ‖suzukiTaPhysicalEmbedding a w‖ =
      ‖ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a w)‖ :=
    (suzukiApertureL2Equiv a).symm.norm_map _
  have hbound : ‖suzukiTaPhysicalEmbedding a w‖ ≤ ‖r‖ + 2 * ‖g‖ := by
    rw [hphys, hsplit]
    have hu : ‖u‖ ≤ ‖g‖ := gamma_embedding_norm a g
    exact (norm_add_le f u).trans (by linarith)
  change ‖suzukiTaPhysicalEmbedding a w‖ ^ 2 ≤ 2 * ‖r‖ ^ 2 + 8 * ‖g‖ ^ 2
  have hs : ‖suzukiTaPhysicalEmbedding a w‖ ^ 2 ≤ (‖r‖ + 2 * ‖g‖) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hbound
  nlinarith only [hs, sq_nonneg (‖r‖ - 2 * ‖g‖)]

/-- The literal matched odd Riesz response has vanishing physical mass.
Both the Gamma lift and its residual are constructed from the actual source. -/
theorem eventually_suzukiTaMatchedOdd_physical_mass_decay :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ a : ℝ in atTop, ∀ ha : 0 < a,
      ‖suzukiTaPhysicalEmbedding ⟨a, ha⟩ (suzukiTaRawCoalescingOdd ⟨a, ha⟩ (1 / 2))‖ ^ 2 ≤
        C * a * Real.exp (-a) := by
  obtain ⟨D, E, hD, hE, h⟩ := eventually_ccmMatchedOddNeumannVector_form_decay
  refine ⟨2 * E ^ 2 + 8 * D, by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with a haForm haOne
  intro ha
  obtain ⟨g, _, hg, hr⟩ := haForm ha
  let r := ccmMatchedOddPoleSource ⟨a, ha⟩ -
    ccmShiftedBoundedWeil ⟨a, ha⟩ (ccmArchimedeanFormToAperture ⟨a, ha⟩ g)
  have hr2 : ‖r‖ ^ 2 ≤ E ^ 2 * a * Real.exp (-a) := by
    have hs : ‖r‖ ^ 2 ≤ (E * Real.exp (-7 * a / 2)) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg r) hr
    have he : (Real.exp (-7 * a / 2)) ^ 2 = Real.exp (-7 * a) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ E ^ 2 * Real.exp (-7 * a) := hs.trans_eq (by rw [mul_pow, he])
      _ ≤ E ^ 2 * Real.exp (-a) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg E)
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left haOne
          (mul_nonneg (sq_nonneg E) (Real.exp_pos (-a)).le)
        nlinarith only [hm]
  have hb := physical_odd_form_residual ⟨a, ha⟩ g
  change _ ≤ 2 * ‖r‖ ^ 2 + 8 * ‖g‖ ^ 2 at hb
  nlinarith only [hb, hr2, hg]

end RHTower
end
