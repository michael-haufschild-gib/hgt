import GaloisForLFunctions.RHTower.CCMParityTopLayerOddTest

/-!
# The odd floor of the restricted Weil form under a finite top layer

**Theorem** (`sourceQuadratic_ge_of_isOdd`). Under `FiniteTopLayer δ t`, at every aperture `a`,
every reflection-odd vector `u` of the CCM form domain satisfies

`Q_a(u) ≥ −(e^{2δa}(Λ(a)/2 + (3/(2δ)) e^{−δa} Σ_j M_j) + L(a)) ‖J u‖²`,

where `Λ(a) = max(λ_max(T(θ(a))), 0)` at the aperture phases `θ_j(a) = −2t_j a`.

**Proof.** For an odd source the top quartets contribute `−M_j(Re û₁(−σ_j)² + Re û₂(−σ_j)²)`
(`re_zeroSumTerm_parity`), i.e. `−e^{2δa}(T(θ)[u₁(a − ·)] + T(θ)[u₂(a − ·)])`. The projection onto
the Cauchy span gives `T(θ)[v] ≤ max(λ_max(θ), 0) ∫ v²` (`halfLineForm_le`). Since `u_k²` is even,
the near half of the reflected source carries half the mass and the far half costs `O(e^{−δa})`
(`halfLineForm_reflect_le_of_sq_even`). Lower copies and real points are handled as for the even
floor, and the odd symmetrization extends the bound by density (`floor_of_isOdd_of_smooth`).
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## The upper projection bound and the halving for even squares -/

/-- **The odd-sector bound of the model:** `T(θ)[v] ≤ max(λ_max(θ), 0) ∫_0^∞ v²`. -/
theorem halfLineForm_le {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    halfLineForm δ t M θ v ≤ max (ccmLambdaMax δ t M θ) 0 * ∫ s in Ioi (0 : ℝ), v s ^ 2 := by
  obtain ⟨x, hpair, hnorm⟩ := exists_realProfile_projection hδ ht htpos hv
  rw [← halfLineForm_congr M θ hpair, ← quadForm_eq_halfLineForm hδ]
  have h1 := quadForm_le_lambdaMax_mul hδ ht htpos hm M θ x
  have hn0 := normForm_nonneg hδ t x
  calc quadForm δ t M θ x ≤ ccmLambdaMax δ t M θ * normForm δ t x := h1
    _ ≤ max (ccmLambdaMax δ t M θ) 0 * normForm δ t x :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hn0
    _ ≤ max (ccmLambdaMax δ t M θ) 0 * ∫ s in Ioi (0 : ℝ), v s ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm (le_max_right _ _)

theorem integral_sq_eq_two_mul_Ioi_of_sq_even {g : ℝ → ℝ} (hg : MemLp g 2)
    (hsq : ∀ x, g (-x) ^ 2 = g x ^ 2) :
    ∫ x, g x ^ 2 = 2 * ∫ x in Ioi (0 : ℝ), g x ^ 2 := by
  have hint : Integrable fun x => g x ^ 2 := hg.integrable_sq
  rw [← integral_add_compl measurableSet_Ioi hint, compl_Ioi]
  have h := integral_comp_neg_Iic (0 : ℝ) (fun x => g x ^ 2)
  simp only [hsq, neg_zero] at h
  rw [h]
  ring

/-- **The odd floor of the reflected form.** -/
theorem halfLineForm_reflect_le_of_sq_even {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : RealIntervalSource a g)
    (hsq : ∀ x, g (-x) ^ 2 = g x ^ 2) :
    halfLineForm δ t M θ (fun s => g (a - s)) ≤
      (max (ccmLambdaMax δ t M θ) 0 / 2 +
        3 / (2 * δ) * Real.exp (-(δ * a)) * ∑ j, |M j|) * ∫ x, g x ^ 2 := by
  set N := ∫ x, g x ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  set v : ℝ → ℝ := fun s => g (a - s) with hv
  set vn : ℝ → ℝ := (Iic a).indicator v with hvn
  set vf : ℝ → ℝ := (Ioi a).indicator v with hvf
  have hvm : MemLp v 2 (volume.restrict (Ioi 0)) := hg.memLp_reflect
  have hvnm : MemLp vn 2 (volume.restrict (Ioi 0)) := hvm.indicator measurableSet_Iic
  have hvfm : MemLp vf 2 (volume.restrict (Ioi 0)) := hvm.indicator measurableSet_Ioi
  have hsum : vn + vf = v := by
    funext s
    simp only [Pi.add_apply, hvn, hvf]
    rw [← compl_Iic]
    exact indicator_self_add_compl_apply _ _ _
  have hNn : ∫ s in Ioi (0 : ℝ), vn s ^ 2 = N / 2 := by
    rw [integral_sq_reflect_Iic hg, hN, integral_sq_eq_two_mul_Ioi_of_sq_even hg.memLp hsq]
    ring
  have hNf : ∫ s in Ioi (0 : ℝ), vf s ^ 2 ≤ N := by
    rw [hN, ← integral_sq_reflect hg]
    refine setIntegral_mono_on hvfm.integrable_sq hvm.integrable_sq measurableSet_Ioi
      fun s _ => ?_
    simp only [hvf]
    by_cases hs : s ∈ Ioi a
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
  have hPn : ∀ j, ‖halfLinePairing δ t vn j‖ ^ 2 ≤ N * (1 / (2 * δ)) := by
    intro j
    refine (norm_halfLinePairing_sq_le hδ t hvnm j).trans ?_
    rw [hNn]
    have : 0 ≤ 1 / (2 * δ) := by positivity
    nlinarith
  have hPf : ∀ j, ‖halfLinePairing δ t vf j‖ ^ 2 ≤ N * (Real.exp (-(2 * δ) * a) / (2 * δ)) := by
    intro j
    refine (norm_halfLinePairing_sq_le_of_vanish hδ t hvfm ha (fun s hs => ?_) j).trans ?_
    · simp only [hvf]
      rw [indicator_of_notMem (show s ∉ Ioi a by simp only [mem_Ioi, not_lt]; exact hs.2)]
    · exact mul_le_mul_of_nonneg_right hNf (by positivity)
  have hnear := halfLineForm_le hδ ht htpos hm M θ hvnm
  rw [hNn] at hnear
  have hpert := abs_halfLineForm_add_sub_le hδ t M θ hvnm hvfm
  rw [hsum] at hpert
  set E := Real.exp (-(δ * a)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hE2 : Real.exp (-(2 * δ) * a) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hterm : ∀ j, ‖halfLinePairing δ t vf j‖ *
      (2 * ‖halfLinePairing δ t vn j‖ + ‖halfLinePairing δ t vf j‖) ≤ 3 / (2 * δ) * E * N := by
    intro j
    set x := ‖halfLinePairing δ t vf j‖
    set y := ‖halfLinePairing δ t vn j‖
    have hx := hPf j
    have hy := hPn j
    rw [hE2] at hx
    have hx0 : 0 ≤ x := norm_nonneg _
    have hy0 : 0 ≤ y := norm_nonneg _
    have hamgm : 2 * x * y ≤ x ^ 2 / E + E * y ^ 2 := by
      rw [div_add' _ _ _ hE0.ne', le_div_iff₀ hE0]
      nlinarith [sq_nonneg (x - E * y)]
    have h1 : x ^ 2 / E ≤ N * (1 / (2 * δ)) * E := by
      rw [div_le_iff₀ hE0]
      calc x ^ 2 ≤ N * (E ^ 2 / (2 * δ)) := hx
        _ = N * (1 / (2 * δ)) * E * E := by ring
    have h2 : E * y ^ 2 ≤ E * (N * (1 / (2 * δ))) := mul_le_mul_of_nonneg_left hy hE0.le
    have h3 : x ^ 2 ≤ N * (1 / (2 * δ)) * E := by
      calc x ^ 2 ≤ N * (E ^ 2 / (2 * δ)) := hx
        _ = N * (1 / (2 * δ)) * E * E := by ring
        _ ≤ N * (1 / (2 * δ)) * E * 1 := by
          apply mul_le_mul_of_nonneg_left hE1; positivity
        _ = N * (1 / (2 * δ)) * E := mul_one _
    calc x * (2 * y + x) = 2 * x * y + x ^ 2 := by ring
      _ ≤ (N * (1 / (2 * δ)) * E + E * (N * (1 / (2 * δ)))) + N * (1 / (2 * δ)) * E := by
        linarith
      _ = 3 / (2 * δ) * E * N := by ring
  have hpert' : |halfLineForm δ t M θ v - halfLineForm δ t M θ vn| ≤
      3 / (2 * δ) * E * (∑ j, |M j|) * N := by
    refine hpert.trans ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_le_mul_of_nonneg_left (hterm j) (abs_nonneg (M j))
    linarith
  rw [abs_le] at hpert'
  nlinarith [hpert'.2]

/-! ## Odd symmetrization of smooth sources and the domain extension -/

/-- The odd symmetrization `x ↦ (u(x) − u(−x))/2` of a smooth interior source. -/
def oddSymSource {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    CCMComplexSmoothInteriorSource a where
  toFun x := (2 : ℂ)⁻¹ * (u x - u (-x))
  smooth := contDiff_const.mul (u.smooth.sub (u.smooth.comp contDiff_neg))
  hasCompactSupport := by
    have hK2 : IsCompact ((fun x : ℝ => -x) ⁻¹' tsupport (u : ℝ → ℂ)) :=
      (Homeomorph.neg ℝ).isCompact_preimage.mpr u.hasCompactSupport.isCompact
    refine HasCompactSupport.of_support_subset_isCompact
      (u.hasCompactSupport.isCompact.union hK2) ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hK
    simp only [Set.mem_union, Set.mem_preimage, not_or] at hK
    have h1 : u x = 0 := image_eq_zero_of_notMem_tsupport hK.1
    have h2 : u (-x) = 0 := image_eq_zero_of_notMem_tsupport hK.2
    exact hx (by rw [h1, h2]; simp)
  tsupport_subset := by
    have hclosed : IsClosed (tsupport (u : ℝ → ℂ) ∪ (fun x : ℝ => -x) ⁻¹' tsupport (u : ℝ → ℂ)) :=
      (isClosed_tsupport _).union ((isClosed_tsupport _).preimage continuous_neg)
    have hsupp : Function.support (fun x => (2 : ℂ)⁻¹ * (u x - u (-x))) ⊆
        tsupport (u : ℝ → ℂ) ∪ (fun x : ℝ => -x) ⁻¹' tsupport (u : ℝ → ℂ) := by
      intro x hx
      rw [Function.mem_support] at hx
      by_contra hK
      simp only [Set.mem_union, Set.mem_preimage, not_or] at hK
      have h1 : u x = 0 := image_eq_zero_of_notMem_tsupport hK.1
      have h2 : u (-x) = 0 := image_eq_zero_of_notMem_tsupport hK.2
      exact hx (by rw [h1, h2]; simp)
    refine (closure_minimal hsupp hclosed).trans ?_
    rintro x (hx | hx)
    · exact u.tsupport_subset hx
    · have h := u.tsupport_subset hx
      simp only [Set.mem_Ioo] at h ⊢
      constructor <;> linarith [h.1, h.2]

theorem oddSymSource_apply {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : (oddSymSource u : ℝ → ℂ) x = (2 : ℂ)⁻¹ * (u x - u (-x)) := rfl

theorem oddSymSource_odd {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : (oddSymSource u : ℝ → ℂ) (-x) = -(oddSymSource u : ℝ → ℂ) x := by
  rw [oddSymSource_apply, oddSymSource_apply, neg_neg]
  ring

/-- The odd part of a smooth source vector is the vector of its odd symmetrization. -/
theorem oddPart_toCCMFormVector {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilOddPart a u.toCCMFormVector = (oddSymSource u).toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective a
  apply Subtype.ext
  set F : SoninL2 := (ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) with hF_def
  have hlin : ((ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a u.toCCMFormVector) :
      suzukiApertureHilbert a) : SoninL2) = (2 : ℂ)⁻¹ • (F - l2Reflection F) := by
    rw [ccmRestrictedWeilOddPart, map_smul, map_sub]
    change (2 : ℂ)⁻¹ • ((F : SoninL2) - ((ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormReflection a u.toCCMFormVector) : suzukiApertureHilbert a) : SoninL2)) = _
    rw [ccmArchimedeanFormToAperture_reflection]
  rw [hlin]
  apply Lp.ext
  have hF : (F : ℝ → ℂ) =ᵐ[volume] u := u.toCCMFormVector_physical_coeFn
  have hFneg : (fun x => (F : ℝ → ℂ) (-x)) =ᵐ[volume] fun x => (u : ℝ → ℂ) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hF
  have hR : ((l2Reflection F : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun x => (F : ℝ → ℂ) (-x) :=
    Lp.coeFn_compMeasurePreserving F (Measure.measurePreserving_neg (volume : Measure ℝ))
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (F - l2Reflection F), Lp.coeFn_sub F (l2Reflection F),
    hR, hF, hFneg, (oddSymSource u).toCCMFormVector_physical_coeFn] with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, h5, smul_eq_mul]
  exact h6.symm

/-- **Domain extension.** An odd floor on smooth sources holds on every odd form vector. -/
theorem floor_of_isOdd_of_smooth {a : SuzukiPositiveAperture} {c : ℝ}
    (hsm : ∀ u : CCMComplexSmoothInteriorSource a, (∀ x, u (-x) = -u x) →
      c * ∫ x, ‖u x‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector)
    (w : CCMArchimedeanFormDomain a) (hw : ccmArchimedeanFormReflection a w = -w) :
    c * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a w := by
  have hcontO : Continuous (ccmRestrictedWeilOddPart a) := by
    unfold ccmRestrictedWeilOddPart
    exact (continuous_id.sub (ccmArchimedeanFormReflection a).continuous).const_smul ((2 : ℂ)⁻¹)
  have key : ∀ v : CCMArchimedeanFormDomain a,
      c * ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilOddPart a v)‖ ^ 2 ≤
        ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilOddPart a v) := by
    intro v
    refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on v ?_ ?_
    · exact isClosed_le
        (continuous_const.mul
          (((ccmArchimedeanFormToAperture a).continuous.comp hcontO).norm.pow 2))
        ((continuous_ccmRestrictedWeilSourceQuadratic a).comp hcontO)
    · intro u
      rw [oddPart_toCCMFormVector, norm_sq_toAperture_toCCMFormVector]
      exact hsm _ (oddSymSource_odd u)
  have hodd : ccmRestrictedWeilOddPart a w = w := by
    rw [ccmRestrictedWeilOddPart, hw, sub_neg_eq_add, ← two_smul ℂ w, smul_smul]
    norm_num
  have := key w
  rwa [hodd] at this

/-! ## The odd floor -/

/-- The odd floor constant `−(e^{2δa}(Λ(a)/2 + (3/(2δ)) e^{−δa} Σ_j M_j) + L(a))`. -/
def oddFloorConst {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (a : ℝ) : ℝ :=
  -(Real.exp (2 * δ * a) *
      (max (ccmLambdaMax δ t h.mult (aperturePhase t a)) 0 / 2 +
        3 / (2 * δ) * Real.exp (-(δ * a)) * ∑ j, |h.mult j|) + h.lowWeight a)

/-- **The odd floor on smooth sources.** -/
theorem sourceQuadratic_ge_of_smooth_odd {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (hodd : ∀ x, u (-x) = -u x) :
    oddFloorConst h a.1 * ∫ x, ‖u x‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  classical
  have ha : 0 ≤ a.1 := a.2.le
  have hδ := h.pos
  have hI := smoothSource_intervalSource u
  set N : ℝ := ∫ x, ‖u x‖ ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => by positivity
  set T : XiZeroCopy → ℂ := fun q => zeroSumTerm u (xiSpectralPoint q) with hT
  have hsumm : Summable T := summable_zeroSumTerm u
  have hsumm_re : Summable fun q => (T q).re := Complex.reCLM.summable hsumm
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum hsumm]
  set g : XiZeroCopy → ℝ := fun q => if q ∈ h.offLine then (T q).re else 0 with hg
  have hgle : ∀ q, g q ≤ (T q).re := by
    intro q
    simp only [hg]
    split_ifs with hq
    · exact le_rfl
    · have him : (xiSpectralPoint q).im = 0 := by
        by_contra hne
        exact hq (h.mem_offLine.mpr hne)
      exact re_zeroSumTerm_nonneg_of_im_eq_zero _ him
  have hgsupp : ∀ q ∉ h.offLine, g q = 0 := fun q hq => by simp [hg, hq]
  have hgsum : Summable g := summable_of_ne_finset_zero hgsupp
  have htsum_g : ∑' q, g q = ∑ q ∈ h.offLine, (T q).re := by
    rw [tsum_eq_sum hgsupp]
    exact Finset.sum_congr rfl fun q hq => by simp [hg, hq]
  have hmain : ∑ q ∈ h.offLine, (T q).re ≤ ∑' q, (T q).re :=
    htsum_g ▸ hgsum.tsum_le_tsum hgle hsumm_re
  refine le_trans ?_ hmain
  rw [h.sum_offLine_eq]
  set u₁ : ℝ → ℝ := fun x => (u x).re with hu₁
  set u₂ : ℝ → ℝ := fun x => (u x).im with hu₂
  have h₁ : RealIntervalSource a.1 u₁ := smoothSource_re_realIntervalSource u
  have h₂ : RealIntervalSource a.1 u₂ := smoothSource_im_realIntervalSource u
  have hpar : ∀ x, u (-x) = ((-1 : ℝ) : ℂ) * u x := fun x => by rw [hodd x]; push_cast; ring
  have hpar' : ∀ x, u (-x) = (-1 : ℂ) * u x := fun x => by rw [hodd x]; ring
  have hs₁ : ∀ x, u₁ (-x) ^ 2 = u₁ x ^ 2 := fun x => by
    simp only [hu₁, hodd x, Complex.neg_re, neg_sq]
  have hs₂ : ∀ x, u₂ (-x) ^ 2 = u₂ x ^ 2 := fun x => by
    simp only [hu₂, hodd x, Complex.neg_im, neg_sq]
  have htopj : ∀ j, ∑ q ∈ h.topSet j, (T q).re =
      -(h.mult j * (((testTransform (fun x => (u₁ x : ℂ)) (-topPoint δ t j)) ^ 2).re +
        ((testTransform (fun x => (u₂ x : ℂ)) (-topPoint δ t j)) ^ 2).re)) := by
    intro j
    have hq : ∀ q ∈ h.topSet j, (T q).re = (zeroSumTerm u (topPoint δ t j)).re := by
      intro q hq
      simp only [FiniteTopLayer.topSet, Finset.mem_filter] at hq
      have hs1 : (-1 : ℂ) * (starRingEnd ℂ) (-1) = 1 := by simp
      rw [hT, re_zeroSumTerm_quartet hpar' hs1 _ hq.2,
        re_zeroSumTerm_quartet hpar' hs1 _ (Or.inl rfl)]
    rw [Finset.sum_congr rfl hq, Finset.sum_const, nsmul_eq_mul,
      re_zeroSumTerm_parity (Or.inr rfl) hpar h₁ h₂]
    simp only [FiniteTopLayer.mult, hu₁, hu₂]
    ring
  have htop : ∑ j, ∑ q ∈ h.topSet j, (T q).re =
      -(Real.exp (2 * δ * a.1) *
        (halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => u₁ (a.1 - s)) +
          halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => u₂ (a.1 - s)))) := by
    simp_rw [htopj, mul_add, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    have e₁ := sum_re_testTransform_sq_eq h₁ δ t h.mult
    have e₂ := sum_re_testTransform_sq_eq h₂ δ t h.mult
    simp only [topPoint]
    rw [e₁, e₂]
    unfold aperturePhase
    ring
  set Λo := max (ccmLambdaMax δ t h.mult (aperturePhase t a.1)) 0 with hΛo
  set C := 3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j| with hC
  have hf₁ := halfLineForm_reflect_le_of_sq_even hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1) ha h₁ hs₁
  have hf₂ := halfLineForm_reflect_le_of_sq_even hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1) ha h₂ hs₂
  have hNsplit : N = (∫ x, u₁ x ^ 2) + ∫ x, u₂ x ^ 2 := integral_norm_sq_eq_re_add_im u
  have htopge : -(Real.exp (2 * δ * a.1) * (Λo / 2 + C) * N) ≤
      ∑ j, ∑ q ∈ h.topSet j, (T q).re := by
    rw [htop, hNsplit]
    have hE : 0 < Real.exp (2 * δ * a.1) := Real.exp_pos _
    have := add_le_add hf₁ hf₂
    nlinarith
  have hlow : ∀ q ∈ h.lowSet,
      -(N * (2 * a.1 * Real.exp (2 * a.1 * |(xiSpectralPoint q).im|))) ≤ (T q).re := by
    intro q _
    set X := N * (2 * a.1 * Real.exp (2 * a.1 * |(xiSpectralPoint q).im|)) with hX
    have h1 := norm_testTransform_sq_le ha hI (-xiSpectralPoint q)
    have h2 := norm_testTransform_sq_le ha hI (-(starRingEnd ℂ) (xiSpectralPoint q))
    simp only [Complex.neg_im, Complex.conj_im, neg_neg, abs_neg] at h1 h2
    have hnorm : ‖T q‖ ≤ X := by
      simp only [hT, zeroSumTerm, norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg (testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)),
        norm_nonneg (testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))),
        sq_nonneg (‖testTransform (u : ℝ → ℂ) (-xiSpectralPoint q)‖ -
          ‖testTransform (u : ℝ → ℂ) (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
    have := Complex.abs_re_le_norm (T q)
    rw [abs_le] at this
    linarith [this.1]
  have hlowsum : -(N * h.lowWeight a.1) ≤ ∑ q ∈ h.lowSet, (T q).re := by
    rw [FiniteTopLayer.lowWeight, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hlow
  unfold oddFloorConst
  rw [← hΛo, ← hC]
  nlinarith

/-- **The odd floor.** -/
theorem sourceQuadratic_ge_of_isOdd {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (w : CCMArchimedeanFormDomain a)
    (hw : ccmArchimedeanFormReflection a w = -w) :
    oddFloorConst h a.1 * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a w :=
  floor_of_isOdd_of_smooth (fun u hu => sourceQuadratic_ge_of_smooth_odd h u hu) w hw

end

end RHTower.CCMParityTopLayer
