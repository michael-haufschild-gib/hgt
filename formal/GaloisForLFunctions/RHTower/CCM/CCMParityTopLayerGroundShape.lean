import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerGroundEnergyLaw

/-!
# Near-ground sources of the restricted Weil form are edge profiles of the Cauchy model

Under `FiniteTopLayer δ t`, let `u` be a smooth interior source of pure parity at aperture `a`
whose Rayleigh quotient is within `ε e^{2δa}/2` of `−(e^{2δa}/2) Λ*(a)`, the asymptotic ground
energy (`groundEnergy_law`). Write `v_k(s) = u_k(a − s)` (`u₁, u₂` the real and imaginary parts) and
`v_k^near = v_k · 1_{(0,a]}` (the half `x ≥ 0` of the source, read from the edge `x = a`).

**Theorem** (`exists_edgeProfile_of_nearGround`). For every small `ε > 0` and all large apertures,
each `v_k^near` lies within `L²`-distance `√(2ε/c₀)‖u‖` of the real span of the edge profiles
`e^{−(δ ∓ it_j)s}`: there are coefficients `x₁, x₂` with

`Σ_k ∫_0^∞ (v_k^near − 2 Re Σ_j x_{k,j} e^{−(δ − it_j)s})² ≤ (2ε/c₀) ∫ |u|²`.

So near-ground states, in particular ground states approximated by smooth sources, are
asymptotically combinations of the exponentials `e^{−(δ ∓ it_j)(a − |x|)}` concentrated in an edge
layer of width `O(1/δ)`: the restricted Weil ground state carries the top layer `t_j + iδ` as its
shape, not only as its energy.

**Proof.** The projection onto the Cauchy span has residual `∫(v − P)² = ∫v² − ∫P²`
(`exists_realProfile_projection_residual`). In the floor argument the top form is then bounded by
`max(λ, 0)(∫ v_near² − residual)`, so an energy within `ε` of the floor forces the residual to be
`O(ε)`; the sector's spectral top is within `2ε` of `Λ* ≥ c₀`.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## Projection with residual -/

/-- **Projection with residual.** The projection `P` of a real `v ∈ L²(0, ∞)` onto the Cauchy span
has `∫(v − P)² = ∫ v² − ∫ P²`. -/
theorem exists_realProfile_projection_residual {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi 0))) :
    ∃ x : Fin m → ℂ, (∀ j, halfLinePairing δ t (realProfile δ t x) j = halfLinePairing δ t v j) ∧
      ∫ s in Ioi (0 : ℝ), (v s - realProfile δ t x s) ^ 2 =
        (∫ s in Ioi (0 : ℝ), v s ^ 2) - normForm δ t x := by
  obtain ⟨x, hx⟩ := exists_realLift_cauchyGram_mulVec_eq hδ ht htpos (isRealVec_nodeMoment δ t v)
  have hmom : nodeMoment δ t (realProfile δ t x) = nodeMoment δ t v := by
    rw [← cauchyGram_mulVec_realLift hδ, hx]
  refine ⟨x, fun j => congr_fun hmom (Sum.inl j), ?_⟩
  set P := realProfile δ t x with hP
  have hvP : normForm δ t x = ∫ s in Ioi (0 : ℝ), v s * P s := by
    unfold normForm
    rw [hx]
    simp only [dotProduct, nodeMoment]
    have hint : ∀ l, IntegrableOn (fun s : ℝ => realLift x l *
        ((v s : ℂ) * Complex.exp (-ccmNodes δ t l * s))) (Ioi 0) :=
      fun l => (integrableOn_mul_exp_neg hv (ccmNodes_re_pos hδ t l)).const_mul _
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun l _ => hint l]
    have hfun : ∀ s : ℝ, ∑ l, realLift x l * ((v s : ℂ) * Complex.exp (-ccmNodes δ t l * s)) =
        ((v s * P s : ℝ) : ℂ) := by
      intro s
      have := nodeProfile_realLift δ t x s
      unfold nodeProfile at this
      rw [Complex.ofReal_mul, ← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    simp_rw [hfun]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have hPP : normForm δ t x = ∫ s in Ioi (0 : ℝ), P s ^ 2 := normForm_eq_integral hδ t x
  have hPm := memLp_realProfile hδ t x
  have hint_vP : IntegrableOn (fun s => v s * P s) (Ioi 0) := hv.integrable_mul hPm
  have hint_v2 : IntegrableOn (fun s => v s ^ 2) (Ioi 0) := hv.integrable_sq
  have hint_P2 : IntegrableOn (fun s => P s ^ 2) (Ioi 0) := hPm.integrable_sq
  have hexp : (fun s => (v s - P s) ^ 2) = fun s => (v s ^ 2 + P s ^ 2) - 2 * (v s * P s) := by
    funext s; ring
  have hI1 : IntegrableOn (fun s => v s ^ 2 + P s ^ 2) (Ioi 0) := hint_v2.add hint_P2
  have hI2 : IntegrableOn (fun s => 2 * (v s * P s)) (Ioi 0) := hint_vP.const_mul 2
  rw [hexp, integral_sub hI1 hI2, integral_add hint_v2 hint_P2, integral_const_mul, ← hvP, ← hPP]
  ring

/-! ## Refined halving -/

theorem halfLineForm_reflect_near_bounds {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (M θ : Fin m → ℝ)
    {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ} (hg : RealIntervalSource a g)
    (hsq : ∀ x, g (-x) ^ 2 = g x ^ 2) :
    ∃ x : Fin m → ℂ,
      (∫ s in Ioi (0 : ℝ), ((Iic a).indicator (fun s => g (a - s)) s - realProfile δ t x s) ^ 2 =
        (∫ x, g x ^ 2) / 2 - normForm δ t x) ∧
      |halfLineForm δ t M θ (fun s => g (a - s)) - quadForm δ t M θ x| ≤
        3 / (2 * δ) * Real.exp (-(δ * a)) * (∑ j, |M j|) * ∫ x, g x ^ 2 := by
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
  obtain ⟨x, hpair, hres⟩ := exists_realProfile_projection_residual hδ ht htpos hvnm
  refine ⟨x, by rw [hres, hNn], ?_⟩
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
  have hq : halfLineForm δ t M θ vn = quadForm δ t M θ x := by
    rw [quadForm_eq_halfLineForm hδ]
    exact halfLineForm_congr M θ fun j => (hpair j).symm
  have hpert := abs_halfLineForm_add_sub_le hδ t M θ hvnm hvfm
  rw [hsum, hq] at hpert
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
  refine hpert.trans ?_
  rw [show 3 / (2 * δ) * E * (∑ j, |M j|) * N = ∑ j, |M j| * (3 / (2 * δ) * E * N) by
    rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hterm j) (abs_nonneg _)

/-! ## The top form bounds the source quadratic -/

theorem topForm_sub_le_sourceQuadratic_of_even {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (heven : ∀ x, u (-x) = u x) :
    Real.exp (2 * δ * a.1) *
        (halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => (u (a.1 - s)).re) +
          halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => (u (a.1 - s)).im)) -
      (∫ x, ‖u x‖ ^ 2) * h.lowWeight a.1 ≤
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
  -- the top layer
  set u₁ : ℝ → ℝ := fun x => (u x).re with hu₁
  set u₂ : ℝ → ℝ := fun x => (u x).im with hu₂
  have h₁ : RealIntervalSource a.1 u₁ := smoothSource_re_realIntervalSource u
  have h₂ : RealIntervalSource a.1 u₂ := smoothSource_im_realIntervalSource u
  have hpar : ∀ x, u (-x) = ((1 : ℝ) : ℂ) * u x := fun x => by rw [heven x]; simp
  have he₁ : ∀ x, u₁ (-x) = u₁ x := fun x => by simp only [hu₁, heven x]
  have he₂ : ∀ x, u₂ (-x) = u₂ x := fun x => by simp only [hu₂, heven x]
  have htopj : ∀ j, ∑ q ∈ h.topSet j, (T q).re =
      h.mult j * (((testTransform (fun x => (u₁ x : ℂ)) (-topPoint δ t j)) ^ 2).re +
        ((testTransform (fun x => (u₂ x : ℂ)) (-topPoint δ t j)) ^ 2).re) := by
    intro j
    have hq : ∀ q ∈ h.topSet j, (T q).re = (zeroSumTerm u (topPoint δ t j)).re := by
      intro q hq
      simp only [FiniteTopLayer.topSet, Finset.mem_filter] at hq
      have hs1 : (1 : ℂ) * (starRingEnd ℂ) 1 = 1 := by simp
      rw [hT, re_zeroSumTerm_quartet (s := 1) (by simpa using heven) hs1 _ hq.2,
        re_zeroSumTerm_quartet (s := 1) (by simpa using heven) hs1 _ (Or.inl rfl)]
    rw [Finset.sum_congr rfl hq, Finset.sum_const, nsmul_eq_mul,
      re_zeroSumTerm_parity (Or.inl rfl) hpar h₁ h₂]
    simp only [FiniteTopLayer.mult, one_mul]
    rfl
  have htop : ∑ j, ∑ q ∈ h.topSet j, (T q).re =
      Real.exp (2 * δ * a.1) *
        (halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => u₁ (a.1 - s)) +
          halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => u₂ (a.1 - s))) := by
    simp_rw [htopj, mul_add, Finset.sum_add_distrib]
    have e₁ := sum_re_testTransform_sq_eq h₁ δ t h.mult
    have e₂ := sum_re_testTransform_sq_eq h₂ δ t h.mult
    simp only [topPoint]
    rw [e₁, e₂]
    unfold aperturePhase
    ring
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
  have := htop
  linarith [hlowsum]

theorem negTopForm_sub_le_sourceQuadratic_of_odd {δ : ℝ} {t : Fin m → ℝ}
    (h : FiniteTopLayer δ t) {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (hodd : ∀ x, u (-x) = -u x) :
    -(Real.exp (2 * δ * a.1) *
        (halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => (u (a.1 - s)).re) +
          halfLineForm δ t h.mult (aperturePhase t a.1) (fun s => (u (a.1 - s)).im))) -
      (∫ x, ‖u x‖ ^ 2) * h.lowWeight a.1 ≤
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
  have := htop
  linarith [hlowsum]


/-! ## Near-ground sources are edge profiles -/

theorem quadForm_ge_neg_mul_of_unit {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    (x : Fin m → ℂ) :
    -(max (ccmLambdaMax δ t M (halfTurn θ)) 0 * normForm δ t x) ≤ quadForm δ t M θ x := by
  have h1 := lambdaMax_halfTurn_mul_ge hδ ht htpos hm M θ x
  have h2 := normForm_nonneg hδ t x
  have h3 : ccmLambdaMax δ t M (halfTurn θ) * normForm δ t x ≤
      max (ccmLambdaMax δ t M (halfTurn θ)) 0 * normForm δ t x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) h2
  linarith

theorem quadForm_le_max_mul {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ)
    (x : Fin m → ℂ) :
    quadForm δ t M θ x ≤ max (ccmLambdaMax δ t M θ) 0 * normForm δ t x := by
  have h1 := quadForm_le_lambdaMax_mul hδ ht htpos hm M θ x
  have h2 := normForm_nonneg hδ t x
  have h3 : ccmLambdaMax δ t M θ * normForm δ t x ≤ max (ccmLambdaMax δ t M θ) 0 * normForm δ t x :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) h2
  linarith

/-- **The residual algebra.** -/
theorem residual_le_of_energy {X A N Lw E2 C₁ Λ' Λs ε c₀ R : ℝ} (hX0 : 0 < X) (hN0 : 0 ≤ N)
    (hR0 : 0 ≤ R) (hΛ'0 : 0 ≤ Λ') (hΛ'le : Λ' ≤ Λs) (hΛs : c₀ ≤ Λs) (hc₀ : 0 < c₀)
    (hεc : ε ≤ c₀ / 4) (hXE2 : X * E2 = 1)
    (hupper : X * A ≤ -(X / 2 * (Λs - ε)) * N + N * Lw)
    (hlower : -(Λ' * N / 2) + Λ' * R - C₁ * N ≤ A)
    (herr : 2 * C₁ + 2 * (Lw * E2) ≤ ε) (hRN : N = 0 → R = 0) :
    R ≤ 2 * ε / c₀ * N := by
  have hXlow := mul_le_mul_of_nonneg_left hlower hX0.le
  have hLw : N * Lw = X * (Lw * E2) * N := by
    calc N * Lw = N * Lw * (X * E2) := by rw [hXE2, mul_one]
      _ = X * (Lw * E2) * N := by ring
  have hLw2 : X * (Lw * E2) * N ≤ X * (ε / 2 - C₁) * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    exact mul_le_mul_of_nonneg_left (by linarith) hX0.le
  -- `X Λ' R ≤ (X/2)(Λ' − Λs + 2ε) N`
  have hmain : X * (Λ' * R) ≤ X / 2 * (Λ' - Λs + 2 * ε) * N := by
    have e1 : X * (-(Λ' * N / 2) + Λ' * R - C₁ * N) =
        -(X / 2 * Λ' * N) + X * (Λ' * R) - X * C₁ * N := by ring
    have e2 : -(X / 2 * (Λs - ε)) * N = -(X / 2 * Λs * N) + X / 2 * ε * N := by ring
    have e3 : X / 2 * (Λ' - Λs + 2 * ε) * N =
        X / 2 * Λ' * N - X / 2 * Λs * N + X * ε * N := by ring
    have e4 : X * (ε / 2 - C₁) * N = X / 2 * ε * N - X * C₁ * N := by ring
    rw [e1] at hXlow
    linarith
  rcases hN0.lt_or_eq with hNpos | hNzero
  · have hX2N : 0 < X / 2 * N := by positivity
    have hnn : 0 ≤ X * (Λ' * R) := mul_nonneg hX0.le (mul_nonneg hΛ'0 hR0)
    have hbig : Λs - 2 * ε ≤ Λ' := by
      by_contra hlt
      push Not at hlt
      have : X / 2 * (Λ' - Λs + 2 * ε) * N < 0 := by
        have : Λ' - Λs + 2 * ε < 0 := by linarith
        have := mul_neg_of_neg_of_pos this hX2N
        linarith
      linarith
    have hΛ'pos : c₀ / 2 ≤ Λ' := by linarith
    have h1 : X * (Λ' * R) ≤ X * (ε * N) := by
      have : X / 2 * (Λ' - Λs + 2 * ε) * N ≤ X / 2 * (2 * ε) * N := by
        apply mul_le_mul_of_nonneg_right _ hN0
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h2 : Λ' * R ≤ ε * N := le_of_mul_le_mul_left h1 hX0
    have h3 : c₀ / 2 * R ≤ ε * N := le_trans (mul_le_mul_of_nonneg_right hΛ'pos hR0) h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    linarith
  · rw [hRN hNzero.symm, ← hNzero]
    simp

/-- **Near-ground even sources are edge profiles.** -/
theorem edgeResidual_le_of_nearGround_even {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {c₀ ε : ℝ} (hc₀ : ∀ θ, c₀ ≤ ccmLambdaMax δ t h.mult θ) (hc₀0 : 0 < c₀)
    (hεc : ε ≤ c₀ / 4) {a : SuzukiPositiveAperture}
    (herr : 2 * (3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j|) +
      2 * (h.lowWeight a.1 * Real.exp (-(2 * δ * a.1))) ≤ ε)
    (u : CCMComplexSmoothInteriorSource a) (heven : ∀ x, u (-x) = u x)
    (hnear : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 - ε)) * ∫ x, ‖u x‖ ^ 2) :
    ∃ x₁ x₂ : Fin m → ℂ,
      (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).re) s -
          realProfile δ t x₁ s) ^ 2) +
        (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).im) s -
          realProfile δ t x₂ s) ^ 2) ≤ 2 * ε / c₀ * ∫ x, ‖u x‖ ^ 2 := by
  have hδ := h.pos
  have ha0 : 0 ≤ a.1 := a.2.le
  set θ := aperturePhase t a.1 with hθ
  set N₁ := ∫ x, (u x).re ^ 2 with hN₁
  set N₂ := ∫ x, (u x).im ^ 2 with hN₂
  have hNs : ∫ x, ‖u x‖ ^ 2 = N₁ + N₂ := integral_norm_sq_eq_re_add_im u
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => sq_nonneg _
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => sq_nonneg _
  have h₁ := smoothSource_re_realIntervalSource u
  have h₂ := smoothSource_im_realIntervalSource u
  have hs₁ : ∀ x, (u (-x)).re ^ 2 = (u x).re ^ 2 := fun x => by rw [heven x]
  have hs₂ : ∀ x, (u (-x)).im ^ 2 = (u x).im ^ 2 := fun x => by rw [heven x]
  obtain ⟨x₁, hr₁, hb₁⟩ := halfLineForm_reflect_near_bounds hδ h.injective h.t_pos h.mult θ ha0
    h₁ hs₁
  obtain ⟨x₂, hr₂, hb₂⟩ := halfLineForm_reflect_near_bounds hδ h.injective h.t_pos h.mult θ ha0
    h₂ hs₂
  refine ⟨x₁, x₂, ?_⟩
  rw [hr₁, hr₂, hNs]
  have hres₁ : 0 ≤ N₁ / 2 - normForm δ t x₁ := by
    rw [← hr₁]; exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
  have hres₂ : 0 ≤ N₂ / 2 - normForm δ t x₂ := by
    rw [← hr₂]; exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
  have hn₁ := normForm_nonneg hδ t x₁
  have hn₂ := normForm_nonneg hδ t x₂
  set Λ' := max (ccmLambdaMax δ t h.mult (halfTurn θ)) 0 with hΛ'
  set C₁ := 3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j| with hC₁
  have hq₁ := quadForm_ge_neg_mul_of_unit hδ h.injective h.t_pos h.nonempty h.mult θ x₁
  have hq₂ := quadForm_ge_neg_mul_of_unit hδ h.injective h.t_pos h.nonempty h.mult θ x₂
  have hcore := topForm_sub_le_sourceQuadratic_of_even h u heven
  rw [abs_le] at hb₁ hb₂
  set l₁ := ccmLambdaMax δ t h.mult θ
  set l₂ := ccmLambdaMax δ t h.mult (halfTurn θ)
  have hl₁ : c₀ ≤ l₁ := hc₀ θ
  have hR : topRadius δ t h.mult a.1 = max l₁ l₂ := rfl
  have hΛ'le : Λ' ≤ max l₁ l₂ := max_le (le_max_right _ _)
    (le_trans hc₀0.le (hl₁.trans (le_max_left _ _)))
  set A := halfLineForm δ t h.mult θ (fun s => (u (a.1 - s)).re) +
    halfLineForm δ t h.mult θ (fun s => (u (a.1 - s)).im) with hA
  set R := (N₁ / 2 - normForm δ t x₁) + (N₂ / 2 - normForm δ t x₂) with hRdef
  have hlower : -(Λ' * (N₁ + N₂) / 2) + Λ' * R - C₁ * (N₁ + N₂) ≤ A := by
    have e : -(Λ' * (N₁ + N₂) / 2) + Λ' * R - C₁ * (N₁ + N₂) =
        -(Λ' * normForm δ t x₁) - C₁ * N₁ + (-(Λ' * normForm δ t x₂) - C₁ * N₂) := by
      rw [hRdef]; ring
    rw [e, hA]
    linarith [hb₁.1, hb₂.1]
  have hupper : Real.exp (2 * δ * a.1) * A ≤
      -(Real.exp (2 * δ * a.1) / 2 * (max l₁ l₂ - ε)) * (N₁ + N₂) +
        (N₁ + N₂) * h.lowWeight a.1 := by
    rw [hR, hNs] at hnear
    rw [hNs] at hcore
    linarith
  have hXE2 : Real.exp (2 * δ * a.1) * Real.exp (-(2 * δ * a.1)) = 1 := by
    rw [← Real.exp_add]; simp
  refine residual_le_of_energy (Real.exp_pos _) (by linarith) (by linarith) (le_max_right _ _)
    hΛ'le (hl₁.trans (le_max_left _ _)) hc₀0 hεc hXE2 hupper hlower herr fun hN => ?_
  have h1 : N₁ = 0 := by linarith
  have h2 : N₂ = 0 := by linarith
  rw [hRdef, h1, h2]
  linarith

/-- **Near-ground odd sources are edge profiles.** -/
theorem edgeResidual_le_of_nearGround_odd {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {c₀ ε : ℝ} (hc₀ : ∀ θ, c₀ ≤ ccmLambdaMax δ t h.mult θ) (hc₀0 : 0 < c₀)
    (hεc : ε ≤ c₀ / 4) {a : SuzukiPositiveAperture}
    (herr : 2 * (3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j|) +
      2 * (h.lowWeight a.1 * Real.exp (-(2 * δ * a.1))) ≤ ε)
    (u : CCMComplexSmoothInteriorSource a) (hodd : ∀ x, u (-x) = -u x)
    (hnear : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
      -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 - ε)) * ∫ x, ‖u x‖ ^ 2) :
    ∃ x₁ x₂ : Fin m → ℂ,
      (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).re) s -
          realProfile δ t x₁ s) ^ 2) +
        (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).im) s -
          realProfile δ t x₂ s) ^ 2) ≤ 2 * ε / c₀ * ∫ x, ‖u x‖ ^ 2 := by
  have hδ := h.pos
  have ha0 : 0 ≤ a.1 := a.2.le
  set θ := aperturePhase t a.1 with hθ
  set N₁ := ∫ x, (u x).re ^ 2 with hN₁
  set N₂ := ∫ x, (u x).im ^ 2 with hN₂
  have hNs : ∫ x, ‖u x‖ ^ 2 = N₁ + N₂ := integral_norm_sq_eq_re_add_im u
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun _ => sq_nonneg _
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => sq_nonneg _
  have h₁ := smoothSource_re_realIntervalSource u
  have h₂ := smoothSource_im_realIntervalSource u
  have hs₁ : ∀ x, (u (-x)).re ^ 2 = (u x).re ^ 2 := fun x => by
    rw [hodd x, Complex.neg_re, neg_sq]
  have hs₂ : ∀ x, (u (-x)).im ^ 2 = (u x).im ^ 2 := fun x => by
    rw [hodd x, Complex.neg_im, neg_sq]
  obtain ⟨x₁, hr₁, hb₁⟩ := halfLineForm_reflect_near_bounds hδ h.injective h.t_pos h.mult θ ha0
    h₁ hs₁
  obtain ⟨x₂, hr₂, hb₂⟩ := halfLineForm_reflect_near_bounds hδ h.injective h.t_pos h.mult θ ha0
    h₂ hs₂
  refine ⟨x₁, x₂, ?_⟩
  rw [hr₁, hr₂, hNs]
  set Λo := max (ccmLambdaMax δ t h.mult θ) 0 with hΛo
  set C₁ := 3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j| with hC₁
  have hq₁ := quadForm_le_max_mul hδ h.injective h.t_pos h.nonempty h.mult θ x₁
  have hq₂ := quadForm_le_max_mul hδ h.injective h.t_pos h.nonempty h.mult θ x₂
  have hcore := negTopForm_sub_le_sourceQuadratic_of_odd h u hodd
  rw [abs_le] at hb₁ hb₂
  set l₁ := ccmLambdaMax δ t h.mult θ
  set l₂ := ccmLambdaMax δ t h.mult (halfTurn θ)
  have hl₁ : c₀ ≤ l₁ := hc₀ θ
  have hR : topRadius δ t h.mult a.1 = max l₁ l₂ := rfl
  have hΛole : Λo ≤ max l₁ l₂ := max_le (le_max_left _ _)
    (le_trans hc₀0.le (hl₁.trans (le_max_left _ _)))
  set A := halfLineForm δ t h.mult θ (fun s => (u (a.1 - s)).re) +
    halfLineForm δ t h.mult θ (fun s => (u (a.1 - s)).im) with hA
  set R := (N₁ / 2 - normForm δ t x₁) + (N₂ / 2 - normForm δ t x₂) with hRdef
  have hlower : -(Λo * (N₁ + N₂) / 2) + Λo * R - C₁ * (N₁ + N₂) ≤ -A := by
    have e : -(Λo * (N₁ + N₂) / 2) + Λo * R - C₁ * (N₁ + N₂) =
        -(Λo * normForm δ t x₁) - C₁ * N₁ + (-(Λo * normForm δ t x₂) - C₁ * N₂) := by
      rw [hRdef]; ring
    rw [e, hA]
    linarith [hb₁.2, hb₂.2]
  have hupper : Real.exp (2 * δ * a.1) * -A ≤
      -(Real.exp (2 * δ * a.1) / 2 * (max l₁ l₂ - ε)) * (N₁ + N₂) +
        (N₁ + N₂) * h.lowWeight a.1 := by
    rw [hR, hNs] at hnear
    rw [hNs] at hcore
    linarith
  have hXE2 : Real.exp (2 * δ * a.1) * Real.exp (-(2 * δ * a.1)) = 1 := by
    rw [← Real.exp_add]; simp
  have hres₁ : 0 ≤ N₁ / 2 - normForm δ t x₁ := by
    rw [← hr₁]; exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
  have hres₂ : 0 ≤ N₂ / 2 - normForm δ t x₂ := by
    rw [← hr₂]; exact setIntegral_nonneg measurableSet_Ioi fun s _ => sq_nonneg _
  have hn₁ := normForm_nonneg hδ t x₁
  have hn₂ := normForm_nonneg hδ t x₂
  refine residual_le_of_energy (Real.exp_pos _) (by linarith) (by linarith) (le_max_right _ _)
    hΛole (hl₁.trans (le_max_left _ _)) hc₀0 hεc hXE2 hupper hlower herr fun hN => ?_
  have h1 : N₁ = 0 := by linarith
  have h2 : N₂ = 0 := by linarith
  rw [hRdef, h1, h2]
  linarith

/-- **Shape of near-ground sources.** Under a finite top layer, for every small `ε > 0` and all
sufficiently large apertures, every smooth source of pure parity whose Rayleigh quotient is within
`ε e^{2δa}/2` of `−(e^{2δa}/2)Λ*(a)` has both reflected near profiles within total squared
distance `(2ε/c₀)‖u‖²` of the edge span of the top layer. -/
theorem exists_edgeProfile_of_nearGround {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ c₀ / 4 → ∃ A : ℝ,
      ∀ a : SuzukiPositiveAperture, A ≤ a.1 → ∀ u : CCMComplexSmoothInteriorSource a,
        ((∀ x, u (-x) = u x) ∨ (∀ x, u (-x) = -u x)) →
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤
          -(Real.exp (2 * δ * a.1) / 2 * (topRadius δ t h.mult a.1 - ε)) * ∫ x, ‖u x‖ ^ 2 →
        ∃ x₁ x₂ : Fin m → ℂ,
          (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).re) s -
              realProfile δ t x₁ s) ^ 2) +
            (∫ s in Ioi (0 : ℝ), ((Iic a.1).indicator (fun s => (u (a.1 - s)).im) s -
              realProfile δ t x₂ s) ^ 2) ≤ 2 * ε / c₀ * ∫ x, ‖u x‖ ^ 2 := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_lambdaMax_lower h.pos h.injective h.t_pos h.nonempty
    h.mult_pos
  refine ⟨c₀, hc₀, fun ε hε hεc => ?_⟩
  obtain ⟨A, hA⟩ := eventually_atTop.mp ((tendsto_floorError h).eventually (gt_mem_nhds hε))
  refine ⟨A, fun a ha u hpar hnear => ?_⟩
  have herr := (hA a.1 ha).le
  rcases hpar with he | ho
  · exact edgeResidual_le_of_nearGround_even h hlow hc₀ hεc herr u he hnear
  · exact edgeResidual_le_of_nearGround_odd h hlow hc₀ hεc herr u ho hnear

end

end RHTower.CCMParityTopLayer
