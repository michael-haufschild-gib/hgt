import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerTransform

/-!
# The even floor of the restricted Weil form under a finite top layer

**Hypothesis** (`FiniteTopLayer δ t`). The Xi zero copies with non-real spectral point form a
finite set. Each of them lies on the quartet of some `σ_j = t_j + iδ` (`j : Fin m`, `t_j > 0`
distinct, `δ > 0`, every `σ_j` a spectral point) or satisfies `|Im z| < δ`. Let `M_j` be the number
of copies on the quartet of `σ_j`.

**Theorem** (`sourceQuadratic_ge_of_isEven`). At every aperture `a`, every reflection-even vector
`u` of the CCM form domain satisfies

`Q_a(u) ≥ −(e^{2δa}(Λ'(a)/2 + (3/(2δ)) e^{−δa} Σ_j M_j) + L(a)) ‖J u‖²`,

where `Λ'(a) = max(λ_max(T(θ(a) + π𝟙)), 0)` for the Cauchy model at the aperture phases
`θ_j(a) = −2t_j a`, and `L(a) = Σ_{lower copies} 2a e^{2a|Im z|}`.

**Proof.** Split the zero sum of a smooth even source. Real points contribute `≥ 0`. Lower copies
are bounded by Cauchy–Schwarz. The quartet of `σ_j` contributes
`M_j (Re û₁(−σ_j)² + Re û₂(−σ_j)²)` (`re_zeroSumTerm_parity`), where `u₁, u₂` are the real and
imaginary parts. By `sum_re_testTransform_sq_eq` the top layer is
`e^{2δa}(T(θ(a))[u₁(a − ·)] + T(θ(a))[u₂(a − ·)])`, and the even halving
(`halfLineForm_reflect_ge_of_even`) bounds each term from below. Density
(`floor_of_isEven_of_smooth`) extends the bound to all even vectors.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-- The top spectral point `σ_j = t_j + iδ`. -/
def topPoint (δ : ℝ) (t : Fin m → ℝ) (j : Fin m) : ℂ := (t j : ℂ) + δ * I

/-- **A finite off-line set with a top layer of height `δ`.** -/
structure FiniteTopLayer (δ : ℝ) (t : Fin m → ℝ) : Prop where
  pos : 0 < δ
  injective : Function.Injective t
  t_pos : ∀ j, 0 < t j
  nonempty : 0 < m
  finite_offLine : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite
  top_or_low : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
    (∃ j, InQuartet (topPoint δ t j) (xiSpectralPoint q)) ∨ |(xiSpectralPoint q).im| < δ
  exists_top : ∀ j, ∃ q : XiZeroCopy, xiSpectralPoint q = topPoint δ t j

namespace FiniteTopLayer

open scoped Classical

variable {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)

/-- The finite set of off-line copies. -/
def offLine : Finset XiZeroCopy := h.finite_offLine.toFinset

/-- Copies on the quartet of `σ_j`. -/
def topSet (j : Fin m) : Finset XiZeroCopy :=
  h.offLine.filter fun q => InQuartet (topPoint δ t j) (xiSpectralPoint q)

/-- Off-line copies strictly below the top layer. -/
def lowSet : Finset XiZeroCopy :=
  h.offLine.filter fun q => ¬ ∃ j, InQuartet (topPoint δ t j) (xiSpectralPoint q)

/-- The multiplicity `M_j` of the quartet of `σ_j`. -/
def mult (j : Fin m) : ℝ := ((h.topSet j).card : ℝ)

/-- `L(A) = Σ_{lower copies} 2A e^{2A|Im z|}`. -/
def lowWeight (A : ℝ) : ℝ :=
  ∑ q ∈ h.lowSet, 2 * A * Real.exp (2 * A * |(xiSpectralPoint q).im|)

theorem mem_offLine {q : XiZeroCopy} : q ∈ h.offLine ↔ (xiSpectralPoint q).im ≠ 0 := by
  unfold offLine
  rw [Set.Finite.mem_toFinset]
  rfl

theorem topPoint_re (j : Fin m) : (topPoint δ t j).re = t j := by simp [topPoint]

theorem topPoint_im (j : Fin m) : (topPoint δ t j).im = δ := by simp [topPoint]

include h in
theorem im_ne_zero_of_inQuartet {j : Fin m} {z : ℂ} (hz : InQuartet (topPoint δ t j) z) :
    z.im ≠ 0 := by
  have hδ := h.pos
  rcases hz with rfl | rfl | rfl | rfl <;> simp [topPoint] <;> linarith

theorem abs_re_of_inQuartet {j : Fin m} {z : ℂ} (hz : InQuartet (topPoint δ t j) z) :
    |z.re| = |t j| := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [topPoint]

include h in
theorem eq_of_inQuartet {j k : Fin m} {z : ℂ} (hj : InQuartet (topPoint δ t j) z)
    (hk : InQuartet (topPoint δ t k) z) : j = k := by
  have h1 := abs_re_of_inQuartet hj
  have h2 := abs_re_of_inQuartet hk
  rw [h1, abs_of_pos (h.t_pos j), abs_of_pos (h.t_pos k)] at h2
  exact h.injective h2

theorem mult_pos (j : Fin m) : 0 < h.mult j := by
  obtain ⟨q, hq⟩ := h.exists_top j
  unfold mult
  have : 0 < (h.topSet j).card := by
    apply Finset.card_pos.mpr
    refine ⟨q, ?_⟩
    unfold topSet
    rw [Finset.mem_filter, mem_offLine]
    have hin : InQuartet (topPoint δ t j) (xiSpectralPoint q) := Or.inl hq
    exact ⟨h.im_ne_zero_of_inQuartet hin, hin⟩
  exact_mod_cast this

theorem abs_im_lt_of_mem_lowSet {q : XiZeroCopy} (hq : q ∈ h.lowSet) :
    |(xiSpectralPoint q).im| < δ := by
  unfold lowSet at hq
  rw [Finset.mem_filter, mem_offLine] at hq
  rcases h.top_or_low q hq.1 with hin | hlt
  · exact absurd hin hq.2
  · exact hlt

theorem lowWeight_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ h.lowWeight A :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- The off-line sum splits into the top quartets and the lower copies. -/
theorem sum_offLine_eq (f : XiZeroCopy → ℝ) :
    ∑ q ∈ h.offLine, f q = ∑ j, ∑ q ∈ h.topSet j, f q + ∑ q ∈ h.lowSet, f q := by
  rw [← Finset.sum_filter_add_sum_filter_not h.offLine
    (fun q => ∃ j, InQuartet (topPoint δ t j) (xiSpectralPoint q))]
  congr 1
  have hbi : h.offLine.filter (fun q => ∃ j, InQuartet (topPoint δ t j) (xiSpectralPoint q)) =
      Finset.univ.biUnion h.topSet := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, topSet]
    constructor
    · rintro ⟨hq, j, hj⟩; exact ⟨j, hq, hj⟩
    · rintro ⟨j, hq, hj⟩; exact ⟨hq, j, hj⟩
  rw [hbi, Finset.sum_biUnion]
  intro j _ k _ hjk
  refine Finset.disjoint_left.mpr fun q hqj hqk => hjk ?_
  simp only [topSet, Finset.mem_filter] at hqj hqk
  exact h.eq_of_inQuartet hqj.2 hqk.2

end FiniteTopLayer

/-! ## Interval sources from smooth sources -/

theorem smoothSource_re_realIntervalSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : RealIntervalSource a.1 fun x => (u x).re where
  memLp := (Complex.continuous_re.comp u.continuous).memLp_of_hasCompactSupport
    (u.hasCompactSupport.comp_left Complex.zero_re)
  vanish := fun x hx => by
    have hnot : x ∉ tsupport (u : ℝ → ℂ) := fun hmem => by
      have := u.tsupport_subset hmem
      rw [mem_Ioo] at this
      have := abs_lt.mpr this
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot, Complex.zero_re]

theorem smoothSource_im_realIntervalSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : RealIntervalSource a.1 fun x => (u x).im where
  memLp := (Complex.continuous_im.comp u.continuous).memLp_of_hasCompactSupport
    (u.hasCompactSupport.comp_left Complex.zero_im)
  vanish := fun x hx => by
    have hnot : x ∉ tsupport (u : ℝ → ℂ) := fun hmem => by
      have := u.tsupport_subset hmem
      rw [mem_Ioo] at this
      have := abs_lt.mpr this
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot, Complex.zero_im]

theorem integral_norm_sq_eq_re_add_im {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ∫ x, ‖u x‖ ^ 2 = (∫ x, (u x).re ^ 2) + ∫ x, (u x).im ^ 2 := by
  rw [← integral_add (smoothSource_re_realIntervalSource u).memLp.integrable_sq
    (smoothSource_im_realIntervalSource u).memLp.integrable_sq]
  congr 1
  funext x
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The aperture phases `θ_j(a) = −2t_j a`. -/
def aperturePhase (t : Fin m → ℝ) (a : ℝ) : Fin m → ℝ := fun j => -2 * t j * a

/-- The even floor constant
`c_e(a) = −(e^{2δa}(Λ'(a)/2 + (3/(2δ)) e^{−δa} Σ_j M_j) + L(a))`. -/
def evenFloorConst {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (a : ℝ) : ℝ :=
  -(Real.exp (2 * δ * a) *
      (max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a))) 0 / 2 +
        3 / (2 * δ) * Real.exp (-(δ * a)) * ∑ j, |h.mult j|) + h.lowWeight a)

/-- **The even floor on smooth sources.** -/
theorem sourceQuadratic_ge_of_smooth_even {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (heven : ∀ x, u (-x) = u x) :
    evenFloorConst h a.1 * ∫ x, ‖u x‖ ^ 2 ≤
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
  set Λ' := max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) 0 with hΛ'
  set C := 3 / (2 * δ) * Real.exp (-(δ * a.1)) * ∑ j, |h.mult j| with hC
  have hf₁ := halfLineForm_reflect_ge_of_even hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1) ha h₁ he₁
  have hf₂ := halfLineForm_reflect_ge_of_even hδ h.injective h.t_pos h.nonempty h.mult
    (aperturePhase t a.1) ha h₂ he₂
  have hNsplit : N = (∫ x, u₁ x ^ 2) + ∫ x, u₂ x ^ 2 := integral_norm_sq_eq_re_add_im u
  have htopge : -(Real.exp (2 * δ * a.1) * (Λ' / 2 + C) * N) ≤
      ∑ j, ∑ q ∈ h.topSet j, (T q).re := by
    rw [htop, hNsplit]
    have hE : 0 < Real.exp (2 * δ * a.1) := Real.exp_pos _
    have := add_le_add hf₁ hf₂
    nlinarith
  -- the lower copies
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
  unfold evenFloorConst
  rw [← hΛ', ← hC]
  nlinarith

/-- **The even floor.** -/
theorem sourceQuadratic_ge_of_isEven {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    {a : SuzukiPositiveAperture} (w : CCMArchimedeanFormDomain a)
    (hw : ccmArchimedeanFormReflection a w = w) :
    evenFloorConst h a.1 * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a w :=
  floor_of_isEven_of_smooth (fun u hu => sourceQuadratic_ge_of_smooth_even h u hu) w hw

end

end RHTower.CCMParityTopLayer
