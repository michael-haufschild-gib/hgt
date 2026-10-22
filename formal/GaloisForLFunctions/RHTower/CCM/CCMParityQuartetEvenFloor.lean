import GaloisForLFunctions.RHTower.CCM.CCMParityQuartetZeroSum

/-!
# The even floor of the restricted Weil form under an isolated off-line quartet

**Hypothesis** (`IsolatedTopQuartet σ`).  `σ = t + iδ` with `t, δ > 0` is a spectral point of a Xi
zero copy; the copies with non-real spectral point form a finite set; each of them lies on the
quartet `{σ, σ̄, −σ, −σ̄}` or has `|Im z| < δ`.  Let `M ≥ 1` be the number of copies on the quartet.

**Theorem** (`sourceQuadratic_ge_of_isEven`).  At every aperture `a`, every reflection-even vector
`u` of the CCM form domain satisfies

`Q_a(u) ≥ −((M/4) D⁺(a) + L(a)) ‖J u‖²`,

with `D⁺(a) = ∫_{−a}^{a} 4 sin²(tx) sinh²(δx) dx` and `L(a) = Σ_{lower copies} 2a e^{2a|Im z|}`.

**Proof.**  For a smooth even source the zero sum splits into real points (`|û|² ≥ 0`), the top
quartet (each copy contributes `Re(p q̄)`, `p = û(σ)`, `q = û(σ̄)`) and the lower copies (each bounded
by Cauchy–Schwarz).  Since `4 Re(p q̄) = |p+q|² − |p−q|² ≥ −|p−q|²` and, for even `u`,
`p − q = ∫ u(x) (cos σx − cos σ̄x) dx` with `|cos σx − cos σ̄x| = 2|sin(tx) sinh(δx)|`,
Cauchy–Schwarz gives `|p − q|² ≤ ‖u‖² D⁺`.  Smooth sources are dense in the form domain, the even
projection is continuous, and `Q_a` and `J` are continuous, so the bound passes to all even vectors.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityQuartet

noncomputable section

/-! ## Square-integrability and Cauchy–Schwarz on an interval -/

theorem memLp_indicator_Icc {g : ℝ → ℂ} (hg : Continuous g) (A : ℝ) :
    MemLp ((Icc (-A) A).indicator g) 2 := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Icc (-A) A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hC))

theorem integral_norm_sq_indicator_Icc {g : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) :
    ∫ x, ‖(Icc (-A) A).indicator g x‖ ^ 2 = ∫ x in (-A)..A, ‖g x‖ ^ 2 := by
  have hfun : (fun x => ‖(Icc (-A) A).indicator g x‖ ^ 2) =
      (Icc (-A) A).indicator (fun x => ‖g x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-A) A <;> simp [hx]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

theorem integral_norm_sq_indicator_le {g : ℝ → ℂ} {A B : ℝ} (hA : 0 ≤ A)
    (hB : ∀ x ∈ Icc (-A) A, ‖g x‖ ^ 2 ≤ B) :
    ∫ x, ‖(Icc (-A) A).indicator g x‖ ^ 2 ≤ 2 * A * B := by
  have hfun : (fun x => ‖(Icc (-A) A).indicator g x‖ ^ 2) =
      (Icc (-A) A).indicator (fun x => ‖g x‖ ^ 2) := by
    funext x
    by_cases hx : x ∈ Icc (-A) A <;> simp [hx]
  rw [hfun, integral_indicator measurableSet_Icc]
  have hle := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun x => ‖g x‖ ^ 2)
    (s := Icc (-A) A) measure_Icc_lt_top (C := B) fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hB x hx
  have hvol : volume.real (Icc (-A) A) = 2 * A := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hle
  calc (∫ x in Icc (-A) A, ‖g x‖ ^ 2) ≤ ‖∫ x in Icc (-A) A, ‖g x‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ B * (2 * A) := hle
    _ = 2 * A * B := by ring

/-- A compactly supported continuous source vanishing off `[−A, A]`. -/
structure IntervalSource (A : ℝ) (f : ℝ → ℂ) : Prop where
  continuous : Continuous f
  hasCompactSupport : HasCompactSupport f
  vanish : ∀ x, x ∉ Icc (-A) A → f x = 0

theorem IntervalSource.memLp {A : ℝ} {f : ℝ → ℂ} (hf : IntervalSource A f) : MemLp f 2 :=
  hf.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport

theorem IntervalSource.mul_eq_mul_indicator {A : ℝ} {f : ℝ → ℂ} (hf : IntervalSource A f)
    (g : ℝ → ℂ) (x : ℝ) : f x * g x = f x * (Icc (-A) A).indicator g x := by
  by_cases hx : x ∈ Icc (-A) A
  · simp [hx]
  · simp [hx, hf.vanish x hx]

/-- `|f̂(w)|² ≤ ‖f‖² · 2A e^{2A|Im w|}`. -/
theorem norm_testTransform_sq_le {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ} (hf : IntervalSource A f)
    (w : ℂ) :
    ‖testTransform f w‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2) * (2 * A * Real.exp (2 * A * |w.im|)) := by
  have hexp : Continuous fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ)) := by fun_prop
  have heq : testTransform f w =
      ∫ x, f x * (Icc (-A) A).indicator (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x := by
    unfold testTransform
    congr 1
    funext x
    exact hf.mul_eq_mul_indicator (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x
  rw [heq]
  refine (norm_integral_mul_sq_le hf.memLp (memLp_indicator_Icc hexp A)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => by positivity)
  apply integral_norm_sq_indicator_le hA
  intro x hx
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * w * (x : ℂ)).re = -(w.im * x) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hx' : |x| ≤ A := abs_le.mpr ⟨hx.1, hx.2⟩
  have : -(w.im * x) ≤ |w.im| * A := by
    have h1 : -(w.im * x) ≤ |w.im * x| := neg_le_abs _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg w.im]
  push_cast
  linarith

/-! ## The even difference vector -/

theorem testTransform_eq_integral_cos {f : ℝ → ℂ} {A : ℝ} (hf : IntervalSource A f)
    (heven : ∀ x, f (-x) = f x) (w : ℂ) :
    testTransform f w = ∫ x, f x * Complex.cos (w * x) := by
  have hneg := testTransform_neg_of_reflect (s := 1) (by simpa using heven) w
  rw [one_mul] at hneg
  have hint : ∀ v : ℂ, Integrable fun x : ℝ => f x * Complex.exp (Complex.I * v * (x : ℂ)) :=
    fun v => (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hf.hasCompactSupport.mul_right)
  have h2 : testTransform f w = (testTransform f w + testTransform f (-w)) / 2 := by
    rw [hneg]
    ring
  rw [h2]
  unfold testTransform
  rw [← integral_add (hint w) (hint (-w)), ← integral_div]
  congr 1
  funext x
  rw [Complex.cos.eq_1]
  ring_nf

theorem cos_mul_sub_cos_conj_mul (σ : ℂ) (x : ℝ) :
    Complex.cos (σ * x) - Complex.cos ((starRingEnd ℂ) σ * x) =
      -2 * Complex.I * (Real.sin (σ.re * x) : ℂ) * (Real.sinh (σ.im * x) : ℂ) := by
  have h1 : σ * (x : ℂ) = ((σ.re * x : ℝ) : ℂ) + ((σ.im * x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have h2 : (starRingEnd ℂ) σ * (x : ℂ) =
      ((σ.re * x : ℝ) : ℂ) + ((-(σ.im * x) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h1, h2, Complex.cos_add_mul_I, Complex.cos_add_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, Real.cosh_neg, Real.sinh_neg]
  push_cast
  ring

theorem norm_cos_mul_sub_cos_conj_mul_sq (σ : ℂ) (x : ℝ) :
    ‖Complex.cos (σ * x) - Complex.cos ((starRingEnd ℂ) σ * x)‖ ^ 2 =
      4 * Real.sin (σ.re * x) ^ 2 * Real.sinh (σ.im * x) ^ 2 := by
  rw [cos_mul_sub_cos_conj_mul, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  norm_num
  rw [mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- For an even interval source, `|f̂(σ) − f̂(σ̄)|² ≤ ‖f‖² D⁺(A)`. -/
theorem norm_sub_testTransform_sq_le_of_even {A : ℝ} (hA : 0 ≤ A) {f : ℝ → ℂ}
    (hf : IntervalSource A f) (heven : ∀ x, f (-x) = f x) (σ : ℂ) :
    ‖testTransform f σ - testTransform f ((starRingEnd ℂ) σ)‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2) * evenFloorMass σ.re σ.im A := by
  have hint : ∀ v : ℂ, Integrable fun x : ℝ => f x * Complex.cos (v * x) :=
    fun v => (hf.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hf.hasCompactSupport.mul_right)
  have hcos : Continuous fun x : ℝ =>
      Complex.cos (σ * x) - Complex.cos ((starRingEnd ℂ) σ * x) := by fun_prop
  rw [testTransform_eq_integral_cos hf heven, testTransform_eq_integral_cos hf heven,
    ← integral_sub (hint σ) (hint _)]
  have heq : (∫ x, f x * Complex.cos (σ * x) - f x * Complex.cos ((starRingEnd ℂ) σ * x)) =
      ∫ x, f x * (Icc (-A) A).indicator
        (fun x : ℝ => Complex.cos (σ * x) - Complex.cos ((starRingEnd ℂ) σ * x)) x := by
    congr 1
    funext x
    rw [← hf.mul_eq_mul_indicator, mul_sub]
  rw [heq]
  refine (norm_integral_mul_sq_le hf.memLp (memLp_indicator_Icc hcos A)).trans ?_
  apply le_of_eq
  congr 1
  rw [integral_norm_sq_indicator_Icc hA, evenFloorMass]
  congr 1
  funext x
  rw [norm_cos_mul_sub_cos_conj_mul_sq]

/-! ## The isolated off-line quartet hypothesis -/

/-- `z` lies on the quartet `{σ, σ̄, −σ, −σ̄}`. -/
def InQuartet (σ z : ℂ) : Prop :=
  z = σ ∨ z = (starRingEnd ℂ) σ ∨ z = -σ ∨ z = -(starRingEnd ℂ) σ

/-- **The isolated off-line quartet hypothesis.**  `σ = t + iδ` (`t, δ > 0`) is a spectral point,
the non-real spectral points form a finite set of copies, and each lies on the quartet of `σ` or
strictly closer to the real axis. -/
structure IsolatedTopQuartet (σ : ℂ) : Prop where
  re_pos : 0 < σ.re
  im_pos : 0 < σ.im
  finite_offLine : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite
  top_or_low : ∀ q : XiZeroCopy, (xiSpectralPoint q).im ≠ 0 →
    InQuartet σ (xiSpectralPoint q) ∨ |(xiSpectralPoint q).im| < σ.im
  exists_top : ∃ q : XiZeroCopy, xiSpectralPoint q = σ

namespace IsolatedTopQuartet

open scoped Classical

variable {σ : ℂ} (h : IsolatedTopQuartet σ)

/-- The finite set of off-line copies. -/
def offLine : Finset XiZeroCopy := h.finite_offLine.toFinset

/-- Copies on the top quartet. -/
def topSet : Finset XiZeroCopy := h.offLine.filter fun q => InQuartet σ (xiSpectralPoint q)

/-- Off-line copies strictly below the top. -/
def lowSet : Finset XiZeroCopy := h.offLine.filter fun q => ¬ InQuartet σ (xiSpectralPoint q)

/-- The number `M` of copies on the top quartet. -/
def topCount : ℕ := h.topSet.card

/-- `L(A) = Σ_{lower copies} 2A e^{2A|Im z|}`. -/
def lowWeight (A : ℝ) : ℝ :=
  ∑ q ∈ h.lowSet, 2 * A * Real.exp (2 * A * |(xiSpectralPoint q).im|)

theorem mem_offLine {q : XiZeroCopy} : q ∈ h.offLine ↔ (xiSpectralPoint q).im ≠ 0 := by
  unfold offLine
  rw [Set.Finite.mem_toFinset]
  rfl

include h in
theorem im_ne_zero_of_inQuartet {z : ℂ} (hz : InQuartet σ z) : z.im ≠ 0 := by
  have hδ := h.im_pos
  rcases hz with rfl | rfl | rfl | rfl <;> simp <;> linarith

include h in

theorem topCount_pos : 0 < h.topCount := by
  obtain ⟨q, hq⟩ := h.exists_top
  apply Finset.card_pos.mpr
  refine ⟨q, ?_⟩
  unfold topSet
  rw [Finset.mem_filter, mem_offLine]
  have hin : InQuartet σ (xiSpectralPoint q) := Or.inl hq
  exact ⟨h.im_ne_zero_of_inQuartet hin, hin⟩

theorem abs_im_lt_of_mem_lowSet {q : XiZeroCopy} (hq : q ∈ h.lowSet) :
    |(xiSpectralPoint q).im| < σ.im := by
  unfold lowSet at hq
  rw [Finset.mem_filter, mem_offLine] at hq
  rcases h.top_or_low q hq.1 with hin | hlt
  · exact absurd hin hq.2
  · exact hlt

theorem lowWeight_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ h.lowWeight A :=
  Finset.sum_nonneg fun _ _ => by positivity

end IsolatedTopQuartet

/-! ## The even floor for smooth sources -/

theorem smoothSource_intervalSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : IntervalSource a.1 u where
  continuous := u.continuous
  hasCompactSupport := u.hasCompactSupport
  vanish := fun x hx => by
    by_contra hne
    exact hx (Ioo_subset_Icc_self (u.support_subset hne))

theorem four_mul_re_mul_conj (p q : ℂ) :
    4 * (p * (starRingEnd ℂ) q).re = ‖p + q‖ ^ 2 - ‖p - q‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  ring

theorem re_mul_conj_ge (p q : ℂ) : -(‖p - q‖ ^ 2 / 4) ≤ (p * (starRingEnd ℂ) q).re := by
  have h := four_mul_re_mul_conj p q
  have : 0 ≤ ‖p + q‖ ^ 2 := by positivity
  linarith

/-- **The even floor on smooth sources.** -/
theorem sourceQuadratic_ge_of_smooth_even {σ : ℂ} (h : IsolatedTopQuartet σ)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (heven : ∀ x, u (-x) = u x) :
    -((h.topCount : ℝ) / 4 * evenFloorMass σ.re σ.im a.1 + h.lowWeight a.1) *
        ∫ x, ‖u x‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  classical
  have ha : 0 ≤ a.1 := a.2.le
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
  rw [← Finset.sum_filter_add_sum_filter_not h.offLine
    (fun q => InQuartet σ (xiSpectralPoint q))]
  -- the top quartet
  set P := testTransform u σ with hP
  set Q := testTransform u ((starRingEnd ℂ) σ) with hQ
  have htop : ∀ q ∈ h.topSet, (T q).re = (P * (starRingEnd ℂ) Q).re := by
    intro q hq
    unfold IsolatedTopQuartet.topSet at hq
    rw [Finset.mem_filter] at hq
    exact re_zeroSumTerm_quartet (s := 1) (by simpa using heven) (by simp) σ hq.2
  have htopsum : ∑ q ∈ h.offLine with InQuartet σ (xiSpectralPoint q), (T q).re =
      (h.topCount : ℝ) * (P * (starRingEnd ℂ) Q).re := by
    have hset : ∑ q ∈ h.offLine with InQuartet σ (xiSpectralPoint q), (T q).re =
        ∑ q ∈ h.topSet, (T q).re := rfl
    rw [hset, Finset.sum_congr rfl htop, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hPQ : ‖P - Q‖ ^ 2 ≤ N * evenFloorMass σ.re σ.im a.1 :=
    norm_sub_testTransform_sq_le_of_even ha hI heven σ
  have htopge : -((h.topCount : ℝ) / 4 * evenFloorMass σ.re σ.im a.1) * N ≤
      (h.topCount : ℝ) * (P * (starRingEnd ℂ) Q).re := by
    have hre := re_mul_conj_ge P Q
    have hM : (0 : ℝ) ≤ h.topCount := Nat.cast_nonneg _
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
  have hlowsum : -(N * h.lowWeight a.1) ≤
      ∑ q ∈ h.offLine with ¬ InQuartet σ (xiSpectralPoint q), (T q).re := by
    have : ∑ q ∈ h.offLine with ¬ InQuartet σ (xiSpectralPoint q), (T q).re =
        ∑ q ∈ h.lowSet, (T q).re := rfl
    rw [this, IsolatedTopQuartet.lowWeight, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hlow
  rw [htopsum]
  nlinarith

/-! ## The physical norm of a smooth source -/

theorem norm_sq_toAperture_toCCMFormVector {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  set f : SoninL2 := (ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) with hf
  have hnorm : ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ = ‖f‖ := rfl
  rw [hnorm]
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have hpoint : ∀ x : ℝ, inner ℂ ((f : ℝ → ℂ) x) ((f : ℝ → ℂ) x) =
      ((‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpoint] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h2
  have h5 : ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by exact_mod_cast h4
  rw [h5]
  apply integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
  rw [hx]

/-! ## Even symmetrization of smooth sources and the domain extension -/

/-- The even symmetrization `x ↦ (u(x) + u(−x))/2` of a smooth interior source. -/
def evenSymSource {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    CCMComplexSmoothInteriorSource a where
  toFun x := (2 : ℂ)⁻¹ * (u x + u (-x))
  smooth := contDiff_const.mul (u.smooth.add (u.smooth.comp contDiff_neg))
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
    have hsupp : Function.support (fun x => (2 : ℂ)⁻¹ * (u x + u (-x))) ⊆
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

theorem evenSymSource_apply {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : (evenSymSource u : ℝ → ℂ) x = (2 : ℂ)⁻¹ * (u x + u (-x)) := rfl

theorem evenSymSource_even {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : (evenSymSource u : ℝ → ℂ) (-x) = (evenSymSource u : ℝ → ℂ) x := by
  rw [evenSymSource_apply, evenSymSource_apply, neg_neg, add_comm]

/-- The even part of a smooth source vector is the vector of its even symmetrization. -/
theorem evenPart_toCCMFormVector {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilEvenPart a u.toCCMFormVector = (evenSymSource u).toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective a
  apply Subtype.ext
  set F : SoninL2 := (ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) with hF_def
  have hlin : ((ccmArchimedeanFormToAperture a (ccmRestrictedWeilEvenPart a u.toCCMFormVector) :
      suzukiApertureHilbert a) : SoninL2) = (2 : ℂ)⁻¹ • (F + l2Reflection F) := by
    rw [ccmRestrictedWeilEvenPart, map_smul, map_add]
    change (2 : ℂ)⁻¹ • ((F : SoninL2) + ((ccmArchimedeanFormToAperture a
      (ccmArchimedeanFormReflection a u.toCCMFormVector) : suzukiApertureHilbert a) : SoninL2)) = _
    rw [ccmArchimedeanFormToAperture_reflection]
  rw [hlin]
  apply Lp.ext
  have hF : (F : ℝ → ℂ) =ᵐ[volume] u := u.toCCMFormVector_physical_coeFn
  have hFneg : (fun x => (F : ℝ → ℂ) (-x)) =ᵐ[volume] fun x => (u : ℝ → ℂ) (-x) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp hF
  have hR : ((l2Reflection F : SoninL2) : ℝ → ℂ) =ᵐ[volume] fun x => (F : ℝ → ℂ) (-x) :=
    Lp.coeFn_compMeasurePreserving F (Measure.measurePreserving_neg (volume : Measure ℝ))
  filter_upwards [Lp.coeFn_smul (2 : ℂ)⁻¹ (F + l2Reflection F), Lp.coeFn_add F (l2Reflection F),
    hR, hF, hFneg, (evenSymSource u).toCCMFormVector_physical_coeFn] with x h1 h2 h3 h4 h5 h6
  rw [h1, Pi.smul_apply, h2, Pi.add_apply, h3, h4, h5, smul_eq_mul]
  exact h6.symm

/-- **Domain extension.**  An even floor on smooth sources holds on every even form vector. -/
theorem floor_of_isEven_of_smooth {a : SuzukiPositiveAperture} {c : ℝ}
    (hsm : ∀ u : CCMComplexSmoothInteriorSource a, (∀ x, u (-x) = u x) →
      c * ∫ x, ‖u x‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector)
    (w : CCMArchimedeanFormDomain a) (hw : ccmArchimedeanFormReflection a w = w) :
    c * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a w := by
  have hcontE : Continuous (ccmRestrictedWeilEvenPart a) := by
    unfold ccmRestrictedWeilEvenPart
    exact (continuous_id.add (ccmArchimedeanFormReflection a).continuous).const_smul ((2 : ℂ)⁻¹)
  have key : ∀ v : CCMArchimedeanFormDomain a,
      c * ‖ccmArchimedeanFormToAperture a (ccmRestrictedWeilEvenPart a v)‖ ^ 2 ≤
        ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a v) := by
    intro v
    refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on v ?_ ?_
    · exact isClosed_le
        (continuous_const.mul
          (((ccmArchimedeanFormToAperture a).continuous.comp hcontE).norm.pow 2))
        ((continuous_ccmRestrictedWeilSourceQuadratic a).comp hcontE)
    · intro u
      rw [evenPart_toCCMFormVector, norm_sq_toAperture_toCCMFormVector]
      exact hsm _ (evenSymSource_even u)
  have hev : ccmRestrictedWeilEvenPart a w = w := by
    rw [ccmRestrictedWeilEvenPart, hw, ← two_smul ℂ w, smul_smul]
    norm_num
  have := key w
  rwa [hev] at this

/-- **The even floor.**  Under an isolated off-line quartet, every reflection-even form vector
satisfies `Q_a(u) ≥ −((M/4) D⁺(a) + L(a)) ‖J u‖²`. -/
theorem sourceQuadratic_ge_of_isEven {σ : ℂ} (h : IsolatedTopQuartet σ)
    {a : SuzukiPositiveAperture} (w : CCMArchimedeanFormDomain a)
    (hw : ccmArchimedeanFormReflection a w = w) :
    -((h.topCount : ℝ) / 4 * evenFloorMass σ.re σ.im a.1 + h.lowWeight a.1) *
        ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤ ccmRestrictedWeilSourceQuadratic a w :=
  floor_of_isEven_of_smooth (fun u hu => sourceQuadratic_ge_of_smooth_even h u hu) w hw

end

end RHTower.CCMParityQuartet
