import GaloisForLFunctions.SquareRootThreshold.IntervalSourceTransformsSampledOnLocallyBoundedPoints
import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsALandauExponent
import GaloisForLFunctions.SquareRootThreshold.TheSideIsTheDepthAndTheWidthIsItsSupremum
import GaloisForLFunctions.RHTower.CCMParityTopLayerGroundEnergyLaw
import GaloisForLFunctions.RHTower.XiThermalSourceRelativeGapBound
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# The zero width is the fall rate of the ground energy when the off-line zeros do not cluster

The restricted Weil ground energy `μ(A)` falls at least like `−e^{2σA}` whenever the zero width
`σ = sup |Re ρ − ½|` is positive; this module proves the converse under one hypothesis on the
off-line zeros: that their number in any unit height window is bounded
(`OffLineCopiesLocallyBounded M`).

* **The floor** (`neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy`): for every aperture
  `A`, `μ(A) ≥ −M (2A + 2π) e^{2π} e^{2σA}`, `σ = zetaZeroWidth`.  On the zero side the source
  quadratic of a smooth interior source is `Σ_q Re Φ(−z_q) conj Φ(−z̄_q)`; the on-line copies
  contribute `|Φ(−z_q)|² ≥ 0`, and the off-line copies contribute at least
  `−(|Φ(−z_q)|² + |Φ(−z̄_q)|²)/2`, whose sum the sampling inequality
  `sum_norm_sq_testTransform_le_of_locallyBounded'` bounds by `M (2A + 2π) e^{2π} e^{2σA} ‖u‖²`
  since every depth `|Im z_q| = |Re ρ − ½|` is at most the width.  Density extends the floor from
  smooth sources to the even and odd form vectors, and a pure-parity ground state turns it into a
  bound on `μ(A)`.
* **The exponent identity** (`polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded`):
  the polar ground-energy exponent equals the zero width.
* **The finite case** (`exists_groundEnergy_exponential_bounds_of_finite_offLine`): when only
  finitely many zeros are off the line, the off-line copies form a finite top layer at depth
  `zetaZeroWidth` and the fall is two-sided, `c e^{2σA} ≤ −μ(A) ≤ C e^{2σA}`.
* **The dichotomy** (`polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster`): the
  exponent equals the width, or the off-line zeros cluster without bound on unit windows; in
  particular a strict inequality forces infinitely many off-line zeros.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.Zeta23 _root_.RHTower _root_.RHTower.CCMParityQuartet
  _root_.RHTower.CCMParityTopLayer

namespace GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### 1. The hypothesis: off-line copies are locally bounded in height -/

/-- At most `M` off-line divisor copies have height within `1` of any `T`. -/
def OffLineCopiesLocallyBounded (M : ℕ) : Prop :=
  ∀ T : ℝ, {q : XiZeroCopy |
    (xiSpectralPoint q).im ≠ 0 ∧ |(xiSpectralPoint q).re - T| ≤ 1}.encard ≤ M

/-- The floor constant `K(M, A) = M (2A + 2π) e^{2π} e^{2σA}` with `σ` the zero width. -/
def clusterFloorConst (M : ℕ) (A : ℝ) : ℝ :=
  M * ((2 * A + 2 * π) * Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A))

theorem clusterFloorConst_nonneg (M : ℕ) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ clusterFloorConst M A := by
  unfold clusterFloorConst; positivity

/-- Every divisor copy is a point of the zeta zero configuration. -/
theorem xiZeroCopy_mem_zetaZeroConfig_carrier (q : XiZeroCopy) :
    (q.1 : ℂ) ∈ zetaZeroConfig.carrier := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have hne : (q.1 : ℂ) ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h1
    exact lt_irrefl _ h1
  exact mem_zetaZeroConfig_of_riemannZeta_eq_zero_of_re_pos
    ((xi_eq_zero_iff h0 hne).mp (xi_eq_zero_of_mem_divisor_support q.1)) h0

/-- The depth of every copy is at most the width. -/
theorem abs_im_xiSpectralPoint_le_zetaZeroWidth (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ zetaZeroWidth := by
  rw [abs_im_xiSpectralPoint_eq]
  exact criticalDepth_le_zetaZeroWidth (xiZeroCopy_mem_zetaZeroConfig_carrier q)

/-! ### 2. The zero-side floor on smooth sources -/

/-- **The off-line copies are paid by the sampling inequality.** For a smooth interior source
`u` at aperture `a`, the source quadratic is at least `−K(M, a) ∫|u|²`. -/
theorem sourceQuadratic_ge_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    -(clusterFloorConst M a.1) * ∫ x, ‖u x‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  classical
  have ha : 0 < a.1 := a.2
  have hI := smoothSource_intervalSource u
  set N := ∫ x, ‖u x‖ ^ 2 with hN
  set K := clusterFloorConst M a.1 with hK
  have hK_eq : K = M * ((2 * a.1 + 2 * π) * Real.exp (2 * π) *
      Real.exp (2 * zetaZeroWidth * a.1)) := rfl
  set T : XiZeroCopy → ℂ := fun q => zeroSumTerm u (xiSpectralPoint q) with hT
  have hsumm : Summable T := summable_zeroSumTerm u
  have hsumm_re : Summable fun q => (T q).re := Complex.reCLM.summable hsumm
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum hsumm]
  -- the local count seen from the heights `−Re z_q`
  have hcount : ∀ (s : Finset XiZeroCopy) (T₀ : ℝ),
      (((s.filter fun q => (xiSpectralPoint q).im ≠ 0) : Set XiZeroCopy) ∩
        {q | |-(xiSpectralPoint q).re - T₀| ≤ 1}).encard ≤ M := by
    intro s T₀
    refine (Set.encard_le_encard ?_).trans (hM (-T₀))
    intro q hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq1
    rw [Set.mem_setOf_eq] at hq2
    refine ⟨hq1.2, ?_⟩
    have e : |-(xiSpectralPoint q).re - T₀| = |(xiSpectralPoint q).re - -T₀| := by
      rw [show -(xiSpectralPoint q).re - T₀ = -((xiSpectralPoint q).re - -T₀) by ring, abs_neg]
    rw [e] at hq2
    exact hq2
  have hdepth : ∀ q : XiZeroCopy, |-(xiSpectralPoint q).im| ≤ zetaZeroWidth := fun q => by
    rw [abs_neg]; exact abs_im_xiSpectralPoint_le_zetaZeroWidth q
  -- the two sampled sums
  have hA : ∀ s : Finset XiZeroCopy,
      ∑ q ∈ s.filter (fun q => (xiSpectralPoint q).im ≠ 0),
        ‖testTransform u (-xiSpectralPoint q)‖ ^ 2 ≤ K * N := by
    intro s
    have h := sum_norm_sq_testTransform_le_of_locallyBounded' ha hI
      (fun q => -(xiSpectralPoint q).re) (fun q => -(xiSpectralPoint q).im)
      zetaZeroWidth_nonneg hdepth (s.filter fun q => (xiSpectralPoint q).im ≠ 0) (hcount s)
    rw [hK_eq, hN]
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 3
    apply Complex.ext <;> simp
  have hB : ∀ s : Finset XiZeroCopy,
      ∑ q ∈ s.filter (fun q => (xiSpectralPoint q).im ≠ 0),
        ‖testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 ≤ K * N := by
    intro s
    have h := sum_norm_sq_testTransform_le_of_locallyBounded' ha hI
      (fun q => -(xiSpectralPoint q).re) (fun q => (xiSpectralPoint q).im)
      zetaZeroWidth_nonneg abs_im_xiSpectralPoint_le_zetaZeroWidth
      (s.filter fun q => (xiSpectralPoint q).im ≠ 0) (hcount s)
    rw [hK_eq, hN]
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 3
    apply Complex.ext <;> simp
  -- the lower family
  set low : XiZeroCopy → ℝ := fun q => if (xiSpectralPoint q).im ≠ 0 then
      -((‖testTransform u (-xiSpectralPoint q)‖ ^ 2 +
        ‖testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) / 2) else 0 with hlow
  have hlow_le : ∀ q, low q ≤ (T q).re := by
    intro q
    simp only [hlow]
    split_ifs with hq
    · have h1 := Complex.abs_re_le_norm (T q)
      have h2 : ‖T q‖ = ‖testTransform u (-xiSpectralPoint q)‖ *
          ‖testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ := by
        simp only [hT, zeroSumTerm, norm_mul, Complex.norm_conj]
      rw [abs_le] at h1
      nlinarith [h1.1, sq_nonneg (‖testTransform u (-xiSpectralPoint q)‖ -
        ‖testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
    · push Not at hq
      exact re_zeroSumTerm_nonneg_of_im_eq_zero _ hq
  have hneg : ∀ q, -low q = if (xiSpectralPoint q).im ≠ 0 then
      (‖testTransform u (-xiSpectralPoint q)‖ ^ 2 +
        ‖testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) / 2 else 0 := by
    intro q
    simp only [hlow]
    split_ifs <;> simp
  have hlow_sum : ∀ s : Finset XiZeroCopy, ∑ q ∈ s, -low q ≤ K * N := by
    intro s
    simp_rw [hneg]
    rw [← Finset.sum_filter, ← Finset.sum_div, Finset.sum_add_distrib]
    have := add_le_add (hA s) (hB s)
    linarith
  have hlow_summ : Summable fun q => -low q :=
    summable_of_sum_le (fun q => by rw [hneg]; split_ifs <;> positivity) hlow_sum
  have hlow_summ' : Summable low := by simpa using hlow_summ.neg
  calc -K * N = -(K * N) := by ring
    _ ≤ -∑' q, -low q := neg_le_neg (hlow_summ.tsum_le_of_sum_le hlow_sum)
    _ = ∑' q, low q := by rw [tsum_neg, neg_neg]
    _ ≤ ∑' q, (T q).re := hlow_summ'.tsum_le_tsum hlow_le hsumm_re

/-- The floor on every pure-parity form vector. -/
theorem sourceQuadratic_ge_of_offLineCopiesLocallyBounded_of_parity {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {a : SuzukiPositiveAperture}
    (w : CCMArchimedeanFormDomain a)
    (hw : ccmArchimedeanFormReflection a w = w ∨ ccmArchimedeanFormReflection a w = -w) :
    -(clusterFloorConst M a.1) * ‖ccmArchimedeanFormToAperture a w‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a w := by
  rcases hw with hw | hw
  · exact floor_of_isEven_of_smooth
      (fun u _ => sourceQuadratic_ge_of_offLineCopiesLocallyBounded hM u) w hw
  · exact floor_of_isOdd_of_smooth
      (fun u _ => sourceQuadratic_ge_of_offLineCopiesLocallyBounded hM u) w hw

/-! ### 3. The ground-energy floor at rate twice the width -/

/-- **The width-to-floor arrow under locally bounded off-line copies.**
`μ(A) ≥ −M (2A + 2π) e^{2π} e^{2·zetaZeroWidth·A}` at every aperture. -/
theorem neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (A : SuzukiPositiveAperture) :
    -(clusterFloorConst M A.1) ≤ ccmRestrictedWeilGroundEnergy A := by
  obtain ⟨f, hf0, hpar, hground⟩ := exists_ccmRestrictedWeil_pureParity_groundFormState A
  have hpos : 0 < ‖ccmArchimedeanFormToAperture A f‖ ^ 2 := by positivity
  have hfl := sourceQuadratic_ge_of_offLineCopiesLocallyBounded_of_parity hM f hpar
  rw [hground] at hfl
  exact le_of_mul_le_mul_right hfl hpos

/-- **Pure exponential floors at every rate above the width.** -/
theorem exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {σ : ℝ} (hσ : zetaZeroWidth < σ) :
    ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
  set ε := σ - zetaZeroWidth with hε
  have hε0 : 0 < ε := by linarith
  refine ⟨M * ((1 / ε + 2 * π) * Real.exp (2 * π)), fun A => ?_⟩
  refine le_trans ?_ (neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy hM A)
  apply neg_le_neg
  have hA : 0 < A.1 := A.2
  have hexp1 : 2 * ε * A.1 + 1 ≤ Real.exp (2 * ε * A.1) := Real.add_one_le_exp _
  have hexp2 : 1 ≤ Real.exp (2 * ε * A.1) := Real.one_le_exp (by positivity)
  have hlin : 2 * A.1 + 2 * π ≤ (1 / ε + 2 * π) * Real.exp (2 * ε * A.1) := by
    have h1 : 2 * A.1 ≤ 1 / ε * Real.exp (2 * ε * A.1) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hε0]
      nlinarith
    nlinarith [Real.pi_pos]
  have hsplit : Real.exp (2 * σ * A.1) = Real.exp (2 * ε * A.1) *
      Real.exp (2 * zetaZeroWidth * A.1) := by
    rw [← Real.exp_add]; congr 1; rw [hε]; ring
  unfold clusterFloorConst
  rw [hsplit]
  have hE := Real.exp_pos (2 * zetaZeroWidth * A.1)
  have hP := Real.exp_pos (2 * π)
  calc (M : ℝ) * ((2 * A.1 + 2 * π) * Real.exp (2 * π) * Real.exp (2 * zetaZeroWidth * A.1))
      ≤ M * (((1 / ε + 2 * π) * Real.exp (2 * ε * A.1)) * Real.exp (2 * π) *
          Real.exp (2 * zetaZeroWidth * A.1)) := by gcongr
    _ = M * ((1 / ε + 2 * π) * Real.exp (2 * π)) *
          (Real.exp (2 * ε * A.1) * Real.exp (2 * zetaZeroWidth * A.1)) := by ring

/-- **The polar ground-energy exponent is the zero width** when the off-line copies are locally
bounded. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) : polarGroundEnergyRate = zetaZeroWidth := by
  refine le_antisymm ?_ zetaZeroWidth_le_polarGroundEnergyRate
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨C, hC⟩ := exists_ccmRestrictedWeilGroundEnergy_ge_neg_exp_of_offLineCopiesLocallyBounded
    hM (show zetaZeroWidth < zetaZeroWidth + ε by linarith)
  refine csInf_le bddBelow_polarGroundEnergyRates
    ⟨by linarith [zetaZeroWidth_nonneg], C, 0, fun A _ => ?_⟩
  exact (hC A).trans (ccmRestrictedWeilGroundEnergy_le_polar A)

/-! ### 4. Finitely many off-line zeros: a finite top layer at the width -/

/-- A point with `|Re z| = t` and `|Im z| = δ` lies on the quartet of `t + iδ`. -/
theorem inQuartet_of_abs_eq {t δ : ℝ} {z : ℂ} (hre : |z.re| = t) (him : |z.im| = δ) :
    InQuartet ((t : ℂ) + δ * I) z := by
  unfold InQuartet
  subst hre
  subst him
  rcases abs_choice z.re with h1 | h1 <;> rcases abs_choice z.im with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (by apply Complex.ext <;> simp)
  · exact Or.inr (Or.inl (by apply Complex.ext <;> simp))
  · exact Or.inr (Or.inr (Or.inr (by apply Complex.ext <;> simp)))
  · exact Or.inr (Or.inr (Or.inl (by apply Complex.ext <;> simp)))

/-- The quartet symmetries produce a copy with spectral point `|Re z| + i|Im z|`. -/
theorem exists_xiZeroCopy_spectralPoint_eq_abs (q : XiZeroCopy) :
    ∃ q' : XiZeroCopy, xiSpectralPoint q' =
      ((|(xiSpectralPoint q).re| : ℝ) : ℂ) + ((|(xiSpectralPoint q).im| : ℝ) : ℂ) * I := by
  rcases abs_choice (xiSpectralPoint q).re with h1 | h1 <;>
    rcases abs_choice (xiSpectralPoint q).im with h2 | h2 <;> rw [h1, h2]
  · exact ⟨q, by apply Complex.ext <;> simp⟩
  · exact ⟨xiZeroCopyLineConjEquiv q, by
      rw [xiSpectralPoint_lineConj]; apply Complex.ext <;> simp⟩
  · exact ⟨xiZeroCopyReflectEquiv (xiZeroCopyLineConjEquiv q), by
      rw [xiSpectralPoint_reflect, xiSpectralPoint_lineConj]; apply Complex.ext <;> simp⟩
  · exact ⟨xiZeroCopyReflectEquiv q, by rw [xiSpectralPoint_reflect]; apply Complex.ext <;> simp⟩

/-- Spectral points have nonzero height (the zeros of `ξ` are not real). -/
theorem xiSpectralPoint_re_ne_zero (q : XiZeroCopy) : (xiSpectralPoint q).re ≠ 0 := by
  intro hq
  have h2 := xiZeroCopy_two_lt_im_sq q
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  rw [hre] at hq
  rw [hq] at h2
  norm_num at h2

/-- **A finite off-line set is a finite top layer at depth `zetaZeroWidth`.** -/
theorem exists_finiteTopLayer_of_finite_offLine
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite)
    (hne : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Nonempty) :
    ∃ (m : ℕ) (t : Fin m → ℝ), FiniteTopLayer zetaZeroWidth t := by
  classical
  set F := h.toFinset with hF
  have hFne : F.Nonempty := h.toFinset_nonempty.mpr hne
  obtain ⟨q₀, hq₀, hmax⟩ := F.exists_max_image (fun q => |(xiSpectralPoint q).im|) hFne
  set δ := |(xiSpectralPoint q₀).im| with hδ
  have hq₀off : (xiSpectralPoint q₀).im ≠ 0 := h.mem_toFinset.mp hq₀
  have hδ0 : 0 < δ := abs_pos.mpr hq₀off
  have hall : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ δ := by
    intro q
    by_cases hq : (xiSpectralPoint q).im = 0
    · rw [hq, abs_zero]; exact hδ0.le
    · exact hmax q (h.mem_toFinset.mpr hq)
  have hδw : δ = zetaZeroWidth := by
    refine le_antisymm ?_ ?_
    · exact abs_im_xiSpectralPoint_le_zetaZeroWidth q₀
    · rw [zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hδ0.le]
      intro ρ hρ
      have hmem := mem_xi_divisor_support_of_eq_zero hρ
      have hpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) ρ) :=
        Int.lt_toNat.mpr (by simpa using xi_divisor_pos_on_support ⟨ρ, hmem⟩)
      have hq := hall ⟨⟨ρ, hmem⟩, ⟨0, hpos⟩⟩
      rw [xiSpectralPoint_im_eq] at hq
      change |1 / 2 - ρ.re| ≤ δ at hq
      have := (abs_le.mp hq).1
      linarith
  rw [← hδw]
  set Ftop := F.filter (fun q => |(xiSpectralPoint q).im| = δ) with hFtop
  set Tset := Ftop.image (fun q => |(xiSpectralPoint q).re|) with hTset
  have hq₀top : q₀ ∈ Ftop := Finset.mem_filter.mpr ⟨hq₀, rfl⟩
  have hTne : Tset.Nonempty := ⟨_, Finset.mem_image.mpr ⟨q₀, hq₀top, rfl⟩⟩
  refine ⟨Tset.card, fun j => Tset.orderEmbOfFin rfl j, ?_⟩
  refine ⟨hδ0, (Tset.orderEmbOfFin rfl).injective, ?_, Finset.card_pos.mpr hTne, h, ?_, ?_⟩
  · intro j
    obtain ⟨q, _, hqe⟩ := Finset.mem_image.mp (Tset.orderEmbOfFin_mem rfl j)
    rw [← hqe]
    exact abs_pos.mpr (xiSpectralPoint_re_ne_zero q)
  · intro q hq
    by_cases hqδ : |(xiSpectralPoint q).im| = δ
    · left
      have hmem : |(xiSpectralPoint q).re| ∈ Tset :=
        Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨h.mem_toFinset.mpr hq, hqδ⟩, rfl⟩
      have hrange : |(xiSpectralPoint q).re| ∈ Set.range (Tset.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hmem
      obtain ⟨j, hj⟩ := hrange
      exact ⟨j, inQuartet_of_abs_eq hj.symm hqδ⟩
    · right
      exact lt_of_le_of_ne (hall q) hqδ
  · intro j
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp (Tset.orderEmbOfFin_mem rfl j)
    have hqδ := (Finset.mem_filter.mp hq).2
    obtain ⟨q', hq'⟩ := exists_xiZeroCopy_spectralPoint_eq_abs q
    refine ⟨q', ?_⟩
    rw [hq', hqe, hqδ]
    rfl

/-- **Finitely many off-line zeros: the fall of the ground energy is exactly twice the width.**
`c e^{2σA} ≤ −μ(A) ≤ C e^{2σA}` for all large `A`, `σ = zetaZeroWidth`. -/
theorem exists_groundEnergy_exponential_bounds_of_finite_offLine
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite)
    (hne : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Nonempty) :
    ∃ c C A : ℝ, 0 < c ∧ ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      c * Real.exp (2 * zetaZeroWidth * a.1) ≤ -ccmRestrictedWeilGroundEnergy a ∧
        -ccmRestrictedWeilGroundEnergy a ≤ C * Real.exp (2 * zetaZeroWidth * a.1) := by
  obtain ⟨m, t, ht⟩ := exists_finiteTopLayer_of_finite_offLine h hne
  exact exists_groundEnergy_exponential_bounds ht

/-- A finite off-line set is locally bounded by its cardinality. -/
theorem offLineCopiesLocallyBounded_of_finite
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    OffLineCopiesLocallyBounded h.toFinset.card := by
  intro T
  calc {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0 ∧ |(xiSpectralPoint q).re - T| ≤ 1}.encard
      ≤ {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard :=
        Set.encard_le_encard fun q hq => hq.1
    _ = h.toFinset.card := h.encard_eq_coe_toFinset_card

/-- With finitely many off-line zeros the polar exponent is the width. -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_of_finite_offLine
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite) :
    polarGroundEnergyRate = zetaZeroWidth :=
  polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded
    (offLineCopiesLocallyBounded_of_finite h)

/-! ### 5. The dichotomy -/

/-- **The exponent is the width, or the off-line zeros cluster.** -/
theorem polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster :
    polarGroundEnergyRate = zetaZeroWidth ∨ ∀ M : ℕ, ¬ OffLineCopiesLocallyBounded M := by
  by_cases h : ∃ M : ℕ, OffLineCopiesLocallyBounded M
  · obtain ⟨M, hM⟩ := h
    exact Or.inl (polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded hM)
  · push Not at h
    exact Or.inr h

/-- A strict inequality between the exponent and the width forces infinitely many off-line
zeros. -/
theorem infinite_offLine_of_zetaZeroWidth_lt_polarGroundEnergyRate
    (hlt : zetaZeroWidth < polarGroundEnergyRate) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite := by
  intro hfin
  exact hlt.ne' (polarGroundEnergyRate_eq_zetaZeroWidth_of_finite_offLine hfin)

/-- **The width reads the ground-energy rate when the off-line zeros do not cluster.** -/
theorem theWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster :
    (∀ M : ℕ, OffLineCopiesLocallyBounded M → ∀ A : SuzukiPositiveAperture,
      -(clusterFloorConst M A.1) ≤ ccmRestrictedWeilGroundEnergy A) ∧
    (∀ M : ℕ, OffLineCopiesLocallyBounded M → polarGroundEnergyRate = zetaZeroWidth) ∧
    (polarGroundEnergyRate = zetaZeroWidth ∨ ∀ M : ℕ, ¬ OffLineCopiesLocallyBounded M) ∧
    (zetaZeroWidth < polarGroundEnergyRate →
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite) :=
  ⟨fun _ hM => neg_clusterFloorConst_le_ccmRestrictedWeilGroundEnergy hM,
    fun _ hM => polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded hM,
    polarGroundEnergyRate_eq_zetaZeroWidth_or_offLineCopies_cluster,
    infinite_offLine_of_zetaZeroWidth_lt_polarGroundEnergyRate⟩

end

end GaloisForLFunctions.SquareRootThreshold
