import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete
import GaloisForLFunctions.RHTower.SoninSemilocalGradingNoGo
import GaloisForLFunctions.RHTower.SoninPhysicalTailVanishing
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.HTGeometry.TwoProjectionDeficiency
import GaloisForLFunctions.HTGeometry.HilbertSchmidtNormComparison

/-!
# Small-cutoff survival of the smoothed semilocal ground row

The archimedean Sonin projection at aperture `a` is the orthogonal projection onto
`ker A_a ∩ ker R_a`, where `A_a` is multiplication by the indicator of `[-a,a]` and `R_a` is its
Fourier conjugate.  Two strong limits control it:

* as `a ↓ 0` the two forbidden subspaces make an angle bounded away from zero — the time--band
  block has Hilbert--Schmidt norm exactly `2a` — so the Friedrichs deficiency bound gives
  `Q_a → 1` strongly;
* as `a → ∞` the Sonin space lies in `ker A_a`, so `‖Q_a g‖ ≤ ‖g − A_a g‖ → 0`.

Combined with the elementary rank-one algebra of the smoothed ground row
`T = −⟨v, ·⟩ p₀`, this shows that the corner `(1 − Q^P) T Q_a` is a nonzero rank-one operator for
every sufficiently small aperture, and that its trace norm tends to zero along the cofinal
large-aperture direction.
-/

namespace RHTower

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The central Sonin carrier as an orthogonal complement -/

theorem centralSoninCarrier_eq_sup_orthogonal (a : ℝ) :
    centralSoninCarrier a
      = (centralPhysicalForbidden a ⊔ centralFourierForbidden a)ᗮ := by
  rw [centralSoninCarrier]
  exact Submodule.inf_orthogonal _ _

theorem starProjection_congr {K L : Submodule ℂ SoninL2} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] (h : K = L) : K.starProjection = L.starProjection := by
  subst h
  rfl

theorem centralSoninProjection_eq_supOrthogonal (a : ℝ) :
    centralSoninProjection a
      = ((centralPhysicalForbidden a ⊔ centralFourierForbidden a)ᗮ).starProjection :=
  starProjection_congr (centralSoninCarrier_eq_sup_orthogonal a)

theorem centralPhysicalForbidden_starProjection (a : ℝ) :
    (centralPhysicalForbidden a).starProjection
      = indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) :=
  (indicatorCutoff_eq_physicalForbidden_starProjection (centralInterval a)
    (measurableSet_centralInterval a)).symm

theorem centralFourierForbidden_starProjection (a : ℝ) :
    (centralFourierForbidden a).starProjection
      = fourierCutoff (centralInterval a) (measurableSet_centralInterval a) :=
  (fourierCutoff_eq_fourierForbidden_starProjection (centralInterval a)
    (measurableSet_centralInterval a)).symm

/-! ## The time--band angle -/

theorem norm_centralForbidden_block_le (a : ℝ) (ha : 0 < a) :
    ‖(centralPhysicalForbidden a).starProjection
      * (centralFourierForbidden a).starProjection‖ ≤ 2 * a := by
  have hHS := isHilbertSchmidt_fourierCutoff_indicatorCutoff_central a a ha
  have harea := hsNormSq_fourierCutoff_indicatorCutoff_central a a ha ha
  have hnorm := ContinuousLinearMap.norm_le_hsNorm hHS
  rw [ContinuousLinearMap.hsNorm, harea] at hnorm
  have hsq : Real.sqrt (4 * a * a) = 2 * a := by
    rw [show (4 : ℝ) * a * a = (2 * a) ^ 2 from by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq] at hnorm
  have hindsa : star (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a))
      = indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) := by
    rw [← centralPhysicalForbidden_starProjection a]
    exact isSelfAdjoint_starProjection (centralPhysicalForbidden a)
  have hfoursa : star (fourierCutoff (centralInterval a) (measurableSet_centralInterval a))
      = fourierCutoff (centralInterval a) (measurableSet_centralInterval a) := by
    rw [← centralFourierForbidden_starProjection a]
    exact isSelfAdjoint_starProjection (centralFourierForbidden a)
  have hadj : (centralPhysicalForbidden a).starProjection
      * (centralFourierForbidden a).starProjection
      = star (fourierCutoff (centralInterval a) (measurableSet_centralInterval a) *
          indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)) := by
    rw [star_mul, hindsa, hfoursa, centralPhysicalForbidden_starProjection,
      centralFourierForbidden_starProjection]
  rw [hadj, norm_star]
  exact hnorm

/-! ## The deficiency of the Sonin projection at small aperture -/

theorem norm_sub_centralSoninProjection_sq_le {a : ℝ} (ha : 0 < a) (hsmall : 2 * a ≤ 1 / 2)
    (g : SoninL2) :
    ‖g - centralSoninProjection a g‖ ^ 2
      ≤ 2 * (‖indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g‖ ^ 2
        + ‖fourierCutoff (centralInterval a) (measurableSet_centralInterval a) g‖ ^ 2) := by
  have hangle := angle_of_norm_starProjection_mul_le
    (U := centralPhysicalForbidden a) (V := centralFourierForbidden a) (c := 1 / 2)
    (le_trans (norm_centralForbidden_block_le a ha) hsmall)
  have hd := norm_sub_intersectionProjection_sq_le (U := centralPhysicalForbidden a)
    (V := centralFourierForbidden a) (by norm_num) (by norm_num) hangle g
  rw [centralPhysicalForbidden_starProjection, centralFourierForbidden_starProjection] at hd
  rw [centralSoninProjection_eq_supOrthogonal]
  refine le_trans hd (le_of_eq ?_)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num]
  field_simp

/-! ## Strong convergence as the aperture shrinks -/

theorem tendsto_norm_indicatorCutoff_of_tendsto_zero (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        ‖indicatorCutoff (centralInterval (R n)) (measurableSet_centralInterval (R n)) g‖)
      atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun n x =>
    ‖(centralInterval (R n)).indicator (fun y : ℝ => (g : ℝ → ℂ) y) x‖ ^ 2 with hF
  have hgint : Integrable (fun x : ℝ => ‖(g : ℝ → ℂ) x‖ ^ 2) volume := by
    have := (Lp.memLp g).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    exact (((Lp.aestronglyMeasurable g).indicator
      (measurableSet_centralInterval (R n))).norm).pow 2
  have hbound : ∀ n : ℕ, ∀ᵐ x : ℝ, ‖F n x‖ ≤ ‖(g : ℝ → ℂ) x‖ ^ 2 := by
    intro n
    filter_upwards with x
    simp only [hF]
    have hnn : (0 : ℝ) ≤ ‖(centralInterval (R n)).indicator
        (fun y : ℝ => (g : ℝ → ℂ) y) x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    by_cases hmem : x ∈ centralInterval (R n)
    · simp [Set.indicator_of_mem hmem]
    · simp [Set.indicator_of_notMem hmem]
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n : ℕ => F n x) atTop (𝓝 (0 : ℝ)) := by
    have hane : ∀ᵐ x : ℝ, x ≠ 0 := by
      have hz : volume ({(0 : ℝ)}) = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hz] with x hx
      simpa using hx
    filter_upwards [hane] with x hx
    have hev : ∀ᶠ n : ℕ in atTop, F n x = 0 := by
      have hpos : (0 : ℝ) < |x| := abs_pos.mpr hx
      have hlt : ∀ᶠ n : ℕ in atTop, R n < |x| := hR.eventually_lt_const hpos
      filter_upwards [hlt] with n hn
      have hnot : x ∉ centralInterval (R n) := by
        intro hmem
        exact absurd (abs_le.mpr hmem) (not_le.mpr hn)
      simp [hF, Set.indicator_of_notMem hnot]
    exact Tendsto.congr' (by filter_upwards [hev] with n hn; rw [hn]) tendsto_const_nhds
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => ‖(g : ℝ → ℂ) x‖ ^ 2) hmeas hgint hbound hlim
  rw [integral_zero] at hdct
  have hsq : Tendsto (fun n : ℕ =>
      ‖indicatorCutoff (centralInterval (R n))
        (measurableSet_centralInterval (R n)) g‖ ^ 2) atTop (𝓝 0) := by
    refine hdct.congr fun n => ?_
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [indicatorCutoff_ae (centralInterval (R n))
      (measurableSet_centralInterval (R n)) g] with x hind
    rw [hF]
    simp only [hind]
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

theorem norm_fourierCutoff_eq (s : Set ℝ) (hs : MeasurableSet s) (g : SoninL2) :
    ‖fourierCutoff s hs g‖ = ‖indicatorCutoff s hs (fourierUnitary g)‖ := by
  rw [fourierCutoff_apply]
  exact LinearIsometryEquiv.norm_map _ _

theorem tendsto_norm_fourierCutoff_of_tendsto_zero (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        ‖fourierCutoff (centralInterval (R n)) (measurableSet_centralInterval (R n)) g‖)
      atTop (𝓝 0) := by
  have h := tendsto_norm_indicatorCutoff_of_tendsto_zero (fourierUnitary g) R hR
  refine h.congr fun n => ?_
  exact (norm_fourierCutoff_eq (centralInterval (R n)) (measurableSet_centralInterval (R n)) g).symm

/-- **Card equation (5).**  The archimedean Sonin projection converges strongly to the identity as
the aperture shrinks. -/
theorem tendsto_norm_sub_centralSoninProjection_of_tendsto_zero (g : SoninL2)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖g - centralSoninProjection (R n) g‖) atTop (𝓝 0) := by
  have h1 := tendsto_norm_indicatorCutoff_of_tendsto_zero g R hR
  have h2 := tendsto_norm_fourierCutoff_of_tendsto_zero g R hR
  have hsq1 : Tendsto (fun n : ℕ =>
      2 * (‖indicatorCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) g‖ ^ 2
        + ‖fourierCutoff (centralInterval (R n))
            (measurableSet_centralInterval (R n)) g‖ ^ 2)) atTop (𝓝 0) := by
    have := ((h1.pow 2).add (h2.pow 2)).const_mul 2
    simpa using this
  have hsmall : ∀ᶠ n : ℕ in atTop, 2 * R n ≤ 1 / 2 := by
    have := hR.eventually_le_const (by norm_num : (0:ℝ) < 1 / 4)
    filter_upwards [this] with n hn
    linarith
  have hsq : Tendsto (fun n : ℕ => ‖g - centralSoninProjection (R n) g‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _)) ?_ hsq1
    filter_upwards [hsmall] with n hn
    exact norm_sub_centralSoninProjection_sq_le (hRpos n) hn g
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

/-! ## Cofinal decay of the Sonin projection -/

theorem norm_centralSoninProjection_le (a : ℝ) (g : SoninL2) :
    ‖centralSoninProjection a g‖
      ≤ ‖g - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g‖ := by
  set Q : SoninL2 := centralSoninProjection a g with hQdef
  have hmem : Q ∈ centralSoninCarrier a := Submodule.starProjection_apply_mem _ _
  have hzero : (inner ℂ Q (g - Q) : ℂ) = 0 :=
    Submodule.sub_starProjection_mem_orthogonal g Q hmem
  have hAQ : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) Q = 0 := by
    rw [centralPhysicalForbidden_starProjection a |>.symm]
    exact (centralPhysicalForbidden a).starProjection_apply_eq_zero_iff.mpr
      (by
        have := hmem
        rw [centralSoninCarrier, Submodule.mem_inf] at this
        exact this.1)
  have hcross : (inner ℂ Q
      (indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g) : ℂ) = 0 := by
    rw [centralPhysicalForbidden_starProjection a |>.symm]
    rw [← Submodule.inner_starProjection_left_eq_right]
    rw [centralPhysicalForbidden_starProjection a, hAQ]
    simp
  have hself : (inner ℂ Q Q : ℂ) = inner ℂ Q
      (g - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g) := by
    have h1 : (inner ℂ Q g : ℂ) = inner ℂ Q Q := by
      have := hzero
      rw [inner_sub_right] at this
      linear_combination this
    rw [inner_sub_right, hcross, ← h1]
    ring
  have hnormsq : (‖Q‖ ^ 2 : ℝ) ≤ ‖Q‖ *
      ‖g - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g‖ := by
    have hval : ((‖Q‖ ^ 2 : ℝ) : ℂ) = inner ℂ Q
        (g - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g) := by
      rw [← hself, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have := norm_inner_le_norm (𝕜 := ℂ) Q
      (g - indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) g)
    rw [← hval] at this
    simpa using this
  rcases eq_or_lt_of_le (norm_nonneg Q) with h0 | h0
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_left (by nlinarith [hnormsq]) h0

/-- **Card equation (7).**  The archimedean Sonin projection converges strongly to zero as the
aperture grows. -/
theorem tendsto_norm_centralSoninProjection_atTop (g : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ => ‖centralSoninProjection (R n) g‖) atTop (𝓝 0) :=
  squeeze_zero (fun _n => norm_nonneg _) (fun n => norm_centralSoninProjection_le (R n) g)
    (tendsto_norm_sub_indicatorCutoff_atTop g R hR)

/-! ## The rank-one smoothed ground row -/

section GroundRow

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The smoothed ground row `T f = −⟪v, f⟫ p₀` of card equation (4). -/
def groundRow (p₀ : K) (v : H) : H →L[ℂ] K := -(InnerProductSpace.rankOne ℂ p₀ v)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem groundRow_apply (p₀ : K) (v : H) (f : H) :
    groundRow p₀ v f = -((inner ℂ v f : ℂ) • p₀) := rfl

omit [CompleteSpace K] in
/-- **Card equation (2).**  The ground projection annihilates the semilocal number operator, so
the first term of `(1)` drops out after left projection. -/
theorem groundProjection_numberOperator_eq_zero {p₀ : K} (N : K →ₗ[ℂ] K)
    (hN : N.IsSymmetric) (hp : N p₀ = 0) (x : K) :
    (inner ℂ p₀ (N x) : ℂ) • p₀ = 0 := by
  rw [← hN p₀ x, hp]
  simp

omit [CompleteSpace H] [CompleteSpace K] in
omit [CompleteSpace H] [CompleteSpace K] in
theorem groundRow_eq_rankOne (p₀ : K) (v : H) :
    groundRow p₀ v = InnerProductSpace.rankOne ℂ (-p₀) v := by
  ext f
  simp [groundRow]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_groundRow (p₀ : K) (v : H) : ‖groundRow p₀ v‖ = ‖p₀‖ * ‖v‖ := by
  rw [groundRow, norm_neg]
  exact InnerProductSpace.norm_rankOne p₀ v

omit [CompleteSpace H] [CompleteSpace K] in
theorem groundRow_ne_zero {p₀ : K} {v : H} (hp : p₀ ≠ 0) (hv : v ≠ 0) :
    groundRow p₀ v ≠ 0 := by
  intro h
  have hn : ‖groundRow p₀ v‖ = 0 := by rw [h, norm_zero]
  rw [norm_groundRow] at hn
  rcases mul_eq_zero.mp hn with h1 | h1
  · exact hp (norm_eq_zero.mp h1)
  · exact hv (norm_eq_zero.mp h1)

omit [CompleteSpace K] in
/-- **Card equation (3).**  The exact Sonin corner of the smoothed ground row is again a ground
row, with output vector `(1 − Q_P) p₀` and input vector `Q_∞ v`. -/
theorem corner_eq (Qp : K →L[ℂ] K) (Qi : H →L[ℂ] H) (hQi : IsSelfAdjoint Qi)
    (p₀ : K) (v : H) :
    ((1 - Qp) ∘L groundRow p₀ v) ∘L Qi = groundRow ((1 - Qp) p₀) (Qi v) := by
  ext f
  have hadj : (inner ℂ (Qi v) f : ℂ) = inner ℂ v (Qi f) := by
    have h := ContinuousLinearMap.adjoint_inner_left Qi f v
    rw [show ContinuousLinearMap.adjoint Qi = Qi from hQi] at h
    exact h
  simp only [ContinuousLinearMap.comp_apply, groundRow_apply, map_neg, map_smul, hadj]

omit [CompleteSpace K] in
theorem norm_corner (Qp : K →L[ℂ] K) (Qi : H →L[ℂ] H) (hQi : IsSelfAdjoint Qi)
    (p₀ : K) (v : H) :
    ‖((1 - Qp) ∘L groundRow p₀ v) ∘L Qi‖ = ‖(1 - Qp) p₀‖ * ‖Qi v‖ := by
  rw [corner_eq Qp Qi hQi p₀ v, norm_groundRow]

omit [CompleteSpace K] in
theorem corner_ne_zero {Qp : K →L[ℂ] K} {Qi : H →L[ℂ] H} (hQi : IsSelfAdjoint Qi)
    {p₀ : K} {v : H} (h1 : (1 - Qp) p₀ ≠ 0) (h2 : Qi v ≠ 0) :
    ((1 - Qp) ∘L groundRow p₀ v) ∘L Qi ≠ 0 := by
  rw [corner_eq Qp Qi hQi p₀ v]
  exact groundRow_ne_zero h1 h2

end GroundRow

/-! ## Survival at small aperture and decay at large aperture -/

theorem isSelfAdjoint_centralSoninProjection (a : ℝ) :
    IsSelfAdjoint (centralSoninProjection a) :=
  isSelfAdjoint_starProjection (centralSoninCarrier a)

/-- **Card (3), small-cutoff survival, abstract form.**  If the smoothed ground row is nonzero and
the semilocal ground state is not Sonin, then the exact Sonin corner is a nonzero rank-one operator
for every sufficiently late member of a family of projections converging strongly to the
identity. -/
theorem eventually_corner_ne_zero_of_tendsto
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Qp : K →L[ℂ] K) (p₀ : K) (v : H) (Q : ℕ → (H →L[ℂ] H))
    (hQ : ∀ n, IsSelfAdjoint (Q n))
    (hlim : Tendsto (fun n : ℕ => ‖v - Q n v‖) atTop (𝓝 0))
    (hp : (1 - Qp) p₀ ≠ 0) (hv : v ≠ 0) :
    ∀ᶠ n in atTop, ((1 - Qp) ∘L groundRow p₀ v) ∘L Q n ≠ 0 := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  filter_upwards [hlim.eventually_lt_const hvpos] with n hn
  refine corner_ne_zero (hQ n) hp ?_
  intro hzero
  rw [hzero, sub_zero] at hn
  exact lt_irrefl _ hn

/-- **Card (8), cofinal decay, abstract form.** -/
theorem tendsto_norm_corner_of_tendsto
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Qp : K →L[ℂ] K) (p₀ : K) (v : H) (Q : ℕ → (H →L[ℂ] H))
    (hQ : ∀ n, IsSelfAdjoint (Q n))
    (hlim : Tendsto (fun n : ℕ => ‖Q n v‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ‖((1 - Qp) ∘L groundRow p₀ v) ∘L Q n‖) atTop (𝓝 0) := by
  have h := hlim.const_mul ‖(1 - Qp) p₀‖
  simp only [mul_zero] at h
  refine h.congr fun n => ?_
  exact (norm_corner Qp (Q n) (hQ n) p₀ v).symm

/-- **Card (3), small-cutoff survival on the archimedean Sonin family.** -/
theorem eventually_corner_ne_zero
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Qp : K →L[ℂ] K) (p₀ : K) (v : SoninL2)
    (hp : (1 - Qp) p₀ ≠ 0) (hv : v ≠ 0)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ((1 - Qp) ∘L groundRow p₀ v) ∘L centralSoninProjection (R n) ≠ 0 :=
  eventually_corner_ne_zero_of_tendsto Qp p₀ v _
    (fun n => isSelfAdjoint_centralSoninProjection (R n))
    (tendsto_norm_sub_centralSoninProjection_of_tendsto_zero v R hRpos hR) hp hv

/-- **Card (8), cofinal decay on the archimedean Sonin family.** -/
theorem tendsto_norm_corner_atTop
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Qp : K →L[ℂ] K) (p₀ : K) (v : SoninL2)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n : ℕ =>
        ‖((1 - Qp) ∘L groundRow p₀ v) ∘L centralSoninProjection (R n)‖) atTop (𝓝 0) :=
  tendsto_norm_corner_of_tendsto Qp p₀ v _
    (fun n => isSelfAdjoint_centralSoninProjection (R n))
    (tendsto_norm_centralSoninProjection_atTop v R hR)

/-! ## The concrete one-prime smoothed ground row -/

/-- The one-prime smoothed ground-row vector `v_P = F_∞ J_P^* p_0^P` in Jacobi coordinates: its
`k`-th coefficient is `2k/(2k+1)` times the ground moment `⟪p_0^P, J_P p_{2k}^∞⟫`. -/
def onePrimeGroundRowVector {p : ℕ} (hp : p.Prime) : lp (fun _ : ℕ => ℂ) 2 :=
  semilocalOnePrimeGroundRowVector p 1
    (summable_norm_sq_semilocalOnePrimeGroundRowCoefficient hp (by norm_num))

theorem semilocalOnePrimeGroundCommutatorRow_one_ne_zero {p : ℕ} (hp : p.Prime) :
    semilocalOnePrimeGroundCommutatorRow p 1 ≠ 0 := by
  obtain ⟨c, C, hc, hcC, hrow⟩ := abs_semilocalOnePrimeGroundCommutatorRow_sharp_order hp
  have h := (hrow 1 (by norm_num)).1
  rw [Nat.cast_one, Real.one_rpow, mul_one] at h
  intro hzero
  rw [hzero, abs_zero] at h
  linarith

theorem onePrimeGroundRowVector_ne_zero {p : ℕ} (hp : p.Prime) :
    onePrimeGroundRowVector hp ≠ 0 := by
  intro hzero
  have hval : ((onePrimeGroundRowVector hp : ℕ → ℂ) 1) = 0 := by
    rw [hzero]
    rfl
  have hcoe : ((onePrimeGroundRowVector hp : ℕ → ℂ) 1)
      = (semilocalOnePrimeGroundRowCoefficient p 1 1 : ℂ) := rfl
  rw [hcoe] at hval
  have hreal : semilocalOnePrimeGroundRowCoefficient p 1 1 = 0 := by
    have := congrArg Complex.re hval
    simpa using this
  rw [semilocalOnePrimeGroundRowCoefficient] at hreal
  have h3 : (((2 * 1 + 1 : ℕ) : ℝ)) ^ (-(1 : ℝ)) ≠ 0 := by
    have hpos : (0:ℝ) < (((2 * 1 + 1 : ℕ) : ℝ)) ^ (-(1 : ℝ)) := by
      apply Real.rpow_pos_of_pos
      norm_num
    exact ne_of_gt hpos
  rcases mul_eq_zero.mp hreal with h | h
  · exact semilocalOnePrimeGroundCommutatorRow_one_ne_zero hp h
  · exact h3 h

/-- **Card equation (4) and the nonvanishing of `T_P`.**  The one-prime smoothed ground row is a
nonzero rank-one operator. -/
theorem onePrimeGroundRow_ne_zero {p : ℕ} (hp : p.Prime) :
    groundRow ((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)) (onePrimeGroundRowVector hp) ≠ 0 := by
  refine groundRow_ne_zero ?_ (onePrimeGroundRowVector_ne_zero hp)
  intro h
  have hval : (((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ) 0) = 0 := by rw [h]; rfl
  rw [lp.single_apply] at hval
  simp at hval

/-- The one-prime smoothed ground row is trace class, for the strongest possible reason: it is
rank one. -/
theorem onePrimeGroundRow_isTraceClass {p : ℕ} (hp : p.Prime) :
    ContinuousLinearMap.IsTraceClass
      (groundRow ((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)) (onePrimeGroundRowVector hp)) := by
  rw [groundRow_eq_rankOne]
  exact isTraceClass_rankOne_lp _ _

/-- Every exact Sonin corner of a ground row in the Jacobi model is again trace class. -/
theorem groundRow_corner_isTraceClass
    (Qp : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (Qi : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) (hQi : IsSelfAdjoint Qi)
    (p₀ v : lp (fun _ : ℕ => ℂ) 2) :
    ContinuousLinearMap.IsTraceClass (((1 - Qp) ∘L groundRow p₀ v) ∘L Qi) := by
  rw [corner_eq Qp Qi hQi p₀ v, groundRow_eq_rankOne]
  exact isTraceClass_rankOne_lp _ _

/-! ## The finite-prime-set smoothed ground row -/

/-- The `k`-th coefficient of the smoothed ground-row vector of a finite prime family:
`2k/(2k+1)` times the ground moment `⟪p_0^P, J_P p_{2k}^∞⟫`. -/
def finitePrimeGroundRowCoefficient {n : ℕ} (P : Fin (n + 1) → ℕ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ) / (2 * (k : ℝ) + 1)) * semilocalFinitePrimeEvenJacobiMoment k P

/-- The smoothed ground-row vector `v_P = F_∞ J_P^* p_0^P` of a finite prime family.  Its
square-summability is exactly the statement that `J_P^* p_0^P` lies in the archimedean space, i.e.
the boundedness of `J_P` assumed in the source construction. -/
def finitePrimeGroundRowVector {n : ℕ} (P : Fin (n + 1) → ℕ)
    (h : Summable fun k : ℕ => ‖((finitePrimeGroundRowCoefficient P k : ℝ) : ℂ)‖ ^ 2) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun k => ((finitePrimeGroundRowCoefficient P k : ℝ) : ℂ),
    HilbertSchmidt.memℓp_of_sq h⟩

/-- **The smoothed ground row is nonzero for every finite nonempty prime set.**  Its first
coefficient is `−(2/3)` times the alternating all-even ground residue. -/
theorem finitePrimeGroundRowVector_ne_zero {n : ℕ} (P : Fin (n + 1) → ℕ)
    (hP : Function.Injective P) (hprime : ∀ i, (P i).Prime)
    (h : Summable fun k : ℕ => ‖((finitePrimeGroundRowCoefficient P k : ℝ) : ℂ)‖ ^ 2) :
    finitePrimeGroundRowVector P h ≠ 0 := by
  have hmom := semilocalFinitePrimeEvenJacobiMoment_signed_pos (k := 1) P hP hprime
  have hne : semilocalFinitePrimeEvenJacobiMoment 1 P ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmom
    exact lt_irrefl _ hmom
  intro hzero
  have hval : ((finitePrimeGroundRowVector P h : ℕ → ℂ) 1) = 0 := by
    rw [hzero]
    rfl
  have hcoe : ((finitePrimeGroundRowVector P h : ℕ → ℂ) 1)
      = ((finitePrimeGroundRowCoefficient P 1 : ℝ) : ℂ) := rfl
  rw [hcoe] at hval
  have hreal : finitePrimeGroundRowCoefficient P 1 = 0 := by
    have := congrArg Complex.re hval
    simpa using this
  rw [finitePrimeGroundRowCoefficient] at hreal
  rcases mul_eq_zero.mp hreal with hfac | hfac
  · norm_num at hfac
  · exact hne hfac

/-- The finite-prime smoothed ground row is a nonzero trace-class rank-one operator. -/
theorem finitePrimeGroundRow_ne_zero {n : ℕ} (P : Fin (n + 1) → ℕ)
    (hP : Function.Injective P) (hprime : ∀ i, (P i).Prime)
    (h : Summable fun k : ℕ => ‖((finitePrimeGroundRowCoefficient P k : ℝ) : ℂ)‖ ^ 2) :
    groundRow ((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2))
        (finitePrimeGroundRowVector P h) ≠ 0 := by
  refine groundRow_ne_zero ?_ (finitePrimeGroundRowVector_ne_zero P hP hprime h)
  intro hz
  have hval : (((lp.single 2 0 (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ) 0) = 0 := by
    rw [hz]; rfl
  rw [lp.single_apply] at hval
  simp at hval

/-! ## The card's theorem -/

/-- **Small-cutoff survival of the smoothed semilocal ground row.**  Whenever the semilocal ground
state is not Sonin and the smoothed ground-row vector is nonzero, the exact Sonin corner of the
smoothed ground row is a nonzero rank-one operator at every sufficiently small aperture, while its
norm tends to zero along the cofinal large-aperture direction. -/
theorem smallCutoff_groundRow_survival
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (Qp : K →L[ℂ] K) (p₀ : K) (v : SoninL2)
    (hp : (1 - Qp) p₀ ≠ 0) (hv : v ≠ 0)
    (R S : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop (𝓝 0))
    (hS : Tendsto S atTop atTop) :
    (∀ᶠ n in atTop, ((1 - Qp) ∘L groundRow p₀ v) ∘L centralSoninProjection (R n) ≠ 0)
      ∧ Tendsto (fun n : ℕ =>
          ‖((1 - Qp) ∘L groundRow p₀ v) ∘L centralSoninProjection (S n)‖) atTop (𝓝 0) :=
  ⟨eventually_corner_ne_zero Qp p₀ v hp hv R hRpos hR,
    tendsto_norm_corner_atTop Qp p₀ v S hS⟩

end

end RHTower
