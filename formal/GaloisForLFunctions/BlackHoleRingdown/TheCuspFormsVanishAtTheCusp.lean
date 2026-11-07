import GaloisForLFunctions.RHTower.DeckCuspidalFourierExpansion
import GaloisForLFunctions.RHTower.DeckCuspEigenvalueNonneg
import GaloisForLFunctions.RHTower.DeckConstantCuspidalOrthogonal
import GaloisForLFunctions.RHTower.HyperbolicAbelTransformHorocyclicSlice
import GaloisForLFunctions.RHTower.SelbergConjectureSmallLevel

/-!
# The cusp forms of the modular horizon vanish at the cusp

A square-integrable cuspidal Laplace eigenfunction `U` on `PSL₂(ℤ)\ℍ` tends to zero at the cusp, so it is a
genuine Maass cusp form, and Selberg's bound gives `λ ≥ ¼`.

The decay is elementary. `U` is a fixed multiple of a point-pair average of itself. Along a horocycle `U` is
periodic with mean zero, so its primitive is bounded by the `L¹` norm over a period, and integrating by parts
trades `U` for the `x`-derivative of the kernel `φ(u)`. With `u = ((x-x₀)² + (y-y₀)²)/(4y₀y)` that derivative
is `≲ X/(y₀y)` on `|x - x₀| ≤ X = √(4Ry₀y)`, so its `L¹` norm is `≲ R`, uniformly in the heights. The kernel
vanishes for `y ≤ y₀/(4R+3)`. Therefore `‖U(z)‖ ≲ ∫_{y₀/(4R+3)}^∞ y⁻² ‖U(·, y)‖_{L¹} dy`, the tail of a
convergent integral.

The eigenvalue `0` is excluded directly: the point-pair average of a unit profile fixes `U`, ergodicity makes
`U` constant, and a constant vanishing at the cusp is zero.
-/

open Complex MeasureTheory Set Filter Topology
open scoped MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.DeckPointPair
  GaloisForLFunctions.HTGeometry MaassFiniteDeckDirichlet SelbergMaassCongruenceTrace
  SelbergSmallLevel
open UpperHalfPlane (ofComplex ofComplex_apply_of_im_pos atImInfty)

/-! ### Integration by parts along a horocycle -/

/-- **Integration by parts against a mean-zero periodic function.** -/
theorem norm_integral_mul_le_of_mean_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hmean : ∫ x in (0 : ℝ)..1, f x = 0) {g g' : ℝ → ℂ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') {a X K : ℝ} (hX : 0 ≤ X)
    (hgs : ∀ x, X < |x - a| → g x = 0) (hgs' : ∀ x, X < |x - a| → g' x = 0)
    (hK : ∀ x, |x - a| ≤ X → ‖g' x‖ ≤ K) :
    ‖∫ x, g x * f x‖ ≤ 2 * X * K * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  set V : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, f t with hV
  have hVd : ∀ x, HasDerivAt V (f x) x := fun x => (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hVc : Continuous V := continuous_iff_continuousAt.mpr fun x => (hVd x).continuousAt
  have hVper : Function.Periodic V 1 := fun x => by
    have h1 : ∫ t in x..x + 1, f t = 0 := by
      rw [hper.intervalIntegral_add_eq x 0, zero_add, hmean]
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 x) (hf.intervalIntegrable x (x + 1))
    simp only [hV]
    rw [← h2, h1, add_zero]
  have hnorm : Continuous fun x => ‖f x‖ := hf.norm
  have hVb : ∀ x, ‖V x‖ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ := fun x => by
    obtain ⟨x', hx', hVx⟩ := hVper.exists_mem_Ico₀ one_pos x
    rw [hVx]
    have h1 : ‖V x'‖ ≤ ∫ t in (0 : ℝ)..x', ‖f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx'.1
    exact h1.trans (intervalIntegral.integral_mono_interval (μ := volume) le_rfl hx'.1 hx'.2.le
      (Eventually.of_forall fun t => norm_nonneg _) (hnorm.intervalIntegrable _ _))
  have hout : ∀ x, x ∉ Icc (a - X) (a + X) → X < |x - a| := fun x hx => by
    by_contra h
    push Not at h
    exact hx (mem_Icc.mpr ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)
  have hin : ∀ x ∈ Icc (a - X) (a + X), |x - a| ≤ X := fun x hx =>
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hgcs : HasCompactSupport g :=
    HasCompactSupport.intro isCompact_Icc fun x hx => hgs x (hout x hx)
  have hg'cs : HasCompactSupport g' :=
    HasCompactSupport.intro isCompact_Icc fun x hx => hgs' x (hout x hx)
  have i1 : Integrable (g * f) := (hgc.mul hf).integrable_of_hasCompactSupport hgcs.mul_right
  have i2 : Integrable (g' * V) := (hg'.mul hVc).integrable_of_hasCompactSupport hg'cs.mul_right
  have i3 : Integrable (g * V) := (hgc.mul hVc).integrable_of_hasCompactSupport hgcs.mul_right
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hg x) (fun x _ => hVd x)
    i1 i2 i3
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK a (by simpa using hX))
  have hset : ∫ x in Icc (a - X) (a + X), g' x * V x = ∫ x, g' x * V x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hgs' x (hout x hx)]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (a - X) (a + X))
    (f := fun x => g' x * V x) (C := K * ∫ x in (0 : ℝ)..1, ‖f x‖)
    (by simp) (fun x hx => by
      rw [norm_mul]
      exact mul_le_mul (hK x (hin x hx)) (hVb x) (norm_nonneg _) hK0)
  rw [hparts, norm_neg, ← hset]
  refine hb.trans (le_of_eq ?_)
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

/-! ### The kernel in horocyclic coordinates -/

/-- The point-pair invariant in horocyclic coordinates. -/
def horoU (x₀ y₀ y x : ℝ) : ℝ := ((x₀ - x) ^ 2 + (y₀ - y) ^ 2) / (4 * y₀ * y)

theorem pairU_ofComplex (z : UpperHalfPlane) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    pairU z (ofComplex ⟨x, y⟩) = horoU z.re z.im y x := by
  rw [ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
  show dist (z : ℂ) (⟨x, y⟩ : ℂ) ^ 2 / (4 * z.im * y) = _
  rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, horoU]
  have e1 : ((z : ℂ) - (⟨x, y⟩ : ℂ)).re = z.re - x := by rw [Complex.sub_re]; rfl
  have e2 : ((z : ℂ) - (⟨x, y⟩ : ℂ)).im = z.im - y := by rw [Complex.sub_im]; rfl
  rw [e1, e2]
  ring

theorem hasDerivAt_horoU (x₀ : ℝ) {y₀ y : ℝ} (h₀ : 0 < y₀) (hy : 0 < y) (x : ℝ) :
    HasDerivAt (horoU x₀ y₀ y) ((x - x₀) / (2 * y₀ * y)) x := by
  have h1 : HasDerivAt (fun x => (x₀ - x) ^ 2 + (y₀ - y) ^ 2) (2 * (x₀ - x) * (-1)) x := by
    have := (((hasDerivAt_id x).const_sub x₀).pow 2).add_const ((y₀ - y) ^ 2)
    simpa using this
  refine (h1.div_const (4 * y₀ * y)).congr_deriv ?_
  field_simp
  ring

/-- Outside the width `X² = 4Ry₀y` the invariant exceeds `R`. -/
theorem lt_horoU_of_width {R X x₀ y₀ y x : ℝ} (h₀ : 0 < y₀) (hy : 0 < y) (hX0 : 0 ≤ X)
    (hX : X ^ 2 = 4 * R * y₀ * y) (hx : X < |x - x₀|) : R < horoU x₀ y₀ y x := by
  have h4 : 0 < 4 * y₀ * y := by positivity
  rw [horoU, lt_div_iff₀ h4]
  have h1 : X ^ 2 < (x₀ - x) ^ 2 := by
    rw [← sq_abs (x₀ - x), abs_sub_comm]
    exact pow_lt_pow_left₀ hx hX0 two_ne_zero
  nlinarith [sq_nonneg (y₀ - y)]

/-- Below the height `y₀/(4R+3)` the invariant exceeds `R`. -/
theorem lt_horoU_of_low {R y₀ y : ℝ} (h₀ : 0 < y₀) (hy : 0 < y)
    (hlow : (4 * R + 3) * y ≤ y₀) (x₀ x : ℝ) : R < horoU x₀ y₀ y x := by
  have h4 : 0 < 4 * y₀ * y := by positivity
  rw [horoU, lt_div_iff₀ h4]
  have h1 : y₀ * ((4 * R + 3) * y) ≤ y₀ * y₀ := mul_le_mul_of_nonneg_left hlow h₀.le
  have h2 : 0 < y₀ * y := mul_pos h₀ hy
  nlinarith [sq_nonneg (x₀ - x), sq_nonneg y]

/-- **The uniform estimate along one horocycle.** -/
theorem norm_horocycle_integral_le (P : SmoothProfile) {f : ℝ → ℂ} (hf : Continuous f)
    (hper : Function.Periodic f 1) (hmean : ∫ x in (0 : ℝ)..1, f x = 0) (x₀ : ℝ) {y₀ y : ℝ}
    (h₀ : 0 < y₀) (hy : 0 < y) :
    ‖∫ x, ((P.toFun (horoU x₀ y₀ y x) : ℝ) : ℂ) * f x‖ ≤
      4 * P.radius * P.pp.derivBound * ∫ x in (0 : ℝ)..1, ‖f x‖ := by
  have hR := P.radius_nonneg
  set X : ℝ := Real.sqrt (4 * P.radius * y₀ * y) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = 4 * P.radius * y₀ * y := Real.sq_sqrt (by positivity)
  set φ := P.toFun with hφ
  have hφd : Differentiable ℝ φ := P.pp.differentiable
  have hφ'c : Continuous (deriv φ) := P.pp.continuous_deriv
  have hbd : ∀ u, |deriv φ u| ≤ P.pp.derivBound := P.pp.abs_deriv_le
  have hM : 0 ≤ P.pp.derivBound := (abs_nonneg _).trans (hbd 0)
  have hud : ∀ x, HasDerivAt (horoU x₀ y₀ y) ((x - x₀) / (2 * y₀ * y)) x :=
    hasDerivAt_horoU x₀ h₀ hy
  have huc : Continuous (horoU x₀ y₀ y) :=
    continuous_iff_continuousAt.mpr fun x => (hud x).continuousAt
  have hg : ∀ x, HasDerivAt (fun x => ((φ (horoU x₀ y₀ y x) : ℝ) : ℂ))
      (((deriv φ (horoU x₀ y₀ y x) * ((x - x₀) / (2 * y₀ * y)) : ℝ) : ℂ)) x := fun x =>
    (((hφd _).hasDerivAt).comp x (hud x)).ofReal_comp
  have hg'c : Continuous fun x : ℝ =>
      ((deriv φ (horoU x₀ y₀ y x) * ((x - x₀) / (2 * y₀ * y)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hφ'c.comp huc).mul (by fun_prop))
  have hzero : ∀ x, X < |x - x₀| → P.radius < horoU x₀ y₀ y x := fun x hx =>
    lt_horoU_of_width h₀ hy hX0 hX2 hx
  have hmain := norm_integral_mul_le_of_mean_zero hf hper hmean hg hg'c (a := x₀) (X := X)
    (K := P.pp.derivBound * (X / (2 * y₀ * y))) hX0
    (fun x hx => by
      have := P.kernelSupport _ (hzero x hx)
      simp only [hφ, this, Complex.ofReal_zero])
    (fun x hx => by
      have h1 : P.radius < |horoU x₀ y₀ y x| := (hzero x hx).trans_le (le_abs_self _)
      have := deriv_eq_zero_of_abs_support P.support h1
      simp only [hφ, this, zero_mul, Complex.ofReal_zero])
    (fun x hx => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_pos (by positivity : 0 < 2 * y₀ * y)]
      exact mul_le_mul (hbd _) (div_le_div_of_nonneg_right hx (by positivity))
        (by positivity) hM)
  refine hmain.trans (le_of_eq ?_)
  have hne : y₀ * y ≠ 0 := by positivity
  have hkey : 2 * X * (P.pp.derivBound * (X / (2 * y₀ * y))) =
      4 * P.radius * P.pp.derivBound := by
    have : 2 * X * (P.pp.derivBound * (X / (2 * y₀ * y))) =
        P.pp.derivBound * X ^ 2 / (y₀ * y) := by
      field_simp
    rw [this, hX2]
    field_simp
  rw [hkey]

/-- Tails of an integrable function tend to zero. -/
theorem tendsto_integral_Ioi_atTop {W : ℝ → ℝ} {a : ℝ} (hW : IntegrableOn W (Ioi a)) :
    Tendsto (fun T => ∫ y in Ioi T, W y) atTop (𝓝 0) := by
  have h1 := intervalIntegral_tendsto_integral_Ioi a hW tendsto_id
  have h2 := (tendsto_const_nhds (x := ∫ y in Ioi a, W y)).sub h1
  rw [sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  have := intervalIntegral.integral_interval_add_Ioi hW (hW.mono_set (Ioi_subset_Ioi hT))
  simp only [id]
  linarith

/-! ### Decay -/

section Decay

variable {lam : ℝ} {U : UpperHalfPlane → DeckSpace 0}

theorem chart_point (x y : ℝ) : SelbergMaassMean.point x y = (⟨x, y⟩ : ℂ) := by
  apply Complex.ext <;> simp [SelbergMaassMean.point]

theorem continuous_of_cuspEigen (hU : IsCuspLaplaceEigen 0 lam U) : Continuous U :=
  continuous_of_isChartC1 (formPreDomain.c1 hU.toPre)

theorem continuous_slice {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => (ofComplex (⟨x, y⟩ : ℂ) : UpperHalfPlane) := by
  simpa only [chart_point] using continuous_ofComplex_point hy

/-- At level one the eigenfunction is periodic. -/
theorem periodic_slice (hU : IsCuspLaplaceEigen 0 lam U) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x : ℝ => U (ofComplex (⟨x, y⟩ : ℂ))) 1 := fun x => by
  ext q
  have h := hU.component_periodic q hy x
  simp only [Function.comp_apply, chart_point, Nat.cast_one, zero_add, component] at h
  exact h

/-- At level one every horocycle mean vanishes. -/
theorem mean_slice (hU : IsCuspLaplaceEigen 0 lam U) (q : Deck 0) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..1, U (ofComplex (⟨x, y⟩ : ℂ)) q = 0 := by
  have h := hU.levelCuspZero q hy 0
  simp only [chart_point, Nat.cast_one, zero_add] at h
  exact h

/-- The weight of the tail. -/
def cuspTail (U : UpperHalfPlane → DeckSpace 0) (y : ℝ) : ℝ :=
  (y ^ 2)⁻¹ * ∫ x in (0 : ℝ)..1, ‖U (ofComplex (⟨x, y⟩ : ℂ))‖

theorem integrableOn_inv_sq : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi 1) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := 1) one_pos
  refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  simp only
  rw [Real.rpow_neg hy0.le]
  norm_num

theorem integrableOn_cuspTail (hU : IsCuspLaplaceEigen 0 lam U) :
    IntegrableOn (cuspTail U) (Ioi 1) := by
  have hUc := continuous_of_cuspEigen hU
  have hsq := DeckPointPair.IsCuspLaplaceEigen.mem_cuspidalFormPreDomain hU
  have hrect := MaassFiniteDeckDirichlet.cusp_value_weighted_integrable
    (⟨U, hsq⟩ : cuspidalFormPreDomain 0) le_rfl
  have hmono : IntegrableOn (fun p : ℝ × ℝ => ‖U (ofComplex (⟨p.1, p.2⟩ : ℂ))‖ * (p.2 ^ 2)⁻¹)
      (_root_.RHTower.cuspRect 1) volume := by
    have hbound : IntegrableOn (fun p : ℝ × ℝ =>
        ‖U (ofComplex (SelbergMaassMean.point p.1 p.2))‖ ^ (2 : ℕ) / p.2 ^ (2 : ℕ) + (p.2 ^ 2)⁻¹)
        (_root_.RHTower.cuspRect 1) volume := by
      refine hrect.add ?_
      have hfin : IntegrableOn (fun _ : ℝ => (1 : ℝ)) _root_.RHTower.unitIcc :=
        integrableOn_const (by simp [_root_.RHTower.unitIcc])
      have := (hfin.mul_prod integrableOn_inv_sq)
      rw [Measure.prod_restrict] at this
      rw [Measure.volume_eq_prod]
      simpa [_root_.RHTower.cuspRect, IntegrableOn] using this
    refine Integrable.mono' hbound ?_ ?_
    · refine (ContinuousOn.aestronglyMeasurable ?_ (_root_.RHTower.measurableSet_cuspRect 1))
      have hy : ∀ p ∈ _root_.RHTower.cuspRect 1, (0 : ℝ) < p.2 := fun p hp =>
        lt_trans one_pos hp.2
      have hco : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) :=
        Complex.equivRealProdCLM.symm.continuous
      have hch : ContinuousOn (fun p : ℝ × ℝ => U (ofComplex (⟨p.1, p.2⟩ : ℂ)))
          (_root_.RHTower.cuspRect 1) :=
        hU.contDiffOn.continuousOn.comp hco.continuousOn fun p hp => hy p hp
      refine hch.norm.mul ?_
      refine ContinuousOn.inv₀ (by fun_prop) fun p hp => pow_ne_zero 2 (hy p hp).ne'
    · refine (ae_restrict_iff' (_root_.RHTower.measurableSet_cuspRect 1)).mpr
        (Eventually.of_forall fun p hp => ?_)
      have hy : (0 : ℝ) < p.2 := lt_trans one_pos hp.2
      have hinv : 0 ≤ (p.2 ^ 2)⁻¹ := by positivity
      rw [Real.norm_of_nonneg (by positivity), chart_point, div_eq_mul_inv]
      nlinarith [sq_nonneg (‖U (ofComplex (⟨p.1, p.2⟩ : ℂ))‖ - 1), norm_nonneg (U (ofComplex (⟨p.1, p.2⟩ : ℂ)))]
  rw [IntegrableOn, Measure.volume_eq_prod, _root_.RHTower.cuspRect, ← Measure.prod_restrict] at hmono
  have hfib := hmono.integral_prod_right
  refine (hfib.congr ?_)
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  simp only [cuspTail]
  rw [integral_mul_const, mul_comm]
  congr 1
  rw [_root_.RHTower.unitIcc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have hp : Function.Periodic (fun x : ℝ => ‖U (ofComplex (⟨x, y⟩ : ℂ))‖) 1 := fun x => by
    simp only [periodic_slice hU hy0 x]
  have := hp.intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at this
  norm_num
  exact this

/-- **The pointwise bound by the tail.** -/
theorem exists_norm_component_le_tail (hU : IsCuspLaplaceEigen 0 lam U) (q : Deck 0) :
    ∃ C c : ℝ, 0 ≤ C ∧ 1 ≤ c ∧ ∀ z : UpperHalfPlane, c ≤ z.im →
      ‖U z q‖ ≤ C * ∫ y in Ioi (z.im / c), cuspTail U y := by
  obtain ⟨P, h, hh, hPU⟩ := hU.exists_selberg_rep
  have hR := P.radius_nonneg
  have hM : 0 ≤ P.pp.derivBound := (abs_nonneg _).trans (P.pp.abs_deriv_le 0)
  have hUc := continuous_of_cuspEigen hU
  have hφc : Continuous P.toFun := P.pp.differentiable.continuous
  set c : ℝ := 4 * P.radius + 3 with hc
  have hc0 : 0 < c := by positivity
  have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  refine ⟨‖h‖⁻¹ * (4 * P.radius * P.pp.derivBound), c, by positivity, by rw [hc]; linarith,
    fun z hz => ?_⟩
  set y₀ := z.im with hy₀
  have h₀ : 0 < y₀ := z.im_pos
  set T := y₀ / c with hT
  have hT1 : 1 ≤ T := by rw [hT, one_le_div hc0]; exact hz
  have hT0 : 0 < T := by linarith
  set F : UpperHalfPlane → ℂ := fun w => ((P.toFun (pairU z w) : ℝ) : ℂ) * U w q with hF
  have hint := integrable_pairKernel_smul hφc P.kernelSupport hUc z
  have hFi : Integrable F := by
    have := (EuclideanSpace.proj q : DeckSpace 0 →L[ℂ] ℂ).integrable_comp hint
    exact this
  have hval : h * U z q = ∫ w, F w := by
    have h1 := hPU z
    rw [ppApply_eq_integral hφc P.kernelSupport hUc hU.equivariant] at h1
    have h2 := (EuclideanSpace.proj q : DeckSpace 0 →L[ℂ] ℂ).integral_comp_comm hint
    have h3 : (EuclideanSpace.proj q : DeckSpace 0 →L[ℂ] ℂ) (h • U z) = h * U z q := rfl
    rw [← h3, ← h1, ← h2]
    rfl
  rw [MehlerFock.integral_upperHalfPlane_eq_iterated F hFi] at hval
  set Φ : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • ∫ x : ℝ, F (ofComplex (⟨x, y⟩ : ℂ)) with hΦ
  have hslice : ∀ x y : ℝ, 0 < y → F (ofComplex (⟨x, y⟩ : ℂ)) =
      ((P.toFun (horoU z.re y₀ y x) : ℝ) : ℂ) * U (ofComplex (⟨x, y⟩ : ℂ)) q := fun x y hy => by
    simp only [hF]
    rw [pairU_ofComplex z x hy]
  have hlow : ∀ y ∈ Ioi (0 : ℝ) \ Ioi T, Φ y = 0 := fun y hy => by
    have hy0 : 0 < y := hy.1
    have hyT : y ≤ T := not_lt.mp hy.2
    have hle : c * y ≤ y₀ := by
      have := mul_le_mul_of_nonneg_left hyT hc0.le
      rwa [hT, mul_div_cancel₀ _ hc0.ne'] at this
    have h0 : ∀ x, F (ofComplex (⟨x, y⟩ : ℂ)) = 0 := fun x => by
      rw [hslice x y hy0, P.kernelSupport _ (lt_horoU_of_low h₀ hy0 hle _ _)]
      simp
    simp [hΦ, h0]
  have hset : ∫ y in Ioi (0 : ℝ), Φ y = ∫ y in Ioi T, Φ y :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi hT0.le) hlow
  have htail : IntegrableOn (cuspTail U) (Ioi T) :=
    (integrableOn_cuspTail hU).mono_set (Ioi_subset_Ioi hT1)
  have hbound : ∀ y ∈ Ioi T, ‖Φ y‖ ≤ 4 * P.radius * P.pp.derivBound * cuspTail U y := fun y hy => by
    have hy0 : 0 < y := hT0.trans hy
    have hfc : Continuous fun x : ℝ => U (ofComplex (⟨x, y⟩ : ℂ)) q :=
      (PiLp.continuous_apply 2 _ q).comp (hUc.comp (continuous_slice hy0))
    have hfper : Function.Periodic (fun x : ℝ => U (ofComplex (⟨x, y⟩ : ℂ)) q) 1 := fun x => by
      simp only [periodic_slice hU hy0 x]
    have hin := norm_horocycle_integral_le P hfc hfper (mean_slice hU q hy0) z.re h₀ hy0
    have hmono : ∫ x in (0 : ℝ)..1, ‖U (ofComplex (⟨x, y⟩ : ℂ)) q‖ ≤
        ∫ x in (0 : ℝ)..1, ‖U (ofComplex (⟨x, y⟩ : ℂ))‖ :=
      intervalIntegral.integral_mono_on (by norm_num) (hfc.norm.intervalIntegrable _ _)
        ((hUc.comp (continuous_slice hy0)).norm.intervalIntegrable _ _)
        fun x _ => PiLp.norm_apply_le _ q
    have heq : ∫ x : ℝ, F (ofComplex (⟨x, y⟩ : ℂ)) =
        ∫ x : ℝ, ((P.toFun (horoU z.re y₀ y x) : ℝ) : ℂ) * U (ofComplex (⟨x, y⟩ : ℂ)) q :=
      integral_congr_ae (Eventually.of_forall fun x => hslice x y hy0)
    simp only [hΦ]
    rw [norm_smul, heq, Real.norm_of_nonneg (by positivity), cuspTail]
    have hinv : 0 ≤ (y ^ 2)⁻¹ := by positivity
    calc (y ^ 2)⁻¹ * ‖∫ x : ℝ, ((P.toFun (horoU z.re y₀ y x) : ℝ) : ℂ) * U (ofComplex (⟨x, y⟩ : ℂ)) q‖
        ≤ (y ^ 2)⁻¹ * (4 * P.radius * P.pp.derivBound *
            ∫ x in (0 : ℝ)..1, ‖U (ofComplex (⟨x, y⟩ : ℂ))‖) :=
          mul_le_mul_of_nonneg_left (hin.trans (mul_le_mul_of_nonneg_left hmono (by positivity))) hinv
      _ = _ := by ring
  have hest : ‖∫ y in Ioi T, Φ y‖ ≤ ∫ y in Ioi T, 4 * P.radius * P.pp.derivBound * cuspTail U y :=
    norm_integral_le_of_norm_le (htail.const_mul _)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  rw [integral_const_mul] at hest
  have h5 : ‖h‖ * ‖U z q‖ ≤ 4 * P.radius * P.pp.derivBound * ∫ y in Ioi T, cuspTail U y := by
    rw [← norm_mul, hval, hset]
    exact hest
  calc ‖U z q‖ = ‖h‖⁻¹ * (‖h‖ * ‖U z q‖) := by field_simp
    _ ≤ ‖h‖⁻¹ * (4 * P.radius * P.pp.derivBound * ∫ y in Ioi T, cuspTail U y) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring

/-- **Cuspidal eigenfunctions vanish at the cusp.** -/
theorem tendsto_component_atImInfty (hU : IsCuspLaplaceEigen 0 lam U) (q : Deck 0) :
    Tendsto (fun z => U z q) atImInfty (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hb⟩ := exists_norm_component_le_tail hU q
  have hc0 : 0 < c := by linarith
  have him : Tendsto (fun z : UpperHalfPlane => z.im) atImInfty atTop := tendsto_comap
  have hT : Tendsto (fun z : UpperHalfPlane => z.im / c) atImInfty atTop :=
    him.atTop_div_const hc0
  have htail := (tendsto_integral_Ioi_atTop (integrableOn_cuspTail hU)).comp hT
  have hlim := htail.const_mul C
  rw [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [him.eventually_ge_atTop c] with z hz
  exact hb z hz

end Decay

/-! ### The bridge to Selberg -/

section Bridge

variable {lam : ℝ} {U : UpperHalfPlane → DeckSpace 0}

instance subsingleton_deck_zero : Subsingleton (Deck 0) := by
  refine ⟨fun a b => ?_⟩
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      refine QuotientGroup.eq.2 ?_
      show a⁻¹ * b ∈ CongruenceSubgroup.Gamma 1
      rw [CongruenceSubgroup.Gamma_one_top]
      trivial

/-- `U` is invariant under the modular group. -/
theorem component_smul (hU : IsCuspLaplaceEigen 0 lam U) (q : Deck 0) (A : SL(2, ℤ))
    (z : UpperHalfPlane) : U (A • z) q = U z q := by
  have hq : q * (QuotientGroup.mk A : Deck 0) = q := Subsingleton.elim _ _
  rw [hU.equivariant A z, finiteRegularUnitary_apply, hq]

/-- A nonzero cuspidal eigenfunction at level one is a Maass cusp form. -/
def toMaassCuspEigenform (hU : IsCuspLaplaceEigen 0 lam U) (q : Deck 0) (hne : ∃ z, U z ≠ 0) :
    MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) lam := by
  refine ⟨⟨fun z => U z q, ?_⟩, ?_, hU.isMaassEigenfunction_component q, ?_⟩
  · rintro ⟨γ, A, -, rfl⟩ z
    exact component_smul hU q A z
  · intro h0
    obtain ⟨z, hz⟩ := hne
    apply hz
    ext q'
    have := congrFun (congrArg Subtype.val h0) z
    rw [Subsingleton.elim q' q]
    simpa using this
  · intro σ
    have heq : (fun z : UpperHalfPlane => U (integralSL2ToReal σ • z) q) = fun z => U z q := by
      funext z
      exact component_smul hU q σ z
    show Tendsto _ _ _
    rw [heq]
    exact tendsto_component_atImInfty hU q

theorem exists_ne_zero_of_toDeckL2_ne (hU : IsCuspLaplaceEigen 0 lam U)
    (h0 : toDeckL2 U hU.memLp ≠ 0) : ∃ z, U z ≠ 0 := by
  by_contra h
  push Not at h
  apply h0
  have hz : U = 0 := funext h
  subst hz
  exact (MemLp.toLp_zero _).trans rfl

/-- **The eigenvalue `0` does not occur.** -/
theorem lam_ne_zero (hU : IsCuspLaplaceEigen 0 lam U) (hne : ∃ z, U z ≠ 0) : lam ≠ 0 := by
  rintro rfl
  obtain ⟨P, hP0, hPm, hPpos⟩ := exists_posUnitProfile (R := 1) one_pos
  have hc : Continuous P.toFun := P.contDiff.continuous
  have hUc := continuous_of_cuspEigen hU
  have hS : selbergTransform P.toFun 0 = 1 := by
    have h1 := integral_pairKernel hc hP0 hPm UpperHalfPlane.I
    rw [selbergTransform]
    simp only [HyperbolicPowerEigen.powerEigen, cpow_zero, mul_one]
    have hco : (∫ w : UpperHalfPlane, ((P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ)) =
        ((∫ w : UpperHalfPlane, P.toFun (pairU UpperHalfPlane.I w) : ℝ) : ℂ) := integral_ofReal
    rw [hco, h1, Complex.ofReal_one]
  have hfix : ∀ z, ppApply P.toFun U z = U z := fun z => by
    rw [ppApply_eigen hc P.kernelSupport hU.contDiffOn hU.equivariant (s := 0) (fun z => by
      rw [hU.eigen z]
      simp) z, hS, one_smul]
  have hconst := eq_of_ppApply_eq_self hc P.kernelSupport hP0 hPm one_pos hPpos hUc hU.equivariant
    hU.memLp hfix
  obtain ⟨z, hz⟩ := hne
  apply hz
  ext q
  have hlim := tendsto_component_atImInfty hU q
  have hev : (fun w => U w q) = fun _ => U z q := by
    funext w
    rw [hconst w z]
  rw [hev] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- **Selberg's bound for the modular horizon.** -/
theorem one_quarter_le_of_cuspEigen (hU : IsCuspLaplaceEigen 0 lam U)
    (h0 : toDeckL2 U hU.memLp ≠ 0) : 1 / 4 ≤ lam := by
  have hne := exists_ne_zero_of_toDeckL2_ne hU h0
  have hnn := hU.lam_nonneg h0
  have hz := lam_ne_zero hU hne
  by_contra hlt
  push Not at hlt
  have hq : Deck 0 := QuotientGroup.mk 1
  exact (no_exceptional_of_principal_le (Γ := CongruenceSubgroup.Gamma 1) (N := 1) le_rfl
    (by norm_num) le_rfl ⟨lt_of_le_of_ne hnn hz.symm, hlt⟩).false (toMaassCuspEigenform hU hq hne)

/-- **Every eigenvalue of the level-one cuspidal basis is at least `¼`.** -/
theorem one_quarter_le_cuspEigenBasis (i : CuspEigenIndex 0) : 1 / 4 ≤ i.1 := by
  obtain ⟨U, hU, hUb⟩ := cuspEigenBasis_spec i
  refine one_quarter_le_of_cuspEigen hU ?_
  rw [← hUb]
  intro h0
  have h1 := (cuspEigenBasis 0).orthonormal.1 i
  have h2 : (cuspEigenBasis 0 i : CuspidalL2 0) = 0 := Subtype.ext h0
  rw [h2, norm_zero] at h1
  exact zero_ne_one h1

end Bridge

end GaloisForLFunctions.BlackHoleRingdown

end
