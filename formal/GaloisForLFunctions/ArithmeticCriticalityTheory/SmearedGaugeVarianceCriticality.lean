import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormJumpKernelGaugeFreedom
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThetaConvolutionCoshMomentLaw
import GaloisForLFunctions.HTGeometry.NavierStokesHadamardQuotient

/-!
# The variance is indispensable: criticality of the pure-jump form in every smeared gauge

In a smeared shifted ground state `M = ∫ ν(c) m_c dc` (`ν ≥ 0` smooth, supported in `(0, ∞)`) RH is
the pure-jump inequality `J_M(u) + V_μ(u) ≥ 0` for every even `u ∈ C²_c`, `μ = M sinh(x/2)`
(`riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`). The variance term cannot be reduced
(`exists_zeroForm_lt_mul_varianceEnergy`): for every `ε > 0` some even `u ∈ C²_c` has

    Z(Φ(ω_ν u)) = J_M(u) + V_μ(u) < ε V_μ(u),

so `J_M + (1 − ε) V_μ` takes negative values; in particular the signed jump energy `J_M` alone is
negative somewhere, unconditionally (`exists_signedJumpEnergy_neg`). No positive odd gauge of this kind
makes the conductance form positive: the all-pairs variance carries positivity that the jumps lack.

Proof. A pole-free pair `M'` (`σ = 0`) has plateau truncations `M' u_L` with zero form `→ 0`. In the
gauge `M` they are `M · (w u_L)` with `w = M'/M`, smooth through the origin because `M'(0) = M(0) = 0`
and `M'(0) > 0` (Hadamard division; `M'(0) = 2 ∫ ν (−Φ') > 0` by strict monotonicity of `Φ`). The
quotient `w` is not constant on `(0, ∞)`, since `M' = cM` would force `0 = σ' = c B/2`, and the
variance of `w u_L` stays above the variance of `w` on a fixed window.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open GaloisForLFunctions.HTGeometry.Interfinity GaloisForLFunctions.HTGeometry.NavierStokesHadamardQuotient

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The derivative of Riemann's kernel -/

theorem deriv_riemannKernelReal_neg (c : ℝ) :
    deriv riemannKernelReal (-c) = -deriv riemannKernelReal c := by
  have h := deriv_comp_neg riemannKernelReal c
  have e : (fun x => riemannKernelReal (-x)) = riemannKernelReal := funext riemannKernelReal_neg'
  rw [e] at h
  linarith

theorem deriv_riemannKernelReal_nonpos {c : ℝ} (hc : 0 ≤ c) : deriv riemannKernelReal c ≤ 0 := by
  have h := hasDerivAt_riemannKernelReal c
  rw [← h.deriv] at h
  refine le_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have := riemannKernelReal_antitone_of_nonneg hc (show c ≤ c + t by linarith)
  simp only [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht0.le) (by linarith)

theorem riemannKernelReal_lt_of_lt {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) :
    riemannKernelReal q < riemannKernelReal p := by
  have h := shiftDifference_pos (a := (q - p) / 2) (x := (p + q) / 2) (by linarith) (by linarith)
  unfold shiftDifference at h
  rw [show (p + q) / 2 - (q - p) / 2 = p by ring, show (p + q) / 2 + (q - p) / 2 = q by ring] at h
  linarith

/-- On every interval of the half line `Φ'` is somewhere negative. -/
theorem exists_deriv_riemannKernelReal_neg {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) :
    ∃ ξ ∈ Ioo p q, deriv riemannKernelReal ξ < 0 := by
  obtain ⟨ξ, hξ, hd⟩ := exists_deriv_eq_slope riemannKernelReal hpq
    continuous_riemannKernelReal.continuousOn
    (fun y _ => (hasDerivAt_riemannKernelReal y).differentiableAt.differentiableWithinAt)
  refine ⟨ξ, hξ, ?_⟩
  rw [hd]
  exact div_neg_of_neg_of_pos (by linarith [riemannKernelReal_lt_of_lt hp hpq]) (by linarith)

/-! ### Smoothness and the slope at the origin -/

theorem isSmoothReal_thetaConv {φ : ℝ → ℝ} (hφ : IsSmoothReal φ) (hφc : HasCompactSupport φ) :
    IsSmoothReal (thetaConv φ) := fun n => by
  rw [thetaConv_eq_convolution]
  exact hφc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (n := n) (hφ n)
    integrable_riemannKernelReal.locallyIntegrable

theorem isSmoothReal_spanShiftDifference {ι : Type*} (s : Finset ι) (c a : ι → ℝ) :
    IsSmoothReal (spanShiftDifference s c a) := fun n => by
  unfold spanShiftDifference shiftDifference
  exact ContDiff.sum fun j _ => contDiff_const.mul
    ((contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
      (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const)))

/-- The slope of a smeared shifted ground state at the origin: `M'(0) = 2 ∫ ν (−Φ') > 0`. -/
theorem deriv_thetaConv_smearedProfile_zero_pos {ν : ℝ → ℝ} (hν : ContDiff ℝ 1 ν)
    (hνc : HasCompactSupport ν) (hν0 : ∀ b, 0 ≤ ν b) (hνpos : ∀ b, b ≤ 0 → ν b = 0) {b₀ : ℝ}
    (hb₀ : 0 < ν b₀) : 0 < deriv (thetaConv (smearedProfile ν)) 0 := by
  set φ := smearedProfile ν with hφ_def
  have hφ : ContDiff ℝ 1 φ := hν.sub (hν.comp contDiff_neg)
  have hφc : HasCompactSupport φ := hνc.sub (hνc.comp_homeomorph (Homeomorph.neg ℝ))
  rw [(hasDerivAt_thetaConv hφ hφc 0).deriv]
  have hb₀pos : 0 < b₀ := by
    by_contra h
    rw [hνpos b₀ (not_lt.mp h)] at hb₀
    exact lt_irrefl _ hb₀
  -- integration by parts: `∫ φ' Φ = −∫ φ Φ'`
  have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    (hφ.differentiable one_ne_zero x).hasDerivAt
  have hΦd : ∀ x, HasDerivAt riemannKernelReal (deriv riemannKernelReal x) x := fun x => by
    have h := hasDerivAt_riemannKernelReal x
    rwa [← h.deriv] at h
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hΦ'c : Continuous (deriv riemannKernelReal) :=
    contDiff_riemannKernelReal.continuous_deriv le_rfl
  have hi1 : Integrable (riemannKernelReal * deriv φ) :=
    (hφ'c.mul continuous_riemannKernelReal).integrable_of_hasCompactSupport (hφc.deriv.mul_right)
      |>.congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hi2 : Integrable (deriv riemannKernelReal * φ) :=
    (hΦ'c.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hlim : ∀ l : Filter ℝ, l ≤ cocompact ℝ → Tendsto (riemannKernelReal * φ) l (𝓝 0) := by
    intro l hl
    refine tendsto_nhds_of_eventually_eq ?_
    have hcs : HasCompactSupport (riemannKernelReal * φ) := hφc.mul_left
    have hmem : (tsupport (riemannKernelReal * φ))ᶜ ∈ l := hl hcs.isCompact.compl_mem_cocompact
    exact Filter.mem_of_superset hmem fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hIBP := integral_mul_deriv_eq_deriv_mul (fun x _ => hΦd x) (fun x _ => hφd x) hi1 hi2
    (hlim atBot atBot_le_cocompact) (hlim atTop atTop_le_cocompact)
  have hconv : thetaConv (deriv φ) 0 = ∫ x, riemannKernelReal x * deriv φ x := by
    unfold thetaConv
    exact integral_congr_ae (Eventually.of_forall fun b => by
      simp only
      rw [zero_sub, riemannKernelReal_neg']
      ring)
  rw [hconv, hIBP, sub_zero, zero_sub]
  -- `−∫ Φ' φ = 2 ∫ ν (−Φ')`
  have hνi : Integrable fun c => deriv riemannKernelReal c * ν c :=
    (hΦ'c.mul hν.continuous).integrable_of_hasCompactSupport hνc.mul_left
  have hνi' : Integrable fun c => deriv riemannKernelReal c * ν (-c) :=
    (hΦ'c.mul (hν.continuous.comp continuous_neg)).integrable_of_hasCompactSupport
      (hνc.comp_homeomorph (Homeomorph.neg ℝ)).mul_left
  have hsplit : (∫ x, deriv riemannKernelReal x * φ x) =
      2 * ∫ c, deriv riemannKernelReal c * ν c := by
    have e : (fun x => deriv riemannKernelReal x * φ x) =
        fun x => deriv riemannKernelReal x * ν x - deriv riemannKernelReal x * ν (-x) :=
      funext fun x => by simp only [hφ_def, smearedProfile]; ring
    have h2 : (∫ c, deriv riemannKernelReal c * ν (-c)) = -∫ c, deriv riemannKernelReal c * ν c := by
      rw [← integral_neg_eq_self (fun c => deriv riemannKernelReal c * ν (-c)) volume, ← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun c => by
        simp only [neg_neg, deriv_riemannKernelReal_neg]; ring)
    rw [e, integral_sub hνi hνi', h2]
    ring
  rw [hsplit]
  -- positivity of `∫ ν (−Φ')`
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hν.continuous.continuousAt (ν b₀ / 2)
    (by linarith)
  obtain ⟨ξ, hξ, hd⟩ := exists_deriv_riemannKernelReal_neg (p := b₀) (q := b₀ + δ / 2)
    hb₀pos.le (by linarith)
  have hνξ : 0 < ν ξ := by
    have h := hball (show dist ξ b₀ < δ by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hξ.1, hξ.2])
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  have hpos : 0 < ∫ c, ν c * -deriv riemannKernelReal c := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ξ)
      (hν.continuous.mul hΦ'c.neg) hνc.mul_right (fun c => ?_) (mul_pos hνξ (by linarith)).ne'
    show (0 : ℝ) ≤ ν c * -deriv riemannKernelReal c
    rcases le_or_gt c 0 with hc | hc
    · rw [hνpos c hc, zero_mul]
    · exact mul_nonneg (hν0 c) (by linarith [deriv_riemannKernelReal_nonpos hc.le])
  have e : (∫ c, ν c * -deriv riemannKernelReal c) = -∫ c, deriv riemannKernelReal c * ν c := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun c => by simp only; ring)
  linarith

/-! ### Division by the gauge -/

theorem smoothCoordinateQuotient_neg_of_odd {h : ℝ → ℝ} (hh : IsSmoothReal h)
    (hodd : ∀ x, h (-x) = -h x) (y : ℝ) :
    smoothCoordinateQuotient h (-y) = smoothCoordinateQuotient h y := by
  have h0 : h 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  rcases eq_or_ne y 0 with rfl | hy
  · rw [neg_zero]
  · rw [smoothCoordinateQuotient_eq_div hh h0 hy, smoothCoordinateQuotient_eq_div hh h0 (neg_ne_zero.mpr hy),
      hodd, neg_div_neg_eq]

/-- The inner variance integral: `∫ (u(x) − u(y))² μ(x)μ(y) dy = μ(x)(u(x)² ∫μ − 2u(x) ∫uμ + ∫u²μ)`. -/
theorem integral_sq_sub_mul_mul_eq {μ u : ℝ → ℝ} (hμ : Integrable μ) (hu : Continuous u) {Z : ℝ}
    (hZ : ∀ x, |u x| ≤ Z) (x : ℝ) :
    (∫ y, (u x - u y) ^ 2 * (μ x * μ y)) = μ x * (u x ^ 2 * (∫ y, μ y) -
      2 * u x * (∫ y, u y * μ y) + ∫ y, u y ^ 2 * μ y) := by
  have h1 : Integrable fun y => u y * μ y :=
    hμ.bdd_mul hu.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hZ y)
  have h2 : Integrable fun y => u y ^ 2 * μ y :=
    hμ.bdd_mul (hu.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZ y) 2)
  have e : (fun y => (u x - u y) ^ 2 * (μ x * μ y)) = fun y =>
      (μ x * u x ^ 2) * μ y - (2 * μ x * u x) * (u y * μ y) + μ x * (u y ^ 2 * μ y) :=
    funext fun y => by ring
  have i1 : Integrable fun y => (μ x * u x ^ 2) * μ y := hμ.const_mul _
  have i2 : Integrable fun y => (2 * μ x * u x) * (u y * μ y) := h1.const_mul _
  have i3 : Integrable fun y => μ x * (u y ^ 2 * μ y) := h2.const_mul _
  have i12 : Integrable fun y => (μ x * u x ^ 2) * μ y - (2 * μ x * u x) * (u y * μ y) := i1.sub i2
  rw [e, integral_add i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

/-- **Window lower bound for the variance energy.** For `μ ≥ 0` integrable and `u` bounded continuous,
`V_μ(u) ≥ ∫_W ∫_W (u(x) − u(y))² μ(x)μ(y)` for every `W = [p, q]`. -/
theorem setIntegral_setIntegral_le_varianceEnergy {μ u : ℝ → ℝ} (hμ : Integrable μ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμc : Continuous μ) (hu : Continuous u) {Z : ℝ}
    (hZ : ∀ x, |u x| ≤ Z) (p q : ℝ) :
    (∫ x in Icc p q, ∫ y in Icc p q, (u x - u y) ^ 2 * (μ x * μ y)) ≤ varianceEnergy μ u := by
  have h1 : Integrable fun y => u y * μ y :=
    hμ.bdd_mul hu.aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hZ y)
  have h2 : Integrable fun y => u y ^ 2 * μ y :=
    hμ.bdd_mul (hu.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hZ y) 2)
  have hinner : ∀ x, Integrable fun y => (u x - u y) ^ 2 * (μ x * μ y) := fun x => by
    have e : (fun y => (u x - u y) ^ 2 * (μ x * μ y)) = fun y =>
        (μ x * u x ^ 2) * μ y - (2 * μ x * u x) * (u y * μ y) + μ x * (u y ^ 2 * μ y) :=
      funext fun y => by ring
    rw [e]
    exact ((hμ.const_mul _).sub (h1.const_mul _)).add (h2.const_mul _)
  have hnn : ∀ x y, 0 ≤ (u x - u y) ^ 2 * (μ x * μ y) := fun x y =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (hμ0 x) (hμ0 y))
  have houter : Integrable fun x => ∫ y, (u x - u y) ^ 2 * (μ x * μ y) := by
    have e : (fun x => ∫ y, (u x - u y) ^ 2 * (μ x * μ y)) = fun x =>
        (∫ y, μ y) * (u x ^ 2 * μ x) - (2 * ∫ y, u y * μ y) * (u x * μ x) +
          (∫ y, u y ^ 2 * μ y) * μ x := funext fun x => by
      rw [integral_sq_sub_mul_mul_eq hμ hu hZ x]; ring
    rw [e]
    exact ((h2.const_mul _).sub (h1.const_mul _)).add (hμ.const_mul _)
  unfold varianceEnergy
  calc (∫ x in Icc p q, ∫ y in Icc p q, (u x - u y) ^ 2 * (μ x * μ y))
      ≤ ∫ x in Icc p q, ∫ y, (u x - u y) ^ 2 * (μ x * μ y) := by
        refine setIntegral_mono_on ?_ houter.integrableOn measurableSet_Icc fun x _ =>
          setIntegral_le_integral (hinner x) (Eventually.of_forall fun y => hnn x y)
        have hc : Continuous fun x => ∫ y in Icc p q, (u x - u y) ^ 2 * (μ x * μ y) :=
          continuous_parametric_integral_of_continuous
            (((hu.comp continuous_fst).sub (hu.comp continuous_snd)).pow 2 |>.mul
              ((hμc.comp continuous_fst).mul (hμc.comp continuous_snd))) isCompact_Icc
        exact hc.integrableOn_Icc
    _ ≤ ∫ x, ∫ y, (u x - u y) ^ 2 * (μ x * μ y) :=
        setIntegral_le_integral houter (Eventually.of_forall fun x =>
          integral_nonneg fun y => hnn x y)

/-! ### Variance criticality -/

section Smeared

variable {ν : ℝ → ℝ} (hν : IsSmoothReal ν) (hνc : HasCompactSupport ν) (hν0 : ∀ b, 0 ≤ ν b)
  (hνpos : ∀ b, b ≤ 0 → ν b = 0) {b₀ : ℝ} (hb₀ : 0 < ν b₀)
include hν hνc hν0 hνpos hb₀

/-- **The variance cannot be reduced.** In the smeared gauge `M = ∫ ν(c) m_c dc`, for every `ε > 0`
some even `u ∈ C²_c` has `Z(Φ(ω_ν u)) < ε V_μ(u)`, `μ = M sinh(x/2)`. -/
theorem exists_zeroForm_lt_mul_varianceEnergy {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      zeroForm (phiDoobTest fun y => convGauge (smearedProfile ν) y * u y) <
        ε * varianceEnergy (fun x => thetaConv (smearedProfile ν) x * Real.sinh (x / 2)) u := by
  set φ := smearedProfile ν with hφ_def
  have hφs : IsSmoothReal φ := fun n => (hν n).sub ((hν n).comp contDiff_neg)
  have hφ : ContDiff ℝ 2 φ := hφs 2
  have hφc : HasCompactSupport φ := hνc.sub (hνc.comp_homeomorph (Homeomorph.neg ℝ))
  have hodd : ∀ b, φ (-b) = -φ b := smearedProfile_neg ν
  set M := thetaConv φ with hM_def
  have hMs : IsSmoothReal M := isSmoothReal_thetaConv hφs hφc
  have hMpos : ∀ x, 0 < x → 0 < M x := fun x hx =>
    thetaConv_smearedProfile_pos (hν 0).continuous hνc hν0 hνpos hb₀ hx
  have hModd : ∀ x, M (-x) = -M x := thetaConv_neg_of_odd hodd
  have hM0 : M 0 = 0 := by have := hModd 0; rw [neg_zero] at this; linarith
  have hnn : ∀ x, 0 < x → 0 ≤ M x := fun x hx => (hMpos x hx).le
  have hQpos : ∀ y, 0 < smoothCoordinateQuotient M y := fun y => by
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [smoothCoordinateQuotient_eq_div hMs hM0 hy.ne]
      have := hMpos (-y) (by linarith)
      rw [hModd] at this
      exact div_pos_of_neg_of_neg (by linarith) hy
    · rw [smoothCoordinateQuotient_zero]
      exact deriv_thetaConv_smearedProfile_zero_pos (hν 1) hνc hν0 hνpos hb₀
    · rw [smoothCoordinateQuotient_eq_div hMs hM0 hy.ne']
      exact div_pos (hMpos y hy) hy
  have hMne : ∀ y, y ≠ 0 → M y ≠ 0 := fun y hy h => by
    have := hQpos y
    rw [smoothCoordinateQuotient_eq_div hMs hM0 hy, h, zero_div] at this
    exact lt_irrefl _ this
  -- the null direction and its quotient by the gauge
  obtain ⟨n, hn⟩ := exists_nat_nullPair_ne_zero (x := 1) one_ne_zero
  set c := nullPairCoeff (n : ℝ)
  set a := nullPairShift (n : ℝ)
  set M' := spanShiftDifference Finset.univ c a with hM'_def
  have hM's : IsSmoothReal M' := isSmoothReal_spanShiftDifference _ _ _
  have hM'odd : ∀ x, M' (-x) = -M' x := spanShiftDifference_neg _ _ _
  have hM'0 : M' 0 = 0 := by have := hM'odd 0; rw [neg_zero] at this; linarith
  set w : ℝ → ℝ := fun y => smoothCoordinateQuotient M' y / smoothCoordinateQuotient M y
    with hw_def
  have hws : IsSmoothReal w := (smooth_smoothCoordinateQuotient hM's).div
    (smooth_smoothCoordinateQuotient hMs) fun y => (hQpos y).ne'
  have hweven : ∀ y, w (-y) = w y := fun y => by
    simp only [hw_def, smoothCoordinateQuotient_neg_of_odd hM's hM'odd,
      smoothCoordinateQuotient_neg_of_odd hMs hModd]
  have hMw : ∀ y, M y * w y = M' y := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · rw [hM0, hM'0, zero_mul]
    · simp only [hw_def]
      rw [smoothCoordinateQuotient_eq_div hM's hM'0 hy, smoothCoordinateQuotient_eq_div hMs hM0 hy]
      have := hMne y hy
      field_simp
  -- the quotient is not constant on the half line
  have hnonconst : ∃ p₀ q₀ : ℝ, 0 < p₀ ∧ p₀ < q₀ ∧ w p₀ ≠ w q₀ := by
    by_contra hcon
    have hcon' : ∀ p₀ q₀ : ℝ, 0 < p₀ → p₀ < q₀ → w p₀ = w q₀ := fun p₀ q₀ h1 h2 => by
      by_contra h3
      exact hcon ⟨p₀, q₀, h1, h2, h3⟩
    have hconst : ∀ x, 0 < x → w x = w 1 := fun x hx => by
      rcases lt_trichotomy x 1 with h | rfl | h
      · exact hcon' x 1 hx h
      · rfl
      · exact (hcon' 1 x one_pos h).symm
    have hMM : ∀ x, M' x = w 1 * M x := fun x => by
      rcases lt_trichotomy x 0 with h | rfl | h
      · rw [← neg_neg x, hM'odd, hModd, ← hMw (-x), hconst (-x) (by linarith)]
        ring
      · rw [hM'0, hM0, mul_zero]
      · rw [← hMw x, hconst x h]
        ring
    have h1 : (∫ x, M' x * Real.sinh (x / 2)) = 0 := by
      rw [hM'_def, integral_spanShiftDifference_mul_sinh_half, spanSourceCoefficient_nullPair]
    have h2 : (∫ x, M x * Real.sinh (x / 2)) = convSinhCoefficient φ / 2 :=
      integral_thetaConv_mul_sinh_half hφ hφc
    have hB : 0 < convSinhCoefficient φ :=
      convSinhCoefficient_pos hφ hφc hodd hnn one_pos (hMpos 1 one_pos)
    have h3 : (∫ x, M' x * Real.sinh (x / 2)) = w 1 * ∫ x, M x * Real.sinh (x / 2) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hMM x]; ring)
    rw [h1, h2] at h3
    have hw1 : w 1 = 0 := by
      rcases mul_eq_zero.mp h3.symm with h | h
      · exact h
      · linarith
    apply hn
    show M' 1 = 0
    rw [hMM 1, hw1, zero_mul]
  obtain ⟨p₀, q₀, hp₀, hpq, hwne⟩ := hnonconst
  -- the variance density
  set μ : ℝ → ℝ := fun x => M x * Real.sinh (x / 2) with hμ_def
  have hMc : Continuous M := (hMs 0).continuous
  have hμc : Continuous μ := hMc.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hμ0 : ∀ x, 0 ≤ μ x := fun x => by
    rcases lt_trichotomy x 0 with h | rfl | h
    · have h1 := hMpos (-x) (by linarith)
      rw [hModd] at h1
      have h2 : Real.sinh (x / 2) < 0 := Real.sinh_neg_iff.mpr (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) h2.le
    · simp [hμ_def, hM0]
    · exact mul_nonneg (hMpos x h).le (Real.sinh_nonneg_iff.mpr (by linarith))
  have hμi : Integrable μ := by
    obtain ⟨C, hC0, hCb⟩ := exists_abs_thetaConv_le_of_continuous hφ.continuous hφc
    refine (integrable_exp_neg_eight_mul_abs.const_mul C).mono' hμc.aestronglyMeasurable
      (Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, hμ_def, abs_mul]
    have hs : |Real.sinh (r / 2)| ≤ Real.exp (8 * |r|) :=
      (abs_sinh_le_exp_abs _).trans (exp_abs_half_le_exp_eight r)
    have he : Real.exp (-(24 * |r|)) * Real.exp (8 * |r|) ≤ Real.exp (-(8 * |r|)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [abs_nonneg r])
    calc |M r| * |Real.sinh (r / 2)| ≤ (C * Real.exp (-(24 * |r|))) * Real.exp (8 * |r|) :=
          mul_le_mul (hCb r) hs (abs_nonneg _) (by positivity)
      _ = C * (Real.exp (-(24 * |r|)) * Real.exp (8 * |r|)) := by ring
      _ ≤ C * Real.exp (-(8 * |r|)) := mul_le_mul_of_nonneg_left he hC0
  -- the window energy of the quotient
  set p := p₀ / 2
  set q := q₀ + 1
  have hwc : Continuous w := (hws 0).continuous
  set g : ℝ → ℝ → ℝ := fun x y => (w x - w y) ^ 2 * (μ x * μ y) with hg_def
  have hgc : Continuous (Function.uncurry g) :=
    (((hwc.comp continuous_fst).sub (hwc.comp continuous_snd)).pow 2).mul
      ((hμc.comp continuous_fst).mul (hμc.comp continuous_snd))
  have hg0 : ∀ x y, 0 ≤ g x y := fun x y => mul_nonneg (sq_nonneg _) (mul_nonneg (hμ0 x) (hμ0 y))
  set G : ℝ → ℝ := fun x => ∫ y in Icc p q, g x y with hG_def
  have hGc : Continuous G := continuous_parametric_integral_of_continuous hgc isCompact_Icc
  have hμp : 0 < μ p₀ := mul_pos (hMpos p₀ hp₀) (Real.sinh_pos_iff.mpr (by linarith))
  have hμq : 0 < μ q₀ := mul_pos (hMpos q₀ (by linarith)) (Real.sinh_pos_iff.mpr (by linarith))
  have hGp : 0 < G p₀ := by
    have hgx : Continuous (g p₀) := hgc.comp (continuous_const.prodMk continuous_id)
    show 0 < ∫ y in Icc p q, g p₀ y
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (hg0 p₀)) hgx.integrableOn_Icc]
    have hopen : IsOpen (Function.support (g p₀) ∩ Ioo p q) :=
      (isOpen_ne_fun hgx continuous_const).inter isOpen_Ioo
    have hmem : q₀ ∈ Function.support (g p₀) ∩ Ioo p q := by
      refine ⟨(mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hwne)) (mul_pos hμp hμq)).ne', ?_, ?_⟩
      · show p₀ / 2 < q₀; linarith
      · show q₀ < q₀ + 1; linarith
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hmem⟩)
      (measure_mono fun y hy => ⟨hy.1, Ioo_subset_Icc_self hy.2⟩)
  have hG0 : ∀ x, 0 ≤ G x := fun x => setIntegral_nonneg measurableSet_Icc fun y _ => hg0 x y
  have hκ : 0 < ∫ x in Icc p q, G x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hG0) hGc.integrableOn_Icc]
    have hopen : IsOpen (Function.support G ∩ Ioo p q) :=
      (isOpen_ne_fun hGc continuous_const).inter isOpen_Ioo
    have hmem : p₀ ∈ Function.support G ∩ Ioo p q := by
      refine ⟨hGp.ne', ?_, ?_⟩
      · show p₀ / 2 < p₀; linarith
      · show p₀ < q₀ + 1; linarith
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨_, hmem⟩)
      (measure_mono fun y hy => ⟨hy.1, Ioo_subset_Icc_self hy.2⟩)
  -- the null sequence
  obtain ⟨K, -, hK⟩ := exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree
    (s := Finset.univ) (c := c) (a := a) (spanSourceCoefficient_nullPair n)
  obtain ⟨L, hLq, hLK⟩ : ∃ L : ℝ, q ≤ L ∧ K * Real.exp (-(8 * L)) < ε * ∫ x in Icc p q, G x := by
    have h0 : Tendsto (fun L : ℝ => K * Real.exp (-(8 * L))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 8))).const_mul K
      simpa [Function.comp_def, neg_mul] using this
    obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp (h0.eventually (gt_mem_nhds (mul_pos hε hκ)))
    exact ⟨max L₁ q, le_max_right _ _, hL₁ _ (le_max_left _ _)⟩
  set u : ℝ → ℝ := fun y => w y * smoothPlateau L y with hu_def
  have hu : ContDiff ℝ 2 u := (hws 2).mul (contDiff_smoothPlateau L)
  have huc : HasCompactSupport u := (hasCompactSupport_smoothPlateau L).mul_left
  have hueven : ∀ x, u (-x) = u x := fun x => by simp only [hu_def, hweven, smoothPlateau_neg]
  refine ⟨u, hu, huc, hueven, ?_⟩
  -- the test is the plateau truncation of the pole-free pair
  have htest : (phiDoobTest fun y => convGauge φ y * u y) =
      phiDoobTest (spanPlateauProfile Finset.univ c a L) := funext fun x => by
    rw [phiDoobTest_spanPlateauProfile]
    unfold phiDoobTest
    simp only [hu_def]
    rw [← mul_assoc, ← mul_assoc, riemannKernelReal_mul_convGauge, ← hM_def, hMw]
  have hZ : zeroForm (phiDoobTest fun y => convGauge φ y * u y) ≤ K * Real.exp (-(8 * L)) := by
    rw [htest]
    unfold zeroForm
    have := (le_abs_self _).trans (hK L)
    nlinarith [sq_nonneg (oddPoleMoment (phiDoobTest (spanPlateauProfile Finset.univ c a L)))]
  -- the variance stays above the window energy
  obtain ⟨Z, hZb⟩ := huc.exists_bound_of_continuous hu.continuous
  have hZ' : ∀ x, |u x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZb x
  have hV : (∫ x in Icc p q, G x) ≤ varianceEnergy μ u := by
    refine le_trans (le_of_eq ?_) (setIntegral_setIntegral_le_varianceEnergy hμi hμ0 hμc
      hu.continuous hZ' p q)
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
    have hx1 : |x| ≤ L := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2, show (0 : ℝ) < p from by positivity]
    have hy1 : |y| ≤ L := by
      rw [abs_le]; constructor <;> linarith [hy.1, hy.2, show (0 : ℝ) < p from by positivity]
    simp only [hg_def, hu_def, smoothPlateau_eq_one hx1, smoothPlateau_eq_one hy1, mul_one]
  calc zeroForm (phiDoobTest fun y => convGauge φ y * u y) ≤ K * Real.exp (-(8 * L)) := hZ
    _ < ε * ∫ x in Icc p q, G x := hLK
    _ ≤ ε * varianceEnergy μ u := mul_le_mul_of_nonneg_left hV hε.le

/-- **The signed jump energy alone is not positive** in any smeared gauge: some even `u ∈ C²_c` has
`J_M(u) < 0`; more precisely `J_M + (1 − ε) V_μ` takes negative values for every `ε > 0`. -/
theorem exists_signedJumpEnergy_add_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      signedJumpEnergy (thetaConv (smearedProfile ν)) u +
        (1 - ε) * varianceEnergy (fun x => thetaConv (smearedProfile ν) x * Real.sinh (x / 2)) u < 0 := by
  obtain ⟨u, hu, huc, heven, hlt⟩ := exists_zeroForm_lt_mul_varianceEnergy hν hνc hν0 hνpos hb₀ hε
  have hφ : ContDiff ℝ 2 (smearedProfile ν) := (hν 2).sub ((hν 2).comp contDiff_neg)
  have hφc : HasCompactSupport (smearedProfile ν) :=
    hνc.sub (hνc.comp_homeomorph (Homeomorph.neg ℝ))
  rw [zeroForm_phiDoob_convGauge_mul_eq hφ hφc (smearedProfile_neg ν) hu huc] at hlt
  exact ⟨u, hu, huc, heven, by linarith⟩

theorem exists_signedJumpEnergy_neg :
    ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
      signedJumpEnergy (thetaConv (smearedProfile ν)) u < 0 := by
  obtain ⟨u, hu, huc, heven, hlt⟩ := exists_signedJumpEnergy_add_lt hν hνc hν0 hνpos hb₀ one_pos
  exact ⟨u, hu, huc, heven, by simpa using hlt⟩

end Smeared

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
