import GaloisForLFunctions.RHTower.TwistedArcLegendreForm
import GaloisForLFunctions.RHTower.ArcPairSlopeCosineMoment
import GaloisForLFunctions.RHTower.TwistedArcN1Reduction

/-!
# Twisted arc moments against clamped Legendre kernels

Let `M_n(u) = ∫ g_u(x) cos(k x) dx`, `k = 2π(n+2)`, be the twisted integer moments of the twisted
arc vectors `g_u = √y (τ_u + τ_{−u})` (`twArcMoment`), and let `k_c = legendreKernel ½ c ≥ 0` be the
clamped Legendre kernel of `HTGeometry.LegendreRunningMeanKernel` (`0 < c ≤ ½`).

**Theorem** (`integral_twArcMoment_mul_legendreKernel`).

`∫₀^{1/2} M_n(u) k_c(u)/√y_u du = 4 [(3/2) S_k(½) − (1 − c²) S_k(c)/c]`,

where `S_k(c) = (kc/y) K₁(ky) cos(kc) − k K₀(ky) sin(kc)`, `y = √(1 − c²)`, is the `c`-derivative of
the arc Whittaker mode `K₀(k√(1 − c²)) cos(kc)` (`arcWhittakerSlope`).

Proof.  `g_u/√y = τ_u(x) + τ_u(−x)` (`twPointVec_neg_neg`).  Fubini on `[0, ½] × ℝ` (the integrand
is bounded by `const · (1 + x²)⁻¹`), then
`TwistedArcLegendreForm.integral_twPointPair_mul_legendreKernel` for the `u`-integral, then the
cosine moments `∫ arcPairSlope(c, x) cos(kx) dx = 4 S_k(c)`
(`ArcPairSlopeCosineMoment.integral_arcPairSlope_mul_cos`, with `Q_c(±x) = (x ∓ c)² + y²`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-- `S_k(c) = (kc/y) K₁(ky) cos(kc) − k K₀(ky) sin(kc)`, `y = √(1 − c²)`. -/
def arcWhittakerSlope (k c : ℝ) : ℝ :=
  k * c / modularArcHeight c * kMoment 1 (k * modularArcHeight c) * Real.cos (k * c) -
    k * kMoment 0 (k * modularArcHeight c) * Real.sin (k * c)

theorem modularArcHeight_sq_of_abs_lt {c : ℝ} (hc : |c| < 1) :
    modularArcHeight c ^ 2 = 1 - c ^ 2 := by
  unfold modularArcHeight
  rw [Real.sq_sqrt]
  have := abs_lt.mp hc
  nlinarith

theorem modularArcHeight_pos_of_abs_lt {c : ℝ} (hc : |c| < 1) : 0 < modularArcHeight c := by
  unfold modularArcHeight
  have := abs_lt.mp hc
  exact Real.sqrt_pos.mpr (by nlinarith)

theorem arcQuadTerm_one_eq {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    arcQuadTerm c 1 x = ((x - c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ) := by
  have hQ := arcQuad_pos hc x
  have e : arcQuad c x = (x - c) ^ 2 + modularArcHeight c ^ 2 := by
    rw [modularArcHeight_sq_of_abs_lt hc]; unfold arcQuad; ring
  unfold arcQuadTerm
  rw [← e, pow_one, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hQ]
  norm_num

theorem arcQuadTerm_one_neg_eq {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    arcQuadTerm c 1 (-x) = ((x + c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ) := by
  rw [arcQuadTerm_one_eq hc]
  congr 1
  ring

theorem arcPairSlope_eq {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    arcPairSlope c x = x * (((x - c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ) -
      ((x + c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ)) := by
  unfold arcPairSlope
  rw [arcQuadTerm_one_eq hc, arcQuadTerm_one_neg_eq hc]
  ring

theorem integrable_mul_rpow_shift {y : ℝ} (hy : 0 < y) (d : ℝ) :
    Integrable fun x : ℝ => x * ((x - d) ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) := by
  have hx0 : Integrable fun x : ℝ => x * (x ^ 2 + y ^ 2) ^ (-(3 / 2) : ℝ) :=
    (integrable_abs_mul_rpow hy).mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)])
  refine ((hx0.comp_sub_right d).add ((integrable_rpow_neg_three_halves hy).comp_sub_right d
    |>.const_mul d)).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem integrable_arcPairSlope {c : ℝ} (hc : |c| < 1) : Integrable (arcPairSlope c) := by
  have hy := modularArcHeight_pos_of_abs_lt hc
  refine ((integrable_mul_rpow_shift hy c).sub (integrable_mul_rpow_shift hy (-c))).congr
    (Eventually.of_forall fun x => ?_)
  rw [arcPairSlope_eq hc]
  simp only [Pi.sub_apply, sub_neg_eq_add]
  ring

theorem integrable_arcPairSlope_mul_cos {c : ℝ} (hc : |c| < 1) (k : ℝ) :
    Integrable fun x => arcPairSlope c x * Real.cos (k * x) :=
  (integrable_arcPairSlope hc).mul_bdd (by fun_prop : Continuous fun x : ℝ =>
    Real.cos (k * x)).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- `∫ arcPairSlope(c, x) cos(kx) dx = 4 S_k(c)`. -/
theorem integral_arcPairSlope_mul_cos_eq {c k : ℝ} (hc : |c| < 1) (hk : 0 < k) :
    ∫ x, arcPairSlope c x * Real.cos (k * x) = 4 * arcWhittakerSlope k c := by
  have hy := modularArcHeight_pos_of_abs_lt hc
  have e : ∀ x, arcPairSlope c x * Real.cos (k * x) =
      x * (((x - c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ) -
        ((x + c) ^ 2 + modularArcHeight c ^ 2) ^ (-(3 / 2) : ℝ)) * Real.cos (k * x) := fun x => by
    rw [arcPairSlope_eq hc]
  simp_rw [e]
  rw [integral_arcPairSlope_mul_cos hy hk c]
  unfold arcWhittakerSlope
  ring

/-- The arc point of `u`, clamped to `[−½, ½]`. -/
def arcClamp (u : ℝ) : ArcParam := Set.projIcc (-1 / 2) (1 / 2) (by norm_num) u

theorem arcClamp_coe {u : ℝ} (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : (arcClamp u : ℝ) = u := by
  unfold arcClamp
  rw [Set.projIcc_of_mem _ hu]

theorem twArcVector_arcClamp {u : ℝ} (hu : u ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (x : ℝ) :
    twArcVector (arcClamp u) x =
      Real.sqrt (modularArcHeight u) * (twPointVec u x + twPointVec u (-x)) := by
  unfold twArcVector
  rw [arcClamp_coe hu]
  have h := twPointVec_neg_neg u (-x)
  rw [neg_neg] at h
  rw [h]

theorem continuousAt_twPointVec_joint {p : ℝ × ℝ} (hp : |p.1| < 1) :
    ContinuousAt (fun q : ℝ × ℝ => twPointVec q.1 q.2) p := by
  have hQ : ∀ j : ℕ, ContinuousAt (fun q : ℝ × ℝ => arcQuadTerm q.1 j q.2) p := by
    intro j
    have hA : Continuous fun q : ℝ × ℝ => arcQuad q.1 q.2 := by unfold arcQuad; fun_prop
    have hpos := arcQuad_pos hp p.2
    unfold arcQuadTerm
    exact ((hA.continuousAt).rpow_const (Or.inl hpos.ne')).div
      ((hA.continuousAt).pow j) (pow_pos hpos j).ne'
  unfold twPointVec
  have h1 := hQ 1; have h2 := hQ 2; have h3 := hQ 3; have h4 := hQ 4
  fun_prop

theorem continuousOn_legendreKernel_half {c : ℝ} :
    ContinuousOn (legendreKernel (1 / 2) c) (Icc 0 (1 / 2)) := fun u hu =>
  (hasDerivAt_legendreKernel (by norm_num) (by nlinarith [hu.1, hu.2])).continuousAt
    |>.continuousWithinAt

/-- **Twisted moments against a clamped Legendre kernel.** -/
theorem integral_twArcMoment_mul_legendreKernel (n : ℕ) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2) :
    ∫ u in (0 : ℝ)..(1 / 2), twArcMoment n (arcClamp u) *
        (legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u)) =
      4 * ((3 / 2) * arcWhittakerSlope (arcFreq (n + 1)) (1 / 2) -
        (1 - c ^ 2) * arcWhittakerSlope (arcFreq (n + 1)) c / c) := by
  set k := arcFreq (n + 1) with hk
  have hk0 : 0 < k := arcFreq_pos _
  set f : ℝ → ℝ → ℝ := fun u x =>
    (twPointVec u x + twPointVec u (-x)) * Real.cos (k * x) * legendreKernel (1 / 2) c u with hf
  have hIcc : ∀ u ∈ Ioc (0 : ℝ) (1 / 2), u ∈ Icc (-1 / 2 : ℝ) (1 / 2) := fun u hu =>
    ⟨by linarith [hu.1], hu.2⟩
  -- the integrand, pointwise in `u`
  have hpt : ∀ u ∈ Ioc (0 : ℝ) (1 / 2), twArcMoment n (arcClamp u) *
      (legendreKernel (1 / 2) c u / Real.sqrt (modularArcHeight u)) = ∫ x, f u x := by
    intro u hu
    have hy : 0 < Real.sqrt (modularArcHeight u) :=
      Real.sqrt_pos.mpr (modularArcHeight_pos (hIcc u hu))
    unfold twArcMoment
    rw [← MeasureTheory.integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hf]
    rw [twArcVector_arcClamp (hIcc u hu)]
    field_simp
    simp only [hk]
    ring
  -- a uniform bound on the kernel
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    (continuousOn_legendreKernel_half (c := c))
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0 ⟨le_rfl, by norm_num⟩)
  have hbound : ∀ u ∈ Ioc (0 : ℝ) (1 / 2), ∀ x, ‖f u x‖ ≤ K * (9000 * (1 + x ^ 2)⁻¹) := by
    intro u hu x
    have hu1 : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have h1 := abs_twPointVec_le hu1 x
    have h2 := abs_twPointVec_le hu1 (-x)
    have hx2 : (1 + (-x) ^ 2)⁻¹ = (1 + x ^ 2)⁻¹ := by rw [neg_sq]
    rw [hx2] at h2
    have hk' : ‖legendreKernel (1 / 2) c u‖ ≤ K := hK u ⟨hu.1.le, hu.2⟩
    simp only [hf, norm_mul, Real.norm_eq_abs]
    have hcos := Real.abs_cos_le_one (k * x)
    have hsum : |twPointVec u x + twPointVec u (-x)| ≤ 9000 * (1 + x ^ 2)⁻¹ := by
      calc |twPointVec u x + twPointVec u (-x)| ≤ |twPointVec u x| + |twPointVec u (-x)| :=
            abs_add_le _ _
        _ ≤ 4500 * (1 + x ^ 2)⁻¹ + 4500 * (1 + x ^ 2)⁻¹ := add_le_add h1 h2
        _ = 9000 * (1 + x ^ 2)⁻¹ := by ring
    rw [Real.norm_eq_abs] at hk'
    calc |twPointVec u x + twPointVec u (-x)| * |Real.cos (k * x)| *
          |legendreKernel (1 / 2) c u|
        ≤ (9000 * (1 + x ^ 2)⁻¹) * 1 * K :=
          mul_le_mul (mul_le_mul hsum hcos (abs_nonneg _) (by positivity)) hk' (abs_nonneg _)
            (by positivity)
      _ = K * (9000 * (1 + x ^ 2)⁻¹) := by ring
  -- integrability on the product
  have hcont : ContinuousOn (Function.uncurry f) (Ioc (0 : ℝ) (1 / 2) ×ˢ univ) := by
    intro p hp
    have hp1 : |p.1| < 1 := by
      have := hp.1; rw [abs_lt]; constructor <;> linarith [this.1, this.2]
    have hpk : ContinuousWithinAt (fun q : ℝ × ℝ => legendreKernel (1 / 2) c q.1)
        (Ioc (0 : ℝ) (1 / 2) ×ˢ univ) p := by
      have hpk1 : ContinuousWithinAt (legendreKernel (1 / 2) c) (Icc 0 (1 / 2)) p.1 :=
        continuousOn_legendreKernel_half p.1 ⟨hp.1.1.le, hp.1.2⟩
      exact hpk1.comp continuousWithinAt_fst (fun q hq => ⟨hq.1.1.le, hq.1.2⟩)
    have hpv : ContinuousAt (fun q : ℝ × ℝ => twPointVec q.1 q.2 + twPointVec q.1 (-q.2)) p := by
      have h1 := continuousAt_twPointVec_joint hp1
      have h2 : ContinuousAt (fun q : ℝ × ℝ => twPointVec q.1 (-q.2)) p :=
        ContinuousAt.comp (g := fun q : ℝ × ℝ => twPointVec q.1 q.2)
          (f := fun q : ℝ × ℝ => (q.1, -q.2)) (continuousAt_twPointVec_joint (p := (p.1, -p.2)) hp1)
          (by fun_prop)
      exact h1.add h2
    have hcosc : ContinuousAt (fun q : ℝ × ℝ => Real.cos (k * q.2)) p := by fun_prop
    exact ((hpv.mul hcosc).continuousWithinAt).mul hpk
  have hprod : (volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioc (0 : ℝ) (1 / 2) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod volume) := by
    rw [hprod]
    exact hcont.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hFint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℝ => K * (9000 * (1 + p.2 ^ 2)⁻¹))
        ((volume.restrict (Ioc (0 : ℝ) (1 / 2))).prod volume) := by
      have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc (0 : ℝ) (1 / 2))) :=
        integrable_const 1
      have := h1.mul_prod ((integrable_inv_one_add_sq).const_mul (K * 9000))
      refine this.congr (Eventually.of_forall fun p => ?_)
      simp only
      ring
    refine hg.mono' hmeas ?_
    rw [hprod]
    exact ae_restrict_of_forall_mem (measurableSet_Ioc.prod MeasurableSet.univ)
      fun p hp => hbound p.1 hp.1 p.2
  -- Fubini
  have hswap := integral_integral_swap hFint
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    setIntegral_congr_fun measurableSet_Ioc hpt, hswap]
  -- the inner `u`-integral
  have hinner : ∀ x, ∫ u in Ioc (0 : ℝ) (1 / 2), f u x =
      Real.cos (k * x) * ((1 - (1 / 2 : ℝ) ^ 2) * arcPairSlope (1 / 2) x / (1 / 2) -
        (1 - c ^ 2) * arcPairSlope c x / c) := by
    intro x
    rw [← integral_twPointPair_mul_legendreKernel x hc hc2,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hf]
    ring
  simp_rw [hinner]
  have hhalf : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hc1 : |c| < 1 := by rw [abs_of_pos hc]; linarith
  have i1 := integrable_arcPairSlope_mul_cos hhalf k
  have i2 := integrable_arcPairSlope_mul_cos hc1 k
  have e : ∀ x, Real.cos (k * x) * ((1 - (1 / 2 : ℝ) ^ 2) * arcPairSlope (1 / 2) x / (1 / 2) -
      (1 - c ^ 2) * arcPairSlope c x / c) =
      (3 / 2) * (arcPairSlope (1 / 2) x * Real.cos (k * x)) -
        ((1 - c ^ 2) / c) * (arcPairSlope c x * Real.cos (k * x)) := fun x => by
    field_simp
    ring
  simp_rw [e]
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_arcPairSlope_mul_cos_eq hhalf hk0,
    integral_arcPairSlope_mul_cos_eq hc1 hk0]
  ring

end

end RHTower
