import GaloisForLFunctions.RHTower.StretchedBoseNonDensity

/-!
# The completeness phase transition of stretched Bose defects

**Theorem** (`defectDilateL2_span_dense_iff`).  For `a > 0` the integer dilates `D_a(k·)`,
`k ≥ 1`, of the stretched Bose defect `D_a(t) = Γ(1/a+1)/t - Σ_{n ≥ 1} e^{-(nt)^a}` span a dense
subspace of `L²(0,∞)` iff `a ≤ 1`.

* `a ≤ 1` (`defectDilateL2_span_dense`): the Mellin multiplier `Γ(s/a)/a · ζ(s)` decays at rate
  `π/(2a) ≥ π/2` on the critical line.  This is the Carlson rate at which `log ℕ` (even the prime
  logarithms) stops being a uniqueness set, so an orthogonal vector has vanishing prime moments
  under the Carlson room and is zero.  The argument is that of `boseDilateL2_span_dense` for a
  general multiplier (`span_dense_of_mellin_multiplier`).
* `a > 1` (`defectDilateL2_span_closure_ne_top`): a pole-free sinc separator is orthogonal to every
  dilate.

For `a > 1` RH is equivalent to `e^{-t^a}` lying in the closed span
(`riemannHypothesis_iff_kernelL2_mem_closure`).  At `a ≤ 1` the span is everything, and RH is a
statement about the size of the coefficients.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace FourierTransform

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry

/-! ## Completeness for a general Mellin multiplier -/

section General

variable {Φ : ℂ → ℂ} {C : ℝ} {m : ℕ}

/-- The Carlson weight `conj(Φζ(s(ξ))) · (𝓜 g)(ξ)`. -/
def multiplierWeight (Φ : ℂ → ℂ) (g : HalfLineL2) (ξ : ℝ) : ℂ :=
  conj (Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) *
    (halfLineMellinUnitary g : ℝ → ℂ) ξ

theorem continuous_multiplier_mul_zeta (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ)) :
    Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ) := by
  refine hΦc.mul ?_
  rw [continuous_iff_continuousAt]
  intro ξ
  exact ((differentiableAt_riemannZeta (mellinLinePoint_ne_one ξ)).continuousAt).comp
    continuous_mellinLinePoint.continuousAt

theorem stronglyMeasurable_multiplierWeight (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ))
    (g : HalfLineL2) : StronglyMeasurable (multiplierWeight Φ g) :=
  ((Complex.continuous_conj.comp (continuous_multiplier_mul_zeta hΦc)).stronglyMeasurable).mul
    (Lp.stronglyMeasurable _)

open PrimeBlindCarlson in
theorem integrable_multiplierWeight_room (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ))
    (hb : ∀ ξ : ℝ, ‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ≤
      C * (1 + |2 * Real.pi * ξ|) ^ m * Real.exp (-(Real.pi / 2 * |2 * Real.pi * ξ|)))
    (g : HalfLineL2) :
    Integrable fun ξ => ‖multiplierWeight Φ g ξ‖ * roomWeight (m + 2) (2 * Real.pi * ξ) := by
  set Mg : ℝ → ℂ := (halfLineMellinUnitary g : ℝ → ℂ) with hMg
  have hK1 : MemLp (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 : ℝ))) 2 volume := by
    refine (memLp_two_iff_integrable_sq
      (Measurable.aestronglyMeasurable (by fun_prop))).mpr ?_
    refine (integrable_one_add_norm (E := ℝ) (r := 4) (by norm_num)).congr
      (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    try norm_num
  have hK2 : MemLp (fun ξ => ‖Mg ξ‖) 2 volume := (Lp.memLp _).norm
  have hK : Integrable (fun ξ : ℝ => (1 + ‖ξ‖) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := hK1.integrable_mul hK2
  refine (hK.const_mul |C|).mono'
    (((stronglyMeasurable_multiplierWeight hΦc g).norm.mul
      (by unfold roomWeight; fun_prop : Measurable fun ξ : ℝ =>
        roomWeight (m + 2) (2 * Real.pi * ξ)).stronglyMeasurable).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have hrw : 0 ≤ roomWeight (m + 2) (2 * Real.pi * ξ) := roomWeight_nonneg _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrw)]
  set x := |2 * Real.pi * ξ| with hx
  have hxξ : |ξ| ≤ x := by
    rw [hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hW : ‖multiplierWeight Φ g ξ‖ ≤
      |C| * (1 + x) ^ m * Real.exp (-(Real.pi / 2 * x)) * ‖Mg ξ‖ := by
    unfold multiplierWeight
    rw [norm_mul, Complex.norm_conj]
    refine mul_le_mul_of_nonneg_right ((hb ξ).trans ?_) (norm_nonneg _)
    gcongr; exact le_abs_self C
  have hroom : roomWeight (m + 2) (2 * Real.pi * ξ) =
      Real.exp (Real.pi / 2 * x) * (1 + x) ^ (-((m : ℝ) + 2)) := by
    unfold roomWeight; rw [hx]
  have hpos1 : 0 < 1 + x := by positivity
  have hpow : (1 + x) ^ m * (1 + x) ^ (-((m : ℝ) + 2)) = (1 + x) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hpos1]; congr 1; ring
  have hmono : (1 + x) ^ (-(2 : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hexp : Real.exp (-(Real.pi / 2 * x)) * Real.exp (Real.pi / 2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖multiplierWeight Φ g ξ‖ * roomWeight (m + 2) (2 * Real.pi * ξ)
      ≤ (|C| * (1 + x) ^ m * Real.exp (-(Real.pi / 2 * x)) * ‖Mg ξ‖) *
          roomWeight (m + 2) (2 * Real.pi * ξ) := mul_le_mul_of_nonneg_right hW hrw
    _ = |C| * ((1 + x) ^ m * (1 + x) ^ (-((m : ℝ) + 2))) * ‖Mg ξ‖ *
          (Real.exp (-(Real.pi / 2 * x)) * Real.exp (Real.pi / 2 * x)) := by rw [hroom]; ring
    _ = |C| * ((1 + x) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := by rw [hpow, hexp]; ring
    _ ≤ |C| * ((1 + ‖ξ‖) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := by gcongr

/-- Mellin form of the orthogonality relations for a multiplier family. -/
theorem inner_multiplier_eq {v : ℕ → HalfLineL2}
    (hv : ∀ k : ℕ, (halfLineMellinUnitary (v k) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * Φ (mellinLinePoint ξ) *
        riemannZeta (mellinLinePoint ξ)))
    {p : ℕ} (hp : 2 ≤ p) (g : HalfLineL2) :
    ⟪v (p - 1), g⟫_ℂ =
      -cexp (-((Real.log p : ℝ) : ℂ) / 2) *
        ∫ ξ, multiplierWeight Φ g ξ *
          cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log p : ℝ) : ℂ)) := by
  have hk : p - 1 + 1 = p := by omega
  have hin : ∀ x y : ℂ, ⟪x, y⟫_ℂ = conj x * y := fun x y => by simp [mul_comm]
  rw [← halfLineMellinUnitary.inner_map_map, MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hv (p - 1)] with ξ hξ
  rw [hin, hξ, hk, map_neg, map_mul, map_mul,
    conj_natCast_cpow_neg_mellinLinePoint (by omega : 0 < p) ξ]
  unfold multiplierWeight
  rw [map_mul]
  ring

/-- **Completeness for a general Mellin multiplier.**  If `Φ` is continuous and nonvanishing on
the critical line and `|Φζ(1/2+it)| ≤ C (1+|t|)^m e^{-(π/2)|t|}`, then vectors whose Mellin
images are `-(k+1)^{-s} Φ(s) ζ(s)` span a dense subspace. -/
theorem span_dense_of_mellin_multiplier {v : ℕ → HalfLineL2}
    (hv : ∀ k : ℕ, (halfLineMellinUnitary (v k) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * Φ (mellinLinePoint ξ) *
        riemannZeta (mellinLinePoint ξ)))
    (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ))
    (hΦ0 : ∀ ξ : ℝ, Φ (mellinLinePoint ξ) ≠ 0)
    (hb : ∀ ξ : ℝ, ‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ≤
      C * (1 + |2 * Real.pi * ξ|) ^ m * Real.exp (-(Real.pi / 2 * |2 * Real.pi * ξ|))) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hgp : ∀ p : ℕ, p.Prime → ⟪v (p - 1), g⟫_ℂ = 0 := fun p _ =>
    hg _ (Submodule.subset_span ⟨p - 1, rfl⟩)
  set W := multiplierWeight Φ g with hWdef
  have h2pi0 : 0 < 2 * Real.pi := by positivity
  have h2pi : 2 * Real.pi ≠ 0 := h2pi0.ne'
  set w : ℝ → ℂ := fun t => W (t / (2 * Real.pi)) with hwdef
  have hmomξ : ∀ p : ℕ, p.Prime →
      ∫ ξ, W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log p : ℝ) : ℂ)) = 0 := by
    intro p hp
    have h := inner_multiplier_eq hv hp.two_le g
    rw [hgp p hp] at h
    have hne : cexp (-((Real.log p : ℝ) : ℂ) / 2) ≠ 0 := Complex.exp_ne_zero _
    have h' := h.symm
    rw [neg_mul, neg_eq_zero, mul_eq_zero] at h'
    exact h'.resolve_left hne
  have htransport : ∀ x : ℝ, ∫ t, w t * cexp (-(I * t) * x) =
      (2 * Real.pi : ℝ) • ∫ ξ, W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * x) := by
    intro x
    have h := Measure.integral_comp_div
      (fun ξ => W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * x)) (2 * Real.pi)
    rw [abs_of_pos h2pi0] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hwdef]
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [ht]
  have hmom : ∀ p : ℕ, p.Prime → ∫ t, w t * cexp (-(I * t) * Real.log p) = 0 := by
    intro p hp
    rw [htransport, hmomξ p hp, smul_zero]
  have hWsm := stronglyMeasurable_multiplierWeight hΦc g
  have hwm : AEStronglyMeasurable w volume :=
    (hWsm.comp_measurable (measurable_id.div_const _)).aestronglyMeasurable
  have hroom : Integrable fun t => ‖w t‖ * PrimeBlindCarlson.roomWeight (m + 2) t := by
    refine ((integrable_multiplierWeight_room hΦc hb g).comp_div h2pi).congr
      (Eventually.of_forall fun t => ?_)
    simp only [hwdef]
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [ht]
  have hcarl := fun x => PrimeBlindCarlson.fourier_eq_zero_of_primeMoment_eq_zero_room
    (by positivity : (0 : ℝ) ≤ (m : ℝ) + 2) hwm hroom hmom x
  -- the room weight is bounded below
  set n : ℕ := m + 2 with hn
  set c : ℝ := 1 / ((n.factorial : ℝ) * (2 / Real.pi) ^ n * Real.exp (Real.pi / 2)) with hc
  have hc0 : 0 < c := by positivity
  have hroomlow : ∀ t : ℝ, c ≤ PrimeBlindCarlson.roomWeight (m + 2) t := by
    intro t
    have hy : 0 ≤ |t| := abs_nonneg t
    set z : ℝ := Real.pi / 2 * (1 + |t|) with hz
    have hz0 : 0 ≤ z := by positivity
    have he := Real.pow_div_factorial_le_exp z hz0 n
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hpow : (1 + |t|) ^ n ≤ (n.factorial : ℝ) * (2 / Real.pi) ^ n * Real.exp (Real.pi / 2) *
        Real.exp (Real.pi / 2 * |t|) := by
      rw [div_le_iff₀ hfac, hz, mul_pow] at he
      have hexp : Real.exp (Real.pi / 2 * (1 + |t|)) =
          Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2 * |t|) := by
        rw [← Real.exp_add]; ring_nf
      rw [hexp] at he
      have h2π : (Real.pi / 2) ^ n * (2 / Real.pi) ^ n = 1 := by
        rw [← mul_pow]; field_simp; simp
      calc (1 + |t|) ^ n = ((Real.pi / 2) ^ n * (1 + |t|) ^ n) * (2 / Real.pi) ^ n := by
            rw [show ((Real.pi / 2) ^ n * (1 + |t|) ^ n) * (2 / Real.pi) ^ n =
              ((Real.pi / 2) ^ n * (2 / Real.pi) ^ n) * (1 + |t|) ^ n by ring, h2π, one_mul]
        _ ≤ (Real.exp (Real.pi / 2) * Real.exp (Real.pi / 2 * |t|) * (n.factorial : ℝ)) *
              (2 / Real.pi) ^ n := mul_le_mul_of_nonneg_right he (by positivity)
        _ = _ := by ring
    unfold PrimeBlindCarlson.roomWeight
    rw [show ((m : ℝ) + 2) = ((n : ℕ) : ℝ) by rw [hn]; push_cast; ring, Real.rpow_neg (by positivity),
      Real.rpow_natCast, hc, one_div, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have hWint : Integrable W := by
    refine ((integrable_multiplierWeight_room hΦc hb g).const_mul c⁻¹).mono'
      hWsm.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    have h := hroomlow (2 * Real.pi * ξ)
    have h0 := norm_nonneg (W ξ)
    calc ‖W ξ‖ = c⁻¹ * (‖W ξ‖ * c) := by field_simp
      _ ≤ c⁻¹ * (‖W ξ‖ * PrimeBlindCarlson.roomWeight (↑m + 2) (2 * Real.pi * ξ)) := by gcongr
  have hF : ∀ y, FourierTransform.fourier W y = 0 := by
    intro y
    have h := hcarl y
    rw [htransport, smul_eq_zero] at h
    have h' := h.resolve_left (by exact_mod_cast h2pi)
    rw [Real.fourier_real_eq, ← h']
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have hW0 : W =ᵐ[volume] 0 := integrable_ae_eq_zero_of_fourier_eq_zero hWint hF
  have hcount : (mellinLinePoint ⁻¹' {s | zetaEntire s = 0}).Countable :=
    countable_setOf_zetaEntire_eq_zero.preimage mellinLinePoint_injective
  have hnull : ∀ᵐ ξ ∂volume, ξ ∉ mellinLinePoint ⁻¹' {s | zetaEntire s = 0} :=
    hcount.ae_notMem volume
  have hMg : (halfLineMellinUnitary g : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [hW0, hnull] with ξ h1 h2
    have hz : riemannZeta (mellinLinePoint ξ) ≠ 0 := by
      intro hz
      apply h2
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [zetaEntire_eq (mellinLinePoint_ne_one ξ), hz, mul_zero]
    have h1' : W ξ = 0 := h1
    simp only [hWdef, multiplierWeight, mul_eq_zero, map_eq_zero] at h1'
    rcases h1' with (h | h) | h
    · exact absurd h (hΦ0 ξ)
    · exact absurd h hz
    · simpa using h
  have hzero : halfLineMellinUnitary g = 0 := (Lp.eq_zero_iff_ae_eq_zero).mpr hMg
  exact (LinearIsometryEquiv.map_eq_zero_iff halfLineMellinUnitary).mp hzero

end General

/-! ## Stretched kernels with `a ≤ 1` -/

/-- For `a ≤ 1`: `|F_a(1/2 + it)| ≤ C (1+|t|)^N e^{-(π/2)|t|}`. -/
theorem exists_norm_mellinFactor_half_le_of_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ t : ℝ, ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ ≤
      C * (1 + |t|) ^ N * Real.exp (-(Real.pi / 2 * |t|)) := by
  set x : ℝ := 1 / (2 * a) with hx
  have hx0 : 0 < x := by positivity
  obtain ⟨C₁, N, hC₁, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip x x
  have hΓx : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  set C : ℝ := (C₁ * (a⁻¹) ^ N + Real.Gamma x * Real.exp (Real.pi / 2)) / a with hC
  refine ⟨C, N, by positivity, fun t => ?_⟩
  rw [mellinFactor_half a t ha0.ne', norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha0]
  set y : ℝ := t / a with hy
  have hya : |y| = |t| / a := by rw [hy, abs_div, abs_of_pos ha0]
  have hz : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hzim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  have hE0 : 0 < Real.exp (-(Real.pi / 2 * |t|)) := Real.exp_pos _
  have h1t : (1 : ℝ) ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  rw [div_le_iff₀ ha0]
  have hCa : C * (1 + |t|) ^ N * Real.exp (-(Real.pi / 2 * |t|)) * a =
      (C₁ * (a⁻¹) ^ N + Real.Gamma x * Real.exp (Real.pi / 2)) * (1 + |t|) ^ N *
        Real.exp (-(Real.pi / 2 * |t|)) := by
    rw [hC]; field_simp
  rw [hCa]
  rcases le_or_gt 1 |y| with hbig | hsmall
  · have h1 := hΓ _ (by rw [hz]) (by rw [hz]) (by rw [hzim]; exact hbig)
    rw [hzim] at h1
    have hexp : Real.exp (-(Real.pi * |y| / 2)) ≤ Real.exp (-(Real.pi / 2 * |t|)) := by
      rw [Real.exp_le_exp, hya]
      have : |t| ≤ |t| / a := by
        rw [le_div_iff₀ ha0]; nlinarith [abs_nonneg t]
      nlinarith [Real.pi_pos]
    have hpow : |y| ^ N ≤ (a⁻¹) ^ N * (1 + |t|) ^ N := by
      rw [← mul_pow, hya, div_eq_mul_inv, mul_comm]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by positivity)) N
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖
        ≤ C₁ * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) := h1
      _ ≤ C₁ * ((a⁻¹) ^ N * (1 + |t|) ^ N) * Real.exp (-(Real.pi / 2 * |t|)) := by gcongr
      _ = C₁ * (a⁻¹) ^ N * (1 + |t|) ^ N * Real.exp (-(Real.pi / 2 * |t|)) := by ring
      _ ≤ _ := by
          gcongr
          have : 0 ≤ Real.Gamma x * Real.exp (Real.pi / 2) := by positivity
          linarith
  · have h1 : ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ Real.Gamma x := by
      have := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re (s := (x : ℂ) + (y : ℂ) * I)
        (by rw [hz]; exact hx0)
      rwa [hz] at this
    have ht1 : |t| ≤ 1 := by
      have : |t| / a < 1 := by rw [← hya]; exact hsmall
      rw [div_lt_one ha0] at this; linarith
    have hexp : 1 ≤ Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2 * |t|)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ Real.Gamma x := h1
      _ ≤ Real.Gamma x * (Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2 * |t|))) :=
          le_mul_of_one_le_right hΓx.le hexp
      _ ≤ Real.Gamma x * Real.exp (Real.pi / 2) * (1 + |t|) ^ N *
            Real.exp (-(Real.pi / 2 * |t|)) := by
          rw [← mul_assoc]
          calc Real.Gamma x * Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 2 * |t|))
              = Real.Gamma x * Real.exp (Real.pi / 2) * 1 * Real.exp (-(Real.pi / 2 * |t|)) := by
                ring
            _ ≤ _ := by gcongr
      _ ≤ _ := by
          gcongr
          have : 0 ≤ C₁ * (a⁻¹) ^ N := by positivity
          linarith

/-- **Density for `a ≤ 1`.**  The integer dilates of `D_a` are complete in `L²(0,∞)`. -/
theorem defectDilateL2_span_dense {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    (Submodule.span ℂ (Set.range (defectDilateL2 ha0))).topologicalClosure = ⊤ := by
  obtain ⟨C, N, hC0, hC⟩ := exists_norm_mellinFactor_half_le_of_le_one ha0 ha1
  refine span_dense_of_mellin_multiplier (Φ := mellinFactor a) (C := 18 * C) (m := N + 1)
    (halfLineMellinUnitary_defectDilateL2 ha0) ?_ (mellinFactor_ne_zero ha0) ?_
  · rw [continuous_iff_continuousAt]
    intro ξ
    exact (analyticAt_mellinFactor ha0 (by rw [mellinLinePoint_re]; norm_num)).continuousAt.comp
      continuous_mellinLinePoint.continuousAt
  · intro ξ
    rw [mellinLinePoint_eq]
    set t : ℝ := -(2 * Real.pi * ξ) with ht
    have habs : |t| = |2 * Real.pi * ξ| := by rw [ht, abs_neg]
    rw [← habs, norm_mul]
    calc ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ * ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖
        ≤ (C * (1 + |t|) ^ N * Real.exp (-(Real.pi / 2 * |t|))) * (18 * (1 + |t|)) :=
          mul_le_mul (hC t) (norm_riemannZeta_half_le t) (norm_nonneg _) (by positivity)
      _ = 18 * C * (1 + |t|) ^ (N + 1) * Real.exp (-(Real.pi / 2 * |t|)) := by ring

/-- **The completeness phase transition.**  For `a > 0`, the integer dilates of the stretched
Bose defect `D_a` span a dense subspace of `L²(0,∞)` iff `a ≤ 1`. -/
theorem defectDilateL2_span_dense_iff {a : ℝ} (ha0 : 0 < a) :
    (Submodule.span ℂ (Set.range (defectDilateL2 ha0))).topologicalClosure = ⊤ ↔ a ≤ 1 := by
  constructor
  · intro h
    by_contra ha
    exact defectDilateL2_span_closure_ne_top (not_le.mp ha) h
  · exact defectDilateL2_span_dense ha0

end RHTower.StretchedBose
