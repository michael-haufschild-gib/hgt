import GaloisForLFunctions.RHTower.StretchedBoseDensity
import GaloisForLFunctions.RHTower.IntegerBlindLogarithmicCarlsonCritical

/-!
# Density of dilation systems up to the critical logarithmic room

Let `v_k ∈ L²(0,∞)` have Mellin images `-(k+1)^{-s} Φ(s) ζ(s)` on the critical line.

**Theorem** (`span_dense_of_mellin_multiplier_logRoom`).  If `Φ` is continuous and nonvanishing on
`Re s = 1/2` and `|Φζ(1/2+it)| e^{(π/2)|t| − (π/2)|t|/log(|t|+3)} ≤ C(1+|t|)^{-2}`, the `v_k` span a
dense subspace.  An orthogonal vector `g` produces `w = conj(Φζ)·𝓜g`, whose Dirichlet moments
vanish at every integer `n ≥ 2` and which is integrable against the critical room `K = π/2`.  The
critical logarithmic Carlson theorem (`fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical`)
kills `ŵ`, and `𝓜g = 0` off the countable zero set of `ζ`.

This extends `span_dense_of_mellin_multiplier` (multipliers at the Carlson rate `π/2` with
polynomial room) to multipliers that are larger by up to `e^{(π/2)|t|/log(|t|+3)}`.  By
`exists_integerBlind_logRoom`, `π/2` is also the exact second-order constant for integer-blind
separators.  Hence the switch between unconditional density and the regime where RH becomes a
membership question (`riemannHypothesis_iff_kernelL2_mem_closure`) sits at the logarithmic Carlson
room.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace FourierTransform

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry PrimeBlindCarlson

variable {Φ : ℂ → ℂ} {C : ℝ}

theorem one_le_logRoomWeight_critical (t : ℝ) : 1 ≤ logRoomWeight (Real.pi / 2) t := by
  unfold logRoomWeight
  apply Real.one_le_exp
  have hL : 1 ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; linarith [abs_nonneg t]
  have h : Real.pi / 2 * |t| / Real.log (|t| + 3) ≤ Real.pi / 2 * |t| :=
    div_le_self (by positivity) hL
  linarith

theorem integrable_multiplierWeight_logRoom
    (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ))
    (hb : ∀ ξ : ℝ, ‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
      logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ) ≤ C * (1 + |2 * Real.pi * ξ|) ^ (-(2 : ℝ)))
    (g : HalfLineL2) :
    Integrable fun ξ => ‖multiplierWeight Φ g ξ‖ * logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ) := by
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
      ((continuous_logRoomWeight _).comp (continuous_const.mul continuous_id)).stronglyMeasurable
      ).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have hrw : 0 ≤ logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ) := logRoomWeight_nonneg _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hrw)]
  set x := |2 * Real.pi * ξ| with hx
  have hxξ : |ξ| ≤ x := by
    rw [hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hmono : (1 + x) ^ (-(2 : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(2 : ℝ)) := by
    rw [Real.norm_eq_abs]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hW : ‖multiplierWeight Φ g ξ‖ * logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ) =
      (‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
        logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ)) * ‖Mg ξ‖ := by
    unfold multiplierWeight
    rw [norm_mul, Complex.norm_conj]; ring
  rw [hW]
  calc (‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
        logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ)) * ‖Mg ξ‖
      ≤ (|C| * (1 + x) ^ (-(2 : ℝ))) * ‖Mg ξ‖ := by
        refine mul_le_mul_of_nonneg_right ((hb ξ).trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((1 + ‖ξ‖) ^ (-(2 : ℝ)) * ‖Mg ξ‖) := by
        rw [mul_assoc]; gcongr

/-- **Completeness up to the critical logarithmic room.**  If `Φ` is continuous and nonvanishing
on the critical line and `|Φζ(1/2+it)| ≤ C (1+|t|)^{-2} e^{-(π/2)|t| + (π/2)|t|/log(|t|+3)}`, then
vectors whose Mellin images are `-(k+1)^{-s} Φ(s) ζ(s)` span a dense subspace of `L²(0,∞)`. -/
theorem span_dense_of_mellin_multiplier_logRoom {v : ℕ → HalfLineL2}
    (hv : ∀ k : ℕ, (halfLineMellinUnitary (v k) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => -(((k + 1 : ℕ) : ℂ) ^ (-mellinLinePoint ξ) * Φ (mellinLinePoint ξ) *
        riemannZeta (mellinLinePoint ξ)))
    (hΦc : Continuous fun ξ : ℝ => Φ (mellinLinePoint ξ))
    (hΦ0 : ∀ ξ : ℝ, Φ (mellinLinePoint ξ) ≠ 0)
    (hb : ∀ ξ : ℝ, ‖Φ (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ *
      logRoomWeight (Real.pi / 2) (2 * Real.pi * ξ) ≤ C * (1 + |2 * Real.pi * ξ|) ^ (-(2 : ℝ))) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hgk : ∀ p : ℕ, 2 ≤ p → ⟪v (p - 1), g⟫_ℂ = 0 := fun p _ =>
    hg _ (Submodule.subset_span ⟨p - 1, rfl⟩)
  set W := multiplierWeight Φ g with hWdef
  have h2pi0 : 0 < 2 * Real.pi := by positivity
  have h2pi : 2 * Real.pi ≠ 0 := h2pi0.ne'
  set w : ℝ → ℂ := fun t => W (t / (2 * Real.pi)) with hwdef
  have hmomξ : ∀ p : ℕ, 2 ≤ p →
      ∫ ξ, W ξ * cexp (-(I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * ((Real.log p : ℝ) : ℂ)) = 0 := by
    intro p hp
    have h := inner_multiplier_eq hv hp g
    rw [hgk p hp] at h
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
  have hmom : ∀ p ∈ {n : ℕ | 2 ≤ n}, ∫ t, w t * cexp (-(I * t) * Real.log p) = 0 := by
    intro p hp
    rw [htransport, hmomξ p hp, smul_zero]
  have hWsm := stronglyMeasurable_multiplierWeight hΦc g
  have hwm : AEStronglyMeasurable w volume :=
    (hWsm.comp_measurable (measurable_id.div_const _)).aestronglyMeasurable
  have hroom : Integrable fun t => ‖w t‖ * logRoomWeight (Real.pi / 2) t := by
    refine ((integrable_multiplierWeight_logRoom hΦc hb g).comp_div h2pi).congr
      (Eventually.of_forall fun t => ?_)
    simp only [hwdef]
    have ht : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
    rw [ht]
  have hcarl := fun x => fourier_eq_zero_of_dirichletMoment_eq_zero_logRoom_critical
    (N := {n : ℕ | 2 ≤ n}) (fun _ hn => hn) not_summable_one_div_mul_log hwm hroom hmom x
  have hWint : Integrable W := by
    refine (integrable_multiplierWeight_logRoom hΦc hb g).mono'
      hWsm.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    have h := one_le_logRoomWeight_critical (2 * Real.pi * ξ)
    have h0 := norm_nonneg (W ξ)
    nlinarith
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

end RHTower.StretchedBose
