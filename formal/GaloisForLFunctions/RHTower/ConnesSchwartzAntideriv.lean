import GaloisForLFunctions.RHTower.ConnesTwoSidedPowerTail

/-!
# A Schwartz function of zero integral has a Schwartz primitive

The one structural brick behind Hadamard division on the Schwartz space, used for the last
identification of §V in

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

If `F` is a Schwartz function on `ℝ` with `∫ F = 0`, then `x ↦ ∫_{(-∞,x]} F` is again a Schwartz
function, and its derivative is `F`.  Smoothness is the fundamental theorem of calculus; rapid
decay uses the vanishing of the total integral to rewrite the primitive as `−∫_{(x,∞)} F` on the
right half line, so that on *both* sides it is dominated by the tail mass `∫_{|t| ≥ |x|} ‖F‖`.
-/

open MeasureTheory Set Filter Topology
open scoped SchwartzMap ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The primitive of a Schwartz function normalized at `-∞`. -/
def connesAntiderivFun (F : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ := ∫ t in Iic x, (F : ℝ → ℂ) t

theorem connesAntiderivFun_eq_intervalIntegral (F : 𝓢(ℝ, ℂ)) (x : ℝ) :
    connesAntiderivFun F x
      = (∫ t in Iic (0 : ℝ), (F : ℝ → ℂ) t) + ∫ t in (0 : ℝ)..x, (F : ℝ → ℂ) t := by
  have h := intervalIntegral.integral_Iic_sub_Iic (f := (F : ℝ → ℂ)) (μ := volume)
    (a := (0 : ℝ)) (b := x) F.integrable.integrableOn F.integrable.integrableOn
  rw [connesAntiderivFun, ← h]
  ring

theorem connes_hasDerivAt_antideriv (F : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (connesAntiderivFun F) ((F : ℝ → ℂ) x) x := by
  have hc : Continuous ((F : ℝ → ℂ)) := F.continuous
  have h := (hc.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt
  have h2 := h.const_add (∫ t in Iic (0 : ℝ), (F : ℝ → ℂ) t)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact connesAntiderivFun_eq_intervalIntegral F y

theorem connes_deriv_antideriv (F : 𝓢(ℝ, ℂ)) :
    deriv (connesAntiderivFun F) = (F : ℝ → ℂ) := by
  funext x
  exact (connes_hasDerivAt_antideriv F x).deriv

theorem connes_contDiff_antideriv (F : 𝓢(ℝ, ℂ)) : ContDiff ℝ ∞ (connesAntiderivFun F) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (connes_hasDerivAt_antideriv F x).differentiableAt, ?_⟩
  rw [connes_deriv_antideriv F]
  exact F.smooth'

/-- On the right half line the vanishing of the total integral turns the primitive into a
tail integral. -/
theorem connes_antideriv_eq_neg_tail (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0)
    (x : ℝ) : connesAntiderivFun F x = - ∫ t in Ioi x, (F : ℝ → ℂ) t := by
  have h := intervalIntegral.integral_Iic_add_Ioi (f := (F : ℝ → ℂ)) (μ := volume) (b := x)
    F.integrable.integrableOn F.integrable.integrableOn
  rw [hF] at h
  rw [connesAntiderivFun]
  linear_combination h

/-- The primitive is bounded by the total mass. -/
theorem connes_antideriv_norm_le_total (F : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖connesAntiderivFun F x‖ ≤ ∫ t : ℝ, ‖(F : ℝ → ℂ) t‖ := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine MeasureTheory.setIntegral_le_integral F.integrable.norm ?_
  filter_upwards with t using norm_nonneg _

/-- The primitive is bounded by the tail mass beyond `|x|`, on both half lines. -/
theorem connes_antideriv_norm_le_tail (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0)
    (x : ℝ) : ‖connesAntiderivFun F x‖ ≤ ∫ t in {t : ℝ | |x| ≤ |t|}, ‖(F : ℝ → ℂ) t‖ := by
  have hSm : MeasurableSet {t : ℝ | |x| ≤ |t|} := measurableSet_le measurable_const measurable_norm
  have hInt : IntegrableOn (fun t : ℝ => ‖(F : ℝ → ℂ) t‖) {t : ℝ | |x| ≤ |t|} volume :=
    F.integrable.norm.integrableOn
  rcases le_or_gt x 0 with hx | hx
  · have hsub : Iic x ⊆ {t : ℝ | |x| ≤ |t|} := by
      intro t ht
      have ht' : t ≤ x := ht
      rw [Set.mem_setOf_eq, abs_of_nonpos hx, abs_of_nonpos (le_trans ht' hx)]
      linarith
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact MeasureTheory.setIntegral_mono_set hInt
      (Filter.Eventually.of_forall fun t => norm_nonneg _)
      (LE.le.eventuallyLE hsub)
  · have hsub : Ioi x ⊆ {t : ℝ | |x| ≤ |t|} := by
      intro t ht
      have ht' : x < t := ht
      rw [Set.mem_setOf_eq, abs_of_pos hx, abs_of_pos (lt_trans hx ht')]
      linarith
    rw [connes_antideriv_eq_neg_tail F hF x, norm_neg]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact MeasureTheory.setIntegral_mono_set hInt
      (Filter.Eventually.of_forall fun t => norm_nonneg _)
      (LE.le.eventuallyLE hsub)

/-- The order-zero decay estimate for the primitive. -/
theorem connes_antideriv_decay_zero (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0)
    (k : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖connesAntiderivFun F x‖
      ≤ (∫ t : ℝ, ‖(F : ℝ → ℂ) t‖) + 2 * SchwartzMap.seminorm ℂ (k + 2) 0 F := by
  set M : ℝ := ∫ t : ℝ, ‖(F : ℝ → ℂ) t‖ with hM
  set σ : ℝ := SchwartzMap.seminorm ℂ (k + 2) 0 F with hσ
  have hM0 : (0 : ℝ) ≤ M := integral_nonneg fun t => norm_nonneg _
  have hσ0 : (0 : ℝ) ≤ σ := apply_nonneg _ F
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 : ‖x‖ ^ k ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) hx
    have h2 : ‖x‖ ^ k * ‖connesAntiderivFun F x‖ ≤ 1 * M :=
      mul_le_mul h1 (connes_antideriv_norm_le_total F x) (norm_nonneg _) zero_le_one
    rw [one_mul] at h2
    linarith
  · have hx0 : (0 : ℝ) < |x| := lt_trans zero_lt_one hx
    have hSm : MeasurableSet {t : ℝ | |x| ≤ |t|} :=
      measurableSet_le measurable_const measurable_norm
    set p : ℝ := (k : ℝ) + 2 with hp
    have hp1 : (1 : ℝ) < p := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hp]; linarith
    have hbound : ∀ t ∈ {t : ℝ | |x| ≤ |t|}, ‖(F : ℝ → ℂ) t‖ ≤ σ * |t| ^ (-p) := by
      intro t ht
      have ht0 : (0 : ℝ) < |t| := lt_of_lt_of_le hx0 ht
      have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ F (k + 2) t
      rw [Real.norm_eq_abs] at hsem
      have hrw : |t| ^ (-p) = (|t| ^ (k + 2))⁻¹ := by
        rw [Real.rpow_neg ht0.le, hp]
        congr 1
        rw [← Real.rpow_natCast |t| (k + 2)]
        norm_num
      rw [hrw, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖(F : ℝ → ℂ) t‖ * |t| ^ (k + 2) = |t| ^ (k + 2) * ‖(F : ℝ → ℂ) t‖ := by ring
        _ ≤ σ := hsem
    have hIntF : IntegrableOn (fun t : ℝ => ‖(F : ℝ → ℂ) t‖) {t : ℝ | |x| ≤ |t|} volume :=
      F.integrable.norm.integrableOn
    have hIntP : IntegrableOn (fun t : ℝ => σ * |t| ^ (-p)) {t : ℝ | |x| ≤ |t|} volume :=
      (connes_absRpow_tail_integrable hp1 hx0).const_mul σ
    have hmono : (∫ t in {t : ℝ | |x| ≤ |t|}, ‖(F : ℝ → ℂ) t‖)
        ≤ ∫ t in {t : ℝ | |x| ≤ |t|}, σ * |t| ^ (-p) :=
      MeasureTheory.setIntegral_mono_on hIntF hIntP hSm hbound
    have hval : (∫ t in {t : ℝ | |x| ≤ |t|}, σ * |t| ^ (-p))
        = σ * (2 * (|x| ^ (1 - p) / (p - 1))) := by
      rw [MeasureTheory.integral_const_mul]
      congr 1
      rw [← MeasureTheory.integral_indicator hSm]
      exact connes_absRpow_tail_value hp1 hx0
    have htail : ‖connesAntiderivFun F x‖ ≤ σ * (2 * (|x| ^ (1 - p) / (p - 1))) := by
      calc ‖connesAntiderivFun F x‖
          ≤ ∫ t in {t : ℝ | |x| ≤ |t|}, ‖(F : ℝ → ℂ) t‖ := connes_antideriv_norm_le_tail F hF x
        _ ≤ ∫ t in {t : ℝ | |x| ≤ |t|}, σ * |t| ^ (-p) := hmono
        _ = σ * (2 * (|x| ^ (1 - p) / (p - 1))) := hval
    have hpow : |x| ^ k * |x| ^ (1 - p) = |x| ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast |x| k, ← Real.rpow_add hx0]
      congr 1
      rw [hp]
      ring
    have hpowle : |x| ^ (-1 : ℝ) ≤ 1 := by
      rw [Real.rpow_neg_one]
      rw [inv_le_one_iff₀]
      exact Or.inr hx.le
    have hp1' : (1 : ℝ) ≤ p - 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      rw [hp]; linarith
    have hxk : (0 : ℝ) ≤ |x| ^ k := by positivity
    calc ‖x‖ ^ k * ‖connesAntiderivFun F x‖
        = |x| ^ k * ‖connesAntiderivFun F x‖ := by rw [Real.norm_eq_abs]
      _ ≤ |x| ^ k * (σ * (2 * (|x| ^ (1 - p) / (p - 1)))) := by
          exact mul_le_mul_of_nonneg_left htail hxk
      _ = σ * 2 * ((|x| ^ k * |x| ^ (1 - p)) / (p - 1)) := by ring
      _ = σ * 2 * (|x| ^ (-1 : ℝ) / (p - 1)) := by rw [hpow]
      _ ≤ σ * 2 * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hσ0 (by norm_num : (0 : ℝ) ≤ 2))
          rw [div_le_one (by linarith)]
          linarith
      _ = 2 * σ := by ring
      _ ≤ M + 2 * σ := by linarith

/-- All decay estimates for the primitive. -/
theorem connes_antideriv_decay (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (connesAntiderivFun F) x‖ ≤ C := by
  cases n with
  | zero =>
      refine ⟨(∫ t : ℝ, ‖(F : ℝ → ℂ) t‖) + 2 * SchwartzMap.seminorm ℂ (k + 2) 0 F, fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      exact connes_antideriv_decay_zero F hF k x
  | succ m =>
      obtain ⟨C, hC⟩ := F.decay' k m
      refine ⟨C, fun x => ?_⟩
      have hstep : ‖iteratedFDeriv ℝ (m + 1) (connesAntiderivFun F) x‖
          = ‖iteratedFDeriv ℝ m ((F : ℝ → ℂ)) x‖ := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          iteratedDeriv_succ', connes_deriv_antideriv F]
      rw [hstep]
      exact hC x

/-- **A Schwartz function of zero integral has a Schwartz primitive.** -/
def connesAntideriv (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0) : 𝓢(ℝ, ℂ) where
  toFun := connesAntiderivFun F
  smooth' := connes_contDiff_antideriv F
  decay' := connes_antideriv_decay F hF

@[simp] theorem connesAntideriv_apply (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0)
    (x : ℝ) : ((connesAntideriv F hF : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x = ∫ t in Iic x, (F : ℝ → ℂ) t := rfl

theorem connes_deriv_connesAntideriv (F : 𝓢(ℝ, ℂ)) (hF : (∫ t : ℝ, (F : ℝ → ℂ) t) = 0) :
    deriv ((connesAntideriv F hF : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (F : ℝ → ℂ) :=
  connes_deriv_antideriv F

end

end GaloisForLFunctions.RHTower
