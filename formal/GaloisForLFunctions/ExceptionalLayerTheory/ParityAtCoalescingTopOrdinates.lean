import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerNoGo
import GaloisForLFunctions.HTGeometry.ExponentialFilterPhaseLinearization

/-!
# Parity at coalescing top ordinates

Moving an ordinate changes its quadratic form on the half-line unit sphere by at most a
constant times its displacement. The constant depends only on depth and aperture. Comparing
both spectral extremes on this common sphere allows arbitrary positive splittings of an atom,
including splittings for which the Cauchy Gram matrix approaches a singular matrix.
-/

open Complex MeasureTheory Set Filter Topology
open RHTower RHTower.CCMParityCauchy RHTower.CCMParityTopLayer

namespace GaloisForLFunctions.ExceptionalLayerTheory

noncomputable section

private abbrev halfMeasure := volume.restrict (Ioi (0 : ℝ))

private def wave (δ r s : ℝ) : ℂ := Complex.exp (-((δ : ℂ) - I * r) * s)

private def moment (δ r : ℝ) (v : ℝ → ℝ) : ℂ :=
  ∫ s, (v s : ℂ) * wave δ r s ∂halfMeasure

private theorem wave_memLp {δ : ℝ} (hδ : 0 < δ) (r : ℝ) :
    MemLp (wave δ r) 2 halfMeasure :=
  memLp_exp_neg_Ioi (p := (δ : ℂ) - I * r) (by simp [hδ])

private theorem wave_norm (δ r s : ℝ) : ‖wave δ r s‖ = Real.exp (-(δ * s)) := by
  simp [wave, Complex.norm_exp, Complex.mul_re]

private theorem wave_sub_norm (δ r t s : ℝ) :
    ‖wave δ r s - wave δ t s‖ ≤ Real.exp (-(δ * s)) * (|r - t| * |s|) := by
  have split (k : ℝ) : wave δ k s =
      Complex.exp ((-(δ * s) : ℝ) : ℂ) * Complex.exp (((k * s : ℝ) : ℂ) * I) := by
    rw [wave, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [split r, split t, ← mul_sub, norm_mul, Complex.norm_exp, Complex.ofReal_re]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa [← sub_mul, abs_mul] using norm_cexp_phase_sub_le (r * s) (t * s)

private theorem moment_bound {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (r : ℝ) :
    ‖moment δ r v‖ ≤ Real.sqrt (1 / (2 * δ)) := by
  have h := norm_integral_mul_sq_le_of_memLp (hv.ofReal (K := ℂ)) (wave_memLp hδ r)
  change ‖moment δ r v‖ ^ 2 ≤ _ at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, hu, one_mul, wave_norm,
    ← Real.exp_nat_mul] at h
  have he : ∀ s : ℝ, (2 : ℕ) * -(δ * s) = -(2 * δ) * s := fun s => by push_cast; ring
  simp only [he, integral_exp_mul_Ioi (neg_lt_zero.mpr (by positivity : 0 < 2 * δ)) 0,
    mul_zero, Real.exp_zero, neg_div_neg_eq] at h
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr h

private theorem moment_sub_bound {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (r t : ℝ) :
    ‖moment δ r v - moment δ t v‖ ≤ |r - t| * Real.sqrt (2 / (2 * δ) ^ 3) := by
  have h2δ : 0 < 2 * δ := by positivity
  have hr := wave_memLp hδ r
  have ht := wave_memLp hδ t
  have hv' := hv.ofReal (K := ℂ)
  have hd := norm_integral_mul_sq_le_of_memLp hv' (hr.sub ht)
  have hi : (∫ s, (v s : ℂ) * (wave δ r - wave δ t) s ∂halfMeasure) =
      moment δ r v - moment δ t v := by
    simp only [Pi.sub_apply, mul_sub, moment, integral_sub (hv'.integrable_mul hr)
      (hv'.integrable_mul ht)]
  rw [hi] at hd
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, hu, one_mul] at hd
  have hm := HTGeometry.integral_sq_mul_exp_neg_mul_Ioi h2δ
  have hint : Integrable (fun s : ℝ => s ^ 2 * Real.exp (-(2 * δ * s))) halfMeasure := by
    by_contra hn
    rw [integral_undef hn] at hm
    exact (by positivity : 0 < 2 / (2 * δ) ^ 3).ne hm
  have he : (∫ s, ‖(wave δ r - wave δ t) s‖ ^ 2 ∂halfMeasure) ≤
      |r - t| ^ 2 * (2 / (2 * δ) ^ 3) := by
    rw [← hm, ← integral_const_mul]
    apply integral_mono ((memLp_two_iff_integrable_sq_norm
      (hr.sub ht).aestronglyMeasurable).mp (hr.sub ht)) (hint.const_mul _)
    intro s
    calc ‖(wave δ r - wave δ t) s‖ ^ 2
        ≤ (Real.exp (-(δ * s)) * (|r - t| * |s|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (wave_sub_norm δ r t s) 2
      _ = _ := by
        rw [mul_pow, mul_pow, sq_abs s, ← Real.exp_nat_mul]
        push_cast
        ring_nf
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact hd.trans he

/-- A unit half-line source reads one atom at aperture `a` with phase `−2ra`. -/
private def reading (δ a r : ℝ) (v : ℝ → ℝ) : ℝ :=
  (Complex.exp (((-2 * r * a : ℝ) : ℂ) * I) * moment δ r v ^ 2).re

/-- Cost per unit ordinate displacement for a unit-norm source. -/
def parityTransportCost (δ a : ℝ) : ℝ :=
  2 * |a| * Real.sqrt (1 / (2 * δ)) ^ 2 +
    2 * Real.sqrt (1 / (2 * δ)) * Real.sqrt (2 / (2 * δ) ^ 3)

private theorem reading_sub_le {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1) (a r t : ℝ) :
    |reading δ a r v - reading δ a t v| ≤ parityTransportCost δ a * |r - t| := by
  let p (k : ℝ) := Complex.exp (((-2 * k * a : ℝ) : ℂ) * I)
  let w (k : ℝ) := moment δ k v
  let B := Real.sqrt (1 / (2 * δ))
  let D := Real.sqrt (2 / (2 * δ) ^ 3)
  have hw (k : ℝ) : ‖w k‖ ≤ B := moment_bound hδ hv hu k
  have hd : ‖w r - w t‖ ≤ |r - t| * D := moment_sub_bound hδ hv hu r t
  have hp : ‖p r - p t‖ ≤ 2 * |a| * |r - t| := by
    refine (norm_cexp_phase_sub_le _ _).trans_eq ?_
    rw [show -2 * r * a - -2 * t * a = (-2 * a) * (r - t) by ring, abs_mul, abs_mul]
    norm_num
  have hs : ‖w r + w t‖ ≤ 2 * B := (norm_add_le _ _).trans (by linarith [hw r, hw t])
  change |(p r * w r ^ 2).re - (p t * w t ^ 2).re| ≤ _
  rw [← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [show p r * w r ^ 2 - p t * w t ^ 2 =
      (p r - p t) * w r ^ 2 + p t * ((w r - w t) * (w r + w t)) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul, norm_pow, p, Complex.norm_exp_ofReal_mul_I, one_mul]
  calc _ ≤ (2 * |a| * |r - t|) * B ^ 2 + (|r - t| * D) * (2 * B) :=
      add_le_add (mul_le_mul hp (pow_le_pow_left₀ (norm_nonneg _) (hw r) 2)
        (by positivity) (by positivity))
        (mul_le_mul hd hs (norm_nonneg _) (by dsimp [D]; positivity))
    _ = _ := by unfold parityTransportCost; dsimp [B, D]; ring

private theorem form_eq_sum {m : ℕ} (δ a : ℝ) (t M : Fin m → ℝ) (v : ℝ → ℝ) :
    halfLineForm δ t M (aperturePhase t a) v = ∑ j, M j * reading δ a (t j) v := by
  simp only [halfLineForm, Complex.re_sum, aperturePhase, reading, mul_assoc,
    Complex.re_ofReal_mul, halfLinePairing, moment, wave]

private theorem form_transport {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {v : ℝ → ℝ}
    (hv : MemLp v 2 halfMeasure) (hu : ∫ s, v s ^ 2 ∂halfMeasure = 1)
    (a r : ℝ) (t M : Fin m → ℝ) (hM : ∀ j, 0 ≤ M j) :
    |halfLineForm δ t M (aperturePhase t a) v - (∑ j, M j) * reading δ a r v| ≤
      parityTransportCost δ a * ∑ j, M j * |t j - r| := by
  rw [form_eq_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hM j)]
  exact (mul_le_mul_of_nonneg_left (reading_sub_le hδ hv hu a (t j) r) (hM j)).trans_eq
    (by ring)

end

end GaloisForLFunctions.ExceptionalLayerTheory
