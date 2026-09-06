import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mellin transformation of compactly weighted Möbius sources

The actual series `sum mu(n) * w(n*t)` has Mellin transform
`mellin w s / zeta(s)` on the half-plane of absolute convergence. The proof
establishes integrability before interchanging the series and integral.
Compactly supported bounded measurable weights give finite source sums,
measurability, a uniform inverse-time bound and local integrability.

These statements concern the actual weighted arithmetic source. They do not
assert a critical half-power bound or a vanishing approximation error.
-/

noncomputable section
open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology LSeries.notation Moebius
namespace RHTower

/-- The actual integer-dilation source, with its zero Möbius term included. -/
def chronologicalMobiusWeightedSource (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (moebius n : ℂ) * w ((n : ℝ) * t)

private theorem mellin_norm_dilate (w : ℝ → ℂ) (s : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * w (a*t)‖) =
      a ^ (-s.re) * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * w t‖ := by
  let F : ℝ → ℝ := fun t => ‖(t : ℂ) ^ (s-1) * w t‖
  have heq (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      ‖(t : ℂ) ^ (s-1) * w (a*t)‖ = a ^ (1-s.re) * F (a*t) := by
    have ht0 : 0 < t := ht
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha ht0)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [Real.mul_rpow ha.le ht0.le]
    have hp : a ^ (1-s.re) * a ^ (s.re-1) = 1 := by
      rw [← Real.rpow_add ha]
      simp
    calc
      t ^ (s.re-1) * ‖w (a*t)‖ = 1 * (t ^ (s.re-1) * ‖w (a*t)‖) := by ring
      _ = (a ^ (1-s.re) * a ^ (s.re-1)) * (t ^ (s.re-1) * ‖w (a*t)‖) := by rw [hp]
      _ = a ^ (1-s.re) * (a ^ (s.re-1) * t ^ (s.re-1) * ‖w (a*t)‖) := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul,
    integral_comp_mul_left_Ioi F 0 ha, mul_zero, smul_eq_mul]
  have hp : a ^ (1-s.re) * a⁻¹ = a ^ (-s.re) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ha]
    congr 1
    ring
  simpa [F, mul_assoc] using congrArg (fun x : ℝ => x * ∫ t : ℝ in Ioi 0, F t) hp

private theorem integrable_tsum_of_norm_integrals {F : ℕ → ℝ → ℂ} {ν : Measure ℝ}
    (hi : ∀ n, Integrable (F n) ν)
    (hs : Summable (fun n => ∫ t, ‖F n t‖ ∂ν)) :
    Integrable (fun t => ∑' n, F n t) ν := by
  refine ⟨(AEMeasurable.tsum (fun n => (hi n).aemeasurable)).aestronglyMeasurable, ?_⟩
  apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun n => (hi n).1.enorm)]
  simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun t => norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

private theorem mobius_weight_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖(moebius n : ℂ)‖ / (n : ℝ)^s.re) := by
  have h := (LSeriesSummable_moebius_iff.mpr hs).norm
  refine h.congr (fun n => ?_)
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · subst n; simp
  · simp [hn]

/-- Absolute Mellin interchange for the weighted Möbius source, including convergence of the resulting integral. -/
theorem chronologicalMobiusWeightedSource_hasMellin (w : ℝ → ℂ) {s : ℂ}
    (hs : 1 < s.re) (hw : MellinConvergent w s) :
    HasMellin (chronologicalMobiusWeightedSource w) s (mellin w s * (riemannZeta s)⁻¹) := by
  let F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s-1) * ((moebius n : ℂ) * w ((n : ℝ)*t))
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) := by
    by_cases hn : n = 0
    · subst n
      simp [F]
    · have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have h := ((MellinConvergent.comp_mul_left hn0).mpr hw).const_smul (moebius n : ℂ)
      simpa [MellinConvergent, smul_eq_mul, F] using h
  have hn (n : ℕ) : (∫ t : ℝ in Ioi 0, ‖F n t‖) =
      (‖(moebius n : ℂ)‖ / (n : ℝ) ^ s.re) *
        ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s-1) * w t‖ := by
    by_cases hn : n = 0
    · subst n
      simp [F]
    · have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have he (t : ℝ) : ‖F n t‖ = ‖(moebius n : ℂ)‖ * ‖(t : ℂ)^(s-1) * w ((n:ℝ)*t)‖ := by
        dsimp [F]
        simp only [norm_mul]
        ring
      simp_rw [he]
      rw [integral_const_mul, mellin_norm_dilate w s hn0, Real.rpow_neg hn0.le]
      ring
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    simp_rw [hn]
    exact (mobius_weight_summable hs).mul_right _
  have hconv : MellinConvergent (chronologicalMobiusWeightedSource w) s := by
    simpa [MellinConvergent, IntegrableOn, chronologicalMobiusWeightedSource, smul_eq_mul, F, tsum_mul_left]
      using integrable_tsum_of_norm_integrals hi hsum
  refine ⟨hconv, ?_⟩
  have hswap := hasSum_integral_of_summable_integral_norm hi hsum
  have hv (n : ℕ) : (∫ t : ℝ in Ioi 0, F n t) =
      mellin w s * LSeries.term (fun n => (moebius n : ℂ)) s n := by
    by_cases hn : n = 0
    · subst n
      simp [F, LSeries.term]
    · have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      change mellin (fun t => (moebius n : ℂ) • w ((n:ℝ)*t)) s = _
      rw [mellin_const_smul, mellin_comp_mul_left w s hn0,
        LSeries.term_def₀ (by simp) s n, smul_eq_mul, smul_eq_mul]
      push_cast
      ring
  simp_rw [hv] at hswap
  have heq : mellin (chronologicalMobiusWeightedSource w) s = ∫ t : ℝ in Ioi 0, ∑' n, F n t := by
    unfold mellin chronologicalMobiusWeightedSource
    simp only [smul_eq_mul, F, tsum_mul_left]
  rw [heq, ← hswap.tsum_eq, tsum_mul_left]
  congr 1
  exact LSeries_moebius_eq_inv_riemannZeta hs

/-- The classical weighted Mellin identity on `Re s > 1`. -/
theorem chronologicalMobiusWeightedSource_mellin (w : ℝ → ℂ) {s : ℂ}
    (hs : 1 < s.re) (hw : MellinConvergent w s) :
    mellin (chronologicalMobiusWeightedSource w) s = mellin w s * (riemannZeta s)⁻¹ :=
  (chronologicalMobiusWeightedSource_hasMellin w hs hw).2

/-- A weight vanishing beyond a finite endpoint makes the arithmetic source an exact finite sum at every positive scale. -/
theorem chronologicalMobiusWeightedSource_eq_sum (w : ℝ → ℂ) (N : ℕ)
    {θ t : ℝ} (ht : 0 < t) (hw : ∀ x, θ < x → w x = 0)
    (hcut : θ < ((N:ℝ)+1)*t) :
    chronologicalMobiusWeightedSource w t =
      ∑ n ∈ Finset.range (N+1), (moebius n : ℂ) * w ((n:ℝ)*t) := by
  apply tsum_eq_sum
  intro n hn
  have hnN : N+1 ≤ n := Nat.le_of_not_gt (by simpa using hn)
  have hnR : (N:ℝ)+1 ≤ n := by exact_mod_cast hnN
  rw [hw _ (hcut.trans_le (mul_le_mul_of_nonneg_right hnR ht.le)), mul_zero]

/-- The source vanishes once the physical scale exceeds the positive support endpoint. -/
theorem chronologicalMobiusWeightedSource_eq_zero {w : ℝ → ℂ}
    {θ t : ℝ} (hθ : 0 ≤ θ) (hw : ∀ x, θ < x → w x = 0) (ht : θ < t) :
    chronologicalMobiusWeightedSource w t = 0 := by
  rw [chronologicalMobiusWeightedSource_eq_sum w 0 (hθ.trans_lt ht) hw (by simpa using ht)]
  simp

/-- Measurable weights give a measurable weighted source. -/
theorem chronologicalMobiusWeightedSource_measurable {w : ℝ → ℂ}
    (hw : Measurable w) : Measurable (chronologicalMobiusWeightedSource w) := by
  unfold chronologicalMobiusWeightedSource
  fun_prop

/-- A weight bounded by `C` on the positive half-line and vanishing beyond one gives the uniform source bound `2*C/t`. -/
theorem chronologicalMobiusWeightedSource_norm_bound {w : ℝ → ℂ} {C t : ℝ}
    (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0) (ht : 0 < t) :
    ‖chronologicalMobiusWeightedSource w t‖ ≤ 2*C/t := by
  by_cases ht1 : 1 < t
  · rw [chronologicalMobiusWeightedSource_eq_zero (by positivity : (0:ℝ) ≤ 1) htop ht1]
    simpa only [norm_zero] using (div_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2) hC) ht.le)
  have ht1 : t ≤ 1 := le_of_not_gt ht1
  let N : ℕ := ⌊1/t⌋₊
  have hcut : (1:ℝ) < ((N:ℝ)+1)*t := by
    have h := Nat.lt_floor_add_one (1/t)
    exact (div_lt_iff₀ ht).mp h
  rw [chronologicalMobiusWeightedSource_eq_sum w N ht htop hcut]
  have hsum : ‖∑ n ∈ Finset.range (N+1), (moebius n : ℂ) * w ((n:ℝ)*t)‖ ≤ ((N:ℝ)+1)*C := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N+1), ‖(moebius n : ℂ) * w ((n:ℝ)*t)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range (N+1), C := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : n = 0
        · subst n; simpa using hC
        · have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          rw [norm_mul]
          have hm : ‖(moebius n : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]
            exact_mod_cast (abs_moebius_le_one (n := n))
          exact (mul_le_mul hm (hw _ (mul_pos hn0 ht)) (norm_nonneg _) (by positivity)).trans_eq (one_mul C)
      _ = ((N:ℝ)+1)*C := by simp
  have hN : (N:ℝ) ≤ 1/t := Nat.floor_le (by positivity)
  have hNt : ((N:ℝ)+1)*t ≤ 2 := by
    have hNt := (le_div_iff₀ ht).mp hN
    nlinarith
  apply hsum.trans
  rw [le_div_iff₀ ht]
  nlinarith

/-- The actual weighted source is locally integrable on the positive half-line for bounded measurable weights supported below one. -/
theorem chronologicalMobiusWeightedSource_locallyIntegrable {w : ℝ → ℂ} {C : ℝ}
    (hm : Measurable w) (hC : 0 ≤ C) (hw : ∀ x, 0 < x → ‖w x‖ ≤ C)
    (htop : ∀ x, 1 < x → w x = 0) :
    LocallyIntegrableOn (chronologicalMobiusWeightedSource w) (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  refine ⟨Ioo (x/2) (x+1), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  apply IntegrableOn.of_bound measure_Ioo_lt_top
    (chronologicalMobiusWeightedSource_measurable hm).aestronglyMeasurable.restrict (4*C/x)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := by linarith [ht.1]
  apply (chronologicalMobiusWeightedSource_norm_bound hC hw htop ht0).trans
  rw [div_le_div_iff₀ ht0 hx0]
  nlinarith [ht.1]

end RHTower
