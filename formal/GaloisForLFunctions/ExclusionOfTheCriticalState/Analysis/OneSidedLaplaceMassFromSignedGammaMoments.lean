import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

/-!
# One-sided Laplace mass from signed gamma moments

The positive partial sums of the exponential series test a signed density on
the positive ray. Absolute summability of its signed gamma means gives a
uniform bound on their integrals. Thus at each damping between zero and one,
finite mass on one side forces finite absolute mass.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Gamma density of order n on the positive ray. -/
def primeGammaWeight (n : ℕ) (t : ℝ) : ℝ := t^n * Real.exp (-t) / n.factorial

/-- A one-sided exponential moment controls the absolute moment at the same
damping when the signed gamma means are absolutely summable. -/
theorem integrable_abs_of_posPart_of_summable_gamma_moments {f : ℝ → ℝ} {b : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hi : ∀ n, IntegrableOn (fun t => primeGammaWeight n t * f t) (Ioi 0))
    (hs : Summable fun n => |∫ t in Ioi (0:ℝ), primeGammaWeight n t * f t|)
    (hp : IntegrableOn (fun t => Real.exp (-b*t) * max (f t) 0) (Ioi 0)) :
    IntegrableOn (fun t => Real.exp (-b*t) * |f t|) (Ioi 0) := by
  let r := 1-b
  have hr : 0 ≤ r := sub_nonneg.mpr hb1
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  let w := fun n t => r^n * primeGammaWeight n t
  let P := fun N t => ∑ n ∈ Finset.range N, w n t
  have hw (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ w n t := by
    dsimp only [w,primeGammaWeight]; positivity
  have hsum (t : ℝ) : HasSum (fun n => w n t) (Real.exp (-b*t)) := by
    have h := (RHTower.summable_shift_terms 1 r t).hasSum
    rw [← RHTower.exp_shift_tsum, show 1-r=b by dsimp only [r]; ring] at h
    exact h.congr_fun fun n => by dsimp only [w,primeGammaWeight]; rw [neg_one_mul]; ring
  have hP (N : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ P N t ∧ P N t ≤ Real.exp (-b*t) := by
    exact ⟨Finset.sum_nonneg fun n _ => hw n ht,
      ((hsum t).summable.sum_le_tsum _ fun n _ => hw n ht).trans_eq (hsum t).tsum_eq⟩
  let g := fun N t => P N t * f t
  have eg (N : ℕ) : g N = fun t => ∑ n ∈ Finset.range N, r^n*(primeGammaWeight n t * f t) := by
    funext t; simp only [g,P,w,Finset.sum_mul,mul_assoc]
  have hgi (N : ℕ) : IntegrableOn (g N) (Ioi 0) := by
    rw [eg]; exact integrable_finsetSum _ fun n _ => (hi n).const_mul _
  let M := ∑' n, |∫ t in Ioi (0:ℝ), primeGammaWeight n t * f t|
  have hlow (N : ℕ) : -(∫ t in Ioi (0:ℝ), g N t) ≤ M := by
    rw [eg, integral_finsetSum _ fun n _ => (hi n).const_mul _, ← Finset.sum_neg_distrib]
    refine (Finset.sum_le_sum fun n _ => ?_).trans
      (hs.sum_le_tsum _ fun n _ => abs_nonneg _)
    rw [integral_const_mul]
    apply (neg_le_abs _).trans
    rw [abs_mul,abs_of_nonneg (pow_nonneg hr n)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hr hr1)
  let B := 2 * (∫ t in Ioi (0:ℝ), Real.exp (-b*t) * max (f t) 0) + M
  have hbound (N : ℕ) : (∫ t in Ioi (0:ℝ), |g N t|) ≤ B := by
    have e := integral_mono_ae (hgi N).abs ((hp.const_mul 2).sub (hgi N)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      obtain ⟨h0,h1⟩ := hP N (le_of_lt ht)
      change |P N t * f t| ≤ 2*(Real.exp (-b*t)*max (f t) 0) - P N t * f t
      rw [abs_mul,abs_of_nonneg h0]
      rcases le_total 0 (f t) with hy | hy
      · rw [max_eq_left hy,abs_of_nonneg hy]; linarith only [mul_le_mul_of_nonneg_right h1 hy]
      · simp only [max_eq_right hy, abs_of_nonpos hy, mul_zero, zero_sub, mul_neg, le_refl])
    simp only [Pi.sub_apply] at e
    rw [integral_sub (hp.const_mul 2) (hgi N),integral_const_mul] at e
    dsimp only [B]; linarith only [e,hlow N]
  have hlim (t : ℝ) : Tendsto (fun N => g N t) atTop (𝓝 (Real.exp (-b*t)*f t)) :=
    (hsum t).tendsto_sum_nat.mul_const _
  have hfi : IntegrableOn (fun t => Real.exp (-b*t)*f t) (Ioi 0) := by
    apply integrable_of_tendsto (Eventually.of_forall hlim) (fun n => (hgi n).1)
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := B))
    apply liminf_le_of_frequently_le'
    apply Frequently.of_forall
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hgi n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact hfi.abs.congr (Eventually.of_forall fun t => by simp only [abs_mul,abs_of_pos (Real.exp_pos _)])

#print axioms integrable_abs_of_posPart_of_summable_gamma_moments

end GaloisForLFunctions.ExclusionOfTheCriticalState
