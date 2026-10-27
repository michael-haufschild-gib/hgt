import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionSpace
import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity

/-!
# Independent sections on separated intervals

Each interval carries its own real profile. Disjointness supplies the Lévy gain, while
symmetry of the arithmetic pair kernel turns mixed correlations into weighted row sums.
Below the pole scale these estimates give a square-mass floor for the original Weil form.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset Finsupp RHTower Zeta23

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SeparatedSections

open RHTower.SeparatedBump

variable {N : ℕ}

/-- Independent local profiles translated to prescribed centres. -/
def sectionSum (G : Fin N → ℝ → ℝ) (x : Fin N → ℝ) (u : ℝ) : ℝ :=
  ∑ i, G i (u - x i)

theorem contDiff_sectionSum {G : Fin N → ℝ → ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (x : Fin N → ℝ) :
    ContDiff ℝ 2 (sectionSum G x) := by
  apply ContDiff.sum
  intro i _
  exact (hG i).comp (contDiff_id.sub contDiff_const)

theorem hasCompactSupport_sectionSum {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hs : ∀ i u, δ / 2 < |u| → G i u = 0) (x : Fin N → ℝ) :
    HasCompactSupport (sectionSum G x) := by
  apply HasCompactSupport.sum
  intro i _
  exact hasCompactSupport_of_abs_gt (R := |x i| + δ / 2) fun u hu =>
    translate_eq_zero (hs i) (x i) hu

/-- Two profiles cannot meet when their centres are farther apart than their width. -/
theorem mixed_translate_eq_zero {g h : ℝ → ℝ} {δ p q : ℝ}
    (hg : ∀ u, δ / 2 < |u| → g u = 0) (hh : ∀ u, δ / 2 < |u| → h u = 0)
    (hpq : δ < |p - q|) (u : ℝ) : g (u - p) * h (u - q) = 0 := by
  by_cases hgz : g (u - p) = 0
  · rw [hgz, zero_mul]
  by_cases hhz : h (u - q) = 0
  · rw [hhz, mul_zero]
  have h1 := abs_le_of_ne_zero hg hgz
  have h2 := abs_le_of_ne_zero hh hhz
  have h3 : |p - q| ≤ |u - p| + |u - q| := by
    calc |p - q| = |(u - q) - (u - p)| := by congr 1; ring
      _ ≤ |u - q| + |u - p| := abs_sub _ _
      _ = |u - p| + |u - q| := add_comm _ _
  linarith only [h1, h2, h3, hpq]

theorem integrable_mixed_translate {g h : ℝ → ℝ} {δ : ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hs : ∀ u, δ / 2 < |u| → g u = 0) (p q : ℝ) :
    Integrable fun u => g (u - p) * h (u - q) := by
  have hc : Continuous fun u => g (u - p) * h (u - q) :=
    (hg.continuous.comp (continuous_id.sub continuous_const)).mul
      (hh.continuous.comp (continuous_id.sub continuous_const))
  exact hc.integrable_of_hasCompactSupport
    (hasCompactSupport_of_abs_gt (R := |p| + δ / 2) fun u hu => by
      change g (u - p) * h (u - q) = 0
      rw [translate_eq_zero hs p hu, zero_mul])

/-- Young's inequality assigns each mixed correlation to its two local square masses. -/
theorem abs_integral_mixed_translate_le {g h : ℝ → ℝ} {δ : ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgs : ∀ u, δ / 2 < |u| → g u = 0) (hhs : ∀ u, δ / 2 < |u| → h u = 0)
    (p q : ℝ) :
    |∫ u, g (u - p) * h (u - q)| ≤ ((∫ u, g u ^ 2) + ∫ u, h u ^ 2) / 2 := by
  have hg2 : Integrable fun u => g (u - p) ^ 2 := by
    simpa only [sq] using integrable_mixed_translate hg hg hgs p p
  have hh2 : Integrable fun u => h (u - q) ^ 2 := by
    simpa only [sq] using integrable_mixed_translate hh hh hhs q q
  calc |∫ u, g (u - p) * h (u - q)| ≤ ∫ u, |g (u - p) * h (u - q)| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u, (g (u - p) ^ 2 + h (u - q) ^ 2) / 2 := by
      apply integral_mono (integrable_mixed_translate hg hh hgs p q).abs
        ((hg2.add hh2).div_const 2)
      intro u
      rw [abs_mul]
      nlinarith only [sq_nonneg (|g (u - p)| - |h (u - q)|),
        sq_abs (g (u - p)), sq_abs (h (u - q))]
    _ = ((∫ u, g u ^ 2) + ∫ u, h u ^ 2) / 2 := by
      rw [integral_div, integral_add hg2 hh2, integral_sub_right_eq_self,
        integral_sub_right_eq_self]

theorem integral_sectionSum_mul_sub {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (x : Fin N → ℝ) (t : ℝ) :
    ∫ u, sectionSum G x u * sectionSum G x (u - t) =
      ∑ i, ∑ j, ∫ u, G i (u - x i) * G j (u - (t + x j)) := by
  have he : ∀ u, sectionSum G x u * sectionSum G x (u - t) =
      ∑ i, ∑ j, G i (u - x i) * G j (u - (t + x j)) := by
    intro u
    simp only [sectionSum, sum_mul_sum]
    congr 1
    funext i
    congr 1
    funext j
    rw [show u - t - x j = u - (t + x j) by ring]
  simp_rw [he]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_mixed_translate (hG i) (hG j) (hs i) _ _]
  exact sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
    integrable_mixed_translate (hG i) (hG j) (hs i) _ _

/-- Separated supports make the total square mass the sum of the local masses. -/
theorem integral_sectionSum_sq {G : Fin N → ℝ → ℝ} {δ s : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (hδs : δ < s) {x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    ∫ u, sectionSum G x u ^ 2 = ∑ i, ∫ u, G i u ^ 2 := by
  have he := integral_sectionSum_mul_sub hG hs x 0
  simp only [sub_zero, zero_add, ← sq] at he
  rw [he]
  apply sum_congr rfl
  intro i _
  rw [sum_eq_single i]
  · simpa only [← sq] using integral_sub_right_eq_self (fun u => G i u ^ 2) (x i)
  · intro j _ hji
    have hz := mixed_translate_eq_zero (hs i) (hs j) (hδs.trans_le (hsep i j hji.symm))
    simp_rw [hz]
    exact integral_zero _ _
  · simp

theorem sectionSum_mul_add_eq_zero {G : Fin N → ℝ → ℝ} {δ s t : ℝ}
    (hs : ∀ i u, δ / 2 < |u| → G i u = 0) (hδ : 0 < δ) {x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) (ht1 : δ < t) (ht2 : t < s - δ)
    (u : ℝ) : sectionSum G x u * sectionSum G x (u + t) = 0 := by
  unfold sectionSum
  rw [sum_mul_sum]
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j _
  rw [show u + t - x j = u - (x j - t) by ring]
  apply mixed_translate_eq_zero (hs i) (hs j)
  by_cases hij : i = j
  · subst j
    rw [show x i - (x i - t) = t by ring, abs_of_pos (hδ.trans ht1)]
    exact ht1
  · have h1 := hsep i j hij
    have h2 := abs_sub_abs_le_abs_sub (x i - x j) (-t)
    rw [abs_neg, abs_of_pos (hδ.trans ht1)] at h2
    rw [show x i - x j - -t = x i - (x j - t) by ring] at h2
    linarith only [h1, h2, ht2]

/-- The gap between the intervals is a full-strength translation-energy window. -/
theorem integral_sectionSum_sub_translate_sq {G : Fin N → ℝ → ℝ} {δ s t : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (hδ : 0 < δ) {x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (ht1 : δ < t) (ht2 : t < s - δ) :
    ∫ u, (sectionSum G x u - sectionSum G x (u + t)) ^ 2 =
      2 * ∫ u, sectionSum G x u ^ 2 := by
  have hfc := hasCompactSupport_sectionSum hs x
  have hfd := (contDiff_sectionSum hG x).continuous
  have hi : Integrable fun u => sectionSum G x u ^ 2 :=
    (hfd.pow 2).integrable_of_hasCompactSupport (hfc.pow (by norm_num))
  have hi' : Integrable fun u => sectionSum G x (u + t) ^ 2 := by
    exact hi.comp_add_right t
  have he : ∀ u, (sectionSum G x u - sectionSum G x (u + t)) ^ 2 =
      sectionSum G x u ^ 2 + sectionSum G x (u + t) ^ 2 := by
    intro u
    have hz := sectionSum_mul_add_eq_zero hs hδ hsep ht1 ht2 u
    nlinarith only [hz]
  simp_rw [he]
  rw [integral_add hi hi', integral_add_right_eq_self]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SeparatedSections
