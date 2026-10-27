import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionSpace
import GaloisForLFunctions.RHTower.SeparatedBumpWeilPositivity

/-!
# Independent sections on separated intervals

Each interval carries its own real profile. Disjointness supplies the Lévy gain, while
symmetry of the arithmetic pair kernel turns mixed correlations into weighted row sums.
Below the pole scale these estimates give a square-mass floor for the original Weil form.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset RHTower Zeta23

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

theorem sectionSum_eq_zero {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hs : ∀ i u, δ / 2 < |u| → G i u = 0) (x : Fin N → ℝ) {u : ℝ}
    (hu : (∑ i, |x i|) + δ / 2 < |u|) : sectionSum G x u = 0 := by
  apply sum_eq_zero
  intro i _
  have hi : |x i| ≤ ∑ j, |x j| :=
    single_le_sum (fun j _ => abs_nonneg (x j)) (mem_univ i)
  exact translate_eq_zero (hs i) (x i) (by linarith only [hi, hu])

theorem hasCompactSupport_sectionSum {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hs : ∀ i u, δ / 2 < |u| → G i u = 0) (x : Fin N → ℝ) :
    HasCompactSupport (sectionSum G x) := by
  exact hasCompactSupport_of_abs_gt fun _ hu => sectionSum_eq_zero hs x hu

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
      change |g (u - p) * h (u - q)| ≤ (g (u - p) ^ 2 + h (u - q) ^ 2) / 2
      rw [abs_mul]
      nlinarith only [sq_nonneg (|g (u - p)| - |h (u - q)|),
        sq_abs (g (u - p)), sq_abs (h (u - q))]
    _ = ((∫ u, g u ^ 2) + ∫ u, h u ^ 2) / 2 := by
      rw [integral_div, integral_add hg2 hh2,
        integral_sub_right_eq_self (fun u => g u ^ 2) p,
        integral_sub_right_eq_self (fun u => h u ^ 2) q]

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
  have hfd := (contDiff_sectionSum hG x).continuous
  have hi : Integrable fun u => sectionSum G x u ^ 2 := by
    apply (hfd.pow 2).integrable_of_hasCompactSupport
    exact hasCompactSupport_of_abs_gt fun _ hu => by
      rw [sectionSum_eq_zero hs x hu]
      norm_num
  have hi' : Integrable fun u => sectionSum G x (u + t) ^ 2 := by
    exact hi.comp_add_right t
  have he : ∀ u, (sectionSum G x u - sectionSum G x (u + t)) ^ 2 =
      sectionSum G x u ^ 2 + sectionSum G x (u + t) ^ 2 := by
    intro u
    have hz := sectionSum_mul_add_eq_zero hs hδ hsep ht1 ht2 u
    nlinarith only [hz]
  simp_rw [he]
  rw [integral_add hi hi', integral_add_right_eq_self (fun u => sectionSum G x u ^ 2) t]
  ring

/-- Integrating the support gap gives the same Lévy gain for independent profiles. -/
theorem levy_sectionSum_ge {G : Fin N → ℝ → ℝ} {δ s : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (hδ : 0 < δ) (hδs : 2 * δ < s) {x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|) :
    2 * (∫ u, sectionSum G x u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t ≤
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t *
        ∫ u, (sectionSum G x u - sectionSum G x (u + t)) ^ 2)).toReal := by
  let f := sectionSum G x
  have hle : δ ≤ s - δ := by linarith only [hδs]
  have hfin := lintegral_levy_ne_top (contDiff_sectionSum hG x)
    (hasCompactSupport_sectionSum hs x)
  have hE : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hcont : ContinuousOn archLevyDensity (Icc δ (s - δ)) :=
    continuousOn_archLevyDensity.mono fun t ht => (lt_of_lt_of_le hδ ht.1 : 0 < t)
  have hint : IntegrableOn (fun t => 2 * (∫ u, f u ^ 2) * archLevyDensity t)
      (Ioo δ (s - δ)) :=
    (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).const_mul _
  have hnn : ∀ t ∈ Ioo δ (s - δ), 0 ≤ 2 * (∫ u, f u ^ 2) * archLevyDensity t :=
    fun t ht => mul_nonneg (by positivity) (archLevyDensity_pos (hδ.trans ht.1)).le
  have hrestr : ENNReal.ofReal (∫ t in Ioo δ (s - δ), 2 * (∫ u, f u ^ 2) * archLevyDensity t) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t *
        ∫ u, (f u - f (u + t)) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hnn))]
    calc ∫⁻ t in Ioo δ (s - δ), ENNReal.ofReal (2 * (∫ u, f u ^ 2) * archLevyDensity t)
        = ∫⁻ t in Ioo δ (s - δ), ENNReal.ofReal (archLevyDensity t *
            ∫ u, (f u - f (u + t)) ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          change ENNReal.ofReal (2 * (∫ u, sectionSum G x u ^ 2) * archLevyDensity t) = _
          rw [show (∫ u, (f u - f (u + t)) ^ 2) = 2 * ∫ u, f u ^ 2 from
            integral_sectionSum_sub_translate_sq hG hs hδ hsep ht.1 ht.2]
          congr 1
          ring
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (archLevyDensity t *
            ∫ u, (f u - f (u + t)) ^ 2) :=
          lintegral_mono_set fun t ht => (hδ.trans ht.1 : 0 < t)
  have hval : (∫ t in Ioo δ (s - δ), 2 * (∫ u, f u ^ 2) * archLevyDensity t) =
      2 * (∫ u, f u ^ 2) * ∫ t in δ..(s - δ), archLevyDensity t := by
    rw [integral_const_mul, intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  have h := ENNReal.toReal_mono hfin hrestr
  rwa [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo hnn), hval] at h

theorem integral_sectionSum_mul_exp {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (x : Fin N → ℝ) (k : ℝ) :
    ∫ u, sectionSum G x u * Real.exp (k * u) =
      ∑ i, Real.exp (k * x i) * ∫ u, G i u * Real.exp (k * u) := by
  have hint : ∀ i : Fin N, Integrable fun u => G i (u - x i) * Real.exp (k * u) := by
    intro i
    have hc : Continuous fun u => G i (u - x i) * Real.exp (k * u) :=
      ((hG i).continuous.comp (continuous_id.sub continuous_const)).mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    exact hc.integrable_of_hasCompactSupport
      (hasCompactSupport_of_abs_gt (R := |x i| + δ / 2) fun u hu => by
        change G i (u - x i) * Real.exp (k * u) = 0
        rw [translate_eq_zero (hs i) (x i) hu, zero_mul])
  simp only [sectionSum, sum_mul]
  rw [integral_finsetSum _ fun i _ => hint i]
  exact sum_congr rfl fun i _ => integral_translate_mul_exp (x i) k

/-- The whole pole product is paid by the sum of the independent square masses. -/
theorem abs_pole_sectionSum_le {G : Fin N → ℝ → ℝ} {δ s D : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (hδ : 0 < δ) (hδs : δ < s) {x : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| ≤ D) :
    |2 * ∫ p : ℝ × ℝ, sectionSum G x p.1 * sectionSum G x p.2 *
        Real.cosh ((p.1 - p.2) / 2)| ≤
      2 * Real.exp (δ / 2) * (Real.exp (D / 2) * δ) * N *
        ∫ u, sectionSum G x u ^ 2 := by
  let L : Fin N → ℝ := fun i => ∫ u, |G i u|
  let A : Fin N → ℝ := fun i => ∫ u, G i u * Real.exp (1 / 2 * u)
  let B : Fin N → ℝ := fun i => ∫ u, G i u * Real.exp (-1 / 2 * u)
  have hL0 : ∀ i, 0 ≤ L i := fun i => integral_nonneg fun u => abs_nonneg _
  have hA : ∀ i, |A i| ≤ Real.exp (δ / 4) * L i := fun i =>
    abs_integral_mul_exp_le (hG i) (hs i) (by norm_num)
  have hB : ∀ i, |B i| ≤ Real.exp (δ / 4) * L i := fun i =>
    abs_integral_mul_exp_le (hG i) (hs i) (by norm_num)
  have hexp : ∀ i j, Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j) ≤ Real.exp (D / 2) := by
    intro i j
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := (le_abs_self (x i - x j)).trans (hspan i j)
    linarith only [h]
  have heδ : Real.exp (δ / 4) * Real.exp (δ / 4) = Real.exp (δ / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hab : |(∑ i, Real.exp (1 / 2 * x i) * A i) *
      ∑ j, Real.exp (-1 / 2 * x j) * B j| ≤
      Real.exp (δ / 2) * Real.exp (D / 2) * (∑ i, L i) ^ 2 := by
    rw [sum_mul_sum, sq, sum_mul_sum, mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro i _
    rw [mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j _
    calc |Real.exp (1 / 2 * x i) * A i * (Real.exp (-1 / 2 * x j) * B j)|
        = (Real.exp (1 / 2 * x i) * Real.exp (-1 / 2 * x j)) * (|A i| * |B j|) := by
          simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
          ring
      _ ≤ Real.exp (D / 2) * ((Real.exp (δ / 4) * L i) * (Real.exp (δ / 4) * L j)) := by
          exact mul_le_mul (hexp i j) (mul_le_mul (hA i) (hB j) (abs_nonneg _) (by positivity))
            (by positivity) (Real.exp_pos _).le
      _ = Real.exp (δ / 2) * Real.exp (D / 2) * (L i * L j) := by
          rw [← heδ]
          ring
  have hsq : (∑ i, L i) ^ 2 ≤ (N : ℝ) * (δ * ∑ i, ∫ u, G i u ^ 2) := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin N))) (f := L)
    simp only [card_univ, Fintype.card_fin] at hcs
    apply hcs.trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    rw [mul_sum]
    exact sum_le_sum fun i _ => sq_integral_abs_le (hG i) (hs i) hδ
  rw [integral_prod_cosh_eq (hasCompactSupport_sectionSum hs x)
    (contDiff_sectionSum hG x).continuous]
  have he₁ : (fun u => sectionSum G x u * Real.exp (u / 2)) =
      fun u => sectionSum G x u * Real.exp (1 / 2 * u) := by funext u; congr 2; ring
  have he₂ : (fun u => sectionSum G x u * Real.exp (-u / 2)) =
      fun u => sectionSum G x u * Real.exp (-1 / 2 * u) := by funext u; congr 2; ring
  rw [he₁, he₂, integral_sectionSum_mul_exp hG hs, integral_sectionSum_mul_exp hG hs,
    abs_mul, abs_two, integral_sectionSum_sq hG hs hδs hsep]
  have h := hab.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
  change 2 * |(∑ i, Real.exp (1 / 2 * x i) * A i) *
    ∑ j, Real.exp (-1 / 2 * x j) * B j| ≤ _
  nlinarith only [h]

/-- Only pairs whose intervals align at the chosen lag can contribute. -/
theorem abs_correlation_sectionSum_le {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (x : Fin N → ℝ) (t : ℝ) :
    |∫ u, sectionSum G x u * sectionSum G x (u - t)| ≤
      ∑ i, ∑ j, ((sectionMass (G i) + sectionMass (G j)) / 2) *
        (if |t - (x i - x j)| ≤ δ then 1 else 0) := by
  rw [integral_sectionSum_mul_sub hG hs]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j _
  split_ifs with h
  · rw [mul_one]
    exact abs_integral_mixed_translate_le (hG i) (hG j) (hs i) (hs j) _ _
  · have hfar : δ < |x i - (t + x j)| := by
      rw [show x i - (t + x j) = -(t - (x i - x j)) by ring, abs_neg]
      exact lt_of_not_ge h
    simp_rw [mixed_translate_eq_zero (hs i) (hs j) hfar]
    simp only [integral_zero, abs_zero, mul_zero, le_refl]

/-- Symmetric row bounds act on independent square masses, without a common profile. -/
theorem mass_pairKernel_le {G : Fin N → ℝ → ℝ} {x : Fin N → ℝ} {δ R : ℝ}
    (hrow : ∀ i, ∑ j, pairKernel δ x i j ≤ R) :
    ∑ i, ∑ j, ((sectionMass (G i) + sectionMass (G j)) / 2) * pairKernel δ x i j ≤
      R * ∑ i, sectionMass (G i) := by
  have he : (∑ i, ∑ j, ((sectionMass (G i) + sectionMass (G j)) / 2) * pairKernel δ x i j) =
      ∑ i, sectionMass (G i) * ∑ j, pairKernel δ x i j := by
    simp only [add_div, add_mul, sum_add_distrib, ← sum_div, div_mul_eq_mul_div]
    have hsym : (∑ i, ∑ j, sectionMass (G j) * pairKernel δ x i j) =
        ∑ i, ∑ j, sectionMass (G i) * pairKernel δ x i j := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by
        rw [pairKernel_symm δ x j i]
    simp only [← sum_div, hsym, ← mul_sum]
    ring
  rw [he, mul_sum]
  exact sum_le_sum fun i _ => by
    simpa only [mul_comm R] using mul_le_mul_of_nonneg_left (hrow i) (sectionMass_nonneg _)

def primeMajorant (δ : ℝ) (G : Fin N → ℝ → ℝ) (x : Fin N → ℝ) (n : ℕ) : ℝ :=
  ∑ i, ∑ j, ((sectionMass (G i) + sectionMass (G j)) / 2) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (if |Real.log n - (x i - x j)| ≤ δ then 1 else 0) +
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (if |Real.log n - (x j - x i)| ≤ δ then 1 else 0))

theorem vonMangoldt_mul_abs_sectionSum_logValue_le {G : Fin N → ℝ → ℝ} {δ : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (x : Fin N → ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n *
        |WeilOneSided.logValue (fun u => (sectionSum G x u : ℂ)) n| ≤
      primeMajorant δ G x n := by
  have h1 := abs_correlation_sectionSum_le hG hs x (Real.log n)
  have h2 := abs_correlation_sectionSum_le hG hs x (-Real.log n)
  have he : ∀ i j : Fin N, |-Real.log n - (x i - x j)| = |Real.log n - (x j - x i)| := by
    intro i j
    rw [show -Real.log n - (x i - x j) = -(Real.log n - (x j - x i)) by ring, abs_neg]
  simp_rw [he] at h2
  have hlog : WeilOneSided.logValue (fun u => (sectionSum G x u : ℂ)) n =
      ((∫ u, sectionSum G x u * sectionSum G x (u - Real.log n)) +
        ∫ u, sectionSum G x u * sectionSum G x (u - -Real.log n)) / Real.sqrt n := by
    unfold WeilOneSided.logValue
    rw [weilTest_ofReal_apply, weilTest_ofReal_apply, integral_complex_ofReal,
      integral_complex_ofReal]
    simp
  rw [hlog, abs_div, abs_of_nonneg (Real.sqrt_nonneg n)]
  have htri := abs_add_le (∫ u, sectionSum G x u * sectionSum G x (u - Real.log n))
    (∫ u, sectionSum G x u * sectionSum G x (u - -Real.log n))
  have h := mul_le_mul_of_nonneg_left (htri.trans (add_le_add h1 h2))
    (div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Real.sqrt_nonneg n))
  calc ArithmeticFunction.vonMangoldt n *
      (|(∫ u, sectionSum G x u * sectionSum G x (u - Real.log n)) +
        ∫ u, sectionSum G x u * sectionSum G x (u - -Real.log n)| / Real.sqrt n)
      = (ArithmeticFunction.vonMangoldt n / Real.sqrt n) *
          |(∫ u, sectionSum G x u * sectionSum G x (u - Real.log n)) +
            ∫ u, sectionSum G x u * sectionSum G x (u - -Real.log n)| := by ring
    _ ≤ _ := h
    _ = primeMajorant δ G x n := by
      unfold primeMajorant
      simp only [mul_add, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem sum_primeMajorant_le (δ : ℝ) (G : Fin N → ℝ → ℝ) (x : Fin N → ℝ)
    (T : Finset ℕ) :
    ∑ n ∈ T, primeMajorant δ G x n ≤
      ∑ i, ∑ j, ((sectionMass (G i) + sectionMass (G j)) / 2) * pairKernel δ x i j := by
  unfold primeMajorant
  rw [sum_comm]
  apply sum_le_sum
  intro i _
  rw [sum_comm]
  apply sum_le_sum
  intro j _
  rw [← mul_sum, sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (add_nonneg (sectionMass_nonneg _) (sectionMass_nonneg _)) (by norm_num))
  exact add_le_add (sum_indicator_le_nodeWeight T δ (x i - x j))
    (sum_indicator_le_nodeWeight T δ (x j - x i))

/-- The prime row estimate is uniform over every local shape in the section space. -/
theorem abs_linearCombination_sectionSum_le {G : Fin N → ℝ → ℝ} {δ R : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (x : Fin N → ℝ) (hrow : ∀ i, ∑ j, pairKernel δ x i j ≤ R)
    (F : WeilOneSided.WeilTestFn) (hF : F.1 = fun u => (sectionSum G x u : ℂ)) :
    |Finsupp.linearCombination ℝ (fun j : WeilOneSided.LogIndex => ArithmeticFunction.vonMangoldt j)
      (WeilOneSided.logVector F)| ≤ R * ∑ i, sectionMass (G i) := by
  apply le_trans _ (mass_pairKernel_le (G := G) hrow)
  let T := (WeilOneSided.logVector F).support
  rw [Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  simp_rw [WeilOneSided.logVector_apply, smul_eq_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  have hterm : ∀ j ∈ T, |WeilOneSided.logValue F.1 j * ArithmeticFunction.vonMangoldt j| ≤
      primeMajorant δ G x j := by
    intro j _
    rw [abs_mul, abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := j)), mul_comm, hF]
    exact vonMangoldt_mul_abs_sectionSum_logValue_le hG hs x j
  apply (sum_le_sum hterm).trans
  have he : ∑ j ∈ T, primeMajorant δ G x j =
      ∑ n ∈ T.map (Function.Embedding.subtype _), primeMajorant δ G x n :=
    (sum_map T (Function.Embedding.subtype _) (primeMajorant δ G x)).symm
  rw [he]
  exact sum_primeMajorant_le δ G x _

/-- Explicit prime and pole losses against the support-gap Lévy gain. -/
theorem le_weil_sectionSum {G : Fin N → ℝ → ℝ} {δ s D M : ℝ}
    (hG : ∀ i, ContDiff ℝ 2 (G i)) (hs : ∀ i u, δ / 2 < |u| → G i u = 0)
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδs : 2 * δ < s) (hM : 0 ≤ M)
    {x : Fin N → ℝ} (hsep : ∀ i j, i ≠ j → s ≤ |x i - x j|)
    (hspan : ∀ i j, |x i - x j| ≤ D) :
    (EF.gammaBracket 0 + Real.exp (-s / 2) * Real.log ((s - δ) / δ) -
        2 * Real.exp (δ / 2) * (Real.exp (D / 2) * δ) * N -
        (N * (6 * δ * (D + 1) * Real.exp (D / 2)) + 8 * (2 + 2 * M / s) +
          8 * N * Real.exp (-(M / 4)))) * ∫ u, sectionSum G x u ^ 2 ≤
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (sectionSum G x u : ℂ))
          (fun u => (sectionSum G x u : ℂ)))).re := by
  have hfd := contDiff_sectionSum hG x
  have hfc := hasCompactSupport_sectionSum hs x
  let F : WeilOneSided.WeilTestFn := ⟨fun u => (sectionSum G x u : ℂ),
    Complex.ofRealCLM.contDiff.comp hfd, hfc.comp_left Complex.ofReal_zero⟩
  rw [WeilOneSided.re_weilFullFunctional_eq
    (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) F]
  have hlev := levy_sectionSum_ge hG hs hδ hδs hsep
  have hint := integral_archLevyDensity_ge hδ hδs
  have hE : 0 ≤ ∫ u, sectionSum G x u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hgain := mul_le_mul_of_nonneg_left hint
    (by positivity : (0 : ℝ) ≤ 2 * ∫ u, sectionSum G x u ^ 2)
  have hpole := abs_pole_sectionSum_le hG hs hδ (by linarith only [hδ, hδs]) hsep hspan
  have hneg := neg_abs_le (2 * ∫ p : ℝ × ℝ,
    sectionSum G x p.1 * sectionSum G x p.2 * Real.cosh ((p.1 - p.2) / 2))
  have hrow := sum_pairKernel_le (D := D) (M := M) hδ hδ2
    (by linarith only [hδ, hδs]) hM hsep hspan
  have hprime := abs_linearCombination_sectionSum_le hG hs x hrow F rfl
  have hmass := integral_sectionSum_sq hG hs (by linarith only [hδ, hδs]) hsep
  change (∫ u, sectionSum G x u ^ 2) = ∑ i, sectionMass (G i) at hmass
  rw [← hmass] at hprime
  have hprime' := le_abs_self (Finsupp.linearCombination ℝ
    (fun j : WeilOneSided.LogIndex => ArithmeticFunction.vonMangoldt j) (WeilOneSided.logVector F))
  change _ ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (sectionSum G x u : ℂ))
    (fun u => (sectionSum G x u : ℂ))) - _
  rw [weilArchRe_eq_levy_pole hfd hfc]
  nlinarith only [hlev, hgain, hpole, hneg, hprime, hprime']

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SeparatedSections
