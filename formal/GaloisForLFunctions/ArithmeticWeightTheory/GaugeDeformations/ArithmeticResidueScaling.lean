import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticResiduePrimeDecomposition

/-!
# Principal-average scaling of arithmetic profile mixtures

The actual Euler product has a quadratic endpoint scale. Nonprincipal
characters and ramified primes disappear from its leading profile, which
is determined exactly by the Taylor coefficients of the principal mean.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
variable {q : ℕ} [NeZero q]

/-- Renormalization after removing the principal logarithmic divergence. -/
def normalizedResidueProfile (Φ : (ZMod q)ˣ → ℂ → ℂ) (ρ : Nat.Primes → ℂ → ℂ)
    (K : ℝ → ℂ → ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  zetaResidueFactor (1 + (t : ℂ) * w) * Complex.exp
    (-analyticSmoothingScalingLog (residueAverage Φ) 0 w +
      analyticSmoothingScaledRemainder (residueAverage Φ) 0 t w + K t (1 + (t : ℂ) * w) +
      residueHigherPrimeLog Φ ρ t (1 + (t : ℂ) * w) - hullRem (1 + (t : ℂ) * w) (twist 0))

private theorem normalizedResidueProfile_zero {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1)
    {K : ℝ → ℂ → ℂ} (hK0 : ∀ s, K 0 s = 0) (w : ℂ) :
    normalizedResidueProfile Φ ρ K 0 w = analyticSmoothingScalingProfile (residueAverage Φ) 0 w := by
  rw [normalizedResidueProfile, Complex.ofReal_zero, zero_mul, add_zero,
    zetaResidueFactor_one, one_mul, hK0, add_zero,
    analyticSmoothingScaledRemainder_zero hR (analyticOnNhd_residueAverage hΦ)
      (residueAverage_one h1) (fun k hk => (Nat.not_lt_zero k hk).elim),
    residueHigherPrimeLog_zero h1 hρ1]
  rw [show -analyticSmoothingScalingLog (residueAverage Φ) 0 w + 2 * hullRem 1 (twist 0) +
      hullRem 1 (twist (exponentialPhaseGauge 0)) - hullRem 1 (twist 0) =
      (hullRem 1 (twist 0) + hullRem 1 (twist (exponentialPhaseGauge 0))) +
        -analyticSmoothingScalingLog (residueAverage Φ) 0 w by ring,
    Complex.exp_add, exp_liouville_hullRem_pair, analyticSmoothingScalingProfile]

private theorem residue_scaled_re {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.re) :
    1 ≤ (1 + (t : ℂ) * w).re := by
  have hm := mul_nonneg ht hw.le
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  linarith only [hm]

private theorem exists_residue_scaling_rectangle {e : ℝ} (he : 0 < e)
    {S : Set ℂ} (hS : IsCompact S) (hhalf : S ⊆ {w : ℂ | 0 < w.re}) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧
      MapsTo (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) (Icc 0 a ×ˢ S)
        (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) := by
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn
    (continuous_id.continuousOn : ContinuousOn (fun w : ℂ => w) S)
  let M := max B 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMw (w : ℂ) (hw : w ∈ S) : ‖w‖ ≤ M := (hB w hw).trans (le_max_left _ _)
  have hMp : 0 < M + 1 := by linarith only [hM]
  let a := min 1 (e / (M + 1))
  have ha : 0 < a := lt_min zero_lt_one (div_pos he hMp)
  have ha1 : a ≤ 1 := min_le_left _ _
  have ham : a * (M + 1) ≤ e := (le_div_iff₀ hMp).mp (min_le_right _ _)
  let D : Set (ℝ × ℂ) := Icc 0 a ×ˢ S
  have hmaps : MapsTo (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) D
      (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}) := by
    intro v hv
    refine ⟨hv.1.1, ?_, ?_⟩
    · exact lt_of_lt_of_le (by linarith only [he]) (residue_scaled_re hv.1.1 (hhalf hv.2))
    · have him : |(1 + (v.1 : ℂ) * v.2).im| ≤ v.1 * ‖v.2‖ := by
        simp only [Complex.add_im, Complex.one_im, zero_add]
        apply (Complex.abs_im_le_norm _).trans_eq
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1.1]
      have hm := mul_le_mul hv.1.2 (hMw v.2 hv.2) (norm_nonneg v.2) ha.le
      exact him.trans_lt (by nlinarith only [hm, ham, ha])
  exact ⟨a, ha, ha1, hmaps⟩

private theorem continuousOn_principalScaledExponent {Ψ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΨ : AnalyticOnNhd ℂ Ψ (closedBall 0 R))
    {a : ℝ} (ha1 : a ≤ 1) {S : Set ℂ} (hS : IsCompact S)
    (hhalf : S ⊆ {w : ℂ | 0 < w.re}) :
    ContinuousOn (fun v : ℝ × ℂ => -analyticSmoothingScalingLog Ψ 0 v.2 +
      analyticSmoothingScaledRemainder Ψ 0 v.1 v.2 -
        hullRem (1 + (v.1 : ℂ) * v.2) (twist 0)) (Icc 0 a ×ˢ S) := by
  have hscaled : ContinuousOn (fun v : ℝ × ℂ => analyticSmoothingScaledRemainder Ψ 0 v.1 v.2)
      (Icc 0 a ×ˢ S) :=
    (continuousOn_analyticSmoothingScaledRemainder hR hΨ 0 hS
      (by simpa only [Nat.cast_zero, neg_zero] using hhalf)).mono
        (fun v hv => ⟨⟨hv.1.1, hv.1.2.trans ha1⟩, hv.2⟩)
  have hL : ContinuousOn (fun v : ℝ × ℂ => analyticSmoothingScalingLog Ψ 0 v.2)
      (Icc 0 a ×ˢ S) :=
    (analyticOnNhd_analyticSmoothingScalingLog hR hΨ 0).continuousOn.comp
      continuous_snd.continuousOn (fun v hv => by
        simpa only [Nat.cast_zero, neg_zero] using hhalf hv.2)
  have hzero : ContinuousOn (fun v : ℝ × ℂ => hullRem (1 + (v.1 : ℂ) * v.2) (twist 0))
      (Icc 0 a ×ˢ S) := by
    intro v hv
    have hs : 1 / 2 < (1 + (v.1 : ℂ) * v.2).re :=
      lt_of_lt_of_le (by norm_num) (residue_scaled_re hv.1.1 (hhalf hv.2))
    have hm : ContinuousAt (fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) v := by fun_prop
    have hz : ContinuousAt (fun s : ℂ => hullRem s (twist 0)) (1 + (v.1 : ℂ) * v.2) :=
      (analyticOnNhd_hullRem (norm_twist_prime 0) _ hs).continuousAt
    exact (hz.comp (g := fun s : ℂ => hullRem s (twist 0))
      (f := fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) hm).continuousWithinAt
  exact (hL.neg.add hscaled).sub hzero

private theorem continuousOn_scaledResidueHigherPrimeLog
    {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    (a : ℝ) {S : Set ℂ} (hhalf : S ⊆ {w : ℂ | 0 < w.re}) :
    ContinuousOn (fun v : ℝ × ℂ => residueHigherPrimeLog Φ ρ v.1 (1 + (v.1 : ℂ) * v.2))
      (Icc 0 a ×ˢ S) := by
  have hmap : Continuous (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) := by fun_prop
  apply (continuousOn_residueHigherPrimeLog hR hΦ hρ hu hρu (b := 3 / 4) (by norm_num)).comp
    hmap.continuousOn
  intro v hv
  exact ⟨hv.1.1, lt_of_lt_of_le (by norm_num) (residue_scaled_re hv.1.1 (hhalf hv.2))⟩

private theorem exists_continuousOn_normalizedResidueProfile
    {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {e : ℝ} (he : 0 < e) {K : ℝ → ℂ → ℂ}
    (hKc : ContinuousOn (fun v : ℝ × ℂ => K v.1 v.2)
      (Ici 0 ×ˢ {s : ℂ | 1 - e < s.re ∧ |s.im| < e}))
    {S : Set ℂ} (hS : IsCompact S) (hhalf : S ⊆ {w : ℂ | 0 < w.re}) :
    ∃ a : ℝ, 0 < a ∧ ContinuousOn (fun v : ℝ × ℂ => normalizedResidueProfile Φ ρ K v.1 v.2)
      (Icc 0 a ×ˢ S) := by
  obtain ⟨a, ha, ha1, hmaps⟩ := exists_residue_scaling_rectangle he hS hhalf
  have hmap : Continuous (fun v : ℝ × ℂ => (v.1, 1 + (v.1 : ℂ) * v.2)) := by fun_prop
  have hK : ContinuousOn (fun v : ℝ × ℂ => K v.1 (1 + (v.1 : ℂ) * v.2))
      (Icc 0 a ×ˢ S) := hKc.comp hmap.continuousOn hmaps
  have hH := continuousOn_scaledResidueHigherPrimeLog hR hΦ hρ hu hρu a hhalf
  have hP := continuousOn_principalScaledExponent hR (analyticOnNhd_residueAverage hΦ) ha1 hS hhalf
  have hE := (hP.add hK).add hH
  have heq : (fun v : ℝ × ℂ => -analyticSmoothingScalingLog (residueAverage Φ) 0 v.2 +
      analyticSmoothingScaledRemainder (residueAverage Φ) 0 v.1 v.2 -
        hullRem (1 + (v.1 : ℂ) * v.2) (twist 0) + K v.1 (1 + (v.1 : ℂ) * v.2) +
          residueHigherPrimeLog Φ ρ v.1 (1 + (v.1 : ℂ) * v.2)) =
      (fun v : ℝ × ℂ => -analyticSmoothingScalingLog (residueAverage Φ) 0 v.2 +
        analyticSmoothingScaledRemainder (residueAverage Φ) 0 v.1 v.2 +
          K v.1 (1 + (v.1 : ℂ) * v.2) + residueHigherPrimeLog Φ ρ v.1 (1 + (v.1 : ℂ) * v.2) -
            hullRem (1 + (v.1 : ℂ) * v.2) (twist 0)) := by
    funext v
    ring
  change ContinuousOn (fun v : ℝ × ℂ => -analyticSmoothingScalingLog (residueAverage Φ) 0 v.2 +
      analyticSmoothingScaledRemainder (residueAverage Φ) 0 v.1 v.2 -
        hullRem (1 + (v.1 : ℂ) * v.2) (twist 0) + K v.1 (1 + (v.1 : ℂ) * v.2) +
          residueHigherPrimeLog Φ ρ v.1 (1 + (v.1 : ℂ) * v.2)) (Icc 0 a ×ˢ S) at hE
  rw [heq] at hE
  have hm : Continuous (fun v : ℝ × ℂ => 1 + (v.1 : ℂ) * v.2) := by fun_prop
  have hZ : ContinuousOn (fun v : ℝ × ℂ => zetaResidueFactor (1 + (v.1 : ℂ) * v.2))
      (Icc 0 a ×ˢ S) := (differentiable_zetaResidueFactor.continuous.comp hm).continuousOn
  exact ⟨a, ha, hZ.mul hE.cexp⟩

private theorem residueEuler_scaled {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R)) (h1 : ∀ a, Φ a 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {K : ℝ → ℂ → ℂ}
    (hKe : ∀ t : ℝ, 0 ≤ t → ∀ s : ℂ, 1 < s.re →
      deformationPrimeSum (residueProfileGauge Φ ρ t) s =
        weightedProfilePrimeSum (fun _ => 1) (residueAverage Φ) t s + K t s)
    {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 0 < w.re) :
    ((1 + (t : ℂ) * w - 1) * gaugeFibre (residueProfileGauge Φ ρ t) (1 + (t : ℂ) * w)) /
      (t : ℂ) ^ 2 = normalizedResidueProfile Φ ρ K t w := by
  have hs : 1 < (1 + (t : ℂ) * w).re := by
    have hm := mul_pos ht hw
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hm]
  have hsne : 1 + (t : ℂ) * w ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hs
    exact lt_irrefl 1 hs
  have he : deformationExponent (residueProfileGauge Φ ρ t) (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) + (-analyticSmoothingScalingLog (residueAverage Φ) 0 w +
        analyticSmoothingScaledRemainder (residueAverage Φ) 0 t w + K t (1 + (t : ℂ) * w) +
        residueHigherPrimeLog Φ ρ t (1 + (t : ℂ) * w) - hullRem (1 + (t : ℂ) * w) (twist 0)) := by
    rw [deformationExponent, hKe t ht.le _ hs,
      principalProfilePrimeSum_scaled hR (analyticOnNhd_residueAverage hΦ) (residueAverage_one h1) ht hw,
      residueHigherPrimeLog_eq_gauge hu hρu ht.le]
    ring
  have hexp : Complex.exp (2 * (Real.log t : ℂ)) = (t : ℂ) ^ 2 := by
    simp only [two_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht, pow_two]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [gaugeFibre_eq_zeta_mul_exp _ hs, he, Complex.exp_add, hexp,
    normalizedResidueProfile, zetaResidueFactor_of_ne hsne]
  field_simp [htC]

/-- Every finite residue-class mixture has the actual locally uniform scaling
profile of its principal average. Ramified phases do not alter this limit. -/
theorem tendstoLocallyUniformlyOn_residueEuler {Φ : (ZMod q)ˣ → ℂ → ℂ}
    {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1) :
    TendstoLocallyUniformlyOn
      (fun t : ℝ => fun w : ℂ =>
        ((1 + (t : ℂ) * w - 1) * gaugeFibre (residueProfileGauge Φ ρ t) (1 + (t : ℂ) * w)) /
          (t : ℂ) ^ 2)
      (analyticSmoothingScalingProfile (residueAverage Φ) 0)
      (𝓝[>] (0 : ℝ)) {w : ℂ | 0 < w.re} := by
  obtain ⟨e, he, K, _, hKc, hK0, hKe⟩ := exists_residuePrime_correction hR hΦ hρ h1 hρ1 hu hρu
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_lt continuous_const Complex.continuous_re)).mpr
  intro S hhalf hS
  obtain ⟨a, ha, hc⟩ := exists_continuousOn_normalizedResidueProfile hR hΦ hρ hu hρu he hKc hS hhalf
  have hlim : TendstoUniformlyOn (normalizedResidueProfile Φ ρ K) (normalizedResidueProfile Φ ρ K 0)
      (𝓝[Icc (0 : ℝ) a] 0) S :=
    ((isCompact_Icc.prod hS).uniformContinuousOn_of_continuous hc).tendstoUniformlyOn ⟨le_rfl, ha.le⟩
  have hlim' : TendstoUniformlyOn (normalizedResidueProfile Φ ρ K) (normalizedResidueProfile Φ ρ K 0)
      (𝓝[>] (0 : ℝ)) S := fun V hV =>
    Filter.Eventually.filter_mono (nhdsGT_zero_le_Icc ha) (hlim V hV)
  rw [show normalizedResidueProfile Φ ρ K 0 = analyticSmoothingScalingProfile (residueAverage Φ) 0
    from funext (normalizedResidueProfile_zero hR hΦ h1 hρ1 hK0)] at hlim'
  intro V hV
  filter_upwards [hlim' V hV, self_mem_nhdsWithin] with t hlimt ht
  change 0 < t at ht
  intro w hw
  rw [residueEuler_scaled hR hΦ h1 hu hρu hKe ht (hhalf hw)]
  exact hlimt w hw

/-- Normalization at zero removes the zeroth Taylor coefficient from the
explicit principal-average scaling law. -/
theorem residueScalingProfile_eq_full {Φ : (ZMod q)ˣ → ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (h0 : ∀ a, Φ a 0 = 1) {w : ℂ} (hw : 0 < w.re) :
    analyticSmoothingScalingProfile (residueAverage Φ) 0 w = riemannZeta 2 * Complex.exp
      (-(∑' n : ℕ, smoothingTaylorCoefficient (residueAverage Φ) (n + 1) *
        Complex.log (w + ((n + 1 : ℕ) : ℂ)))) := by
  exact analyticSmoothingScalingProfile_eq_full hR (analyticOnNhd_residueAverage hΦ)
    (residueAverage_zero h0) (fun k hk => (Nat.not_lt_zero k hk).elim)
    (by simpa only [Nat.cast_zero, neg_zero] using hw)

#print axioms residueScalingProfile_eq_full
#print axioms tendstoLocallyUniformlyOn_residueEuler
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
