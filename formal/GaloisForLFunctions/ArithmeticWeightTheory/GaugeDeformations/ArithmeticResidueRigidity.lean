import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.ArithmeticResidueScaling
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.JointQuadraticScalingRigidity
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingMomentRigidity
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Endpoint obstruction for finite arithmetic mixtures

The mean profile has an unavoidable singular shift. A joint holomorphic
endpoint germ would instead force its actual Euler scaling limit to be
entire. Even agreement only on nearby positive real parameters and real
spectral values leads to this contradiction, by spectral uniqueness.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Every actual gauge fibre is spectrally holomorphic in its half-plane of
absolute convergence after multiplication by the pole factor. -/
private theorem analyticOnNhd_regularizedGaugeFibre (x : GaugeTorus) :
    AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * gaugeFibre x s) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  let b : ℝ := (1 + s.re) / 2
  have hb : 1 < b := by dsimp only [b]; linarith only [hs]
  have hbs : b < s.re := by dsimp only [b]; linarith only [hs]
  have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-b)) :=
    Nat.Primes.summable_rpow.mpr (by linarith only [hb])
  have hbound (p : Nat.Primes) : ‖twist x p - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖twist x p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_twist, norm_one]; norm_num
  have hsum : Summable (fun p : Nat.Primes => ‖twist x p - 1‖ * (p : ℝ) ^ (-b)) :=
    (hbase.mul_left 2).of_nonneg_of_le (fun p => by positivity)
      (fun p => mul_le_mul_of_nonneg_right (hbound p) (by positivity))
  have hF := (exists_isozeric (by linarith only [hb]) hsum).1 s hbs
  have ha := (differentiable_zetaResidueFactor.analyticAt s).mul hF.cexp
  apply ha.congr
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
  have hne : z ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hz
    exact lt_irrefl 1 hz
  change zetaResidueFactor z * Complex.exp (deformationExponent x z) = (z - 1) * gaugeFibre x z
  rw [zetaResidueFactor_of_ne hne, gaugeFibre_eq_zeta_mul_exp _ hz, mul_assoc]

/-- Real agreement just above one propagates across a right half-disc.
The accumulation point is chosen inside the real agreement interval. -/
private theorem eqOn_rightHalfDisc_of_real_agreement {F G : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (ball 1 r ∩ {s : ℂ | 1 < s.re}))
    (hG : AnalyticOnNhd ℂ G (ball 1 r ∩ {s : ℂ | 1 < s.re}))
    (heq : ∀ᶠ σ : ℝ in 𝓝[>] 1, F (σ : ℂ) = G (σ : ℂ)) :
    EqOn F G (ball 1 r ∩ {s : ℂ | 1 < s.re}) := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhdsWithin_iff.mp heq
  let d : ℝ := min r ε / 2
  have hd : 0 < d := div_pos (lt_min hr hε) (by norm_num)
  have hdr : d < r := by
    have hh := min_le_left r ε
    dsimp only [d]
    linarith only [hh, hr]
  have hdε : d < ε := by
    have hh := min_le_right r ε
    dsimp only [d]
    linarith only [hh, hε]
  let c : ℝ := 1 + d
  have hc1 : 1 < c := by dsimp only [c]; linarith only [hd]
  have hcr : (c : ℂ) ∈ ball (1 : ℂ) r := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hc1)]
    dsimp only [c]
    linarith only [hdr]
  have hcε : c ∈ ball (1 : ℝ) ε := by
    rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hc1)]
    dsimp only [c]
    linarith only [hdε]
  have hnear : ∀ᶠ σ : ℝ in 𝓝 c, F (σ : ℂ) = G (σ : ℂ) := by
    filter_upwards [isOpen_ball.mem_nhds hcε, (isOpen_Ioi.mem_nhds hc1)] with σ hσε hσ1
    exact hb ⟨hσε, hσ1⟩
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] c) (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto c).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact fun h => (ne_of_gt hσ) (Complex.ofReal_injective h)
  exact hF.eqOn_of_preconnected_of_frequently_eq hG
    ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt 1)).isPreconnected
    ⟨hcr, hc1⟩ (hmap.frequently (hnear.filter_mono nhdsWithin_le_nhds).frequently)

/-- Real Euler agreement of a joint germ gives the same limit along every
complex direction in the right half-plane. -/
private theorem joint_germ_inherits_residue_limit {q : ℕ} [NeZero q]
    {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (h1 : ∀ a, Φ a 1 = -1) (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1)
    {U : ℂ × ℂ → ℂ} (hU : AnalyticAt ℂ U (0, 1))
    (hagree : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ σ : ℝ in 𝓝[>] 1,
      U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (residueProfileGauge Φ ρ t) (σ : ℂ))
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun t : ℝ => U ((t : ℂ), 1 + (t : ℂ) * w) / (t : ℂ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (analyticSmoothingScalingProfile (residueAverage Φ) 0 w)) := by
  obtain ⟨r, hr, hUa⟩ := hU.exists_ball_analyticOnNhd
  have heq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      EqOn (fun s : ℂ => U ((t : ℂ), s))
        (fun s : ℂ => (s - 1) * gaugeFibre (residueProfileGauge Φ ρ t) s)
        (ball 1 r ∩ {s : ℂ | 1 < s.re}) := by
    filter_upwards [hagree, self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hr)] with t ht ht0 htr
    change 0 < t at ht0
    apply eqOn_rightHalfDisc_of_real_agreement hr _
      ((analyticOnNhd_regularizedGaugeFibre _).mono inter_subset_right) ht
    intro s hs
    have hq : ((t : ℂ), s) ∈ ball ((0 : ℂ), (1 : ℂ)) r := by
      rw [mem_ball, Prod.dist_eq, max_lt_iff]
      refine ⟨?_, hs.1⟩
      simpa only [dist_zero_right, norm_real, Real.norm_eq_abs, abs_of_pos ht0] using htr
    exact (hUa _ hq).comp (g := U) (f := fun s : ℂ => ((t : ℂ), s))
      (analyticAt_const.prod analyticAt_id)
  have hball : ∀ᶠ t : ℝ in 𝓝[>] 0, 1 + (t : ℂ) * w ∈ ball (1 : ℂ) r := by
    have ht : Tendsto (fun t : ℝ => 1 + (t : ℂ) * w) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
        ((show Continuous (fun t : ℝ => 1 + (t : ℂ) * w) by fun_prop).tendsto 0).mono_left
          nhdsWithin_le_nhds
    exact ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
  have hlim := (tendstoLocallyUniformlyOn_residueEuler hR hΦ hρ h1 hρ1 hu hρu).tendsto_at hw
  apply hlim.congr'
  filter_upwards [heq, hball, self_mem_nhdsWithin] with t ht hb ht0
  change 0 < t at ht0
  have hs : 1 < (1 + (t : ℂ) * w).re := by
    have hm := mul_pos ht0 hw
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    linarith only [hm]
  exact congrArg (fun z : ℂ => z / (t : ℂ) ^ 2) (ht ⟨hb, hs⟩).symm

/-- A finite arithmetic mean retains a positive real Taylor coefficient and
the corresponding nonremovable singular shift of its scaling profile. -/
theorem residueAverage_singular_shift {q : ℕ} [NeZero q]
    {Φ : (ZMod q)ˣ → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (h0 : ∀ a, Φ a 0 = 1) (h1 : ∀ a, Φ a 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1) :
    ∃ k : ℕ, 0 < k ∧ 0 < (smoothingTaylorCoefficient (residueAverage Φ) k).re ∧
      singularSmoothingUnit (residueAverage Φ) k 0 ≠ 0 ∧
      Tendsto (fun t : ℝ => continuedSmoothingProfile (residueAverage Φ) k (-(k : ℂ) + (t : ℂ) * I) *
        Complex.exp (smoothingTaylorCoefficient (residueAverage Φ) k * Complex.log ((t : ℂ) * I)))
        (𝓝[>] 0) (𝓝 (singularSmoothingUnit (residueAverage Φ) k 0)) ∧
      ¬ ∃ F : ℂ → ℂ, ContinuousAt F (-(k : ℂ)) ∧
        ∀ᶠ t : ℝ in 𝓝[>] 0, F (-(k : ℂ) + (t : ℂ) * I) =
          continuedSmoothingProfile (residueAverage Φ) k (-(k : ℂ) + (t : ℂ) * I) := by
  obtain ⟨ha, hz, ho, ht⟩ := residueAverage_properties hR hΦ h0 h1 hu
  exact (analyticSmoothing_endpoint_moment_rigidity hR ha hz ho ht).1

/-- No joint holomorphic endpoint germ agrees even with the nearby real
Euler values of a finite residue-class mixture. -/
theorem residueEuler_no_joint_endpoint_regularization {q : ℕ} [NeZero q]
    {Φ : (ZMod q)ˣ → ℂ → ℂ} {ρ : Nat.Primes → ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : ∀ a, AnalyticOnNhd ℂ (Φ a) (closedBall 0 R))
    (hρ : ∀ p : Nat.Primes, (p : ℕ) ∣ q → AnalyticOnNhd ℂ (ρ p) (closedBall 0 R))
    (h0 : ∀ a, Φ a 0 = 1) (h1 : ∀ a, Φ a 1 = -1)
    (hρ1 : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ρ p 1 = -1)
    (hu : ∀ a, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ a (x : ℂ)‖ = 1)
    (hρu : ∀ p : Nat.Primes, (p : ℕ) ∣ q → ∀ x : ℝ, x ∈ Icc 0 1 → ‖ρ p (x : ℂ)‖ = 1) :
    ¬ ∃ U : ℂ × ℂ → ℂ, AnalyticAt ℂ U (0, 1) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᶠ σ : ℝ in 𝓝[>] 1,
        U ((t : ℂ), (σ : ℂ)) = ((σ : ℂ) - 1) * gaugeFibre (residueProfileGauge Φ ρ t) (σ : ℂ) := by
  rintro ⟨U, hU, heq⟩
  obtain ⟨F, hFa, hFe⟩ := joint_quadratic_limit_entire hU
    (fun _ hw => joint_germ_inherits_residue_limit hR hΦ hρ h1 hρ1 hu hρu hU heq hw)
  obtain ⟨ha, hz, ho, ht⟩ := residueAverage_properties hR hΦ h0 h1 hu
  exact (analyticSmoothing_endpoint_moment_rigidity hR ha hz ho ht).2.1
    ⟨F, fun w => (hFa w (mem_univ _)).differentiableAt, hFe⟩

#print axioms residueAverage_singular_shift
#print axioms residueEuler_no_joint_endpoint_regularization
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
