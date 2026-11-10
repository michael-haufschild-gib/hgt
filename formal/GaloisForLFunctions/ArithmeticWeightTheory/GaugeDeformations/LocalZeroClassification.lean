import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LocalResidueClassification
import GaloisForLFunctions.ArithmeticWeightTheory.TheEdgeDivisorOfAFibre
import Mathlib.Analysis.Meromorphic.Order

/-!
# Local edge zeros and reciprocal-ζ continuation

A gauge fibre has a holomorphic germ vanishing at one exactly when its
prime phases differ from the Liouville phases by an absolutely summable
perturbation at some exponent below one. Every such zero is simple.

Translation by a half turn reverses the prime phases. The product of the
two fibres is a nonvanishing analytic factor on `Re s>1/2`, since their
first-order Euler terms cancel. Dividing out the simple zero converts the
problem into local pole preservation for the translated fibre.

The original germ extends meromorphically as `exp(J)/ζ` on a half-plane
left of one. Every ζ zero becomes a pole with exactly the same multiplicity.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Translation by a half turn at every prime reverses every prime phase. -/
def liouvilleTranslate (x : GaugeTorus) : GaugeTorus :=
  x + fun _ => ((1 / 2 : ℝ) : UnitAddCircle)

theorem twist_liouvilleTranslate_prime (x : GaugeTorus) (p : Nat.Primes) :
    twist (liouvilleTranslate x) p = -twist x p := by
  rcases p with ⟨p, hp⟩
  rw [liouvilleTranslate, twist_add]
  have h : twist (fun _ => ((1 / 2 : ℝ) : UnitAddCircle)) p = (-1 : ℂ) := by
    rw [ArithmeticGaugeTheory.twist_prime_apply _ hp]
    rw [fourier_coe_apply, ← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  rw [h, mul_neg_one]

/-- The first-order Euler terms cancel after translation by the Liouville point. -/
def liouvillePairFactor (x : GaugeTorus) (s : ℂ) : ℂ :=
  cexp (hullRem s (twist x) + hullRem s (twist (liouvilleTranslate x)))

theorem analyticOnNhd_liouvillePairFactor (x : GaugeTorus) :
    AnalyticOnNhd ℂ (liouvillePairFactor x) PrimeTorusTheory.rightHalf :=
  ((analyticOnNhd_hullRem (norm_twist_prime x)).add
    (analyticOnNhd_hullRem (norm_twist_prime (liouvilleTranslate x)))).cexp

theorem liouvillePairFactor_ne_zero (x : GaugeTorus) (s : ℂ) :
    liouvillePairFactor x s ≠ 0 := Complex.exp_ne_zero _

theorem gaugeFibre_liouville_pair (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    gaugeFibre x s * gaugeFibre (liouvilleTranslate x) s = liouvillePairFactor x s := by
  have he (p : Nat.Primes) : eulerVar s (twist (liouvilleTranslate x)) p =
      -eulerVar s (twist x) p := by
    simp only [eulerVar, powCoeff, twist_liouvilleTranslate_prime, mul_neg]
  rw [← exp_tsum_eq_gaugeFibre x hs,
    ← exp_tsum_eq_gaugeFibre (liouvilleTranslate x) hs, ← Complex.exp_add]
  change cexp _ = cexp _
  congr 1
  rw [tsum_congr he, tsum_neg]
  ring

private theorem analyticAt_dslope_one {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1) :
    AnalyticAt ℂ (dslope G 1) 1 := by
  obtain ⟨p, hp⟩ := hG
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

private theorem polePoint_zero_tendsto :
    Tendsto (fun δ : ℝ => polePoint δ 0) (𝓝[>] 0) (𝓝 (1 : ℂ)) := by
  have h : ContinuousAt (fun δ : ℝ => polePoint δ 0) 0 := by
    unfold polePoint
    fun_prop
  simpa only [polePoint, add_zero, Complex.ofReal_one, Complex.ofReal_zero,
    zero_mul] using h.tendsto.mono_left nhdsWithin_le_nhds

/-- The universal Euler lower bound makes every holomorphic edge zero simple. -/
theorem deriv_ne_zero_of_local_gauge_zero {x : GaugeTorus} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1) (hGzero : G 1 = 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre x s) :
    deriv G 1 ≠ 0 := by
  have hD := analyticAt_dslope_one hG
  have hfac (s : ℂ) : (s - 1) * dslope G 1 s = G s := by
    simpa only [smul_eq_mul, hGzero, sub_zero] using sub_smul_dslope G 1 s
  let c : ℝ := Real.exp (-(4 * ∑' p : Nat.Primes, (p : ℝ) ^ (-2 : ℝ))) / 2
  have hc : 0 < c := div_pos (Real.exp_pos _) (by norm_num)
  intro hz
  have hDz : dslope G 1 1 = 0 := by rw [dslope_same, hz]
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖dslope G 1 (polePoint δ 0)‖ < c := by
    have ht := (hD.continuousAt.norm.tendsto.comp polePoint_zero_tendsto)
    rw [hDz, norm_zero] at ht
    exact ht.eventually (gt_mem_nhds hc)
  have he := polePoint_zero_tendsto.eventually hagree
  obtain ⟨δ, hlow, hsmallδ, heδ, hδ⟩ :=
    ((eventually_mul_le_norm_gaugeFibre x 0).and
      (hsmall.and (he.and self_mem_nhdsWithin))).exists
  have hδ₀ : 0 < δ := hδ
  have hre : 1 < (polePoint δ 0).re := by rw [polePoint_re]; linarith only [hδ₀]
  have hnorm : ‖polePoint δ 0 - 1‖ = δ := by
    have hpoint : polePoint δ 0 - 1 = (δ : ℂ) := by
      simp only [polePoint, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_add,
        Complex.ofReal_one, add_sub_cancel_left]
    rw [hpoint, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ₀]
  have hprod : ‖gaugeFibre x (polePoint δ 0)‖ = δ * ‖dslope G 1 (polePoint δ 0)‖ := by
    rw [← heδ hre, ← hfac (polePoint δ 0), norm_mul, hnorm]
  rw [hprod] at hlow
  change c * δ ≤ δ * ‖dslope G 1 (polePoint δ 0)‖ at hlow
  nlinarith only [hlow, mul_pos hδ₀ (sub_pos.mpr hsmallδ)]

/-- Reversing prime phases turns a local edge zero into a nonzero pole residue. -/
theorem local_zero_gives_liouville_residue {x : GaugeTorus} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1) (hGzero : G 1 = 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre x s) :
    ∃ U : ℂ → ℂ, AnalyticAt ℂ U 1 ∧ U 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re →
        U s = (s - 1) * gaugeFibre (liouvilleTranslate x) s := by
  have hD := analyticAt_dslope_one hG
  have hDne : dslope G 1 1 ≠ 0 := by
    rw [dslope_same]
    exact deriv_ne_zero_of_local_gauge_zero hG hGzero hagree
  have hE : AnalyticAt ℂ (liouvillePairFactor x) 1 :=
    analyticOnNhd_liouvillePairFactor x 1 (by change (1 / 2 : ℝ) < 1; norm_num)
  refine ⟨fun s => liouvillePairFactor x s / dslope G 1 s,
    hE.div hD hDne, div_ne_zero (liouvillePairFactor_ne_zero x 1) hDne, ?_⟩
  filter_upwards [hagree, hD.continuousAt.eventually_ne hDne] with s hs hds
  intro hse
  apply (div_eq_iff hds).mpr
  have hf : (s - 1) * dslope G 1 s = gaugeFibre x s := by
    simpa only [smul_eq_mul, hGzero, sub_zero, hs hse] using sub_smul_dslope G 1 s
  rw [← gaugeFibre_liouville_pair x hse, ← hf]
  ring

private theorem norm_liouville_perturbation (x : GaugeTorus) (p : Nat.Primes) :
    ‖twist (liouvilleTranslate x) p - 1‖ = ‖twist x p + 1‖ := by
  rw [twist_liouvilleTranslate_prime,
    show -twist x p - 1 = -(twist x p + 1) by ring, norm_neg]

/-- A holomorphic edge zero forces absolute Liouville perturbation summability below one. -/
theorem liouville_power_saving_of_local_zero {x : GaugeTorus} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1) (hGzero : G 1 = 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre x s) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ)) := by
  obtain ⟨U, hU, hUne, he⟩ := local_zero_gives_liouville_residue hG hGzero hagree
  obtain ⟨σ, hσ₀, hσ₁, hs⟩ := absolute_prime_below_one_of_local_residue hU hUne he
  exact ⟨σ, hσ₀, hσ₁, by simpa only [norm_liouville_perturbation] using hs⟩

#print axioms liouville_power_saving_of_local_zero

/-- Holomorphic vanishing at one is equivalent to absolute Liouville summability below one. -/
theorem local_gauge_zero_iff (x : GaugeTorus) :
    (∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧ G 1 = 0 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre x s) ↔
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ)) := by
  constructor
  · rintro ⟨G, hG, hGzero, he⟩
    exact liouville_power_saving_of_local_zero hG hGzero he
  · rintro ⟨σ, hσ₀, hσ₁, hs⟩
    have hf : Summable (fun p : Nat.Primes =>
        ‖twist (liouvilleTranslate x) p - 1‖ * (p : ℝ) ^ (-σ)) := by
      simpa only [norm_liouville_perturbation] using hs
    obtain ⟨U, hU, hUne, he⟩ := (local_nonzero_residue_iff (liouvilleTranslate x)).mpr
      ⟨σ, hσ₀, hσ₁, hf⟩
    have hE := analyticOnNhd_liouvillePairFactor x 1
      (show (1 : ℂ) ∈ PrimeTorusTheory.rightHalf by change (1 / 2 : ℝ) < 1; norm_num)
    refine ⟨fun s => (s - 1) * liouvillePairFactor x s / U s,
      (((analyticAt_id.sub analyticAt_const).mul hE).div hU hUne), ?_, ?_⟩
    · change (1 - 1) * liouvillePairFactor x 1 / U 1 = 0
      rw [sub_self, zero_mul, zero_div]
    · filter_upwards [he, hU.continuousAt.eventually_ne hUne] with s hs hUs
      intro hse
      apply (div_eq_iff hUs).mpr
      rw [hs hse, ← gaugeFibre_liouville_pair x hse]
      ring

/-- The exponent of the nonvanishing factor multiplying reciprocal ζ. -/
def liouvilleExponent (x : GaugeTorus) (s : ℂ) : ℂ :=
  hullRem s (twist x) + hullRem s (twist (liouvilleTranslate x)) -
    deformationExponent (liouvilleTranslate x) s

/-- The reciprocal-ζ continuation, with its removable value fixed at the edge zero. -/
def liouvilleContinuation (x : GaugeTorus) (s : ℂ) : ℂ :=
  (s - 1) * cexp (liouvilleExponent x s) / zetaResidueFactor s

theorem analyticOnNhd_liouvilleExponent {x : GaugeTorus} {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ))) :
    AnalyticOnNhd ℂ (liouvilleExponent x) {s : ℂ | σ < s.re} := by
  have hf : Summable (fun p : Nat.Primes =>
      ‖twist (liouvilleTranslate x) p - 1‖ * (p : ℝ) ^ (-σ)) := by
    simpa only [norm_liouville_perturbation] using hs
  have hsub : {s : ℂ | σ < s.re} ⊆ PrimeTorusTheory.rightHalf := fun s hs => hσ.trans_lt hs
  exact (((analyticOnNhd_hullRem (norm_twist_prime x)).mono hsub).add
    ((analyticOnNhd_hullRem (norm_twist_prime (liouvilleTranslate x))).mono hsub)).sub
      (exists_isozeric hσ hf).1

/-- The explicit continuation agrees with the actual gauge Dirichlet series. -/
theorem liouvilleContinuation_eq_gaugeFibre (x : GaugeTorus) {s : ℂ} (hs : 1 < s.re) :
    liouvilleContinuation x s = gaugeFibre x s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hζ := riemannZeta_ne_zero_of_one_lt_re hs
  have hp := gaugeFibre_liouville_pair x hs
  rw [gaugeFibre_eq_zeta_mul_exp (liouvilleTranslate x) hs] at hp
  have he : cexp (liouvilleExponent x s) = gaugeFibre x s * riemannZeta s := by
    rw [liouvilleExponent, Complex.exp_sub]
    apply (div_eq_iff (Complex.exp_ne_zero _)).mpr
    simpa only [liouvillePairFactor, mul_assoc] using hp.symm
  rw [liouvilleContinuation, he, zetaResidueFactor_of_ne hs1]
  apply (div_eq_iff (mul_ne_zero (sub_ne_zero.mpr hs1) hζ)).mpr
  ring

theorem liouvilleContinuation_eq_div (x : GaugeTorus) {s : ℂ} (hs : s ≠ 1) :
    liouvilleContinuation x s = cexp (liouvilleExponent x s) / riemannZeta s := by
  rw [liouvilleContinuation, zetaResidueFactor_of_ne hs]
  calc
    _ = ((s - 1) / (s - 1)) * (cexp (liouvilleExponent x s) / riemannZeta s) := by
      rw [div_mul_div_comm]
    _ = _ := by rw [div_self (sub_ne_zero.mpr hs), one_mul]

theorem analyticAt_liouvilleContinuation_one {x : GaugeTorus} {σ : ℝ}
    (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ < 1)
    (hs : Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ))) :
    AnalyticAt ℂ (liouvilleContinuation x) 1 :=
  (((analyticAt_id.sub analyticAt_const).mul
    ((analyticOnNhd_liouvilleExponent hσ₀ hs) 1 hσ₁).cexp).div
    (differentiable_zetaResidueFactor.analyticAt 1) (by rw [zetaResidueFactor_one]; exact one_ne_zero))

theorem liouvilleContinuation_one (x : GaugeTorus) : liouvilleContinuation x 1 = 0 := by
  simp only [liouvilleContinuation, sub_self, zero_mul, zero_div]

/-- The continuation is meromorphic throughout the half-plane, including its simple edge zero. -/
theorem meromorphicOn_liouvilleContinuation {x : GaugeTorus} {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ))) :
    MeromorphicOn (liouvilleContinuation x) {s : ℂ | σ < s.re} := by
  intro s hsre
  exact (((analyticAt_id.sub analyticAt_const).mul
    ((analyticOnNhd_liouvilleExponent hσ hs) s hsre).cexp).meromorphicAt).div
      (differentiable_zetaResidueFactor.analyticAt s).meromorphicAt

/-- All ζ zero multiplicities become pole multiplicities of the continuation. -/
theorem liouvilleContinuation_order {x : GaugeTorus} {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (hs : Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ)))
    {s : ℂ} (hsre : σ < s.re) (hs1 : s ≠ 1) :
    meromorphicOrderAt (liouvilleContinuation x) s = -meromorphicOrderAt riemannZeta s := by
  have he : liouvilleContinuation x =ᶠ[𝓝[≠] s]
      (fun z => cexp (liouvilleExponent x z) / riemannZeta z) := by
    have hev : ∀ᶠ z in 𝓝 s, z ≠ (1 : ℂ) := isOpen_ne.mem_nhds hs1
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with z hz
    exact liouvilleContinuation_eq_div x hz
  rw [meromorphicOrderAt_congr he]
  have hJ := ((analyticOnNhd_liouvilleExponent hσ hs) s hsre).cexp
  change AnalyticAt ℂ (fun z => cexp (liouvilleExponent x z)) s at hJ
  change meromorphicOrderAt ((fun z => cexp (liouvilleExponent x z)) / riemannZeta) s = _
  have ho : meromorphicOrderAt (fun z => cexp (liouvilleExponent x z)) s = 0 := by
    rw [hJ.meromorphicOrderAt_eq, hJ.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)]
    rfl
  have hζdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζ : AnalyticAt ℂ riemannZeta s :=
    hζdiff.analyticOnNhd isOpen_compl_singleton s hs1
  rw [meromorphicOrderAt_div hJ.meromorphicAt hζ.meromorphicAt, ho, zero_sub]

private theorem local_zero_germ_unique {G W : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1) (hW : AnalyticAt ℂ W 1)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = W s) :
    G =ᶠ[𝓝 (1 : ℂ)] W := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (hG.eventually_analyticAt.and (hW.eventually_analyticAt.and hagree))
  have hg : AnalyticOnNhd ℂ G (ball 1 r) := fun s hs => (hb hs).1
  have hw : AnalyticOnNhd ℂ W (ball 1 r) := fun s hs => (hb hs).2.1
  let c : ℂ := 1 + ((r / 2 : ℝ) : ℂ)
  have hc : c ∈ ball 1 r := by
    dsimp [c]
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith only [hr] : 0 < r / 2)]
    linarith only [hr]
  have hce : 1 < c.re := by dsimp [c]; linarith only [hr]
  have he : G =ᶠ[𝓝 c] W := by
    filter_upwards [isOpen_ball.mem_nhds hc,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hce] with s hs hse
    exact (hb hs).2.2 hse
  have hid := hg.eqOn_of_preconnected_of_eventuallyEq hw
    (convex_ball (1 : ℂ) r).isPreconnected hc he
  filter_upwards [ball_mem_nhds (1 : ℂ) hr] with s hs
  exact hid hs

/-- The original local zero extends with exactly the opposite divisor to ζ. -/
theorem local_zero_reciprocal_continuation {x : GaugeTorus} {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 1) (hGzero : G 1 = 0)
    (hagree : ∀ᶠ s in 𝓝 (1 : ℂ), 1 < s.re → G s = gaugeFibre x s) :
    deriv G 1 ≠ 0 ∧ ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 ∧
      Summable (fun p : Nat.Primes => ‖twist x p + 1‖ * (p : ℝ) ^ (-σ)) ∧
      AnalyticOnNhd ℂ (liouvilleExponent x) {s : ℂ | σ < s.re} ∧
      MeromorphicOn (liouvilleContinuation x) {s : ℂ | σ < s.re} ∧
      (G =ᶠ[𝓝 (1 : ℂ)] liouvilleContinuation x) ∧
      (∀ s : ℂ, 1 < s.re → liouvilleContinuation x s = gaugeFibre x s) ∧
      ∀ s : ℂ, σ < s.re → s ≠ 1 →
        meromorphicOrderAt (liouvilleContinuation x) s = -meromorphicOrderAt riemannZeta s := by
  refine ⟨deriv_ne_zero_of_local_gauge_zero hG hGzero hagree, ?_⟩
  obtain ⟨σ, hσ₀, hσ₁, hs⟩ := liouville_power_saving_of_local_zero hG hGzero hagree
  refine ⟨σ, hσ₀, hσ₁, hs, analyticOnNhd_liouvilleExponent hσ₀.le hs,
    meromorphicOn_liouvilleContinuation hσ₀.le hs, ?_,
    fun s hse => liouvilleContinuation_eq_gaugeFibre x hse,
    fun s hsre hs1 => liouvilleContinuation_order hσ₀.le hs hsre hs1⟩
  apply local_zero_germ_unique hG (analyticAt_liouvilleContinuation_one hσ₀.le hσ₁ hs)
  filter_upwards [hagree] with s he
  intro hsre
  exact (he hsre).trans (liouvilleContinuation_eq_gaugeFibre x hsre).symm

#print axioms local_gauge_zero_iff
#print axioms liouvilleContinuation_order
#print axioms local_zero_reciprocal_continuation

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
