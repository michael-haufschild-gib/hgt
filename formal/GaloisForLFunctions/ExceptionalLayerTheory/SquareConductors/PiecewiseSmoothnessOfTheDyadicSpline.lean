import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SplineSampling
import GaloisForLFunctions.SignedWindowCriticality.TheContinuumCanonicalSystemIsTheJetHankelSystem

/-!
# Piecewise smoothness and knot regularity of the dyadic prime spline

The eight-box autocorrelation `splineAutoCorr = upow 1 7` is globally `C⁶` with
Lipschitz sixth derivative, and infinitely differentiable with uniformly bounded
derivatives of every order outside its nine even-integer knots. Composing with the
logarithm and square-root weight transfers `C^{6,1}` regularity and off-knot
smoothness to `dyadicSpline`, `C^{7,1}` regularity and ninth-order off-knot
bounds to the conductor integral profile `conductorSplineIntegral`, and `C^{4,1}`
regularity to the Euler-Maclaurin curvature profile `conductorCurvatureProfile`.
-/

noncomputable section
open Finset Filter Topology MeasureTheory
open scoped NNReal Convolution ContDiff
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.ArithmeticWeightTheory GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.SignedWindowCriticality
open RHTower.WeilDeletion
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Conductor-integral profile `Ψ̃(u) = (u / 2) ∫₀ᵘ dyadicSpline(t) / t² dt`. -/
def conductorSplineIntegral (u : ℝ) : ℝ :=
  (u / 2) * ∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2

/-- Second-derivative profile arising from `∂_t² [t · dyadicSpline(z / t²)] = Θ₂(z / t²) / t`. -/
def conductorCurvatureProfile (x : ℝ) : ℝ :=
  2 * x * deriv dyadicSpline x + 4 * x ^ 2 * iteratedDeriv 2 dyadicSpline x

/-- Even-integer knots of `(m + 1)`-fold uniform box convolution on `[-1, 1]`. -/
def upowKnots (m : ℕ) : Finset ℝ :=
  (Icc 0 (m + 1)).image fun i : ℕ => 2 * (i : ℝ) - ((m + 1 : ℕ) : ℝ)

/-- Multiplicative knots of `dyadicSpline` in `[exp(-8), 4 exp(8)]`. -/
def splineKnots : Finset ℝ :=
  ((upowKnots 7).image Real.exp) ∪ ((upowKnots 7).image fun u => Real.exp (u + Real.log 4))

theorem card_splineKnots_le : splineKnots.card ≤ 18 := by
  have h7 : (upowKnots 7).card ≤ 9 :=
    card_image_le.trans (by rw [Nat.card_Icc])
  calc splineKnots.card
      ≤ ((upowKnots 7).image Real.exp).card +
          ((upowKnots 7).image fun u => Real.exp (u + Real.log 4)).card := card_union_le _ _
    _ ≤ (upowKnots 7).card + (upowKnots 7).card := add_le_add card_image_le card_image_le
    _ ≤ 18 := by omega

theorem splineKnots_pos {t : ℝ} (ht : t ∈ splineKnots) : 0 < t := by
  rcases mem_union.mp ht with h1 | h2
  · obtain ⟨u, _, rfl⟩ := mem_image.mp h1; exact Real.exp_pos u
  · obtain ⟨u, _, rfl⟩ := mem_image.mp h2; exact Real.exp_pos _

theorem exp_neg_eight_mem_splineKnots : Real.exp (-8) ∈ splineKnots := by
  refine mem_union_left _ (mem_image.mpr ⟨-8, ?_, rfl⟩)
  exact mem_image.mpr ⟨(0 : ℕ), mem_Icc.mpr ⟨le_rfl, by decide⟩, by norm_num⟩

theorem four_mul_exp_eight_mem_splineKnots : 4 * Real.exp 8 ∈ splineKnots := by
  refine mem_union_right _ (mem_image.mpr ⟨8, ?_, ?_⟩)
  · exact mem_image.mpr ⟨(8 : ℕ), mem_Icc.mpr ⟨by decide, le_rfl⟩, by norm_num⟩
  · rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; ring

theorem dyadicSpline_eq_zero_outside {x : ℝ}
    (hx : x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8)) : dyadicSpline x = 0 := by
  have hx' : x ∉ Set.Icc (Real.exp (-8)) (Real.exp (8 + Real.log 4)) := by
    intro h; apply hx
    rwa [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), mul_comm] at h
  by_cases hp : 0 < x
  · simp only [dyadicSpline, if_pos hp, squarePrimeWeight_zero_outside hp hx',
      Complex.zero_re, mul_zero]
  · exact if_neg hp

/-! ### Global `C^{k,1}` regularity on compact positive support -/

private theorem abs_unif_one_le (t : ℝ) : |unif 1 t| ≤ 1 / 2 := by
  unfold unif
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem ht]; norm_num
  · rw [Set.indicator_of_notMem ht]; norm_num

private theorem lipschitz_upow_one_one : LipschitzWith 1 (upow 1 1) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have h1 := unif_convolution_eq one_pos (integrable_unif 1) x
  have h2 := unif_convolution_eq one_pos (integrable_unif 1) y
  change |upow 1 1 x - upow 1 1 y| ≤ (1 : ℝ) * |x - y|
  simp only [upow] at h1 h2 ⊢
  rw [h1, h2, one_mul]
  have hsub (c : ℝ) :
      |(∫ t in (0 : ℝ)..x + c, unif 1 t) - ∫ t in (0 : ℝ)..y + c, unif 1 t| ≤
        (1 / 2 : ℝ) * |x - y| := by
    rw [intervalIntegral.integral_interval_sub_left
      (integrable_unif 1).intervalIntegrable (integrable_unif 1).intervalIntegrable]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ))
      (a := y + c) (b := x + c) (f := unif 1) fun t _ => by
        rw [Real.norm_eq_abs]; exact abs_unif_one_le t
    rwa [Real.norm_eq_abs, add_sub_add_right_eq_sub] at hb
  have heq : (1 / (2 * (1 : ℝ)) * ((∫ t in (0 : ℝ)..x + 1, unif 1 t) -
        ∫ t in (0 : ℝ)..x - 1, unif 1 t)) -
      (1 / (2 * (1 : ℝ)) * ((∫ t in (0 : ℝ)..y + 1, unif 1 t) -
        ∫ t in (0 : ℝ)..y - 1, unif 1 t)) =
      (1 / 2 : ℝ) * (((∫ t in (0 : ℝ)..x + 1, unif 1 t) - ∫ t in (0 : ℝ)..y + 1, unif 1 t) -
        ((∫ t in (0 : ℝ)..x - 1, unif 1 t) - ∫ t in (0 : ℝ)..y - 1, unif 1 t)) := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm1 := hsub (-1)
  simp only [← sub_eq_add_neg] at hm1
  have htri := (abs_sub _ _).trans (add_le_add (hsub 1) hm1)
  linarith [abs_nonneg (x - y)]

private theorem hasDerivAt_upow_succ {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    HasDerivAt (upow 1 (m + 1)) ((1 / 2 : ℝ) * (upow 1 m (x + 1) - upow 1 m (x - 1))) x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hcont : Continuous (upow 1 (k + 1)) := (contDiff_upow one_pos k).continuous
  have hconv : upow 1 (k + 2) = fun z =>
      1 / (2 * (1 : ℝ)) * ((∫ t in (0 : ℝ)..z + 1, upow 1 (k + 1) t) -
        ∫ t in (0 : ℝ)..z - 1, upow 1 (k + 1) t) :=
    funext (unif_convolution_eq one_pos (integrable_upow 1 (k + 1)))
  rw [hconv]
  have hd1 : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z + 1, upow 1 (k + 1) t)
      (upow 1 (k + 1) (x + 1)) x := by
    have h := (hcont.integral_hasStrictDerivAt 0 (x + 1)).hasDerivAt.comp x
      ((hasDerivAt_id x).add_const 1)
    exact h.congr_deriv (mul_one _)
  have hd2 : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z - 1, upow 1 (k + 1) t)
      (upow 1 (k + 1) (x - 1)) x := by
    have h := (hcont.integral_hasStrictDerivAt 0 (x - 1)).hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const 1)
    exact h.congr_deriv (mul_one _)
  exact ((hd1.sub hd2).const_mul (1 / (2 * (1 : ℝ)))).congr_deriv (by ring)

private theorem lipschitz_iteratedDeriv_upow :
    ∀ k : ℕ, ContDiff ℝ k (upow 1 (k + 1)) ∧
      ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv k (upow 1 (k + 1)))
  | 0 => ⟨contDiff_upow one_pos 0, 1, by simpa using lipschitz_upow_one_one⟩
  | k + 1 => by
    obtain ⟨hck, K, hLK⟩ := lipschitz_iteratedDeriv_upow k
    refine ⟨contDiff_upow one_pos (k + 1), K, ?_⟩
    have hderiv : deriv (upow 1 (k + 2)) =
        fun x => (1 / 2 : ℝ) * (upow 1 (k + 1) (x + 1) - upow 1 (k + 1) (x - 1)) :=
      funext fun x => (hasDerivAt_upow_succ (Nat.succ_pos k) x).deriv
    have hiter : iteratedDeriv (k + 1) (upow 1 (k + 2)) =
        fun x => (1 / 2 : ℝ) *
          (iteratedDeriv k (upow 1 (k + 1)) (x + 1) -
            iteratedDeriv k (upow 1 (k + 1)) (x - 1)) := by
      rw [iteratedDeriv_succ', hderiv]
      funext x
      have h1 : ContDiff ℝ k fun z => upow 1 (k + 1) (z + 1) :=
        hck.comp (contDiff_id.add contDiff_const)
      have h2 : ContDiff ℝ k fun z => upow 1 (k + 1) (z - 1) :=
        hck.comp (contDiff_id.sub contDiff_const)
      rw [_root_.iteratedDeriv_const_mul_field,
        iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt,
        iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]
    rw [hiter, lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq]
    have hA := hLK.dist_le_mul (x + 1) (y + 1)
    have hB := hLK.dist_le_mul (x - 1) (y - 1)
    simp only [Real.dist_eq, add_sub_add_right_eq_sub, sub_sub_sub_cancel_right] at hA hB
    have heq : (1 / 2 : ℝ) * (iteratedDeriv k (upow 1 (k + 1)) (x + 1) -
          iteratedDeriv k (upow 1 (k + 1)) (x - 1)) -
        (1 / 2 : ℝ) * (iteratedDeriv k (upow 1 (k + 1)) (y + 1) -
          iteratedDeriv k (upow 1 (k + 1)) (y - 1)) =
        (1 / 2 : ℝ) * ((iteratedDeriv k (upow 1 (k + 1)) (x + 1) -
            iteratedDeriv k (upow 1 (k + 1)) (y + 1)) -
          (iteratedDeriv k (upow 1 (k + 1)) (x - 1) -
            iteratedDeriv k (upow 1 (k + 1)) (y - 1))) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri := (abs_sub _ _).trans (add_le_add hA hB)
    linarith

private def CkLip (k : ℕ) (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ k f ∧ (∀ x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), f x = 0) ∧
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv k f)

private theorem ckLip_deriv {k : ℕ} {f : ℝ → ℝ} (hf : CkLip (k + 1) f) : CkLip k (deriv f) := by
  obtain ⟨hc, hsupp, K, hL⟩ := hf
  have hc' : ContDiff ℝ k (deriv f) := by
    rw [Nat.cast_succ] at hc
    exact (contDiff_succ_iff_deriv.mp hc).2.2
  refine ⟨hc', fun x hx => ?_, K, ?_⟩
  · have hev : f =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hx) fun z hz => hsupp z hz
    simpa using hev.deriv_eq
  · rwa [← iteratedDeriv_succ']

private theorem lipschitz_of_collar {g : ℝ → ℝ} {B C : ℝ} (hC : 0 ≤ C)
    (hsupp : ∀ x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0)
    (hbound : ∀ x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), |g x| ≤ B)
    (_hB : 0 ≤ B)
    (hin : ∀ x ∈ Set.Icc (Real.exp (-9)) (5 * Real.exp 8),
      ∀ y ∈ Set.Icc (Real.exp (-9)) (5 * Real.exp 8), |g x - g y| ≤ C * |x - y|) :
    ∃ K : ℝ≥0, LipschitzWith K g := by
  let δ := min (Real.exp (-8) - Real.exp (-9)) (5 * Real.exp 8 - 4 * Real.exp 8)
  have hδ : 0 < δ := lt_min (sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num)))
    (by have := Real.exp_pos 8; linarith)
  let M := max C (B / δ)
  have hM : 0 ≤ M := le_trans hC (le_max_left _ _)
  let K : ℝ≥0 := ⟨M, hM⟩
  refine ⟨K, lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_⟩
  rw [Real.dist_eq, Real.dist_eq]
  change |g x - g y| ≤ M * |x - y|
  by_cases hxJ : x ∈ Set.Icc (Real.exp (-9)) (5 * Real.exp 8)
  · by_cases hyJ : y ∈ Set.Icc (Real.exp (-9)) (5 * Real.exp 8)
    · exact (hin x hxJ y hyJ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · by_cases hxS : x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8)
      · have hyS : y ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hyS =>
          hyJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hyS.1,
            hyS.2.trans (by have := Real.exp_pos 8; linarith)⟩
        have hgap : δ ≤ |x - y| := by
          rcases not_and_or.mp hyJ with h1 | h2
          · rw [not_le] at h1
            calc δ ≤ Real.exp (-8) - Real.exp (-9) := min_le_left _ _
              _ ≤ x - y := by linarith [hxS.1]
              _ ≤ |x - y| := le_abs_self _
          · rw [not_le] at h2
            calc δ ≤ 5 * Real.exp 8 - 4 * Real.exp 8 := min_le_right _ _
              _ ≤ y - x := by linarith [hxS.2]
              _ ≤ |x - y| := by rw [← abs_neg, neg_sub]; exact le_abs_self _
        rw [hsupp y hyS, sub_zero]
        calc |g x| ≤ B := hbound x hxS
          _ = (B / δ) * δ := by field_simp [hδ.ne']
          _ ≤ M * |x - y| := mul_le_mul (le_max_right _ _) hgap hδ.le hM
      · have hyS : y ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hyS =>
          hyJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hyS.1,
            hyS.2.trans (by have := Real.exp_pos 8; linarith)⟩
        rw [hsupp x hxS, hsupp y hyS, sub_self, abs_zero]
        exact mul_nonneg hM (abs_nonneg _)
  · by_cases hyS : y ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8)
    · have hxS : x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hxS =>
        hxJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hxS.1,
          hxS.2.trans (by have := Real.exp_pos 8; linarith)⟩
      have hgap : δ ≤ |x - y| := by
        rcases not_and_or.mp hxJ with h1 | h2
        · rw [not_le] at h1
          calc δ ≤ Real.exp (-8) - Real.exp (-9) := min_le_left _ _
            _ ≤ y - x := by linarith [hyS.1]
            _ ≤ |x - y| := by rw [← abs_neg, neg_sub]; exact le_abs_self _
        · rw [not_le] at h2
          calc δ ≤ 5 * Real.exp 8 - 4 * Real.exp 8 := min_le_right _ _
            _ ≤ x - y := by linarith [hyS.2]
            _ ≤ |x - y| := le_abs_self _
      rw [hsupp x hxS, zero_sub, abs_neg]
      calc |g y| ≤ B := hbound y hyS
        _ = (B / δ) * δ := by field_simp [hδ.ne']
        _ ≤ M * |x - y| := mul_le_mul (le_max_right _ _) hgap hδ.le hM
    · have hxS : x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hxS =>
        hxJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hxS.1,
          hxS.2.trans (by have := Real.exp_pos 8; linarith)⟩
      rw [hsupp x hxS, hsupp y hyS, sub_self, abs_zero]
      exact mul_nonneg hM (abs_nonneg _)

private theorem ckLip_add {k : ℕ} {f g : ℝ → ℝ} (hf : CkLip k f) (hg : CkLip k g) :
    CkLip k (fun x => f x + g x) := by
  obtain ⟨hcf, hsf, Kf, hLf⟩ := hf
  obtain ⟨hcg, hsg, Kg, hLg⟩ := hg
  refine ⟨hcf.add hcg, fun x hx => by dsimp only; rw [hsf x hx, hsg x hx, add_zero], Kf + Kg, ?_⟩
  have heq : iteratedDeriv k (fun x => f x + g x) =
      fun x => iteratedDeriv k f x + iteratedDeriv k g x :=
    funext fun x => iteratedDeriv_fun_add hcf.contDiffAt hcg.contDiffAt
  rw [heq]
  exact hLf.add hLg

private theorem ckLip_mul_smooth :
    ∀ {k : ℕ} {f φ : ℝ → ℝ}, CkLip k f → ContDiffOn ℝ ∞ φ (Set.Ioi 0) →
      CkLip k fun x => φ x * f x
  | 0, f, φ, ⟨hcf, hsf, Kf, hLf⟩, hφ => by
    have hcont : Continuous fun x => φ x * f x := by
      rw [continuous_iff_continuousAt]; intro x
      by_cases hx : 0 < x
      · exact (hφ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx)).mul hcf.continuous.continuousAt
      · have hev : (fun z => φ z * f z) =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with z hz
          rw [hsf z fun h => hz.not_ge h.1, mul_zero]; rfl
        exact continuousAt_const.congr hev.symm
    refine ⟨contDiff_zero.mpr hcont, fun x hx => by dsimp only; rw [hsf x hx, mul_zero], ?_⟩
    simp only [iteratedDeriv_zero] at hLf ⊢
    let J := Set.Icc (Real.exp (-9)) (5 * Real.exp 8)
    let S := Set.Icc (Real.exp (-8)) (4 * Real.exp 8)
    have hJsub : J ⊆ Set.Ioi 0 := fun z hz => (Real.exp_pos (-9)).trans_le hz.1
    have hdφ : ContinuousOn (deriv φ) J :=
      (hφ.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hJsub
    obtain ⟨Mφ, hMφ⟩ := (isCompact_Icc : IsCompact J).exists_bound_of_continuousOn
      (hφ.continuousOn.mono hJsub)
    obtain ⟨Lφ, hLφ⟩ := (isCompact_Icc : IsCompact J).exists_bound_of_continuousOn hdφ
    obtain ⟨Mf, hMf⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
      hcf.continuous.continuousOn
    have hJpt : Real.exp (-9) ∈ J := ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-9 : ℝ) < 8); linarith [Real.exp_pos 8]⟩
    have hSpt : Real.exp (-8) ∈ S := ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-8 : ℝ) < 8); linarith [Real.exp_pos 8]⟩
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ _ hJpt)
    have hLφ0 : 0 ≤ Lφ := (norm_nonneg _).trans (hLφ _ hJpt)
    have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf _ hSpt)
    have hφlip : ∀ x ∈ J, ∀ y ∈ J, |φ x - φ y| ≤ Lφ * |x - y| := fun x hx y hy => by
      have hd : ∀ z ∈ J, DifferentiableAt ℝ φ z := fun z hz =>
        (hφ.differentiableOn (by simp) z (hJsub hz)).differentiableAt (isOpen_Ioi.mem_nhds (hJsub hz))
      simpa only [Real.norm_eq_abs] using
        (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
          (fun z hz => hd z hz) (fun z hz => hLφ z hz) hy hx
    refine lipschitz_of_collar (B := Mφ * Mf) (C := Lφ * Mf + Mφ * Kf) (by positivity)
      (fun x hx => by rw [hsf x hx, mul_zero])
      (fun x hx => by
        have hxJ : x ∈ J := ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hx.1,
          hx.2.trans (by linarith [Real.exp_pos 8])⟩
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using hMφ x hxJ)
          (by simpa [Real.norm_eq_abs] using hMf x hx) (abs_nonneg _) hMφ0)
      (by positivity) fun x hx y hy => ?_
    have heq : φ x * f x - φ y * f y = (φ x - φ y) * f x + φ y * (f x - f y) := by ring
    rw [heq]
    have h1 : |(φ x - φ y) * f x| ≤ Lφ * Mf * |x - y| := by
      rw [abs_mul]
      by_cases hxS : x ∈ S
      · exact (mul_le_mul (hφlip x hx y hy) (by simpa [Real.norm_eq_abs] using hMf x hxS)
          (abs_nonneg _) (by positivity)).trans_eq (by ring)
      · rw [hsf x hxS, abs_zero, mul_zero]; positivity
    have h2 : |φ y * (f x - f y)| ≤ Mφ * Kf * |x - y| := by
      rw [abs_mul]
      exact (mul_le_mul (by simpa [Real.norm_eq_abs] using hMφ y hy)
        (by simpa [Real.dist_eq] using hLf.dist_le_mul x y) (abs_nonneg _) hMφ0).trans_eq (by ring)
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  | k + 1, f, φ, hf, hφ => by
    have hdφ : ContDiffOn ℝ ∞ (deriv φ) (Set.Ioi 0) :=
      hφ.deriv_of_isOpen isOpen_Ioi (by simp)
    have hf_k : CkLip k f := by
      obtain ⟨hcf_k, hdk⟩ := contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp hf.1
      have hsupp_k : HasCompactSupport (iteratedDeriv k f) := by
        refine HasCompactSupport.intro (K := Set.Icc (Real.exp (-8)) (4 * Real.exp 8))
          isCompact_Icc fun x hx => ?_
        have hev : f =ᶠ[𝓝 x] 0 :=
          Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hx) fun z hz => hf.2.1 z hz
        simpa using hev.iteratedDeriv_eq k
      exact ⟨hcf_k, hf.2.1,
        ContDiff.lipschitzWith_of_hasCompactSupport hsupp_k hdk (by simp)⟩
    have hsum := ckLip_add (ckLip_mul_smooth hf_k hdφ) (ckLip_mul_smooth (ckLip_deriv hf) hφ)
    have hdiff : ∀ x, HasDerivAt (fun z => φ z * f z) (deriv φ x * f x + φ x * deriv f x) x := by
      intro x
      by_cases hx : 0 < x
      · have hφd : DifferentiableAt ℝ φ x :=
          (hφ.differentiableOn (by simp) x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)
        have hfd : DifferentiableAt ℝ f x :=
          (hf.1.differentiable (by simp)).differentiableAt
        exact hφd.hasDerivAt.mul hfd.hasDerivAt
      · have hxS : x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) :=
          fun h => hx ((Real.exp_pos (-8)).trans_le h.1)
        have hev : (fun z => φ z * f z) =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with z hz
          rw [hf.2.1 z fun h => hz.not_ge h.1, mul_zero]; rfl
        rw [hf.2.1 x hxS, (ckLip_deriv hf).2.1 x hxS, mul_zero, mul_zero, add_zero]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    have hder_eq : deriv (fun z => φ z * f z) = fun x => deriv φ x * f x + φ x * deriv f x :=
      funext fun x => (hdiff x).deriv
    have hc_succ : ContDiff ℝ (k + 1 : ℕ) (fun z => φ z * f z) := by
      rw [Nat.cast_succ]
      exact contDiff_succ_iff_deriv.mpr ⟨fun x => (hdiff x).differentiableAt,
        by simp, hder_eq ▸ hsum.1⟩
    refine ⟨hc_succ, fun x hx => by dsimp only; rw [hf.2.1 x hx, mul_zero], ?_⟩
    rw [iteratedDeriv_succ', hder_eq]
    exact hsum.2.2

private theorem ckLip_comp_log :
    ∀ {k : ℕ} {H : ℝ → ℝ}, ContDiff ℝ k H →
      (∀ u ∉ Set.Icc (-8 : ℝ) (8 + Real.log 4), H u = 0) →
      (∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv k H)) →
      CkLip k fun x => if 0 < x then H (Real.log x) else 0
  | 0, H, hcH, hsuppH, ⟨KH, hLH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    let S := Set.Icc (Real.exp (-8)) (4 * Real.exp 8)
    have hsg : ∀ x ∉ S, g x = 0 := by
      intro x hx; dsimp only [g]
      by_cases hp : 0 < x
      · rw [if_pos hp]
        refine hsuppH (Real.log x) fun hu => hx ⟨?_, ?_⟩
        · rw [← Real.exp_log hp]; exact Real.exp_le_exp.mpr hu.1
        · rw [← Real.exp_log hp]
          exact (Real.exp_le_exp.mpr hu.2).trans_eq
            (by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), mul_comm])
      · exact if_neg hp
    have hcont : Continuous g := by
      rw [continuous_iff_continuousAt]; intro x
      by_cases hp : 0 < x
      · have hev : g =ᶠ[𝓝 x] fun z => H (Real.log z) := by
          filter_upwards [lt_mem_nhds hp] with z hz; exact if_pos hz
        exact (hcH.continuous.continuousAt.comp (Real.continuousAt_log hp.ne')).congr hev.symm
      · have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with z hz
          exact hsg z fun h => hz.not_ge h.1
        exact continuousAt_const.congr hev.symm
    refine ⟨contDiff_zero.mpr hcont, hsg, ?_⟩
    simp only [iteratedDeriv_zero] at hLH ⊢
    obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn hcont.continuousOn
    have hSpt : Real.exp (-8) ∈ S := ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-8 : ℝ) < 8); linarith [Real.exp_pos 8]⟩
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hSpt)
    refine lipschitz_of_collar (B := B) (C := KH * Real.exp 9) (by positivity) hsg
      (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx) hB0 fun x hx y hy => ?_
    have hx0 : 0 < x := (Real.exp_pos (-9)).trans_le hx.1
    have hy0 : 0 < y := (Real.exp_pos (-9)).trans_le hy.1
    have hlog : |Real.log x - Real.log y| ≤ Real.exp 9 * |x - y| := by
      have hd : ∀ z ∈ Set.Icc (Real.exp (-9)) (5 * Real.exp 8),
          HasDerivAt Real.log z⁻¹ z ∧ ‖z⁻¹‖ ≤ Real.exp 9 := fun z hz => by
        have hz0 : 0 < z := (Real.exp_pos (-9)).trans_le hz.1
        refine ⟨Real.hasDerivAt_log hz0.ne', ?_⟩
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz0)]
        exact (inv_anti₀ (Real.exp_pos (-9)) hz.1).trans_eq (by rw [Real.exp_neg, inv_inv])
      simpa only [Real.norm_eq_abs] using
        (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
          (fun z hz => (hd z hz).1.differentiableAt)
          (fun z hz => by rw [(hd z hz).1.deriv]; exact (hd z hz).2) hy hx
    change |(if 0 < x then H (Real.log x) else 0) - (if 0 < y then H (Real.log y) else 0)| ≤ _
    rw [if_pos hx0, if_pos hy0]
    have hHL : |H (Real.log x) - H (Real.log y)| ≤ KH * |Real.log x - Real.log y| := by
      simpa [Real.dist_eq] using hLH.dist_le_mul (Real.log x) (Real.log y)
    exact hHL.trans ((mul_le_mul_of_nonneg_left hlog KH.coe_nonneg).trans_eq (by ring))
  | k + 1, H, hcH, hsuppH, ⟨KH, hLH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    have hsuppH' : ∀ u ∉ Set.Icc (-8 : ℝ) (8 + Real.log 4), deriv H u = 0 := by
      intro u hu
      have hev : H =ᶠ[𝓝 u] 0 :=
        Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hu) fun z hz => hsuppH z hz
      simpa using hev.deriv_eq
    have hcH' : ContDiff ℝ k (deriv H) := by
      rw [Nat.cast_succ] at hcH
      exact (contDiff_succ_iff_deriv.mp hcH).2.2
    have ih := ckLip_comp_log hcH' hsuppH' ⟨KH, by rwa [← iteratedDeriv_succ']⟩
    have hinv : ContDiffOn ℝ ∞ Inv.inv (Set.Ioi (0 : ℝ)) :=
      (contDiffOn_inv ℝ).mono fun x (hx : 0 < x) => hx.ne'
    have hmul := ckLip_mul_smooth ih hinv
    have hsg : ∀ x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0 := by
      intro x hx; dsimp only [g]
      by_cases hp : 0 < x
      · rw [if_pos hp]
        refine hsuppH (Real.log x) fun hu => hx ⟨?_, ?_⟩
        · rw [← Real.exp_log hp]; exact Real.exp_le_exp.mpr hu.1
        · rw [← Real.exp_log hp]
          exact (Real.exp_le_exp.mpr hu.2).trans_eq
            (by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), mul_comm])
      · exact if_neg hp
    have hdiff : ∀ x, HasDerivAt g (x⁻¹ * (if 0 < x then deriv H (Real.log x) else 0)) x := by
      intro x
      by_cases hp : 0 < x
      · have hev : g =ᶠ[𝓝 x] fun z => H (Real.log z) := by
          filter_upwards [lt_mem_nhds hp] with z hz; exact if_pos hz
        have hdH : HasDerivAt H (deriv H (Real.log x)) (Real.log x) :=
          (hcH.differentiable (by simp)).differentiableAt.hasDerivAt
        rw [if_pos hp, mul_comm]
        exact (hdH.comp x (Real.hasDerivAt_log hp.ne')).congr_of_eventuallyEq hev
      · have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with z hz
          exact hsg z fun h => hz.not_ge h.1
        rw [if_neg hp, mul_zero]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    have hder_eq : deriv g = fun x => x⁻¹ * (if 0 < x then deriv H (Real.log x) else 0) :=
      funext fun x => (hdiff x).deriv
    have hc_succ : ContDiff ℝ (k + 1 : ℕ) g := by
      rw [Nat.cast_succ]
      exact contDiff_succ_iff_deriv.mpr ⟨fun x => (hdiff x).differentiableAt,
        by simp, hder_eq ▸ hmul.1⟩
    refine ⟨hc_succ, hsg, ?_⟩
    rw [iteratedDeriv_succ', hder_eq]
    exact hmul.2.2

private theorem squareLogProfile_eq_zero_outside {u : ℝ}
    (hu : u ∉ Set.Icc (-8 : ℝ) (8 + Real.log 4)) : squareLogProfile u = 0 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold squareLogProfile
  have hz1 : splineAutoCorr u = 0 := by
    refine splineAutoCorr_zero_outside ?_
    by_contra! hle
    have ha := abs_le.mp hle
    exact hu ⟨ha.1, by linarith [ha.2]⟩
  have hz2 : splineAutoCorr (u - Real.log 4) = 0 := by
    refine splineAutoCorr_zero_outside ?_
    by_contra! hle
    have hb := abs_le.mp hle
    exact hu ⟨by linarith [hb.1], by linarith [hb.2]⟩
  rw [hz1, hz2]; ring

private theorem ckLip_six_dyadicSpline : CkLip 6 dyadicSpline := by
  obtain ⟨hcA, KA, hLA⟩ := lipschitz_iteratedDeriv_upow 6
  have hAeq : splineAutoCorr = upow 1 7 := funext splineAutoCorr_eq_eight_boxes
  have hcF : ContDiff ℝ (6 : ℕ) squareLogProfile := by
    unfold squareLogProfile; rw [hAeq]
    exact (contDiff_const.mul hcA).sub (hcA.comp (contDiff_id.sub contDiff_const))
  have hLF : ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 6 squareLogProfile) := by
    have heq : iteratedDeriv 6 squareLogProfile =
        fun u => 2 * iteratedDeriv 6 (upow 1 7) u -
          iteratedDeriv 6 (upow 1 7) (u - Real.log 4) := by
      funext u; unfold squareLogProfile; rw [hAeq]
      have h1 : ContDiff ℝ (6 : ℕ) fun z => 2 * upow 1 7 z := contDiff_const.mul hcA
      have h2 : ContDiff ℝ (6 : ℕ) fun z => upow 1 7 (z - Real.log 4) :=
        hcA.comp (contDiff_id.sub contDiff_const)
      rw [iteratedDeriv_fun_sub h1.contDiffAt h2.contDiffAt,
        _root_.iteratedDeriv_const_mul_field, iteratedDeriv_comp_sub_const]
    rw [heq]
    have hL1 : LipschitzWith (2 * KA) (fun u => (2 : ℝ) * iteratedDeriv 6 (upow 1 7) u) := by
      rw [lipschitzWith_iff_dist_le_mul]; intro x y
      have h := hLA.dist_le_mul x y
      simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat] at h ⊢
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hL2 : LipschitzWith KA (fun u => iteratedDeriv 6 (upow 1 7) (u - Real.log 4)) := by
      rw [lipschitzWith_iff_dist_le_mul]; intro x y
      simpa [Real.dist_eq, sub_sub_sub_cancel_right] using
        hLA.dist_le_mul (x - Real.log 4) (y - Real.log 4)
    exact ⟨2 * KA + KA, hL1.sub hL2⟩
  have hlog := ckLip_comp_log hcF (fun _ => squareLogProfile_eq_zero_outside) hLF
  have hφ : ContDiffOn ℝ ∞ (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) (Set.Ioi 0) :=
    contDiffOn_const.mul fun x (hx : 0 < x) =>
      (Real.contDiffAt_rpow_const_of_ne hx.ne').contDiffWithinAt
  have hmul := ckLip_mul_smooth hlog hφ
  have heq : (fun x : ℝ => (2 * x ^ (-(1 / 2 : ℝ))) *
      (if 0 < x then squareLogProfile (Real.log x) else 0)) = dyadicSpline := by
    funext x
    by_cases hx : 0 < x
    · simp only [if_pos hx, dyadicSpline, squarePrimeWeight, Complex.ofReal_re]
      rw [Real.rpow_def_of_pos hx]; ring_nf
    · simp only [if_neg hx, dyadicSpline, mul_zero]
  rwa [heq] at hmul

theorem contDiff_six_dyadicSpline : ContDiff ℝ 6 dyadicSpline := ckLip_six_dyadicSpline.1

theorem lipschitz_iteratedDeriv_six_dyadicSpline :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 6 dyadicSpline) := ckLip_six_dyadicSpline.2.2

/-! ### Properties of `conductorSplineIntegral` and `conductorCurvatureProfile` -/

private theorem contDiff_div_sq_dyadicSpline : ContDiff ℝ 6 (fun t : ℝ => dyadicSpline t / t ^ 2) := by
  have hmul := ckLip_mul_smooth ckLip_six_dyadicSpline
    (((contDiff_id.pow 2).contDiffOn).inv fun x (hx : 0 < x) => (sq_pos_of_pos hx).ne')
  simpa [div_eq_inv_mul] using hmul.1

theorem contDiff_seven_conductorSplineIntegral : ContDiff ℝ 7 conductorSplineIntegral := by
  have hprim : ContDiff ℝ 7 (fun u : ℝ => ∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2) :=
    contDiff_primitive contDiff_div_sq_dyadicSpline
  unfold conductorSplineIntegral
  exact (contDiff_id.div_const 2).mul hprim

theorem conductorSplineIntegral_eq_zero_before {u : ℝ} (hu : u ≤ Real.exp (-8)) :
    conductorSplineIntegral u = 0 := by
  unfold conductorSplineIntegral
  suffices h : (∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2) = 0 by rw [h, mul_zero]
  have hcongr : (∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2) = ∫ _t in (0 : ℝ)..u, (0 : ℝ) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    have hlt : t < Real.exp (-8) ∨ t = Real.exp (-8) := by
      rcases le_total 0 u with h0 | h0
      · rw [Set.uIoc_of_le h0] at ht; exact lt_or_eq_of_le (ht.2.trans hu)
      · rw [Set.uIoc_of_ge h0] at ht; exact Or.inl (ht.2.trans_lt (Real.exp_pos (-8)))
    rcases hlt with hlt | rfl
    · rw [dyadicSpline_eq_zero_outside fun h => hlt.not_ge h.1, zero_div]
    · have hcont : Continuous dyadicSpline := contDiff_six_dyadicSpline.continuous
      have hlim : Tendsto dyadicSpline (𝓝[<] Real.exp (-8)) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (dyadicSpline_eq_zero_outside fun h => hz.not_ge h.1).symm
      have hz : dyadicSpline (Real.exp (-8)) = 0 :=
        tendsto_nhds_unique (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hlim
      rw [hz, zero_div]
  rw [hcongr, intervalIntegral.integral_zero]

theorem conductorSplineIntegral_linear_after {u : ℝ} (hu : 4 * Real.exp 8 ≤ u) :
    conductorSplineIntegral u =
      (u / 2) * ∫ t in (0 : ℝ)..(4 * Real.exp 8), dyadicSpline t / t ^ 2 := by
  unfold conductorSplineIntegral
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (contDiff_div_sq_dyadicSpline.continuous.intervalIntegrable 0 (4 * Real.exp 8))
    (contDiff_div_sq_dyadicSpline.continuous.intervalIntegrable (4 * Real.exp 8) u)]
  suffices hz : (∫ t in (4 * Real.exp 8)..u, dyadicSpline t / t ^ 2) = 0 by rw [hz, add_zero]
  rw [intervalIntegral.integral_of_le hu]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [dyadicSpline_eq_zero_outside fun h => ht.1.not_ge h.2, zero_div]

private theorem iteratedDeriv_add_eq (a b : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv (a + b) f = iteratedDeriv a (iteratedDeriv b f) := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

private theorem iteratedDeriv_two_conductorSplineIntegral :
    iteratedDeriv 2 conductorSplineIntegral = fun u => (2 * u)⁻¹ * deriv dyadicSpline u := by
  let F := fun u : ℝ => ∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2
  have hdF : ∀ u, HasDerivAt F (dyadicSpline u / u ^ 2) u := fun u =>
    (contDiff_div_sq_dyadicSpline.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd1 : ∀ u, HasDerivAt conductorSplineIntegral
      ((1 / 2 : ℝ) * F u + dyadicSpline u / (2 * u)) u := by
    intro u
    refine (((hasDerivAt_id u).div_const 2).mul (hdF u)).congr_deriv ?_
    dsimp only [id]
    by_cases hu : u = 0
    · subst u; simp [dyadicSpline]
    · field_simp [hu]
  have hd1_eq : deriv conductorSplineIntegral =
      fun u => (1 / 2 : ℝ) * F u + dyadicSpline u / (2 * u) :=
    funext fun u => (hd1 u).deriv
  funext u
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd1_eq]
  by_cases hu : 0 < u
  · have hd2a : HasDerivAt (fun z => (1 / 2 : ℝ) * F z) ((1 / 2 : ℝ) * (dyadicSpline u / u ^ 2)) u :=
      (hdF u).const_mul (1 / 2)
    have hdd : DifferentiableAt ℝ dyadicSpline u :=
      (contDiff_six_dyadicSpline.differentiable (by simp)).differentiableAt
    have hd2b : HasDerivAt (fun z => dyadicSpline z / (2 * z))
        ((deriv dyadicSpline u * (2 * u) - dyadicSpline u * 2) / (2 * u) ^ 2) u := by
      have hid2 : HasDerivAt (fun z : ℝ => 2 * z) 2 u :=
        ((hasDerivAt_id u).const_mul 2).congr_deriv (mul_one 2)
      exact hdd.hasDerivAt.fun_div hid2 (by positivity)
    have hd2 : HasDerivAt (fun z => (1 / 2 : ℝ) * F z + dyadicSpline z / (2 * z))
        ((2 * u)⁻¹ * deriv dyadicSpline u) u := by
      refine (hd2a.add hd2b).congr_deriv ?_
      field_simp [hu.ne']; ring
    exact hd2.deriv
  · have huS : u ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) :=
      fun h => hu ((Real.exp_pos (-8)).trans_le h.1)
    have hev : (fun z => (1 / 2 : ℝ) * F z + dyadicSpline z / (2 * z)) =ᶠ[𝓝 u] 0 := by
      filter_upwards [gt_mem_nhds ((le_of_not_gt hu).trans_lt (Real.exp_pos (-8)))] with z hz
      have hzF : F z = 0 := by
        have hc := conductorSplineIntegral_eq_zero_before hz.le
        unfold conductorSplineIntegral at hc
        rcases mul_eq_zero.mp hc with h0 | hF0
        · have hz0 : z = 0 := by linarith
          subst z; simp [F]
        · exact hF0
      rw [hzF, dyadicSpline_eq_zero_outside fun h => hz.not_ge h.1]; simp
    rw [((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev).deriv,
      (ckLip_deriv ckLip_six_dyadicSpline).2.1 u huS, mul_zero]

theorem lipschitz_iteratedDeriv_seven_conductorSplineIntegral :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 7 conductorSplineIntegral) := by
  have h2 : CkLip 5 (fun u => (2 * u)⁻¹ * deriv dyadicSpline u) :=
    ckLip_mul_smooth (ckLip_deriv ckLip_six_dyadicSpline)
      ((contDiffOn_const.mul contDiffOn_id).inv fun x (hx : 0 < x) => by positivity)
  rw [show (7 : ℕ) = 5 + 2 from rfl, iteratedDeriv_add_eq 5 2,
    iteratedDeriv_two_conductorSplineIntegral]
  exact h2.2.2

/-- Exact antiderivative identity for the conductor integral of `t · dyadicSpline(z / t²)`. -/
theorem integral_mul_dyadicSpline_inv_sq {a d z : ℝ} (ha : 0 < a) (had : a ≤ d) (hz : 0 ≤ z) :
    (∫ t in a..d, t * dyadicSpline (z / t ^ 2)) =
      a ^ 2 * conductorSplineIntegral (z / a ^ 2) -
        d ^ 2 * conductorSplineIntegral (z / d ^ 2) := by
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · simp [dyadicSpline, conductorSplineIntegral]
  · let F := fun u : ℝ => ∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2
    let H := fun t : ℝ => -(z / 2) * F (z / t ^ 2)
    have hdF : ∀ u, HasDerivAt F (dyadicSpline u / u ^ 2) u := fun u =>
      (contDiff_div_sq_dyadicSpline.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt
    have hdH : ∀ t ∈ Set.uIcc a d, HasDerivAt H (t * dyadicSpline (z / t ^ 2)) t := by
      intro t ht
      rw [Set.uIcc_of_le had] at ht
      have ht0 : 0 < t := ha.trans_le ht.1
      have hquot : HasDerivAt (fun s : ℝ => z / s ^ 2) (-(2 * z) / t ^ 3) t := by
        refine ((hasDerivAt_const t z).div ((hasDerivAt_id t).pow 2)
          (sq_pos_of_pos ht0).ne').congr_deriv ?_
        dsimp only [id, Pi.pow_apply]; field_simp [ht0.ne']; norm_num; ring
      refine (((hdF (z / t ^ 2)).comp t hquot).const_mul (-(z / 2))).congr_deriv ?_
      field_simp [ht0.ne', hzpos.ne']
    have hint : IntervalIntegrable (fun t : ℝ => t * dyadicSpline (z / t ^ 2)) volume a d := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le had]
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      exact (continuousAt_id.mul (contDiff_six_dyadicSpline.continuous.continuousAt.comp
        (continuousAt_const.div (continuousAt_id.pow 2) (sq_pos_of_pos ht0).ne'))).continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdH hint]
    have hHeq (t : ℝ) (ht : 0 < t) : H t = -t ^ 2 * conductorSplineIntegral (z / t ^ 2) := by
      dsimp only [H, conductorSplineIntegral, F]; field_simp [ht.ne']
    rw [hHeq d (ha.trans_le had), hHeq a ha]; ring

private theorem ckLip_four_conductorCurvatureProfile : CkLip 4 conductorCurvatureProfile := by
  have hd1 : CkLip 4 (deriv dyadicSpline) := by
    have h5 := ckLip_deriv ckLip_six_dyadicSpline
    obtain ⟨hc4, hdk⟩ := contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp h5.1
    have hsupp4 : HasCompactSupport (iteratedDeriv 4 (deriv dyadicSpline)) := by
      refine HasCompactSupport.intro (K := Set.Icc (Real.exp (-8)) (4 * Real.exp 8))
        isCompact_Icc fun x hx => ?_
      have hev : deriv dyadicSpline =ᶠ[𝓝 x] 0 :=
        Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hx) fun z hz => h5.2.1 z hz
      simpa using hev.iteratedDeriv_eq 4
    exact ⟨hc4, h5.2.1,
      ContDiff.lipschitzWith_of_hasCompactSupport hsupp4 hdk (by simp)⟩
  have hd2 : CkLip 4 (iteratedDeriv 2 dyadicSpline) := by
    have h := ckLip_deriv (ckLip_deriv ckLip_six_dyadicSpline)
    rwa [show deriv (deriv dyadicSpline) = iteratedDeriv 2 dyadicSpline by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at h
  exact ckLip_add (ckLip_mul_smooth hd1 (contDiffOn_const.mul contDiffOn_id))
    (ckLip_mul_smooth hd2 (contDiffOn_const.mul (contDiff_id.pow 2).contDiffOn))

theorem contDiff_four_conductorCurvatureProfile : ContDiff ℝ 4 conductorCurvatureProfile :=
  ckLip_four_conductorCurvatureProfile.1

theorem conductorCurvatureProfile_eq_zero_outside {x : ℝ}
    (hx : x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8)) : conductorCurvatureProfile x = 0 :=
  ckLip_four_conductorCurvatureProfile.2.1 x hx

theorem lipschitz_iteratedDeriv_four_conductorCurvatureProfile :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 4 conductorCurvatureProfile) :=
  ckLip_four_conductorCurvatureProfile.2.2

/-- Second conductor derivative `∂_t² [t · dyadicSpline(z / t²)] = Θ₂(z / t²) / t` for `t > 0`. -/
theorem hasDerivAt_conductor_profile (z : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffOn ℝ 2 (fun s : ℝ => s * dyadicSpline (z / s ^ 2)) (Set.Ioi 0) ∧
      iteratedDeriv 2 (fun s : ℝ => s * dyadicSpline (z / s ^ 2)) t =
        conductorCurvatureProfile (z / t ^ 2) / t := by
  let g := fun s : ℝ => s * dyadicSpline (z / s ^ 2)
  have hcd : ContDiffOn ℝ 2 g (Set.Ioi 0) :=
    contDiffOn_id.mul ((contDiff_six_dyadicSpline.of_le (by norm_num)).comp_contDiffOn
      (contDiffOn_const.div (contDiff_id.pow 2).contDiffOn
        fun s (hs : 0 < s) => (sq_pos_of_pos hs).ne'))
  refine ⟨hcd, ?_⟩
  have hd1 : ∀ s > (0 : ℝ), HasDerivAt g
      (dyadicSpline (z / s ^ 2) - 2 * z / s ^ 2 * deriv dyadicSpline (z / s ^ 2)) s := by
    intro s hs
    have hq : HasDerivAt (fun r : ℝ => z / r ^ 2) (-(2 * z) / s ^ 3) s := by
      refine ((hasDerivAt_const s z).div ((hasDerivAt_id s).pow 2)
        (sq_pos_of_pos hs).ne').congr_deriv ?_
      dsimp only [id, Pi.pow_apply]; field_simp [hs.ne']; norm_num; ring
    have hdΦ : HasDerivAt dyadicSpline (deriv dyadicSpline (z / s ^ 2)) (z / s ^ 2) :=
      (contDiff_six_dyadicSpline.differentiable (by simp)).differentiableAt.hasDerivAt
    refine ((hasDerivAt_id s).mul (hdΦ.comp s hq)).congr_deriv ?_
    dsimp only [id, Pi.pow_apply, Function.comp_apply]
    field_simp [hs.ne']; ring
  have hev1 : deriv g =ᶠ[𝓝 t]
      fun s => dyadicSpline (z / s ^ 2) - 2 * z / s ^ 2 * deriv dyadicSpline (z / s ^ 2) := by
    filter_upwards [lt_mem_nhds ht] with s hs; exact (hd1 s hs).deriv
  have hq : HasDerivAt (fun r : ℝ => z / r ^ 2) (-(2 * z) / t ^ 3) t := by
    refine ((hasDerivAt_const t z).div ((hasDerivAt_id t).pow 2)
      (sq_pos_of_pos ht).ne').congr_deriv ?_
    dsimp only [id, Pi.pow_apply]; field_simp [ht.ne']; norm_num; ring
  have hdΦ : HasDerivAt dyadicSpline (deriv dyadicSpline (z / t ^ 2)) (z / t ^ 2) :=
    (contDiff_six_dyadicSpline.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdΦ' : HasDerivAt (deriv dyadicSpline) (iteratedDeriv 2 dyadicSpline (z / t ^ 2)) (z / t ^ 2) := by
    have h5 : ContDiff ℝ 5 (deriv dyadicSpline) := (ckLip_deriv ckLip_six_dyadicSpline).1
    have hd := ((h5.differentiable (by simp)).differentiableAt (x := z / t ^ 2)).hasDerivAt
    rwa [show deriv (deriv dyadicSpline) = iteratedDeriv 2 dyadicSpline by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at hd
  have hfactor : HasDerivAt (fun r : ℝ => 2 * z / r ^ 2) (-(4 * z) / t ^ 3) t := by
    refine ((hasDerivAt_const t (2 * z)).div ((hasDerivAt_id t).pow 2)
      (sq_pos_of_pos ht).ne').congr_deriv ?_
    dsimp only [id, Pi.pow_apply]; field_simp [ht.ne']; ring
  have hd2 := ((hdΦ.comp t hq).sub (hfactor.mul (hdΦ'.comp t hq))).congr_of_eventuallyEq hev1
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd2.deriv]
  dsimp only [conductorCurvatureProfile, Function.comp_apply]
  field_simp [ht.ne']; ring

/-! ### Off-knot `C^∞` regularity and discrete difference-sum bounds -/

private theorem contDiffAt_succ_of_eventually_hasDerivAt {f g : ℝ → ℝ} {u : ℝ} {n : ℕ}
    (hfg : ∀ᶠ x in 𝓝 u, HasDerivAt f (g x) x) (hg : ContDiffAt ℝ n g u) :
    ContDiffAt ℝ (n + 1 : ℕ) f u := by
  rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨fun x => L (g x), ⟨{x | HasDerivAt f (g x) x}, hfg, fun x hx => ?_⟩, ?_⟩
  · rw [hasFDerivAt_iff_hasDerivAt]; simpa [L] using hx
  · exact ((L.contDiff : ContDiff ℝ n L).contDiffAt).comp u hg

private theorem contDiffAt_deriv_of_succ {m : ℕ} {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ (m + 1 : ℕ) g x) :
    DifferentiableAt ℝ g x ∧ ContDiffAt ℝ m (deriv g) x :=
  ⟨hg.differentiableAt (by simp), hg.derivWithin (by norm_cast)⟩

private theorem nat_le_infty (n : ℕ) : (n : ℕ∞ω) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem upowKnots_shift {m : ℕ} {x : ℝ} (hx : x ∉ upowKnots (m + 1)) :
    x + 1 ∉ upowKnots m ∧ x - 1 ∉ upowKnots m := by
  constructor
  · intro h
    rw [upowKnots] at h
    obtain ⟨i, hi, heq⟩ := mem_image.mp h
    apply hx
    rw [upowKnots]
    refine mem_image.mpr ⟨i, mem_Icc.mpr ⟨(mem_Icc.mp hi).1, by have := (mem_Icc.mp hi).2; omega⟩, ?_⟩
    push_cast at heq ⊢; linarith
  · intro h
    rw [upowKnots] at h
    obtain ⟨i, hi, heq⟩ := mem_image.mp h
    apply hx
    rw [upowKnots]
    refine mem_image.mpr ⟨i + 1, mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hi).2; omega⟩, ?_⟩
    push_cast at heq ⊢; linarith

private theorem abs_upow_one_le : ∀ m : ℕ, ∀ x : ℝ, |upow 1 m x| ≤ 1 / 2
  | 0 => abs_unif_one_le
  | m + 1 => fun x => by
    change |(unif 1 ⋆ upow 1 m) x| ≤ 1 / 2
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hb : ∀ t, |unif 1 t * upow 1 m (x - t)| ≤ unif 1 t * (1 / 2) := fun t => by
      rw [abs_mul, abs_of_nonneg (unif_nonneg one_pos t)]
      exact mul_le_mul_of_nonneg_left (abs_upow_one_le m (x - t)) (unif_nonneg one_pos t)
    have hint : Integrable fun t => unif 1 t * upow 1 m (x - t) :=
      Integrable.mono' ((integrable_unif 1).mul_const (1 / 2))
        ((integrable_unif 1).aestronglyMeasurable.mul
          ((integrable_upow 1 m).comp_sub_left x).aestronglyMeasurable)
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hb t)
    calc |∫ t, unif 1 t * upow 1 m (x - t)|
        ≤ ∫ t, |unif 1 t * upow 1 m (x - t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t, unif 1 t * (1 / 2) :=
          integral_mono hint.abs ((integrable_unif 1).mul_const (1 / 2)) hb
      _ = (∫ t, unif 1 t) * (1 / 2) := integral_mul_const _ _
      _ = 1 / 2 := by rw [integral_unif one_pos, one_mul]

private theorem smooth_bounded_upow :
    ∀ m : ℕ, ∀ x ∉ upowKnots m,
      ContDiffAt ℝ ∞ (upow 1 m) x ∧ ∀ r : ℕ, |iteratedDeriv r (upow 1 m) x| ≤ 1 / 2
  | 0 => fun x hx => by
    have hx1 : x ≠ -1 ∧ x ≠ 1 :=
      ⟨fun h => hx (by rw [upowKnots]; exact mem_image.mpr ⟨(0 : ℕ), mem_Icc.mpr ⟨le_rfl, by decide⟩, by norm_num [h]⟩),
       fun h => hx (by rw [upowKnots]; exact mem_image.mpr ⟨(1 : ℕ), mem_Icc.mpr ⟨by decide, le_rfl⟩, by norm_num [h]⟩)⟩
    by_cases hin : x ∈ Set.Ioo (-1 : ℝ) 1
    · have hev : upow 1 0 =ᶠ[𝓝 x] fun _ => (1 / 2 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hin] with z hz
        have hz_mem : z ∈ Set.Icc (-1 : ℝ) 1 := ⟨hz.1.le, hz.2.le⟩
        simp [upow, unif, Set.indicator_of_mem hz_mem]
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, fun r => ?_⟩
      rw [hev.iteratedDeriv_eq r]
      rcases r with _ | r
      · norm_num
      · rw [iteratedDeriv_const]; norm_num
    · have hout : x ∈ (Set.Icc (-1 : ℝ) 1)ᶜ := fun hm =>
        hin ⟨lt_of_le_of_ne hm.1 hx1.1.symm, lt_of_le_of_ne hm.2 hx1.2⟩
      have hev : upow 1 0 =ᶠ[𝓝 x] 0 := by
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with z hz
        simp [upow, unif, Set.indicator_of_notMem hz]
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, fun r => ?_⟩
      rw [hev.iteratedDeriv_eq r]
      rcases r with _ | r <;> simp
  | m + 1 => fun x hx => by
    obtain ⟨hx1, hx2⟩ := upowKnots_shift hx
    obtain ⟨hc1, hb1⟩ := smooth_bounded_upow m (x + 1) hx1
    obtain ⟨hc2, hb2⟩ := smooth_bounded_upow m (x - 1) hx2
    have hd_nhds : ∀ᶠ z in 𝓝 x,
        HasDerivAt (upow 1 (m + 1)) ((1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1))) z := by
      rcases m with _ | m'
      · have hloc (y : ℝ) (hy : y ∉ upowKnots 0) : ∀ᶠ w in 𝓝 y, upow 1 0 w = upow 1 0 y := by
          have hy1 : y ≠ -1 ∧ y ≠ 1 :=
            ⟨fun h => hy (by rw [upowKnots]; exact mem_image.mpr ⟨(0 : ℕ), mem_Icc.mpr ⟨le_rfl, by decide⟩, by norm_num [h]⟩),
             fun h => hy (by rw [upowKnots]; exact mem_image.mpr ⟨(1 : ℕ), mem_Icc.mpr ⟨by decide, le_rfl⟩, by norm_num [h]⟩)⟩
          by_cases hin : y ∈ Set.Ioo (-1 : ℝ) 1
          · filter_upwards [isOpen_Ioo.mem_nhds hin] with w hw
            have hw_mem : w ∈ Set.Icc (-1 : ℝ) 1 := ⟨hw.1.le, hw.2.le⟩
            have hy_mem : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨hin.1.le, hin.2.le⟩
            simp [upow, unif, Set.indicator_of_mem hw_mem, Set.indicator_of_mem hy_mem]
          · have hout : y ∈ (Set.Icc (-1 : ℝ) 1)ᶜ := fun hm =>
              hin ⟨lt_of_le_of_ne hm.1 hy1.1.symm, lt_of_le_of_ne hm.2 hy1.2⟩
            filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with w hw
            simp [upow, unif, Set.indicator_of_notMem hw, Set.indicator_of_notMem hout]
        have h1 : ∀ᶠ z in 𝓝 x, upow 1 0 (z + 1) = upow 1 0 (x + 1) ∧
            upow 1 0 (z - 1) = upow 1 0 (x - 1) :=
          ((continuousAt_id.add continuousAt_const).eventually (hloc _ hx1)).and
            ((continuousAt_id.sub continuousAt_const).eventually (hloc _ hx2))
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h1
        filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
        have hconv := fun w => unif_convolution_eq one_pos (integrable_unif 1) w
        have hev_p : (fun w => ∫ t in (0 : ℝ)..w + 1, unif 1 t) =ᶠ[𝓝 z]
            fun w => (∫ t in (0 : ℝ)..x + 1, unif 1 t) +
              ((w + 1) - (x + 1)) * upow 1 0 (x + 1) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (integrable_unif 1).intervalIntegrable
            (integrable_unif 1).intervalIntegrable (b := x + 1)]
          congr 1
          have hconst : Set.EqOn (unif 1) (fun _ => upow 1 0 (x + 1)) (Set.uIoc (x + 1) (w + 1)) := by
            intro t ht
            have htw : dist (t - 1) x < δ := by
              rw [Metric.mem_ball] at hw
              rw [Real.dist_eq] at hw ⊢
              rcases le_total (x + 1) (w + 1) with hle | hle
              · rw [Set.uIoc_of_le hle] at ht; rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
              · rw [Set.uIoc_of_ge hle] at ht; rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
            simpa [upow] using (hball htw).1
          rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => hconst ht),
            intervalIntegral.integral_const, smul_eq_mul]
        have hev_m : (fun w => ∫ t in (0 : ℝ)..w - 1, unif 1 t) =ᶠ[𝓝 z]
            fun w => (∫ t in (0 : ℝ)..x - 1, unif 1 t) +
              ((w - 1) - (x - 1)) * upow 1 0 (x - 1) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (integrable_unif 1).intervalIntegrable
            (integrable_unif 1).intervalIntegrable (b := x - 1)]
          congr 1
          have hconst : Set.EqOn (unif 1) (fun _ => upow 1 0 (x - 1)) (Set.uIoc (x - 1) (w - 1)) := by
            intro t ht
            have htw : dist (t + 1) x < δ := by
              rw [Metric.mem_ball] at hw
              rw [Real.dist_eq] at hw ⊢
              rcases le_total (x - 1) (w - 1) with hle | hle
              · rw [Set.uIoc_of_le hle] at ht; rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
              · rw [Set.uIoc_of_ge hle] at ht; rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
            simpa [upow] using (hball htw).2
          rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => hconst ht),
            intervalIntegral.integral_const, smul_eq_mul]
        have hev_u : upow 1 1 =ᶠ[𝓝 z] fun w => (1 / 2 : ℝ) *
            (((∫ t in (0 : ℝ)..x + 1, unif 1 t) + ((w + 1) - (x + 1)) * upow 1 0 (x + 1)) -
             ((∫ t in (0 : ℝ)..x - 1, unif 1 t) + ((w - 1) - (x - 1)) * upow 1 0 (x - 1))) := by
          filter_upwards [hev_p, hev_m] with w hp hm
          change (unif 1 ⋆ unif 1) w = _; rw [hconv w, hp, hm]; ring
        have hd_p : HasDerivAt (fun w => (∫ t in (0 : ℝ)..x + 1, unif 1 t) +
            ((w + 1) - (x + 1)) * upow 1 0 (x + 1)) (upow 1 0 (x + 1)) z := by
          exact (((((hasDerivAt_id z).add_const 1).sub_const (x + 1)).mul_const
            (upow 1 0 (x + 1))).const_add _).congr_deriv (by ring)
        have hd_m : HasDerivAt (fun w => (∫ t in (0 : ℝ)..x - 1, unif 1 t) +
            ((w - 1) - (x - 1)) * upow 1 0 (x - 1)) (upow 1 0 (x - 1)) z := by
          exact (((((hasDerivAt_id z).sub_const 1).sub_const (x - 1)).mul_const
            (upow 1 0 (x - 1))).const_add _).congr_deriv (by ring)
        rw [(hball hz).1, (hball hz).2]
        exact ((hd_p.sub hd_m).const_mul (1 / 2)).congr_of_eventuallyEq hev_u
      · exact Eventually.of_forall fun z => hasDerivAt_upow_succ (Nat.succ_pos m') z
    have hder_ev : deriv (upow 1 (m + 1)) =ᶠ[𝓝 x]
        fun z => (1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1)) :=
      hd_nhds.mono fun z hz => hz.deriv
    have hc_rhs : ContDiffAt ℝ ∞
        (fun z => (1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1))) x :=
      contDiffAt_const.mul ((hc1.comp x (contDiffAt_id.add contDiffAt_const)).sub
        (hc2.comp x (contDiffAt_id.sub contDiffAt_const)))
    have hc_top : ContDiffAt ℝ ∞ (upow 1 (m + 1)) x := by
      rw [contDiffAt_infty]; intro n
      rcases n with _ | n
      · exact ((contDiff_upow one_pos m).of_le (by simp)).contDiffAt
      · exact contDiffAt_succ_of_eventually_hasDerivAt hd_nhds (hc_rhs.of_le (nat_le_infty n))
    refine ⟨hc_top, fun r => ?_⟩
    rcases r with _ | r
    · simpa only [iteratedDeriv_zero] using abs_upow_one_le (m + 1) x
    · rw [iteratedDeriv_succ', hder_ev.iteratedDeriv_eq r]
      have h1c : ContDiffAt ℝ r (fun z => upow 1 m (z + 1)) x :=
        (hc1.of_le (nat_le_infty r)).comp x (contDiffAt_id.add contDiffAt_const)
      have h2c : ContDiffAt ℝ r (fun z => upow 1 m (z - 1)) x :=
        (hc2.of_le (nat_le_infty r)).comp x (contDiffAt_id.sub contDiffAt_const)
      rw [_root_.iteratedDeriv_const_mul_field, iteratedDeriv_fun_sub h1c h2c,
        iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have htri := (abs_sub _ _).trans (add_le_add (hb1 r) (hb2 r))
      linarith

private def OffKnotBounded (k : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), f x = 0) ∧
    (∀ x ∉ splineKnots, ContDiffAt ℝ k f x) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8),
      x ∉ splineKnots → ∀ r ≤ k, |iteratedDeriv r f x| ≤ M

private theorem offKnot_mono {k j : ℕ} (hjk : j ≤ k) {f : ℝ → ℝ} (hf : OffKnotBounded k f) :
    OffKnotBounded j f := by
  obtain ⟨hs, hc, M, hM0, hb⟩ := hf
  exact ⟨hs, fun x hx => (hc x hx).of_le (by exact_mod_cast hjk),
    M, hM0, fun x hxS hxk r hr => hb x hxS hxk r (hr.trans hjk)⟩

private theorem offKnot_add {k : ℕ} {f g : ℝ → ℝ}
    (hf : OffKnotBounded k f) (hg : OffKnotBounded k g) :
    OffKnotBounded k (fun x => f x + g x) := by
  obtain ⟨hsf, hcf, Mf, hMf0, hbf⟩ := hf
  obtain ⟨hsg, hcg, Mg, hMg0, hbg⟩ := hg
  refine ⟨fun x hx => by dsimp only; rw [hsf x hx, hsg x hx, add_zero],
    fun x hx => (hcf x hx).add (hcg x hx), Mf + Mg, add_nonneg hMf0 hMg0,
    fun x hxS hxk r hr => ?_⟩
  rw [iteratedDeriv_fun_add ((hcf x hxk).of_le (by exact_mod_cast hr))
    ((hcg x hxk).of_le (by exact_mod_cast hr))]
  exact (abs_add_le _ _).trans (add_le_add (hbf x hxS hxk r hr) (hbg x hxS hxk r hr))

private theorem offKnot_deriv {k : ℕ} {f : ℝ → ℝ} (hf : OffKnotBounded (k + 1) f) :
    OffKnotBounded k (deriv f) := by
  obtain ⟨hsf, hcf, M, hM0, hbf⟩ := hf
  refine ⟨fun x hx => ?_, fun x hx => (contDiffAt_deriv_of_succ (hcf x hx)).2,
    M, hM0, fun x hxS hxk r hr => ?_⟩
  · have hev : f =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hx) fun z hz => hsf z hz
    simpa using hev.deriv_eq
  · rw [← iteratedDeriv_succ']
    exact hbf x hxS hxk (r + 1) (Nat.succ_le_succ hr)

private theorem offKnot_mul_smooth :
    ∀ {k : ℕ} {f φ : ℝ → ℝ}, OffKnotBounded k f → ContDiffOn ℝ ∞ φ (Set.Ioi 0) →
      OffKnotBounded k (fun x => φ x * f x)
  | 0, f, φ, ⟨hsf, hcf, Mf, hMf0, hbf⟩, hφ => by
    let S := Set.Icc (Real.exp (-8)) (4 * Real.exp 8)
    have hsub : S ⊆ Set.Ioi 0 := fun z hz => (Real.exp_pos (-8)).trans_le hz.1
    obtain ⟨Mφ, hMφ⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
      (hφ.continuousOn.mono hsub)
    have hSpt : Real.exp (-8) ∈ S := ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-8 : ℝ) < 8); linarith [Real.exp_pos 8]⟩
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ _ hSpt)
    refine ⟨fun x hx => by dsimp only; rw [hsf x hx, mul_zero], fun x hx => ?_,
      Mφ * Mf, mul_nonneg hMφ0 hMf0, fun x hxS hxk r hr => ?_⟩
    · by_cases hp : 0 < x
      · exact ((hφ.contDiffAt (isOpen_Ioi.mem_nhds hp)).of_le (by simp)).mul (hcf x hx)
      · have hev : (fun z => φ z * f z) =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with z hz
          rw [hsf z fun h => hz.not_ge h.1, mul_zero]; rfl
        exact contDiffAt_const.congr_of_eventuallyEq hev
    · obtain rfl := Nat.le_zero.mp hr
      simp only [iteratedDeriv_zero, abs_mul]
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hMφ x hxS)
        (hbf x hxS hxk 0 le_rfl) (abs_nonneg _) hMφ0
  | k + 1, f, φ, hf, hφ => by
    have hdφ : ContDiffOn ℝ ∞ (deriv φ) (Set.Ioi 0) :=
      hφ.deriv_of_isOpen isOpen_Ioi (by simp)
    have hsum := offKnot_add (offKnot_mul_smooth (offKnot_mono (Nat.le_succ k) hf) hdφ)
      (offKnot_mul_smooth (offKnot_deriv hf) hφ)
    have h0 := offKnot_mul_smooth (offKnot_mono (Nat.zero_le _) hf) hφ
    have hopenK : IsOpen (splineKnots : Set ℝ)ᶜ := splineKnots.finite_toSet.isClosed.isOpen_compl
    have hd_off : ∀ z ∉ splineKnots,
        HasDerivAt (fun w => φ w * f w) (deriv φ z * f z + φ z * deriv f z) z := by
      intro z hz
      by_cases hp : 0 < z
      · have hφd : DifferentiableAt ℝ φ z :=
          (hφ.differentiableOn (by simp) z hp).differentiableAt (isOpen_Ioi.mem_nhds hp)
        have hfd : DifferentiableAt ℝ f z := (contDiffAt_deriv_of_succ (hf.2.1 z hz)).1
        exact hφd.hasDerivAt.mul hfd.hasDerivAt
      · have hzS : z ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) :=
          fun h => hp ((Real.exp_pos (-8)).trans_le h.1)
        have hev : (fun w => φ w * f w) =ᶠ[𝓝 z] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with w hw
          rw [hf.1 w fun h => hw.not_ge h.1, mul_zero]; rfl
        rw [hf.1 z hzS, (offKnot_deriv hf).1 z hzS, mul_zero, mul_zero, add_zero]
        exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev
    obtain ⟨M0, hM0, hb0⟩ := h0.2.2
    obtain ⟨Ms, hMs, hbs⟩ := hsum.2.2
    refine ⟨h0.1, fun x hx => ?_, max M0 Ms, le_trans hM0 (le_max_left _ _),
      fun x hxS hxk r hr => ?_⟩
    · exact contDiffAt_succ_of_eventually_hasDerivAt
        (Filter.eventually_of_mem (hopenK.mem_nhds hx) fun z hz => hd_off z hz)
        (hsum.2.1 x hx)
    · rcases r with _ | r
      · exact (hb0 x hxS hxk 0 le_rfl).trans (le_max_left _ _)
      · have hev : deriv (fun w => φ w * f w) =ᶠ[𝓝 x]
            fun z => deriv φ z * f z + φ z * deriv f z :=
          Filter.eventuallyEq_of_mem (hopenK.mem_nhds hxk) fun z hz => (hd_off z hz).deriv
        rw [iteratedDeriv_succ', hev.iteratedDeriv_eq r]
        exact (hbs x hxS hxk r (Nat.le_of_succ_le_succ hr)).trans (le_max_right _ _)

private theorem offKnot_comp_log :
    ∀ {k : ℕ} {H : ℝ → ℝ},
      (∀ u ∉ Set.Icc (-8 : ℝ) (8 + Real.log 4), H u = 0) →
      (∀ x ∉ splineKnots, 0 < x → ContDiffAt ℝ (k + 1 : ℕ) H (Real.log x)) →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8),
        x ∉ splineKnots → ∀ r ≤ k + 1, |iteratedDeriv r H (Real.log x)| ≤ M) →
      OffKnotBounded k fun x => if 0 < x then H (Real.log x) else 0
  | 0, H, hsuppH, hcH, ⟨MH, hMH0, hbH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    have hsg : ∀ x ∉ Set.Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0 := by
      intro x hx; dsimp only [g]
      by_cases hp : 0 < x
      · rw [if_pos hp]
        refine hsuppH (Real.log x) fun hu => hx ⟨?_, ?_⟩
        · rw [← Real.exp_log hp]; exact Real.exp_le_exp.mpr hu.1
        · rw [← Real.exp_log hp]
          exact (Real.exp_le_exp.mpr hu.2).trans_eq
            (by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), mul_comm])
      · exact if_neg hp
    refine ⟨hsg, fun x hx => ?_, MH, hMH0, fun x hxS hxk r hr => ?_⟩
    · by_cases hp : 0 < x
      · have hev : g =ᶠ[𝓝 x] fun z => H (Real.log z) := by
          filter_upwards [lt_mem_nhds hp] with z hz; exact if_pos hz
        exact (((hcH x hx hp).of_le (by norm_num)).comp x
          ((Real.contDiffAt_log (n := 0)).mpr hp.ne')).congr_of_eventuallyEq hev
      · have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with z hz
          exact hsg z fun h => hz.not_ge h.1
        exact contDiffAt_const.congr_of_eventuallyEq hev
    · obtain rfl := Nat.le_zero.mp hr
      have hp : 0 < x := (Real.exp_pos (-8)).trans_le hxS.1
      simp only [iteratedDeriv_zero, if_pos hp]
      simpa using hbH x hxS hxk 0 (Nat.zero_le _)
  | k + 1, H, hsuppH, hcH, ⟨MH, hMH0, hbH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    have hsuppH' : ∀ u ∉ Set.Icc (-8 : ℝ) (8 + Real.log 4), deriv H u = 0 := by
      intro u hu
      have hev : H =ᶠ[𝓝 u] 0 :=
        Filter.eventuallyEq_of_mem (isClosed_Icc.isOpen_compl.mem_nhds hu) fun z hz => hsuppH z hz
      simpa using hev.deriv_eq
    have hcH' : ∀ x ∉ splineKnots, 0 < x → ContDiffAt ℝ (k + 1 : ℕ) (deriv H) (Real.log x) :=
      fun x hx hp => (contDiffAt_deriv_of_succ (hcH x hx hp)).2
    have hbH' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8),
        x ∉ splineKnots → ∀ r ≤ k + 1, |iteratedDeriv r (deriv H) (Real.log x)| ≤ M :=
      ⟨MH, hMH0, fun x hxS hxk r hr => by
        rw [← iteratedDeriv_succ']
        exact hbH x hxS hxk (r + 1) (Nat.succ_le_succ hr)⟩
    have ih := offKnot_comp_log hsuppH' hcH' hbH'
    have hinv : ContDiffOn ℝ ∞ Inv.inv (Set.Ioi (0 : ℝ)) :=
      (contDiffOn_inv ℝ).mono fun x (hx : 0 < x) => hx.ne'
    have hmul := offKnot_mul_smooth ih hinv
    have h0 := offKnot_comp_log (k := 0) hsuppH
      (fun x hx hp => (hcH x hx hp).of_le (by norm_cast; omega))
      ⟨MH, hMH0, fun x hxS hxk r hr => hbH x hxS hxk r (hr.trans (by omega))⟩
    have hopenK : IsOpen (splineKnots : Set ℝ)ᶜ := splineKnots.finite_toSet.isClosed.isOpen_compl
    have hd_off : ∀ z ∉ splineKnots,
        HasDerivAt g (z⁻¹ * (if 0 < z then deriv H (Real.log z) else 0)) z := by
      intro z hz
      by_cases hp : 0 < z
      · have hev : g =ᶠ[𝓝 z] fun w => H (Real.log w) := by
          filter_upwards [lt_mem_nhds hp] with w hw; exact if_pos hw
        have hdH : HasDerivAt H (deriv H (Real.log z)) (Real.log z) :=
          (contDiffAt_deriv_of_succ (hcH z hz hp)).1.hasDerivAt
        rw [if_pos hp, mul_comm]
        exact (hdH.comp z (Real.hasDerivAt_log hp.ne')).congr_of_eventuallyEq hev
      · have hev : g =ᶠ[𝓝 z] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with w hw
          exact h0.1 w fun h => hw.not_ge h.1
        rw [if_neg hp, mul_zero]
        exact (hasDerivAt_const z (0 : ℝ)).congr_of_eventuallyEq hev
    obtain ⟨M0, hM0, hb0⟩ := h0.2.2
    obtain ⟨Mm, hMm, hbm⟩ := hmul.2.2
    refine ⟨h0.1, fun x hx => ?_, max M0 Mm, le_trans hM0 (le_max_left _ _),
      fun x hxS hxk r hr => ?_⟩
    · exact contDiffAt_succ_of_eventually_hasDerivAt
        (Filter.eventually_of_mem (hopenK.mem_nhds hx) fun z hz => hd_off z hz)
        (hmul.2.1 x hx)
    · rcases r with _ | r
      · exact (hb0 x hxS hxk 0 le_rfl).trans (le_max_left _ _)
      · have hev : deriv g =ᶠ[𝓝 x] fun z => z⁻¹ * (if 0 < z then deriv H (Real.log z) else 0) :=
          Filter.eventuallyEq_of_mem (hopenK.mem_nhds hxk) fun z hz => (hd_off z hz).deriv
        rw [iteratedDeriv_succ', hev.iteratedDeriv_eq r]
        exact (hbm x hxS hxk r (Nat.le_of_succ_le_succ hr)).trans (le_max_right _ _)

private theorem log_not_mem_upowKnots {x : ℝ} (hx : x ∉ splineKnots) (hp : 0 < x) :
    Real.log x ∉ upowKnots 7 ∧ Real.log x - Real.log 4 ∉ upowKnots 7 := by
  constructor
  · intro h
    exact hx (mem_union_left _ (mem_image.mpr ⟨Real.log x, h, Real.exp_log hp⟩))
  · intro h
    apply hx
    refine mem_union_right _ (mem_image.mpr ⟨Real.log x - Real.log 4, h, ?_⟩)
    rw [sub_add_cancel, Real.exp_log hp]

private theorem offKnot_nine_dyadicSpline : OffKnotBounded 9 dyadicSpline := by
  have hAeq : splineAutoCorr = upow 1 7 := funext splineAutoCorr_eq_eight_boxes
  have hcF : ∀ x ∉ splineKnots, 0 < x → ContDiffAt ℝ (10 : ℕ) squareLogProfile (Real.log x) := by
    intro x hx hp
    obtain ⟨hk1, hk2⟩ := log_not_mem_upowKnots hx hp
    obtain ⟨hc1, _⟩ := smooth_bounded_upow 7 (Real.log x) hk1
    obtain ⟨hc2, _⟩ := smooth_bounded_upow 7 (Real.log x - Real.log 4) hk2
    unfold squareLogProfile; rw [hAeq]
    exact (contDiffAt_const.mul (hc1.of_le (nat_le_infty 10))).sub
      ((hc2.of_le (nat_le_infty 10)).comp (Real.log x) (contDiffAt_id.sub contDiffAt_const))
  have hbF : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8),
      x ∉ splineKnots → ∀ r ≤ 10, |iteratedDeriv r squareLogProfile (Real.log x)| ≤ M := by
    refine ⟨3 / 2, by norm_num, fun x hxS hxk r _ => ?_⟩
    have hp : 0 < x := (Real.exp_pos (-8)).trans_le hxS.1
    obtain ⟨hk1, hk2⟩ := log_not_mem_upowKnots hxk hp
    obtain ⟨hc1, hb1⟩ := smooth_bounded_upow 7 (Real.log x) hk1
    obtain ⟨hc2, hb2⟩ := smooth_bounded_upow 7 (Real.log x - Real.log 4) hk2
    unfold squareLogProfile; rw [hAeq]
    have h1 : ContDiffAt ℝ r (fun z => 2 * upow 1 7 z) (Real.log x) :=
      contDiffAt_const.mul (hc1.of_le (nat_le_infty r))
    have h2 : ContDiffAt ℝ r (fun z => upow 1 7 (z - Real.log 4)) (Real.log x) :=
      (hc2.of_le (nat_le_infty r)).comp (Real.log x) (contDiffAt_id.sub contDiffAt_const)
    rw [iteratedDeriv_fun_sub h1 h2, _root_.iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_sub_const]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [hb1 r, hb2 r]
  have hlog := offKnot_comp_log (k := 9) (fun _ => squareLogProfile_eq_zero_outside) hcF hbF
  have hφ : ContDiffOn ℝ ∞ (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) (Set.Ioi 0) :=
    contDiffOn_const.mul fun x (hx : 0 < x) =>
      (Real.contDiffAt_rpow_const_of_ne hx.ne').contDiffWithinAt
  have hmul := offKnot_mul_smooth hlog hφ
  have heq : (fun x : ℝ => (2 * x ^ (-(1 / 2 : ℝ))) *
      (if 0 < x then squareLogProfile (Real.log x) else 0)) = dyadicSpline := by
    funext x
    by_cases hx : 0 < x
    · simp only [if_pos hx, dyadicSpline, squarePrimeWeight, Complex.ofReal_re]
      rw [Real.rpow_def_of_pos hx]; ring_nf
    · simp only [if_neg hx, dyadicSpline, mul_zero]
  rwa [heq] at hmul

/-! ### Local mean value theorem and discrete sum bounds -/

private theorem differentiableAt_iteratedDeriv_of_contDiffAt :
    ∀ k : ℕ, ∀ {g : ℝ → ℝ} {x : ℝ}, ContDiffAt ℝ (k + 1 : ℕ) g x →
      DifferentiableAt ℝ (iteratedDeriv k g) x
  | 0, g, x, hg => by simpa using (contDiffAt_deriv_of_succ hg).1
  | k + 1, g, x, hg => by
    rw [iteratedDeriv_succ']
    exact differentiableAt_iteratedDeriv_of_contDiffAt k (contDiffAt_deriv_of_succ hg).2

private theorem exists_fwdDiff_iter_eq_Ioo :
    ∀ (k : ℕ) {a b : ℝ} {g : ℝ → ℝ}, (∀ x ∈ Set.Ioo a b, ContDiffAt ℝ k g x) →
      ∀ (h u : ℝ), 0 < h → a < u → u + k * h < b →
        ∃ ξ ∈ Set.Icc u (u + k * h), (fwdDiff h)^[k] g u = h ^ k * iteratedDeriv k g ξ
  | 0, a, b, g, _, h, u, _, _, _ => ⟨u, ⟨le_rfl, by simp⟩, by simp⟩
  | k + 1, a, b, g, hg, h, u, hh, hau, hub => by
    have hgk : ∀ x ∈ Set.Ioo a (b - h), ContDiffAt ℝ k (fwdDiff h g) x := fun x hx => by
      have hx1 : x ∈ Set.Ioo a b := ⟨hx.1, by linarith [hx.2]⟩
      have hx2 : x + h ∈ Set.Ioo a b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
      change ContDiffAt ℝ k (fun z => g (z + h) - g z) x
      exact (((hg (x + h) hx2).of_le (by exact_mod_cast Nat.le_succ k)).comp x
        (contDiffAt_id.add contDiffAt_const)).sub
        ((hg x hx1).of_le (by exact_mod_cast Nat.le_succ k))
    have hub' : u + k * h < b - h := by push_cast at hub; linarith
    obtain ⟨ξ', hξ', heq⟩ := exists_fwdDiff_iter_eq_Ioo k hgk h u hh hau hub'
    have hsub_ab : Set.Icc ξ' (ξ' + h) ⊆ Set.Ioo a b := fun z hz =>
      ⟨by linarith [hau, hξ'.1, hz.1], by linarith [hub', hξ'.2, hz.2]⟩
    have hdiff : ∀ z ∈ Set.Icc ξ' (ξ' + h), DifferentiableAt ℝ (iteratedDeriv k g) z :=
      fun z hz => differentiableAt_iteratedDeriv_of_contDiffAt k (hg z (hsub_ab hz))
    obtain ⟨ξ, hξ, hmv⟩ := exists_deriv_eq_slope (iteratedDeriv k g) (by linarith : ξ' < ξ' + h)
      (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hdiff z ⟨hz.1.le, hz.2.le⟩).differentiableWithinAt)
    have hiter_sub : iteratedDeriv k (fwdDiff h g) ξ' =
        iteratedDeriv k g (ξ' + h) - iteratedDeriv k g ξ' := by
      have hx1 : ξ' ∈ Set.Ioo a b := hsub_ab ⟨le_rfl, by linarith⟩
      have hx2 : ξ' + h ∈ Set.Ioo a b := hsub_ab ⟨by linarith, le_rfl⟩
      have hc1 : ContDiffAt ℝ k (fun z => g (z + h)) ξ' :=
        ((hg (ξ' + h) hx2).of_le (by exact_mod_cast Nat.le_succ k)).comp ξ'
          (contDiffAt_id.add contDiffAt_const)
      have hc2 : ContDiffAt ℝ k g ξ' := (hg ξ' hx1).of_le (by exact_mod_cast Nat.le_succ k)
      change iteratedDeriv k (fun z => g (z + h) - g z) ξ' = _
      rw [iteratedDeriv_fun_sub hc1 hc2, iteratedDeriv_comp_add_const]
    rw [← iteratedDeriv_succ, add_sub_cancel_left] at hmv
    refine ⟨ξ, ⟨by linarith [hξ'.1, hξ.1], ?_⟩, ?_⟩
    · push_cast; linarith [hξ'.2, hξ.2]
    · rw [Function.iterate_succ_apply, heq, hiter_sub, hmv]
      field_simp [hh.ne']; ring

private theorem fwdDiff_iter_lipschitz_bound (k : ℕ) {g : ℝ → ℝ} {K : ℝ≥0}
    (hg : ContDiff ℝ k g) (hL : LipschitzWith K (iteratedDeriv k g))
    {h : ℝ} (hh : 0 < h) (u : ℝ) :
    |(fwdDiff h)^[k + 1] g u| ≤ ((k + 1 : ℕ) : ℝ) * K * h ^ (k + 1) := by
  have he : (fwdDiff h)^[k + 1] g u = (fwdDiff h)^[k] g (u + h) - (fwdDiff h)^[k] g u := by
    rw [Function.iterate_succ_apply']; rfl
  obtain ⟨ξ1, hξ1, e1⟩ := exists_fwdDiff_iter_eq k hg hh (u + h)
  obtain ⟨ξ2, hξ2, e2⟩ := exists_fwdDiff_iter_eq k hg hh u
  rw [he, e1, e2, ← mul_sub, abs_mul, abs_of_pos (pow_pos hh k)]
  have hdist : |ξ1 - ξ2| ≤ ((k + 1 : ℕ) : ℝ) * h := by
    rw [abs_le]; push_cast
    constructor <;> linarith [hξ1.1, hξ1.2, hξ2.1, hξ2.2]
  have hlip : |iteratedDeriv k g ξ1 - iteratedDeriv k g ξ2| ≤ K * |ξ1 - ξ2| := by
    simpa [Real.dist_eq] using hL.dist_le_mul ξ1 ξ2
  calc h ^ k * |iteratedDeriv k g ξ1 - iteratedDeriv k g ξ2|
      ≤ h ^ k * (K * (((k + 1 : ℕ) : ℝ) * h)) :=
        mul_le_mul_of_nonneg_left (hlip.trans (mul_le_mul_of_nonneg_left hdist K.coe_nonneg))
          (pow_nonneg hh.le k)
    _ = ((k + 1 : ℕ) : ℝ) * K * h ^ (k + 1) := by rw [pow_succ]; ring

private theorem card_knot_hits_le {h : ℝ} (hh : 0 < h) (m : ℕ) {S : Finset ℕ}
    (hS : ∀ j ∈ S,
      ¬ Disjoint (Set.Icc ((j : ℝ) * h) (((j + m : ℕ) : ℝ) * h)) (splineKnots : Set ℝ)) :
    S.card ≤ 18 * (m + 1) := by
  classical
  let B := fun t : ℝ => Icc (⌊t / h⌋₊ - m) ⌊t / h⌋₊
  have hsub : S ⊆ splineKnots.biUnion B := by
    intro j hj
    have hnd := hS j hj
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨t, ⟨ht1, ht2⟩, htk⟩ := hnd
    have htk' : t ∈ splineKnots := htk
    have ht0 : 0 ≤ t / h := div_nonneg (splineKnots_pos htk').le hh.le
    have hj_hi : j ≤ ⌊t / h⌋₊ := Nat.le_floor ((le_div_iff₀ hh).mpr ht1)
    have hj_lo : ⌊t / h⌋₊ ≤ j + m := by
      have : (⌊t / h⌋₊ : ℝ) < ((j + m + 1 : ℕ) : ℝ) := by
        calc (⌊t / h⌋₊ : ℝ) ≤ t / h := Nat.floor_le ht0
          _ ≤ (j + m : ℕ) := (div_le_iff₀ hh).mpr ht2
          _ < (j + m + 1 : ℕ) := by push_cast; linarith
      exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp this)
    exact mem_biUnion.mpr ⟨t, htk', mem_Icc.mpr ⟨by omega, hj_hi⟩⟩
  calc S.card ≤ (splineKnots.biUnion B).card := card_le_card hsub
    _ ≤ ∑ t ∈ splineKnots, (B t).card := card_biUnion_le
    _ ≤ ∑ _t ∈ splineKnots, (m + 1) := sum_le_sum fun t _ => by
        dsimp only [B]; rw [Nat.card_Icc]; omega
    _ = splineKnots.card * (m + 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ 18 * (m + 1) := Nat.mul_le_mul_right _ card_splineKnots_le

private theorem card_active_grid_le {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (b : ℕ) :
    (((range b).filter fun j : ℕ => (j : ℝ) * h ≤ 4 * Real.exp 8).card : ℝ) ≤
      (4 * Real.exp 8 + 1) / h := by
  let A := (range b).filter fun j : ℕ => (j : ℝ) * h ≤ 4 * Real.exp 8
  have hsub : A ⊆ Icc 0 ⌊4 * Real.exp 8 / h⌋₊ := by
    intro j hj
    exact mem_Icc.mpr ⟨Nat.zero_le j,
      Nat.le_floor ((le_div_iff₀ hh).mpr (mem_filter.mp hj).2)⟩
  have hcard : A.card ≤ ⌊4 * Real.exp 8 / h⌋₊ + 1 :=
    (card_le_card hsub).trans (by simp)
  have hfloor : (⌊4 * Real.exp 8 / h⌋₊ : ℝ) ≤ 4 * Real.exp 8 / h :=
    Nat.floor_le (by positivity)
  have h1 : (1 : ℝ) ≤ 1 / h := (one_le_div hh).mpr hh1
  calc (A.card : ℝ) ≤ (⌊4 * Real.exp 8 / h⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
    _ ≤ 4 * Real.exp 8 / h + 1 / h := add_le_add hfloor h1
    _ = (4 * Real.exp 8 + 1) / h := by ring

private theorem fwdDiff_iter_zero_of_Icc {k : ℕ} {g : ℝ → ℝ} {h u : ℝ} (hh : 0 ≤ h)
    (hz : ∀ x ∈ Set.Icc u (u + k * h), g x = 0) : (fwdDiff h)^[k] g u = 0 := by
  induction k generalizing u with
  | zero => exact hz u ⟨le_rfl, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only [fwdDiff]
    rw [ih (u := u + h), ih (u := u), sub_zero]
    · intro x hx
      exact hz x ⟨hx.1, hx.2.trans (by push_cast; linarith)⟩
    · intro x hx
      exact hz x ⟨by linarith [hx.1], by push_cast; linarith [hx.2]⟩

private theorem disjoint_splineKnots_nhds {a b : ℝ} (hab : a ≤ b)
    (hd : Disjoint (Set.Icc a b) (splineKnots : Set ℝ)) :
    ∃ δ > 0, Disjoint (Set.Ioo (a - δ) (b + δ)) (splineKnots : Set ℝ) ∧
      ((b < Real.exp (-8)) ∨ (4 * Real.exp 8 < a) ∨
        (Real.exp (-8) < a - δ ∧ b + δ < 4 * Real.exp 8)) := by
  have hnot_mem : ∀ t ∈ splineKnots, t < a ∨ b < t := fun t ht => by
    by_contra! h
    exact Set.disjoint_left.mp hd h ht
  have hexp_lo : Real.exp (-8) < a ∨ b < Real.exp (-8) :=
    hnot_mem _ exp_neg_eight_mem_splineKnots
  have hexp_hi : 4 * Real.exp 8 < a ∨ b < 4 * Real.exp 8 :=
    hnot_mem _ four_mul_exp_eight_mem_splineKnots
  have hopen : IsOpen (splineKnots : Set ℝ)ᶜ := splineKnots.finite_toSet.isClosed.isOpen_compl
  obtain ⟨ε, hε, hthick⟩ := isCompact_Icc.exists_thickening_subset_open hopen hd.subset_compl_right
  rcases hexp_lo with hlo | hlo
  · rcases hexp_hi with hhi | hhi
    · refine ⟨min (ε / 2) ((a - 4 * Real.exp 8) / 2), lt_min (half_pos hε) (by linarith), ?_,
        Or.inr (Or.inl hhi)⟩
      refine Set.disjoint_left.mpr fun x hx hxk => hthick ?_ hxk
      rw [Metric.mem_thickening_iff]
      by_cases hxa : x < a
      · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        linarith [hx.1, min_le_left (ε / 2) ((a - 4 * Real.exp 8) / 2)]
      · by_cases hxb : b < x
        · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hx.2, min_le_left (ε / 2) ((a - 4 * Real.exp 8) / 2)]
        · exact ⟨x, ⟨not_lt.mp hxa, not_lt.mp hxb⟩, by simpa using hε⟩
    · let δ := min (ε / 2) (min ((a - Real.exp (-8)) / 2) ((4 * Real.exp 8 - b) / 2))
      have hδ : 0 < δ := lt_min (half_pos hε) (lt_min (by linarith) (by linarith))
      refine ⟨δ, hδ, ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · refine Set.disjoint_left.mpr fun x hx hxk => hthick ?_ hxk
        rw [Metric.mem_thickening_iff]
        by_cases hxa : x < a
        · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
          rw [Real.dist_eq, abs_of_neg (by linarith)]
          linarith [hx.1, min_le_left (ε / 2) (min ((a - Real.exp (-8)) / 2) ((4 * Real.exp 8 - b) / 2))]
        · by_cases hxb : b < x
          · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            linarith [hx.2, min_le_left (ε / 2) (min ((a - Real.exp (-8)) / 2) ((4 * Real.exp 8 - b) / 2))]
          · exact ⟨x, ⟨not_lt.mp hxa, not_lt.mp hxb⟩, by simpa using hε⟩
      · have : δ ≤ (a - Real.exp (-8)) / 2 := (min_le_right _ _).trans (min_le_left _ _)
        linarith
      · have : δ ≤ (4 * Real.exp 8 - b) / 2 := (min_le_right _ _).trans (min_le_right _ _)
        linarith
  · refine ⟨ε / 2, half_pos hε, ?_, Or.inl hlo⟩
    refine Set.disjoint_left.mpr fun x hx hxk => hthick ?_ hxk
    rw [Metric.mem_thickening_iff]
    by_cases hxa : x < a
    · refine ⟨a, ⟨le_rfl, hab⟩, ?_⟩
      rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith [hx.1]
    · by_cases hxb : b < x
      · refine ⟨b, ⟨hab, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [hx.2]
      · exact ⟨x, ⟨not_lt.mp hxa, not_lt.mp hxb⟩, by simpa using hε⟩

/-- Eighth-order grid-sum bound for `dyadicSpline`: smooth blocks pay `O(h⁻¹ · h⁸)`
and the `≤ 162` knot-straddling stencils pay `O(h⁷)` via `C^{6,1}` regularity. -/
theorem sum_fwdDiff_eight_dyadicSpline_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → ∀ b : ℕ,
      (∑ j ∈ range b, |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) ≤ K * h ^ 7 := by
  obtain ⟨KL, hKL⟩ := lipschitz_iteratedDeriv_six_dyadicSpline
  obtain ⟨_, hc8, M8, hM80, hb8⟩ := offKnot_mono (by decide : 8 ≤ 9) offKnot_nine_dyadicSpline
  let K := (4 * Real.exp 8 + 1) * M8 + (18 * 9 : ℝ) * (14 * (KL : ℝ))
  refine ⟨K, by dsimp only [K]; positivity, fun {h} hh hh1 b => ?_⟩
  let P := fun j : ℕ => Disjoint (Set.Icc ((j : ℝ) * h) (((j + 8 : ℕ) : ℝ) * h)) (splineKnots : Set ℝ)
  classical
  rw [← sum_filter_add_sum_filter_not (range b) P]
  have hknot_each : ∀ j : ℕ, |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)| ≤
      14 * (KL : ℝ) * h ^ 7 := fun j => by
    have he : (fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h) =
        (fwdDiff h)^[7] dyadicSpline ((j : ℝ) * h + h) -
          (fwdDiff h)^[7] dyadicSpline ((j : ℝ) * h) := by
      rw [show (8 : ℕ) = 7 + 1 from rfl, Function.iterate_succ_apply']; rfl
    rw [he]
    have h1 := fwdDiff_iter_lipschitz_bound 6 contDiff_six_dyadicSpline hKL hh ((j : ℝ) * h + h)
    have h2 := fwdDiff_iter_lipschitz_bound 6 contDiff_six_dyadicSpline hKL hh ((j : ℝ) * h)
    refine (abs_sub _ _).trans ?_
    push_cast at h1 h2
    linarith
  have hknot_sum : (∑ j ∈ (range b).filter (fun j => ¬ P j),
      |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) ≤
        (18 * 9 : ℝ) * (14 * (KL : ℝ)) * h ^ 7 := by
    have hc : (((range b).filter (fun j => ¬ P j)).card : ℝ) ≤ 18 * 9 := by
      exact_mod_cast card_knot_hits_le hh 8 fun j hj => (mem_filter.mp hj).2
    calc _ ≤ ∑ _j ∈ (range b).filter (fun j => ¬ P j), (14 * (KL : ℝ) * h ^ 7) :=
          sum_le_sum fun j _ => hknot_each j
      _ = (((range b).filter (fun j => ¬ P j)).card : ℝ) * (14 * (KL : ℝ) * h ^ 7) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (18 * 9 : ℝ) * (14 * (KL : ℝ) * h ^ 7) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (18 * 9 : ℝ) * (14 * (KL : ℝ)) * h ^ 7 := by ring
  let Q := fun j : ℕ => (j : ℝ) * h ≤ 4 * Real.exp 8
  rw [← sum_filter_add_sum_filter_not ((range b).filter P) Q]
  have htail_zero : (∑ j ∈ ((range b).filter P).filter (fun j => ¬ Q j),
      |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) = 0 := by
    apply sum_eq_zero; intro j hj
    have hgt : 4 * Real.exp 8 < (j : ℝ) * h := not_le.mp (mem_filter.mp hj).2
    rw [fwdDiff_iter_zero_of_Icc hh.le fun x hx =>
      dyadicSpline_eq_zero_outside fun hs => (hgt.trans_le hx.1).not_ge hs.2, abs_zero]
  have hsmooth_each : ∀ j ∈ ((range b).filter P).filter Q,
      |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)| ≤ M8 * h ^ 8 := by
    intro j hj
    have hPj : P j := (mem_filter.mp (mem_filter.mp hj).1).2
    have hend : ((j + 8 : ℕ) : ℝ) * h = (j : ℝ) * h + (8 : ℕ) * h := by push_cast; ring
    obtain ⟨δ, hδ, hdisj, hcases⟩ := disjoint_splineKnots_nhds
      (by push_cast; linarith [hh.le]) hPj
    rcases hcases with hlo | hhi | ⟨hin1, hin2⟩
    · rw [fwdDiff_iter_zero_of_Icc hh.le fun x hx => by
        rw [← hend] at hx
        exact dyadicSpline_eq_zero_outside fun hs => (hx.2.trans_lt hlo).not_ge hs.1, abs_zero]
      positivity
    · rw [fwdDiff_iter_zero_of_Icc hh.le fun x hx =>
        dyadicSpline_eq_zero_outside fun hs => (hhi.trans_le hx.1).not_ge hs.2, abs_zero]
      positivity
    · obtain ⟨ξ, hξ, heq⟩ := exists_fwdDiff_iter_eq_Ioo 8
        (a := (j : ℝ) * h - δ) (b := ((j + 8 : ℕ) : ℝ) * h + δ)
        (fun x hx => hc8 x fun hxk => Set.disjoint_left.mp hdisj hx hxk)
        h ((j : ℝ) * h) hh (by linarith) (by rw [← hend]; linarith)
      rw [heq, abs_mul, abs_of_pos (pow_pos hh 8), mul_comm]
      rw [← hend] at hξ
      have hξ_in : ξ ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) :=
        ⟨by linarith [hin1, hξ.1], by linarith [hin2, hξ.2]⟩
      have hξ_nk : ξ ∉ splineKnots := fun hxk =>
        Set.disjoint_left.mp hdisj ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ hxk
      exact mul_le_mul_of_nonneg_right (hb8 ξ hξ_in hξ_nk 8 le_rfl) (pow_nonneg hh.le 8)
  have hsmooth_sum : (∑ j ∈ ((range b).filter P).filter Q,
      |(fwdDiff h)^[8] dyadicSpline ((j : ℝ) * h)|) ≤ (4 * Real.exp 8 + 1) * M8 * h ^ 7 := by
    have hsub : ((range b).filter P).filter Q ⊆ (range b).filter Q := fun j hj =>
      mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hj).1).1, (mem_filter.mp hj).2⟩
    calc _ ≤ ∑ _j ∈ ((range b).filter P).filter Q, (M8 * h ^ 8) := sum_le_sum hsmooth_each
      _ = ((((range b).filter P).filter Q).card : ℝ) * (M8 * h ^ 8) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (((range b).filter Q).card : ℝ) * (M8 * h ^ 8) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
      _ ≤ ((4 * Real.exp 8 + 1) / h) * (M8 * h ^ 8) :=
          mul_le_mul_of_nonneg_right (card_active_grid_le hh hh1 b) (by positivity)
      _ = (4 * Real.exp 8 + 1) * M8 * h ^ 7 := by field_simp [hh.ne']
  rw [htail_zero, add_zero]
  dsimp only [K]
  linarith [hsmooth_sum, hknot_sum]

/-- Ninth-order grid-sum bound for `conductorSplineIntegral`: one integration across
conductors raises global regularity to `C^{7,1}` and off-knot smoothness to ninth order. -/
theorem sum_fwdDiff_nine_conductorSplineIntegral_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → ∀ b : ℕ,
      (∑ j ∈ range b, |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)|) ≤ K * h ^ 8 := by
  obtain ⟨KL, hKL⟩ := lipschitz_iteratedDeriv_seven_conductorSplineIntegral
  have hoff2 : OffKnotBounded 7 (iteratedDeriv 2 conductorSplineIntegral) := by
    rw [iteratedDeriv_two_conductorSplineIntegral]
    exact offKnot_mul_smooth
      (offKnot_deriv (offKnot_mono (by decide : 8 ≤ 9) offKnot_nine_dyadicSpline))
      ((contDiffOn_const.mul contDiffOn_id).inv fun x (hx : 0 < x) => by positivity)
  obtain ⟨_, hc7, M9, hM90, hb9⟩ := hoff2
  have hc9 : ∀ x ∉ splineKnots, ContDiffAt ℝ (9 : ℕ) conductorSplineIntegral x := by
    intro x hx
    have hd2_eq : deriv (deriv conductorSplineIntegral) = iteratedDeriv 2 conductorSplineIntegral := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    have hd0_diff : Differentiable ℝ conductorSplineIntegral :=
      contDiff_seven_conductorSplineIntegral.differentiable (by simp)
    have hd1_diff : Differentiable ℝ (deriv conductorSplineIntegral) := by
      have hc6 : ContDiff ℝ 6 (deriv conductorSplineIntegral) := by
        have h := contDiff_seven_conductorSplineIntegral
        rw [show (7 : ℕ∞ω) = 6 + 1 from rfl] at h
        exact (contDiff_succ_iff_deriv.mp h).2.2
      exact hc6.differentiable (by simp)
    have hc8_d1 : ContDiffAt ℝ (8 : ℕ) (deriv conductorSplineIntegral) x :=
      contDiffAt_succ_of_eventually_hasDerivAt
        (Eventually.of_forall fun z => hd2_eq ▸ hd1_diff.differentiableAt.hasDerivAt)
        (hc7 x hx)
    exact contDiffAt_succ_of_eventually_hasDerivAt
      (Eventually.of_forall fun _ => hd0_diff.differentiableAt.hasDerivAt)
      hc8_d1
  let K := (4 * Real.exp 8 + 1) * M9 + (18 * 10 : ℝ) * (16 * (KL : ℝ))
  refine ⟨K, by dsimp only [K]; positivity, fun {h} hh hh1 b => ?_⟩
  let P := fun j : ℕ => Disjoint (Set.Icc ((j : ℝ) * h) (((j + 9 : ℕ) : ℝ) * h)) (splineKnots : Set ℝ)
  classical
  rw [← sum_filter_add_sum_filter_not (range b) P]
  have hknot_each : ∀ j : ℕ, |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)| ≤
      16 * (KL : ℝ) * h ^ 8 := fun j => by
    have he : (fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h) =
        (fwdDiff h)^[8] conductorSplineIntegral ((j : ℝ) * h + h) -
          (fwdDiff h)^[8] conductorSplineIntegral ((j : ℝ) * h) := by
      rw [show (9 : ℕ) = 8 + 1 from rfl, Function.iterate_succ_apply']; rfl
    rw [he]
    have h1 := fwdDiff_iter_lipschitz_bound 7 contDiff_seven_conductorSplineIntegral hKL hh
      ((j : ℝ) * h + h)
    have h2 := fwdDiff_iter_lipschitz_bound 7 contDiff_seven_conductorSplineIntegral hKL hh
      ((j : ℝ) * h)
    refine (abs_sub _ _).trans ?_
    push_cast at h1 h2
    linarith
  have hknot_sum : (∑ j ∈ (range b).filter (fun j => ¬ P j),
      |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)|) ≤
        (18 * 10 : ℝ) * (16 * (KL : ℝ)) * h ^ 8 := by
    have hc : (((range b).filter (fun j => ¬ P j)).card : ℝ) ≤ 18 * 10 := by
      exact_mod_cast card_knot_hits_le hh 9 fun j hj => (mem_filter.mp hj).2
    calc _ ≤ ∑ _j ∈ (range b).filter (fun j => ¬ P j), (16 * (KL : ℝ) * h ^ 8) :=
          sum_le_sum fun j _ => hknot_each j
      _ = (((range b).filter (fun j => ¬ P j)).card : ℝ) * (16 * (KL : ℝ) * h ^ 8) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (18 * 10 : ℝ) * (16 * (KL : ℝ) * h ^ 8) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (18 * 10 : ℝ) * (16 * (KL : ℝ)) * h ^ 8 := by ring
  let Q := fun j : ℕ => (j : ℝ) * h ≤ 4 * Real.exp 8
  rw [← sum_filter_add_sum_filter_not ((range b).filter P) Q]
  have hlin_diff2 : ∀ u : ℝ, 4 * Real.exp 8 ≤ u →
      (fwdDiff h)^[2] conductorSplineIntegral u = 0 := fun u hu => by
    dsimp [fwdDiff]
    rw [conductorSplineIntegral_linear_after (by linarith : 4 * Real.exp 8 ≤ u + h + h),
      conductorSplineIntegral_linear_after (by linarith : 4 * Real.exp 8 ≤ u + h),
      conductorSplineIntegral_linear_after hu]
    ring
  have htail_zero : (∑ j ∈ ((range b).filter P).filter (fun j => ¬ Q j),
      |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)|) = 0 := by
    apply sum_eq_zero; intro j hj
    have hgt : 4 * Real.exp 8 < (j : ℝ) * h := not_le.mp (mem_filter.mp hj).2
    have hsplit : (fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h) =
        (fwdDiff h)^[7] ((fwdDiff h)^[2] conductorSplineIntegral) ((j : ℝ) * h) := by
      rw [show (9 : ℕ) = 7 + 2 from rfl, Function.iterate_add_apply]
    rw [hsplit, fwdDiff_iter_zero_of_Icc hh.le fun x hx =>
      hlin_diff2 x (hgt.le.trans hx.1), abs_zero]
  have hsmooth_each : ∀ j ∈ ((range b).filter P).filter Q,
      |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)| ≤ M9 * h ^ 9 := by
    intro j hj
    have hPj : P j := (mem_filter.mp (mem_filter.mp hj).1).2
    have hend : ((j + 9 : ℕ) : ℝ) * h = (j : ℝ) * h + (9 : ℕ) * h := by push_cast; ring
    obtain ⟨δ, hδ, hdisj, hcases⟩ := disjoint_splineKnots_nhds
      (by push_cast; linarith [hh.le]) hPj
    rcases hcases with hlo | hhi | ⟨hin1, hin2⟩
    · rw [fwdDiff_iter_zero_of_Icc hh.le fun x hx => by
        rw [← hend] at hx
        exact conductorSplineIntegral_eq_zero_before (hx.2.trans hlo.le), abs_zero]
      positivity
    · have hsplit : (fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h) =
          (fwdDiff h)^[7] ((fwdDiff h)^[2] conductorSplineIntegral) ((j : ℝ) * h) := by
        rw [show (9 : ℕ) = 7 + 2 from rfl, Function.iterate_add_apply]
      rw [hsplit, fwdDiff_iter_zero_of_Icc hh.le fun x hx =>
        hlin_diff2 x (hhi.le.trans hx.1), abs_zero]
      positivity
    · obtain ⟨ξ, hξ, heq⟩ := exists_fwdDiff_iter_eq_Ioo 9
        (a := (j : ℝ) * h - δ) (b := ((j + 9 : ℕ) : ℝ) * h + δ)
        (fun x hx => hc9 x fun hxk => Set.disjoint_left.mp hdisj hx hxk)
        h ((j : ℝ) * h) hh (by linarith) (by rw [← hend]; linarith)
      rw [heq, abs_mul, abs_of_pos (pow_pos hh 9), mul_comm]
      rw [← hend] at hξ
      have hξ_in : ξ ∈ Set.Icc (Real.exp (-8)) (4 * Real.exp 8) :=
        ⟨by linarith [hin1, hξ.1], by linarith [hin2, hξ.2]⟩
      have hξ_nk : ξ ∉ splineKnots := fun hxk =>
        Set.disjoint_left.mp hdisj ⟨by linarith [hξ.1], by linarith [hξ.2]⟩ hxk
      have h9eq : iteratedDeriv 9 conductorSplineIntegral ξ =
          iteratedDeriv 7 (iteratedDeriv 2 conductorSplineIntegral) ξ :=
        congrFun (iteratedDeriv_add_eq 7 2 conductorSplineIntegral) ξ
      rw [h9eq]
      exact mul_le_mul_of_nonneg_right (hb9 ξ hξ_in hξ_nk 7 le_rfl) (pow_nonneg hh.le 9)
  have hsmooth_sum : (∑ j ∈ ((range b).filter P).filter Q,
      |(fwdDiff h)^[9] conductorSplineIntegral ((j : ℝ) * h)|) ≤
        (4 * Real.exp 8 + 1) * M9 * h ^ 8 := by
    have hsub : ((range b).filter P).filter Q ⊆ (range b).filter Q := fun j hj =>
      mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hj).1).1, (mem_filter.mp hj).2⟩
    calc _ ≤ ∑ _j ∈ ((range b).filter P).filter Q, (M9 * h ^ 9) := sum_le_sum hsmooth_each
      _ = ((((range b).filter P).filter Q).card : ℝ) * (M9 * h ^ 9) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (((range b).filter Q).card : ℝ) * (M9 * h ^ 9) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card hsub) (by positivity)
      _ ≤ ((4 * Real.exp 8 + 1) / h) * (M9 * h ^ 9) :=
          mul_le_mul_of_nonneg_right (card_active_grid_le hh hh1 b) (by positivity)
      _ = (4 * Real.exp 8 + 1) * M9 * h ^ 8 := by field_simp [hh.ne']
  rw [htail_zero, add_zero]
  dsimp only [K]
  linarith [hsmooth_sum, hknot_sum]

/-- Fifth-order grid-sum bound for `conductorCurvatureProfile` from global `C^{4,1}` regularity. -/
theorem sum_fwdDiff_five_conductorCurvatureProfile_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {h : ℝ}, 0 < h → h ≤ 1 → ∀ b : ℕ,
      (∑ j ∈ range b, |(fwdDiff h)^[5] conductorCurvatureProfile ((j : ℝ) * h)|) ≤ K * h ^ 4 := by
  obtain ⟨KL, hKL⟩ := lipschitz_iteratedDeriv_four_conductorCurvatureProfile
  let K := (4 * Real.exp 8 + 1) * (5 * (KL : ℝ))
  refine ⟨K, by dsimp only [K]; positivity, fun {h} hh hh1 b => ?_⟩
  let Q := fun j : ℕ => (j : ℝ) * h ≤ 4 * Real.exp 8
  classical
  rw [← sum_filter_add_sum_filter_not (range b) Q]
  have htail_zero : (∑ j ∈ (range b).filter (fun j => ¬ Q j),
      |(fwdDiff h)^[5] conductorCurvatureProfile ((j : ℝ) * h)|) = 0 := by
    apply sum_eq_zero; intro j hj
    have hgt : 4 * Real.exp 8 < (j : ℝ) * h := not_le.mp (mem_filter.mp hj).2
    rw [fwdDiff_iter_zero_of_Icc hh.le fun x hx =>
      conductorCurvatureProfile_eq_zero_outside fun hs => (hgt.trans_le hx.1).not_ge hs.2, abs_zero]
  rw [htail_zero, add_zero]
  have heach : ∀ j ∈ (range b).filter Q,
      |(fwdDiff h)^[5] conductorCurvatureProfile ((j : ℝ) * h)| ≤ 5 * (KL : ℝ) * h ^ 5 := fun j _ => by
    simpa [mul_assoc] using
      fwdDiff_iter_lipschitz_bound 4 contDiff_four_conductorCurvatureProfile hKL hh ((j : ℝ) * h)
  calc _ ≤ ∑ _j ∈ (range b).filter Q, (5 * (KL : ℝ) * h ^ 5) := sum_le_sum heach
    _ = (((range b).filter Q).card : ℝ) * (5 * (KL : ℝ) * h ^ 5) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((4 * Real.exp 8 + 1) / h) * (5 * (KL : ℝ) * h ^ 5) :=
        mul_le_mul_of_nonneg_right (card_active_grid_le hh hh1 b) (by positivity)
    _ = K * h ^ 4 := by dsimp only [K]; field_simp [hh.ne']

#print axioms sum_fwdDiff_eight_dyadicSpline_le
#print axioms sum_fwdDiff_nine_conductorSplineIntegral_le
#print axioms sum_fwdDiff_five_conductorCurvatureProfile_le
#print axioms integral_mul_dyadicSpline_inv_sq
#print axioms hasDerivAt_conductor_profile
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
