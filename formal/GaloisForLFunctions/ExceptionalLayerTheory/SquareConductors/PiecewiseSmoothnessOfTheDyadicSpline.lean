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
open Finset Filter Topology MeasureTheory Set
open scoped NNReal Convolution
open GaloisForLFunctions.CountingHolography.Sections
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

/-- Even-integer knots of `(n + 1)`-fold uniform box convolution on `[-1, 1]`. -/
def upowKnots (m : ℕ) : Finset ℝ :=
  (Icc 0 (m + 1)).image fun i : ℕ => 2 * (i : ℝ) - ((m + 1 : ℕ) : ℝ)

/-- Multiplicative knots of `dyadicSpline` in `[exp(-8), 4 exp(8)]`. -/
def splineKnots : Finset ℝ :=
  ((upowKnots 7).image Real.exp) ∪ ((upowKnots 7).image fun u => Real.exp (u + Real.log 4))

theorem card_splineKnots_le : splineKnots.card ≤ 18 := by
  have h7 : (upowKnots 7).card ≤ 9 := by
    refine card_image_le.trans ?_
    simp
  calc splineKnots.card
      ≤ ((upowKnots 7).image Real.exp).card +
          ((upowKnots 7).image fun u => Real.exp (u + Real.log 4)).card := card_union_le _ _
    _ ≤ (upowKnots 7).card + (upowKnots 7).card := add_le_add card_image_le card_image_le
    _ ≤ 18 := by omega

theorem exp_neg_eight_mem_splineKnots : Real.exp (-8) ∈ splineKnots := by
  refine mem_union_left _ (mem_image.mpr ⟨-8, ?_, rfl⟩)
  refine mem_image.mpr ⟨0, mem_Icc.mpr ⟨le_rfl, by decide⟩, ?_⟩
  norm_num

theorem four_mul_exp_eight_mem_splineKnots : 4 * Real.exp 8 ∈ splineKnots := by
  refine mem_union_right _ (mem_image.mpr ⟨8, ?_, ?_⟩)
  · refine mem_image.mpr ⟨8, mem_Icc.mpr ⟨by decide, le_rfl⟩, ?_⟩
    norm_num
  · rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    ring

theorem dyadicSpline_eq_zero_outside {x : ℝ}
    (hx : x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8)) : dyadicSpline x = 0 := by
  have hx' : x ∉ Icc (Real.exp (-8)) (Real.exp (8 + Real.log 4)) := by
    intro h
    apply hx
    rwa [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), mul_comm] at h
  by_cases hp : 0 < x
  · simp only [dyadicSpline, if_pos hp, squarePrimeWeight_zero_outside hp hx',
      Complex.zero_re, mul_zero]
  · exact if_neg hp

/-! ### Global `C^{k,1}` regularity on compact positive support -/

private theorem abs_unif_one_le (t : ℝ) : |unif 1 t| ≤ 1 / 2 := by
  unfold unif
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem ht]; norm_num
  · rw [indicator_of_notMem ht]; norm_num

private theorem lipschitz_upow_one_one : LipschitzWith 1 (upow 1 1) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have h1 := unif_convolution_eq one_pos (integrable_unif 1) x
  have h2 := unif_convolution_eq one_pos (integrable_unif 1) y
  change |upow 1 1 x - upow 1 1 y| ≤ (1 : ℝ) * |x - y| at *
  simp only [upow] at *
  rw [h1, h2, Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  have hsub (c : ℝ) :
      |(∫ t in (0 : ℝ)..x + c, unif 1 t) - ∫ t in (0 : ℝ)..y + c, unif 1 t| ≤
        (1 / 2 : ℝ) * |x - y| := by
    rw [← intervalIntegral.integral_interval_sub_left
      (integrable_unif 1).intervalIntegrable (integrable_unif 1).intervalIntegrable]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := (1 / 2 : ℝ))
      (a := y + c) (b := x + c) (f := unif 1) fun t _ => by
        rw [Real.norm_eq_abs]; exact abs_unif_one_le t
    rw [Real.norm_eq_abs] at hb
    exact hb.trans_eq (by congr 1; ring)
  have heq : (1 / (2 * (1 : ℝ)) * ((∫ t in (0 : ℝ)..x + 1, unif 1 t) -
        ∫ t in (0 : ℝ)..x - 1, unif 1 t)) -
      (1 / (2 * (1 : ℝ)) * ((∫ t in (0 : ℝ)..y + 1, unif 1 t) -
        ∫ t in (0 : ℝ)..y - 1, unif 1 t)) =
      (1 / 2 : ℝ) * (((∫ t in (0 : ℝ)..x + 1, unif 1 t) - ∫ t in (0 : ℝ)..y + 1, unif 1 t) -
        ((∫ t in (0 : ℝ)..x - 1, unif 1 t) - ∫ t in (0 : ℝ)..y - 1, unif 1 t)) := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have htri := (abs_sub _ _).trans (add_le_add (hsub 1) (hsub (-1)))
  linarith

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
    simpa using ((hcont.integral_hasStrictDerivAt 0 (x + 1)).hasDerivAt.comp x
      ((hasDerivAt_id x).add_const 1))
  have hd2 : HasDerivAt (fun z => ∫ t in (0 : ℝ)..z - 1, upow 1 (k + 1) t)
      (upow 1 (k + 1) (x - 1)) x := by
    simpa using ((hcont.integral_hasStrictDerivAt 0 (x - 1)).hasDerivAt.comp x
      ((hasDerivAt_id x).sub_const 1))
  simpa [one_div] using (hd1.sub hd2).const_mul (1 / (2 * (1 : ℝ)))

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
      have hsub : ContDiff ℝ k fun z => upow 1 (k + 1) (z + 1) - upow 1 (k + 1) (z - 1) :=
        h1.sub h2
      rw [iteratedDeriv_const_mul x hsub.contDiffAt,
        iteratedDeriv_sub h1.contDiffAt h2.contDiffAt,
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
  ContDiff ℝ k f ∧ (∀ x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8), f x = 0) ∧
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv k f)

private theorem ckLip_deriv {k : ℕ} {f : ℝ → ℝ} (hf : CkLip (k + 1) f) : CkLip k (deriv f) := by
  obtain ⟨hc, hsupp, K, hL⟩ := hf
  refine ⟨(contDiff_succ_iff_deriv.mp hc).2.2, fun x hx => ?_, K, ?_⟩
  · have hopen : IsOpen (Icc (Real.exp (-8)) (4 * Real.exp 8))ᶜ := isClosed_Icc.isOpen_compl
    have hev : f =ᶠ[𝓝 x] 0 :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => hsupp z hz
    simpa using hev.deriv_eq
  · rwa [iteratedDeriv_succ']

private theorem lipschitz_of_collar {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hsupp : ∀ x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0)
    (hbound : ∀ x ∈ Icc (Real.exp (-8)) (4 * Real.exp 8), |g x| ≤ B)
    (hB : 0 ≤ B)
    (hin : ∀ x ∈ Icc (Real.exp (-9)) (5 * Real.exp 8),
      ∀ y ∈ Icc (Real.exp (-9)) (5 * Real.exp 8), |g x - g y| ≤ C * |x - y|) :
    ∃ K : ℝ≥0, LipschitzWith K g := by
  let δ := min (Real.exp (-8) - Real.exp (-9)) (5 * Real.exp 8 - 4 * Real.exp 8)
  have hδ : 0 < δ := by
    refine lt_min ?_ ?_
    · exact sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
    · have := Real.exp_pos 8; linarith
  let M := max C (B / δ)
  have hM : 0 ≤ M := le_trans hC (le_max_left _ _)
  refine ⟨⟨M, hM⟩, lipschitzWith_iff_dist_le_mul.mpr fun x y => ?_⟩
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_mk]
  by_cases hxJ : x ∈ Icc (Real.exp (-9)) (5 * Real.exp 8)
  · by_cases hyJ : y ∈ Icc (Real.exp (-9)) (5 * Real.exp 8)
    · exact (hin x hxJ y hyJ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    · by_cases hxS : x ∈ Icc (Real.exp (-8)) (4 * Real.exp 8)
      · have hyS : y ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hyS =>
          hyJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hyS.1,
            hyS.2.trans (by have := Real.exp_pos 8; linarith)⟩
        have hgap : δ ≤ |x - y| := by
          rcases not_and_or.mp hyJ with h1 | h2
          · rw [not_le] at h1
            have : δ ≤ x - y := (min_le_left _ _).trans (by linarith [hxS.1])
            exact this.trans (le_abs_self _)
          · rw [not_le] at h2
            have : δ ≤ y - x := (min_le_right _ _).trans (by linarith [hxS.2])
            exact this.trans (by rw [← abs_neg, neg_sub]; exact le_abs_self _)
        rw [hsupp y hyS, sub_zero]
        calc |g x| ≤ B := hbound x hxS
          _ = (B / δ) * δ := by field_simp [hδ.ne']
          _ ≤ M * |x - y| := mul_le_mul (le_max_right _ _) hgap hδ.le hM
      · have hyS : y ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hyS =>
          hyJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hyS.1,
            hyS.2.trans (by have := Real.exp_pos 8; linarith)⟩
        rw [hsupp x hxS, hsupp y hyS, sub_self, abs_zero]
        exact mul_nonneg hM (abs_nonneg _)
  · by_cases hyS : y ∈ Icc (Real.exp (-8)) (4 * Real.exp 8)
    · have hxS : x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hxS =>
        hxJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hxS.1,
          hxS.2.trans (by have := Real.exp_pos 8; linarith)⟩
      have hgap : δ ≤ |x - y| := by
        rcases not_and_or.mp hxJ with h1 | h2
        · rw [not_le] at h1
          have : δ ≤ y - x := (min_le_left _ _).trans (by linarith [hyS.1])
          exact this.trans (by rw [← abs_neg, neg_sub]; exact le_abs_self _)
        · rw [not_le] at h2
          have : δ ≤ x - y := (min_le_right _ _).trans (by linarith [hyS.2])
          exact this.trans (le_abs_self _)
      rw [hsupp x hxS, zero_sub, abs_neg]
      calc |g y| ≤ B := hbound y hyS
        _ = (B / δ) * δ := by field_simp [hδ.ne']
        _ ≤ M * |x - y| := mul_le_mul (le_max_right _ _) hgap hδ.le hM
    · have hxS : x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) := fun hxS =>
        hxJ ⟨(Real.exp_lt_exp.mpr (by norm_num)).le.trans hxS.1,
          hxS.2.trans (by have := Real.exp_pos 8; linarith)⟩
      rw [hsupp x hxS, hsupp y hyS, sub_self, abs_zero]
      exact mul_nonneg hM (abs_nonneg _)

private theorem ckLip_add {k : ℕ} {f g : ℝ → ℝ} (hf : CkLip k f) (hg : CkLip k g) :
    CkLip k (fun x => f x + g x) := by
  obtain ⟨hcf, hsf, Kf, hLf⟩ := hf
  obtain ⟨hcg, hsg, Kg, hLg⟩ := hg
  refine ⟨hcf.add hcg, fun x hx => by rw [hsf x hx, hsg x hx, add_zero], Kf + Kg, ?_⟩
  have heq : iteratedDeriv k (fun x => f x + g x) =
      fun x => iteratedDeriv k f x + iteratedDeriv k g x :=
    funext fun x => iteratedDeriv_add hcf.contDiffAt hcg.contDiffAt
  rw [heq]
  exact hLf.add hLg

private theorem ckLip_mul_smooth :
    ∀ {k : ℕ} {f φ : ℝ → ℝ}, CkLip k f → ContDiffOn ℝ ⊤ φ (Ioi 0) →
      CkLip k fun x => φ x * f x
  | 0, f, φ, ⟨hcf, hsf, Kf, hLf⟩, hφ => by
    have hcont : Continuous fun x => φ x * f x := by
      rw [continuous_iff_continuousAt]; intro x
      by_cases hx : 0 < x
      · exact ((hφ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hx)).mul hcf.continuous.continuousAt)
      · have hev : (fun z => φ z * f z) =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with z hz
          rw [hsf z fun h => hz.not_ge h.1, mul_zero]; rfl
        exact continuousAt_const.congr hev.symm
    refine ⟨contDiff_zero.mpr hcont, fun x hx => by rw [hsf x hx, mul_zero], ?_⟩
    simp only [iteratedDeriv_zero] at hLf ⊢
    let J := Icc (Real.exp (-9)) (5 * Real.exp 8)
    have hJsub : J ⊆ Ioi 0 := fun z hz => (Real.exp_pos (-9)).trans_le hz.1
    have hφ1 : ContDiffOn ℝ 1 φ (Ioi 0) := hφ.of_le le_top
    have hdφ : ContinuousOn (deriv φ) J := by
      have heq : EqOn (derivWithin φ (Ioi 0)) (deriv φ) (Ioi 0) :=
        fun z hz => (hφ1.differentiableOn le_rfl z hz).DifferentiableAt
          (isOpen_Ioi.mem_nhds hz) |>.derivWithin (isOpen_Ioi.uniqueDiffWithinAt hz)
      exact ((hφ1.continuousOn_derivWithin (isOpen_Ioi.uniqueDiffOn) le_rfl).congr heq).mono hJsub
    obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuousOn.mono hJsub)
    obtain ⟨Lφ, hLφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hdφ
    obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hcf.continuous.continuousOn
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ (Real.exp (-9)) ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-9 : ℝ) < 8); linarith [Real.exp_pos 8]⟩)
    have hLφ0 : 0 ≤ Lφ := (norm_nonneg _).trans (hLφ (Real.exp (-9)) ⟨le_rfl, by
      have := Real.exp_lt_exp.mpr (by norm_num : (-9 : ℝ) < 8); linarith [Real.exp_pos 8]⟩)
    have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf (Real.exp (-8)) ⟨le_rfl, by
      linarith [Real.exp_pos 8]⟩)
    have hφlip : ∀ x ∈ J, ∀ y ∈ J, |φ x - φ y| ≤ Lφ * |x - y| := fun x hx y hy => by
      have hd : ∀ z ∈ J, DifferentiableAt ℝ φ z := fun z hz =>
        (hφ1.differentiableOn le_rfl z (hJsub hz)).differentiableAt (isOpen_Ioi.mem_nhds (hJsub hz))
      have hmv := (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hd z hz) (fun z hz => hLφ z hz) hy hx
      simpa only [Real.norm_eq_abs] using hmv
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
      by_cases hxS : x ∈ Icc (Real.exp (-8)) (4 * Real.exp 8)
      · have hfx : |f x| ≤ Mf := by simpa [Real.norm_eq_abs] using hMf x hxS
        exact (mul_le_mul (hφlip x hx y hy) hfx (abs_nonneg _) (by positivity)).trans_eq (by ring)
      · rw [hsf x hxS, abs_zero, mul_zero]; positivity
    have h2 : |φ y * (f x - f y)| ≤ Mφ * Kf * |x - y| := by
      rw [abs_mul]
      have hfl : |f x - f y| ≤ Kf * |x - y| := by
        simpa [Real.dist_eq] using hLf.dist_le_mul x y
      exact (mul_le_mul (by simpa [Real.norm_eq_abs] using hMφ y hy) hfl
        (abs_nonneg _) hMφ0).trans_eq (by ring)
    exact (abs_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  | k + 1, f, φ, hf, hφ => by
    have hdφ : ContDiffOn ℝ ⊤ (deriv φ) (Ioi 0) := by
      have heq : EqOn (derivWithin φ (Ioi 0)) (deriv φ) (Ioi 0) :=
        fun z hz => ((hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ⊤)).differentiableOn le_rfl z hz)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz) |>.derivWithin (isOpen_Ioi.uniqueDiffWithinAt hz)
      exact (hφ.derivWithin isOpen_Ioi.uniqueDiffOn (m := ⊤) le_rfl).congr heq
    have hf_k : CkLip k f := by
      refine ⟨hf.1.of_le (by exact_mod_cast Nat.le_succ k), hf.2.1, ?_⟩
      have hdk : ContDiff ℝ 1 (iteratedDeriv k f) := by
        have := hf.1.iterate_deriv k 1
        simpa using this
      have hsupp_k : HasCompactSupport (iteratedDeriv k f) := by
        refine HasCompactSupport.intro isCompact_Icc fun x hx => ?_
        have hopen : IsOpen (Icc (Real.exp (-8)) (4 * Real.exp 8))ᶜ := isClosed_Icc.isOpen_compl
        have hev : f =ᶠ[𝓝 x] 0 :=
          Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => hf.2.1 z hz
        simpa using hev.iteratedDeriv_eq k
      exact ContDiff.lipschitzWith_of_hasCompactSupport hsupp_k hdk le_rfl
    have h1 := ckLip_mul_smooth hf_k hdφ
    have h2 := ckLip_mul_smooth (ckLip_deriv hf) hφ
    have hsum := ckLip_add h1 h2
    have hdiff : ∀ x, HasDerivAt (fun z => φ z * f z) (deriv φ x * f x + φ x * deriv f x) x := by
      intro x
      by_cases hx : 0 < x
      · have hφd : DifferentiableAt ℝ φ x :=
          ((hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ⊤)).differentiableOn le_rfl x hx)
            |>.differentiableAt (isOpen_Ioi.mem_nhds hx)
        have hfd : DifferentiableAt ℝ f x :=
          (hf.1.differentiable (by positivity)).differentiableAt
        exact hφd.hasDerivAt.mul hfd.hasDerivAt
      · have hxS : x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) :=
          fun h => hx ((Real.exp_pos (-8)).trans_le h.1)
        have hev : (fun z => φ z * f z) =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hx).trans_lt (Real.exp_pos (-8)))] with z hz
          rw [hf.2.1 z fun h => hz.not_ge h.1, mul_zero]; rfl
        have hdf0 : deriv f x = 0 := (ckLip_deriv hf).2.1 x hxS
        rw [hf.2.1 x hxS, hdf0, mul_zero, mul_zero, add_zero]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    have hder_eq : deriv (fun z => φ z * f z) = fun x => deriv φ x * f x + φ x * deriv f x :=
      funext fun x => (hdiff x).deriv
    refine ⟨contDiff_succ_iff_deriv.mpr ⟨fun x => (hdiff x).differentiableAt,
      by simp, hder_eq ▸ hsum.1⟩, fun x hx => by rw [hf.2.1 x hx, mul_zero], ?_⟩
    rw [iteratedDeriv_succ', hder_eq]
    exact hsum.2.2

private theorem ckLip_comp_log :
    ∀ {k : ℕ} {H : ℝ → ℝ}, ContDiff ℝ k H →
      (∀ u ∉ Icc (-8 : ℝ) (8 + Real.log 4), H u = 0) →
      (∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv k H)) →
      CkLip k fun x => if 0 < x then H (Real.log x) else 0
  | 0, H, hcH, hsuppH, ⟨KH, hLH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    have hsg : ∀ x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0 := by
      intro x hx
      dsimp [g]
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
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (Real.exp (-8)) ⟨le_rfl, by linarith [Real.exp_pos 8]⟩)
    refine lipschitz_of_collar (B := B) (C := KH * Real.exp 9) (by positivity) hsg
      (fun x hx => by simpa [Real.norm_eq_abs] using hB x hx) hB0 fun x hx y hy => ?_
    have hx0 : 0 < x := (Real.exp_pos (-9)).trans_le hx.1
    have hy0 : 0 < y := (Real.exp_pos (-9)).trans_le hy.1
    have hlog : |Real.log x - Real.log y| ≤ Real.exp 9 * |x - y| := by
      have hd : ∀ z ∈ Icc (Real.exp (-9)) (5 * Real.exp 8),
          HasDerivAt Real.log z⁻¹ z ∧ ‖z⁻¹‖ ≤ Real.exp 9 := fun z hz => by
        have hz0 : 0 < z := (Real.exp_pos (-9)).trans_le hz.1
        refine ⟨Real.hasDerivAt_log hz0.ne', ?_⟩
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hz0), Real.exp_neg] at hz ⊢
        exact inv_anti₀ (Real.exp_pos (-9)) hz.1 |>.trans_eq (by rw [Real.exp_neg, inv_inv])
      have hmv := (convex_Icc _ _).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hd z hz).1.differentiableAt)
        (fun z hz => by rw [(hd z hz).1.deriv]; exact (hd z hz).2) hy hx
      simpa only [Real.norm_eq_abs] using hmv
    dsimp [g]
    rw [if_pos hx0, if_pos hy0]
    have hHL : |H (Real.log x) - H (Real.log y)| ≤ KH * |Real.log x - Real.log y| := by
      simpa [Real.dist_eq] using hLH.dist_le_mul (Real.log x) (Real.log y)
    exact hHL.trans ((mul_le_mul_of_nonneg_left hlog KH.coe_nonneg).trans_eq (by ring))
  | k + 1, H, hcH, hsuppH, ⟨KH, hLH⟩ => by
    let g := fun x : ℝ => if 0 < x then H (Real.log x) else 0
    have hsuppH' : ∀ u ∉ Icc (-8 : ℝ) (8 + Real.log 4), deriv H u = 0 := by
      intro u hu
      have hopen : IsOpen (Icc (-8 : ℝ) (8 + Real.log 4))ᶜ := isClosed_Icc.isOpen_compl
      have hev : H =ᶠ[𝓝 u] 0 :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hu) fun z hz => hsuppH z hz
      simpa using hev.deriv_eq
    have ih := ckLip_comp_log (contDiff_succ_iff_deriv.mp hcH).2.2 hsuppH'
      ⟨KH, by rwa [iteratedDeriv_succ']⟩
    have hmul := ckLip_mul_smooth ih (contDiffOn_inv ℝ)
    have hsg : ∀ x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8), g x = 0 := by
      intro x hx
      dsimp [g]
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
          (hcH.differentiable (by positivity)).differentiableAt.hasDerivAt
        have hcomp := (hdH.comp x (Real.hasDerivAt_log hp.ne')).congr_of_eventuallyEq hev
        rw [if_pos hp, mul_comm]
        exact hcomp
      · have hev : g =ᶠ[𝓝 x] 0 := by
          filter_upwards [gt_mem_nhds ((le_of_not_gt hp).trans_lt (Real.exp_pos (-8)))] with z hz
          exact hsg z fun h => hz.not_ge h.1
        rw [if_neg hp, mul_zero]
        exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
    have hder_eq : deriv g = fun x => x⁻¹ * (if 0 < x then deriv H (Real.log x) else 0) :=
      funext fun x => (hdiff x).deriv
    refine ⟨contDiff_succ_iff_deriv.mpr ⟨fun x => (hdiff x).differentiableAt,
      by simp, hder_eq ▸ hmul.1⟩, hsg, ?_⟩
    rw [iteratedDeriv_succ', hder_eq]
    exact hmul.2.2

private theorem ckLip_six_dyadicSpline : CkLip 6 dyadicSpline := by
  obtain ⟨hcA, KA, hLA⟩ := lipschitz_iteratedDeriv_upow 6
  have hAeq : splineAutoCorr = upow 1 7 := funext splineAutoCorr_eq_eight_boxes
  have hcF : ContDiff ℝ 6 squareLogProfile := by
    unfold squareLogProfile
    rw [hAeq]
    exact (contDiff_const.mul hcA).sub (hcA.comp (contDiff_id.sub contDiff_const))
  have hsuppF : ∀ u ∉ Icc (-8 : ℝ) (8 + Real.log 4), squareLogProfile u = 0 := by
    intro u hu
    unfold squareLogProfile
    have h1 : 8 < |u| ∨ 8 < |u - Real.log 4| := by
      by_contra! hbad
      apply hu
      have ha := abs_le.mp hbad.1
      have hb := abs_le.mp hbad.2
      have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      exact ⟨ha.1, by linarith⟩
    have hz1 : splineAutoCorr u = 0 := by
      by_cases h : 8 < |u|
      · exact splineAutoCorr_zero_outside h
      · exfalso
        have ha := abs_le.mp (not_lt.mp h)
        have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
        apply hu
        refine ⟨ha.1, ?_⟩
        rcases h1 with h' | h'
        · exact absurd h' h
        · by_contra! hhi
          have : |u - Real.log 4| ≤ 8 := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
    have hz2 : splineAutoCorr (u - Real.log 4) = 0 := by
      by_cases h : 8 < |u - Real.log 4|
      · exact splineAutoCorr_zero_outside h
      · exfalso
        have hb := abs_le.mp (not_lt.mp h)
        have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
        apply hu
        refine ⟨?_, by linarith⟩
        by_contra! hlo
        have : 8 < |u - Real.log 4| := lt_abs.mpr (Or.inr (by linarith))
        exact h this
    rw [hz1, hz2]; ring
  have hLF : ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 6 squareLogProfile) := by
    have heq : iteratedDeriv 6 squareLogProfile =
        fun u => 2 * iteratedDeriv 6 (upow 1 7) u -
          iteratedDeriv 6 (upow 1 7) (u - Real.log 4) := by
      funext u
      unfold squareLogProfile
      rw [hAeq]
      have h1 : ContDiff ℝ 6 fun z => 2 * upow 1 7 z := contDiff_const.mul hcA
      have h2 : ContDiff ℝ 6 fun z => upow 1 7 (z - Real.log 4) :=
        hcA.comp (contDiff_id.sub contDiff_const)
      rw [iteratedDeriv_sub h1.contDiffAt h2.contDiffAt,
        iteratedDeriv_const_mul u hcA.contDiffAt, iteratedDeriv_comp_sub_const]
    rw [heq]
    have hL1 : LipschitzWith (2 * KA) (fun u => (2 : ℝ) * iteratedDeriv 6 (upow 1 7) u) := by
      simpa using hLA.const_mul 2
    have hL2 : LipschitzWith KA (fun u => iteratedDeriv 6 (upow 1 7) (u - Real.log 4)) := by
      simpa using hLA.comp ((LipschitzWith.id).sub (LipschitzWith.const (Real.log 4)))
        |>.weaken (by simp)
    refine ⟨2 * KA + KA, ?_⟩
    exact hL1.sub hL2
  have hlog := ckLip_comp_log hcF hsuppF hLF
  have hφ : ContDiffOn ℝ ⊤ (fun x : ℝ => 2 * x ^ (-(1 / 2 : ℝ))) (Ioi 0) := by
    refine contDiffOn_const.mul ?_
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne hx.ne').contDiffWithinAt
  have hmul := ckLip_mul_smooth hlog hφ
  have heq : (fun x : ℝ => (2 * x ^ (-(1 / 2 : ℝ))) *
      (if 0 < x then squareLogProfile (Real.log x) else 0)) = dyadicSpline := by
    funext x
    by_cases hx : 0 < x
    · simp only [if_pos hx, dyadicSpline, squarePrimeWeight, Complex.ofReal_re]
      rw [Real.rpow_def_of_pos hx]
      ring_nf
    · simp only [if_neg hx, dyadicSpline, mul_zero]
  rwa [heq] at hmul

theorem contDiff_six_dyadicSpline : ContDiff ℝ 6 dyadicSpline := ckLip_six_dyadicSpline.1

theorem lipschitz_iteratedDeriv_six_dyadicSpline :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 6 dyadicSpline) := ckLip_six_dyadicSpline.2.2

/-! ### Properties of `conductorSplineIntegral` and `conductorCurvatureProfile` -/

private theorem contDiff_div_sq_dyadicSpline : ContDiff ℝ 6 (fun t : ℝ => dyadicSpline t / t ^ 2) := by
  have hmul := ckLip_mul_smooth ckLip_six_dyadicSpline
    (contDiffOn_inv ℝ |>.comp (contDiffOn_pow 2) fun x (hx : 0 < x) => sq_pos_of_pos hx)
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
  apply intervalIntegral.integral_eq_zero_of_forall_eq_zero
  intro t ht
  have hlt : t < Real.exp (-8) ∨ t = Real.exp (-8) := by
    rcases le_total 0 u with h0 | h0
    · rw [uIoc_of_le h0] at ht
      exact lt_or_eq_of_le (ht.2.trans hu)
    · rw [uIoc_of_ge h0] at ht
      exact Or.inl (ht.2.trans_lt (Real.exp_pos (-8)))
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

theorem conductorSplineIntegral_linear_after {u : ℝ} (hu : 4 * Real.exp 8 ≤ u) :
    conductorSplineIntegral u =
      (u / 2) * ∫ t in (0 : ℝ)..(4 * Real.exp 8), dyadicSpline t / t ^ 2 := by
  unfold conductorSplineIntegral
  congr 1
  have h0 : (0 : ℝ) ≤ 4 * Real.exp 8 := by positivity
  rw [← intervalIntegral.integral_add_adjacent_intervals
    contDiff_div_sq_dyadicSpline.continuous.intervalIntegrable
    contDiff_div_sq_dyadicSpline.continuous.intervalIntegrable (b := 4 * Real.exp 8)]
  suffices hz : (∫ t in (4 * Real.exp 8)..u, dyadicSpline t / t ^ 2) = 0 by rw [hz, add_zero]
  rw [intervalIntegral.integral_of_le hu]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  rw [dyadicSpline_eq_zero_outside fun h => ht.1.not_ge h.2, zero_div]

private theorem iteratedDeriv_two_conductorSplineIntegral :
    iteratedDeriv 2 conductorSplineIntegral = fun u => (2 * u)⁻¹ * deriv dyadicSpline u := by
  let F := fun u : ℝ => ∫ t in (0 : ℝ)..u, dyadicSpline t / t ^ 2
  have hdF : ∀ u, HasDerivAt F (dyadicSpline u / u ^ 2) u := fun u =>
    (contDiff_div_sq_dyadicSpline.continuous.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd1 : ∀ u, HasDerivAt conductorSplineIntegral
      ((1 / 2 : ℝ) * F u + dyadicSpline u / (2 * u)) u := by
    intro u
    have h := ((hasDerivAt_id u).div_const 2).mul (hdF u)
    refine h.congr_deriv ?_
    by_cases hu : u = 0
    · subst u; simp [dyadicSpline]
    · field_simp [hu]; ring
  have hd1_eq : deriv conductorSplineIntegral =
      fun u => (1 / 2 : ℝ) * F u + dyadicSpline u / (2 * u) :=
    funext fun u => (hd1 u).deriv
  funext u
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd1_eq]
  by_cases hu : 0 < u
  · have hd2a : HasDerivAt (fun z => (1 / 2 : ℝ) * F z) ((1 / 2 : ℝ) * (dyadicSpline u / u ^ 2)) u :=
      (hdF u).const_mul (1 / 2)
    have hdd : DifferentiableAt ℝ dyadicSpline u :=
      (contDiff_six_dyadicSpline.differentiable (by decide)).differentiableAt
    have hd2b : HasDerivAt (fun z => dyadicSpline z / (2 * z))
        ((deriv dyadicSpline u * (2 * u) - dyadicSpline u * 2) / (2 * u) ^ 2) u := by
      simpa using hdd.hasDerivAt.div ((hasDerivAt_id u).const_mul 2) (by positivity)
    rw [(hd2a.add hd2b).deriv]
    field_simp [hu.ne']
    ring
  · have huS : u ∉ Icc (Real.exp (-8)) (4 * Real.exp 8) :=
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
      rw [hzF, dyadicSpline_eq_zero_outside fun h => hz.not_ge h.1]
      simp
    rw [(hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq hev |>.deriv,
      (ckLip_deriv ckLip_six_dyadicSpline).2.1 u huS, mul_zero]

theorem lipschitz_iteratedDeriv_seven_conductorSplineIntegral :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 7 conductorSplineIntegral) := by
  have h2 : CkLip 5 (fun u => (2 * u)⁻¹ * deriv dyadicSpline u) :=
    ckLip_mul_smooth (ckLip_deriv ckLip_six_dyadicSpline)
      ((contDiffOn_id.const_mul 2).inv fun x (hx : 0 < x) => by positivity)
  have heq : iteratedDeriv 7 conductorSplineIntegral =
      iteratedDeriv 5 (iteratedDeriv 2 conductorSplineIntegral) := by
    simpa using (iteratedDeriv_add 5 2 conductorSplineIntegral).symm
  rw [heq, iteratedDeriv_two_conductorSplineIntegral]
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
    have hdH : ∀ t ∈ uIcc a d, HasDerivAt H (t * dyadicSpline (z / t ^ 2)) t := by
      intro t ht
      rw [uIcc_of_le had] at ht
      have ht0 : 0 < t := ha.trans_le ht.1
      have hquot : HasDerivAt (fun s : ℝ => z / s ^ 2) (-(2 * z) / t ^ 3) t := by
        have h := (hasDerivAt_const t z).div ((hasDerivAt_id t).pow 2) (sq_pos_of_pos ht0).ne'
        refine h.congr_deriv ?_
        field_simp [ht0.ne']; ring
      have hcomp := ((hdF (z / t ^ 2)).comp t hquot).const_mul (-(z / 2))
      refine hcomp.congr_deriv ?_
      field_simp [ht0.ne', hzpos.ne']
      ring
    have hint : IntervalIntegrable (fun t : ℝ => t * dyadicSpline (z / t ^ 2)) volume a d := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le had]
      intro t ht
      have ht0 : 0 < t := ha.trans_le ht.1
      exact continuousAt_id.mul (contDiff_six_dyadicSpline.continuous.continuousAt.comp
        (continuousAt_const.div (continuousAt_id.pow 2) (sq_pos_of_pos ht0).ne'))
          |>.continuousWithinAt
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hdH hint]
    have hHeq (t : ℝ) (ht : 0 < t) : H t = -t ^ 2 * conductorSplineIntegral (z / t ^ 2) := by
      dsimp [H, conductorSplineIntegral, F]
      field_simp [ht.ne']
      ring
    rw [hHeq d (ha.trans_le had), hHeq a ha]
    ring

private theorem ckLip_four_conductorCurvatureProfile : CkLip 4 conductorCurvatureProfile := by
  have hd1 : CkLip 4 (deriv dyadicSpline) := by
    have h5 := ckLip_deriv ckLip_six_dyadicSpline
    have hdk : ContDiff ℝ 1 (iteratedDeriv 4 (deriv dyadicSpline)) := by
      simpa using h5.1.iterate_deriv 4 1
    have hsupp4 : HasCompactSupport (iteratedDeriv 4 (deriv dyadicSpline)) := by
      refine HasCompactSupport.intro isCompact_Icc fun x hx => ?_
      have hopen : IsOpen (Icc (Real.exp (-8)) (4 * Real.exp 8))ᶜ := isClosed_Icc.isOpen_compl
      have hev : deriv dyadicSpline =ᶠ[𝓝 x] 0 :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => h5.2.1 z hz
      simpa using hev.iteratedDeriv_eq 4
    exact ⟨h5.1.of_le (by norm_num), h5.2.1,
      ContDiff.lipschitzWith_of_hasCompactSupport hsupp4 hdk le_rfl⟩
  have hd2 : CkLip 4 (iteratedDeriv 2 dyadicSpline) := by
    have h := ckLip_deriv (ckLip_deriv ckLip_six_dyadicSpline)
    rwa [show deriv (deriv dyadicSpline) = iteratedDeriv 2 dyadicSpline by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at h
  have ht1 := ckLip_mul_smooth hd1 (contDiffOn_const.mul contDiffOn_id)
  have ht2 := ckLip_mul_smooth hd2 (contDiffOn_const.mul (contDiffOn_pow 2))
  exact ckLip_add ht1 ht2

theorem contDiff_four_conductorCurvatureProfile : ContDiff ℝ 4 conductorCurvatureProfile :=
  ckLip_four_conductorCurvatureProfile.1

theorem conductorCurvatureProfile_eq_zero_outside {x : ℝ}
    (hx : x ∉ Icc (Real.exp (-8)) (4 * Real.exp 8)) : conductorCurvatureProfile x = 0 :=
  ckLip_four_conductorCurvatureProfile.2.1 x hx

theorem lipschitz_iteratedDeriv_four_conductorCurvatureProfile :
    ∃ K : ℝ≥0, LipschitzWith K (iteratedDeriv 4 conductorCurvatureProfile) :=
  ckLip_four_conductorCurvatureProfile.2.2

/-- Second conductor derivative `∂_t² [t · dyadicSpline(z / t²)] = Θ₂(z / t²) / t` for `t > 0`. -/
theorem hasDerivAt_conductor_profile (z : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffOn ℝ 2 (fun s : ℝ => s * dyadicSpline (z / s ^ 2)) (Ioi 0) ∧
      iteratedDeriv 2 (fun s : ℝ => s * dyadicSpline (z / s ^ 2)) t =
        conductorCurvatureProfile (z / t ^ 2) / t := by
  let g := fun s : ℝ => s * dyadicSpline (z / s ^ 2)
  have hcd : ContDiffOn ℝ 2 g (Ioi 0) := by
    refine contDiffOn_id.mul ?_
    exact (contDiff_six_dyadicSpline.of_le (by norm_num)).comp_contDiffOn
      (contDiffOn_const.div (contDiffOn_pow 2) fun s (hs : 0 < s) => (sq_pos_of_pos hs).ne')
  refine ⟨hcd, ?_⟩
  have hd1 : ∀ s > (0 : ℝ), HasDerivAt g
      (dyadicSpline (z / s ^ 2) - 2 * z / s ^ 2 * deriv dyadicSpline (z / s ^ 2)) s := by
    intro s hs
    have hq : HasDerivAt (fun r : ℝ => z / r ^ 2) (-(2 * z) / s ^ 3) s := by
      refine ((hasDerivAt_const s z).div ((hasDerivAt_id s).pow 2)
        (sq_pos_of_pos hs).ne').congr_deriv ?_
      field_simp [hs.ne']; ring
    have hdΦ : HasDerivAt dyadicSpline (deriv dyadicSpline (z / s ^ 2)) (z / s ^ 2) :=
      (contDiff_six_dyadicSpline.differentiable (by decide)).differentiableAt.hasDerivAt
    refine ((hasDerivAt_id s).mul (hdΦ.comp s hq)).congr_deriv ?_
    field_simp [hs.ne']; ring
  have hev1 : deriv g =ᶠ[𝓝 t]
      fun s => dyadicSpline (z / s ^ 2) - 2 * z / s ^ 2 * deriv dyadicSpline (z / s ^ 2) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact (hd1 s hs).deriv
  have hq : HasDerivAt (fun r : ℝ => z / r ^ 2) (-(2 * z) / t ^ 3) t := by
    refine ((hasDerivAt_const t z).div ((hasDerivAt_id t).pow 2)
      (sq_pos_of_pos ht).ne').congr_deriv ?_
    field_simp [ht.ne']; ring
  have hdΦ : HasDerivAt dyadicSpline (deriv dyadicSpline (z / t ^ 2)) (z / t ^ 2) :=
    (contDiff_six_dyadicSpline.differentiable (by decide)).differentiableAt.hasDerivAt
  have hdΦ' : HasDerivAt (deriv dyadicSpline) (iteratedDeriv 2 dyadicSpline (z / t ^ 2)) (z / t ^ 2) := by
    have h5 := (contDiff_succ_iff_deriv.mp contDiff_six_dyadicSpline).2.2
    have hd := (h5.differentiable (by decide)).differentiableAt.hasDerivAt
    rwa [show deriv (deriv dyadicSpline) = iteratedDeriv 2 dyadicSpline by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]] at hd
  have hfactor : HasDerivAt (fun r : ℝ => 2 * z / r ^ 2) (-(4 * z) / t ^ 3) t := by
    refine ((hasDerivAt_const t (2 * z)).div ((hasDerivAt_id t).pow 2)
      (sq_pos_of_pos ht).ne').congr_deriv ?_
    field_simp [ht.ne']; ring
  have hd2 := ((hdΦ.comp t hq).sub (hfactor.mul (hdΦ'.comp t hq))).congr_of_eventuallyEq hev1
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd2.deriv]
  unfold conductorCurvatureProfile
  field_simp [ht.ne']
  ring

/-! ### Off-knot `C^∞` regularity and discrete difference-sum bounds -/

private theorem upowKnots_shift {m : ℕ} {x : ℝ} (hx : x ∉ upowKnots (m + 1)) :
    x + 1 ∉ upowKnots m ∧ x - 1 ∉ upowKnots m := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := mem_image.mp h
    apply hx
    refine mem_image.mpr ⟨i, mem_Icc.mpr ⟨(mem_Icc.mp hi).1, by omega⟩, ?_⟩
    push_cast at heq ⊢; linarith
  · intro h
    obtain ⟨i, hi, heq⟩ := mem_image.mp h
    apply hx
    refine mem_image.mpr ⟨i + 1, mem_Icc.mpr ⟨by omega, by have := (mem_Icc.mp hi).2; omega⟩, ?_⟩
    push_cast at heq ⊢; linarith

private theorem smooth_bounded_upow :
    ∀ m : ℕ, ∀ x ∉ upowKnots m,
      ContDiffAt ℝ ⊤ (upow 1 m) x ∧ ∀ r : ℕ, |iteratedDeriv r (upow 1 m) x| ≤ 1 / 2
  | 0 => fun x hx => by
    have hx1 : x ≠ -1 ∧ x ≠ 1 := by
      refine ⟨fun h => hx (mem_image.mpr ⟨0, mem_Icc.mpr ⟨le_rfl, by decide⟩, by norm_num [h]⟩),
        fun h => hx (mem_image.mpr ⟨1, mem_Icc.mpr ⟨by decide, le_rfl⟩, by norm_num [h]⟩)⟩
    by_cases hin : x ∈ Ioo (-1 : ℝ) 1
    · have hev : upow 1 0 =ᶠ[𝓝 x] fun _ => (1 / 2 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hin] with z hz
        simp [upow, unif, indicator_of_mem ⟨hz.1.le, hz.2.le⟩]
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, fun r => ?_⟩
      rw [hev.iteratedDeriv_eq r]
      rcases r with _ | r
      · norm_num
      · rw [iteratedDeriv_const]; norm_num
    · have hout : x ∈ (Icc (-1 : ℝ) 1)ᶜ := by
        intro hmem
        rcases eq_or_lt_of_le hmem.1 with h | h1
        · exact hx1.1 h.symm
        · rcases eq_or_lt_of_le hmem.2 with h | h2
          · exact hx1.2 h
          · exact hin ⟨h1, h2⟩
      have hev : upow 1 0 =ᶠ[𝓝 x] 0 := by
        filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with z hz
        simp [upow, unif, indicator_of_notMem hz]
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, fun r => ?_⟩
      rw [hev.iteratedDeriv_eq r]
      rcases r with _ | r <;> simp
  | m + 1 => fun x hx => by
    obtain ⟨hx1, hx2⟩ := upowKnots_shift hx
    obtain ⟨hc1, hb1⟩ := smooth_bounded_upow m (x + 1) hx1
    obtain ⟨hc2, hb2⟩ := smooth_bounded_upow m (x - 1) hx2
    have hopen : IsOpen (upowKnots m : Set ℝ)ᶜ := (upowKnots m).finite_toSet.isClosed.isOpen_compl
    have hd_nhds : ∀ᶠ z in 𝓝 x,
        HasDerivAt (upow 1 (m + 1)) ((1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1))) z := by
      rcases m with _ | m'
      · have h1 : ∀ᶠ z in 𝓝 x, upow 1 0 (z + 1) = upow 1 0 (x + 1) ∧
            upow 1 0 (z - 1) = upow 1 0 (x - 1) := by
          have ha : ContinuousAt (fun z => z + 1) x := continuousAt_id.add continuousAt_const
          have hb : ContinuousAt (fun z => z - 1) x := continuousAt_id.sub continuousAt_const
          have hloc (y : ℝ) (hy : y ∉ upowKnots 0) : ∀ᶠ w in 𝓝 y, upow 1 0 w = upow 1 0 y := by
            have hy1 : y ≠ -1 ∧ y ≠ 1 :=
              ⟨fun h => hy (mem_image.mpr ⟨0, mem_Icc.mpr ⟨le_rfl, by decide⟩, by norm_num [h]⟩),
               fun h => hy (mem_image.mpr ⟨1, mem_Icc.mpr ⟨by decide, le_rfl⟩, by norm_num [h]⟩)⟩
            by_cases hin : y ∈ Ioo (-1 : ℝ) 1
            · filter_upwards [isOpen_Ioo.mem_nhds hin] with w hw
              simp [upow, unif, indicator_of_mem ⟨hw.1.le, hw.2.le⟩,
                indicator_of_mem ⟨hin.1.le, hin.2.le⟩]
            · have hout : y ∈ (Icc (-1 : ℝ) 1)ᶜ := fun hm =>
                hin ⟨lt_of_le_of_ne hm.1 hy1.1.symm, lt_of_le_of_ne hm.2 hy1.2⟩
              filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hout] with w hw
              simp [upow, unif, indicator_of_notMem hw, indicator_of_notMem hout]
          exact (ha.eventually (hloc _ hx1)).and (hb.eventually (hloc _ hx2))
        obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h1
        filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
        have hconv := fun w => unif_convolution_eq one_pos (integrable_unif 1) w
        have hev_p : (fun w => ∫ t in (0 : ℝ)..w + 1, unif 1 t) =ᶠ[𝓝 z]
            fun w => (∫ t in (0 : ℝ)..x + 1, unif 1 t) +
              ((w + 1) - (x + 1)) * upow 1 0 (x + 1) := by
          filter_upwards [Metric.ball_mem_nhds x hδ] with w hw
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (integrable_unif 1).intervalIntegrable (integrable_unif 1).intervalIntegrable
            (b := x + 1)]
          congr 1
          have hconst : EqOn (unif 1) (fun _ => upow 1 0 (x + 1)) (uIoc (x + 1) (w + 1)) := by
            intro t ht
            have htw : dist (t - 1) x < δ := by
              rw [Real.dist_eq] at hw ⊢
              rcases le_total (x + 1) (w + 1) with hle | hle
              · rw [uIoc_of_le hle] at ht
                rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
              · rw [uIoc_of_ge hle] at ht
                rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
            simpa [upow] using (hball htw).1
          rw [intervalIntegral.integral_congr_ae
            (ae_of_all _ fun t ht => hconst ht), intervalIntegral.integral_const, smul_eq_mul]
        have hev_m : (fun w => ∫ t in (0 : ℝ)..w - 1, unif 1 t) =ᶠ[𝓝 z]
            fun w => (∫ t in (0 : ℝ)..x - 1, unif 1 t) +
              ((w - 1) - (x - 1)) * upow 1 0 (x - 1) := by
          filter_upwards [Metric.ball_mem_nhds x hδ] with w hw
          rw [← intervalIntegral.integral_add_adjacent_intervals
            (integrable_unif 1).intervalIntegrable (integrable_unif 1).intervalIntegrable
            (b := x - 1)]
          congr 1
          have hconst : EqOn (unif 1) (fun _ => upow 1 0 (x - 1)) (uIoc (x - 1) (w - 1)) := by
            intro t ht
            have htw : dist (t + 1) x < δ := by
              rw [Real.dist_eq] at hw ⊢
              rcases le_total (x - 1) (w - 1) with hle | hle
              · rw [uIoc_of_le hle] at ht
                rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
              · rw [uIoc_of_ge hle] at ht
                rw [abs_lt] at hw ⊢; constructor <;> linarith [ht.1, ht.2]
            simpa [upow] using (hball htw).2
          rw [intervalIntegral.integral_congr_ae
            (ae_of_all _ fun t ht => hconst ht), intervalIntegral.integral_const, smul_eq_mul]
        have hev_u : upow 1 1 =ᶠ[𝓝 z] fun w => (1 / 2 : ℝ) *
            (((∫ t in (0 : ℝ)..x + 1, unif 1 t) + ((w + 1) - (x + 1)) * upow 1 0 (x + 1)) -
             ((∫ t in (0 : ℝ)..x - 1, unif 1 t) + ((w - 1) - (x - 1)) * upow 1 0 (x - 1))) := by
          filter_upwards [hev_p, hev_m] with w hp hm
          change (unif 1 ⋆ unif 1) w = _
          rw [hconv w, hp, hm]; ring
        have hlin : HasDerivAt (fun w => (1 / 2 : ℝ) *
            (((∫ t in (0 : ℝ)..x + 1, unif 1 t) + ((w + 1) - (x + 1)) * upow 1 0 (x + 1)) -
             ((∫ t in (0 : ℝ)..x - 1, unif 1 t) + ((w - 1) - (x - 1)) * upow 1 0 (x - 1))))
            ((1 / 2 : ℝ) * (upow 1 0 (x + 1) - upow 1 0 (x - 1))) z := by
          have hd_p : HasDerivAt (fun w => (∫ t in (0 : ℝ)..x + 1, unif 1 t) +
              ((w + 1) - (x + 1)) * upow 1 0 (x + 1)) (upow 1 0 (x + 1)) z := by
            simpa using (((hasDerivAt_id z).add_const 1).sub_const (x + 1)).mul_const
              (upow 1 0 (x + 1)) |>.const_add _
          have hd_m : HasDerivAt (fun w => (∫ t in (0 : ℝ)..x - 1, unif 1 t) +
              ((w - 1) - (x - 1)) * upow 1 0 (x - 1)) (upow 1 0 (x - 1)) z := by
            simpa using (((hasDerivAt_id z).sub_const 1).sub_const (x - 1)).mul_const
              (upow 1 0 (x - 1)) |>.const_add _
          exact (hd_p.sub hd_m).const_mul (1 / 2)
        rw [(hball hz).1, (hball hz).2]
        exact hlin.congr_of_eventuallyEq hev_u
      · exact Eventually.of_forall fun z => hasDerivAt_upow_succ (Nat.succ_pos m') z
    have hder_ev : deriv (upow 1 (m + 1)) =ᶠ[𝓝 x]
        fun z => (1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1)) :=
      hd_nhds.mono fun z hz => hz.deriv
    have hc_rhs : ContDiffAt ℝ ⊤
        (fun z => (1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1))) x :=
      contDiffAt_const.mul ((hc1.comp x (contDiffAt_id.add contDiffAt_const)).sub
        (hc2.comp x (contDiffAt_id.sub contDiffAt_const)))
    have hc_top : ContDiffAt ℝ ⊤ (upow 1 (m + 1)) x := by
      rw [contDiffAt_top]
      intro n
      rcases n with _ | n
      · exact contDiffAt_zero.mpr ⟨_, hd_nhds.mono fun z hz => hz.continuousAt⟩
      · rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
        refine ⟨fun z => ContinuousLinearMap.smulRight 1
            ((1 / 2 : ℝ) * (upow 1 m (z + 1) - upow 1 m (z - 1))), ?_, ?_⟩
        · exact hd_nhds.mono fun z hz => hz.hasFDerivAt
        · have hclm : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) =
              (ContinuousLinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm.toContinuousLinearMap := rfl
          exact ContinuousLinearMap.contDiffAt _ |>.comp x (hc_rhs.of_le le_top)
    refine ⟨hc_top, fun r => ?_⟩
    rcases r with _ | r
    · simp only [iteratedDeriv_zero]
      have hconv := unif_convolution_eq one_pos (integrable_upow 1 m) x
      change |(unif 1 ⋆ upow 1 m) x| ≤ 1 / 2
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      have hb_ae : ∀ᵐ t ∂volume, |unif 1 t * upow 1 m (x - t)| ≤ unif 1 t * (1 / 2) := by
        have hfin : ((upowKnots m).image fun u => x - u).Finite := Finset.finite_toSet _
        refine (hfin.measurableSet.measure_zero ?_).mono fun t ht => ?_
        · exact Set.Finite.measure_zero hfin volume
        · rw [abs_mul, abs_of_nonneg (unif_nonneg one_pos t)]
          refine mul_le_mul_of_nonneg_left ?_ (unif_nonneg one_pos t)
          have hxk : x - t ∉ upowKnots m := fun hmem =>
            ht (mem_coe.mpr (mem_image.mpr ⟨x - t, hmem, by ring⟩))
          exact (smooth_bounded_upow m (x - t) hxk).2 0
      have hint1 : Integrable (fun t => unif 1 t * upow 1 m (x - t)) := by
        refine Integrable.mono' ((integrable_unif 1).mul_const (1 / 2)) ?_ ?_
        · exact (integrable_unif 1).aestronglyMeasurable.mul
            ((integrable_upow 1 m).comp_sub_left x).aestronglyMeasurable
        · exact hb_ae.mono fun t ht => by rwa [Real.norm_eq_abs]
      calc |∫ t, unif 1 t * upow 1 m (x - t)|
          ≤ ∫ t, |unif 1 t * upow 1 m (x - t)| := abs_integral_le_integral_abs
        _ ≤ ∫ t, unif 1 t * (1 / 2) :=
            integral_mono_ae hint1.abs ((integrable_unif 1).mul_const (1 / 2)) hb_ae
        _ = (∫ t, unif 1 t) * (1 / 2) := integral_mul_const _ _
        _ = 1 / 2 := by rw [integral_unif one_pos, one_mul]
    · rw [iteratedDeriv_succ', hder_ev.iteratedDeriv_eq r]
      have h1c : ContDiffAt ℝ r (fun z => upow 1 m (z + 1)) x :=
        (hc1.of_le le_top).comp x (contDiffAt_id.add contDiffAt_const)
      have h2c : ContDiffAt ℝ r (fun z => upow 1 m (z - 1)) x :=
        (hc2.of_le le_top).comp x (contDiffAt_id.sub contDiffAt_const)
      have hsub : ContDiffAt ℝ r (fun z => upow 1 m (z + 1) - upow 1 m (z - 1)) x := h1c.sub h2c
      rw [iteratedDeriv_const_mul x hsub, iteratedDeriv_sub h1c h2c,
        iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const,
        abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have htri := (abs_sub _ _).trans (add_le_add (hb1 r) (hb2 r))
      linarith

private def OffKnotBounded (k : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∉ splineKnots, ContDiffAt ℝ k f x) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (Real.exp (-8)) (4 * Real.exp 8),
      x ∉ splineKnots → ∀ r ≤ k, |iteratedDeriv r f x| ≤ M

private theorem offKnot_add {k : ℕ} {f g : ℝ → ℝ}
    (hf : OffKnotBounded k f) (hg : OffKnotBounded k g) :
    OffKnotBounded k (fun x => f x + g x) := by
  obtain ⟨hcf, Mf, hMf0, hbf⟩ := hf
  obtain ⟨hcg, Mg, hMg0, hbg⟩ := hg
  refine ⟨fun x hx => (hcf x hx).add (hcg x hx), Mf + Mg, add_nonneg hMf0 hMg0,
    fun x hxS hxk r hr => ?_⟩
  rw [iteratedDeriv_add ((hcf x hxk).of_le (by exact_mod_cast hr))
    ((hcg x hxk).of_le (by exact_mod_cast hr))]
  exact (abs_add_le _ _).trans (add_le_add (hbf x hxS hxk r hr) (hbg x hxS hxk r hr))

private theorem offKnot_deriv {k : ℕ} {f : ℝ → ℝ} (hf : OffKnotBounded (k + 1) f) :
    OffKnotBounded k (deriv f) := by
  obtain ⟨hcf, M, hM0, hbf⟩ := hf
  refine ⟨fun x hx => ?_, M, hM0, fun x hxS hxk r hr => ?_⟩
  · have h := hcf x hx
    rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt] at h
    obtain ⟨f', hf', hcf'⟩ := h
    have hev : deriv f =ᶠ[𝓝 x] fun z => f' z 1 := hf'.mono fun z hz => hz.hasDerivAt.deriv
    exact ((ContinuousLinearMap.apply ℝ ℝ 1).contDiff.contDiffAt.comp x hcf').congr_of_eventuallyEq hev
  · rw [iteratedDeriv_succ']
    exact hbf x hxS hxk (r + 1) (Nat.succ_le_succ hr)

private theorem offKnot_mul_smooth :
    ∀ {k : ℕ} {f φ : ℝ → ℝ}, OffKnotBounded k f → ContDiffOn ℝ ⊤ φ (Ioi 0) →
      OffKnotBounded k (fun x => φ x * f x)
  | 0, f, φ, ⟨hcf, Mf, hMf0, hbf⟩, hφ => by
    have hsub : Icc (Real.exp (-8)) (4 * Real.exp 8) ⊆ Ioi 0 :=
      fun z hz => (Real.exp_pos (-8)).trans_le hz.1
    obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hφ.continuousOn.mono hsub)
    have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans
      (hMφ (Real.exp (-8)) ⟨le_rfl, by linarith [Real.exp_pos 8]⟩)
    refine ⟨fun x hx => ?_, Mφ * Mf, mul_nonneg hMφ0 hMf0, fun x hxS hxk r hr => ?_⟩
    · simp only [Nat.cast_zero, contDiffAt_zero] at hcf ⊢
      -- WAIT: at x ≤ 0, is φ continuous?!
      sorry
  | k + 1, f, φ, hf, hφ => sorry
