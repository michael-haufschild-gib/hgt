import GaloisForLFunctions.RHTower.RelaxedHerglotzProducerFloor
import GaloisForLFunctions.RHTower.ZetaConvexityBound

/-!
# Trivial weights become a Herglotz producer after a subconvex archimedean boost

Take the weights `lam(n) = 1` for every `n ≥ 2`, whose Dirichlet series is `ζ(s) − 1`, and boost the
archimedean function `½ψ(s/2) − ½ log π + 1/s + 1/(s − 1)` (`archPart`) by `c·(s + ½)^θ`.

**Theorem** (`exists_herglotz_trivialWeights_boosted`).  For every `¼ < θ < 1` there is `c > 0` such
that `archPart(s) + c(s + ½)^θ − (ζ(s) − 1)` has a holomorphic continuation with nonnegative real
part to `Re s > ½`.  So the trivial weights are a Herglotz producer, at the critical abscissa ½,
for the archimedean density boosted by `c|t|^θ`.

Proof.
* The poles at `s = 1` cancel. `ζ(s) − 1/(s − 1)` tends to `γ` (`tendsto_riemannZeta_sub_one_div`),
  so the removable-singularity theorem gives holomorphy at `1`.
* `|ζ(s) − 1/(s − 1)| ≤ K(2 + |t|)^{θ₀}` on `Re s > ½`, with `θ₀ = ¼ + η/2 < θ`. This uses the
  convexity bound for `|t| ≥ 8`, the Dirichlet series beyond `Re s = 1 + η`, and compactness in
  between.
* `Re ψ(s/2)` is bounded below on `Re s > ½`: the digamma asymptotic for `|s| ≥ 4`, compactness
  otherwise.
* `Re (s + ½)^θ ≥ cos(θπ/2)|s + ½|^θ ≥ cos(θπ/2)(2 + |t|)^{θ₀}/3`, which absorbs both bounds once
  `c` is large.

Reading: the weights `1` (all integers) carry the pole at `s = 1` but have the multiplicative large
values of `ζ`. An archimedean excess of subconvexity size pays for them. The true weights `Λ` would
need no excess, which is RH (`riemannHypothesis_iff_exists_herglotzProducer`). The exponent `¼` is
the convexity exponent. Lindelöf would allow every `θ > 0`.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace RHTower.RelaxedHerglotz

/-! ### Complex powers with positive real base -/

/-- `Re (z^θ) = |z|^θ cos(θ arg z)`. -/
theorem re_cpow_ofReal_eq {z : ℂ} (hz : z ≠ 0) (θ : ℝ) :
    (z ^ (θ : ℂ)).re = ‖z‖ ^ θ * Real.cos (θ * z.arg) := by
  rw [cpow_def_of_ne_zero hz, exp_re]
  have h1 : (log z * (θ : ℂ)).re = Real.log ‖z‖ * θ := by
    simp [Complex.mul_re, log_re]
  have h2 : (log z * (θ : ℂ)).im = θ * z.arg := by
    simp [Complex.mul_im, log_im]; ring
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]

/-- For `Re z > 0` and `0 ≤ θ ≤ 1`: `Re (z^θ) ≥ cos(θπ/2)|z|^θ`. -/
theorem cos_mul_rpow_le_re_cpow {z : ℂ} (hz : 0 < z.re) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.cos (θ * (Real.pi / 2)) * ‖z‖ ^ θ ≤ (z ^ (θ : ℂ)).re := by
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz
  rw [re_cpow_ofReal_eq hz0, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg _) _)
  have harg : |z.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [← Real.cos_abs (θ * z.arg)]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by nlinarith [Real.pi_pos]) ?_
  rw [abs_mul, abs_of_nonneg hθ0]
  exact mul_le_mul_of_nonneg_left harg.le hθ0

/-! ### The digamma term is bounded below -/

theorem exists_lower_bound_re_digamma_half :
    ∃ K : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → -K ≤ (Complex.digamma (s / 2)).re := by
  set D : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re} ∩ closedBall 0 4 with hD
  have hDc : IsCompact D :=
    (isCompact_closedBall 0 4).inter_left (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (fun s : ℂ => Complex.digamma (s / 2)) D := fun s hs =>
    ((differentiableAt_digamma_of_re_pos (by
      have := hs.1; simp only [mem_setOf_eq] at this; simp; linarith)).comp s
      ((differentiableAt_id).div_const 2)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hDc.exists_bound_of_continuousOn hcont
  refine ⟨max M 1, fun s hs => ?_⟩
  by_cases h4 : ‖s‖ ≤ 4
  · have := hM s ⟨hs, by simpa [mem_closedBall, dist_zero_right] using h4⟩
    have hre := Complex.abs_re_le_norm (Complex.digamma (s / 2))
    have := le_max_left M 1
    have := neg_abs_le (Complex.digamma (s / 2)).re
    linarith
  · push Not at h4
    have hre0 : 0 < s.re := by linarith
    have h := abs_re_digamma_half_sub_log_le hre0 h4.le
    have hlog : Real.log 4 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) h4.le
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hl2 := Real.log_two_gt_d9
    have hsre : s.re ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s)
    have hfrac : (20 + s.re) / ‖s‖ ^ 2 ≤ 3 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have := (abs_le.mp h).1
    have := le_max_right M 1
    linarith

/-! ### The zeta term -/

/-- `ζ(s) − 1/(s − 1)` extended by `γ` at `s = 1`. -/
def zetaRegular (s : ℂ) : ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1
    (Real.eulerMascheroniConstant : ℂ) s

theorem zetaRegular_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaRegular s = riemannZeta s - 1 / (s - 1) := by
  simp [zetaRegular, Function.update_of_ne hs]

theorem continuous_zetaRegular : Continuous zetaRegular := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : s = 1
  · subst hs
    exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div
  · have hev : (fun s : ℂ => riemannZeta s - 1 / (s - 1)) =ᶠ[𝓝 s] zetaRegular :=
      Filter.eventually_of_mem (isOpen_ne.mem_nhds hs) fun w hw => (zetaRegular_of_ne hw).symm
    refine ContinuousAt.congr ?_ hev
    exact ((differentiableAt_riemannZeta hs).continuousAt).sub
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs))

/-- `‖ζ(s)‖ ≤ Σ n^{−a}` for `Re s ≥ a > 1`. -/
theorem norm_riemannZeta_le_tsum_rpow {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((n : ℝ) ^ a)⁻¹ := by
  have hs1 : 1 < s.re := by linarith
  rw [← LSeries_one_eq_riemannZeta hs1]
  have hsum : Summable fun n : ℕ => ((n : ℝ) ^ a)⁻¹ := Real.summable_nat_rpow_inv.mpr ha
  have hle : ∀ n : ℕ, ‖LSeries.term 1 s n‖ ≤ ((n : ℝ) ^ a)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [LSeries.term_zero, norm_zero]; positivity
    rw [LSeries.term_of_ne_zero hn.ne', Pi.one_apply, norm_div, norm_one,
      norm_natCast_cpow_of_pos hn, one_div]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)
  unfold LSeries
  exact (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hle)).trans
    (Summable.tsum_le_tsum hle (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hle) hsum)

/-- **Growth of the regular part.**  For `0 < η ≤ ½` there is `K` with
`‖ζ(s) − 1/(s − 1)‖ ≤ K(2 + |t|)^{¼ + η/2}` on `Re s > ½`, `s ≠ 1`. -/
theorem exists_norm_zetaRegular_le {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℂ, 1 / 2 < s.re →
      ‖zetaRegular s‖ ≤ K * (2 + |s.im|) ^ (1 / 4 + η / 2) := by
  obtain ⟨C, hC, hconv⟩ := RHTower.exists_norm_riemannZeta_le_convexity hη hη2
  set Z : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (1 + η))⁻¹ with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  set R : Set ℂ := {s : ℂ | 1 / 2 ≤ s.re} ∩ closedBall 0 (12) with hR
  have hRc : IsCompact R :=
    (isCompact_closedBall 0 12).inter_left (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨M, hM⟩ := hRc.exists_bound_of_continuousOn continuous_zetaRegular.continuousOn
  set K : ℝ := max (C + 1) (max (Z + 1 / η) (max M 0)) with hKdef
  have hK1 : C + 1 ≤ K := le_max_left _ _
  have hK2 : Z + 1 / η ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK3 : M ≤ K := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hK0 : 0 ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨K, hK0, fun s hs => ?_⟩
  set θ₀ : ℝ := 1 / 4 + η / 2 with hθ₀
  have hbase : (1 : ℝ) ≤ (2 + |s.im|) ^ θ₀ :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by positivity)
  by_cases hbig : 1 + η < s.re
  · -- beyond the abscissa
    have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hbig; linarith
    rw [zetaRegular_of_ne hs1]
    have hz := norm_riemannZeta_le_tsum_rpow (by linarith : 1 < 1 + η) hbig.le
    have hinv : ‖1 / (s - 1)‖ ≤ 1 / η := by
      rw [norm_div, norm_one]
      have : η ≤ ‖s - 1‖ := by
        have := Complex.abs_re_le_norm (s - 1)
        rw [sub_re, one_re] at this
        linarith [le_abs_self (s.re - 1)]
      exact one_div_le_one_div_of_le hη this
    calc ‖riemannZeta s - 1 / (s - 1)‖ ≤ Z + 1 / η := (norm_sub_le _ _).trans (by linarith)
      _ ≤ K := hK2
      _ ≤ K * (2 + |s.im|) ^ θ₀ := le_mul_of_one_le_right hK0 hbase
  push Not at hbig
  by_cases ht : 8 ≤ |s.im|
  · -- convexity range
    have hs1 : s ≠ 1 := fun h => by rw [h, one_im, abs_zero] at ht; linarith
    rw [zetaRegular_of_ne hs1]
    have hzeta : ‖riemannZeta s‖ ≤ C * |s.im| ^ ((1 + η - s.re) / 2) := by
      rcases le_or_gt 0 s.im with him | him
      · rw [abs_of_nonneg him] at ht ⊢
        have := hconv s.re s.im (by linarith) hbig ht
        rwa [show ((s.re : ℂ) + (s.im : ℂ) * I) = s from Complex.re_add_im s] at this
      · rw [abs_of_neg him] at ht ⊢
        have := hconv s.re (-s.im) (by linarith) hbig ht
        have hconj : ((s.re : ℂ) + ((-s.im : ℝ) : ℂ) * I) = (starRingEnd ℂ) s := by
          apply Complex.ext <;> simp
        rw [hconj, riemannZeta_conj, Complex.norm_conj] at this
        exact this
    have hexp : |s.im| ^ ((1 + η - s.re) / 2) ≤ (2 + |s.im|) ^ θ₀ := by
      calc |s.im| ^ ((1 + η - s.re) / 2) ≤ |s.im| ^ θ₀ :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hθ₀]; linarith)
        _ ≤ (2 + |s.im|) ^ θ₀ :=
            Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by rw [hθ₀]; positivity)
    have hinv : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      have : 8 ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        rw [sub_im, one_im, sub_zero] at this
        linarith
      rw [div_le_one (by linarith)]; linarith
    calc ‖riemannZeta s - 1 / (s - 1)‖ ≤ C * |s.im| ^ ((1 + η - s.re) / 2) + 1 :=
          (norm_sub_le _ _).trans (by linarith)
      _ ≤ C * (2 + |s.im|) ^ θ₀ + (2 + |s.im|) ^ θ₀ := by gcongr
      _ = (C + 1) * (2 + |s.im|) ^ θ₀ := by ring
      _ ≤ K * (2 + |s.im|) ^ θ₀ := by gcongr
  · -- the compact middle range
    push Not at ht
    have hmem : s ∈ R := by
      refine ⟨hs.le, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 12 := by rw [abs_of_pos (by linarith)]; linarith
    calc ‖zetaRegular s‖ ≤ M := hM s hmem
      _ ≤ K := hK3
      _ ≤ K * (2 + |s.im|) ^ θ₀ := le_mul_of_one_le_right hK0 hbase

theorem differentiable_zetaRegular : Differentiable ℂ zetaRegular := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 (1 : ℂ))]
  refine ⟨fun s hs => ?_, continuous_zetaRegular.continuousAt⟩
  have hs1 : s ≠ 1 := hs.2
  have hev : (fun s : ℂ => riemannZeta s - 1 / (s - 1)) =ᶠ[𝓝 s] zetaRegular :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hs1) fun w hw => (zetaRegular_of_ne hw).symm
  refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev.symm).differentiableWithinAt
  exact (differentiableAt_riemannZeta hs1).sub
    ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1))

/-- The trivial weights have Dirichlet series `ζ(s) − 1`. -/
theorem LSeries_lamC_one {s : ℂ} (hs : 1 < s.re) :
    LSeries (WeilHerglotz.lamC fun _ => 1) s = riemannZeta s - 1 := by
  have hδ : LSeriesSummable LSeries.delta s := by
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [LSeries.term, LSeries.delta, hn]
  have hcongr : LSeries (WeilHerglotz.lamC fun _ => 1) s = LSeries (1 - LSeries.delta) s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; simp [WeilHerglotz.lamC, LSeries.delta]
    · have : n ≠ 1 := by omega
      simp [WeilHerglotz.lamC, LSeries.delta, h, this]
  rw [hcongr, LSeries_sub (LSeriesSummable_one_iff.mpr hs) hδ, LSeries_one_eq_riemannZeta hs,
    LSeries_delta, Pi.one_apply]

/-- `|s + ½| ≥ (2 + |Im s|)/3` on `Re s > ½`. -/
theorem two_add_abs_im_le_three_mul_norm {s : ℂ} (hs : 1 / 2 < s.re) :
    2 + |s.im| ≤ 3 * ‖s + 1 / 2‖ := by
  have h1 : s.re + 1 / 2 ≤ ‖s + 1 / 2‖ := by
    have := Complex.abs_re_le_norm (s + 1 / 2)
    have h : (s + 1 / 2).re = s.re + 1 / 2 := by simp
    rw [h] at this
    linarith [le_abs_self (s.re + 1 / 2)]
  have h2 : |s.im| ≤ ‖s + 1 / 2‖ := by
    have := Complex.abs_im_le_norm (s + 1 / 2)
    have h : (s + 1 / 2).im = s.im := by simp
    rwa [h] at this
  linarith

/-- **Trivial weights are a Herglotz producer at the critical abscissa after a subconvex boost.**
For `¼ < θ < 1` there is `c > 0` such that `archPart(s) + c(s + ½)^θ − (ζ(s) − 1)` extends
holomorphically to `Re s > ½` with nonnegative real part. -/
theorem exists_herglotz_trivialWeights_boosted {θ : ℝ} (hθ : 1 / 4 < θ) (hθ1 : θ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re) ∧
      ∀ s : ℂ, 1 < s.re →
        Φ s = WeilHerglotz.weilFunction (fun _ => 1) s + c * (s + 1 / 2) ^ (θ : ℂ) := by
  set η : ℝ := min (1 / 2) (θ - 1 / 4) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη2 : η ≤ 1 / 2 := min_le_left _ _
  have hηθ : 1 / 4 + η / 2 ≤ θ := by
    have := min_le_right (1 / 2 : ℝ) (θ - 1 / 4); linarith
  obtain ⟨K₂, hK₂, hzeta⟩ := exists_norm_zetaRegular_le hη0 hη2
  obtain ⟨K₁, hdig⟩ := exists_lower_bound_re_digamma_half
  set A : ℝ := max K₁ 0 / 2 + Real.log Real.pi / 2 + K₂ with hA
  have hlogpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hA0 : 0 ≤ A := by have := le_max_right K₁ 0; positivity
  set κ : ℝ := Real.cos (θ * (Real.pi / 2)) with hκ
  have hκ0 : 0 < κ :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  set c : ℝ := 3 * (A + 1) / κ with hc
  have hc0 : 0 < c := by positivity
  set Φ : ℂ → ℂ := fun s => Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1
    - zetaRegular s + c * (s + 1 / 2) ^ (θ : ℂ) with hΦ
  refine ⟨c, hc0, Φ, ?_, ?_, ?_⟩
  · intro s hs
    simp only [mem_setOf_eq] at hs
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    have hslit : s + 1 / 2 ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (((((differentiableAt_digamma_of_re_pos (by simp; linarith)).comp s
      ((differentiableAt_id).div_const 2)).div_const 2).sub_const _).add
      ((differentiableAt_const _).div differentiableAt_id hs0) |>.add_const _ |>.sub
      (differentiable_zetaRegular s)).add ((differentiableAt_const _).mul ?_)
    exact (differentiableAt_id.add_const _).cpow_const hslit
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have hX1 : (1 : ℝ) ≤ (2 + |s.im|) ^ θ :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) (by linarith)
    have hZ : ‖zetaRegular s‖ ≤ K₂ * (2 + |s.im|) ^ θ := by
      refine (hzeta s hs).trans (mul_le_mul_of_nonneg_left ?_ hK₂)
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hηθ
    have hZre : (zetaRegular s).re ≤ K₂ * (2 + |s.im|) ^ θ :=
      (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hZ)
    have hD : -max K₁ 0 ≤ (Complex.digamma (s / 2)).re :=
      (neg_le_neg (le_max_left K₁ 0)).trans (hdig s hs.le)
    have hinv : 0 ≤ (1 / s).re := by
      rw [one_div, Complex.inv_re]; exact div_nonneg hs0.le (Complex.normSq_nonneg _)
    have hpow : κ * ‖s + 1 / 2‖ ^ θ ≤ ((s + 1 / 2) ^ (θ : ℂ)).re :=
      cos_mul_rpow_le_re_cpow (by simp; linarith) (by linarith) hθ1.le
    have hnorm : (2 + |s.im|) ^ θ ≤ 3 * ‖s + 1 / 2‖ ^ θ := by
      have h3 : (3 : ℝ) ^ θ ≤ 3 := by
        calc (3 : ℝ) ^ θ ≤ 3 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1.le
          _ = 3 := Real.rpow_one 3
      calc (2 + |s.im|) ^ θ ≤ (3 * ‖s + 1 / 2‖) ^ θ :=
            Real.rpow_le_rpow (by positivity) (two_add_abs_im_le_three_mul_norm hs) (by linarith)
        _ = 3 ^ θ * ‖s + 1 / 2‖ ^ θ := Real.mul_rpow (by norm_num) (norm_nonneg _)
        _ ≤ 3 * ‖s + 1 / 2‖ ^ θ :=
            mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (norm_nonneg _) _)
    have hre : (Φ s).re = (Complex.digamma (s / 2)).re / 2 - Real.log Real.pi / 2 + (1 / s).re + 1
        - (zetaRegular s).re + c * ((s + 1 / 2) ^ (θ : ℂ)).re := by
      simp only [hΦ, Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.ofReal_re, Complex.re_ofReal_mul]
    have hcκ : c * κ = 3 * (A + 1) := by rw [hc]; field_simp
    have hboost : (A + 1) * (2 + |s.im|) ^ θ ≤ c * ((s + 1 / 2) ^ (θ : ℂ)).re := by
      calc (A + 1) * (2 + |s.im|) ^ θ ≤ (A + 1) * (3 * ‖s + 1 / 2‖ ^ θ) :=
            mul_le_mul_of_nonneg_left hnorm (by linarith)
        _ = c * (κ * ‖s + 1 / 2‖ ^ θ) := by rw [← mul_assoc c, hcκ]; ring
        _ ≤ c * ((s + 1 / 2) ^ (θ : ℂ)).re := mul_le_mul_of_nonneg_left hpow hc0.le
    rw [hre]
    set B : ℝ := max K₁ 0 / 2 + Real.log Real.pi / 2 + 1 with hB
    have hB1 : B ≤ B * (2 + |s.im|) ^ θ :=
      le_mul_of_one_le_right (by have := le_max_right K₁ 0; positivity) hX1
    have hsplit : (A + 1) * (2 + |s.im|) ^ θ = B * (2 + |s.im|) ^ θ + K₂ * (2 + |s.im|) ^ θ := by
      rw [hA, hB]; ring
    linarith
  · intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
    rw [WeilHerglotz.weilFunction, LSeries_lamC_one hs]
    simp only [hΦ]
    rw [zetaRegular_of_ne hs1]
    ring

/-! ### Without a boost the trivial weights fail at `s = 1`

The unboosted Weil function of `λ ≡ 1` continues to `½ψ(s/2) − ½log π + 1/s + 1 − (ζ(s) − 1/(s−1))`,
whose value at `s = 1` is `2 − 3γ/2 − log 2 − ½log π < 0`.  So no half-plane reaching down to
`s = 1` carries `λ ≡ 1` as a Herglotz producer, and the boost above is necessary at every level
`σ₀ ≤ 1`.  More generally every producer reaching below `1` has constant term
`lim_{σ→1⁺} (D_λ(σ) − 1/(σ−1)) ≤ 1 − γ/2 − log 2 − ½log π`; the von Mangoldt weights sit at `−γ`.
-/

/-- The continuation of the unboosted Weil function of the trivial weights. -/
def trivialWeilRegular (s : ℂ) : ℂ :=
  Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s + 1 - zetaRegular s

theorem trivialWeilRegular_eq_weilFunction {s : ℂ} (hs : 1 < s.re) :
    trivialWeilRegular s = WeilHerglotz.weilFunction (fun _ => 1) s := by
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  rw [WeilHerglotz.weilFunction, LSeries_lamC_one hs, trivialWeilRegular, zetaRegular_of_ne hs1]
  ring

/-- The archimedean part without its pole at `1`. -/
def archRegular (s : ℂ) : ℂ :=
  Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 + 1 / s

theorem continuousAt_archRegular_one : ContinuousAt archRegular 1 := by
  have hd : DifferentiableAt ℂ (fun s : ℂ => Complex.digamma (s / 2)) 1 :=
    (differentiableAt_digamma_of_re_pos (by norm_num)).comp 1
      ((differentiableAt_id).div_const 2)
  exact (((hd.div_const 2).sub_const _).add
    ((differentiableAt_const _).div differentiableAt_id one_ne_zero)).continuousAt

theorem re_archRegular_one :
    (archRegular 1).re = 1 - Real.eulerMascheroniConstant / 2 - Real.log 2 -
      Real.log Real.pi / 2 := by
  rw [archRegular, show ((1 : ℂ) / 2) = 1 / 2 from rfl, Complex.digamma_one_half]
  simp [Complex.log_re]
  ring

theorem trivialWeilRegular_eq_archRegular (s : ℂ) :
    trivialWeilRegular s = archRegular s + 1 - zetaRegular s := by
  rw [trivialWeilRegular, archRegular]

theorem continuousAt_trivialWeilRegular_one : ContinuousAt trivialWeilRegular 1 := by
  have h : trivialWeilRegular = fun s => archRegular s + 1 - zetaRegular s :=
    funext trivialWeilRegular_eq_archRegular
  rw [h]
  exact (continuousAt_archRegular_one.add continuousAt_const).sub
    continuous_zetaRegular.continuousAt

/-- `log π > 1.12`. -/
theorem log_pi_gt : (1.12 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (0.12 : ℝ) ≤ 1 / (1 - 0.12) := by
    have := Real.add_one_le_exp (-0.12 : ℝ)
    rw [Real.exp_neg] at this
    rw [le_div_iff₀ (by norm_num)]
    have hpos := Real.exp_pos (0.12 : ℝ)
    have : (1 - 0.12 : ℝ) ≤ (Real.exp 0.12)⁻¹ := by linarith
    calc Real.exp 0.12 * (1 - 0.12) ≤ Real.exp 0.12 * (Real.exp 0.12)⁻¹ :=
          mul_le_mul_of_nonneg_left this hpos.le
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h3 : Real.exp (1.12 : ℝ) = Real.exp 1 * Real.exp 0.12 := by
    rw [← Real.exp_add]; norm_num
  have h4 := Real.pi_gt_d2
  rw [h3]
  calc Real.exp 1 * Real.exp 0.12 ≤ 2.7182818286 * (1 / (1 - 0.12)) :=
        mul_le_mul h1.le h2 (Real.exp_pos _).le (by norm_num)
    _ < 3.14 := by norm_num
    _ < Real.pi := h4

/-- **The unboosted Weil function of the trivial weights is negative at `s = 1`:**
`2 − 3γ/2 − log 2 − ½log π < 0`. -/
theorem re_trivialWeilRegular_one_neg : (trivialWeilRegular 1).re < 0 := by
  have hz : zetaRegular 1 = (Real.eulerMascheroniConstant : ℂ) := by
    simp [zetaRegular]
  rw [trivialWeilRegular_eq_archRegular, hz, Complex.sub_re, Complex.add_re, re_archRegular_one]
  simp only [Complex.one_re, Complex.ofReal_re]
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hl2 := Real.log_two_gt_d9
  have hlπ := log_pi_gt
  linarith

/-- **The boost is necessary.**  There is `σ₁ > 1` such that the trivial weights are not a Herglotz
producer on any half-plane `Re s > σ₀` with `σ₀ < σ₁`. -/
theorem exists_not_isHerglotzProducerOn_trivialWeights :
    ∃ σ₁ : ℝ, 1 < σ₁ ∧ ∀ σ₀ : ℝ, σ₀ < σ₁ → ¬ IsHerglotzProducerOn σ₀ fun _ => 1 := by
  have hc := (continuous_re.continuousAt.comp continuousAt_trivialWeilRegular_one).eventually
    (gt_mem_nhds re_trivialWeilRegular_one_neg)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hc
  refine ⟨1 + ε / 2, by linarith, fun σ₀ hσ₀ hP => ?_⟩
  obtain ⟨Φ, -, hre, heq⟩ := hP
  set σ : ℝ := max (1 + ε / 4) ((σ₀ + (1 + ε / 2)) / 2) with hσ
  have hσ1 : 1 + ε / 4 ≤ σ := le_max_left _ _
  have hσ2 : σ < 1 + ε / 2 := max_lt (by linarith) (by linarith)
  have hσ0 : σ₀ < σ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hlt : (trivialWeilRegular (σ : ℂ)).re < 0 := by
    refine hball ?_
    rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hσre : 1 < (σ : ℂ).re := by rw [Complex.ofReal_re]; linarith
  have h0 := hre (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ0)
  rw [heq _ hσre, ← trivialWeilRegular_eq_weilFunction hσre] at h0
  linarith

theorem not_isHerglotzProducerOn_trivialWeights {σ₀ : ℝ} (hσ₀ : σ₀ ≤ 1) :
    ¬ IsHerglotzProducerOn σ₀ fun _ => 1 := by
  obtain ⟨σ₁, hσ₁, h⟩ := exists_not_isHerglotzProducerOn_trivialWeights
  exact h σ₀ (by linarith)

/-- **Constant-term ceiling.**  A Herglotz producer on `Re s > σ₀` with `σ₀ < 1` has
`Re D_λ(σ) − 1/(σ − 1) → C` as `σ → 1⁺` with `C ≤ 1 − γ/2 − log 2 − ½log π`. -/
theorem exists_tendsto_LSeries_sub_le_of_isHerglotzProducerOn {σ₀ : ℝ} (hσ₀ : σ₀ < 1)
    {lam : ℕ → ℝ} (h : IsHerglotzProducerOn σ₀ lam) :
    ∃ C : ℝ, C ≤ 1 - Real.eulerMascheroniConstant / 2 - Real.log 2 - Real.log Real.pi / 2 ∧
      Tendsto (fun σ : ℝ => (LSeries (WeilHerglotz.lamC lam) σ).re - 1 / (σ - 1))
        (𝓝[>] 1) (𝓝 C) := by
  obtain ⟨Φ, hd, hre, heq⟩ := h
  have h1 : (1 : ℂ) ∈ {s : ℂ | σ₀ < s.re} := by simp [hσ₀]
  have hΦ : ContinuousAt Φ 1 :=
    (hd.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds h1)).continuousAt
  refine ⟨(archRegular 1).re - (Φ 1).re, ?_, ?_⟩
  · rw [re_archRegular_one]; linarith [hre 1 h1]
  · have hcont : ContinuousAt (fun σ : ℝ => (archRegular σ).re - (Φ σ).re) 1 := by
      have hA : ContinuousAt (fun σ : ℝ => archRegular σ) 1 :=
        continuousAt_archRegular_one.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
      have hB : ContinuousAt (fun σ : ℝ => Φ σ) 1 :=
        hΦ.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)
      exact (continuous_re.continuousAt.comp hA).sub (continuous_re.continuousAt.comp hB)
    have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simp only [Complex.ofReal_one] at ht
    refine ht.congr' (eventually_nhdsWithin_of_forall fun σ (hσ : 1 < σ) => ?_)
    have hσre : 1 < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ
    have hL : LSeries (WeilHerglotz.lamC lam) σ = archPart σ - Φ σ := by
      rw [heq _ hσre, weilFunction_eq_archPart_sub]; ring
    show (archRegular σ).re - (Φ σ).re = (LSeries (WeilHerglotz.lamC lam) σ).re - 1 / (σ - 1)
    rw [hL, Complex.sub_re, archPart]
    have hσ1 : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hσ1, show ((1 : ℂ) / ((σ - 1 : ℝ) : ℂ)) = ((1 / (σ - 1) : ℝ) : ℂ) by push_cast; ring]
    simp only [archRegular, Complex.add_re, Complex.ofReal_re]
    ring

end RHTower.RelaxedHerglotz
