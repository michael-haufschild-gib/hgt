/-
The seam sign bit at the real anchor, read off the coefficient side.

On the real segment of the critical strip `σ ∈ (0,1)` the completed `ξ` is a
strictly positive real number: `(xi σ).im = 0` and `0 < (xi σ).re`.  The
mechanism is entirely arithmetic, not symmetry:

* The paired Dirichlet-eta series
  `E(s) = Σ_n ((2n+1)^{-s} − (2n+2)^{-s})` converges locally uniformly on
  `Re s > 0` (the consecutive difference is `O(|s|·n^{-Re s−1})` by the mean
  value theorem), hence is analytic there.  On `Re s > 1` it regroups the
  absolutely convergent alternating series into `E(s) = (1 − 2^{1−s})·ζ(s)`,
  and the identity theorem propagates this to the whole punctured half-plane.

* At a real `σ ∈ (0,1)` every term of `E` is a positive real, so `E(σ) > 0`,
  while the eta factor `1 − 2^{1−σ}` is a negative real (`2^{1−σ} > 1`).
  Therefore `ζ(σ) = E(σ)/(1 − 2^{1−σ})` is a *negative* real.

* The archimedean factor `archFactor σ = σ(σ−1)/2 · Γ_ℝ(σ)` is a negative
  real on `(0,1)` (the polynomial part is negative, `Γ_ℝ` positive).

The product `ξ(σ) = archFactor(σ)·ζ(σ) = (negative)·(negative)` is a positive
real.  The base point of all seam-sign bookkeeping is `+`, forced by the
coefficients themselves.
-/
import Mathlib
import GaloisForLFunctions.RHTower.ZetaCarrier

namespace RHTower

open Complex Filter Set Topology

/-! ### The paired Dirichlet-eta series -/

/-- The `n`-th paired eta term `(2n+1)^{-s} − (2n+2)^{-s}` (complex `cpow`,
real positive bases). -/
private noncomputable def etaPairTerm (n : ℕ) (s : ℂ) : ℂ :=
    ((2*(n:ℝ)+1 : ℝ):ℂ)^(-s) - ((2*(n:ℝ)+2 : ℝ):ℂ)^(-s)

/-- The paired eta series `E(s) = Σ_n ((2n+1)^{-s} − (2n+2)^{-s})`. -/
private noncomputable def etaPairSum (s : ℂ) : ℂ := ∑' n, etaPairTerm n s

private theorem etaPairTerm_differentiable (n : ℕ) : Differentiable ℂ (etaPairTerm n) := by
  have hpow : ∀ c : ℝ, 0 < c → Differentiable ℂ (fun s : ℂ => (c:ℂ)^(-s)) := fun c hc x =>
    (HasDerivAt.const_cpow (by simpa using (hasDerivAt_id x).neg)
      (Or.inl (Complex.ofReal_ne_zero.mpr (ne_of_gt hc)))).differentiableAt
  exact (hpow _ (by positivity)).sub (hpow _ (by positivity))

/-- A convergent majorant tail: `Σ_n (2n+1)^{-c}` converges for `c > 1`. -/
private theorem etaTail_summable (c : ℝ) (hc : 1 < c) :
    Summable (fun n : ℕ => (2*(n:ℝ)+1)^(-c)) := by
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) (fun n => ?_)
    ((Real.summable_one_div_nat_add_rpow 1 c).mpr hc)
  have hle : (2*(n:ℝ)+1)^(-c) ≤ ((n:ℝ)+1)^(-c) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  refine hle.trans (le_of_eq ?_)
  rw [Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]

/-- The mean-value bound: the consecutive difference is `O(|w|·(2n+1)^{-Re w−1})`. -/
private theorem etaPairTerm_norm_bound (w : ℂ) (hw : 0 < w.re) (n : ℕ) :
    ‖etaPairTerm n w‖ ≤ ‖w‖ * (2*(n:ℝ)+1)^(-w.re - 1) := by
  set a : ℝ := 2*(n:ℝ)+1 with ha_def
  set b : ℝ := 2*(n:ℝ)+2 with hb_def
  have hapos : 0 < a := by rw [ha_def]; positivity
  have hab : a < b := by rw [ha_def, hb_def]; linarith
  have hba : b - a = 1 := by rw [ha_def, hb_def]; ring
  have hwne : -w ≠ 0 := by simp only [neg_ne_zero]; intro h; rw [h] at hw; simp at hw
  set φ : ℝ → ℂ := fun t => (t:ℂ)^(-w) with hφ
  have hderiv : ∀ x ∈ Icc a b, HasDerivWithinAt φ ((-w) * (x:ℂ)^((-w)-1)) (Icc a b) x := fun x hx =>
    (hasDerivAt_ofReal_cpow_const (ne_of_gt (lt_of_lt_of_le hapos hx.1)) hwne).hasDerivWithinAt
  set C : ℝ := ‖w‖ * a^(-w.re - 1) with hC
  have hbound : ∀ x ∈ Ico a b, ‖(-w) * (x:ℂ)^((-w)-1)‖ ≤ C := by
    intro x hx
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hapos hx.1),
      show ((-w) - 1).re = -w.re - 1 by simp, hC]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hapos hx.1 (by linarith)) (norm_nonneg w)
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b (right_mem_Icc.2 hab.le)
  rw [hba, mul_one] at hmvt
  calc ‖etaPairTerm n w‖ = ‖φ b - φ a‖ := by rw [etaPairTerm, hφ, norm_sub_rev]
    _ ≤ C := hmvt

private theorem etaPairTerm_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun n => etaPairTerm n s) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => etaPairTerm_norm_bound s hs n) ?_)
  exact ((etaTail_summable (s.re + 1) (by linarith)).mul_left ‖s‖).congr
    (fun n => by rw [show (-s.re - 1) = -(s.re+1) by ring])

/-- The paired eta series is analytic on the open half-plane `Re s > 0`. -/
private theorem etaPairSum_analyticOnNhd :
    AnalyticOnNhd ℂ etaPairSum {s : ℂ | 0 < s.re} := by
  refine DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hz' : 0 < z.re := hz
  set δ : ℝ := z.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set M : ℝ := ‖z‖ + δ with hM
  have hDiffBall : DifferentiableOn ℂ etaPairSum (Metric.ball z δ) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => M * (2*(n:ℝ)+1)^(-δ-1)) ?_
      (fun n => (etaPairTerm_differentiable n).differentiableOn) Metric.isOpen_ball ?_
    · exact ((etaTail_summable (δ+1) (by linarith)).mul_left M).congr
        (fun n => by rw [show (-δ - 1) = -(δ+1) by ring])
    · intro n w hw
      have hd : dist w z < δ := by simpa [Metric.mem_ball] using hw
      have h2 : ‖w - z‖ < δ := by simpa [dist_eq] using hd
      have hwre : δ < w.re := by
        have h1 : |(w - z).re| ≤ ‖w - z‖ := by simpa using RCLike.abs_re_le_norm (w - z)
        have := (abs_lt.mp (lt_of_le_of_lt h1 h2)).1
        simp only [Complex.sub_re] at this
        rw [hδ]; linarith
      have hwle : ‖w‖ ≤ M := by
        have htri : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
          calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
            _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        rw [hM]; linarith
      calc ‖etaPairTerm n w‖ ≤ ‖w‖ * (2*(n:ℝ)+1)^(-w.re-1) := etaPairTerm_norm_bound w (by linarith) n
        _ ≤ M * (2*(n:ℝ)+1)^(-δ-1) := by
            apply mul_le_mul hwle _ (Real.rpow_nonneg (by positivity) _) (by rw [hM]; positivity)
            exact Real.rpow_le_rpow_of_exponent_le
              (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  exact (hDiffBall.differentiableAt (Metric.ball_mem_nhds z hδpos)).differentiableWithinAt

/-! ### The eta identity on `Re s > 1` -/

/-- Regroup an absolutely convergent series over `ℕ` into consecutive pairs. -/
private theorem tsum_pair_split (f : ℕ → ℂ) (hf : Summable f) :
    ∑' m, f m = ∑' k, (f (2*k) + f (2*k+1)) := by
  have hcomp : Summable (fun p : ℕ × Fin 2 => f ((Nat.divModEquiv 2).symm p)) :=
    hf.comp_injective (Nat.divModEquiv 2).symm.injective
  rw [← Equiv.tsum_eq (Nat.divModEquiv 2).symm f,
      hcomp.tsum_prod' (fun b => (hasSum_fintype _).summable)]
  refine tsum_congr (fun k => ?_)
  rw [tsum_fintype, Fin.sum_univ_two]
  congr 1 <;> · simp [Nat.divModEquiv]; ring_nf

/-- On `Re s > 1` the paired eta series equals `(1 − 2^{1−s})·ζ(s)`. -/
private theorem etaPairSum_eq_eta {s : ℂ} (hs : 1 < s.re) :
    etaPairSum s = (1 - (2:ℂ)^(1-s)) * riemannZeta s := by
  unfold etaPairSum
  set zt : ℕ → ℂ := fun m => ((m:ℂ)+1)^(-s) with hzt
  have hzeta : riemannZeta s = ∑' m, zt m := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    exact tsum_congr (fun m => by simp only [hzt, Complex.cpow_neg, one_div])
  have hzt_sum : Summable zt := by
    apply Summable.of_norm
    have hcongr : ∀ m : ℕ, ‖zt m‖ = 1 / |(m:ℝ)+1|^s.re := by
      intro m
      simp only [hzt]
      rw [show ((m:ℂ)+1) = (((m:ℝ)+1:ℝ):ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      rw [Complex.neg_re, Real.rpow_neg (by positivity), one_div, abs_of_pos (by positivity)]
    exact ((Real.summable_one_div_nat_add_rpow 1 s.re).mpr hs).congr (fun m => (hcongr m).symm)
  have hsum_odd : Summable (fun k => zt (2*k)) := hzt_sum.comp_injective (fun a b h => by omega)
  have hsum_even : Summable (fun k => zt (2*k+1)) := hzt_sum.comp_injective (fun a b h => by omega)
  have pw_even : ∀ k, zt (2*k+1) = (2:ℂ)^(-s) * zt k := by
    intro k
    simp only [hzt]
    rw [show ((2*k+1:ℕ):ℂ)+1 = ((2:ℝ):ℂ) * (((k:ℝ)+1:ℝ):ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    push_cast; ring
  have pw_Et : ∀ k, etaPairTerm k s = zt (2*k) - zt (2*k+1) := by
    intro k
    rw [etaPairTerm]; simp only [hzt]
    congr 2 <;> · push_cast; ring
  have hSeven : (∑' k, zt (2*k+1)) = (2:ℂ)^(-s) * riemannZeta s := by
    rw [hzeta, show (∑' k, zt (2*k+1)) = ∑' k, (2:ℂ)^(-s) * zt k from tsum_congr pw_even]
    exact tsum_mul_left
  have hζsplit : riemannZeta s = (∑' k, zt (2*k)) + (∑' k, zt (2*k+1)) := by
    rw [hzeta, tsum_pair_split zt hzt_sum, hsum_odd.tsum_add hsum_even]
  have hE : (∑' n, etaPairTerm n s) = (∑' k, zt (2*k)) - (∑' k, zt (2*k+1)) := by
    rw [show (∑' n, etaPairTerm n s) = ∑' k, (zt (2*k) - zt (2*k+1)) from tsum_congr pw_Et]
    exact hsum_odd.tsum_sub hsum_even
  rw [hE]
  have hSodd : (∑' k, zt (2*k)) = riemannZeta s - (∑' k, zt (2*k+1)) := by rw [hζsplit]; ring
  rw [hSodd, hSeven]
  have h2 : (2:ℂ)^(1-s) = 2 * (2:ℂ)^(-s) := by
    rw [show (1:ℂ)-s = 1 + (-s) by ring, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [h2]; ring

/-! ### The real coefficient series at the anchor -/

/-- The real `n`-th paired eta term `(2n+1)^{-σ} − (2n+2)^{-σ}`. -/
private noncomputable def etaRealTerm (σ : ℝ) (n : ℕ) : ℝ :=
    (2*(n:ℝ)+1)^(-σ) - (2*(n:ℝ)+2)^(-σ)

private theorem etaPairTerm_ofReal (σ : ℝ) (n : ℕ) :
    etaPairTerm n (σ:ℂ) = ((etaRealTerm σ n : ℝ):ℂ) := by
  simp only [etaPairTerm, etaRealTerm]
  rw [Complex.ofReal_sub, show (-(σ:ℂ)) = (((-σ):ℝ):ℂ) by push_cast; ring,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]

private theorem etaRealTerm_pos (σ : ℝ) (hσ : 0 < σ) (n : ℕ) : 0 < etaRealTerm σ n := by
  simp only [etaRealTerm]
  have : (2*(n:ℝ)+2)^(-σ) < (2*(n:ℝ)+1)^(-σ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity),
        inv_lt_inv₀ (Real.rpow_pos_of_pos (by positivity) σ) (Real.rpow_pos_of_pos (by positivity) σ)]
    exact Real.rpow_lt_rpow (by positivity) (by linarith) hσ
  linarith

private theorem etaRealTerm_summable (σ : ℝ) (hσ : 0 < σ) : Summable (etaRealTerm σ) := by
  have hc : Summable (fun n => etaPairTerm n (σ:ℂ)) := etaPairTerm_summable (σ:ℂ) (by simpa using hσ)
  have hc2 : Summable (fun n => ((etaRealTerm σ n : ℝ):ℂ)) :=
    hc.congr (fun n => etaPairTerm_ofReal σ n)
  simpa using hc2.map (Complex.reCLM) Complex.reCLM.continuous

/-! ### `ζ` is a negative real on `(0,1)`, hence `ξ` is a positive real -/

/-- On the open real segment `(0,1)` the Riemann zeta function takes a strictly
negative real value.  This is read off the coefficient side: the paired eta
series is positive there and the eta factor `1 − 2^{1−σ}` is negative. -/
private theorem zeta_neg_real_on_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ Z : ℝ, Z < 0 ∧ riemannZeta (σ:ℂ) = (Z:ℂ) := by
  -- identity theorem on a preconnected region reaching `Re s > 1`
  set A : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1} with hA
  set B : Set ℂ := {s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im} with hB
  set W : Set ℂ := A ∪ B with hW
  have hW_sub : W ⊆ {s : ℂ | 0 < s.re} := by
    rw [hW]; exact union_subset inter_subset_left inter_subset_left
  have hA_conv : Convex ℝ A := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have hB_conv : Convex ℝ B := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hAB : (A ∩ B).Nonempty := by
    refine ⟨(⟨1/2, 1⟩ : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
    · show (0:ℝ) < 1/2; norm_num
    · show (1/2:ℝ) < 1; norm_num
    · show (0:ℝ) < 1/2; norm_num
    · show (0:ℝ) < 1; norm_num
  have hW_pre : IsPreconnected W :=
    IsPreconnected.union' hAB hA_conv.isPreconnected hB_conv.isPreconnected
  have hne1 : ∀ w ∈ W, w ≠ 1 := by
    intro w hw
    rcases hw with hw | hw
    · intro h; rw [h] at hw; exact absurd hw.2 (by norm_num)
    · intro h; rw [h] at hw; exact absurd hw.2 (by norm_num)
  have hE_an : AnalyticOnNhd ℂ etaPairSum W := etaPairSum_analyticOnNhd.mono hW_sub
  have hG_an : AnalyticOnNhd ℂ (fun s => (1 - (2:ℂ)^(1-s)) * riemannZeta s) W := by
    have hdon : DifferentiableOn ℂ (fun s => (1 - (2:ℂ)^(1-s)) * riemannZeta s) {(1:ℂ)}ᶜ := by
      intro w hw
      have hw1 : w ≠ 1 := hw
      have h2d : DifferentiableAt ℂ (fun s : ℂ => (2:ℂ)^(1-s)) w :=
        (HasDerivAt.const_cpow ((hasDerivAt_const w (1:ℂ)).sub (hasDerivAt_id w))
          (Or.inl two_ne_zero)).differentiableAt
      exact (((differentiableAt_const (1:ℂ)).sub h2d).mul
        (differentiableAt_riemannZeta hw1)).differentiableWithinAt
    intro w hw
    exact hdon.analyticAt (isOpen_compl_singleton.mem_nhds (hne1 w hw))
  have h2I : (2 + I : ℂ) ∈ W := by
    right; exact ⟨by show (0:ℝ) < (2+I).re; simp, by show (0:ℝ) < (2+I).im; simp⟩
  have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 + I : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show (1:ℝ) < (2+I).re; simp)
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 + I : ℂ), etaPairSum z = (1 - (2:ℂ)^(1-z)) * riemannZeta z :=
    ((Filter.eventually_of_mem hmem (fun z hz => etaPairSum_eq_eta hz)).filter_mono
      nhdsWithin_le_nhds).frequently
  have hEqOn : Set.EqOn etaPairSum (fun s => (1 - (2:ℂ)^(1-s)) * riemannZeta s) W :=
    hE_an.eqOn_of_preconnected_of_frequently_eq hG_an hW_pre h2I hfreq
  have hσmem : (σ:ℂ) ∈ W := by left; exact ⟨by simpa using h0, by simpa using h1⟩
  have hid : etaPairSum (σ:ℂ) = (1 - (2:ℂ)^(1-(σ:ℂ))) * riemannZeta (σ:ℂ) := hEqOn hσmem
  -- cast the two sides to reals
  have hEcast : etaPairSum (σ:ℂ) = ((∑' n, etaRealTerm σ n : ℝ):ℂ) := by
    unfold etaPairSum
    rw [Complex.ofReal_tsum]
    exact tsum_congr (fun n => etaPairTerm_ofReal σ n)
  have hetafac : (1 - (2:ℂ)^(1-(σ:ℂ))) = ((1 - (2:ℝ)^(1-σ) : ℝ):ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one,
        show (1-(σ:ℂ)) = (((1-σ):ℝ):ℂ) by push_cast; ring,
        show ((2:ℂ)) = ((2:ℝ):ℂ) by norm_num, Complex.ofReal_cpow (by norm_num)]
  have hApos : 0 < ∑' n, etaRealTerm σ n := by
    have := Summable.tsum_lt_tsum_of_nonneg (f := fun _ => (0:ℝ)) (i := 0)
      (fun _ => le_refl 0) (fun n => (etaRealTerm_pos σ h0 n).le)
      (by simpa using etaRealTerm_pos σ h0 0) (etaRealTerm_summable σ h0)
    simpa using this
  have hDneg : (1:ℝ) - (2:ℝ)^(1-σ) < 0 := by
    have h2gt : (1:ℝ) < (2:ℝ)^(1-σ) := by
      rw [Real.one_lt_rpow_iff_of_pos (by norm_num)]; left; exact ⟨by norm_num, by linarith⟩
    linarith
  have hDne : ((1 - (2:ℝ)^(1-σ) : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hDneg)
  have key : ((∑' n, etaRealTerm σ n : ℝ):ℂ)
      = ((1 - (2:ℝ)^(1-σ) : ℝ):ℂ) * riemannZeta (σ:ℂ) := by
    rw [← hEcast, hid, hetafac]
  have hζeq : riemannZeta (σ:ℂ)
      = ((∑' n, etaRealTerm σ n : ℝ):ℂ) / ((1 - (2:ℝ)^(1-σ) : ℝ):ℂ) := by
    rw [eq_div_iff hDne, mul_comm]; exact key.symm
  refine ⟨(∑' n, etaRealTerm σ n) / (1 - (2:ℝ)^(1-σ)), div_neg_of_pos_of_neg hApos hDneg, ?_⟩
  rw [hζeq, ← Complex.ofReal_div]

/-- On `(0,1)` the archimedean factor `σ(σ−1)/2 · Γ_ℝ(σ)` is a negative real. -/
private theorem archFactor_neg_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ Wa : ℝ, Wa < 0 ∧ archFactor (σ:ℂ) = (Wa:ℂ) := by
  refine ⟨σ*(σ-1)/2 * (Real.pi^(-σ/2) * Real.Gamma (σ/2)), ?_, ?_⟩
  · apply mul_neg_of_neg_of_pos
    · apply div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h0 (by linarith)) (by norm_num)
    · exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
  · rw [archFactor, Complex.Gammaℝ_def, show ((σ:ℂ)/2) = (((σ/2):ℝ):ℂ) by push_cast; ring,
        Complex.Gamma_ofReal, show (-(σ:ℂ)/2) = (((-σ/2):ℝ):ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow Real.pi_pos.le]
    push_cast; ring

/-- On `(0,1)` the completed `ξ` is a strictly positive real number. -/
private theorem xi_real_anchor_eq {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ r : ℝ, 0 < r ∧ xi (σ:ℂ) = (r:ℂ) := by
  obtain ⟨Z, hZ, hζ⟩ := zeta_neg_real_on_Ioo h0 h1
  obtain ⟨Wa, hWa, harch⟩ := archFactor_neg_real h0 h1
  have hσ0 : (σ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h0)
  have hσ1 : (σ:ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; exact ne_of_lt h1
  have hG : Gammaℝ (σ:ℂ) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using h0)
  refine ⟨Wa * Z, mul_pos_of_neg_of_neg hWa hZ, ?_⟩
  rw [xi_eq_archFactor_mul_zeta hσ0 hσ1 hG, harch, hζ, ← Complex.ofReal_mul]

/-! ### The seam sign bit at the real anchor -/

/-- `ξ` is real on the real segment of the critical strip: for `σ ∈ (0,1)`,
`ξ(σ)` has vanishing imaginary part. -/
theorem xi_real_on_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (xi (σ:ℂ)).im = 0 := by
  obtain ⟨r, _, hr⟩ := xi_real_anchor_eq h0 h1
  rw [hr, Complex.ofReal_im]

/-- `ξ` is strictly positive on the real segment of the critical strip: for
`σ ∈ (0,1)`, `0 < ξ(σ).re`.  The seam sign at the real anchor is `+`, forced by
the coefficients (positive paired eta series, negative eta factor, negative
archimedean factor). -/
theorem xi_pos_on_real_anchor {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    0 < (xi (σ:ℂ)).re := by
  obtain ⟨r, hr, hval⟩ := xi_real_anchor_eq h0 h1
  rw [hval, Complex.ofReal_re]; exact hr

end RHTower
