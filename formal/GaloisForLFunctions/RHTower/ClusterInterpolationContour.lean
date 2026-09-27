import GaloisForLFunctions.RHTower.ClusterNodeFrame
import GaloisForLFunctions.HTGeometry.ForwardDifferenceProductSelection

/-!
# Interpolation at a cluster of zeros of `Ξ` through two rectangle contours

A `ClusterSetup` fixes a height `t₀ ≥ 101`, a depth `δ₀ ∈ (0, ½]`, and, chosen by the
forward-difference selection over the window zeros, the half-width `X ∈ [½, ¾]` and the depth
`y₀ ∈ [δ₀/4, δ₀/2]` of the rectangles `[t₀ ± X] × ±[y₀, 1]` (`exists_clusterSetup`). The nodes
are the zeros of `Ξ` in these rectangles, and `K = D_L Φ` is Riemann's kernel divided by the node
divisor.

* On the frames, `|K̂| ≥ e^{-π(t₀+1)/4 - O(N + log t₀)} (δ₀/(16e))^N`, `N` the number of window
  zeros (`Lh_le_norm_Khat`). Every frame point is joined to `Re s = 2` by at most two zero-free
  segments along which `log|ξ/P_V|` is `O(log t₀)`-Lipschitz.
* `|P_{s_p}| ≥ 1` near `t₀` for the polar shift `s_p = (2k+1)π/t₀ ∈ [1/16, 1/8]`
  (`one_le_norm_polarSymbol`).
* The polynomial `Q` in `w = e^{iκz}` (`κ = 1/(8(N+1))`) interpolating `±i/(P K̂)` at the nodes
  is bounded on the real line by `2·3^N·Mb`, where `Mb` involves only frame quantities
  (`norm_Q_eval_le`). The distances between the nodes never enter.
-/

open Complex MeasureTheory Filter Topology Set Polynomial GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## `|Ξ|` through the window quotient -/

theorem sub_eq_I_mul_sub_gammaOf (t : ℂ) (q : ℂ) :
    (1 / 2 + I * t) - q = I * (t - gammaOf q) := by
  have := one_half_add_I_mul_gammaOf q
  linear_combination this

theorem norm_riemannXiHat_eq_window (t₀ : ℝ) (t : ℂ) :
    ‖riemannXiHat t‖ = ‖windowQuotient t₀ (1 / 2 + I * t)‖ *
      ∏ q ∈ windowCopySet t₀, ‖t - gammaOf (q.1 : ℂ)‖ := by
  have hP : ‖windowPoly t₀ (1 / 2 + I * t)‖ = ∏ q ∈ windowCopySet t₀, ‖t - gammaOf (q.1 : ℂ)‖ := by
    unfold windowPoly
    rw [norm_prod]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [sub_eq_I_mul_sub_gammaOf, norm_mul, Complex.norm_I, one_mul]
  rw [riemannXiHat_eq_xi, ← hP]
  by_cases h0 : windowPoly t₀ (1 / 2 + I * t) = 0
  · rw [h0, norm_zero, mul_zero]
    unfold windowPoly at h0
    obtain ⟨q, _, hq⟩ := Finset.prod_eq_zero_iff.mp h0
    rw [sub_eq_zero.mp hq, xi_xiZeroCopy_eq_zero, norm_zero]
  · unfold windowQuotient
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h0)]

/-- The window product splits into the node divisor and the other window zeros. -/
theorem prod_window_split (t₀ X y₀ : ℝ) (t : ℂ) :
    ∏ q ∈ windowCopySet t₀, ‖t - gammaOf (q.1 : ℂ)‖ =
      ‖divisorEval (nodeList t₀ X y₀) t‖ *
        ∏ q ∈ (windowCopySet t₀).filter (fun q => q.1 ∉ nodeSet t₀ X y₀),
          ‖t - gammaOf (q.1 : ℂ)‖ := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (windowCopySet t₀)
    (fun q => q.1 ∈ nodeSet t₀ X y₀)]
  congr 1
  have hsub : (windowCopySet t₀).filter (fun q => q.1 ∈ nodeSet t₀ X y₀) =
      (nodeSet t₀ X y₀).sigma fun _ => Finset.univ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, and_true]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      unfold windowCopySet
      rw [Finset.mem_sigma]
      exact ⟨(Finset.mem_filter.mp h).1, Finset.mem_univ _⟩
  rw [hsub, Finset.prod_sigma, divisorEval_nodeList, norm_prod]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
  rfl

/-! ## `log|ξ/P|` on the frame of the lower rectangle -/

theorem mem_segment_re_im {a b z : ℂ} (hz : z ∈ segment ℝ a b) :
    ∃ θ ∈ Icc (0 : ℝ) 1, z.re = a.re + θ * (b.re - a.re) ∧ z.im = a.im + θ * (b.im - a.im) := by
  rw [segment_eq_image] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  refine ⟨θ, hθ, ?_, ?_⟩ <;> simp <;> ring

/-- The number of window copies. -/
abbrev windowCount (t₀ : ℝ) : ℕ := (windowCopySet t₀).card

/-- The lower bound for `log|ξ/P|` on the frame. -/
def frameLogLower (t₀ : ℝ) : ℝ :=
  -(π * (t₀ + 1) / 4) - 2 - windowCount t₀ * Real.log 5 - 3 * (windowLogConst * Real.log t₀)

/-- **`log|ξ/P|` on the frame of the lower rectangle.** Every frame point of
`[t₀ - X, t₀ + X] × [-1, -y₀]` is joined to an anchor `2 + iτ` by at most two zero-free
segments of total length `≤ 3`. -/
theorem log_norm_windowQuotient_frame_ge {t₀ X y₀ : ℝ} (ht₀ : 8 ≤ t₀) (hX1 : 1 / 2 ≤ X)
    (hX2 : X ≤ 3 / 4) (hy₀ : 0 < y₀) (hy₁ : y₀ ≤ 1 / 4)
    (hnoX : ∀ q ∈ windowCopySet t₀, |(q.1 : ℂ).im - t₀| ≠ X)
    (hnoy : ∀ q ∈ windowCopySet t₀, |(q.1 : ℂ).re - 1 / 2| ≠ y₀)
    {t : ℂ} (hre : |t.re - t₀| ≤ X) (him1 : -1 ≤ t.im) (him2 : t.im ≤ -y₀)
    (hframe : OnFrame t₀ X y₀ t) :
    frameLogLower t₀ ≤ Real.log ‖windowQuotient t₀ (1 / 2 + I * t)‖ := by
  set C := windowLogConst * Real.log t₀ with hC
  have hC0 : 0 ≤ C := mul_nonneg windowLogConst_nonneg (Real.log_nonneg (by linarith))
  set s : ℂ := 1 / 2 + I * t with hs
  have hsre : s.re = 1 / 2 - t.im := by simp [hs]; ring
  have hsim : s.im = t.re := by simp [hs]
  -- no zero of `ξ` at ordinate `t₀ ± X`
  have hzeroA : ∀ z : ℂ, |z.im - t₀| = X → xi z ≠ 0 := by
    intro z hz h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have hqV : q ∈ windowCopySet t₀ := mem_windowCopySet.mpr (by rw [hq]; linarith)
    exact hnoX q hqV (by rw [hq]; exact hz)
  -- no zero of `ξ` on `Re s = ½ + y₀` in the window
  have hzeroB : ∀ z : ℂ, z.re = 1 / 2 + y₀ → |z.im - t₀| ≤ X → xi z ≠ 0 := by
    intro z hz1 hz2 h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have hqV : q ∈ windowCopySet t₀ := mem_windowCopySet.mpr (by rw [hq]; linarith)
    exact hnoy q hqV (by rw [hq, hz1]; simp [abs_of_pos hy₀])
  -- no zero of `ξ` with `Re s ≥ 1`
  have hzeroC : ∀ z : ℂ, 1 ≤ z.re → xi z ≠ 0 := by
    intro z hz h
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h
    have := xiZeroCopy_re_lt_one q
    rw [hq] at this; linarith
  -- a generic horizontal segment to the anchor
  have hanchor : ∀ τ : ℝ, |τ - t₀| ≤ 1 →
      -(π * (t₀ + 1) / 4) - 2 - windowCount t₀ * Real.log 5 ≤
        Real.log ‖windowQuotient t₀ (2 + τ * I)‖ := by
    intro τ hτ
    have h := log_norm_windowQuotient_anchor_ge ht₀ hτ
    have : -(π * (t₀ + 1) / 4) ≤ -(π * τ / 4) := by
      have := (abs_le.mp hτ).2; nlinarith [Real.pi_pos]
    unfold windowCount; linarith
  have hlip := fun {a b : ℂ} (h : ∀ z ∈ segment ℝ a b,
      1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0) =>
    (abs_le.mp (abs_log_windowQuotient_sub_le ht₀ h)).2
  unfold frameLogLower
  rcases hframe with h1 | h2 | h3
  · -- vertical side: go right at height `t.re`
    set b : ℂ := 2 + t.re * I
    have hseg : ∀ z ∈ segment ℝ s b, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0 := by
      intro z hz
      obtain ⟨θ, hθ, hzr, hzi⟩ := mem_segment_re_im hz
      have hbre : b.re = 2 := by simp [b]
      have hbim : b.im = t.re := by simp [b]
      rw [hbre, hsre] at hzr; rw [hbim, hsim] at hzi
      have hzi' : z.im = t.re := by rw [hzi]; ring
      refine ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2], by rw [hzi']; linarith, ?_⟩
      exact hzeroA z (by rw [hzi']; exact h1)
    have hl := hlip hseg
    have hlen : ‖b - s‖ ≤ 3 / 2 := by
      have : b - s = ((3 / 2 + t.im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [b, hs]; ring
        · simp [b, hs]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have ha := hanchor t.re (by linarith)
    have hm := mul_le_mul_of_nonneg_left hlen hC0
    linarith
  · -- inner side: up along `Re s = ½ + y₀`, then right
    have htim : t.im = -y₀ := by
      rcases abs_eq (hy₀.le) |>.mp h2 with h | h <;> [linarith; exact h]
    set m : ℂ := (1 / 2 + y₀ : ℝ) + ((t₀ + X : ℝ) : ℂ) * I
    set b : ℂ := 2 + ((t₀ + X : ℝ) : ℂ) * I
    have hseg1 : ∀ z ∈ segment ℝ s m, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0 := by
      intro z hz
      obtain ⟨θ, hθ, hzr, hzi⟩ := mem_segment_re_im hz
      have hmre : m.re = 1 / 2 + y₀ := by simp [m]
      have hmim : m.im = t₀ + X := by simp [m]
      rw [hmre, hsre, htim] at hzr; rw [hmim, hsim] at hzi
      have hzr' : z.re = 1 / 2 + y₀ := by rw [hzr]; ring
      have hre' := abs_le.mp hre
      have hzim : |z.im - t₀| ≤ X := by
        rw [hzi, abs_le]; constructor <;> nlinarith [hθ.1, hθ.2]
      exact ⟨by linarith, by linarith, by linarith, hzeroB z hzr' hzim⟩
    have hseg2 : ∀ z ∈ segment ℝ m b, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0 := by
      intro z hz
      obtain ⟨θ, hθ, hzr, hzi⟩ := mem_segment_re_im hz
      have hmre : m.re = 1 / 2 + y₀ := by simp [m]
      have hmim : m.im = t₀ + X := by simp [m]
      have hbre : b.re = 2 := by simp [b]
      have hbim : b.im = t₀ + X := by simp [b]
      rw [hmre, hbre] at hzr; rw [hmim, hbim] at hzi
      have hzi' : z.im = t₀ + X := by rw [hzi]; ring
      refine ⟨by nlinarith [hθ.1, hθ.2], by nlinarith [hθ.1, hθ.2], ?_, ?_⟩
      · rw [hzi']; rw [abs_of_nonneg (by linarith)]; linarith
      · exact hzeroA z (by rw [hzi']; ring_nf; exact abs_of_nonneg (by linarith))
    have hl1 := hlip hseg1
    have hl2 := hlip hseg2
    have hlen1 : ‖m - s‖ ≤ 3 / 2 := by
      have : m - s = ((t₀ + X - t.re : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [m, hs, htim]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hre' := abs_le.mp hre
      rw [abs_le]; constructor <;> linarith
    have hlen2 : ‖b - m‖ ≤ 3 / 2 := by
      have : b - m = ((3 / 2 - y₀ : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [m, b]; ring
        · simp [m, b]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have ha := hanchor (t₀ + X) (by rw [abs_of_nonneg (by linarith)]; linarith)
    have hm1 := mul_le_mul_of_nonneg_left hlen1 hC0
    have hm2 := mul_le_mul_of_nonneg_left hlen2 hC0
    linarith
  · -- outer side: right at height `t.re` from `Re s = 3/2`
    have htim : t.im = -1 := by
      rcases abs_eq (zero_le_one) |>.mp h3 with h | h <;> [linarith; exact h]
    set b : ℂ := 2 + t.re * I
    have hseg : ∀ z ∈ segment ℝ s b, 1 / 2 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im - t₀| ≤ 1 ∧ xi z ≠ 0 := by
      intro z hz
      obtain ⟨θ, hθ, hzr, hzi⟩ := mem_segment_re_im hz
      have hbre : b.re = 2 := by simp [b]
      have hbim : b.im = t.re := by simp [b]
      rw [hbre, hsre, htim] at hzr; rw [hbim, hsim] at hzi
      have hzi' : z.im = t.re := by rw [hzi]; ring
      have hzr1 : 1 ≤ z.re := by rw [hzr]; nlinarith [hθ.1, hθ.2]
      refine ⟨by linarith, by rw [hzr]; nlinarith [hθ.1, hθ.2], by rw [hzi']; linarith,
        hzeroC z hzr1⟩
    have hl := hlip hseg
    have hlen : ‖b - s‖ ≤ 1 / 2 := by
      have : b - s = ((1 / 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [b, hs, htim]; norm_num
        · simp [b, hs, htim]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    have ha := hanchor t.re (by linarith)
    have hm := mul_le_mul_of_nonneg_left hlen hC0
    linarith


/-- The transform of a super-exponentially decaying function is entire. -/
theorem SuperExpDecay.differentiable_paperFT {g : ℝ → ℂ} (hg : SuperExpDecay g) :
    Differentiable ℂ (paperFT g) := by
  intro z₀
  set F : ℂ → ℝ → ℂ := fun z u => g u * Complex.exp (I * z * u) with hF
  set F' : ℂ → ℝ → ℂ := fun z u => g u * (I * u * Complex.exp (I * z * u)) with hF'
  set bound : ℝ → ℝ := fun u => ‖g u‖ * Real.exp ((|z₀.im| + 2) * |u|) with hbound
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hmeas : ∀ z, AEStronglyMeasurable (F z) volume := fun z =>
    (hg.1.mul (by fun_prop)).aestronglyMeasurable
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := z₀) (bound := bound) hball (Eventually.of_forall hmeas) (hg.integrable_mul_cexp z₀)
    ((hg.1.mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u z hz => ?_) (hg.2 _) (Eventually.of_forall fun u z _ => ?_)
  · exact h.2.differentiableAt
  · -- the bound on the derivative
    have hzim : |z.im| ≤ |z₀.im| + 1 := by
      have := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at this
      have h1 := Complex.abs_im_le_norm (z - z₀)
      rw [Complex.sub_im] at h1
      have := abs_sub_abs_le_abs_sub z.im z₀.im
      linarith
    simp only [hF', hbound]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have he := norm_cexp_I_mul_le_exp hzim u
    have hu : |u| ≤ Real.exp |u| := by
      have := Real.add_one_le_exp |u|; linarith
    calc ‖g u‖ * (|u| * ‖Complex.exp (I * z * u)‖)
        ≤ ‖g u‖ * (Real.exp |u| * Real.exp ((|z₀.im| + 1) * |u|)) := by gcongr
      _ = ‖g u‖ * Real.exp ((|z₀.im| + 2) * |u|) := by
          rw [← Real.exp_add]; congr 2; ring
  · -- the derivative
    have h1 : HasDerivAt (fun z : ℂ => I * z * (u : ℂ)) (I * u) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (u : ℂ)
    have h2 := (h1.cexp).const_mul (g u)
    simp only [hF, hF']
    exact h2.congr_deriv (by ring)

/-! ## The polar shift adapted to the height -/

/-- The odd multiple `(2k+1)π/t₀` of `π/t₀` in `[1/16, 1/8]`. -/
def heightPolarShift (t₀ : ℝ) : ℝ :=
  (2 * ⌈(t₀ / (16 * π) - 1) / 2⌉₊ + 1) * π / t₀

theorem heightPolarShift_mem {t₀ : ℝ} (ht₀ : 101 ≤ t₀) :
    1 / 16 ≤ heightPolarShift t₀ ∧ heightPolarShift t₀ ≤ 1 / 8 := by
  have hpi := Real.pi_pos
  have hpi4 : π < 3.1416 := Real.pi_lt_d4
  have ht0 : 0 < t₀ := by linarith
  set k := ⌈(t₀ / (16 * π) - 1) / 2⌉₊ with hk
  have hk1 : (t₀ / (16 * π) - 1) / 2 ≤ k := Nat.le_ceil _
  have hq : 2 ≤ t₀ / (16 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hk2 : (k : ℝ) < (t₀ / (16 * π) - 1) / 2 + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  unfold heightPolarShift
  rw [← hk]
  constructor
  · rw [le_div_iff₀ ht0]
    have : t₀ / (16 * π) ≤ 2 * k + 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  · rw [div_le_iff₀ ht0]
    have : (2 * k + 1 : ℝ) ≤ t₀ / (8 * π) := by
      have e : t₀ / (8 * π) = 2 * (t₀ / (16 * π)) := by field_simp; ring
      rw [e]; linarith
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith

theorem exp_I_mul_heightPolarShift {t₀ : ℝ} (ht₀ : 101 ≤ t₀) :
    Complex.exp (I * t₀ * heightPolarShift t₀) = -1 := by
  have ht0 : (t₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t₀ ≠ 0)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, heightPolarShift t₀ = (2 * k + 1) * π / t₀ := ⟨_, rfl⟩
  have e : I * (t₀ : ℂ) * ((heightPolarShift t₀ : ℝ) : ℂ) = (k : ℂ) * (2 * π * I) + π * I := by
    rw [hk]; push_cast; field_simp
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]

/-- Near the height `t₀`, the polar symbol is at least `1` in modulus. -/
theorem one_le_norm_polarSymbol {t₀ : ℝ} (ht₀ : 101 ≤ t₀) {z : ℂ} (hre : |z.re - t₀| ≤ 1) :
    1 ≤ ‖polarSymbol (heightPolarShift t₀) z‖ := by
  set s := heightPolarShift t₀
  obtain ⟨hs1, hs2⟩ := heightPolarShift_mem ht₀
  set w : ℂ := z - t₀ with hw
  have hz : z = t₀ + w := by rw [hw]; ring
  have hsplit : polarSymbol s z = -Complex.cos (w * s) - (Real.cosh (s / 2) : ℂ) := by
    unfold polarSymbol
    have e1 : Complex.exp (I * z * s) = -Complex.exp (w * s * I) := by
      rw [hz, show I * ((t₀ : ℂ) + w) * s = I * t₀ * s + w * s * I by ring, Complex.exp_add,
        exp_I_mul_heightPolarShift ht₀]; ring
    have e2 : Complex.exp (-(I * z * s)) = -Complex.exp (-(w * s) * I) := by
      rw [hz, show -(I * ((t₀ : ℂ) + w) * s) = -(I * t₀ * s) + -(w * s) * I by ring,
        Complex.exp_add, Complex.exp_neg, exp_I_mul_heightPolarShift ht₀]; ring
    rw [e1, e2, Complex.cos]; ring
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (w * s).re := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (w * s).im := ⟨_, rfl⟩
  have hc : Complex.cos (w * s) = (Real.cos x : ℂ) * (Real.cosh y : ℂ) -
      (Real.sin x : ℂ) * (Real.sinh y : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im (w * s), ← hx, ← hy]
    rw [Complex.cos_add_mul_I, Complex.ofReal_cos, Complex.ofReal_cosh, Complex.ofReal_sin,
      Complex.ofReal_sinh]
  have hre' : ((-Complex.cos (w * s) - (Real.cosh (s / 2) : ℂ))).re =
      -(Real.cos ((w * s).re) * Real.cosh ((w * s).im)) - Real.cosh (s / 2) := by
    rw [hc, ← hx, ← hy]
    simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hws : |(w * (s : ℂ)).re| ≤ 1 / 8 := by
    have : (w * (s : ℂ)).re = w.re * s := by simp
    rw [this, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
    have : |w.re| ≤ 1 := by rw [hw]; simpa using hre
    nlinarith [abs_nonneg w.re]
  have hcos : 0 ≤ Real.cos ((w * s).re) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> linarith [(abs_le.mp hws).1, (abs_le.mp hws).2, Real.pi_gt_three]
  have hcosh : 0 < Real.cosh ((w * s).im) := Real.cosh_pos _
  have hcosh2 : 1 ≤ Real.cosh (s / 2) := Real.one_le_cosh _
  rw [hsplit]
  calc (1 : ℝ) ≤ -((-Complex.cos (w * s) - (Real.cosh (s / 2) : ℂ))).re := by
        rw [hre']; nlinarith
    _ ≤ |((-Complex.cos (w * s) - (Real.cosh (s / 2) : ℂ))).re| := neg_le_abs _
    _ ≤ _ := Complex.abs_re_le_norm _

/-! ## The cluster setup -/


/-- A height `t₀`, a depth `δ₀`, and the frame parameters `X ∈ [½, ¾]`, `y₀ ∈ [δ₀/4, δ₀/2]`
chosen by the forward-difference selection over the window zeros. -/
structure ClusterSetup where
  t₀ : ℝ
  X : ℝ
  y₀ : ℝ
  δ₀ : ℝ
  ht₀ : 101 ≤ t₀
  hX1 : 1 / 2 ≤ X
  hX2 : X ≤ 3 / 4
  hδ₀ : 0 < δ₀
  hδ₁ : δ₀ ≤ 1 / 2
  hy₀ : δ₀ / 4 ≤ y₀
  hy₁ : y₀ ≤ δ₀ / 2
  hselX : (1 / (8 * Real.exp 1)) ^ windowCount t₀ ≤
    ∏ q ∈ windowCopySet t₀, abs (X - |(q.1 : ℂ).im - t₀|)
  hsely : (δ₀ / (8 * Real.exp 1)) ^ windowCount t₀ ≤
    ∏ q ∈ windowCopySet t₀, abs (y₀ - |(q.1 : ℂ).re - 1 / 2|)

/-- Every height and depth admit a cluster setup. -/
theorem exists_clusterSetup {t₀ δ₀ : ℝ} (ht₀ : 101 ≤ t₀) (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1 / 2) :
    ∃ C : ClusterSetup, C.t₀ = t₀ ∧ C.δ₀ = δ₀ := by
  obtain ⟨X, hX, hselX⟩ := HTGeometry.exists_mem_Icc_prod_abs_sub_ge (windowCopySet t₀)
    (fun q => |(q.1 : ℂ).im - t₀|) (1 / 2) (L := 1 / 4) (by norm_num)
  obtain ⟨y₀, hy, hsely⟩ := HTGeometry.exists_mem_Icc_prod_abs_sub_ge (windowCopySet t₀)
    (fun q => |(q.1 : ℂ).re - 1 / 2|) (δ₀ / 4) (L := δ₀ / 4) (by positivity)
  refine ⟨⟨t₀, X, y₀, δ₀, ht₀, hX.1, by linarith [hX.2], hδ₀, hδ₁, hy.1, by linarith [hy.2],
    ?_, ?_⟩, rfl, rfl⟩
  · refine le_trans (le_of_eq ?_) hselX
    congr 1; field_simp; ring
  · refine le_trans (le_of_eq ?_) hsely
    congr 1; field_simp; ring

namespace ClusterSetup

variable (C : ClusterSetup)

/-- The nodes. -/
abbrev nodes : Finset XiDivisorSupport := nodeSet C.t₀ C.X C.y₀

/-- The node divisor. -/
abbrev L : List (ℂ × ℕ) := nodeList C.t₀ C.X C.y₀

/-- Riemann's kernel divided by the node divisor. -/
abbrev K : ℝ → ℂ := multiResolvent C.L Φ

/-- The node shift `κ = 1/(8(N+1))`. -/
def κ : ℝ := 1 / (8 * (windowCount C.t₀ + 1))

theorem κ_pos : 0 < C.κ := by unfold κ; positivity

theorem κ_le : C.κ ≤ 1 / 8 := by
  unfold κ
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (0 : ℝ) ≤ windowCount C.t₀ := Nat.cast_nonneg _
  linarith

theorem κ_mul_count_le : (windowCount C.t₀ : ℝ) * C.κ ≤ 1 / 8 := by
  unfold κ
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The lower rectangle `[t₀ - X, t₀ + X] × [-1, -y₀]`. -/
def lowRect : Set ℂ := Rectangle (((C.t₀ - C.X : ℝ) : ℂ) - I) (((C.t₀ + C.X : ℝ) : ℂ) - C.y₀ * I)

/-- The upper rectangle `[t₀ - X, t₀ + X] × [y₀, 1]`. -/
def upRect : Set ℂ := Rectangle (((C.t₀ - C.X : ℝ) : ℂ) + C.y₀ * I) (((C.t₀ + C.X : ℝ) : ℂ) + I)

theorem y₀_pos : 0 < C.y₀ := by have := C.hδ₀; have := C.hy₀; linarith

theorem y₀_le : C.y₀ ≤ 1 / 4 := by have := C.hδ₁; have := C.hy₁; linarith

theorem mem_lowRect {t : ℂ} : t ∈ C.lowRect ↔
    C.t₀ - C.X ≤ t.re ∧ t.re ≤ C.t₀ + C.X ∧ -1 ≤ t.im ∧ t.im ≤ -C.y₀ := by
  unfold lowRect
  rw [mem_Rect (by simp; linarith [C.hX1]) (by simp; linarith [C.y₀_le])]
  simp

theorem mem_upRect {t : ℂ} : t ∈ C.upRect ↔
    C.t₀ - C.X ≤ t.re ∧ t.re ≤ C.t₀ + C.X ∧ C.y₀ ≤ t.im ∧ t.im ≤ 1 := by
  unfold upRect
  rw [mem_Rect (by simp; linarith [C.hX1]) (by simp; linarith [C.y₀_le])]
  simp

theorem lowRect_mem_nhds {t : ℂ} (h1 : |t.re - C.t₀| < C.X) (h2 : -1 < t.im) (h3 : t.im < -C.y₀) :
    C.lowRect ∈ 𝓝 t := by
  unfold lowRect
  rw [rectangle_mem_nhds_iff]
  have hre := abs_lt.mp h1
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.mul_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self]
    rw [Set.uIoo_of_le (by linarith [C.hX1])]
    exact ⟨by linarith, by linarith⟩
  · simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub, Complex.mul_im,
      Complex.I_re, mul_zero, mul_one, Complex.ofReal_re]
    rw [Set.uIoo_of_le (by linarith [C.y₀_le])]
    exact ⟨by linarith, by linarith⟩

theorem upRect_mem_nhds {t : ℂ} (h1 : |t.re - C.t₀| < C.X) (h2 : C.y₀ < t.im) (h3 : t.im < 1) :
    C.upRect ∈ 𝓝 t := by
  unfold upRect
  rw [rectangle_mem_nhds_iff]
  have hre := abs_lt.mp h1
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.mul_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self]
    rw [Set.uIoo_of_le (by linarith [C.hX1])]
    exact ⟨by linarith, by linarith⟩
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add, Complex.mul_im,
      Complex.I_re, mul_zero, mul_one, add_zero, Complex.ofReal_re]
    rw [Set.uIoo_of_le (by linarith [C.y₀_le])]
    exact ⟨by linarith, by linarith⟩

theorem hnoX : ∀ q ∈ windowCopySet C.t₀, |(q.1 : ℂ).im - C.t₀| ≠ C.X := by
  intro q hq h
  have hpos : 0 < ∏ q ∈ windowCopySet C.t₀, abs (C.X - |(q.1 : ℂ).im - C.t₀|) :=
    lt_of_lt_of_le (by have := Real.exp_pos 1; positivity) C.hselX
  have h0 : ∏ q ∈ windowCopySet C.t₀, abs (C.X - |(q.1 : ℂ).im - C.t₀|) = 0 :=
    Finset.prod_eq_zero hq (by rw [h, sub_self, abs_zero])
  linarith

theorem hnoy : ∀ q ∈ windowCopySet C.t₀, |(q.1 : ℂ).re - 1 / 2| ≠ C.y₀ := by
  intro q hq h
  have hpos : 0 < ∏ q ∈ windowCopySet C.t₀, abs (C.y₀ - |(q.1 : ℂ).re - 1 / 2|) :=
    lt_of_lt_of_le (by have := Real.exp_pos 1; have := C.hδ₀; positivity) C.hsely
  have h0 : ∏ q ∈ windowCopySet C.t₀, abs (C.y₀ - |(q.1 : ℂ).re - 1 / 2|) = 0 :=
    Finset.prod_eq_zero hq (by rw [h, sub_self, abs_zero])
  linarith

theorem firstCopy_mem_window {ρ : XiDivisorSupport} (hρ : |(ρ : ℂ).im - C.t₀| < 2) :
    firstCopy ρ ∈ windowCopySet C.t₀ :=
  mem_windowCopySet.mpr hρ

/-- A node lies strictly inside the frame. -/
theorem node_coords {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) :
    |(gammaOf (ρ : ℂ)).re - C.t₀| < C.X ∧ C.y₀ < |(gammaOf (ρ : ℂ)).im| ∧
      |(gammaOf (ρ : ℂ)).im| < 1 / 2 := by
  obtain ⟨h1, h2⟩ := (mem_nodeSet (by linarith [C.hX2])).mp hρ
  rw [WeilEF.gammaOf_re, WeilEF.gammaOf_im]
  refine ⟨h1, by rw [abs_sub_comm]; exact h2, ?_⟩
  have := abs_gammaOf_divisorSupport_im_lt ρ
  rwa [WeilEF.gammaOf_im] at this

/-- A zero of `Ξ` on one of the closed rectangles is a node. -/
theorem zero_in_rect_is_node {z : ℂ} (hz : riemannXiHat z = 0)
    (hR : z ∈ C.lowRect ∨ z ∈ C.upRect) : ∃ ρ ∈ C.nodes, gammaOf (ρ : ℂ) = z := by
  obtain ⟨ρ, rfl⟩ := exists_divisorSupport_of_riemannXiHat_eq_zero hz
  refine ⟨ρ, ?_, rfl⟩
  have hre : |(gammaOf (ρ : ℂ)).re - C.t₀| ≤ C.X ∧ C.y₀ ≤ |(gammaOf (ρ : ℂ)).im| := by
    rcases hR with h | h
    · obtain ⟨a, b, c, d⟩ := C.mem_lowRect.mp h
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by rw [abs_of_neg (by linarith [C.y₀_pos])]; linarith⟩
    · obtain ⟨a, b, c, d⟩ := C.mem_upRect.mp h
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, by rw [abs_of_pos (by linarith [C.y₀_pos])]; linarith⟩
  rw [WeilEF.gammaOf_re, WeilEF.gammaOf_im] at hre
  have hwin : |(ρ : ℂ).im - C.t₀| < 2 := by linarith [hre.1, C.hX2]
  have hc := C.firstCopy_mem_window hwin
  have hX' : |(ρ : ℂ).im - C.t₀| ≠ C.X := C.hnoX _ hc
  have hy' : |(ρ : ℂ).re - 1 / 2| ≠ C.y₀ := C.hnoy _ hc
  rw [mem_nodeSet (by linarith [C.hX2])]
  refine ⟨lt_of_le_of_ne hre.1 hX', ?_⟩
  have : |1 / 2 - (ρ : ℂ).re| = |(ρ : ℂ).re - 1 / 2| := abs_sub_comm _ _
  rw [this] at hre
  exact lt_of_le_of_ne hre.2 (Ne.symm hy')

/-! ### The divided kernel on the rectangles -/

theorem K_spec : SuperExpDecay C.K ∧
    (∀ z, divisorEval C.L z * paperFT C.K z = riemannXiHat z) ∧
    (∀ ρ ∈ C.nodes, paperFT C.K (gammaOf (ρ : ℂ)) ≠ 0) := by
  obtain ⟨h1, h2, h3, -⟩ := multiResolvent_spec C.L superExpDecay_riemannPhiKernel
    (divisorData_nodeList C.t₀ C.X C.y₀)
  refine ⟨h1, fun z => h2 z, fun ρ hρ => ?_⟩
  exact h3 (gammaOf (ρ : ℂ), divMult ρ) (mem_nodeList.mpr ⟨ρ, hρ, rfl⟩)

theorem divisorEval_ne_zero_of_not_node {z : ℂ} (hz : ∀ ρ ∈ C.nodes, z ≠ gammaOf (ρ : ℂ)) :
    divisorEval C.L z ≠ 0 := by
  refine divisorEval_ne_zero fun p hp => ?_
  obtain ⟨ρ, hρ, rfl⟩ := mem_nodeList.mp hp
  exact hz ρ hρ

theorem Khat_ne_zero_on_rect {t : ℂ} (hR : t ∈ C.lowRect ∨ t ∈ C.upRect) :
    paperFT C.K t ≠ 0 := by
  obtain ⟨-, hprod, hnode⟩ := C.K_spec
  by_cases hn : ∃ ρ ∈ C.nodes, t = gammaOf (ρ : ℂ)
  · obtain ⟨ρ, hρ, rfl⟩ := hn
    exact hnode ρ hρ
  · push Not at hn
    intro h0
    have hXi : riemannXiHat t = 0 := by rw [← hprod t, h0, mul_zero]
    obtain ⟨ρ, hρ, hγ⟩ := C.zero_in_rect_is_node hXi hR
    exact hn ρ hρ hγ.symm

theorem onFrame_of_border_low {t : ℂ}
    (ht : t ∈ RectangleBorder (((C.t₀ - C.X : ℝ) : ℂ) - I) (((C.t₀ + C.X : ℝ) : ℂ) - C.y₀ * I)) :
    OnFrame C.t₀ C.X C.y₀ t := by
  have hy := C.y₀_pos
  unfold RectangleBorder at ht
  simp only [Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at ht
  unfold OnFrame
  rcases ht with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
  · right; right; simp at h; rw [h]; norm_num
  · left; simp at h; rw [h]; simp; linarith [C.hX1]
  · right; left; simp at h; rw [h, abs_neg, abs_of_pos hy]
  · left; simp at h; rw [h]; simp; linarith [C.hX1]

theorem onFrame_of_border_up {t : ℂ}
    (ht : t ∈ RectangleBorder (((C.t₀ - C.X : ℝ) : ℂ) + C.y₀ * I) (((C.t₀ + C.X : ℝ) : ℂ) + I)) :
    OnFrame C.t₀ C.X C.y₀ t := by
  have hy := C.y₀_pos
  unfold RectangleBorder at ht
  simp only [Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff] at ht
  unfold OnFrame
  rcases ht with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
  · right; left; simp at h; rw [h, abs_of_pos hy]
  · left; simp at h; rw [h]; simp; linarith [C.hX1]
  · right; right; simp at h; rw [h]; norm_num
  · left; simp at h; rw [h]; simp; linarith [C.hX1]

theorem onFrame_conj {t : ℂ} (h : OnFrame C.t₀ C.X C.y₀ t) :
    OnFrame C.t₀ C.X C.y₀ ((starRingEnd ℂ) t) := by
  unfold OnFrame at *
  simpa using h

theorem not_node_of_onFrame {t : ℂ} (h : OnFrame C.t₀ C.X C.y₀ t) :
    ∀ ρ ∈ C.nodes, t ≠ gammaOf (ρ : ℂ) := by
  intro ρ hρ e
  obtain ⟨h1, h2, h3⟩ := C.node_coords hρ
  rw [← e] at h1 h2 h3
  rcases h with h | h | h <;> linarith

/-- The lower bound for `|K̂|` on the frames. -/
def Lh : ℝ := Real.exp (frameLogLower C.t₀) * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀

theorem Lh_pos : 0 < C.Lh := by
  unfold Lh; have := C.hδ₀; have := Real.exp_pos 1; positivity

/-- **`|K̂|` on the frame.** At every point of the frame of either rectangle,
`|K̂(t)| ≥ e^{L(t₀)} (δ₀/(16e))^N`. -/
theorem Lh_le_norm_Khat {t : ℂ} (hR : t ∈ C.lowRect ∨ t ∈ C.upRect)
    (hframe : OnFrame C.t₀ C.X C.y₀ t) : C.Lh ≤ ‖paperFT C.K t‖ := by
  obtain ⟨-, hprod, -⟩ := C.K_spec
  have hnn := C.not_node_of_onFrame hframe
  have hdiv := C.divisorEval_ne_zero_of_not_node hnn
  -- the reflected point on the lower frame
  set t' : ℂ := if t.im ≤ 0 then t else (starRingEnd ℂ) t with ht'
  have ht'R : t' ∈ C.lowRect := by
    rcases hR with h | h
    · have := (C.mem_lowRect.mp h).2.2.2
      have hle : t.im ≤ 0 := by linarith [C.y₀_pos]
      rw [ht', if_pos hle]; exact h
    · obtain ⟨a, b, c, d⟩ := C.mem_upRect.mp h
      have hle : ¬ t.im ≤ 0 := by linarith [C.y₀_pos]
      rw [ht', if_neg hle]
      exact C.mem_lowRect.mpr ⟨by simpa using a, by simpa using b, by simp; linarith,
        by simp; linarith⟩
  have ht'F : OnFrame C.t₀ C.X C.y₀ t' := by
    rw [ht']; split_ifs
    · exact hframe
    · exact C.onFrame_conj hframe
  obtain ⟨a', b', c', d'⟩ := C.mem_lowRect.mp ht'R
  have hXi : ‖riemannXiHat t‖ = ‖windowQuotient C.t₀ (1 / 2 + I * t')‖ *
      ∏ q ∈ windowCopySet C.t₀, ‖t - gammaOf (q.1 : ℂ)‖ := by
    rw [ht']
    split_ifs with hle
    · exact norm_riemannXiHat_eq_window C.t₀ t
    · rw [← Complex.norm_conj (riemannXiHat t), ← riemannXiHat_conj,
        norm_riemannXiHat_eq_window C.t₀]
      congr 1
      have e : ∀ q : XiZeroCopy, ‖(starRingEnd ℂ) t - gammaOf (q.1 : ℂ)‖ =
          ‖t - (starRingEnd ℂ) (gammaOf (q.1 : ℂ))‖ := by
        intro q
        rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
      simp_rw [e]
      exact prod_windowCopySet_conj C.t₀ (fun w => ‖t - w‖)
  -- the window quotient on the lower frame
  have hlog := log_norm_windowQuotient_frame_ge (t₀ := C.t₀) (X := C.X) (y₀ := C.y₀)
    (by linarith [C.ht₀]) C.hX1 C.hX2 C.y₀_pos C.y₀_le C.hnoX C.hnoy
    (abs_le.mpr ⟨by linarith, by linarith⟩) c' d' ht'F
  have hW0 : windowQuotient C.t₀ (1 / 2 + I * t') ≠ 0 := by
    have hxi : xi (1 / 2 + I * t') ≠ 0 := by
      intro h0
      have hz : riemannXiHat t' = 0 := by rw [riemannXiHat_eq_xi]; exact h0
      obtain ⟨ρ, hρ, hγ⟩ := C.zero_in_rect_is_node hz (Or.inl ht'R)
      exact C.not_node_of_onFrame ht'F ρ hρ hγ.symm
    exact div_ne_zero hxi (windowPoly_ne_zero hxi)
  have hW : Real.exp (frameLogLower C.t₀) ≤ ‖windowQuotient C.t₀ (1 / 2 + I * t')‖ := by
    rw [← Real.exp_log (norm_pos_iff.mpr hW0)]
    exact Real.exp_le_exp.mpr hlog
  -- split off the node divisor
  rw [prod_window_split C.t₀ C.X C.y₀ t] at hXi
  have hK : ‖paperFT C.K t‖ = ‖windowQuotient C.t₀ (1 / 2 + I * t')‖ *
      ∏ q ∈ (windowCopySet C.t₀).filter (fun q => q.1 ∉ nodeSet C.t₀ C.X C.y₀),
        ‖t - gammaOf (q.1 : ℂ)‖ := by
    have h := congrArg norm (hprod t)
    rw [norm_mul, hXi] at h
    have hd : 0 < ‖divisorEval C.L t‖ := norm_pos_iff.mpr hdiv
    have : ‖divisorEval C.L t‖ * ‖paperFT C.K t‖ = ‖divisorEval C.L t‖ *
        (‖windowQuotient C.t₀ (1 / 2 + I * t')‖ *
          ∏ q ∈ (windowCopySet C.t₀).filter (fun q => q.1 ∉ nodeSet C.t₀ C.X C.y₀),
            ‖t - gammaOf (q.1 : ℂ)‖) := by rw [h]; ring
    exact mul_left_cancel₀ hd.ne' this
  have hrest := prod_norm_sub_ge_on_frame C.hX1 C.hX2 C.hδ₀ C.hδ₁ C.hy₁ C.hselX C.hsely hframe
    (S := (windowCopySet C.t₀).filter (fun q => q.1 ∉ nodeSet C.t₀ C.X C.y₀))
    (Finset.filter_subset _ _)
  rw [hK]
  unfold Lh
  exact mul_le_mul hW hrest (by have := C.hδ₀; have := Real.exp_pos 1; positivity)
    (norm_nonneg _)

/-! ### Exponential nodes -/

theorem half_norm_le_norm_exp_sub_one {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : ‖w‖ / 2 ≤ ‖Complex.exp w - 1‖ := by
  have h := Complex.norm_exp_sub_one_sub_id_le (by linarith : ‖w‖ ≤ 1)
  have h2 : ‖w‖ ≤ ‖Complex.exp w - 1‖ + ‖Complex.exp w - 1 - w‖ := by
    calc ‖w‖ = ‖(Complex.exp w - 1) - (Complex.exp w - 1 - w)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  nlinarith [norm_nonneg w]

/-- No aliasing: `e^{iκt} = e^{iκt'}` with `|t - t'| ≤ 3` forces `t = t'`. -/
theorem eq_of_exp_eq {t t' : ℂ} (hd : ‖t - t'‖ ≤ 3)
    (he : Complex.exp (I * t * C.κ) = Complex.exp (I * t' * C.κ)) : t = t' := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hκ := C.κ_pos
  have hκ8 := C.κ_le
  have e : (t - t') * C.κ = n * (2 * π) := by
    have h' : I * ((t - t') * C.κ - n * (2 * π)) = 0 := by linear_combination hn
    rcases mul_eq_zero.mp h' with h | h
    · exact absurd h I_ne_zero
    · exact sub_eq_zero.mp h
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    have h2 := congrArg norm e
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ,
      Complex.norm_intCast, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos] at h2
    have h3 : ‖t - t'‖ * C.κ ≤ 3 / 8 := by nlinarith [norm_nonneg (t - t')]
    nlinarith [Real.pi_gt_three]
  rw [hn0] at e
  simp at e
  rcases e with e | e
  · exact sub_eq_zero.mp e
  · exact absurd e (by exact_mod_cast hκ.ne')

theorem norm_exp_I_mul_κ (t : ℂ) : ‖Complex.exp (I * t * C.κ)‖ = Real.exp (-(t.im * C.κ)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- The exponential nodes `ω_ρ = e^{iκγ_ρ}`. -/
def ω (ρ : XiDivisorSupport) : ℂ := Complex.exp (I * gammaOf (ρ : ℂ) * C.κ)

theorem node_norm_sub_le {ρ ρ' : XiDivisorSupport} (hρ : ρ ∈ C.nodes) (hρ' : ρ' ∈ C.nodes) :
    ‖gammaOf (ρ : ℂ) - gammaOf (ρ' : ℂ)‖ ≤ 3 := by
  obtain ⟨a, -, c⟩ := C.node_coords hρ
  obtain ⟨a', -, c'⟩ := C.node_coords hρ'
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have := C.hX2
  have h1 : |(gammaOf (ρ : ℂ)).re - (gammaOf (ρ' : ℂ)).re| ≤ 3 / 2 := by
    rw [abs_lt] at a a'; rw [abs_le]; constructor <;> linarith [a.1, a.2, a'.1, a'.2]
  have h2 : |(gammaOf (ρ : ℂ)).im - (gammaOf (ρ' : ℂ)).im| ≤ 1 := by
    rw [abs_lt] at c c'; rw [abs_le]; constructor <;> linarith [c.1, c.2, c'.1, c'.2]
  linarith

theorem ω_injOn : Set.InjOn C.ω C.nodes := by
  intro ρ hρ ρ' hρ' h
  exact Subtype.ext (gammaOf_injective (C.eq_of_exp_eq (C.node_norm_sub_le hρ hρ') h))

theorem rect_norm_sub_node_le {t : ℂ} (hR : t ∈ C.lowRect ∨ t ∈ C.upRect) {ρ : XiDivisorSupport}
    (hρ : ρ ∈ C.nodes) : ‖t - gammaOf (ρ : ℂ)‖ ≤ 3 := by
  obtain ⟨a, -, c⟩ := C.node_coords hρ
  have hX := C.hX2
  have ht : |t.re - C.t₀| ≤ C.X ∧ |t.im| ≤ 1 := by
    rcases hR with h | h
    · obtain ⟨p, q, r, u⟩ := C.mem_lowRect.mp h
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith [C.y₀_pos]⟩⟩
    · obtain ⟨p, q, r, u⟩ := C.mem_upRect.mp h
      exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith [C.y₀_pos], by linarith⟩⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |t.re - (gammaOf (ρ : ℂ)).re| ≤ 3 / 2 := by
    have ht1 := abs_le.mp ht.1
    rw [abs_lt] at a; rw [abs_le]; constructor <;> linarith [a.1, a.2, ht1.1, ht1.2]
  have h2 : |t.im - (gammaOf (ρ : ℂ)).im| ≤ 3 / 2 := by
    have := abs_sub t.im (gammaOf (ρ : ℂ)).im; linarith [ht.2]
  linarith

/-- The nodes in the upper rectangle are exactly those with `Im γ > 0`. -/
theorem node_mem_rect {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) :
    (0 < (gammaOf (ρ : ℂ)).im → C.upRect ∈ 𝓝 (gammaOf (ρ : ℂ)) ∧
        gammaOf (ρ : ℂ) ∉ C.lowRect) ∧
      ((gammaOf (ρ : ℂ)).im < 0 → C.lowRect ∈ 𝓝 (gammaOf (ρ : ℂ)) ∧
        gammaOf (ρ : ℂ) ∉ C.upRect) := by
  obtain ⟨a, b, c⟩ := C.node_coords hρ
  refine ⟨fun hpos => ⟨?_, ?_⟩, fun hneg => ⟨?_, ?_⟩⟩
  · rw [abs_of_pos hpos] at b c
    exact C.upRect_mem_nhds a b (by linarith)
  · intro h; have := (C.mem_lowRect.mp h).2.2.2; linarith [C.y₀_pos]
  · rw [abs_of_neg hneg] at b c
    exact C.lowRect_mem_nhds a (by linarith) (by linarith)
  · intro h; have := (C.mem_upRect.mp h).2.2.1; linarith [C.y₀_pos]

theorem node_im_ne_zero {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) : (gammaOf (ρ : ℂ)).im ≠ 0 := by
  obtain ⟨-, b, -⟩ := C.node_coords hρ
  intro h; rw [h, abs_zero] at b; linarith [C.y₀_pos]

/-! ### The interpolant -/

/-- The polar symbol at the adapted shift. -/
def Pp (z : ℂ) : ℂ := polarSymbol (heightPolarShift C.t₀) z

theorem differentiable_Pp : Differentiable ℂ C.Pp := by
  unfold Pp polarSymbol; fun_prop

theorem one_le_norm_Pp {t : ℂ} (hR : t ∈ C.lowRect ∨ t ∈ C.upRect) : 1 ≤ ‖C.Pp t‖ := by
  apply one_le_norm_polarSymbol C.ht₀
  have hX := C.hX2
  rcases hR with h | h
  · obtain ⟨a, b, -, -⟩ := C.mem_lowRect.mp h; rw [abs_le]; constructor <;> linarith
  · obtain ⟨a, b, -, -⟩ := C.mem_upRect.mp h; rw [abs_le]; constructor <;> linarith

/-- The target values `±i/(P K̂)` at the nodes: `+i` in the upper rectangle, `-i` in the lower. -/
def r (ρ : XiDivisorSupport) : ℂ :=
  (if 0 < (gammaOf (ρ : ℂ)).im then I else -I) /
    (C.Pp (gammaOf (ρ : ℂ)) * paperFT C.K (gammaOf (ρ : ℂ)))

/-- The interpolating polynomial in `w = e^{iκz}`. -/
def Q : ℂ[X] := Lagrange.interpolate C.nodes C.ω C.r

theorem Q_eval_node {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) : C.Q.eval (C.ω ρ) = C.r ρ :=
  Lagrange.eval_interpolate_at_node C.r C.ω_injOn hρ

/-- The node count is at most the window count. -/
theorem card_nodes_le : C.nodes.card ≤ windowCount C.t₀ := by
  have hsub : C.nodes.map ⟨firstCopy, fun a b h => by
      simp only [firstCopy] at h; exact (Sigma.mk.inj_iff.mp h).1⟩ ⊆ windowCopySet C.t₀ := by
    intro q hq
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨h1, -⟩ := (mem_nodeSet (by linarith [C.hX2])).mp hρ
    exact C.firstCopy_mem_window (by linarith [C.hX2])
  have := Finset.card_le_card hsub
  rwa [Finset.card_map] at this

theorem natDegree_Q_le : C.Q.natDegree ≤ windowCount C.t₀ := by
  have h : C.Q.degree < C.nodes.card := by
    unfold Q; exact Lagrange.degree_interpolate_lt C.r C.ω_injOn
  have hcard := C.card_nodes_le
  rcases eq_or_ne C.Q 0 with h0 | h0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  · rw [degree_eq_natDegree h0] at h
    have : C.Q.natDegree < C.nodes.card := by exact_mod_cast h
    omega

/-- The contour bound for one rectangle. -/
def Mb : ℝ := 4 / (C.Lh * C.y₀ * (C.κ / 4) ^ windowCount C.t₀ *
  (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀)

theorem Mb_pos : 0 < C.Mb := by
  unfold Mb
  have := C.Lh_pos; have := C.y₀_pos; have := C.κ_pos; have := C.hδ₀; have := Real.exp_pos 1
  positivity

theorem one_sub_exp_ge {u : ℝ} (hu : |u| ≤ 1) : |u| / 2 ≤ |1 - Real.exp (-u)| := by
  rcases le_or_gt 0 u with h | h
  · rw [abs_of_nonneg h]
    have h1 := Real.add_one_le_exp u
    have h2 : Real.exp (-u) = (Real.exp u)⁻¹ := Real.exp_neg u
    have hpos := Real.exp_pos u
    have h3 : Real.exp (-u) ≤ 1 / (1 + u) := by
      rw [h2, ← one_div]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have h4 : 1 / (1 + u) ≤ 1 - u / 2 := by
      rw [div_le_iff₀ (by linarith)]; rw [abs_of_nonneg h] at hu; nlinarith
    rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_neg h]
    have h1 := Real.add_one_le_exp (-u)
    rw [abs_of_neg (by linarith)]; linarith

open scoped Classical in
/-- **The interior barycentric sum of one rectangle is at most `Mb`.** -/
theorem norm_sum_inside_le {z w : ℂ} (hzw : z.re ≤ w.re) (hzw' : z.im ≤ w.im) (c : ℂ)
    (hc : ‖c‖ = 1) (hR : ∀ t ∈ Rectangle z w, t ∈ C.lowRect ∨ t ∈ C.upRect)
    (hIm : ∀ t ∈ Rectangle z w, C.y₀ ≤ |t.im|)
    (hB : ∀ t ∈ RectangleBorder z w, OnFrame C.t₀ C.X C.y₀ t)
    (hnode : ∀ ρ ∈ C.nodes, Rectangle z w ∈ 𝓝 (gammaOf (ρ : ℂ)) ∨
      gammaOf (ρ : ℂ) ∉ Rectangle z w)
    (hsgn : ∀ ρ ∈ C.nodes, gammaOf (ρ : ℂ) ∈ Rectangle z w →
      C.r ρ = c / (C.Pp (gammaOf (ρ : ℂ)) * paperFT C.K (gammaOf (ρ : ℂ))))
    (hdim : |w.re - z.re| + |w.im - z.im| ≤ 5 / 2) (hne : C.nodes.Nonempty) (x : ℝ) :
    ‖∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle z w),
        Lagrange.nodalWeight C.nodes C.ω ρ * (Complex.exp (I * x * C.κ) - C.ω ρ)⁻¹ * C.r ρ‖ ≤
      C.Mb := by
  classical
  obtain ⟨hK, -, -⟩ := C.K_spec
  have hKc := hK.continuous_paperFT
  have hKd := hK.differentiable_paperFT
  set G : ℂ → ℂ := fun t => c / (C.Pp t * paperFT C.K t) with hG
  set U : Set ℂ := (fun t => C.Pp t * paperFT C.K t) ⁻¹' {0}ᶜ with hU
  have hUo : IsOpen U :=
    ((C.differentiable_Pp.continuous).mul hKc).isOpen_preimage _ isOpen_compl_singleton
  have hRU : Rectangle z w ⊆ U := by
    intro t ht
    have h1 := C.one_le_norm_Pp (hR t ht)
    have h2 := C.Khat_ne_zero_on_rect (hR t ht)
    exact mul_ne_zero (fun h => by rw [h, norm_zero] at h1; linarith) h2
  have hGd : DifferentiableOn ℂ G U := by
    refine (differentiableOn_const c).div ((C.differentiable_Pp.mul hKd).differentiableOn)
      fun t ht => ht
  have hκ0 : (C.κ : ℝ) ≠ 0 := C.κ_pos.ne'
  have huniq : ∀ ρ ∈ C.nodes, ∀ t ∈ Rectangle z w,
      Complex.exp (I * t * C.κ) = Complex.exp (I * gammaOf (ρ : ℂ) * C.κ) → t = gammaOf (ρ : ℂ) :=
    fun ρ hρ t ht he => C.eq_of_exp_eq (C.rect_norm_sub_node_le (hR t ht) hρ) he
  have hxR : ∀ t ∈ Rectangle z w, Complex.exp (I * t * C.κ) ≠ Complex.exp (I * x * C.κ) := by
    intro t ht he
    have h1 := congrArg norm he
    rw [C.norm_exp_I_mul_κ, C.norm_exp_I_mul_κ] at h1
    have h2 := Real.exp_injective h1
    simp only [Complex.ofReal_im, zero_mul, neg_zero, neg_eq_zero, mul_eq_zero] at h2
    have hy := hIm t ht
    rcases h2 with h | h
    · rw [h, abs_zero] at hy; linarith [C.y₀_pos]
    · exact hκ0 h
  have hcont := HTGeometry.sum_expNodalWeight_inside_eq_rectangleIntegral (s := C.nodes)
    (v := fun ρ => gammaOf (ρ : ℂ)) hκ0 C.ω_injOn hne hUo hRU hGd hzw hzw' hnode huniq hxR
  have hsum_eq : ∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle z w),
      Lagrange.nodalWeight C.nodes C.ω ρ * (Complex.exp (I * x * C.κ) - C.ω ρ)⁻¹ * C.r ρ =
      ∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle z w),
        Lagrange.nodalWeight C.nodes (fun i => Complex.exp (I * gammaOf (i : ℂ) * C.κ)) ρ *
          (Complex.exp (I * x * C.κ) - Complex.exp (I * gammaOf (ρ : ℂ) * C.κ))⁻¹ *
            G (gammaOf (ρ : ℂ)) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    obtain ⟨hρn, hρR⟩ := Finset.mem_filter.mp hρ
    rw [hsgn ρ hρn hρR]
    rfl
  rw [hsum_eq, hcont]
  refine (HTGeometry.norm_rectangleIntegral'_le (M := C.Mb * (Real.pi / (5 / 2))) ?_).trans ?_
  · -- the integrand on the border
    intro t ht
    have htR : t ∈ Rectangle z w := rectangleBorder_subset_rectangle z w ht
    have hFr := hB t ht
    have hRR := hR t htR
    have hP := C.one_le_norm_Pp hRR
    have hKt := C.Lh_le_norm_Khat hRR hFr
    have hLh := C.Lh_pos
    have hy := hIm t htR
    have ht1 : |t.im| ≤ 1 := by
      rcases hRR with h | h
      · obtain ⟨-, -, a, b⟩ := C.mem_lowRect.mp h
        rw [abs_le]; constructor <;> linarith [C.y₀_pos]
      · obtain ⟨-, -, a, b⟩ := C.mem_upRect.mp h
        rw [abs_le]; constructor <;> linarith [C.y₀_pos]
    have hκ := C.κ_pos
    have hκ8 := C.κ_le
    -- the factors
    have nG : ‖G t‖ ≤ 1 / C.Lh := by
      simp only [hG]
      rw [norm_div, hc, norm_mul]
      apply one_div_le_one_div_of_le hLh
      nlinarith [norm_nonneg (paperFT C.K t)]
    have nE : ‖I * C.κ * Complex.exp (I * t * C.κ)‖ ≤ 2 * C.κ := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hκ, C.norm_exp_I_mul_κ]
      have h1 : -(t.im * C.κ) ≤ 1 / 8 := by
        have := neg_abs_le t.im
        nlinarith [abs_nonneg t.im]
      have h2 : Real.exp (-(t.im * C.κ)) ≤ 2 := by
        have := Real.exp_le_exp.mpr h1
        have h3 : Real.exp (1 / 8) ≤ 2 := by
          by_contra hc
          push Not at hc
          have hp : (2 : ℝ) ^ 8 ≤ Real.exp (1 / 8) ^ 8 := pow_le_pow_left₀ (by norm_num) hc.le 8
          have he : Real.exp (1 / 8) ^ 8 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
          have := Real.exp_one_lt_d9
          linarith
        linarith
      nlinarith
    have nD : C.κ * C.y₀ / 2 ≤ ‖Complex.exp (I * x * C.κ) - Complex.exp (I * t * C.κ)‖ := by
      have h1 := abs_norm_sub_norm_le (Complex.exp (I * x * C.κ)) (Complex.exp (I * t * C.κ))
      rw [C.norm_exp_I_mul_κ, C.norm_exp_I_mul_κ] at h1
      simp only [Complex.ofReal_im, zero_mul, neg_zero, Real.exp_zero] at h1
      have h2 := one_sub_exp_ge (u := t.im * C.κ) (by
        rw [abs_mul, abs_of_pos hκ]; nlinarith [abs_nonneg t.im])
      rw [abs_mul, abs_of_pos hκ] at h2
      have : C.κ * C.y₀ / 2 ≤ |t.im| * C.κ / 2 := by nlinarith
      linarith
    have nΩ : (C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀ ≤
        ‖eval (Complex.exp (I * t * C.κ))
          (Lagrange.nodal C.nodes (fun i => Complex.exp (I * gammaOf (i : ℂ) * C.κ)))‖ := by
      rw [Lagrange.eval_nodal, norm_prod]
      have hfac : ∀ ρ ∈ C.nodes, C.κ / 4 * ‖t - gammaOf (ρ : ℂ)‖ ≤
          ‖Complex.exp (I * t * C.κ) - Complex.exp (I * gammaOf (ρ : ℂ) * C.κ)‖ := by
        intro ρ hρ
        have hd := C.rect_norm_sub_node_le hRR hρ
        have e : Complex.exp (I * t * C.κ) - Complex.exp (I * gammaOf (ρ : ℂ) * C.κ) =
            Complex.exp (I * gammaOf (ρ : ℂ) * C.κ) *
              (Complex.exp (I * (t - gammaOf (ρ : ℂ)) * C.κ) - 1) := by
          rw [mul_sub, mul_one, ← Complex.exp_add]; ring_nf
        rw [e, norm_mul, C.norm_exp_I_mul_κ]
        have hw : ‖I * (t - gammaOf (ρ : ℂ)) * C.κ‖ = C.κ * ‖t - gammaOf (ρ : ℂ)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hκ]; ring
        have h1 := half_norm_le_norm_exp_sub_one (w := I * (t - gammaOf (ρ : ℂ)) * C.κ)
          (by rw [hw]; nlinarith [norm_nonneg (t - gammaOf (ρ : ℂ))])
        rw [hw] at h1
        obtain ⟨-, -, hc'⟩ := C.node_coords hρ
        have h2 : 1 / 2 ≤ Real.exp (-((gammaOf (ρ : ℂ)).im * C.κ)) := by
          have h3 : -(1 / 16 : ℝ) ≤ -((gammaOf (ρ : ℂ)).im * C.κ) := by
            have := abs_lt.mp hc'; nlinarith [this.1, this.2]
          have h4 := Real.add_one_le_exp (-((gammaOf (ρ : ℂ)).im * C.κ))
          linarith
        nlinarith [norm_nonneg (t - gammaOf (ρ : ℂ)),
          norm_nonneg (Complex.exp (I * (t - gammaOf (ρ : ℂ)) * C.κ) - 1)]
      have hprod := Finset.prod_le_prod (fun ρ _ => by
        have := norm_nonneg (t - gammaOf (ρ : ℂ)); positivity) hfac
      rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
      have hnodesS : ∏ ρ ∈ C.nodes, ‖t - gammaOf (ρ : ℂ)‖ =
          ∏ q ∈ C.nodes.map ⟨firstCopy, fun a b h => by
            simp only [firstCopy] at h; exact (Sigma.mk.inj_iff.mp h).1⟩,
            ‖t - gammaOf (q.1 : ℂ)‖ := by
        rw [Finset.prod_map]; rfl
      have hS : C.nodes.map ⟨firstCopy, fun a b h => by
          simp only [firstCopy] at h; exact (Sigma.mk.inj_iff.mp h).1⟩ ⊆ windowCopySet C.t₀ := by
        intro q hq
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_map.mp hq
        obtain ⟨h1, -⟩ := (mem_nodeSet (by linarith [C.hX2])).mp hρ
        exact C.firstCopy_mem_window (by linarith [C.hX2])
      have hlow := prod_norm_sub_ge_on_frame C.hX1 C.hX2 C.hδ₀ C.hδ₁ C.hy₁ C.hselX C.hsely hFr hS
      rw [← hnodesS] at hlow
      have hpow : (C.κ / 4) ^ windowCount C.t₀ ≤ (C.κ / 4) ^ C.nodes.card :=
        pow_le_pow_of_le_one (by positivity) (by linarith) C.card_nodes_le
      calc (C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀
          ≤ (C.κ / 4) ^ C.nodes.card * ∏ ρ ∈ C.nodes, ‖t - gammaOf (ρ : ℂ)‖ :=
            mul_le_mul hpow hlow (by have := C.hδ₀; have := Real.exp_pos 1; positivity)
              (by positivity)
        _ ≤ _ := hprod
    have hΩpos : 0 < (C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀ := by
      have := C.hδ₀; have := Real.exp_pos 1; positivity
    have hDpos : 0 < C.κ * C.y₀ / 2 := by have := C.y₀_pos; positivity
    rw [norm_div, norm_mul (G t) _,
      norm_mul (Complex.exp (I * x * C.κ) - Complex.exp (I * t * C.κ)) _]
    rw [div_le_iff₀ (mul_pos (lt_of_lt_of_le hDpos nD) (lt_of_lt_of_le hΩpos nΩ))]
    have hMb : C.Mb * (Real.pi / (5 / 2)) * ((C.κ * C.y₀ / 2) *
        ((C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀)) ≥
        1 / C.Lh * (2 * C.κ) := by
      have hLh := C.Lh_pos
      have hy0 := C.y₀_pos
      have hW : 0 < (C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀ :=
        hΩpos
      have hA0 : 0 < (C.κ / 4) ^ windowCount C.t₀ := by have := C.κ_pos; positivity
      have hD0 : 0 < (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀ := by
        have := C.hδ₀; have := Real.exp_pos 1; positivity
      have e : C.Mb * (Real.pi / (5 / 2)) * ((C.κ * C.y₀ / 2) *
          ((C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀)) =
          (4 * Real.pi / 5) * C.κ / C.Lh := by
        unfold Mb
        generalize (C.κ / 4) ^ windowCount C.t₀ = A at hA0 ⊢
        generalize (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀ = D at hD0 ⊢
        field_simp
      rw [ge_iff_le, e, one_div_mul_eq_div]
      apply div_le_div_of_nonneg_right _ hLh.le
      nlinarith [Real.pi_gt_three, C.κ_pos]
    calc ‖G t‖ * ‖I * C.κ * Complex.exp (I * t * C.κ)‖ ≤ 1 / C.Lh * (2 * C.κ) :=
          mul_le_mul nG nE (norm_nonneg _) (by positivity)
      _ ≤ C.Mb * (Real.pi / (5 / 2)) * ((C.κ * C.y₀ / 2) *
          ((C.κ / 4) ^ windowCount C.t₀ * (C.δ₀ / (16 * Real.exp 1)) ^ windowCount C.t₀)) := hMb
      _ ≤ C.Mb * (Real.pi / (5 / 2)) *
          (‖Complex.exp (I * x * C.κ) - Complex.exp (I * t * C.κ)‖ *
            ‖eval (Complex.exp (I * t * C.κ))
              (Lagrange.nodal C.nodes (fun i => Complex.exp (I * gammaOf (i : ℂ) * C.κ)))‖) := by
          apply mul_le_mul_of_nonneg_left _ (by have := C.Mb_pos; positivity)
          exact mul_le_mul nD nΩ hΩpos.le (norm_nonneg _)
  · have hMb := C.Mb_pos
    calc (|w.re - z.re| + |w.im - z.im|) * (C.Mb * (Real.pi / (5 / 2))) / Real.pi
        ≤ (5 / 2) * (C.Mb * (Real.pi / (5 / 2))) / Real.pi := by gcongr
      _ = C.Mb := by field_simp

/-- The bound for the interpolant on the real line. -/
def Mq : ℝ := 2 * 3 ^ windowCount C.t₀ * C.Mb

theorem Mq_pos : 0 < C.Mq := by unfold Mq; have := C.Mb_pos; positivity

theorem norm_ω_le {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) : ‖C.ω ρ‖ ≤ 2 := by
  unfold ω
  rw [C.norm_exp_I_mul_κ]
  obtain ⟨-, -, hc⟩ := C.node_coords hρ
  have hκ := C.κ_pos
  have hκ8 := C.κ_le
  have h1 : -((gammaOf (ρ : ℂ)).im * C.κ) ≤ 1 / 16 := by
    have := abs_lt.mp hc; nlinarith [this.1, this.2]
  have h3 : Real.exp (1 / 16) ≤ 2 := by
    by_contra hc'
    push Not at hc'
    have hp : (2 : ℝ) ^ 16 ≤ Real.exp (1 / 16) ^ 16 := pow_le_pow_left₀ (by norm_num) hc'.le 16
    have he : Real.exp (1 / 16) ^ 16 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_lt_d9
    linarith
  exact (Real.exp_le_exp.mpr h1).trans h3

theorem ω_ne_exp_real {ρ : XiDivisorSupport} (hρ : ρ ∈ C.nodes) (x : ℝ) :
    Complex.exp (I * x * C.κ) ≠ C.ω ρ := by
  intro he
  have h1 := congrArg norm he
  unfold ω at h1
  rw [C.norm_exp_I_mul_κ, C.norm_exp_I_mul_κ] at h1
  have h2 := Real.exp_injective h1
  simp only [Complex.ofReal_im, zero_mul, neg_zero] at h2
  have h3 : (gammaOf (ρ : ℂ)).im * C.κ = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h | h
  · exact C.node_im_ne_zero hρ h
  · exact C.κ_pos.ne' h

open scoped Classical in
/-- **The interpolant is bounded on the real line.** For every real `x`,
`|Q(e^{iκx})| ≤ 2·3^N·Mb`, whatever the configuration of the nodes. -/
theorem norm_Q_eval_le (hne : C.nodes.Nonempty) (x : ℝ) :
    ‖C.Q.eval (Complex.exp (I * x * C.κ))‖ ≤ C.Mq := by
  set ex := Complex.exp (I * x * C.κ) with hex
  have hx : ∀ ρ ∈ C.nodes, ex ≠ C.ω ρ := fun ρ hρ => C.ω_ne_exp_real hρ x
  have hev : C.Q.eval ex = (Lagrange.nodal C.nodes C.ω).eval ex *
      ∑ ρ ∈ C.nodes, Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ :=
    Lagrange.eval_interpolate_not_at_node C.r hx
  set zU : ℂ := ((C.t₀ - C.X : ℝ) : ℂ) + C.y₀ * I
  set wU : ℂ := ((C.t₀ + C.X : ℝ) : ℂ) + I
  set zL : ℂ := ((C.t₀ - C.X : ℝ) : ℂ) - I
  set wL : ℂ := ((C.t₀ + C.X : ℝ) : ℂ) - C.y₀ * I
  have hUp : C.upRect = Rectangle zU wU := rfl
  have hLow : C.lowRect = Rectangle zL wL := rfl
  have hX := C.hX1
  have hy := C.y₀_pos
  have hy4 := C.y₀_le
  -- the split of the barycentric sum
  have hsplit : ∑ ρ ∈ C.nodes, Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ =
      ∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle zU wU),
        Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ +
      ∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle zL wL),
        Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ := by
    rw [← Finset.sum_filter_add_sum_filter_not C.nodes
      (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle zU wU)]
    congr 1
    refine Finset.sum_congr (Finset.filter_congr fun ρ hρ => ?_) fun _ _ => rfl
    have h0 := C.node_im_ne_zero hρ
    obtain ⟨hpos, hneg⟩ := C.node_mem_rect hρ
    rw [← hUp, ← hLow]
    constructor
    · intro hnot
      rcases lt_or_gt_of_ne h0 with h | h
      · exact mem_of_mem_nhds (hneg h).1
      · exact absurd (mem_of_mem_nhds (hpos h).1) hnot
    · intro hin hup
      rcases lt_or_gt_of_ne h0 with h | h
      · exact (hneg h).2 hup
      · exact (hpos h).2 hin
  -- the two rectangles
  have hdimU : |wU.re - zU.re| + |wU.im - zU.im| ≤ 5 / 2 := by
    simp only [zU, wU, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im]
    norm_num
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith [C.hX2]
  have hdimL : |wL.re - zL.re| + |wL.im - zL.im| ≤ 5 / 2 := by
    simp only [zL, wL, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.mul_im]
    norm_num
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith [C.hX2]
  have hbU := C.norm_sum_inside_le (z := zU) (w := wU) (by simp [zU, wU]; linarith)
    (by simp [zU, wU]; linarith) I Complex.norm_I
    (fun t ht => Or.inr (by rw [hUp]; exact ht))
    (fun t ht => by
      have := (C.mem_upRect.mp (by rw [hUp]; exact ht)).2.2.1
      exact this.trans (le_abs_self _))
    (fun t ht => C.onFrame_of_border_up ht)
    (fun ρ hρ => by
      have h0 := C.node_im_ne_zero hρ
      obtain ⟨hpos, hneg⟩ := C.node_mem_rect hρ
      rw [← hUp]
      rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inr (hneg h).2
      · exact Or.inl (hpos h).1)
    (fun ρ hρ hin => by
      have := (C.mem_upRect.mp (by rw [hUp]; exact hin)).2.2.1
      unfold r; rw [if_pos (by linarith)])
    hdimU hne x
  have hbL := C.norm_sum_inside_le (z := zL) (w := wL) (by simp [zL, wL]; linarith)
    (by simp [zL, wL]; linarith) (-I) (by rw [norm_neg, Complex.norm_I])
    (fun t ht => Or.inl (by rw [hLow]; exact ht))
    (fun t ht => by
      have := (C.mem_lowRect.mp (by rw [hLow]; exact ht)).2.2.2
      rw [abs_of_neg (by linarith)]; linarith)
    (fun t ht => C.onFrame_of_border_low ht)
    (fun ρ hρ => by
      have h0 := C.node_im_ne_zero hρ
      obtain ⟨hpos, hneg⟩ := C.node_mem_rect hρ
      rw [← hLow]
      rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inl (hneg h).1
      · exact Or.inr (hpos h).2)
    (fun ρ hρ hin => by
      have := (C.mem_lowRect.mp (by rw [hLow]; exact hin)).2.2.2
      unfold r; rw [if_neg (by linarith)])
    hdimL hne x
  -- the nodal polynomial on the circle
  have hΩ : ‖(Lagrange.nodal C.nodes C.ω).eval ex‖ ≤ 3 ^ windowCount C.t₀ := by
    rw [Lagrange.eval_nodal, norm_prod]
    have hex1 : ‖ex‖ = 1 := by
      rw [hex, C.norm_exp_I_mul_κ]; simp
    calc ∏ ρ ∈ C.nodes, ‖ex - C.ω ρ‖ ≤ ∏ ρ ∈ C.nodes, (3 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun ρ hρ => ?_
          have := C.norm_ω_le hρ
          calc ‖ex - C.ω ρ‖ ≤ ‖ex‖ + ‖C.ω ρ‖ := norm_sub_le _ _
            _ ≤ 3 := by linarith
      _ = 3 ^ C.nodes.card := Finset.prod_const _
      _ ≤ 3 ^ windowCount C.t₀ := pow_le_pow_right₀ (by norm_num) C.card_nodes_le
  rw [hev, norm_mul, hsplit]
  have hsum : ‖∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle zU wU),
        Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ +
      ∑ ρ ∈ C.nodes.filter (fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) ∈ Rectangle zL wL),
        Lagrange.nodalWeight C.nodes C.ω ρ * (ex - C.ω ρ)⁻¹ * C.r ρ‖ ≤ C.Mb + C.Mb :=
    (norm_add_le _ _).trans (add_le_add hbU hbL)
  unfold Mq
  have := C.Mb_pos
  calc ‖(Lagrange.nodal C.nodes C.ω).eval ex‖ * _ ≤ 3 ^ windowCount C.t₀ * (C.Mb + C.Mb) :=
        mul_le_mul hΩ hsum (norm_nonneg _) (by positivity)
    _ = 2 * 3 ^ windowCount C.t₀ * C.Mb := by ring

end ClusterSetup

end

end RHTower
