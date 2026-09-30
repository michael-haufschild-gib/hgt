import GaloisForLFunctions.RHTower.DeBruijnNewmanStrictBound

/-!
# The Riemann hypothesis as absence of collisions in the de Bruijn–Newman flow

If `Λ = newmanConstant > 0`, then `H_Λ` has a multiple zero (`exists_multiple_zero_of_newmanConstant_pos`):
for `t < Λ` close to `Λ` the function `H_t` has non-real zeros, which stay in a compact box (uniform
Ki–Kim–Lee reality) and accumulate at a zero `x*` of `H_Λ`; `x*` is real, and a conjugate pair
`ζ, ζ̄` of zeros of `H_t` converging to it is impossible if `x*` is simple, because near a simple zero
`H_t` is injective for `t` close to `Λ` (`injOn_of_norm_deriv_sub_le`). Together with the
simplicity of all zeros for `t > Λ`:

`RH ⇔` for every `t > 0` every zero of `H_t` is simple (`riemannHypothesis_iff_forall_zeros_simple`).

The flow is collision-free at positive times exactly under the Riemann hypothesis; if RH fails, the
last collision happens at `t = Λ`.
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-- Time continuity of all derivatives: for `0 ≤ h ≤ 1`,
`‖H_{t+h}^{(n)}(z) − H_t^{(n)}(z)‖ ≤ (∫ |x|^{n+2} Φ e^{(t+1)x²} e^{|Im z||x|}) h`. -/
theorem norm_iteratedDeriv_riemannHeat_add_sub_le {t h : ℝ} (ht : 0 ≤ t) (hh0 : 0 ≤ h)
    (hh1 : h ≤ 1) (n : ℕ) (z : ℂ) :
    ‖iteratedDeriv n (riemannHeat (t + h)) z - iteratedDeriv n (riemannHeat t) z‖ ≤
      (∫ x, |x| ^ (n + 2) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|)) * h := by
  rw [iteratedDeriv_riemannHeat (by linarith), iteratedDeriv_riemannHeat ht]
  simp only [expTransform]
  rw [← integral_sub (integrable_heatWeight_mul_pow_mul_exp (by linarith) n z)
    (integrable_heatWeight_mul_pow_mul_exp ht n z)]
  refine (norm_integral_le_of_norm_le
    ((integrable_pow_mul_heatWeight (by linarith : (0 : ℝ) ≤ t + 1) (n + 2) |z.im|).mul_const h)
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_mul_const _ _))
  have hsplit : heatWeight (t + h) x * (I * x) ^ n * Complex.exp (I * z * x) -
      heatWeight t x * (I * x) ^ n * Complex.exp (I * z * x) =
      heatWeight t x * (I * x) ^ n * Complex.exp (I * z * x) *
        ((Real.exp (h * x ^ 2) - 1 : ℝ) : ℂ) := by
    rw [heatWeight_add]; push_cast; ring
  rw [hsplit, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hu : 0 ≤ h * x ^ 2 := by positivity
  have h1 : Real.exp (h * x ^ 2) - 1 ≤ h * x ^ 2 * Real.exp (h * x ^ 2) := by
    have := Real.add_one_le_exp (-(h * x ^ 2))
    have he := Real.exp_pos (h * x ^ 2)
    have e : Real.exp (-(h * x ^ 2)) * Real.exp (h * x ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have h1' : |Real.exp (h * x ^ 2) - 1| ≤ h * x ^ 2 * Real.exp (x ^ 2) := by
    rw [abs_of_nonneg (by linarith [Real.add_one_le_exp (h * x ^ 2)])]
    refine h1.trans ?_
    gcongr
    nlinarith [sq_nonneg x]
  have h2 := norm_exp_I_mul_le z x
  have hmain := norm_heatWeight_mul_exp t x
  calc ‖heatWeight t x‖ * |x| ^ n * ‖Complex.exp (I * z * x)‖ * |Real.exp (h * x ^ 2) - 1|
      ≤ ‖heatWeight t x‖ * |x| ^ n * Real.exp (|z.im| * |x|) *
          (h * x ^ 2 * Real.exp (x ^ 2)) := by gcongr
    _ = |x| ^ (n + 2) * (‖heatWeight t x‖ * Real.exp (x ^ 2)) * Real.exp (|z.im| * |x|) * h := by
        rw [pow_add, ← sq_abs x]; ring
    _ = |x| ^ (n + 2) * ‖heatWeight (t + 1) x‖ * Real.exp (|z.im| * |x|) * h := by rw [hmain]

/-- A function whose derivative stays within `‖A‖/2` of `A ≠ 0` on a closed disc is injective there. -/
theorem injOn_of_norm_deriv_sub_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c A : ℂ} {r : ℝ}
    (hA : A ≠ 0) (hder : ∀ w ∈ closedBall c r, ‖deriv g w - A‖ ≤ ‖A‖ / 2) :
    InjOn g (closedBall c r) := by
  intro z hz w hw hzw
  set F : ℂ → ℂ := fun u => g u - A * u with hF
  have hFd : ∀ u, HasDerivAt F (deriv g u - A) u := fun u => by
    refine ((hg u).hasDerivAt.sub ((hasDerivAt_id' u).const_mul A)).congr_deriv ?_
    ring
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (C := ‖A‖ / 2)
    (fun u _ => (hFd u).differentiableAt) (fun u hu => by rw [(hFd u).deriv]; exact hder u hu)
    (convex_closedBall c r) hw hz
  have e : F z - F w = -(A * (z - w)) := by simp only [hF, hzw]; ring
  rw [e, norm_neg, norm_mul] at hmv
  have hA0 : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have : ‖z - w‖ ≤ 0 := by nlinarith [norm_nonneg (z - w)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

/-- **The last collision.** If `Λ = newmanConstant > 0`, then `H_Λ` has a multiple zero. -/
theorem exists_multiple_zero_of_newmanConstant_pos (hΛ : 0 < newmanConstant) :
    ∃ z : ℂ, riemannHeat newmanConstant z = 0 ∧ deriv (riemannHeat newmanConstant) z = 0 := by
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = newmanConstant := ⟨_, rfl⟩
  rw [← hΛdef] at hΛ ⊢
  have hΛ8 : Λ < 1 / 8 := hΛdef ▸ newmanConstant_lt_eighth
  -- times approaching `Λ` from below
  obtain ⟨tn, htn⟩ : ∃ tn : ℕ → ℝ, ∀ n, tn n = Λ - Λ / (2 * ((n : ℝ) + 1)) :=
    ⟨fun n => Λ - Λ / (2 * ((n : ℝ) + 1)), fun n => rfl⟩
  have hgap : ∀ n, 0 < Λ - tn n ∧ Λ - tn n ≤ Λ / 2 := by
    intro n
    rw [htn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    constructor
    · have : 0 < Λ / (2 * ((n : ℝ) + 1)) := by positivity
      linarith
    · have : Λ / (2 * ((n : ℝ) + 1)) ≤ Λ / 2 := by
        apply div_le_div_of_nonneg_left hΛ.le (by norm_num); linarith
      linarith
  have hgap_lim : Tendsto (fun n => Λ - tn n) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => (Λ / 2) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((Λ / 2) * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at h
    refine h.congr fun n => ?_
    rw [htn]
    field_simp
    ring
  -- non-real zeros before `Λ`
  have hnon : ∀ n, ∃ ζ : ℂ, riemannHeat (tn n) ζ = 0 ∧ ζ.im ≠ 0 := by
    intro n
    have h0 : 0 ≤ tn n := by linarith [(hgap n).2]
    have hnot : tn n ∉ realRootedTimes := by
      rw [mem_realRootedTimes_iff h0, ← hΛdef]; linarith [(hgap n).1]
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    exact hnot ⟨h0, hall⟩
  choose ζ hζ0 hζim using hnon
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real_uniform (t₀ := Λ / 2) (by positivity)
  have hbox : ∀ n, ζ n ∈ closedBall (0 : ℂ) (|X₀| + 1) := by
    intro n
    have htpos : 0 < tn n := by linarith [(hgap n).2]
    have hre : |(ζ n).re| < X₀ := by
      by_contra h
      exact hζim n (hX₀ (tn n) ⟨by linarith [(hgap n).2], by linarith [(hgap n).1]⟩ _ (hζ0 n)
        (not_lt.mp h))
    have him2 : (ζ n).im ^ 2 ≤ 1 / 4 := (riemannHeat_zeros_im_sq_le htpos (hζ0 n)).trans
      (max_le (by linarith) (by norm_num))
    have him : |(ζ n).im| ≤ 1 / 2 := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    rw [mem_closedBall, dist_zero_right]
    calc ‖ζ n‖ ≤ |(ζ n).re| + |(ζ n).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ |X₀| + 1 := by linarith [le_abs_self X₀]
  obtain ⟨zs, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : ℂ) (|X₀| + 1)).tendsto_subseq hbox
  have hgφ : Tendsto (fun n => Λ - tn (φ n)) atTop (𝓝 0) := hgap_lim.comp hφ.tendsto_atTop
  -- uniform time-continuity constants on `|Im z| ≤ 2`
  set K₀ := ∫ x, |x| ^ (0 + 2) * ‖heatWeight (Λ + 1) x‖ * Real.exp (2 * |x|)
  set K₁ := ∫ x, |x| ^ (1 + 2) * ‖heatWeight (Λ + 1) x‖ * Real.exp (2 * |x|)
  have hKn : ∀ m : ℕ, ∀ n, ∀ w : ℂ, |w.im| ≤ 2 →
      ‖iteratedDeriv m (riemannHeat Λ) w - iteratedDeriv m (riemannHeat (tn (φ n))) w‖ ≤
        (∫ x, |x| ^ (m + 2) * ‖heatWeight (Λ + 1) x‖ * Real.exp (2 * |x|)) *
          (Λ - tn (φ n)) := by
    intro m n w hw
    have hg := hgap (φ n)
    have h := norm_iteratedDeriv_riemannHeat_add_sub_le (t := tn (φ n)) (h := Λ - tn (φ n))
      (by linarith) hg.1.le (by linarith) m w
    rw [show tn (φ n) + (Λ - tn (φ n)) = Λ by ring] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hg.1.le)
    refine integral_mono (integrable_pow_mul_heatWeight (by linarith) _ _)
      (integrable_pow_mul_heatWeight (by linarith) _ _) fun x => ?_
    have hle : tn (φ n) + 1 ≤ Λ + 1 := by linarith
    dsimp only
    have hw1 : ‖heatWeight (tn (φ n) + 1) x‖ ≤ ‖heatWeight (Λ + 1) x‖ := by
      simp only [heatWeight, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _)),
        abs_of_pos (mul_pos (riemannKernelReal_pos x) (Real.exp_pos _))]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x]))
        (riemannKernelReal_pos x).le
    gcongr
  -- the limit is a zero of `H_Λ`
  have hΛmem : Λ ∈ realRootedTimes := (mem_realRootedTimes_iff hΛ.le).mpr hΛdef.ge
  have hzs0 : riemannHeat Λ zs = 0 := by
    have hA : Tendsto (fun n => riemannHeat Λ (ζ (φ n))) atTop (𝓝 (riemannHeat Λ zs)) :=
      ((differentiable_riemannHeat hΛ.le).continuous.tendsto zs).comp hlim
    have hB : Tendsto (fun n => riemannHeat Λ (ζ (φ n)) - riemannHeat (tn (φ n)) (ζ (φ n)))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) (by simpa using hgφ.const_mul K₀)
      have := hKn 0 n (ζ (φ n)) (by
        have h2 : (ζ (φ n)).im ^ 2 ≤ 1 / 4 := (riemannHeat_zeros_im_sq_le
          (by linarith [(hgap (φ n)).2]) (hζ0 _)).trans
          (max_le (by linarith [(hgap (φ n)).2]) (by norm_num))
        have h3 : |(ζ (φ n)).im| ≤ 1 / 2 := by
          rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
        linarith)
      rw [iteratedDeriv_zero, iteratedDeriv_zero] at this
      exact this
    have h := hA.sub hB
    have e : (fun n => riemannHeat Λ (ζ (φ n)) -
        (riemannHeat Λ (ζ (φ n)) - riemannHeat (tn (φ n)) (ζ (φ n)))) = fun _ => 0 := by
      funext n; rw [hζ0]; ring
    rw [e, sub_zero] at h
    exact tendsto_nhds_unique tendsto_const_nhds h |>.symm
  have hzsre : zs.im = 0 := hΛmem.2 zs hzs0
  refine ⟨zs, hzs0, ?_⟩
  by_contra hd
  set A := deriv (riemannHeat Λ) zs
  have hA0 : 0 < ‖A‖ := norm_pos_iff.mpr hd
  -- a disc around `zs` on which `H_Λ'` stays within `‖A‖/4` of `A`
  have hcont : ContinuousAt (deriv (riemannHeat Λ)) zs := by
    have := (differentiable_iteratedDeriv_riemannHeat hΛ.le 1).continuous.continuousAt (x := zs)
    simpa [iteratedDeriv_one] using this
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hcont.eventually (Metric.closedBall_mem_nhds A (by positivity : 0 < ‖A‖ / 4)))
  set r := min (r₀ / 2) 1
  have hr : 0 < r := lt_min (by positivity) one_pos
  have hnear : ∀ w ∈ closedBall zs r, ‖deriv (riemannHeat Λ) w - A‖ ≤ ‖A‖ / 4 := by
    intro w hw
    have := hball w (by
      rw [mem_ball]; exact lt_of_le_of_lt (mem_closedBall.mp hw)
        (lt_of_le_of_lt (min_le_left _ _) (by linarith)))
    rwa [dist_eq_norm] at this
  have himw : ∀ w ∈ closedBall zs r, |w.im| ≤ 2 := by
    intro w hw
    have h1 := (Complex.abs_im_le_norm (w - zs)).trans
      ((mem_closedBall_iff_norm.mp hw).trans (min_le_right _ _))
    rw [Complex.sub_im, hzsre, sub_zero] at h1
    linarith
  -- eventually `H_{t_n}` is injective on the disc and contains `ζ_n`, `ζ̄_n`
  have hK1 : 0 ≤ K₁ := integral_nonneg fun x => by positivity
  have hev1 : ∀ᶠ n in atTop, K₁ * (Λ - tn (φ n)) ≤ ‖A‖ / 4 := by
    have h := hgφ.const_mul K₁
    rw [mul_zero] at h
    exact h.eventually (eventually_le_nhds (by positivity : 0 < ‖A‖ / 4))
  have hev2 : ∀ᶠ n in atTop, ‖ζ (φ n) - zs‖ ≤ r :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).eventually (eventually_le_nhds hr)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  have hinj : InjOn (riemannHeat (tn (φ n))) (closedBall zs r) := by
    refine injOn_of_norm_deriv_sub_le (differentiable_riemannHeat
      (by linarith [(hgap (φ n)).2])) hd fun w hw => ?_
    have h1 := hKn 1 n w (himw w hw)
    simp only [iteratedDeriv_one] at h1
    have h2 := hnear w hw
    calc ‖deriv (riemannHeat (tn (φ n))) w - A‖
        ≤ ‖deriv (riemannHeat Λ) w - deriv (riemannHeat (tn (φ n))) w‖ +
          ‖deriv (riemannHeat Λ) w - A‖ := by
          rw [← norm_neg (deriv (riemannHeat Λ) w - deriv (riemannHeat (tn (φ n))) w)]
          refine (norm_add_le _ _).trans_eq' ?_
          congr 1; ring
      _ ≤ ‖A‖ / 4 + ‖A‖ / 4 := by gcongr; exact h1.trans hn1
      _ = ‖A‖ / 2 := by ring
  have hmem1 : ζ (φ n) ∈ closedBall zs r := mem_closedBall_iff_norm.mpr hn2
  have hmem2 : (starRingEnd ℂ) (ζ (φ n)) ∈ closedBall zs r := by
    rw [mem_closedBall_iff_norm]
    have : (starRingEnd ℂ) (ζ (φ n)) - zs = (starRingEnd ℂ) (ζ (φ n) - zs) := by
      rw [map_sub, show (starRingEnd ℂ) zs = zs from
        Complex.ext (by simp) (by simp [hzsre])]
    rw [this, Complex.norm_conj]
    exact hn2
  have hconj0 : riemannHeat (tn (φ n)) ((starRingEnd ℂ) (ζ (φ n))) = 0 := by
    rw [riemannHeat_conj (by linarith [(hgap (φ n)).2]), hζ0, map_zero]
  have heq := hinj hmem1 hmem2 (by rw [hζ0, hconj0])
  apply hζim (φ n)
  have := congrArg Complex.im heq
  simp only [Complex.conj_im] at this
  linarith

/-- **The Riemann hypothesis as a collision-free flow.** RH holds iff for every heat time `t > 0`
every zero of `H_t` is simple. -/
theorem riemannHypothesis_iff_forall_zeros_simple :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → ∀ z : ℂ, riemannHeat t z = 0 →
      deriv (riemannHeat t) z ≠ 0 := by
  constructor
  · intro hRH t ht z hz
    exact (riemannHeat_zeros_real_simple_of_riemannHypothesis hRH ht hz).2
  · intro hsimple
    rw [riemannHypothesis_iff_newmanConstant_eq_zero]
    by_contra hne
    have hpos : 0 < newmanConstant := lt_of_le_of_ne newmanConstant_nonneg (Ne.symm hne)
    obtain ⟨z, hz, hd⟩ := exists_multiple_zero_of_newmanConstant_pos hpos
    exact hsimple _ hpos z hz hd

end

end RHTower.DeBruijn
