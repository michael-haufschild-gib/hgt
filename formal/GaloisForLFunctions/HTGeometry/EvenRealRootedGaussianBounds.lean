import GaloisForLFunctions.HTGeometry.LaguerrePolyaImaginaryAxisBounds

/-!
# Gaussian bounds for even real-rooted polynomials and their limits

Let `q` be a real polynomial that splits over `ℝ`, with `q(0) ≠ 0`, and write
`Λ(q) = q′(0)² − q(0)q″(0)`, so that `Λ(q)/q(0)² = Σ_j 1/a_j²` over the roots.

* **Plane bound** (`norm_sq_polyEvalC_le_of_even`). If `q` is even, then
  `‖q(z)‖² ≤ q(0)² exp(‖z‖² Λ(q)/q(0)²)` for every `z ∈ ℂ`. Root by root,
  `|a² − z²| ≤ a² + |z|² = |a² − (i|z|)²|`, so `|q(z)q(−z)| ≤ |q(i|z|)q(−i|z|)|`, and the imaginary
  axis carries the Gaussian bound.
* **Real pair bound** (`polyEval_mul_neg_le`). If every root satisfies `a² > t²`, then
  `0 < q(t)q(−t) ≤ q(0)² exp(−t² Λ(q)/q(0)²)`, peeling one root at a time with
  `a² − t² ≤ a² e^{−t²/a²}`.

Both bounds pass to locally uniform limits of even real-rooted polynomials
(`norm_sq_le_of_tendsto_even`, `mul_neg_le_of_tendsto_even`), with the limit constant
`L = (F′(0)² − F(0)F″(0))/F(0)²`.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Polynomials -/

theorem norm_sq_sub_sq_le (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) ^ 2 - z ^ 2‖ ≤ ‖(a : ℂ) ^ 2 - (Complex.I * (‖z‖ : ℂ)) ^ 2‖ := by
  have h2 : ‖(a : ℂ) ^ 2 - (Complex.I * (‖z‖ : ℂ)) ^ 2‖ = a ^ 2 + ‖z‖ ^ 2 := by
    rw [mul_pow, Complex.I_sq, show (a : ℂ) ^ 2 - (-1) * (‖z‖ : ℂ) ^ 2 =
      ((a ^ 2 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  rw [h2]
  calc ‖(a : ℂ) ^ 2 - z ^ 2‖ ≤ ‖(a : ℂ) ^ 2‖ + ‖z ^ 2‖ := norm_sub_le _ _
    _ = a ^ 2 + ‖z‖ ^ 2 := by
      rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_mul_le_norm_mul {A B A' B' : ℂ} (h1 : ‖A‖ ≤ ‖A'‖) (h2 : ‖B‖ ≤ ‖B'‖) :
    ‖A * B‖ ≤ ‖A' * B'‖ := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

/-- For a monic real-rooted product, `‖P(z)P(−z)‖ ≤ ‖P(iy)P(−iy)‖` with `y = ‖z‖`. -/
theorem norm_prod_mul_neg_le (s : Multiset ℝ) (z : ℂ) :
    ‖polyEvalC ((s.map fun a => X - C a).prod) z *
        polyEvalC ((s.map fun a => X - C a).prod) (-z)‖ ≤
      ‖polyEvalC ((s.map fun a => X - C a).prod) (Complex.I * (‖z‖ : ℂ)) *
        polyEvalC ((s.map fun a => X - C a).prod) (-(Complex.I * (‖z‖ : ℂ)))‖ := by
  induction s using Multiset.induction with
  | empty => simp [polyEvalC]
  | cons a t ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, polyEvalC_mul, polyEvalC_X_sub_C]
    have e1 : ∀ w : ℂ, (w - a) * polyEvalC ((t.map fun a => X - C a).prod) w *
        ((-w - a) * polyEvalC ((t.map fun a => X - C a).prod) (-w)) =
          ((a : ℂ) ^ 2 - w ^ 2) * (polyEvalC ((t.map fun a => X - C a).prod) w *
            polyEvalC ((t.map fun a => X - C a).prod) (-w)) := by
      intro w; ring
    rw [e1, e1]
    exact norm_mul_le_norm_mul (norm_sq_sub_sq_le a z) ih

/-- **Plane bound for even real-rooted polynomials.** -/
theorem norm_sq_polyEvalC_le_of_even {q : ℝ[X]} (hq : q.Splits) (h0 : q.eval 0 ≠ 0)
    (heven : ∀ z, polyEvalC q (-z) = polyEvalC q z) (z : ℂ) :
    ‖polyEvalC q z‖ ^ 2 ≤ q.eval 0 ^ 2 * Real.exp (‖z‖ ^ 2 * lagAtZero q / q.eval 0 ^ 2) := by
  have hI := norm_sq_polyEvalC_I_mul_le hq h0 ‖z‖
  have hz : ‖polyEvalC q z‖ ^ 2 = ‖polyEvalC q z * polyEvalC q (-z)‖ := by
    rw [heven, norm_mul, sq]
  have hy : ‖polyEvalC q (Complex.I * (‖z‖ : ℂ))‖ ^ 2 =
      ‖polyEvalC q (Complex.I * (‖z‖ : ℂ)) * polyEvalC q (-(Complex.I * (‖z‖ : ℂ)))‖ := by
    rw [heven, norm_mul, sq]
  have hprod : ‖polyEvalC q z * polyEvalC q (-z)‖ ≤
      ‖polyEvalC q (Complex.I * (‖z‖ : ℂ)) * polyEvalC q (-(Complex.I * (‖z‖ : ℂ)))‖ := by
    rw [hq.eq_prod_roots]
    simp only [polyEvalC_mul, polyEvalC_C]
    have e : ∀ w : ℂ, (q.leadingCoeff : ℂ) * polyEvalC ((q.roots.map fun a => X - C a).prod) w *
        ((q.leadingCoeff : ℂ) * polyEvalC ((q.roots.map fun a => X - C a).prod) (-w)) =
          (q.leadingCoeff : ℂ) ^ 2 * (polyEvalC ((q.roots.map fun a => X - C a).prod) w *
            polyEvalC ((q.roots.map fun a => X - C a).prod) (-w)) := by
      intro w; ring
    rw [e, e]
    exact norm_mul_le_norm_mul le_rfl (norm_prod_mul_neg_le _ z)
  have : ‖polyEvalC q (Complex.I * (‖z‖ : ℂ))‖ ^ 2 ≤
      q.eval 0 ^ 2 * Real.exp (‖z‖ ^ 2 * lagAtZero q / q.eval 0 ^ 2) := by
    exact hI
  rw [hz]
  linarith [hy ▸ this]

/-- The real pair bound for monic real-rooted products. -/
theorem prod_eval_mul_neg_le (s : Multiset ℝ) {t : ℝ} (hs : ∀ a ∈ s, t ^ 2 < a ^ 2) :
    0 < ((s.map fun a => X - C a).prod).eval t * ((s.map fun a => X - C a).prod).eval (-t) ∧
      ((s.map fun a => X - C a).prod).eval t * ((s.map fun a => X - C a).prod).eval (-t) ≤
        (((s.map fun a => X - C a).prod).eval 0) ^ 2 *
          Real.exp (-(t ^ 2 * lagAtZero ((s.map fun a => X - C a).prod) /
            (((s.map fun a => X - C a).prod).eval 0) ^ 2)) := by
  induction s using Multiset.induction with
  | empty => simp [lagAtZero]
  | cons a u ih =>
    have hat : t ^ 2 < a ^ 2 := hs a (Multiset.mem_cons_self a u)
    obtain ⟨ihpos, ihle⟩ := ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    set Q := (u.map fun a => X - C a).prod with hQ
    have hQ0 : Q.eval 0 ≠ 0 := by
      rw [hQ, eval_multiset_prod, Multiset.map_map]
      refine Multiset.prod_ne_zero ?_
      intro h0
      obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp h0
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C, zero_sub, neg_eq_zero] at hb0
      have := hs b (Multiset.mem_cons_of_mem hb)
      rw [hb0] at this
      nlinarith [sq_nonneg t]
    have ha : a ≠ 0 := by rintro rfl; nlinarith [sq_nonneg t]
    rw [Multiset.map_cons, Multiset.prod_cons, ← hQ, lagAtZero_X_sub_C_mul]
    simp only [eval_mul, eval_sub, eval_X, eval_C, zero_sub]
    have hfac : (t - a) * Q.eval t * ((-t - a) * Q.eval (-t)) =
        (a ^ 2 - t ^ 2) * (Q.eval t * Q.eval (-t)) := by ring
    rw [hfac]
    have hd : 0 < a ^ 2 - t ^ 2 := by linarith
    refine ⟨mul_pos hd ihpos, ?_⟩
    have hpos : 0 < Q.eval 0 ^ 2 := by positivity
    have ha2 : 0 < a ^ 2 := by positivity
    have e : -(t ^ 2 * (Q.eval 0 ^ 2 + a ^ 2 * lagAtZero Q) / (-a * Q.eval 0) ^ 2) =
        -(t ^ 2 / a ^ 2) + -(t ^ 2 * lagAtZero Q / Q.eval 0 ^ 2) := by
      field_simp
      ring
    rw [e, Real.exp_add]
    have h1 : a ^ 2 - t ^ 2 ≤ a ^ 2 * Real.exp (-(t ^ 2 / a ^ 2)) := by
      have := Real.add_one_le_exp (-(t ^ 2 / a ^ 2))
      have e2 : a ^ 2 * (-(t ^ 2 / a ^ 2) + 1) = a ^ 2 - t ^ 2 := by field_simp; ring
      nlinarith
    calc (a ^ 2 - t ^ 2) * (Q.eval t * Q.eval (-t))
        ≤ (a ^ 2 * Real.exp (-(t ^ 2 / a ^ 2))) *
            (Q.eval 0 ^ 2 * Real.exp (-(t ^ 2 * lagAtZero Q / Q.eval 0 ^ 2))) :=
          mul_le_mul h1 ihle ihpos.le (by positivity)
      _ = (-a * Q.eval 0) ^ 2 *
            (Real.exp (-(t ^ 2 / a ^ 2)) * Real.exp (-(t ^ 2 * lagAtZero Q / Q.eval 0 ^ 2))) := by
          ring

/-- **Real pair bound.** If every root of the real-rooted `q` satisfies `a² > t²`, then
`0 < q(t)q(−t) ≤ q(0)² exp(−t²Λ(q)/q(0)²)`. -/
theorem polyEval_mul_neg_le {q : ℝ[X]} (hq : q.Splits) (h0 : q.eval 0 ≠ 0) {t : ℝ}
    (hroots : ∀ a ∈ q.roots, t ^ 2 < a ^ 2) :
    0 < q.eval t * q.eval (-t) ∧
      q.eval t * q.eval (-t) ≤ q.eval 0 ^ 2 * Real.exp (-(t ^ 2 * lagAtZero q / q.eval 0 ^ 2)) := by
  have hfac := hq.eq_prod_roots
  set P := (q.roots.map fun a => X - C a).prod with hP
  obtain ⟨hpos, hle⟩ := prod_eval_mul_neg_le q.roots hroots
  rw [← hP] at hpos hle
  have hlc : q.leadingCoeff ≠ 0 := by
    intro h; rw [hfac, h, map_zero, zero_mul, eval_zero] at h0; exact h0 rfl
  have hP0 : P.eval 0 ≠ 0 := by
    intro h; rw [hfac, eval_mul, eval_C, h, mul_zero] at h0; exact h0 rfl
  have hL : lagAtZero q = q.leadingCoeff ^ 2 * lagAtZero P := by
    conv_lhs => rw [hfac]
    exact lagAtZero_C_mul _ _
  have hq0 : q.eval 0 = q.leadingCoeff * P.eval 0 := by
    conv_lhs => rw [hfac]
    rw [eval_mul, eval_C]
  have hqt : ∀ s, q.eval s = q.leadingCoeff * P.eval s := by
    intro s; conv_lhs => rw [hfac]
    rw [eval_mul, eval_C]
  have hE : t ^ 2 * lagAtZero q / q.eval 0 ^ 2 = t ^ 2 * lagAtZero P / P.eval 0 ^ 2 := by
    rw [hL, hq0]; field_simp
  rw [hE, hqt, hqt, hq0]
  have hlc2 : 0 < q.leadingCoeff ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have : q.leadingCoeff * P.eval t * (q.leadingCoeff * P.eval (-t)) =
        q.leadingCoeff ^ 2 * (P.eval t * P.eval (-t)) := by ring
    rw [this]; positivity
  · have : q.leadingCoeff * P.eval t * (q.leadingCoeff * P.eval (-t)) =
        q.leadingCoeff ^ 2 * (P.eval t * P.eval (-t)) := by ring
    rw [this, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left hle hlc2.le

/-! ## Locally uniform limits -/

theorem polyEvalC_ofReal (q : ℝ[X]) (t : ℝ) : polyEvalC q (t : ℂ) = ((q.eval t : ℝ) : ℂ) := by
  rw [polyEvalC_eq_eval_map, Polynomial.eval_map, show (t : ℂ) = algebraMap ℝ ℂ t from rfl,
    Polynomial.eval₂_at_apply]
  rfl

/-- `Λ(q)/q(0)²` through derivatives of the evaluation map. -/
theorem lagAtZero_div_eq (q : ℝ[X]) :
    ((lagAtZero q / q.eval 0 ^ 2 : ℝ) : ℂ) =
      ((deriv (polyEvalC q) 0) ^ 2 - polyEvalC q 0 * deriv (deriv (polyEvalC q)) 0) /
        (polyEvalC q 0) ^ 2 := by
  rw [deriv_polyEvalC, deriv_polyEvalC, polyEvalC_zero_eq, polyEvalC_zero_eq, polyEvalC_zero_eq,
    lagAtZero]
  push_cast
  ring

/-- The limit constant `L(F) = (F′(0)² − F(0)F″(0))/F(0)²`. -/
def lagRatio (F : ℂ → ℂ) : ℂ := ((deriv F 0) ^ 2 - F 0 * deriv (deriv F) 0) / (F 0) ^ 2

theorem tendsto_lagRatio {q : ℕ → ℝ[X]} {F : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly (fun N => polyEvalC (q N)) F atTop) (hF0 : F 0 ≠ 0) :
    Tendsto (fun N => ((lagAtZero (q N) / (q N).eval 0 ^ 2 : ℝ) : ℂ)) atTop (𝓝 (lagRatio F)) := by
  have hdiff : ∀ N, Differentiable ℂ (polyEvalC (q N)) := fun N => differentiable_polyEvalC _
  have h0 := tendstoLocallyUniformly_iterate_deriv hconv hdiff 0
  have h1 := tendstoLocallyUniformly_iterate_deriv hconv hdiff 1
  have h2 := tendstoLocallyUniformly_iterate_deriv hconv hdiff 2
  have p0 := (tendstoLocallyUniformlyOn_univ.2 h0).tendsto_at (Set.mem_univ (0 : ℂ))
  have p1 := (tendstoLocallyUniformlyOn_univ.2 h1).tendsto_at (Set.mem_univ (0 : ℂ))
  have p2 := (tendstoLocallyUniformlyOn_univ.2 h2).tendsto_at (Set.mem_univ (0 : ℂ))
  simp only [Function.iterate_zero, id_eq, Function.iterate_succ,
    Function.comp_apply] at p0 p1 p2
  simp only [lagAtZero_div_eq, lagRatio]
  exact ((p1.pow 2).sub (p0.mul p2)).div (p0.pow 2) (pow_ne_zero 2 hF0)

/-- **Plane bound in the limit.** -/
theorem norm_sq_le_of_tendsto_even {q : ℕ → ℝ[X]} {F : ℂ → ℂ} (hsplit : ∀ N, (q N).Splits)
    (heven : ∀ N z, polyEvalC (q N) (-z) = polyEvalC (q N) z)
    (hconv : TendstoLocallyUniformly (fun N => polyEvalC (q N)) F atTop) (hF0 : F 0 ≠ 0)
    (z : ℂ) : ‖F z‖ ^ 2 ≤ ‖F 0‖ ^ 2 * Real.exp (‖z‖ ^ 2 * (lagRatio F).re) := by
  have hpt : ∀ w, Tendsto (fun N => polyEvalC (q N) w) atTop (𝓝 (F w)) := fun w =>
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (Set.mem_univ w)
  have hL := (Complex.continuous_re.tendsto _).comp (tendsto_lagRatio hconv hF0)
  simp only [Function.comp_def, Complex.ofReal_re] at hL
  have hev : ∀ᶠ N in atTop, (q N).eval 0 ≠ 0 := by
    have := (hpt 0).eventually (isOpen_ne.mem_nhds hF0)
    filter_upwards [this] with N hN
    intro h; apply hN; rw [polyEvalC_zero_eq, h, Complex.ofReal_zero]
  have hlim_l : Tendsto (fun N => ‖polyEvalC (q N) z‖ ^ 2) atTop (𝓝 (‖F z‖ ^ 2)) :=
    ((continuous_norm.tendsto _).comp (hpt z)).pow 2
  have hlim_r : Tendsto (fun N => (q N).eval 0 ^ 2 *
      Real.exp (‖z‖ ^ 2 * (lagAtZero (q N) / (q N).eval 0 ^ 2))) atTop
        (𝓝 (‖F 0‖ ^ 2 * Real.exp (‖z‖ ^ 2 * (lagRatio F).re))) := by
    have h0 : Tendsto (fun N => (q N).eval 0 ^ 2) atTop (𝓝 (‖F 0‖ ^ 2)) := by
      have := ((continuous_norm.tendsto _).comp (hpt 0)).pow 2
      refine this.congr fun N => ?_
      simp [polyEvalC_zero_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h0.mul ((Real.continuous_exp.tendsto _).comp (hL.const_mul _))
  refine le_of_tendsto_of_tendsto hlim_l hlim_r ?_
  filter_upwards [hev] with N hN
  have := norm_sq_polyEvalC_le_of_even (hsplit N) hN (heven N) z
  rwa [mul_div_assoc] at this

/-- **Real pair bound in the limit.** If `F` has no zero on `[−|t|, |t|]`, then
`Re(F(t)F(−t)) ≤ |F(0)|² exp(−t² L(F))`. -/
theorem mul_neg_le_of_tendsto_even {q : ℕ → ℝ[X]} {F : ℂ → ℂ} (hsplit : ∀ N, (q N).Splits)
    (hconv : TendstoLocallyUniformly (fun N => polyEvalC (q N)) F atTop) (hF0 : F 0 ≠ 0)
    {t : ℝ} (hne : ∀ s : ℝ, |s| ≤ |t| → F s ≠ 0) :
    (F t * F (-t)).re ≤ ‖F 0‖ ^ 2 * Real.exp (-(t ^ 2 * (lagRatio F).re)) := by
  have hpt : ∀ w, Tendsto (fun N => polyEvalC (q N) w) atTop (𝓝 (F w)) := fun w =>
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (Set.mem_univ w)
  have hL := (Complex.continuous_re.tendsto _).comp (tendsto_lagRatio hconv hF0)
  simp only [Function.comp_def, Complex.ofReal_re] at hL
  -- `F` is bounded away from zero on the real segment
  set K : Set ℂ := (fun s : ℝ => (s : ℂ)) '' Set.Icc (-|t|) |t| with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hFc : ContinuousOn F K := by
    have : Continuous F := by
      have hd : Differentiable ℂ F := by
        rw [← differentiableOn_univ]
        exact (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
          (Eventually.of_forall fun N => (differentiable_polyEvalC (q N)).differentiableOn)
          isOpen_univ
      exact hd.continuous
    exact this.continuousOn
  have hKne : ∀ w ∈ K, F w ≠ 0 := by
    rintro w ⟨s, hs, rfl⟩
    exact hne s (abs_le.mpr ⟨hs.1, hs.2⟩)
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ w ∈ K, m ≤ ‖F w‖ := by
    rcases (Set.Icc (-|t|) |t|).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, fun w hw => by rw [hK, h, Set.image_empty] at hw; exact absurd hw id⟩
    obtain ⟨w₀, hw₀, hmin⟩ := hKc.exists_isMinOn (h.image _) (continuous_norm.comp_continuousOn hFc)
    exact ⟨‖F w₀‖, norm_pos_iff.mpr (hKne w₀ hw₀), fun w hw => hmin hw⟩
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hKc
  have hev : ∀ᶠ N in atTop, ∀ w ∈ K, m / 2 < ‖polyEvalC (q N) w‖ := by
    have := Metric.tendstoUniformlyOn_iff.mp hunif (m / 2) (by positivity)
    filter_upwards [this] with N hN w hw
    have h1 := hN w hw
    have h2 := hmK w hw
    rw [dist_eq_norm] at h1
    have := norm_sub_norm_le (F w) (polyEvalC (q N) w)
    linarith
  have hev0 : ∀ᶠ N in atTop, (q N).eval 0 ≠ 0 := by
    have := (hpt 0).eventually (isOpen_ne.mem_nhds hF0)
    filter_upwards [this] with N hN
    intro h; apply hN; rw [polyEvalC_zero_eq, h, Complex.ofReal_zero]
  have hneg : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  have hlim_l : Tendsto (fun N => (q N).eval t * (q N).eval (-t)) atTop (𝓝 ((F t * F (-t)).re)) := by
    have h1 := hpt (-t : ℝ)
    rw [hneg] at h1
    have := (Complex.continuous_re.tendsto _).comp ((hpt t).mul h1)
    refine this.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [← hneg, polyEvalC_ofReal, polyEvalC_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hlim_r : Tendsto (fun N => (q N).eval 0 ^ 2 *
      Real.exp (-(t ^ 2 * (lagAtZero (q N) / (q N).eval 0 ^ 2)))) atTop
        (𝓝 (‖F 0‖ ^ 2 * Real.exp (-(t ^ 2 * (lagRatio F).re)))) := by
    have h0 : Tendsto (fun N => (q N).eval 0 ^ 2) atTop (𝓝 (‖F 0‖ ^ 2)) := by
      have := ((continuous_norm.tendsto _).comp (hpt 0)).pow 2
      refine this.congr fun N => ?_
      simp [polyEvalC_zero_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact h0.mul ((Real.continuous_exp.tendsto _).comp ((hL.const_mul _).neg))
  refine le_of_tendsto_of_tendsto hlim_l hlim_r ?_
  filter_upwards [hev, hev0] with N hN hN0
  have hroots : ∀ a ∈ (q N).roots, t ^ 2 < a ^ 2 := by
    intro a ha
    by_contra hcon
    push Not at hcon
    have habs : |a| ≤ |t| := sq_le_sq.mp hcon
    have haK : (a : ℂ) ∈ K := ⟨a, abs_le.mp habs, rfl⟩
    have hz := hN (a : ℂ) haK
    have hq0 : q N ≠ 0 := by rintro h; rw [h] at hN0; simp at hN0
    have hroot : (q N).eval a = 0 := (mem_roots hq0).mp ha
    rw [polyEvalC_ofReal, hroot, Complex.ofReal_zero, norm_zero] at hz
    linarith
  have := (polyEval_mul_neg_le (hsplit N) hN0 hroots).2
  rwa [mul_div_assoc] at this

end

end GaloisForLFunctions.HTGeometry
