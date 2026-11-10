import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent

/-!
# Approximants that share zeros with `ξ` in growing boxes lose their zeros

Let Dirichlet series `F_k` converge to `F ≢ 0` in the norm of absolute convergence at a real point
`x`, and let every zero of `F_k` in the box `|Re s − ½| < ω`, `|Im s| ≤ H_k`, `H_k → ∞`, be a zero
of `ξ` (the strip lies right of `x`). Then:

* the limit is a constituent in the strip (`xi_eq_zero_of_limit_of_box_zeros`): a zero of `F` is a
  limit of zeros of the `F_k`, which lie in the boxes;
* so `F` has no zero in the strip, and is bounded below on every closed substrip
  (`exists_le_norm_LSeries_of_strip_zeroFree`);
* hence from some index on `F_k` has no zero in the closed substrip, at any height
  (`eventually_LSeries_ne_zero_of_box_zeros_subset_xi`).

For Dirichlet polynomials of bounded length this is uniform
(`exists_height_forall_dirichletPolynomial`): there is a height `H₀`, depending only on the length
and the strips, such that a nonzero Dirichlet polynomial of length at most `N` with a zero within
`ω'` of the critical line has, in the strip of half-width `ω` and below the height `H₀`, a zero
that is not a zero of `ξ`.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

section Limit

variable {a : ℕ → ℂ} {x : ℝ}

/-- **A Dirichlet series without zeros in a strip is bounded below on closed substrips**, by the
norm of its inverse in the Wiener algebra of the substrip. -/
theorem exists_le_norm_LSeries_of_strip_zeroFree (hsum : LSeriesSummable a x) {ω ω' : ℝ}
    (hω' : 0 ≤ ω') (hωω : ω' < ω) (hx : x ≤ 1 / 2 - ω)
    (hzf : ∀ s : ℂ, |s.re - 1 / 2| < ω → LSeries a s ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ s : ℂ, |s.re - 1 / 2| ≤ ω' → m ≤ ‖LSeries a s‖ := by
  have hc : WSummable (1 / 2 - ω) (1 / 2 + ω) (dirichletCoeff a) :=
    wsummable_dirichletCoeff hsum hx (by linarith)
  have hexp : ∀ z : ℂ, 1 / 2 - ω ≤ z.re → expansion (dirichletCoeff a) z = LSeries a z :=
    fun z hz => expansion_dirichletCoeff hsum (by linarith)
  obtain ⟨d, hd, hd1⟩ := exists_inverse_expansion_on_substrip (τ₁ := 1 / 2 - ω)
    (τ₂ := 1 / 2 + ω) (σ₁ := 1 / 2 - ω') (σ₂ := 1 / 2 + ω') (by linarith) (by linarith)
    (by linarith) hc fun z h1 h2 => by
      rw [hexp z h1.le]
      exact hzf z (abs_lt.mpr ⟨by linarith, by linarith⟩)
  set Dn : ℝ := ∑' q, ‖d q‖ * stripWeight (1 / 2 - ω') (1 / 2 + ω') q with hDn
  have hkey : ∀ s : ℂ, |s.re - 1 / 2| ≤ ω' → 1 ≤ ‖LSeries a s‖ * Dn := by
    intro s hs
    have h := abs_le.mp hs
    have h1 : 1 / 2 - ω' ≤ s.re := by linarith [h.1]
    have h2 : s.re ≤ 1 / 2 + ω' := by linarith [h.2]
    have hprod := hd1 s h1 h2
    rw [hexp s (by linarith)] at hprod
    have hnorm : ‖LSeries a s‖ * ‖expansion d s‖ = 1 := by rw [← norm_mul, hprod, norm_one]
    rw [← hnorm]
    exact mul_le_mul_of_nonneg_left (hd.norm_expansion_le h1 h2) (norm_nonneg _)
  have hDpos : 0 < Dn := by
    by_contra hle
    have h := hkey ((1 / 2 : ℝ) : ℂ) (by rw [ofReal_re, sub_self, abs_zero]; exact hω')
    have : ‖LSeries a ((1 / 2 : ℝ) : ℂ)‖ * Dn ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) (not_lt.mp hle)
    linarith
  refine ⟨Dn⁻¹, inv_pos.mpr hDpos, fun s hs => ?_⟩
  rw [inv_le_iff_one_le_mul₀ hDpos]
  exact hkey s hs

variable {A : ℕ → ℕ → ℂ}

/-- Convergence in the norm of absolute convergence at `x` is uniform convergence right of `x`. -/
theorem norm_LSeries_sub_le (hsum : LSeriesSummable a x) {b : ℕ → ℂ} (hb : LSeriesSummable b x)
    {s : ℂ} (hs : x ≤ s.re) :
    ‖LSeries b s - LSeries a s‖ ≤ ∑' m, ‖LSeries.term (b - a) x m‖ := by
  have hre : ((x : ℂ)).re ≤ s.re := by rwa [ofReal_re]
  rw [← LSeries_sub (hb.of_re_le_re hre) (hsum.of_re_le_re hre)]
  exact norm_LSeries_le_of_summable (hb.sub hsum) hs

/-- **The limit of approximants that share zeros in growing boxes is a constituent.** -/
theorem xi_eq_zero_of_limit_of_box_zeros (hsum : LSeriesSummable a x)
    (hA : ∀ k, LSeriesSummable (A k) x)
    (hconv : Tendsto (fun k => ∑' m, ‖LSeries.term (A k - a) x m‖) atTop (𝓝 0)) {n : ℕ}
    (hn : a (n + 1) ≠ 0) {ω : ℝ} (hx : x ≤ 1 / 2 - ω) {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hbox : ∀ k (s : ℂ), |s.re - 1 / 2| < ω → |s.im| ≤ H k → LSeries (A k) s = 0 → xi s = 0)
    {z : ℂ} (hz : |z.re - 1 / 2| < ω) (hz0 : LSeries a z = 0) : xi z = 0 := by
  by_contra hxi
  -- `ξ` does not vanish near `z`, and `z` is an isolated zero of the limit
  obtain ⟨r₁, hr₁, hxi1⟩ := Metric.eventually_nhds_iff.mp
    (xi_differentiable.continuous.continuousAt.eventually_ne hxi)
  have hFd := differentiableOn_LSeries_of_summable hsum
  have hVo : IsOpen {w : ℂ | x < w.re} := isOpen_lt continuous_const continuous_re
  have hzV : x < z.re := by linarith [(abs_lt.mp hz).1]
  have hFan : AnalyticOnNhd ℂ (LSeries a) {w : ℂ | x < w.re} := hFd.analyticOnNhd hVo
  have hiso : ∀ᶠ w in 𝓝[≠] z, LSeries a w ≠ 0 := by
    refine (hFan z hzV).eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hev => ?_
    obtain ⟨z₁, hz₁re, hz₁⟩ := exists_LSeries_ne_zero hsum hn (y := x + 1) (by linarith)
    exact hz₁ (hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt x).isPreconnected hzV hev
      (show x < z₁.re by rw [hz₁re]; linarith))
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp hiso
  have hgap : 0 < ω - |z.re - 1 / 2| := by linarith
  set r : ℝ := min (min (r₀ / 2) (r₁ / 2)) ((ω - |z.re - 1 / 2|) / 2) with hr
  have hrpos : 0 < r := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hrle : r ≤ min (r₀ / 2) (r₁ / 2) := min_le_left _ _
  have hr0 : r < r₀ := by
    have h : min (r₀ / 2) (r₁ / 2) ≤ r₀ / 2 := min_le_left _ _
    linarith
  have hr1 : r < r₁ := by
    have h : min (r₀ / 2) (r₁ / 2) ≤ r₁ / 2 := min_le_right _ _
    linarith
  have hr2 : r < ω - |z.re - 1 / 2| := by
    have h : r ≤ (ω - |z.re - 1 / 2|) / 2 := min_le_right _ _
    linarith
  -- points of the closed ball stay in the strip
  have hstrip : ∀ w ∈ closedBall z r, |w.re - 1 / 2| < ω ∧ |w.im| ≤ |z.im| + r := by
    intro w hw
    have hwn : ‖w - z‖ ≤ r := mem_closedBall_iff_norm.mp hw
    have hre := abs_le.mp ((abs_re_le_norm (w - z)).trans hwn)
    have him := abs_le.mp ((abs_im_le_norm (w - z)).trans hwn)
    rw [sub_re] at hre
    rw [sub_im] at him
    refine ⟨?_, ?_⟩
    · have h1 := abs_lt.mp hz
      rcases abs_cases (z.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hab] at hr2 <;>
        rw [abs_lt] <;> constructor <;> linarith [hre.1, hre.2]
    · rcases abs_cases z.im with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hab] <;> rw [abs_le] <;>
        constructor <;> linarith [him.1, him.2]
  have hsubV : closedBall z r ⊆ {w : ℂ | x < w.re} := fun w hw => by
    have h := abs_lt.mp (hstrip w hw).1
    show x < w.re
    linarith [h.1]
  have hsphere : ∀ w ∈ sphere z r, LSeries a w ≠ 0 := by
    intro w hw
    refine hball ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Metric.mem_sphere.mp hw]
      exact hr0
    · intro hwz
      rw [Set.mem_singleton_iff.mp hwz, Metric.mem_sphere, dist_self] at hw
      exact hrpos.ne hw
  have hcont : ContinuousOn (fun w => ‖LSeries a w‖) (sphere z r) :=
    (hFd.continuousOn.mono (sphere_subset_closedBall.trans hsubV)).norm
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_sphere z r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hrpos.le) hcont
  have hμ : 0 < ‖LSeries a w₀‖ := norm_pos_iff.mpr (hsphere w₀ hw₀)
  -- an approximant within a third of the minimum, with a box that contains the ball
  obtain ⟨k, hk1, hk2⟩ := ((hconv.eventually (Iio_mem_nhds (div_pos hμ (by norm_num :
    (0 : ℝ) < 3)))).and (hH.eventually_ge_atTop (|z.im| + r))).exists
  have hk1' : (∑' m, ‖LSeries.term (A k - a) x m‖) < ‖LSeries a w₀‖ / 3 := hk1
  by_cases hkz : LSeries (A k) z = 0
  · exact hxi (hbox k z hz (by linarith [hrpos.le]) hkz)
  · obtain ⟨w, hw, hw0⟩ := HTGeometry.exists_zero_of_sphere_domination
      (g := fun w => LSeries (A k) w - LSeries a w) (h := LSeries a) hrpos
      (((differentiableOn_LSeries_of_summable (hA k)).sub hFd).diffContOnCl_ball hsubV)
      (hFd.diffContOnCl_ball hsubV) hz0
      (by
        show LSeries (A k) z - LSeries a z ≠ 0
        rw [hz0, sub_zero]
        exact hkz)
      (fun w hw => by
        have h3 := norm_LSeries_sub_le hsum (hA k) (hsubV (sphere_subset_closedBall hw)).le
        have h4 := isMinOn_iff.mp hmin w hw
        show 3 * ‖LSeries (A k) w - LSeries a w‖ ≤ ‖LSeries a w‖
        linarith)
    have hw0' : LSeries (A k) w = 0 := by
      have h : LSeries (A k) w - LSeries a w + LSeries a w = 0 := hw0
      rwa [sub_add_cancel] at h
    have hws := hstrip w hw
    have hxiw := hbox k w hws.1 (hws.2.trans hk2) hw0'
    exact hxi1 (lt_of_le_of_lt (mem_closedBall.mp hw) hr1) hxiw

/-- **Approximants that share zeros with `ξ` in growing boxes lose their zeros.** If Dirichlet
series `F_k` converge to `F ≢ 0` in the norm of absolute convergence at `x`, and every zero of
`F_k` in the box `|Re s − ½| < ω`, `|Im s| ≤ H_k`, with `H_k → ∞`, is a zero of `ξ`, then for every
`ω' < ω`, from some index on `F_k` has no zero with `|Re s − ½| ≤ ω'`, at any height. -/
theorem eventually_LSeries_ne_zero_of_box_zeros_subset_xi (hsum : LSeriesSummable a x)
    (hA : ∀ k, LSeriesSummable (A k) x)
    (hconv : Tendsto (fun k => ∑' m, ‖LSeries.term (A k - a) x m‖) atTop (𝓝 0)) {n : ℕ}
    (hn : a (n + 1) ≠ 0) {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) (hx : x < 1 / 2 - ω)
    {H : ℕ → ℝ} (hH : Tendsto H atTop atTop)
    (hbox : ∀ k (s : ℂ), |s.re - 1 / 2| < ω → |s.im| ≤ H k → LSeries (A k) s = 0 → xi s = 0)
    {ω' : ℝ} (hω' : 0 ≤ ω') (hωω : ω' < ω) :
    ∀ᶠ k in atTop, ∀ s : ℂ, |s.re - 1 / 2| ≤ ω' → LSeries (A k) s ≠ 0 := by
  have hzf : ∀ s : ℂ, |s.re - 1 / 2| < ω → LSeries a s ≠ 0 := fun s hs =>
    LSeries_ne_zero_of_strip_zeros_subset_xi hsum hω0 hω hx hn
      (fun z hz hz0 => xi_eq_zero_of_limit_of_box_zeros hsum hA hconv hn hx.le hH hbox hz hz0) hs
  obtain ⟨m, hm, hlow⟩ := exists_le_norm_LSeries_of_strip_zeroFree hsum hω' hωω hx.le hzf
  filter_upwards [hconv.eventually (Iio_mem_nhds hm)] with k hk s hs h0
  have hk' : (∑' j, ‖LSeries.term (A k - a) x j‖) < m := hk
  have hsx : x ≤ s.re := by linarith [(abs_le.mp hs).1]
  have h1 := norm_LSeries_sub_le hsum (hA k) hsx
  rw [h0, zero_sub, norm_neg] at h1
  linarith [hlow s hs]

end Limit

/-! ### Dirichlet polynomials of bounded length -/

section Polynomial

variable {N : ℕ}

/-- The coefficient sequence of the Dirichlet polynomial `Σ_{i < N} v_i (i+1)^{−s}`. -/
def polyCoeff (v : Fin N → ℂ) (m : ℕ) : ℂ :=
  if h : 0 < m ∧ m ≤ N then v ⟨m - 1, by omega⟩ else 0

theorem polyCoeff_succ (v : Fin N → ℂ) (i : Fin N) : polyCoeff v (i + 1) = v i := by
  unfold polyCoeff
  rw [dif_pos ⟨Nat.succ_pos _, i.2⟩]
  congr 1

theorem polyCoeff_of_gt (v : Fin N → ℂ) {m : ℕ} (hm : N < m) : polyCoeff v m = 0 := by
  unfold polyCoeff
  rw [dif_neg fun h => absurd h.2 (not_le.mpr hm)]

theorem polyCoeff_zero_apply (v : Fin N → ℂ) : polyCoeff v 0 = 0 := by
  unfold polyCoeff
  rw [dif_neg fun h => absurd h.1 (lt_irrefl 0)]

theorem norm_polyCoeff_le (v : Fin N → ℂ) (m : ℕ) : ‖polyCoeff v m‖ ≤ ‖v‖ := by
  unfold polyCoeff
  split_ifs
  · exact norm_le_pi_norm v _
  · rw [norm_zero]
    exact norm_nonneg _

theorem polyCoeff_sub (u v : Fin N → ℂ) : polyCoeff u - polyCoeff v = polyCoeff (u - v) := by
  funext m
  unfold polyCoeff
  rw [Pi.sub_apply]
  split_ifs
  · rfl
  · rw [sub_zero]

theorem polyCoeff_smul (c : ℂ) (v : Fin N → ℂ) : polyCoeff (c • v) = c • polyCoeff v := by
  funext m
  unfold polyCoeff
  rw [Pi.smul_apply]
  split_ifs
  · rfl
  · rw [smul_zero]

theorem term_polyCoeff_of_gt (v : Fin N → ℂ) (s : ℂ) {m : ℕ} (hm : N < m) :
    LSeries.term (polyCoeff v) s m = 0 := by
  rw [LSeries.term_of_ne_zero (by omega), polyCoeff_of_gt v hm, zero_div]

/-- A Dirichlet polynomial converges absolutely everywhere. -/
theorem lSeriesSummable_polyCoeff (v : Fin N → ℂ) (s : ℂ) : LSeriesSummable (polyCoeff v) s :=
  summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun m hm =>
    term_polyCoeff_of_gt v s (by
      rw [Finset.mem_range] at hm
      omega)

/-- The norm of absolute convergence is bounded by the sup norm of the coefficient vector. -/
theorem tsum_norm_term_polyCoeff_le (v : Fin N → ℂ) (x : ℝ) :
    (∑' m, ‖LSeries.term (polyCoeff v) x m‖) ≤
      ‖v‖ * ∑ m ∈ Finset.range (N + 1), ‖LSeries.term (fun _ => (1 : ℂ)) x m‖ := by
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun m hm => by
    rw [term_polyCoeff_of_gt v x (by
      rw [Finset.mem_range] at hm
      omega), norm_zero], Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs
  · rw [mul_zero]
  · rw [norm_one, ← mul_div_assoc, mul_one]
    exact div_le_div_of_nonneg_right (norm_polyCoeff_le v m)
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)

/-- **A uniform height for Dirichlet polynomials of bounded length.** For every length `N` and
strips `ω' < ω ≤ ½` there is a height `H₀` such that for every nonzero Dirichlet polynomial of
length at most `N`: if all its zeros in the box `|Re s − ½| < ω`, `|Im s| ≤ H₀` are zeros of `ξ`,
it has no zero with `|Re s − ½| ≤ ω'`. So a polynomial of length `N` with a zero within `ω'` of
the line has, below the height `H₀` in the wider strip, a zero that is not a zero of `ξ`. -/
theorem exists_height_forall_dirichletPolynomial (N : ℕ) {ω ω' : ℝ} (hω' : 0 ≤ ω')
    (hωω : ω' < ω) (hω : ω ≤ 1 / 2) :
    ∃ H₀ : ℝ, ∀ v : Fin N → ℂ, v ≠ 0 →
      (∀ s : ℂ, |s.re - 1 / 2| < ω → |s.im| ≤ H₀ → LSeries (polyCoeff v) s = 0 → xi s = 0) →
      ∀ s : ℂ, |s.re - 1 / 2| ≤ ω' → LSeries (polyCoeff v) s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  choose v hv0 hvbox sz hsz hsz0 using fun k : ℕ => hcon (k : ℝ)
  -- normalize the coefficient vectors
  have hnorm : ∀ k, ‖v k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hv0 k)
  set u : ℕ → Fin N → ℂ := fun k => (((‖v k‖)⁻¹ : ℝ) : ℂ) • v k with hu
  have hcne : ∀ k, (((‖v k‖)⁻¹ : ℝ) : ℂ) ≠ 0 := fun k =>
    ofReal_ne_zero.mpr (inv_ne_zero (hnorm k))
  have hu1 : ∀ k, u k ∈ sphere (0 : Fin N → ℂ) 1 := fun k => by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ (hnorm k)]
  have hLu : ∀ k (s : ℂ), LSeries (polyCoeff (u k)) s =
      (((‖v k‖)⁻¹ : ℝ) : ℂ) * LSeries (polyCoeff (v k)) s := fun k s => by
    rw [hu, polyCoeff_smul, LSeries_smul]
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := (isCompact_sphere (0 : Fin N → ℂ) 1).tendsto_subseq hu1
  have hu₀ne : u₀ ≠ 0 := fun h => by
    rw [h, mem_sphere_zero_iff_norm, norm_zero] at hu₀
    exact zero_ne_one hu₀
  obtain ⟨i, hi⟩ : ∃ i, u₀ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu₀ne (funext h)
  -- convergence in the norm of absolute convergence at `−1`
  have hconv : Tendsto (fun k => ∑' m, ‖LSeries.term (polyCoeff (u (φ k)) - polyCoeff u₀)
      ((-1 : ℝ) : ℂ) m‖) atTop (𝓝 0) := by
    have hsq : Tendsto (fun k => ‖u (φ k) - u₀‖ *
        ∑ m ∈ Finset.range (N + 1), ‖LSeries.term (fun _ => (1 : ℂ)) ((-1 : ℝ) : ℂ) m‖)
        atTop (𝓝 0) := by
      have h := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).mul_const
        (∑ m ∈ Finset.range (N + 1), ‖LSeries.term (fun _ => (1 : ℂ)) ((-1 : ℝ) : ℂ) m‖)
      rwa [zero_mul] at h
    refine squeeze_zero (fun k => tsum_nonneg fun m => norm_nonneg _) (fun k => ?_) hsq
    rw [polyCoeff_sub]
    exact tsum_norm_term_polyCoeff_le _ _
  have hH : Tendsto (fun k => ((φ k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hev := eventually_LSeries_ne_zero_of_box_zeros_subset_xi (a := polyCoeff u₀)
    (A := fun k => polyCoeff (u (φ k))) (x := -1) (lSeriesSummable_polyCoeff _ _)
    (fun k => lSeriesSummable_polyCoeff _ _) hconv (n := i)
    (by rw [polyCoeff_succ]; exact hi) (lt_of_le_of_lt hω' hωω) hω (by linarith) hH
    (fun k s hs1 hs2 hs0 => by
      have h0 : LSeries (polyCoeff (v (φ k))) s = 0 := by
        rw [hLu] at hs0
        exact (mul_eq_zero.mp hs0).resolve_left (hcne _)
      exact hvbox (φ k) s hs1 hs2 h0) hω' hωω
  obtain ⟨k, hk⟩ := hev.exists
  exact hk (sz (φ k)) (hsz (φ k)) (by rw [hLu, hsz0, mul_zero])

end Polynomial

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
