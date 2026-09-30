import GaloisForLFunctions.RHTower.DeBruijnHeatLocalModel

/-!
# Multiple zeros of `H_s` shed non-real zeros backward in time

If `z₀` is a zero of order `k ≥ 2` of `H_s` (`s > 0`), then backward in time, at the parabolic scale,
`H_{s−q²}(z₀ + qσ) = (a/k!) q^k P_k(σ) + O(q^{k+1})` with `P_k = e^{D²}σ^k`. For `k ≥ 2`,
`P_k(σ) = σ^{k mod 2} S(σ²)` where `S` has positive coefficients, so `S` has no root in `[0, ∞)`
and `P_k` has a root `τ` off the real axis (`exists_heatModel_root_im_pos`). By the minimum modulus
principle (`exists_zero_of_norm_lt_sphere`) `H_{s−q²}` has a zero within `qρ` of `z₀ + qτ`, so
`|Im ζ| ≥ |Im z₀| + cq` (`exists_zero_off_multiple_zero`). Consequences:

* zeros on the de Bruijn barrier `(Im z)² = ¼ − 2s > 0` are simple
  (`deriv_riemannHeat_ne_zero_of_barrier`): the shed zero would violate the barrier at `s − q²`;
* for `t > newmanConstant` every zero of `H_t` is simple
  (`deriv_riemannHeat_ne_zero_of_newmanConstant_lt`, Csordas–Smith–Varga): the shed zero would be a
  non-real zero of the real-rooted `H_{t−q²}`.
-/

open Complex Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## The model polynomial -/

/-- The polynomial `S_k(u) = Σ_{m ≤ k/2} k!/(m!(k−2m)!) u^{k/2−m}`, with
`P_k(σ) = σ^{k mod 2} S_k(σ²)`. -/
def heatModelEven (k : ℕ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range (k / 2 + 1),
    Polynomial.C ((k.factorial : ℂ) / ((m.factorial : ℂ) * ((k - 2 * m).factorial : ℂ))) *
      Polynomial.X ^ (k / 2 - m)

theorem heatModel_eq (k : ℕ) (σ : ℂ) :
    heatModel k σ = σ ^ (k % 2) * (heatModelEven k).eval (σ ^ 2) := by
  simp only [heatModel, heatModelEven, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Finset.mem_range] at hm
  rw [← pow_mul, mul_left_comm, ← pow_add]
  congr 2
  omega

theorem degree_heatModelEven_pos {k : ℕ} (hk : 2 ≤ k) : 0 < (heatModelEven k).degree := by
  set T : Polynomial ℂ := ∑ m ∈ Finset.range (k / 2),
    Polynomial.C ((k.factorial : ℂ) / (((m + 1).factorial : ℂ) * ((k - 2 * (m + 1)).factorial : ℂ))) *
      Polynomial.X ^ (k / 2 - (m + 1)) with hT
  have hsplit : heatModelEven k = Polynomial.X ^ (k / 2) + T := by
    rw [heatModelEven, Finset.sum_range_succ', hT, add_comm]
    congr 1
    have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    simp [hk0]
  have hj : 1 ≤ k / 2 := by omega
  have hTdeg : T.degree < ((k / 2 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro m hm
    simp only [Finset.mem_range] at hm
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    exact_mod_cast (by omega : k / 2 - (m + 1) < k / 2)
  rw [hsplit, Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
    Polynomial.degree_X_pow]
  exact_mod_cast (by omega : 0 < k / 2)

theorem heatModelEven_eval_ofReal_ne_zero (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (heatModelEven k).eval (x : ℂ) ≠ 0 := by
  have e : (heatModelEven k).eval (x : ℂ) = ((∑ m ∈ Finset.range (k / 2 + 1),
      ((k.factorial : ℝ) / ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ))) *
        x ^ (k / 2 - m) : ℝ) : ℂ) := by
    simp only [heatModelEven, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    push_cast
    rfl
  rw [e, Complex.ofReal_ne_zero]
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun m =>
    ((k.factorial : ℝ) / ((m.factorial : ℝ) * ((k - 2 * m).factorial : ℝ))) * x ^ (k / 2 - m))
    (fun m _ => by positivity) (Finset.self_mem_range_succ (k / 2))))
  simp only [Nat.sub_self, pow_zero, mul_one]
  positivity

theorem heatModel_conj (k : ℕ) (σ : ℂ) :
    heatModel k ((starRingEnd ℂ) σ) = (starRingEnd ℂ) (heatModel k σ) := by
  simp only [heatModel, map_sum, map_mul, map_pow, map_div₀, map_natCast]

/-- **A root of the model off the real axis.** For `k ≥ 2`, `P_k` has a root with `Im > 0`. -/
theorem exists_heatModel_root_im_pos {k : ℕ} (hk : 2 ≤ k) :
    ∃ τ : ℂ, heatModel k τ = 0 ∧ 0 < τ.im := by
  obtain ⟨u, hu⟩ := Complex.exists_root (degree_heatModelEven_pos hk)
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos
  have hroot : ∀ τ : ℂ, τ ^ 2 = u → heatModel k τ = 0 := by
    intro τ hτ
    rw [heatModel_eq, hτ, hu.eq_zero, mul_zero]
  have him : σ.im ≠ 0 := by
    intro h0
    have hur : u = ((σ.re ^ 2 : ℝ) : ℂ) := by
      rw [← hσ]; apply Complex.ext <;> simp [sq, h0]
    apply heatModelEven_eval_ofReal_ne_zero k (sq_nonneg σ.re)
    rw [← hur]
    exact hu.eq_zero
  rcases lt_or_gt_of_ne him with h | h
  · exact ⟨-σ, hroot _ (by rw [neg_sq]; exact hσ), by simpa using h⟩
  · exact ⟨σ, hroot _ hσ, h⟩

theorem differentiable_heatModel (k : ℕ) : Differentiable ℂ (heatModel k) := by
  unfold heatModel
  fun_prop

/-- The model is bounded below on all small circles around any point. -/
theorem exists_sphere_heatModel_lower (k : ℕ) (τ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ 0 < δ ∧ ∀ σ ∈ sphere τ ρ, δ ≤ ‖heatModel k σ‖ := by
  have han : AnalyticAt ℂ (heatModel k) τ := (differentiable_heatModel k).analyticAt τ
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall := ((differentiable_heatModel k).differentiableOn.analyticOnNhd
      isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ τ) h (mem_univ (1 : ℂ))
    have h1 : heatModel k 1 = (heatModelEven k).eval (1 : ℂ) := by
      rw [heatModel_eq]; simp
    have hne := heatModelEven_eval_ofReal_ne_zero k (x := 1) zero_le_one
    push_cast at hne
    exact hne (h1 ▸ hall)
  · obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
    set ρ := min (ρ₀ / 2) ε
    have hρ : 0 < ρ := lt_min (by positivity) hε
    have hne : ∀ σ ∈ sphere τ ρ, heatModel k σ ≠ 0 := by
      intro σ hσ
      refine hball ⟨?_, ?_⟩
      · rw [mem_ball, mem_sphere.mp hσ]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · intro hστ
        rw [mem_singleton_iff.mp hστ, mem_sphere, dist_self] at hσ
        linarith
    obtain ⟨σ₁, hσ₁, hmin⟩ := (isCompact_sphere τ ρ).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hρ.le) (differentiable_heatModel k).continuous.norm.continuousOn
    exact ⟨ρ, ‖heatModel k σ₁‖, hρ, min_le_right _ _, norm_pos_iff.mpr (hne σ₁ hσ₁),
      fun σ hσ => hmin hσ⟩

/-! ## The minimum modulus principle -/

/-- If `|f(c)| < |f|` on the circle `|z − c| = ρ`, then `f` vanishes in the disc. -/
theorem exists_zero_of_norm_lt_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (h : ∀ z ∈ sphere c ρ, ‖f c‖ < ‖f z‖) : ∃ z ∈ ball c ρ, f z = 0 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hcl : ∀ z ∈ closedBall c ρ, f z ≠ 0 := by
    intro z hz
    rcases eq_or_lt_of_le (mem_closedBall.mp hz) with h1 | h1
    · exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (h z (mem_sphere.mpr h1)))
    · exact hne z (mem_ball.mpr h1)
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le) hf.continuous.norm.continuousOn
  have hg : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hρ.ne']
    exact hf.differentiableOn.inv hcl
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
    (C := ‖f z₁‖⁻¹) (fun z hz => by
      rw [frontier_ball c hρ.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr (hcl z₁ (sphere_subset_closedBall hz₁))) (hmin hz))
    (subset_closure (mem_ball_self hρ))
  rw [norm_inv] at hbd
  have h1 := h z₁ hz₁
  have hc : 0 < ‖f c‖ := norm_pos_iff.mpr (hcl c (mem_closedBall_self hρ.le))
  have := (inv_le_inv₀ hc (hc.trans h1)).mp hbd
  linarith

/-! ## Barrier zeros -/

/-- A nonzero entire function has a nonvanishing derivative of some order at every point. -/
theorem exists_iteratedDeriv_riemannHeat_ne_zero {s : ℝ} (hs : 0 ≤ s) (z₀ : ℂ) :
    ∃ n, iteratedDeriv n (riemannHeat s) z₀ ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have h := Complex.taylorSeries_eq_on_ball' (c := z₀) (r := ‖z₀‖ + 1) (z := 0)
    (by rw [mem_ball, dist_eq_norm, zero_sub, norm_neg]; linarith)
    (differentiable_riemannHeat hs).differentiableOn
  simp only [hall, mul_zero, zero_mul, tsum_zero] at h
  exact riemannHeat_zero_ne hs h.symm

/-- **A multiple zero sheds a zero off its horizontal line backward in time.** If `z₀` is a
multiple zero of `H_s` (`s > 0`), there is `c > 0` such that for arbitrarily small `q > 0` the
function `H_{s−q²}` has a zero `ζ` with `|Im ζ| ≥ |Im z₀| + cq`. -/
theorem exists_zero_off_multiple_zero {s : ℝ} (hs : 0 < s) {z₀ : ℂ}
    (hz : riemannHeat s z₀ = 0) (hd : deriv (riemannHeat s) z₀ = 0) :
    ∃ c > 0, ∀ ε > 0, ∃ q : ℝ, 0 < q ∧ q ≤ ε ∧ q ^ 2 < s ∧ ∃ ζ : ℂ,
      riemannHeat (s - q ^ 2) ζ = 0 ∧ |z₀.im| + c * q ≤ |ζ.im| := by
  classical
  set H := riemannHeat s with hH
  have hex := exists_iteratedDeriv_riemannHeat_ne_zero hs.le z₀
  set k := Nat.find hex with hkdef
  have ha : iteratedDeriv k H z₀ ≠ 0 := Nat.find_spec hex
  have hvan : ∀ i < k, iteratedDeriv i H z₀ = 0 := fun i hi => not_not.mp (Nat.find_min hex hi)
  have hk : 2 ≤ k := by
    have h0 : k ≠ 0 := fun h => ha (by rw [h, iteratedDeriv_zero]; exact hz)
    have h1 : k ≠ 1 := fun h => ha (by rw [h, iteratedDeriv_one]; exact hd)
    omega
  -- a root of the model off the real axis, on the side of `z₀`
  obtain ⟨τ₀, hτ₀, hη⟩ := exists_heatModel_root_im_pos hk
  set η := τ₀.im
  set τ : ℂ := if 0 ≤ z₀.im then τ₀ else (starRingEnd ℂ) τ₀ with hτdef
  have hτ : heatModel k τ = 0 := by
    rw [hτdef]; split_ifs
    · exact hτ₀
    · rw [heatModel_conj, hτ₀, map_zero]
  have hτim : τ.im = if 0 ≤ z₀.im then η else -η := by
    rw [hτdef]; split_ifs <;> simp [η]
  obtain ⟨ρ, δ, hρ, hρη, hδ, hsph⟩ := exists_sphere_heatModel_lower k τ (ε := η / 2)
    (by positivity)
  obtain ⟨C, q₀, hq₀, hmodel⟩ := exists_norm_riemannHeat_sub_heatModel_le hs.le hvan
    (S := ‖τ‖ + ρ) (by positivity)
  set A := ‖iteratedDeriv k H z₀‖ / (k.factorial : ℝ)
  have hA : 0 < A := div_pos (norm_pos_iff.mpr ha) (by exact_mod_cast Nat.factorial_pos k)
  refine ⟨η / 2, by positivity, fun ε hε => ?_⟩
  set q := min (min q₀ 1) (min (s / 2) (min (A * δ / (4 * (|C| + 1))) ε))
  have hq : 0 < q := lt_min (lt_min hq₀ one_pos) (lt_min (by positivity)
    (lt_min (by positivity) hε))
  have hqq₀ : q ≤ q₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hq1 : q ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hqs : q ≤ s / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hqC : q ≤ A * δ / (4 * (|C| + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqε : q ≤ ε := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hq2s : q ^ 2 < s := by linarith
  -- the error is below half the model on the circle
  have hCq : C * q ^ (k + 1) < A * δ * q ^ k / 2 := by
    have hqk : 0 < q ^ k := pow_pos hq k
    have h1 : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq.le
    have h2 : |C| * q < A * δ / 2 := by
      have : |C| * q ≤ |C| * (A * δ / (4 * (|C| + 1))) :=
        mul_le_mul_of_nonneg_left hqC (abs_nonneg C)
      have h3 : |C| * (A * δ / (4 * (|C| + 1))) < A * δ / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_pos hA hδ, abs_nonneg C]
      linarith
    calc C * q ^ (k + 1) = (C * q) * q ^ k := by ring
      _ ≤ (|C| * q) * q ^ k := mul_le_mul_of_nonneg_right h1 hqk.le
      _ < (A * δ / 2) * q ^ k := mul_lt_mul_of_pos_right h2 hqk
      _ = A * δ * q ^ k / 2 := by ring
  -- the minimum modulus principle at the earlier time `s − q²`
  set f : ℂ → ℂ := fun σ => riemannHeat (s - q ^ 2) (z₀ + q * σ) with hf
  have hfd : Differentiable ℂ f := by
    have := differentiable_riemannHeat (t := s - q ^ 2) (by linarith)
    simp only [hf]
    fun_prop
  have hmain : ∀ σ : ℂ, ‖σ‖ ≤ ‖τ‖ + ρ →
      ‖f σ - iteratedDeriv k H z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ‖ ≤
        C * q ^ (k + 1) := fun σ hσ => hmodel q hq.le hqq₀ hq2s.le σ hσ
  have hcentre : ‖f τ‖ ≤ C * q ^ (k + 1) := by
    have := hmain τ (by linarith)
    rwa [hτ, mul_zero, sub_zero] at this
  have hnormA : ‖iteratedDeriv k H z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k‖ = A * q ^ k := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq]
  have hsphere : ∀ σ ∈ sphere τ ρ, ‖f τ‖ < ‖f σ‖ := by
    intro σ hσ
    have hσn : ‖σ‖ ≤ ‖τ‖ + ρ := by
      have := norm_le_norm_add_norm_sub' σ τ
      rw [← dist_eq_norm, mem_sphere.mp hσ] at this
      exact this
    have h1 := hmain σ hσn
    have h2 := hsph σ hσ
    have h3 := norm_sub_norm_le
      (iteratedDeriv k H z₀ / (k.factorial : ℂ) * (q : ℂ) ^ k * heatModel k σ) (f σ)
    rw [norm_sub_rev, norm_mul, hnormA] at h3
    have h4 : A * q ^ k * δ ≤ A * q ^ k * ‖heatModel k σ‖ :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  obtain ⟨σ₁, hσ₁, hf0⟩ := exists_zero_of_norm_lt_sphere hfd hρ hsphere
  refine ⟨q, hq, hqε, hq2s, z₀ + q * σ₁, hf0, ?_⟩
  have hζim : (z₀ + q * σ₁).im = z₀.im + q * σ₁.im := by simp
  rw [hζim]
  have hσim : |σ₁.im - τ.im| < η / 2 := by
    have := (Complex.abs_im_le_norm (σ₁ - τ)).trans_lt (mem_ball_iff_norm.mp hσ₁)
    rw [Complex.sub_im] at this
    linarith
  rw [hτim] at hσim
  split_ifs at hσim with hpos
  · have hs1 : η / 2 < σ₁.im := by rw [abs_lt] at hσim; linarith
    have h1 : q * (η / 2) < q * σ₁.im := mul_lt_mul_of_pos_left hs1 hq
    rw [abs_of_nonneg hpos, abs_of_nonneg (by nlinarith)]
    linarith
  · have hneg : z₀.im < 0 := not_le.mp hpos
    have hs1 : σ₁.im < -(η / 2) := by rw [abs_lt] at hσim; linarith
    have h1 : q * σ₁.im < q * (-(η / 2)) := mul_lt_mul_of_pos_left hs1 hq
    rw [abs_of_neg hneg, abs_of_neg (by nlinarith)]
    linarith

/-- **Zeros on the de Bruijn barrier are simple.** If `H_s(z₀) = 0` with `s > 0`, `Im z₀ ≠ 0` and
`(Im z₀)² ≥ ¼ − 2s`, then `H_s'(z₀) ≠ 0`. -/
theorem deriv_riemannHeat_ne_zero_of_barrier {s : ℝ} (hs : 0 < s) {z₀ : ℂ}
    (hz : riemannHeat s z₀ = 0) (hbar : 1 / 4 - 2 * s ≤ z₀.im ^ 2) (him : z₀.im ≠ 0) :
    deriv (riemannHeat s) z₀ ≠ 0 := by
  intro hd
  obtain ⟨c, hc, hoff⟩ := exists_zero_off_multiple_zero hs hz hd
  have hy : 0 < |z₀.im| := abs_pos.mpr him
  obtain ⟨q, hq, hqε, hqs, ζ, hζ, hζim⟩ := hoff (|z₀.im| * c / 2) (by positivity)
  have hbarrier := riemannHeat_zeros_im_sq_le (t := s - q ^ 2) (by linarith) hζ
  have hmax : max (1 / 4 - 2 * (s - q ^ 2)) 0 ≤ z₀.im ^ 2 + 2 * q ^ 2 :=
    max_le (by linarith) (by positivity)
  have hlow : (|z₀.im| + c * q) ^ 2 ≤ ζ.im ^ 2 := by
    rw [← sq_abs ζ.im]
    exact pow_le_pow_left₀ (by positivity) hζim 2
  have hgap : 2 * q ^ 2 < 2 * |z₀.im| * c * q := by
    have : q < |z₀.im| * c := by linarith [mul_pos hy hc]
    nlinarith
  have hsq : (|z₀.im| + c * q) ^ 2 = z₀.im ^ 2 + 2 * |z₀.im| * c * q + c ^ 2 * q ^ 2 := by
    rw [add_sq, sq_abs]; ring
  nlinarith [sq_nonneg (c * q)]

/-- **Csordas–Smith–Varga: simplicity above the de Bruijn–Newman constant.** For every
`t > newmanConstant`, every zero of `H_t` is simple. A multiple zero would shed a non-real zero of
`H_{t−q²}` for small `q`, while `H_{t−q²}` is still real-rooted. -/
theorem deriv_riemannHeat_ne_zero_of_newmanConstant_lt {t : ℝ} (ht : newmanConstant < t)
    {z : ℂ} (hz : riemannHeat t z = 0) : deriv (riemannHeat t) z ≠ 0 := by
  intro hd
  have ht0 : 0 < t := lt_of_le_of_lt newmanConstant_nonneg ht
  obtain ⟨c, hc, hoff⟩ := exists_zero_off_multiple_zero ht0 hz hd
  obtain ⟨q, hq, hqε, hqs, ζ, hζ, hζim⟩ := hoff (min 1 ((t - newmanConstant) / 2))
    (lt_min one_pos (by linarith))
  have hq1 : q ≤ 1 := hqε.trans (min_le_left _ _)
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hqΛ : q ≤ (t - newmanConstant) / 2 := hqε.trans (min_le_right _ _)
  have hmem : t - q ^ 2 ∈ realRootedTimes :=
    (mem_realRootedTimes_iff (by linarith)).mpr (by linarith)
  have h0 := hmem.2 ζ hζ
  rw [h0, abs_zero] at hζim
  have : 0 < c * q := mul_pos hc hq
  linarith [abs_nonneg z.im]

end

end RHTower.DeBruijn
