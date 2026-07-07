/-
# The classification of entire automorphisms of ℂ

Building on the generalized Liouville theorem (`EntireGrowth`), this file classifies the
holomorphic self-maps of `ℂ` that arise as symmetries:

* `exists_polynomial_of_polyGrowth` — an entire function of polynomial growth is a
  polynomial function (the headline strengthening of Liouville that mathlib lacked);
* `exists_polynomial_of_entire_injective` — the collision: an injective entire function is a
  polynomial (open mapping + removable singularity + Liouville feed the generalized Liouville);
* `natDegree_eq_one_of_iterate_id` — a polynomial whose evaluation iterates to the identity
  has degree `1` (`(deg P)ⁿ = deg X = 1`);
* `finiteOrder_entire_fixing_is_rotation` — the full classification: *any* entire automorphism
  of finite order fixing `ρ` is the rotation `z ↦ ρ + a(z − ρ)` with `aⁿ = 1`.

This pins the uniqueness of the deck-charge forcing symmetry unconditionally: a finite-order
entire symmetry fixing `ρ` is a rotation about `ρ`, so `analyticOrderAt_dvd_of_rotation` captures
every such symmetric forcing of a rung.
-/
import GaloisForLFunctions.RHTower.EntireGrowth

namespace RHTower

open Complex Metric Topology Filter Set Polynomial

/-- The degree-`d` Taylor polynomial of `f` at `0` as an element of `ℂ[X]`. -/
noncomputable def taylorPoly (f : ℂ → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (iteratedDeriv i f 0 / i.factorial) * Polynomial.X ^ i

theorem taylorPoly_eval (f : ℂ → ℂ) (d : ℕ) (z : ℂ) :
    (taylorPoly f d).eval z = ∑ i ∈ Finset.range (d + 1),
      (iteratedDeriv i f 0 / i.factorial) * z ^ i := by
  unfold taylorPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- The `n`-th derivative of the Taylor polynomial function at `0` recovers the `n`-th Taylor
coefficient for `n ≤ d`, and vanishes for `n > d`. -/
theorem iteratedDeriv_taylorPoly_eval (f : ℂ → ℂ) (d n : ℕ) :
    iteratedDeriv n (fun z => (taylorPoly f d).eval z) 0 =
      if n < d + 1 then iteratedDeriv n f 0 else 0 := by
  have hfun : (fun z => (taylorPoly f d).eval z) =
      fun z => ∑ i ∈ Finset.range (d + 1), (iteratedDeriv i f 0 / i.factorial) * z ^ i := by
    funext z; exact taylorPoly_eval f d z
  rw [hfun, iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  have hterm : ∀ i ∈ Finset.range (d + 1),
      iteratedDeriv n (fun z : ℂ => (iteratedDeriv i f 0 / i.factorial) * z ^ i) 0 =
        if n = i then iteratedDeriv i f 0 else 0 := by
    intro i _
    have heq : (fun z : ℂ => (iteratedDeriv i f 0 / i.factorial) * z ^ i)
        = (iteratedDeriv i f 0 / i.factorial) • (fun z : ℂ => z ^ i) := by
      funext z; simp [smul_eq_mul]
    rw [heq, iteratedDeriv_const_smul (by fun_prop), iteratedDeriv_fun_pow_zero, smul_eq_mul]
    by_cases hni : n = i
    · rw [if_pos hni, if_pos hni,
        div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero i)]
    · simp [hni]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq (Finset.range (d + 1)) n (fun i => iteratedDeriv i f 0)]
  simp only [Finset.mem_range]

/-- **An entire function of polynomial growth is a polynomial.**  If `f` is entire and
`‖f z‖ ≤ M(‖z‖+1)^d`, then `f` equals the evaluation of a polynomial. -/
theorem exists_polynomial_of_polyGrowth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} {d : ℕ} (hgrow : ∀ z : ℂ, ‖f z‖ ≤ M * (‖z‖ + 1) ^ d) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  refine ⟨taylorPoly f d, ?_⟩
  have hg : Differentiable ℂ (fun z => f z - (taylorPoly f d).eval z) :=
    hf.sub (Polynomial.differentiable _)
  have hzero : (fun z => f z - (taylorPoly f d).eval z) = 0 := by
    refine eq_zero_of_iteratedDeriv_eq_zero hg (fun n => ?_)
    rw [iteratedDeriv_fun_sub
        ((hf.differentiableOn.analyticOnNhd isOpen_univ 0 (Set.mem_univ 0)).contDiffAt)
        (((Polynomial.differentiable (taylorPoly f d)).differentiableOn.analyticOnNhd
          isOpen_univ 0 (Set.mem_univ 0)).contDiffAt),
      iteratedDeriv_taylorPoly_eval]
    by_cases hn : n < d + 1
    · rw [if_pos hn, sub_self]
    · rw [if_neg hn, sub_zero]
      exact iteratedDeriv_eq_zero_of_polyGrowth hf hgrow (by omega)
  intro z
  have := congrFun hzero z
  simpa [sub_eq_zero] using this

/-- **Eventual polynomial growth ⟹ polynomial.**  Only the growth at infinity matters. -/
theorem exists_polynomial_of_polyGrowth_eventually {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M R₀ : ℝ} {d : ℕ} (hR₀ : 0 < R₀)
    (hgrow : ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z‖ ≤ M * ‖z‖ ^ d) :
    ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  refine ⟨taylorPoly f d, ?_⟩
  have hzero : (fun z => f z - (taylorPoly f d).eval z) = 0 := by
    refine eq_zero_of_iteratedDeriv_eq_zero (hf.sub (Polynomial.differentiable _)) (fun n => ?_)
    rw [iteratedDeriv_fun_sub
        ((hf.differentiableOn.analyticOnNhd isOpen_univ 0 (Set.mem_univ 0)).contDiffAt)
        (((Polynomial.differentiable (taylorPoly f d)).differentiableOn.analyticOnNhd
          isOpen_univ 0 (Set.mem_univ 0)).contDiffAt),
      iteratedDeriv_taylorPoly_eval]
    by_cases hn : n < d + 1
    · rw [if_pos hn, sub_self]
    · rw [if_neg hn, sub_zero]
      exact iteratedDeriv_eq_zero_of_polyGrowth_eventually hf hR₀ hgrow (by omega)
  intro z
  have := congrFun hzero z
  simpa [sub_eq_zero] using this

/-! ## The collision: an entire injective function is a polynomial -/

/-- **An injective entire function is a polynomial.**  Open mapping gives a target ball avoided
outside the unit disc; the removable-singularity theorem extends `1/(f − f₀)` across `∞`; the
germ there either forces boundedness (Liouville ⟹ constant ⟹ not injective) or polynomial
growth (feeding the generalized Liouville). -/
theorem exists_polynomial_of_entire_injective {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hinj : Function.Injective f) : ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z := by
  classical
  have hOpen : IsOpenMap f := by
    rcases (hf.differentiableOn.analyticOnNhd isOpen_univ).is_constant_or_isOpenMap with hc | ho
    · obtain ⟨w, hw⟩ := hc
      exact absurd (hinj (show f 0 = f 1 from by rw [hw 0, hw 1])) (by norm_num)
    · exact ho
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (hOpen _ Metric.isOpen_ball) (f 0)
    ⟨0, Metric.mem_ball_self one_pos, rfl⟩
  have hfar : ∀ z : ℂ, 1 ≤ ‖z‖ → r ≤ ‖f z - f 0‖ := by
    intro z hz
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨z', hz'ball, hz'eq⟩ := hrsub (by rw [Metric.mem_ball, Complex.dist_eq]; exact hlt)
    rw [mem_ball_zero_iff] at hz'ball
    rw [hinj hz'eq] at hz'ball; linarith
  have hfar' : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → r ≤ ‖f w⁻¹ - f 0‖ := fun w hw0 hwlt =>
    hfar w⁻¹ (by rw [norm_inv]; exact le_of_lt ((one_lt_inv₀ (norm_pos_iff.mpr hw0)).mpr hwlt))
  set g : ℂ → ℂ := fun w => (f w⁻¹ - f 0)⁻¹ with hg_def
  have hg_ne : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → g w ≠ 0 := fun w hw0 hwlt => by
    rw [hg_def]; refine inv_ne_zero fun h => ?_
    have := hfar' w hw0 hwlt; rw [h, norm_zero] at this; linarith
  have hg_diff : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → DifferentiableAt ℂ g w := fun w hw0 hwlt => by
    have hne : f w⁻¹ - f 0 ≠ 0 := fun h => by
      have := hfar' w hw0 hwlt; rw [h, norm_zero] at this; linarith
    exact (((hf w⁻¹).comp w (differentiableAt_inv hw0)).sub_const _).inv hne
  have hg_bdd : ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 → ‖g w‖ ≤ r⁻¹ := fun w hw0 hwlt => by
    rw [hg_def, norm_inv]; exact inv_anti₀ hr (hfar' w hw0 hwlt)
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝[≠] (0 : ℂ) :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 one_pos)
  have hd_pn : ∀ᶠ w in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ g w := by
    filter_upwards [self_mem_nhdsWithin, hball] with w hw hwb
    exact hg_diff w hw (mem_ball_zero_iff.mp hwb)
  have hbdd_under : Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ)) (fun w => ‖g w - g 0‖) := by
    refine ⟨r⁻¹ + ‖g 0‖, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [self_mem_nhdsWithin, hball] with w hw hwb
    calc ‖g w - g 0‖ ≤ ‖g w‖ + ‖g 0‖ := norm_sub_le _ _
      _ ≤ r⁻¹ + ‖g 0‖ := by gcongr; exact hg_bdd w hw (mem_ball_zero_iff.mp hwb)
  set L : ℂ := Filter.limUnder (𝓝[≠] (0 : ℂ)) g with hL_def
  have htendsto : Filter.Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 L) :=
    tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd_pn hbdd_under
  set G : ℂ → ℂ := Function.update g 0 L with hG_def
  have hGg : ∀ w : ℂ, w ≠ 0 → G w = g w := fun w hw => Function.update_of_ne hw _ _
  have hG_an : AnalyticAt ℂ G 0 := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
    · filter_upwards [hd_pn, self_mem_nhdsWithin] with w hw hw0
      refine hw.congr_of_eventuallyEq ?_
      filter_upwards [compl_singleton_mem_nhds hw0] with y hy
      rw [hG_def, Function.update_of_ne hy]
    · rw [hG_def]; exact continuousAt_update_same.2 htendsto
  by_cases hL0 : L = 0
  · have hGne_top : analyticOrderAt G 0 ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top]
      intro hev
      have h0 : ∀ᶠ w in 𝓝[≠] (0:ℂ), G w = 0 := hev.filter_mono nhdsWithin_le_nhds
      have hne : ∀ᶠ w in 𝓝[≠] (0:ℂ), G w ≠ 0 := by
        filter_upwards [self_mem_nhdsWithin, hball] with w hw hwb
        rw [hGg w hw]; exact hg_ne w hw (mem_ball_zero_iff.mp hwb)
      have hfalse : ∀ᶠ w in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [h0, hne] with w hw hwne; exact hwne hw
      exact hfalse.exists.elim fun _ h => h
    set m : ℕ := (analyticOrderAt G 0).toNat with hm_def
    have hm : (m : ℕ∞) = analyticOrderAt G 0 := ENat.coe_toNat hGne_top
    obtain ⟨U, hU_an, hU0, hUfact⟩ := (hG_an.analyticOrderAt_eq_natCast).mp hm.symm
    have hUpos : ∀ᶠ w in 𝓝 (0 : ℂ), ‖U 0‖ / 2 ≤ ‖U w‖ := by
      have hcont : ContinuousAt (fun w => ‖U w‖) 0 := hU_an.continuousAt.norm
      have hgt : ‖U 0‖ / 2 < ‖U 0‖ := by have := norm_pos_iff.mpr hU0; linarith
      filter_upwards [hcont.eventually (eventually_gt_nhds hgt)] with w hw; exact le_of_lt hw
    obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp (hUfact.and hUpos)
    refine exists_polynomial_of_polyGrowth_eventually hf (M := ‖f 0‖ + 2 / ‖U 0‖)
      (R₀ := max 1 (δ⁻¹ + 1)) (d := m) (by positivity) ?_
    intro z hz
    have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hz
    have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
    have hwne : z⁻¹ ≠ 0 := inv_ne_zero hz0
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
    have hwsmall : dist z⁻¹ (0:ℂ) < δ := by
      rw [dist_zero_right, norm_inv]
      have hd2 : δ⁻¹ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hz
      rw [inv_lt_comm₀ hzpos hδ]; linarith
    obtain ⟨hUf, hUb⟩ := hδsub hwsmall
    have hUw0 : U z⁻¹ ≠ 0 := fun h => by rw [h, norm_zero] at hUb; nlinarith [norm_pos_iff.mpr hU0]
    have hgz : g z⁻¹ = (f z - f 0)⁻¹ := by rw [hg_def]; simp [inv_inv]
    have hGw : (f z - f 0)⁻¹ = z⁻¹ ^ m * U z⁻¹ := by
      rw [← hgz, ← hGg z⁻¹ hwne, hUf]; simp [sub_zero, smul_eq_mul]
    have hfz0 : ‖f z - f 0‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; exact fun h => by
        have := hfar z hz1; rw [h, norm_zero] at this; linarith
    have hfeq : f z - f 0 = (z⁻¹ ^ m * U z⁻¹)⁻¹ := by rw [← hGw, inv_inv]
    have hnorm : ‖f z - f 0‖ = ‖z‖ ^ m / ‖U z⁻¹‖ := by
      rw [hfeq, norm_inv, norm_mul, norm_pow, norm_inv, inv_pow, mul_inv, inv_inv,
        ← div_eq_mul_inv]
    have hUinv_le : ‖z‖ ^ m / ‖U z⁻¹‖ ≤ ‖z‖ ^ m * (2 / ‖U 0‖) := by
      rw [div_eq_mul_inv]
      gcongr
      rw [← inv_div]
      exact inv_anti₀ (by positivity) hUb
    calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
          have := norm_add_le (f z - f 0) (f 0); simpa using this
      _ = ‖z‖ ^ m / ‖U z⁻¹‖ + ‖f 0‖ := by rw [hnorm]
      _ ≤ ‖z‖ ^ m * (2 / ‖U 0‖) + ‖f 0‖ * ‖z‖ ^ m := by
          have hf0le : ‖f 0‖ ≤ ‖f 0‖ * ‖z‖ ^ m := by
            nlinarith [one_le_pow₀ hz1 (n := m), norm_nonneg (f 0)]
          linarith [hUinv_le, hf0le]
      _ = (‖f 0‖ + 2 / ‖U 0‖) * ‖z‖ ^ m := by ring
  · exfalso
    have hLpos : 0 < ‖L‖ := norm_pos_iff.mpr hL0
    have hge : ∀ᶠ w in 𝓝[≠] (0:ℂ), ‖L‖ / 2 ≤ ‖g w‖ := by
      have := (htendsto.norm).eventually (eventually_gt_nhds (by linarith : ‖L‖ / 2 < ‖L‖))
      filter_upwards [this] with w hw; linarith
    obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hge)
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0:ℂ) (max 1 (δ⁻¹ + 1))).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    have hbound : ∀ z : ℂ, ‖f z‖ ≤ max K (‖f 0‖ + 2 / ‖L‖) := by
      intro z
      by_cases hzle : ‖z‖ ≤ max 1 (δ⁻¹ + 1)
      · exact le_trans (hK z (by rwa [Metric.mem_closedBall, dist_zero_right])) (le_max_left _ _)
      · rw [not_le] at hzle
        have hz1 : 1 ≤ ‖z‖ := le_trans (le_max_left _ _) hzle.le
        have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
        have hwne : z⁻¹ ≠ 0 := inv_ne_zero hz0
        have hzpos : 0 < ‖z‖ := lt_of_lt_of_le one_pos hz1
        have hwsmall : dist z⁻¹ (0:ℂ) < δ := by
          rw [dist_zero_right, norm_inv]
          have hd2 : δ⁻¹ + 1 ≤ ‖z‖ := le_trans (le_max_right _ _) hzle.le
          rw [inv_lt_comm₀ hzpos hδ]; linarith
        have hgge := hδsub hwsmall hwne
        have hgz : g z⁻¹ = (f z - f 0)⁻¹ := by rw [hg_def]; simp [inv_inv]
        rw [hgz, norm_inv] at hgge
        have hfsub_le : ‖f z - f 0‖ ≤ 2 / ‖L‖ := by
          have h := inv_anti₀ (by positivity : (0:ℝ) < ‖L‖ / 2) hgge
          rwa [inv_inv, inv_div] at h
        calc ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
              have := norm_add_le (f z - f 0) (f 0); simpa using this
          _ ≤ 2 / ‖L‖ + ‖f 0‖ := by linarith
          _ ≤ max K (‖f 0‖ + 2 / ‖L‖) := le_trans (by linarith) (le_max_right _ _)
    have hrange : Bornology.IsBounded (Set.range f) := by
      rw [Metric.isBounded_iff_subset_closedBall (0:ℂ)]
      exact ⟨max K (‖f 0‖ + 2 / ‖L‖), by
        rintro y ⟨z, rfl⟩; rw [Metric.mem_closedBall, dist_zero_right]; exact hbound z⟩
    exact absurd (hinj (hf.apply_eq_apply_of_bounded hrange 0 1)) (by norm_num)

/-! ## Finite-order polynomials are affine (composition-degree argument) -/

/-- The `n`-fold self-composition of `P`, as a polynomial. -/
noncomputable def polyIterate (P : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  (fun Q => P.comp Q)^[n] Polynomial.X

theorem polyIterate_eval (P : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (polyIterate P n).eval z = (fun w => P.eval w)^[n] z := by
  induction n with
  | zero => simp [polyIterate]
  | succ k ih =>
    rw [polyIterate, Function.iterate_succ_apply', ← polyIterate, eval_comp, ih,
      Function.iterate_succ_apply']

theorem polyIterate_natDegree (P : Polynomial ℂ) (n : ℕ) :
    (polyIterate P n).natDegree = P.natDegree ^ n := by
  induction n with
  | zero => simp [polyIterate]
  | succ k ih =>
    rw [polyIterate, Function.iterate_succ_apply', ← polyIterate, natDegree_comp, ih, pow_succ,
      mul_comm]

/-- **A finite-order polynomial map is affine.**  If `(P.eval)^[n] = id` with `n ≥ 1`, then
`P` has degree exactly `1`: `(deg P)^n = deg X = 1` forces `deg P = 1` (degree `0` is a
constant, whose iterate is not the identity). -/
theorem natDegree_eq_one_of_iterate_id {P : Polynomial ℂ} {n : ℕ} (hn : 0 < n)
    (hid : (fun w => P.eval w)^[n] = id) : P.natDegree = 1 := by
  have hpoly : polyIterate P n = Polynomial.X := by
    apply Polynomial.funext
    intro z
    rw [polyIterate_eval, hid, Polynomial.eval_X, id]
  have hdeg : P.natDegree ^ n = 1 := by
    rw [← polyIterate_natDegree, hpoly, natDegree_X]
  exact Nat.pow_eq_one.mp hdeg |>.resolve_right (by omega)

/-- The affine map `x ↦ a x + c` iterated `m` times scales differences by `aᵐ`. -/
theorem iterate_affine_sub (a c : ℂ) (m : ℕ) (z w : ℂ) :
    (fun x => a * x + c)^[m] z - (fun x => a * x + c)^[m] w = a ^ m * (z - w) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
    linear_combination a * ih

/-- **A finite-order entire polynomial automorphism fixing `ρ` is a rotation.**  If
`f = P.eval` with `(f)^[n] = id` (`n ≥ 1`) and `f ρ = ρ`, then `f z = ρ + a(z − ρ)` with
`a^n = 1`: the rotation about `ρ` by an `n`-th root of unity. -/
theorem finiteOrder_polynomial_fixing_is_rotation {P : Polynomial ℂ} {ρ : ℂ} {n : ℕ}
    (hn : 0 < n) (hid : (fun w => P.eval w)^[n] = id) (hfix : P.eval ρ = ρ) :
    ∃ a : ℂ, a ^ n = 1 ∧ ∀ z, P.eval z = ρ + a * (z - ρ) := by
  have hdeg : P.natDegree = 1 := natDegree_eq_one_of_iterate_id hn hid
  have hP0 : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
  have hdeg1 : P.degree ≤ 1 := le_trans degree_le_natDegree (by rw [hdeg]; norm_cast)
  have hform : P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_degree_le_one hdeg1
  set a := P.coeff 1 with ha
  set c := P.coeff 0 with hc
  have heval : ∀ z, P.eval z = a * z + c := by
    intro z; rw [hform, eval_add, eval_mul, eval_C, eval_X, eval_C]
  have hfix' : a * ρ + c = ρ := by rw [← heval ρ]; exact hfix
  have hrot : ∀ z, P.eval z = ρ + a * (z - ρ) := by
    intro z; rw [heval z]; linear_combination hfix'
  have hfeq : (fun w => P.eval w) = fun x => a * x + c := funext heval
  have hid' : (fun x => a * x + c)^[n] = id := by rw [← hfeq]; exact hid
  have hkey := iterate_affine_sub a c n 1 0
  rw [hid'] at hkey
  simp only [id_eq, sub_zero, mul_one] at hkey
  exact ⟨a, hkey.symm, hrot⟩

/-- **A finite-order entire automorphism fixing `ρ` is a rotation.**  Full classification: an
entire `f` with `f^[n] = id` (`n ≥ 1`) fixing `ρ` is `z ↦ ρ + a(z − ρ)` with `a^n = 1`.  The
finite order makes `f` injective, the collision makes it a polynomial, and the
composition-degree argument makes that polynomial a rotation.  So the *only* finite-order
entire symmetry fixing `ρ` is a rotation about `ρ`. -/
theorem finiteOrder_entire_fixing_is_rotation {f : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    (hf : Differentiable ℂ f) (hn : 0 < n) (hid : f^[n] = id) (hfix : f ρ = ρ) :
    ∃ a : ℂ, a ^ n = 1 ∧ ∀ z, f z = ρ + a * (z - ρ) := by
  have hinj : Function.Injective f := by
    have hli : Function.LeftInverse (f^[n-1]) f := by
      intro x
      have h1 : f^[n-1] (f x) = f^[n] x := by
        rw [← Function.iterate_succ_apply]; congr 1; omega
      rw [h1, hid, id]
    exact hli.injective
  obtain ⟨P, hP⟩ := exists_polynomial_of_entire_injective hf hinj
  have hid' : (fun w => P.eval w)^[n] = id := by
    have : (fun w => P.eval w) = f := by funext w; exact (hP w).symm
    rw [this]; exact hid
  have hfix' : P.eval ρ = ρ := by rw [← hP ρ]; exact hfix
  obtain ⟨a, han, hrot⟩ := finiteOrder_polynomial_fixing_is_rotation hn hid' hfix'
  exact ⟨a, han, fun z => by rw [hP z]; exact hrot z⟩

end RHTower
