import GaloisForLFunctions.FiniteFreeProbability.ZeroFreeHalfPlaneStability

/-!
# Hurwitz deflation and the concentration of finite free roots

Write the scaled Jensen approximants of `g = Σ f_k u^k` (`f_0 = 1`) through the roots `x` of the
reversed Jensen polynomial `R_d = R_d(g)`:

`Φ_d(u) = Π_{x} (1 − (x/d) u)`,   `Σ_x x/d = −f_1`.

So `Φ_d → g` locally uniformly and the rescaled roots `v = x/d` have a fixed sum. *Hurwitz with
multiplicity* is proved here by deflation: if `g = (1 − u/z) G` then some `v_d` tends to `1/z` and
the product with `v_d` erased converges to `G` (uniform convergence on a large circle, then the
maximum principle). Iterating over a finite set `T` of zeros (repeated according to multiplicity)
splits the rescaled roots as `A_d + B_d` with `Σ_{A_d} v → Σ_T 1/z_i`.

**Concentration.** If all roots have `Im x ≤ 0`, then

`Σ_{v∈B_d} (−Im v) → τ(T) = Im f_1 + Σ_T Im(1/z_i)`,

hence at most `|T| + (τ(T) + ε) d/μ` roots have `Im x ≤ −μ`, for large `d`. When `τ(T)` can be made
arbitrarily small, almost all roots converge to the real axis: only finitely many outliers
`x ≈ d/z_i` carry the imaginary mass.
-/

open Polynomial Filter Topology Complex Metric

namespace FiniteFreeProbability

noncomputable section

/-! ## Products of linear factors indexed by a multiset -/

/-- `Π_{v∈V} (1 − v u)`. -/
def linearProd (V : Multiset ℂ) (u : ℂ) : ℂ :=
  (V.map fun v => 1 - v * u).prod

theorem linearProd_cons (v : ℂ) (V : Multiset ℂ) (u : ℂ) :
    linearProd (v ::ₘ V) u = (1 - v * u) * linearProd V u := by
  simp [linearProd]

theorem differentiable_linearProd (V : Multiset ℂ) : Differentiable ℂ (linearProd V) := by
  induction V using Multiset.induction_on with
  | empty =>
    have : linearProd 0 = fun _ => 1 := funext fun u => by simp [linearProd]
    rw [this]
    exact differentiable_const _
  | cons v V ih =>
    have : linearProd (v ::ₘ V) = fun u => (1 - v * u) * linearProd V u :=
      funext (linearProd_cons v V)
    rw [this]
    fun_prop

theorem exists_mem_of_linearProd_eq_zero {V : Multiset ℂ} {u : ℂ} (h : linearProd V u = 0) :
    ∃ v ∈ V, v * u = 1 := by
  rw [linearProd, Multiset.prod_eq_zero_iff, Multiset.mem_map] at h
  obtain ⟨v, hv, h⟩ := h
  exact ⟨v, hv, (sub_eq_zero.1 h).symm⟩

theorem linearProd_eq_of_mem {V : Multiset ℂ} {v : ℂ} (hv : v ∈ V) (u : ℂ) :
    linearProd V u = (1 - v * u) * linearProd (V.erase v) u := by
  rw [← linearProd_cons, Multiset.cons_erase hv]

/-! ## Deflation -/

/-- Hurwitz, existence direction, for a locally uniform limit of entire functions. -/
theorem eventually_exists_zero_of_tendstoLocallyUniformly {P : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hP : TendstoLocallyUniformly P g atTop) (hPd : ∀ n, Differentiable ℂ (P n))
    (hg : Differentiable ℂ g) {a z : ℂ} (ha : g a ≠ 0) (hz : g z = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in atTop, ∃ u ∈ ball z r, P n u = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hQ⟩ := extraction_of_frequently_atTop hcon
  have hconv : TendstoLocallyUniformly (fun n => P (φ n)) g atTop := fun u hu x => by
    obtain ⟨t, ht, h⟩ := hP u hu x
    exact ⟨t, ht, hφ.tendsto_atTop.eventually h⟩
  have hmem := RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv
    (fun w _ => hg.analyticAt w) (Eventually.of_forall fun n => hPd _)
    isOpen_ball.isClosed_compl
    (Eventually.of_forall fun n w hw hwb => hQ n ⟨w, hwb, hw⟩) ha hz
  exact hmem (mem_ball_self hr)

/-- **Deflation.** If `Π_{v∈V_n}(1 − vu) → g = (1 − u/z) G` locally uniformly, some `v_n ∈ V_n` tends
to `1/z`, and the product with `v_n` erased converges to `G`. -/
theorem exists_deflation {V : ℕ → Multiset ℂ} {g G : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hG : Differentiable ℂ G) (hfac : ∀ u, g u = (1 - u / z) * G u) (hne : ∃ a, g a ≠ 0)
    (hV : TendstoLocallyUniformly (fun n => linearProd (V n)) g atTop) :
    ∃ v : ℕ → ℂ, (∀ᶠ n in atTop, v n ∈ V n) ∧ Tendsto v atTop (𝓝 (1 / z)) ∧
      TendstoLocallyUniformly (fun n => linearProd ((V n).erase (v n))) G atTop := by
  have hg : Differentiable ℂ g := by
    rw [show g = fun u => (1 - u / z) * G u from funext hfac]
    fun_prop
  obtain ⟨a, ha⟩ := hne
  have hgz : g z = 0 := by rw [hfac, div_self hz, sub_self, zero_mul]
  have hnear : ∀ ε > 0, ∀ᶠ n in atTop, ∃ v ∈ V n, dist v (1 / z) < ε := by
    intro ε hε
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1 (continuousAt_inv₀ hz) ε hε
    filter_upwards [eventually_exists_zero_of_tendstoLocallyUniformly hV
      (fun n => differentiable_linearProd _) hg ha hgz hr] with n hn
    obtain ⟨u, hu, hu0⟩ := hn
    obtain ⟨v, hv, hvu⟩ := exists_mem_of_linearProd_eq_zero hu0
    refine ⟨v, hv, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hvu, one_div]
    exact hball (mem_ball.1 hu)
  -- the element of `V n` nearest to `1/z`
  have hex : ∀ n, ∃ v : ℂ, (V n ≠ 0 → v ∈ V n) ∧
      ∀ w ∈ V n, dist v (1 / z) ≤ dist w (1 / z) := by
    intro n
    by_cases h : V n = 0
    · exact ⟨0, fun h' => absurd h h', fun w hw => by rw [h] at hw; simp at hw⟩
    · obtain ⟨w₀, hw₀⟩ := Multiset.exists_mem_of_ne_zero h
      obtain ⟨v, hv, hmin⟩ := (V n).toFinset.exists_min_image (fun v => dist v (1 / z))
        ⟨w₀, Multiset.mem_toFinset.2 hw₀⟩
      exact ⟨v, fun _ => Multiset.mem_toFinset.1 hv,
        fun w hw => hmin w (Multiset.mem_toFinset.2 hw)⟩
  choose v hvmem hvmin using hex
  have hmem : ∀ᶠ n in atTop, v n ∈ V n := by
    filter_upwards [hnear 1 one_pos] with n hn
    obtain ⟨w, hw, _⟩ := hn
    exact hvmem n fun h => by rw [h] at hw; simp at hw
  have hlim : Tendsto v atTop (𝓝 (1 / z)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hnear ε hε] with n hn
    obtain ⟨w, hw, hwd⟩ := hn
    exact (hvmin n w hw).trans_lt hwd
  refine ⟨v, hmem, hlim, ?_⟩
  -- uniform convergence on a large circle, then the maximum principle
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall z
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall z R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set m := R / (2 * ‖z‖)
  have hm : 0 < m := by positivity
  set B := ‖z‖ + R
  have hB : 0 < B := by positivity
  have hcont : Continuous fun u => u * G u := continuous_id.mul hG.continuous
  obtain ⟨C₀, hC₀⟩ := (isCompact_sphere z R).exists_bound_of_continuousOn hcont.continuousOn
  set C := |C₀| + 1
  have hC : 0 < C := by positivity
  have hCb : ∀ u ∈ sphere z R, ‖u * G u‖ ≤ C := fun u hu => by
    have := hC₀ u hu
    have := le_abs_self C₀
    simp only [C]
    linarith
  have hVS := (tendstoLocallyUniformly_iff_forall_isCompact.1 hV) (sphere z R)
    (isCompact_sphere z R)
  rw [Metric.tendstoUniformlyOn_iff] at hVS ⊢
  intro ε hε
  set η := ε / 2
  have hη : 0 < η := half_pos hε
  have hδ : 0 < min (m / B) (η * m / (2 * C)) := lt_min (by positivity) (by positivity)
  filter_upwards [hVS (η * m / 2) (by positivity), hmem,
    (Metric.tendsto_nhds.1 hlim) _ hδ] with n h1 h2 h3 u hu
  rw [dist_eq_norm] at h3
  have hd1 : ‖v n - 1 / z‖ * B ≤ m :=
    (le_div_iff₀ hB).1 (h3.le.trans (min_le_left _ _))
  have hd2 : ‖v n - 1 / z‖ * C < η * m / 2 := by
    have := h3.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at this
    linarith
  have hsph : ∀ w ∈ sphere z R, ‖linearProd ((V n).erase (v n)) w - G w‖ ≤ η := by
    intro w hw
    have hwR : ‖w - z‖ = R := mem_sphere_iff_norm.1 hw
    have hwn : ‖w‖ ≤ B := by
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = B := by rw [hwR]
    have hlow : m ≤ ‖1 - v n * w‖ := by
      have hsplit : 1 - v n * w = (z - w) / z - (v n - 1 / z) * w := by
        field_simp
        ring
      have h2m : ‖(z - w) / z‖ = 2 * m := by
        rw [norm_div, norm_sub_rev, hwR]
        simp only [m]
        field_simp
      have hsmall : ‖(v n - 1 / z) * w‖ ≤ m := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left hwn (norm_nonneg _)).trans hd1
      rw [hsplit]
      have := norm_sub_norm_le ((z - w) / z) ((v n - 1 / z) * w)
      linarith
    have hid : (1 - v n * w) * (linearProd ((V n).erase (v n)) w - G w) =
        (linearProd (V n) w - g w) + (v n - 1 / z) * (w * G w) := by
      rw [mul_sub, ← linearProd_eq_of_mem h2 w, hfac w]
      field_simp
      ring
    have hP := h1 w hw
    rw [dist_comm, dist_eq_norm] at hP
    have hbound : m * ‖linearProd ((V n).erase (v n)) w - G w‖ ≤ m * η := by
      calc m * ‖linearProd ((V n).erase (v n)) w - G w‖
          ≤ ‖1 - v n * w‖ * ‖linearProd ((V n).erase (v n)) w - G w‖ :=
            mul_le_mul_of_nonneg_right hlow (norm_nonneg _)
        _ = ‖(linearProd (V n) w - g w) + (v n - 1 / z) * (w * G w)‖ := by rw [← norm_mul, hid]
        _ ≤ ‖linearProd (V n) w - g w‖ + ‖v n - 1 / z‖ * ‖w * G w‖ := by
            rw [← norm_mul]
            exact norm_add_le _ _
        _ ≤ ‖linearProd (V n) w - g w‖ + ‖v n - 1 / z‖ * C := by
            gcongr
            exact hCb w hw
        _ ≤ m * η := by linarith
    exact le_of_mul_le_mul_left hbound hm
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball z R)
    (f := fun w => linearProd ((V n).erase (v n)) w - G w) isBounded_ball
    (Differentiable.diffContOnCl ((differentiable_linearProd _).sub hG)) (C := η)
    (fun w hw => hsph w (by rwa [frontier_ball z hR.ne'] at hw)) (z := u)
    (by rw [closure_ball z hR.ne']; exact hKR hu)
  rw [dist_comm, dist_eq_norm]
  exact hmax.trans_lt (half_lt_self hε)

/-- **Hurwitz with multiplicity.** If `Π_{v∈V_n}(1 − vu) → g = Π_{i∈T}(1 − u/z_i) · G`, the multisets
split as `V_n = A_n + B_n` with `|A_n| = |T|`, `Σ_{A_n} v → Σ_T 1/z_i` and `Π_{B_n}(1 − vu) → G`. -/
theorem exists_multiset_deflation {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (T : Finset ι)
    (hz : ∀ i ∈ T, z i ≠ 0) :
    ∀ {V : ℕ → Multiset ℂ} {g G : ℂ → ℂ}, Differentiable ℂ G →
      (∀ u, g u = (∏ i ∈ T, (1 - u / z i)) * G u) → (∃ a, g a ≠ 0) →
      TendstoLocallyUniformly (fun n => linearProd (V n)) g atTop →
      ∃ A B : ℕ → Multiset ℂ,
        (∀ᶠ n in atTop, V n = A n + B n ∧ Multiset.card (A n) = T.card) ∧
        Tendsto (fun n => (A n).sum) atTop (𝓝 (∑ i ∈ T, 1 / z i)) ∧
        TendstoLocallyUniformly (fun n => linearProd (B n)) G atTop := by
  induction T using Finset.induction_on with
  | empty =>
    intro V g G hG hfac _ hV
    have : g = G := funext fun u => by simpa using hfac u
    subst this
    exact ⟨fun _ => 0, V, Eventually.of_forall fun n => by simp, by simp, hV⟩
  | insert j T hj ih =>
    intro V g G hG hfac hne hV
    have hzj := hz j (Finset.mem_insert_self j T)
    set G' : ℂ → ℂ := fun u => (1 - u / z j) * G u
    have hG' : Differentiable ℂ G' := by
      simp only [G']
      fun_prop
    have hfac' : ∀ u, g u = (∏ i ∈ T, (1 - u / z i)) * G' u := fun u => by
      rw [hfac u, Finset.prod_insert hj]
      simp only [G']
      ring
    obtain ⟨A, B, hsplit, hsum, hB⟩ :=
      ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) hG' hfac' hne hV
    obtain ⟨a, ha⟩ := hne
    have hne' : ∃ a, G' a ≠ 0 := ⟨a, fun h => ha (by rw [hfac', h, mul_zero])⟩
    obtain ⟨v, hmem, hlim, hE⟩ :=
      exists_deflation (V := B) (g := G') hzj hG (fun u => rfl) hne' hB
    refine ⟨fun n => v n ::ₘ A n, fun n => (B n).erase (v n), ?_, ?_, hE⟩
    · filter_upwards [hsplit, hmem] with n hn hm
      refine ⟨?_, by rw [Multiset.card_cons, hn.2, Finset.card_insert_of_notMem hj]⟩
      rw [hn.1, Multiset.cons_add, ← Multiset.add_cons, Multiset.cons_erase hm]
    · simp only [Multiset.sum_cons]
      rw [Finset.sum_insert hj]
      exact hlim.add hsum

/-! ## The roots of the reversed Jensen polynomials -/

/-- The rescaled roots `x/d` of `R_d(f)`, with multiplicity. -/
def jensenScaledRoots (f : ℕ → ℂ) (d : ℕ) : Multiset ℂ :=
  (jensenRev d (PowerSeries.mk f)).roots.map fun x => x / (d : ℂ)

theorem constantCoeff_mk (f : ℕ → ℂ) : PowerSeries.constantCoeff (PowerSeries.mk f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]

theorem natDegree_jensenRev_mk {f : ℕ → ℂ} (hf0 : f 0 = 1) (d : ℕ) :
    (jensenRev d (PowerSeries.mk f)).natDegree = d :=
  natDegree_jensenRev (by rw [constantCoeff_mk, hf0]; exact one_ne_zero)

theorem leadingCoeff_jensenRev_mk {f : ℕ → ℂ} (hf0 : f 0 = 1) (d : ℕ) :
    (jensenRev d (PowerSeries.mk f)).leadingCoeff = 1 := by
  rw [leadingCoeff, natDegree_jensenRev_mk hf0, coeff_jensenRev_self, constantCoeff_mk, hf0]

theorem card_roots_jensenRev_mk {f : ℕ → ℂ} (hf0 : f 0 = 1) (d : ℕ) :
    Multiset.card (jensenRev d (PowerSeries.mk f)).roots = d := by
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_jensenRev_mk hf0]

theorem multiset_prod_sub_eq (M : Multiset ℂ) {c e u : ℂ} (h : ∀ x : ℂ, c * ((x / e) * u) = x) :
    (M.map fun x => c - x).prod = c ^ Multiset.card M * (M.map fun x => 1 - (x / e) * u).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
    have := h a
    linear_combination (c ^ Multiset.card M * (M.map fun x => 1 - (x / e) * u).prod) * this

/-- `Φ_d(u) = Π_x (1 − (x/d) u)` over the roots `x` of `R_d(f)`. -/
theorem scaledJensen_eq_linearProd {f : ℕ → ℂ} (hf0 : f 0 = 1) {d : ℕ} (hd : 0 < d) (u : ℂ) :
    scaledJensen f d u = linearProd (jensenScaledRoots f d) u := by
  by_cases hu : u = 0
  · subst hu
    rw [scaledJensen_zero, hf0]
    simp [linearProd, jensenScaledRoots]
  · have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have hc : (d : ℂ) / u ≠ 0 := div_ne_zero hd' hu
    have h1 := eval_jensenRev_div f hd hu
    have h2 : (jensenRev d (PowerSeries.mk f)).eval ((d : ℂ) / u) =
        ((d : ℂ) / u) ^ d * linearProd (jensenScaledRoots f d) u := by
      conv_lhs => rw [(IsAlgClosed.splits (jensenRev d (PowerSeries.mk f))).eq_prod_roots]
      rw [leadingCoeff_jensenRev_mk hf0, map_one, one_mul, eval_multiset_prod, Multiset.map_map,
        linearProd, jensenScaledRoots, Multiset.map_map]
      have := multiset_prod_sub_eq (jensenRev d (PowerSeries.mk f)).roots (c := (d : ℂ) / u)
        (e := (d : ℂ)) (u := u) (fun x => by field_simp)
      rw [card_roots_jensenRev_mk hf0] at this
      simpa only [Function.comp_def, eval_sub, eval_X, eval_C] using this
    exact mul_left_cancel₀ (pow_ne_zero d hc) (h1.symm.trans h2)

theorem multiset_sum_map_div (M : Multiset ℂ) (c : ℂ) :
    (M.map fun x => x / c).sum = M.sum / c := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih => simp [ih, add_div]

/-- The first moment: `Σ_x x/d = −f_1`. -/
theorem sum_jensenScaledRoots {f : ℕ → ℂ} (hf0 : f 0 = 1) {d : ℕ} (hd : 0 < d) :
    (jensenScaledRoots f d).sum = -f 1 := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hnext := (IsAlgClosed.splits (jensenRev d (PowerSeries.mk f))).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [leadingCoeff_jensenRev_mk hf0, nextCoeff_of_natDegree_pos (by rw [natDegree_jensenRev_mk hf0]; exact hd),
    natDegree_jensenRev_mk hf0, coeff_jensenRev d _ (Nat.sub_le d 1),
    show d - (d - 1) = 1 by omega, PowerSeries.coeff_mk, Nat.descFactorial_one] at hnext
  rw [jensenScaledRoots, multiset_sum_map_div, div_eq_iff hd']
  linear_combination hnext

theorem card_filter_mul_le (B : Multiset ℂ) (hB : ∀ v ∈ B, v.im ≤ 0) (c : ℝ) :
    (Multiset.card (B.filter fun v => v.im ≤ -c) : ℝ) * c ≤ -B.sum.im := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a B ih =>
    have h1 := ih fun v hv => hB v (Multiset.mem_cons_of_mem hv)
    have ha := hB a (Multiset.mem_cons_self a B)
    rw [Multiset.sum_cons, add_im]
    by_cases h : a.im ≤ -c
    · rw [Multiset.filter_cons_of_pos (p := fun v => v.im ≤ -c) B h, Multiset.card_cons]
      push_cast
      linarith
    · rw [Multiset.filter_cons_of_neg (p := fun v => v.im ≤ -c) B h]
      linarith

/-! ## Concentration -/

/-- **Counting the roots far from the real axis.** Suppose all roots of all `R_d(f)` have `Im ≤ 0`
and `Σ f_k u^k = Π_{i∈T}(1 − u/z_i) · G` with `G` entire. Then, for large `d`, at most
`|T| + (Im f_1 + Σ_T Im(1/z_i) + ε) d/μ` roots have `Im x ≤ −μ`. -/
theorem eventually_card_filter_le {f : ℕ → ℂ} (hf0 : f 0 = 1)
    (hs : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k)
    (hstab : ∀ d x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im ≤ 0)
    {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (T : Finset ι) (hz : ∀ i ∈ T, z i ≠ 0) {G : ℂ → ℂ}
    (hG : Differentiable ℂ G)
    (hfac : ∀ u, ∑' k, f k * u ^ k = (∏ i ∈ T, (1 - u / z i)) * G u)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop,
      (Multiset.card ((jensenRev d (PowerSeries.mk f)).roots.filter fun x => x.im ≤ -μ) : ℝ) ≤
        T.card + ((f 1).im + (∑ i ∈ T, (1 / z i).im) + ε) / μ * d := by
  have hne : ∃ a, (fun u => ∑' k, f k * u ^ k) a ≠ 0 := ⟨0, by
    simp only
    rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
    simp [hf0]⟩
  have hV : TendstoLocallyUniformly (fun n => linearProd (jensenScaledRoots f n))
      (fun u => ∑' k, f k * u ^ k) atTop := fun s hs' x => by
    obtain ⟨t, ht, h⟩ := tendstoLocallyUniformly_scaledJensen hs (ψ := fun n => n) tendsto_id s hs' x
    refine ⟨t, ht, ?_⟩
    filter_upwards [h, eventually_gt_atTop 0] with n hn hn0 y hy
    rw [← scaledJensen_eq_linearProd hf0 hn0]
    exact hn y hy
  obtain ⟨A, B, hsplit, hsum, -⟩ := exists_multiset_deflation z T hz hG hfac hne hV
  set τ := ∑ i ∈ T, (1 / z i).im
  have hsumim : ∀ᶠ n in atTop, (A n).sum.im < τ + ε := by
    have hc := (Complex.continuous_im.tendsto _).comp hsum
    have hval : (∑ i ∈ T, 1 / z i).im = τ := by rw [Complex.im_sum]
    rw [hval] at hc
    exact hc.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hsplit, hsumim, eventually_gt_atTop 0] with d hd1 hd2 hd0
  obtain ⟨hVAB, hcard⟩ := hd1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  -- the count in terms of the rescaled roots
  have hcount : Multiset.card ((jensenRev d (PowerSeries.mk f)).roots.filter fun x => x.im ≤ -μ) =
      Multiset.card ((jensenScaledRoots f d).filter fun v => v.im ≤ -(μ / d)) := by
    rw [jensenScaledRoots, Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun x _ => ?_
    simp only [Function.comp_apply, Complex.div_natCast_im]
    rw [← neg_div, div_le_div_iff_of_pos_right hdR]
  have hBim : ∀ v ∈ B d, v.im ≤ 0 := fun v hv => by
    have hvV : v ∈ jensenScaledRoots f d := by
      rw [hVAB]
      exact Multiset.mem_add.2 (Or.inr hv)
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hvV
    rw [Complex.div_natCast_im]
    refine div_nonpos_of_nonpos_of_nonneg (hstab d x ?_) hdR.le
    exact isRoot_of_mem_roots hx
  have h1 := card_filter_mul_le (B d) hBim (μ / d)
  have h2 : -(B d).sum.im = (f 1).im + (A d).sum.im := by
    have hs1 := sum_jensenScaledRoots hf0 hd0
    rw [hVAB, Multiset.sum_add] at hs1
    have := congrArg Complex.im hs1
    simp only [add_im, neg_im] at this
    linarith
  have hBcount : (Multiset.card ((B d).filter fun v => v.im ≤ -(μ / d)) : ℝ) ≤
      ((f 1).im + τ + ε) / μ * d := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    have h3 : (Multiset.card ((B d).filter fun v => v.im ≤ -(μ / d)) : ℝ) * (μ / d) ≤
        (f 1).im + τ + ε := by linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hdR.le
    have h5 : (Multiset.card ((B d).filter fun v => v.im ≤ -(μ / d)) : ℝ) * (μ / d) * d =
        (Multiset.card ((B d).filter fun v => v.im ≤ -(μ / d)) : ℝ) * μ := by
      rw [mul_assoc, div_mul_cancel₀ _ hdR.ne']
    linarith
  have hAcount : (Multiset.card ((A d).filter fun v => v.im ≤ -(μ / d)) : ℝ) ≤ T.card := by
    rw [← hcard]
    exact_mod_cast Multiset.card_le_card (Multiset.filter_le _ _)
  rw [hcount, hVAB, Multiset.filter_add, Multiset.card_add]
  push_cast
  linarith

/-- **Concentration on the real axis.** If all roots of all `R_d(f)` have `Im ≤ 0` and the drift
`Im f_1 + Σ_T Im(1/z_i)` can be made arbitrarily small by factoring out zeros, then for every
`μ > 0` the proportion of roots with `Im x ≤ −μ` tends to `0`. -/
theorem tendsto_card_filter_div {f : ℕ → ℂ} (hf0 : f 0 = 1)
    (hs : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k)
    (hstab : ∀ d x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im ≤ 0)
    {ι : Type*} [DecidableEq ι] (z : ι → ℂ) (hz : ∀ i, z i ≠ 0)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ T : Finset ι, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      (∀ u, ∑' k, f k * u ^ k = (∏ i ∈ T, (1 - u / z i)) * G u) ∧
      (f 1).im + ∑ i ∈ T, (1 / z i).im < ε)
    {μ : ℝ} (hμ : 0 < μ) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d (PowerSeries.mk f)).roots.filter fun x => x.im ≤ -μ) : ℝ) / d)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε := η * μ / 8
  have hε : 0 < ε := by positivity
  obtain ⟨T, G, hG, hfac, hτ⟩ := htail ε hε
  have hsmall : ∀ᶠ d : ℕ in atTop, (T.card : ℝ) / d < η / 2 :=
    (tendsto_const_div_atTop_nhds_zero_nat (T.card : ℝ)).eventually (gt_mem_nhds (half_pos hη))
  filter_upwards [eventually_card_filter_le hf0 hs hstab z T (fun i _ => hz i) hG hfac hμ hε,
    hsmall, eventually_gt_atTop 0] with d hd hd2 hd0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hdR]
  rw [div_lt_iff₀ hdR] at hd2
  have h3 : ((f 1).im + ∑ i ∈ T, (1 / z i).im + ε) / μ * d ≤ (2 * ε) / μ * d := by
    gcongr
    linarith
  have h4 : (2 * ε) / μ * d = η / 4 * d := by
    simp only [ε]
    field_simp
    ring
  nlinarith

/-- A vanishing proportion leaves, for large `d`, a root with `Im x > −μ`. -/
theorem eventually_exists_root_im_gt {f : ℕ → ℂ} (hf0 : f 0 = 1) {μ : ℝ}
    (h : Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d (PowerSeries.mk f)).roots.filter fun x => x.im ≤ -μ) : ℝ) / d)
      atTop (𝓝 0)) :
    ∀ᶠ d : ℕ in atTop, ∃ x, (jensenRev d (PowerSeries.mk f)).IsRoot x ∧ -μ < x.im := by
  filter_upwards [h.eventually (gt_mem_nhds one_pos), eventually_gt_atTop 0] with d hd hd0
  by_contra hcon
  push Not at hcon
  have hall : ∀ x ∈ (jensenRev d (PowerSeries.mk f)).roots, x.im ≤ -μ :=
    fun x hx => hcon x (isRoot_of_mem_roots hx)
  rw [Multiset.filter_eq_self.2 hall, card_roots_jensenRev_mk hf0] at hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [div_self hdR] at hd
  exact lt_irrefl _ hd

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.exists_multiset_deflation
#print axioms FiniteFreeProbability.tendsto_card_filter_div
