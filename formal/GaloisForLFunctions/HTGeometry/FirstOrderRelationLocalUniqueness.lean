import GaloisForLFunctions.HTGeometry.ParabolicFatouJetRealization

/-!
# Local uniqueness for first-order algebraic differential relations

Let `Q ∈ ℂ[X][Y]` and let `(a₀, b₀)` be a point with `∂_Y Q (a₀, b₀) ≠ 0`.  Two holomorphic
solutions `v`, `w` of the implicit first-order equation `Q(u, u') = 0` on a connected open set, which
agree at one point `z₀` and whose values and derivatives at `z₀` are close to `(a₀, b₀)`, agree
everywhere.

No implicit function theorem and no local branch `u' = R(u)` is used.  Divided differences split

`0 = Q(v, v') - Q(w, w') = (v - w)·E + (v' - w')·D`,

where `D` is close to `∂_Y Q (a₀, b₀) ≠ 0` and `E` is bounded, so `|v' - w'| ≤ K |v - w|` near `z₀`.
Grönwall's inequality along every radius of a small disc forces `v = w` there, and the identity
theorem propagates the equality.
-/

open Polynomial Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- Evaluation of a bivariate polynomial `Q ∈ ℂ[X][Y]` at `(a, b)`: the coefficients, which are
polynomials in `X`, are evaluated at `a`, and `Y` is then set to `b`. -/
noncomputable def relEval (Q : Polynomial (Polynomial ℂ)) (a b : ℂ) : ℂ :=
  (Q.map (evalRingHom a)).eval b

theorem relEval_eq_sum (Q : Polynomial (Polynomial ℂ)) (a b : ℂ) :
    relEval Q a b = ∑ j ∈ Finset.range (Q.natDegree + 1), (Q.coeff j).eval a * b ^ j := by
  rw [relEval, eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_map, coe_evalRingHom]

theorem continuous_relEval (Q : Polynomial (Polynomial ℂ)) :
    Continuous fun p : ℂ × ℂ => relEval Q p.1 p.2 := by
  simp_rw [relEval_eq_sum]
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((Q.coeff j).continuous.comp continuous_fst).mul (continuous_snd.pow j)

theorem analyticAt_relEval (Q : Polynomial (Polynomial ℂ)) {A B : ℂ → ℂ} {z₀ : ℂ}
    (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀) :
    AnalyticAt ℂ (fun z => relEval Q (A z) (B z)) z₀ := by
  simp_rw [relEval_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun j _ => ?_
  exact ((analyticAt_polyEval_parabolicFatouJetRealization (Q.coeff j) (A z₀)).comp hA).mul
    (hB.fun_pow j)

/-! ## Divided differences -/

/-- The divided difference of `relEval Q a ·` between `b` and `b'`. -/
noncomputable def relDivY (Q : Polynomial (Polynomial ℂ)) (a b b' : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (Q.natDegree + 1),
    (Q.coeff j).eval a * ∑ i ∈ Finset.range j, b ^ i * b' ^ (j - 1 - i)

/-- The divided difference of `relEval Q · b` between `a` and `a'`. -/
noncomputable def relDivX (Q : Polynomial (Polynomial ℂ)) (a a' b : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (Q.natDegree + 1), polyDivDiff (Q.coeff j) a a' * b ^ j

theorem relEval_sub_relEval_right (Q : Polynomial (Polynomial ℂ)) (a b b' : ℂ) :
    relEval Q a b - relEval Q a b' = (b - b') * relDivY Q a b b' := by
  rw [relEval_eq_sum, relEval_eq_sum, relDivY, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hgeo := geom_sum₂_mul b b' j
  linear_combination -((Q.coeff j).eval a) * hgeo

theorem relEval_sub_relEval_left (Q : Polynomial (Polynomial ℂ)) (a a' b : ℂ) :
    relEval Q a b - relEval Q a' b = (a - a') * relDivX Q a a' b := by
  rw [relEval_eq_sum, relEval_eq_sum, relDivX, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := polyDivDiff_spec (Q.coeff j) a a'
  linear_combination b ^ j * h

theorem continuous_polyDivDiff (P : Polynomial ℂ) :
    Continuous fun p : ℂ × ℂ => polyDivDiff P p.1 p.2 := by
  unfold polyDivDiff
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_finsetSum _ fun i _ => (continuous_fst.pow i).mul (continuous_snd.pow _)

theorem continuous_relDivY (Q : Polynomial (Polynomial ℂ)) :
    Continuous fun p : ℂ × ℂ × ℂ => relDivY Q p.1 p.2.1 p.2.2 := by
  unfold relDivY
  refine continuous_finsetSum _ fun j _ => ?_
  refine ((Q.coeff j).continuous.comp continuous_fst).mul ?_
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_fst.comp continuous_snd).pow i).mul ((continuous_snd.comp continuous_snd).pow _)

theorem continuous_relDivX (Q : Polynomial (Polynomial ℂ)) :
    Continuous fun p : ℂ × ℂ × ℂ => relDivX Q p.1 p.2.1 p.2.2 := by
  simp only [relDivX, polyDivDiff]
  fun_prop

/-- On the diagonal the divided difference in `Y` is the partial derivative `∂_Y Q`. -/
theorem relDivY_self (Q : Polynomial (Polynomial ℂ)) (a b : ℂ) :
    relDivY Q a b b = relEval (derivative Q) a b := by
  have hdeg : (derivative Q).natDegree < Q.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_derivative_le Q) (by omega)
  rw [relEval, eval_eq_sum_range' (lt_of_le_of_lt natDegree_map_le hdeg), relDivY]
  have hinner : ∀ j : ℕ, ∑ i ∈ Finset.range j, b ^ i * b ^ (j - 1 - i) = (j : ℂ) * b ^ (j - 1) := by
    intro j
    rw [Finset.sum_congr rfl fun i hi => by
      rw [← pow_add, show i + (j - 1 - i) = j - 1 by
        have := Finset.mem_range.mp hi; omega]]
    simp
  simp_rw [hinner, coeff_map, coe_evalRingHom, coeff_derivative, eval_mul]
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have htop : Q.coeff (Q.natDegree + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
  simp only [htop, eval_zero, zero_mul, add_zero, Nat.cast_zero, mul_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.cast_add, Nat.cast_one, eval_add, eval_natCast, eval_one, Nat.add_sub_cancel]
  ring

/-! ## Grönwall along a radius -/

/-- A holomorphic function on a disc vanishing at the centre, whose derivative is bounded by a fixed
multiple of itself, vanishes on the disc. -/
theorem eqOn_ball_zero_of_norm_deriv_le {e : ℂ → ℂ} {z₀ : ℂ} {r C : ℝ}
    (he : DifferentiableOn ℂ e (ball z₀ r)) (h0 : e z₀ = 0)
    (hbound : ∀ z ∈ ball z₀ r, ‖deriv e z‖ ≤ C * ‖e z‖) :
    ∀ z ∈ ball z₀ r, e z = 0 := by
  intro z hz
  set γ : ℂ → ℂ := fun u => z₀ + u * (z - z₀) with hγ
  have hγball : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → γ t ∈ ball z₀ r := by
    intro t ht
    rw [mem_ball, dist_eq_norm]
    have : γ t - z₀ = (t : ℂ) * (z - z₀) := by simp [hγ]
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hz' : ‖z - z₀‖ < r := by rwa [mem_ball, dist_eq_norm] at hz
    nlinarith [norm_nonneg (z - z₀), ht.2]
  have hderiv : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun s : ℝ => e (γ s)) (deriv e (γ t) * (z - z₀)) t := by
    intro t ht
    have hdiff : DifferentiableAt ℂ e (γ t) :=
      he.differentiableAt (isOpen_ball.mem_nhds (hγball t ht))
    have hγd : HasDerivAt γ (z - z₀) (t : ℂ) := by
      simpa [hγ] using ((hasDerivAt_id (t : ℂ)).mul_const (z - z₀)).const_add z₀
    exact (hdiff.hasDerivAt.comp (t : ℂ) hγd).comp_ofReal
  have hcont : ContinuousOn (fun s : ℝ => e (γ s)) (Icc 0 1) :=
    fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := C * ‖z - z₀‖)
    (ε := 0) hcont (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [hγ, h0])
    (fun t ht => by
      rw [norm_mul, add_zero]
      have h1 := mul_le_mul_of_nonneg_right (hbound (γ t) (hγball t (Ico_subset_Icc_self ht)))
        (norm_nonneg (z - z₀))
      calc ‖deriv e (γ t)‖ * ‖z - z₀‖ ≤ C * ‖e (γ t)‖ * ‖z - z₀‖ := h1
        _ = C * ‖z - z₀‖ * ‖e (γ t)‖ := by ring)
    1 (right_mem_Icc.mpr zero_le_one)
  rw [gronwallBound_ε0_δ0] at hgron
  have hγ1 : γ 1 = z := by simp [hγ]
  simpa [hγ1] using hgron

/-! ## Local uniqueness -/

/-- **Local uniqueness for an implicit first-order algebraic equation.**  Near a point where
`∂_Y Q ≠ 0`, two holomorphic solutions of `Q(u, u') = 0` on a connected open set that agree at one
point, with values and derivatives there close to `(a₀, b₀)`, coincide. -/
theorem eqOn_of_relEval_eq_zero {Q : Polynomial (Polynomial ℂ)} {a₀ b₀ : ℂ}
    (hQ : relEval (derivative Q) a₀ b₀ ≠ 0) :
    ∃ δ > 0, ∀ {U : Set ℂ} {z₀ : ℂ} {v w : ℂ → ℂ}, IsOpen U → IsPreconnected U → z₀ ∈ U →
      DifferentiableOn ℂ v U → DifferentiableOn ℂ w U →
      (∀ z ∈ U, relEval Q (v z) (deriv v z) = 0) → (∀ z ∈ U, relEval Q (w z) (deriv w z) = 0) →
      v z₀ = w z₀ → ‖v z₀ - a₀‖ < δ → ‖deriv v z₀ - b₀‖ < δ → ‖deriv w z₀ - b₀‖ < δ →
      EqOn v w U := by
  set q₀ := relEval (derivative Q) a₀ b₀ with hq₀
  have hq₀pos : 0 < ‖q₀‖ := norm_pos_iff.mpr hQ
  -- the divided difference in `Y` stays away from zero near `(a₀, b₀, b₀)`
  obtain ⟨δ₁, hδ₁, hD⟩ : ∃ δ₁ > 0, ∀ p : ℂ × ℂ × ℂ, dist p (a₀, b₀, b₀) < δ₁ →
      ‖q₀‖ / 2 < ‖relDivY Q p.1 p.2.1 p.2.2‖ := by
    have hc := (continuous_relDivY Q).continuousAt (x := (a₀, b₀, b₀))
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ₁, hδ₁, h⟩ := hc (‖q₀‖ / 2) (by linarith)
    refine ⟨δ₁, hδ₁, fun p hp => ?_⟩
    have h1 := h hp
    rw [dist_eq_norm] at h1
    have hself : relDivY Q (a₀, b₀, b₀).1 (a₀, b₀, b₀).2.1 (a₀, b₀, b₀).2.2 = q₀ :=
      relDivY_self Q a₀ b₀
    rw [hself] at h1
    have := norm_sub_norm_le q₀ (relDivY Q p.1 p.2.1 p.2.2)
    rw [norm_sub_rev] at h1
    linarith
  -- the divided difference in `X` stays bounded near `(a₀, a₀, b₀)`
  set K := ‖relDivX Q a₀ a₀ b₀‖ + 1 with hK
  obtain ⟨δ₂, hδ₂, hE⟩ : ∃ δ₂ > 0, ∀ p : ℂ × ℂ × ℂ, dist p (a₀, a₀, b₀) < δ₂ →
      ‖relDivX Q p.1 p.2.1 p.2.2‖ ≤ K := by
    have hc := (continuous_relDivX Q).continuousAt (x := (a₀, a₀, b₀))
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ₂, hδ₂, h⟩ := hc 1 one_pos
    refine ⟨δ₂, hδ₂, fun p hp => ?_⟩
    have h1 := h hp
    rw [dist_eq_norm] at h1
    have := norm_le_norm_add_norm_sub' (relDivX Q p.1 p.2.1 p.2.2) (relDivX Q a₀ a₀ b₀)
    rw [hK]
    linarith
  set δ := min δ₁ δ₂ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, ?_⟩
  intro U z₀ v w hU hUc hz₀ hv hw hQv hQw hvw hva hvb hwb
  have hvd : DifferentiableOn ℂ (deriv v) U := hv.deriv hU
  have hwd : DifferentiableOn ℂ (deriv w) U := hw.deriv hU
  have hcont : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U → ∀ᶠ z in 𝓝 z₀, ‖g z - g z₀‖ < δ := by
    intro g hg
    have hca : ContinuousAt g z₀ := (hg.differentiableAt (hU.mem_nhds hz₀)).continuousAt
    have := hca.eventually (Metric.ball_mem_nhds (g z₀) hδpos)
    filter_upwards [this] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ball z₀ r ⊆ U ∧ ∀ z ∈ ball z₀ r,
      ‖v z - v z₀‖ < δ ∧ ‖w z - w z₀‖ < δ ∧ ‖deriv v z - deriv v z₀‖ < δ ∧
        ‖deriv w z - deriv w z₀‖ < δ := by
    have hev := (hU.mem_nhds hz₀)
    have hall : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ (‖v z - v z₀‖ < δ ∧ ‖w z - w z₀‖ < δ ∧
        ‖deriv v z - deriv v z₀‖ < δ ∧ ‖deriv w z - deriv w z₀‖ < δ) := by
      filter_upwards [hev, hcont v hv, hcont w hw, hcont _ hvd, hcont _ hwd] with z h1 h2 h3 h4 h5
      exact ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff_ball.mp hall
    exact ⟨r, hr, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2⟩
  have hmin₁ : 2 * δ ≤ δ₁ := by rw [hδ]; linarith [min_le_left δ₁ δ₂]
  have hmin₂ : 2 * δ ≤ δ₂ := by rw [hδ]; linarith [min_le_right δ₁ δ₂]
  -- the Lipschitz comparison of the derivatives
  have hkey : ∀ z ∈ ball z₀ r, ‖deriv (fun z => v z - w z) z‖ ≤ (2 * K / ‖q₀‖) * ‖v z - w z‖ := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hball.2 z hz
    have hzU := hball.1 hz
    have hdv : DifferentiableAt ℂ v z := hv.differentiableAt (hU.mem_nhds hzU)
    have hdw : DifferentiableAt ℂ w z := hw.differentiableAt (hU.mem_nhds hzU)
    rw [deriv_fun_sub hdv hdw]
    have hva' : ‖v z - a₀‖ < 2 * δ := by
      have := norm_sub_le_norm_sub_add_norm_sub (v z) (v z₀) a₀; linarith
    have hwa' : ‖w z - a₀‖ < 2 * δ := by
      have hwa0 : ‖w z₀ - a₀‖ < δ := hvw ▸ hva
      have := norm_sub_le_norm_sub_add_norm_sub (w z) (w z₀) a₀; linarith
    have hvb' : ‖deriv v z - b₀‖ < 2 * δ := by
      have := norm_sub_le_norm_sub_add_norm_sub (deriv v z) (deriv v z₀) b₀; linarith
    have hwb' : ‖deriv w z - b₀‖ < 2 * δ := by
      have := norm_sub_le_norm_sub_add_norm_sub (deriv w z) (deriv w z₀) b₀; linarith
    have hDz := hD (w z, deriv v z, deriv w z) (by
      simp only [Prod.dist_eq, Complex.dist_eq]
      refine max_lt (by linarith) (max_lt (by linarith) (by linarith)))
    have hEz := hE (v z, w z, deriv v z) (by
      simp only [Prod.dist_eq, Complex.dist_eq]
      refine max_lt (by linarith) (max_lt (by linarith) (by linarith)))
    have hsplit : (v z - w z) * relDivX Q (v z) (w z) (deriv v z)
        + (deriv v z - deriv w z) * relDivY Q (w z) (deriv v z) (deriv w z) = 0 := by
      rw [← relEval_sub_relEval_left, ← relEval_sub_relEval_right, hQv z hzU, hQw z hzU]
      ring
    have hnorm : ‖deriv v z - deriv w z‖ * ‖relDivY Q (w z) (deriv v z) (deriv w z)‖
        = ‖v z - w z‖ * ‖relDivX Q (v z) (w z) (deriv v z)‖ := by
      rw [← norm_mul, ← norm_mul, eq_neg_of_add_eq_zero_right hsplit, norm_neg]
    have hle : ‖deriv v z - deriv w z‖ * (‖q₀‖ / 2) ≤ ‖v z - w z‖ * K := by
      calc ‖deriv v z - deriv w z‖ * (‖q₀‖ / 2)
          ≤ ‖deriv v z - deriv w z‖ * ‖relDivY Q (w z) (deriv v z) (deriv w z)‖ :=
            mul_le_mul_of_nonneg_left hDz.le (norm_nonneg _)
        _ = ‖v z - w z‖ * ‖relDivX Q (v z) (w z) (deriv v z)‖ := hnorm
        _ ≤ ‖v z - w z‖ * K := mul_le_mul_of_nonneg_left hEz (norm_nonneg _)
    rw [div_mul_eq_mul_div, le_div_iff₀ hq₀pos]
    calc ‖deriv v z - deriv w z‖ * ‖q₀‖ = 2 * (‖deriv v z - deriv w z‖ * (‖q₀‖ / 2)) := by ring
      _ ≤ 2 * (‖v z - w z‖ * K) := by linarith
      _ = 2 * K * ‖v z - w z‖ := by ring
  have hzero := eqOn_ball_zero_of_norm_deriv_le (e := fun z => v z - w z)
    ((hv.mono hball.1).sub (hw.mono hball.1)) (by simp [hvw]) hkey
  have heq : v =ᶠ[𝓝 z₀] w := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    exact sub_eq_zero.mp (hzero z hz)
  exact (hv.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hw.analyticOnNhd hU) hUc hz₀ heq

end GaloisForLFunctions.HTGeometry
