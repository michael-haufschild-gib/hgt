import GaloisForLFunctions.HTGeometry.ComplexExponentialPolynomial
import GaloisForLFunctions.HTGeometry.FiniteOrderHadamard

/-!
# Zeros of exponential sums and Hurwitz's theorem

* **Exponential sums vanish somewhere** (`exists_zero_of_injective_frequencies`).  A sum
  `Σ_j a_j e^{c_j z}` with at least two pairwise distinct frequencies and nonzero coefficients has a
  complex zero.  If it never vanished it would be `e^{p(z)}` for a polynomial `p` (Hadamard for
  finite order); then `F' = p' F` gives `Σ_j a_j (c_j − p'(z)) e^{c_j z} = 0`, so by independence of
  exponentials `p' = c_j` for every `j`, forcing all frequencies to coincide.

* **Hurwitz's theorem** (`ne_zero_of_tendstoUniformlyOn_of_forall_ne_zero`).  A uniform limit `F` of
  zero-free analytic functions on a closed disk, nonvanishing on the boundary circle, is nonzero at
  the centre.  By Jensen, `log ‖g_n(z₀)‖` equals the circle average of `log ‖g_n‖`, which stays above
  `log(δ/2)` with `δ = min ‖F‖` on the circle; a zero of `F` at `z₀` would push `log ‖g_n(z₀)‖` below.
-/

open Complex Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **An exponential sum with two distinct frequencies has a zero.** -/
theorem exists_zero_of_injective_frequencies {m : ℕ} (c : Fin (m + 2) → ℂ)
    (hc : Function.Injective c) (a : Fin (m + 2) → ℂ) (ha : ∀ j, a j ≠ 0) :
    ∃ z : ℂ, ∑ j, a j * Complex.exp (c j * z) = 0 := by
  by_contra hcon
  push Not at hcon
  set F : ℂ → ℂ := fun z => ∑ j, a j * Complex.exp (c j * z) with hF
  have hFc : F = CExpPoly.cexpFn c (fun j => Polynomial.C (a j)) := by
    funext z
    simp [hF, CExpPoly.cexpFn]
  have hdiff : Differentiable ℂ F := by
    rw [hFc]; exact CExpPoly.differentiable_cexpFn _ _
  obtain ⟨C, A, hC1, hA0, hCA⟩ := CExpPoly.exists_exponentialType_bound c
    (fun j => Polynomial.C (a j))
  have hgrow : ∀ z, ‖F z‖ ≤ Real.exp ((Real.log C + A) * (1 + ‖z‖) ^ 1) := by
    intro z
    have hlog : 0 ≤ Real.log C := Real.log_nonneg hC1
    refine (by rw [hFc]; exact hCA z : ‖F z‖ ≤ C * Real.exp (A * ‖z‖)).trans ?_
    rw [pow_one, show C = Real.exp (Real.log C) from (Real.exp_log (by linarith)).symm,
      Real.log_exp, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [norm_nonneg z]
  obtain ⟨p, hp⟩ := exists_polynomial_exp_of_ne_zero_of_growth hdiff hcon
    (by have := Real.log_nonneg hC1; linarith) hgrow
  -- `F' = p' F`
  have hderivF : ∀ z, deriv F z = ∑ j, a j * c j * Complex.exp (c j * z) := by
    intro z
    have h : HasDerivAt F (∑ j, a j * (c j * Complex.exp (c j * z))) z := by
      rw [hF]
      refine HasDerivAt.fun_sum fun j _ => ?_
      refine HasDerivAt.const_mul (a j) ?_
      have := ((hasDerivAt_id z).const_mul (c j)).cexp
      simpa [mul_comm] using this
    rw [h.deriv]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hFexp : F = fun z => Complex.exp (p.eval z) := funext hp
  have hderivE : ∀ z, deriv F z = (Polynomial.derivative p).eval z * F z := by
    intro z
    rw [hFexp]
    have h := (Polynomial.hasDerivAt p z).cexp
    rw [h.deriv]
    ring
  -- independence of exponentials
  set Q : Fin (m + 2) → Polynomial ℂ := fun j =>
    Polynomial.C (a j * c j) - Polynomial.C (a j) * Polynomial.derivative p with hQ
  have hzero : ∀ z, CExpPoly.cexpFn c Q z = 0 := by
    intro z
    have h1 := hderivF z
    rw [hderivE z, hF] at h1
    simp only [CExpPoly.cexpFn, hQ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Finset.mul_sum] at h1
    have h2 : ∑ j, (a j * c j - a j * (Polynomial.derivative p).eval z) *
        Complex.exp (c j * z) = ∑ j, a j * c j * Complex.exp (c j * z) -
          ∑ j, (Polynomial.derivative p).eval z * (a j * Complex.exp (c j * z)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, ← h1, sub_self]
  have hQ0 := CExpPoly.eq_zero_of_cexpFn_eq_zero (m + 1) c Q hc hzero
  have hval : ∀ j, c j = (Polynomial.derivative p).eval 0 := by
    intro j
    have h1 := congrArg (Polynomial.eval 0) (hQ0 j)
    simp only [hQ, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_zero] at h1
    have h2 : a j * (c j - (Polynomial.derivative p).eval 0) = 0 := by rw [mul_sub]; exact h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 (ha j)
    · exact sub_eq_zero.1 h3
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by
    intro h; have := congrArg Fin.val h; simp at this
  exact h01 (hc ((hval 0).trans (hval 1).symm))

/-- **Hurwitz's theorem.**  If zero-free analytic functions `g n` converge uniformly on the closed
disk `‖z − z₀‖ ≤ r` to `F`, and `F` is continuous and nonvanishing on the circle, then
`F z₀ ≠ 0`. -/
theorem ne_zero_of_tendstoUniformlyOn_of_forall_ne_zero {g : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {z₀ : ℂ}
    {r : ℝ} (hr : 0 < r) (hg : ∀ n, AnalyticOnNhd ℂ (g n) (closedBall z₀ r))
    (hg0 : ∀ n, ∀ u ∈ closedBall z₀ r, g n u ≠ 0)
    (hconv : TendstoUniformlyOn g F atTop (closedBall z₀ r))
    (hFc : ContinuousOn F (sphere z₀ r)) (hF : ∀ u ∈ sphere z₀ r, F u ≠ 0) : F z₀ ≠ 0 := by
  intro h0
  have hcpt : IsCompact (sphere z₀ r) := isCompact_sphere z₀ r
  have hne : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.2 hr.le
  obtain ⟨u₀, hu₀, hmin⟩ := hcpt.exists_isMinOn hne (hFc.norm)
  set δ : ℝ := ‖F u₀‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (hF u₀ hu₀)
  have hδle : ∀ u ∈ sphere z₀ r, δ ≤ ‖F u‖ := fun u hu => hmin hu
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.1 hconv (δ / 2) (by positivity)).exists
  have habs : |r| = r := abs_of_pos hr
  -- on the circle `‖g n‖ ≥ δ/2`
  have hcirc : ∀ u ∈ sphere z₀ |r|, Real.log (δ / 2) ≤ Real.log ‖g n u‖ := by
    intro u hu
    rw [habs] at hu
    have h1 := hn u (sphere_subset_closedBall hu)
    rw [dist_eq_norm] at h1
    have h2 : δ / 2 ≤ ‖g n u‖ := by
      have := norm_sub_norm_le (F u) (g n u)
      linarith [hδle u hu]
    exact Real.log_le_log (by positivity) h2
  -- at the centre `‖g n z₀‖ < δ/2`
  have hcentre : ‖g n z₀‖ < δ / 2 := by
    have h1 := hn z₀ (mem_closedBall_self hr.le)
    rwa [dist_eq_norm, h0, zero_sub, norm_neg] at h1
  have hpos : 0 < ‖g n z₀‖ := norm_pos_iff.2 (hg0 n z₀ (mem_closedBall_self hr.le))
  -- Jensen for a zero-free function
  have hJ : Real.circleAverage (fun u => Real.log ‖g n u‖) z₀ r = Real.log ‖g n z₀‖ := by
    refine AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (by rw [habs]; exact hg n) ?_
    rw [habs]; exact hg0 n
  have hint : CircleIntegrable (fun u => Real.log ‖g n u‖) z₀ r := by
    refine MeromorphicOn.circleIntegrable_log_norm ?_
    intro u hu
    rw [habs] at hu
    exact (hg n u (sphere_subset_closedBall hu)).meromorphicAt
  have hlow : Real.log (δ / 2) ≤ Real.circleAverage (fun u => Real.log ‖g n u‖) z₀ r := by
    have h := Real.circleAverage_mono (circleIntegrable_const (Real.log (δ / 2)) z₀ r) hint hcirc
    rwa [Real.circleAverage_const] at h
  rw [hJ] at hlow
  have := Real.log_lt_log hpos hcentre
  linarith

/-- **Finset form.**  For a set `W` of at least two frequencies and coefficients nonzero on `W`,
the sum `Σ_{w ∈ W} a_w e^{w z}` vanishes somewhere. -/
theorem exists_zero_of_finset_frequencies (W : Finset ℂ) (hW : 2 ≤ W.card) (a : ℂ → ℂ)
    (ha : ∀ w ∈ W, a w ≠ 0) : ∃ z : ℂ, ∑ w ∈ W, a w * Complex.exp (w * z) = 0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, W.card = m + 2 := ⟨W.card - 2, by omega⟩
  set e : Fin (m + 2) ≃ W := (W.equivFin.trans (finCongr hm)).symm with he
  obtain ⟨z, hz⟩ := exists_zero_of_injective_frequencies (fun j => (e j).1)
    (fun i j h => e.injective (Subtype.ext h)) (fun j => a (e j).1) (fun j => ha _ (e j).2)
  refine ⟨z, ?_⟩
  rw [← Finset.sum_coe_sort W, ← e.sum_comp]
  exact hz

/-- **Independence of exponentials, Finset form.** -/
theorem eq_zero_of_finset_frequencies_sum_eq_zero (W : Finset ℂ) (a : ℂ → ℂ)
    (h : ∀ z : ℂ, ∑ w ∈ W, a w * Complex.exp (w * z) = 0) : ∀ w ∈ W, a w = 0 := by
  intro w hw
  obtain ⟨m, hm⟩ : ∃ m : ℕ, W.card = m + 1 := ⟨W.card - 1, by
    have := Finset.card_pos.2 ⟨w, hw⟩; omega⟩
  set e : Fin (m + 1) ≃ W := (W.equivFin.trans (finCongr hm)).symm with he
  have hzero : ∀ z, CExpPoly.cexpFn (fun j => (e j).1) (fun j => Polynomial.C (a (e j).1)) z = 0 := by
    intro z
    simp only [CExpPoly.cexpFn, Polynomial.eval_C]
    rw [e.sum_comp (fun x : W => a x.1 * Complex.exp (x.1 * z)), Finset.sum_coe_sort W
      (fun x => a x * Complex.exp (x * z))]
    exact h z
  have hP := CExpPoly.eq_zero_of_cexpFn_eq_zero m (fun j => (e j).1)
    (fun j => Polynomial.C (a (e j).1)) (fun _ _ hij => e.injective (Subtype.ext hij)) hzero
    (e.symm ⟨w, hw⟩)
  simpa using hP

/-- **An exponential sum with two frequencies has an isolated zero.**  For `#W ≥ 2` and
coefficients nonzero on `W`, `F(z) = Σ_{w ∈ W} a_w e^{w z}` has a zero `z₀` and a circle about `z₀`
on which `F` does not vanish. -/
theorem exists_isolated_zero_of_finset_frequencies (W : Finset ℂ) (hW : 2 ≤ W.card) (a : ℂ → ℂ)
    (ha : ∀ w ∈ W, a w ≠ 0) :
    ∃ z₀ : ℂ, ∑ w ∈ W, a w * Complex.exp (w * z₀) = 0 ∧ ∃ r : ℝ, 0 < r ∧
      ∀ u ∈ sphere z₀ r, ∑ w ∈ W, a w * Complex.exp (w * u) ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_zero_of_finset_frequencies W hW a ha
  set F : ℂ → ℂ := fun z => ∑ w ∈ W, a w * Complex.exp (w * z) with hF
  have hdiff : Differentiable ℂ F := by
    rw [hF]; fun_prop
  refine ⟨z₀, hz₀, ?_⟩
  rcases (hdiff.analyticAt z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hAn : AnalyticOnNhd ℂ F Set.univ := fun z _ => hdiff.analyticAt z
    have hall := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z₀) h
    obtain ⟨w, hw⟩ : W.Nonempty := Finset.card_pos.1 (by omega)
    exact ha w hw (eq_zero_of_finset_frequencies_sum_eq_zero W a
      (fun z => hall (Set.mem_univ z)) w hw)
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 h
    refine ⟨ε / 2, by positivity, fun u hu => ?_⟩
    have hu' : u ∈ ball z₀ ε ∩ {z₀}ᶜ := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, mem_sphere.1 hu]; linarith
      · intro h0
        rw [Set.mem_singleton_iff] at h0
        rw [h0, mem_sphere, dist_self] at hu
        linarith
    exact hball hu'

end

end GaloisForLFunctions.HTGeometry
