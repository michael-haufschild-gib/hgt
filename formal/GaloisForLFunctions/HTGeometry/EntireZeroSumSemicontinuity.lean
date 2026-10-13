import GaloisForLFunctions.HTGeometry.PolynomialRootSumSemicontinuity

/-!
# Weighted zero sums of an entire limit of polynomials

Let `f` be a nonzero entire function and `F n` complex polynomials converging to `f` locally
uniformly.  For a continuous weight `Ψ ≥ 0` and any finite set `S` of points,

`Σ_{w ∈ S} mult_f(w) Ψ(w) ≤ liminf_n Σ_{roots of F n} Ψ`
(`sum_zeroMult_mul_le_of_tendstoLocallyUniformly`).

This transfers inequalities for weighted root sums of polynomial approximants to the zeros of an
entire function, one finite set of zeros at a time; for a function with finitely many nonreal
zeros and a weight vanishing on the real axis it controls the whole nonreal zero sum.

**Proof.**  The zeros of `f` are isolated (`exists_isolating_ball_entire`).  Around each point of
`S` take a small disc on which `Ψ ≥ Ψ(w) − ε`, with no other zero of `f` on its closure; the
argument principle gives eventually `mult_f(w)` roots of `F n` in the disc, and `Ψ ≥ 0` handles
the remaining roots.
-/

open Polynomial Complex Metric Set Filter Topology Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Zeros of a nonzero entire function are isolated.** -/
theorem exists_isolating_ball_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∃ z, f z ≠ 0) (w : ℂ) :
    ∃ r > 0, ∀ z ∈ closedBall w r, z ≠ w → f z ≠ 0 := by
  rcases (hf.analyticAt w).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨z, hz⟩ := hnz
    have hon : AnalyticOnNhd ℂ f univ := fun x _ => hf.analyticAt x
    have := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ w) h (mem_univ z)
    exact hz this
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hball⟩ := h
    refine ⟨ε / 2, by linarith, fun z hz hzw => hball ?_ hzw⟩
    have := mem_closedBall.mp hz
    linarith

/-- **Lower semicontinuity of weighted zero sums of an entire limit.** -/
theorem sum_zeroMult_mul_le_of_tendstoLocallyUniformly {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∃ z, f z ≠ 0) (S : Finset ℂ) {F : ℕ → ℂ[X]}
    (hconv : TendstoLocallyUniformly (fun n z => (F n).eval z) f atTop)
    {Ψ : ℂ → ℝ} (hΨ : Continuous Ψ) (hΨ0 : ∀ w, 0 ≤ Ψ w) {K : ℝ}
    (hK : ∀ᶠ n in atTop, ((F n).roots.map Ψ).sum ≤ K) :
    ∑ w ∈ S, (zeroMult f w : ℝ) * Ψ w ≤ K := by
  classical
  by_contra hcon
  push Not at hcon
  set L := ∑ w ∈ S, (zeroMult f w : ℝ) * Ψ w
  set c : ℝ := ∑ w ∈ S, (zeroMult f w : ℝ) + 1
  have hc : 0 < c := by
    have : 0 ≤ ∑ w ∈ S, (zeroMult f w : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
    simp only [c]; linarith
  set ε := (L - K) / (2 * c)
  have hε : 0 < ε := div_pos (by linarith) (by positivity)
  -- separation of the points of `S`
  obtain ⟨d, hd, hsep⟩ : ∃ d > 0, ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → d ≤ dist e e' := by
    rcases (S.offDiag).eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun e he₁ e' he' hne => ?_⟩
      have : (e, e') ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne⟩
      rw [he] at this; simp at this
    · refine ⟨S.offDiag.inf' hne (fun pr => dist pr.1 pr.2), ?_, fun e he₁ e' he' hne' => ?_⟩
      · refine (Finset.lt_inf'_iff hne).mpr fun pr hpr => ?_
        obtain ⟨-, -, hpr⟩ := Finset.mem_offDiag.mp hpr
        exact dist_pos.mpr hpr
      · have hmem : (e, e') ∈ S.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne'⟩
        exact Finset.inf'_le (fun pr : ℂ × ℂ => dist pr.1 pr.2) hmem
  have hcont : ∀ e : ℂ, ∃ δ > 0, ∀ z, dist z e < δ → Ψ e - ε ≤ Ψ z := by
    intro e
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.mp hΨ e ε hε
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have := h z hz
    rw [Real.dist_eq, abs_lt] at this
    linarith
  choose δ hδ hδΨ using hcont
  have hiso := fun e => exists_isolating_ball_entire hf hnz e
  choose ρ hρ hρf using hiso
  set r : ℂ → ℝ := fun e => min (min (d / 3) (δ e)) (ρ e)
  have hr : ∀ e, 0 < r e := fun e => lt_min (lt_min (by linarith) (hδ e)) (hρ e)
  have hsph : ∀ e, ∀ z ∈ sphere e (r e), f z ≠ 0 := by
    intro e z hz
    have hz' : dist z e = r e := mem_sphere.mp hz
    refine hρf e z (mem_closedBall.mpr ?_) ?_
    · rw [hz']; exact min_le_right _ _
    · intro hze; rw [hze, dist_self] at hz'; exact (hr e).ne hz'
  have hcount : ∀ e, zeroSumBall f e (r e) = (zeroMult f e : ℂ) := by
    intro e
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall (hr e)
      (by linarith [hr e] : r e < 2 * r e) isOpen_univ (Set.subset_univ _)
      hf.differentiableOn (hsph e)
    rw [hZs]
    by_cases he0 : f e = 0
    · have hZ : Z = {e} := by
        ext z
        rw [Finset.mem_singleton]
        constructor
        · intro hz
          by_contra hze
          exact hρf e z (mem_closedBall.mpr ((le_of_lt (mem_ball.mp (hZb z hz))).trans
            (min_le_right _ _))) hze ((hZz z (hZb z hz)).mpr hz)
        · rintro rfl
          exact (hZz z (mem_ball_self (hr z))).mp he0
      rw [hZ, Finset.sum_singleton]
    · have hZ : Z = ∅ := by
        ext z
        simp only [Finset.notMem_empty, iff_false]
        intro hz
        have hzf := (hZz z (hZb z hz)).mpr hz
        by_cases hze : z = e
        · rw [hze] at hzf; exact he0 hzf
        · exact hρf e z (mem_closedBall.mpr ((le_of_lt (mem_ball.mp (hZb z hz))).trans
            (min_le_right _ _))) hze hzf
      have hmult : zeroMult f e = 0 := by
        rw [zeroMult]
        have : analyticOrderAt f e = 0 := (hf.analyticAt e).analyticOrderAt_eq_zero.mpr he0
        rw [this]; rfl
      rw [hZ, Finset.sum_empty, hmult, Nat.cast_zero]
  have hev : ∀ e ∈ S, ∀ᶠ n in atTop,
      zeroSumBall (fun z => (F n).eval z) e (r e) = (zeroMult f e : ℂ) ∧
        ∀ w ∈ sphere e (r e), (F n).eval w ≠ 0 := by
    intro e _
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun n => (F n).differentiable) hf hconv (hr e) (by linarith [hr e] : r e < 2 * r e)
      (hsph e)
    have h2 := eventually_ne_zero_on_sphere hf.continuous hconv (hr e).le (hsph e)
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  obtain ⟨n, hn, hKn⟩ := (((Filter.eventually_all_finset S).mpr hev).and hK).exists
  have hnonneg : 0 ≤ ((F n).roots.map Ψ).sum :=
    Multiset.sum_nonneg fun x hx => by
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx; exact hΨ0 w
  rcases S.eq_empty_or_nonempty with hS | hS
  · have : L = 0 := by simp [L, hS]
    linarith
  obtain ⟨e₀, he₀⟩ := hS
  have hFn : F n ≠ 0 := by
    intro h0
    have hw : e₀ + (r e₀ : ℂ) ∈ sphere e₀ (r e₀) := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hr e₀)]
    exact (hn e₀ he₀).2 _ hw (by rw [h0, eval_zero])
  have hZ : ∀ e ∈ S, ∃ Z : Finset ℂ, (∀ q ∈ Z, q ∈ ball e (r e)) ∧
      (∀ q ∈ Z, (F n).eval q = 0) ∧ ∑ q ∈ Z, (F n).roots.count q = zeroMult f e := by
    intro e he
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall (hr e)
      (by linarith [hr e] : r e < 2 * r e) isOpen_univ (Set.subset_univ _)
      (F n).differentiable.differentiableOn (hn e he).2
    refine ⟨Z, hZb, fun q hq => (hZz q (hZb q hq)).mpr hq, ?_⟩
    have h := hZs
    rw [(hn e he).1] at h
    have h' : ((∑ q ∈ Z, zeroMult (fun y : ℂ => (F n).eval y) q : ℕ) : ℂ) =
        (zeroMult f e : ℂ) := by push_cast; exact h.symm
    have h'' : ∑ q ∈ Z, zeroMult (fun y : ℂ => (F n).eval y) q = zeroMult f e := by
      exact_mod_cast h'
    rw [← h'']
    exact Finset.sum_congr rfl fun q _ => by
      rw [count_roots, zeroMult_eval_eq_rootMultiplicity hFn]
  choose! Z hZball hZzero hZcount using hZ
  have hpd : (S : Set ℂ).PairwiseDisjoint Z := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    have h1 := hsep e he e' he' hne
    have hz1 := mem_ball.mp (hZball e he z hz)
    have hz2 := mem_ball.mp (hZball e' he' z hz')
    have h2 : dist e e' ≤ dist z e + dist z e' := by
      rw [dist_comm z e]; exact dist_triangle e z e'
    have := min_le_left (min (d / 3) (δ e)) (ρ e)
    have := min_le_left (d / 3) (δ e)
    have := min_le_left (min (d / 3) (δ e')) (ρ e')
    have := min_le_left (d / 3) (δ e')
    simp only [r] at hz1 hz2
    linarith
  have hsub : S.biUnion Z ⊆ (F n).roots.toFinset := by
    intro z hz
    obtain ⟨e, he, hz⟩ := Finset.mem_biUnion.mp hz
    exact Multiset.mem_toFinset.mpr ((mem_roots hFn).mpr (hZzero e he z hz))
  have hlow : ∑ e ∈ S, (zeroMult f e : ℝ) * (Ψ e - ε) ≤ ((F n).roots.map Ψ).sum := by
    rw [Finset.sum_multiset_map_count]
    calc ∑ e ∈ S, (zeroMult f e : ℝ) * (Ψ e - ε)
        = ∑ e ∈ S, ∑ q ∈ Z e, ((F n).roots.count q : ℝ) * (Ψ e - ε) := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [← Finset.sum_mul, ← hZcount e he]; push_cast; ring
      _ ≤ ∑ e ∈ S, ∑ q ∈ Z e, ((F n).roots.count q : ℝ) * Ψ q := by
          refine Finset.sum_le_sum fun e he => Finset.sum_le_sum fun q hq => ?_
          have hq' := mem_ball.mp (hZball e he q hq)
          have hle : r e ≤ δ e := (min_le_left _ _).trans (min_le_right _ _)
          exact mul_le_mul_of_nonneg_left (hδΨ e q (by linarith)) (by positivity)
      _ = ∑ q ∈ S.biUnion Z, ((F n).roots.count q : ℝ) * Ψ q := (Finset.sum_biUnion hpd).symm
      _ ≤ ∑ q ∈ (F n).roots.toFinset, (F n).roots.count q • Ψ q := by
          rw [Finset.sum_congr rfl fun q _ => (nsmul_eq_mul ((F n).roots.count q) (Ψ q)).symm]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
            nsmul_nonneg (hΨ0 q) _
  have hsplit : ∑ e ∈ S, (zeroMult f e : ℝ) * (Ψ e - ε) =
      L - ε * ∑ e ∈ S, (zeroMult f e : ℝ) := by
    simp only [L]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hmult : ∑ e ∈ S, (zeroMult f e : ℝ) ≤ c := by simp only [c]; linarith
  have hεc : ε * c = (L - K) / 2 := by simp only [ε]; field_simp
  have : ε * ∑ e ∈ S, (zeroMult f e : ℝ) ≤ ε * c := mul_le_mul_of_nonneg_left hmult hε.le
  linarith

end

end GaloisForLFunctions.HTGeometry
