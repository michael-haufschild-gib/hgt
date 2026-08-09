import Mathlib

/-!
# The order-`N` Schwarz lemma

A function holomorphic on a disc whose derivatives of every order below `N` vanish at the centre is
smaller than its boundary bound by the factor `q^N`, where `q` is the relative radius.  This is the
quantitative statement behind every "high-order vanishing forces smallness" step; in particular it
is the one-variable input of the polydisc Schwarz lemma, obtained there by restricting to complex
lines through the centre.

The proof is the Taylor expansion together with Cauchy's estimate on the boundary circle: the
`n`-th coefficient is at most `C/R^n`, and the first `N` coefficients vanish, so the series is
dominated by the geometric tail `C·q^N/(1−q)`.
-/

open Complex Metric

namespace GaloisForLFunctions.HTGeometry

/-- **Order-`N` Schwarz lemma.** -/
theorem norm_le_of_iteratedDeriv_vanish
    {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) R))
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C)
    {N : ℕ} (hvan : ∀ k, k < N → iteratedDeriv k f 0 = 0)
    {t : ℂ} (ht : t ∈ ball (0 : ℂ) R) :
    ‖f t‖ ≤ C * (‖t‖ / R) ^ N / (1 - ‖t‖ / R) := by
  have htR : ‖t‖ < R := by simpa [mem_ball, dist_eq_norm] using ht
  have hC0 : 0 ≤ C := by
    have hmem : (R : ℂ) ∈ sphere (0 : ℂ) R := by
      simp [mem_sphere_iff_norm, abs_of_pos hR]
    exact le_trans (norm_nonneg _) (hC _ hmem)
  set q : ℝ := ‖t‖ / R with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hqdef, div_lt_one hR]; exact htR
  -- the Taylor series of `f` at the centre
  have hsum : HasSum (fun n : ℕ => ((Nat.factorial n : ℂ))⁻¹ • (t - 0) ^ n • iteratedDeriv n f 0) (f t) :=
    Complex.hasSum_taylorSeries_on_ball hf.differentiableOn ht
  set u : ℕ → ℂ := fun n => ((Nat.factorial n : ℂ))⁻¹ • (t - 0) ^ n • iteratedDeriv n f 0 with hu
  -- the termwise bound from Cauchy's estimate
  have hterm : ∀ n : ℕ, ‖u n‖ ≤ C * q ^ n := by
    intro n
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hC
    have hfac : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hnorm : ‖u n‖ = (‖t‖ ^ n / (Nat.factorial n : ℝ)) * ‖iteratedDeriv n f 0‖ := by
      rw [hu]
      simp only [smul_eq_mul, norm_mul, norm_inv, norm_pow, sub_zero]
      rw [show ‖((Nat.factorial n : ℂ))‖ = (Nat.factorial n : ℝ) by simp]
      field_simp
    rw [hnorm]
    calc (‖t‖ ^ n / (Nat.factorial n : ℝ)) * ‖iteratedDeriv n f 0‖
        ≤ (‖t‖ ^ n / (Nat.factorial n : ℝ)) * ((Nat.factorial n : ℝ) * C / R ^ n) := by
          exact mul_le_mul_of_nonneg_left hcauchy (by positivity)
      _ = C * q ^ n := by
          rw [hqdef, div_pow]
          field_simp
  -- the first `N` terms vanish
  have hzero : ∀ n : ℕ, n < N → u n = 0 := by
    intro n hn
    rw [hu]
    simp [hvan n hn]
  have hsummable : Summable fun n : ℕ => ‖u n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm ?_
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left C
  -- the tail bound
  have hsplit := hsummable.sum_add_tsum_nat_add N
  have hfin : ∑ i ∈ Finset.range N, ‖u i‖ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [hzero i (Finset.mem_range.mp hi)]
    simp
  have htail : ∑' i : ℕ, ‖u (i + N)‖ ≤ C * q ^ N / (1 - q) := by
    have hle : ∀ i : ℕ, ‖u (i + N)‖ ≤ (C * q ^ N) * q ^ i := by
      intro i
      have := hterm (i + N)
      rw [pow_add] at this
      calc ‖u (i + N)‖ ≤ C * (q ^ i * q ^ N) := this
        _ = (C * q ^ N) * q ^ i := by ring
    have hsum2 : Summable fun i : ℕ => (C * q ^ N) * q ^ i :=
      (summable_geometric_of_lt_one hq0 hq1).mul_left _
    have hbound := Summable.tsum_le_tsum hle
      (hsummable.comp_injective (add_left_injective N)) hsum2
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at hbound
    calc ∑' i : ℕ, ‖u (i + N)‖ ≤ (C * q ^ N) * (1 - q)⁻¹ := hbound
      _ = C * q ^ N / (1 - q) := by rw [div_eq_mul_inv]
  calc ‖f t‖ = ‖∑' n : ℕ, u n‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' n : ℕ, ‖u n‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' i : ℕ, ‖u (i + N)‖ := by rw [← hsplit, hfin, zero_add]
    _ ≤ C * q ^ N / (1 - q) := htail


/-- **Polydisc Schwarz lemma, slice form.**  If every complex line through `c` meets the vanishing
hypothesis to order `N`, and `F` is bounded by `C` on the closed ball of radius `R` about `c`, then
`F` is smaller than `C` by the factor `q^N` at relative radius `q`.  The line through `c` in the
direction `y` stays inside that ball for `|t| ≤ R`, so the one-variable lemma applies to the
restriction. -/
theorem norm_le_of_slice_iteratedDeriv_vanish
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (hF : Differentiable ℂ F) {c : E} {R C : ℝ} (hR : 0 < R)
    (hbd : ∀ w : E, ‖w‖ ≤ R → ‖F (c + w)‖ ≤ C)
    {N : ℕ}
    (hvan : ∀ u : E, ‖u‖ = 1 → ∀ k, k < N →
      iteratedDeriv k (fun t : ℂ => F (c + t • u)) 0 = 0)
    {y : E} (hy0 : y ≠ 0) (hy : ‖y‖ < R) :
    ‖F (c + y)‖ ≤ C * (‖y‖ / R) ^ N / (1 - ‖y‖ / R) := by
  have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
  have hreal : ∀ (r : ℝ) (v : E), (r : ℝ) • v = ((r : ℂ)) • v := by
    intro r v
    rw [← IsScalarTower.algebraMap_smul ℂ r v, Complex.coe_algebraMap]
  set u : E := (‖y‖ : ℝ)⁻¹ • y with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hyn]
    field_simp
  set φ : ℂ → ℂ := fun t => F (c + t • u) with hφ
  have hφdiff : Differentiable ℂ φ :=
    hF.comp ((differentiable_id.smul_const u).const_add c)
  have hφbd : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖φ z‖ ≤ C := by
    intro z hz
    have hzn : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    refine hbd (z • u) ?_
    rw [norm_smul, hun, mul_one, hzn]
  have hφvan : ∀ k, k < N → iteratedDeriv k φ 0 = 0 := hvan u hun
  have hmem : ((‖y‖ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hyn]
    exact hy
  have hscal : ((‖y‖ : ℝ) : ℂ) * ((‖y‖⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
    exact div_self (Complex.ofReal_ne_zero.mpr hyn.ne')
  have hval : φ ((‖y‖ : ℝ) : ℂ) = F (c + y) := by
    show F (c + ((‖y‖ : ℝ) : ℂ) • u) = F (c + y)
    rw [hu, hreal, smul_smul, hscal, one_smul]
  have hres := norm_le_of_iteratedDeriv_vanish hR hφdiff.diffContOnCl hφbd hφvan hmem
  rw [hval] at hres
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyn] using hres

/-- **The slice derivative is the jet evaluated on the direction.**  Restricting to the complex
line `t ↦ c + t·u` turns the `k`-th multilinear jet of `F` at `c` into the `k`-th derivative of the
restriction at `0`, evaluated at the constant tuple `u`. -/
theorem iteratedDeriv_slice_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (c u : E) (k : ℕ) :
    iteratedDeriv k (fun t : ℂ => F (c + t • u)) 0
      = iteratedFDeriv ℂ k F c (fun _ => u) := by
  set L : ℂ →L[ℂ] E := (1 : ℂ →L[ℂ] ℂ).smulRight u with hL
  have hLapply : ∀ t : ℂ, L t = t • u := by
    intro t
    simp [hL]
  have hcomp : (fun t : ℂ => F (c + t • u)) = (fun z : E => F (c + z)) ∘ L := by
    funext t
    simp [Function.comp_apply, hLapply t]
  have hG : ContDiff ℂ (⊤ : ℕ∞) (fun z : E => F (c + z)) :=
    hF.comp (contDiff_const.add contDiff_id)
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hG 0 (by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLapply, one_smul]
  rw [iteratedFDeriv_comp_add_left]
  simp

/-- **Polydisc Schwarz lemma, jet form.**  The multi-index form of
`norm_le_of_slice_iteratedDeriv_vanish`: vanishing of every jet of order below `N` at the centre. -/
theorem norm_le_of_iteratedFDeriv_vanish
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) {c : E} {R C : ℝ} (hR : 0 < R)
    (hbd : ∀ w : E, ‖w‖ ≤ R → ‖F (c + w)‖ ≤ C)
    {N : ℕ} (hvan : ∀ k, k < N → iteratedFDeriv ℂ k F c = 0)
    {y : E} (hy0 : y ≠ 0) (hy : ‖y‖ < R) :
    ‖F (c + y)‖ ≤ C * (‖y‖ / R) ^ N / (1 - ‖y‖ / R) := by
  refine norm_le_of_slice_iteratedDeriv_vanish (hF.differentiable (by simp)) hR hbd ?_ hy0 hy
  intro u _ k hk
  rw [iteratedDeriv_slice_eq hF c u k, hvan k hk]
  rfl

end GaloisForLFunctions.HTGeometry
