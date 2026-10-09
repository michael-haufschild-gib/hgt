import GaloisForLFunctions.HTGeometry.ComplexAffineLineSimplyConnected
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Continuous root branches off a finite set are polynomials

Let `f(t, w)` be monic of positive degree in `w` with polynomial coefficients, separable in `w`
for `t` outside a finite set `B`.  A continuous function `φ` on `ℂ ∖ B` with `f(t, φ(t)) = 0` is
holomorphic there by the implicit function theorem, bounded near `B` by the monic Cauchy bound,
hence extends to an entire function of polynomial growth: `φ` is a polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set Filter

noncomputable section

/-- A root branch continuous at a separable parameter is analytic there. -/
theorem analyticAt_of_continuousAt_biRoot {f : ℂ[X][X]} {g : ℂ → ℂ} {s₀ : ℂ}
    (hg : ContinuousAt g s₀) (hroot : ∀ᶠ s in 𝓝 s₀, biEval f (s, g s) = 0)
    (hsep0 : (biFibre f s₀).Separable) : AnalyticAt ℂ g s₀ := by
  have hroot0 : biEval f (s₀, g s₀) = 0 := hroot.self_of_nhds
  have hmem : (s₀, g s₀) ∈ BiRootLocus f := hroot0
  set e : BiRootLocus f := ⟨(s₀, g s₀), hmem⟩ with he
  obtain ⟨r, hr, hrs, hrroot⟩ :=
    HolomorphicIFT.holo_implicit (analyticAt_biEval f (s₀, g s₀)) hroot0
      (by simpa using biRootLocus_partial_ne e hsep0)
  obtain ⟨φ, hφmem, hφeq⟩ := exists_chart_biRootProj e hsep0
  obtain ⟨U, hU, hUeq⟩ : ∃ U : Set (ℂ × ℂ), IsOpen U ∧
      φ.source = (fun q : BiRootLocus f => (q : ℂ × ℂ)) ⁻¹' U := by
    have := φ.open_source
    rw [isOpen_induced_iff] at this
    obtain ⟨U, hU, hUeq⟩ := this
    exact ⟨U, hU, hUeq.symm⟩
  have hmemU : (s₀, g s₀) ∈ U := by
    have : e ∈ φ.source := hφmem
    rwa [hUeq] at this
  have hev1 : ∀ᶠ s in 𝓝 s₀, (s, g s) ∈ U :=
    (continuousAt_id.prodMk hg).preimage_mem_nhds (hU.mem_nhds hmemU)
  have hev2 : ∀ᶠ s in 𝓝 s₀, (s, r s) ∈ U := by
    have hrc : ContinuousAt r s₀ := hr.continuousAt
    have : ContinuousAt (fun s => (s, r s)) s₀ := continuousAt_id.prodMk hrc
    exact this.preimage_mem_nhds (hU.mem_nhds (by rw [hrs]; exact hmemU))
  have hgr : ∀ᶠ s in 𝓝 s₀, g s = r s := by
    filter_upwards [hev1, hev2, hrroot, hroot] with s h1 h2 h3 h4
    have hq1 : (s, g s) ∈ BiRootLocus f := h4
    have hq2 : (s, r s) ∈ BiRootLocus f := h3
    have hs1 : (⟨(s, g s), hq1⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h1
    have hs2 : (⟨(s, r s), hq2⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h2
    have : (⟨(s, g s), hq1⟩ : BiRootLocus f) = ⟨(s, r s), hq2⟩ := by
      apply φ.injOn hs1 hs2
      have h1' : (φ : BiRootLocus f → ℂ) ⟨(s, g s), hq1⟩ = s := by
        rw [← hφeq]; rfl
      have h2' : (φ : BiRootLocus f → ℂ) ⟨(s, r s), hq2⟩ = s := by
        rw [← hφeq]; rfl
      rw [h1', h2']
    exact congrArg (fun q : BiRootLocus f => (q : ℂ × ℂ).2) this
  exact hr.congr (Filter.EventuallyEq.symm hgr)

/-- The monic Cauchy bound as a continuous function of the parameter. -/
def cauchyBound (f : ℂ[X][X]) (t : ℂ) : ℝ :=
  max 1 (∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval t‖)

theorem continuous_cauchyBound (f : ℂ[X][X]) : Continuous (cauchyBound f) := by
  refine continuous_const.max (continuous_finsetSum _ fun i _ => ?_)
  exact ((f.coeff i).continuous_aeval).norm

theorem norm_le_cauchyBound {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    {t w : ℂ} (h : biEval f (t, w) = 0) : ‖w‖ ≤ cauchyBound f t :=
  biRootLocus_norm_le hf hdeg ⟨(t, w), h⟩

/-- **Root branches off a finite set are polynomials.** -/
theorem exists_polynomial_of_root_branch {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (B : Finset ℂ) (hsep : ∀ t, t ∉ B → (biFibre f t).Separable) {φ : ℂ → ℂ}
    (hφc : ContinuousOn φ (B : Set ℂ)ᶜ) (hroot : ∀ t, t ∉ B → biEval f (t, φ t) = 0) :
    ∃ Q : ℂ[X], ∀ t, t ∉ B → φ t = Q.eval t := by
  classical
  have hopen : IsOpen ((B : Set ℂ)ᶜ) := B.finite_toSet.isClosed.isOpen_compl
  have hanal : ∀ t, t ∉ B → AnalyticAt ℂ φ t := by
    intro t ht
    have hnhds : (B : Set ℂ)ᶜ ∈ 𝓝 t := hopen.mem_nhds ht
    refine analyticAt_of_continuousAt_biRoot (hφc.continuousAt hnhds) ?_ (hsep t ht)
    filter_upwards [hnhds] with s hs using hroot s hs
  set Φ : ℂ → ℂ := fun t => if t ∈ B then limUnder (𝓝[≠] t) φ else φ t with hΦdef
  have hΦout : ∀ t, t ∉ B → Φ t = φ t := fun t ht => by simp [hΦdef, ht]
  have hdiff : Differentiable ℂ Φ := by
    intro t
    by_cases ht : t ∈ B
    · -- a ball around `t` meeting `B` only at `t`
      have hfin : ((B.erase t : Finset ℂ) : Set ℂ).Finite := Finset.finite_toSet _
      have hcl : IsClosed ((B.erase t : Finset ℂ) : Set ℂ) := hfin.isClosed
      have hnot : t ∉ ((B.erase t : Finset ℂ) : Set ℂ) := by simp
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl t hnot
      set s := Metric.ball t r
      have hsB : ∀ z ∈ s \ {t}, z ∉ B := by
        rintro z ⟨hz, hzt⟩ hzB
        exact hball hz (Finset.mem_erase.mpr ⟨hzt, hzB⟩)
      have hd : DifferentiableOn ℂ φ (s \ {t}) := fun z hz =>
        (hanal z (hsB z hz)).differentiableAt.differentiableWithinAt
      have hb : BddAbove (norm ∘ φ '' (s \ {t})) := by
        obtain ⟨M, hM⟩ := (isCompact_closedBall t r).exists_bound_of_continuousOn
          (continuous_cauchyBound f).continuousOn
        refine ⟨M, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        have h1 := norm_le_cauchyBound hf hdeg (hroot z (hsB z hz))
        have h2 := hM z (Metric.ball_subset_closedBall hz.1)
        rw [Real.norm_eq_abs] at h2
        exact h1.trans ((le_abs_self _).trans h2)
      have hu := Complex.differentiableOn_update_limUnder_of_bddAbove
        (Metric.ball_mem_nhds t hr) hd hb
      have heq : Function.update φ t (limUnder (𝓝[≠] t) φ) =ᶠ[𝓝 t] Φ := by
        filter_upwards [Metric.ball_mem_nhds t hr] with z hz
        by_cases hzt : z = t
        · subst hzt; simp [hΦdef, ht]
        · rw [Function.update_of_ne hzt, hΦout z (hsB z ⟨hz, hzt⟩)]
      exact ((hu t (Metric.mem_ball_self hr)).differentiableAt
        (Metric.ball_mem_nhds t hr)).congr_of_eventuallyEq heq.symm
    · have heq : φ =ᶠ[𝓝 t] Φ := by
        filter_upwards [hopen.mem_nhds ht] with z hz using (hΦout z hz).symm
      exact (hanal t ht).differentiableAt.congr_of_eventuallyEq heq.symm
  -- polynomial growth
  set N : ℕ := (Finset.range f.natDegree).sup (fun i => (f.coeff i).natDegree) with hN
  set A : ℝ := ∑ i ∈ Finset.range f.natDegree,
      ∑ j ∈ Finset.range ((f.coeff i).natDegree + 1), ‖(f.coeff i).coeff j‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hcb : ∀ t : ℂ, cauchyBound f t ≤ (1 + A) * (max 1 ‖t‖) ^ N := by
    intro t
    set M : ℝ := max 1 ‖t‖ with hM
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hMN : (1 : ℝ) ≤ M ^ N := one_le_pow₀ hM1
    have hbound : ∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval t‖ ≤ A * M ^ N := by
      rw [hA, Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro i hi
      refine (norm_eval_le_sum (f.coeff i) t).trans ?_
      refine mul_le_mul_of_nonneg_left ?_
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
      have hle : (f.coeff i).natDegree ≤ N := by
        rw [hN]
        exact Finset.le_sup (f := fun i => (f.coeff i).natDegree) hi
      exact pow_le_pow_right₀ hM1 hle
    have h2 : cauchyBound f t ≤ 1 + A * M ^ N :=
      max_le (by nlinarith) (hbound.trans (le_add_of_nonneg_left zero_le_one))
    refine h2.trans ?_
    nlinarith [mul_nonneg hA0 (le_of_lt (lt_of_lt_of_le zero_lt_one hMN))]
  have hclosed : IsClosed {t : ℂ | ‖Φ t‖ ≤ cauchyBound f t} :=
    isClosed_le hdiff.continuous.norm (continuous_cauchyBound f)
  have hdense : Dense ((B : Set ℂ)ᶜ) := by
    have h := (dense_univ (X := ℂ)).sdiff_finset B
    rwa [← Set.compl_eq_univ_sdiff] at h
  have hall : ∀ t, ‖Φ t‖ ≤ cauchyBound f t := by
    intro t
    have hsub : (B : Set ℂ)ᶜ ⊆ {t : ℂ | ‖Φ t‖ ≤ cauchyBound f t} := by
      intro z hz
      change ‖Φ z‖ ≤ _
      rw [hΦout z hz]
      exact norm_le_cauchyBound hf hdeg (hroot z hz)
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense.closure_eq ▸ mem_univ t)
  obtain ⟨Q, hQ⟩ := Bottcher.exists_polynomial_of_entire_polyGrowth hdiff
    (fun z => (hall z).trans (hcb z))
  exact ⟨Q, fun t ht => (hΦout t ht).symm.trans (hQ t)⟩

end

end GaloisForLFunctions.HTGeometry
