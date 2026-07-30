import GaloisForLFunctions.HTGeometry.HerglotzJetMapContinuity
import GaloisForLFunctions.HTGeometry.HerglotzGenericity
import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

/-!
# Countable genericity for the Herglotz chart

Density for one polynomial relation does not intersect countably.  What does is nowhere density of
each degeneracy locus, and that needs the loci closed — hence continuity of the jet map, which the
Lipschitz estimate supplies.

Each degeneracy locus is then closed with empty interior, the latter being exactly the density
statement for that relation.  The countable avoidance backbone intersects them, giving a dense set
of parameters on which *every* member of a countable family of nonzero polynomial jet relations
fails to degenerate.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false in
/-- The Herglotz jet map is continuous in the parameter. -/
theorem continuous_herglotzJetMap (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Continuous (herglotzJetMap μ w x n) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  set C : ℝ := 2 * (∑ s : jetIndex n, cauchyJetKernelBound x n s) *
    ∫ t, Real.exp (u₀ t) * |w t| ∂μ with hCdef
  have hmass : 0 ≤ ∫ t, Real.exp (u₀ t) * |w t| ∂μ :=
    integral_nonneg fun t => by positivity
  have hCnonneg : 0 ≤ C := by
    rw [hCdef]
    apply mul_nonneg _ hmass
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun s _ => cauchyJetKernelBound_nonneg x n s
  refine ⟨min 1 (ε / (C + 1)), by positivity, ?_⟩
  intro u hu
  have hnorm : ‖u - u₀‖ < min 1 (ε / (C + 1)) := by
    rwa [← dist_eq_norm]
  have hone : ‖u - u₀‖ ≤ 1 := le_of_lt (lt_of_lt_of_le hnorm (min_le_left _ _))
  have hsmall : ‖u - u₀‖ < ε / (C + 1) :=
    lt_of_lt_of_le hnorm (min_le_right _ _)
  have hcoord : ∀ s : jetIndex n,
      ‖herglotzJetMap μ w x n u s - herglotzJetMap μ w x n u₀ s‖ ≤
        C * ‖u - u₀‖ := by
    intro s
    refine le_trans (norm_herglotzJetMap_sub_le μ w hw x hne n u₀ u hone s) ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hCdef]
    apply mul_le_mul_of_nonneg_right _ hmass
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    exact Finset.single_le_sum
      (fun s' _ => cauchyJetKernelBound_nonneg x n s') (Finset.mem_univ s)
  have hle : ‖herglotzJetMap μ w x n u - herglotzJetMap μ w x n u₀‖ ≤
      C * ‖u - u₀‖ := by
    apply pi_norm_le_iff_of_nonneg (mul_nonneg hCnonneg (norm_nonneg _)) |>.mpr
    intro s
    simpa using hcoord s
  rw [dist_eq_norm]
  calc ‖herglotzJetMap μ w x n u - herglotzJetMap μ w x n u₀‖
      ≤ C * ‖u - u₀‖ := hle
    _ ≤ (C + 1) * ‖u - u₀‖ := by nlinarith [norm_nonneg (u - u₀)]
    _ < (C + 1) * (ε / (C + 1)) := by
        apply mul_lt_mul_of_pos_left hsmall
        linarith
    _ = ε := by field_simp

/-- **Countable genericity for the Herglotz chart.**  For a base measure of infinite support with a
strictly positive integrable Nevanlinna density, the bounded parameters on which *every* member of a
countable family of nonzero polynomial jet relations fails to degenerate are dense. -/
theorem dense_countable_nondegenerate_herglotzJetMap
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (P : ℕ → MvPolynomial (jetIndex n) ℂ) (hP : ∀ k, P k ≠ 0) :
    Dense {u : Lp ℝ ⊤ μ | ∀ k,
      MvPolynomial.eval (herglotzJetMap μ w x n u) (P k) ≠ 0} := by
  classical
  set hne : ∀ i, (x i).im ≠ 0 := fun i => ne_of_gt (hupper i) with hnedef
  set D : ℕ → Set (Lp ℝ ⊤ μ) := fun k =>
    {u | MvPolynomial.eval (herglotzJetMap μ w x n u) (P k) = 0} with hDdef
  have hcont := continuous_herglotzJetMap μ w hw x hne n
  have hclosed : ∀ k, IsClosed (D k) := by
    intro k
    exact (mvPolynomial_zero_set_isClosed (P k)).preimage hcont
  have hinterior : ∀ k, interior (D k) = ∅ := by
    intro k
    rw [interior_eq_empty_iff_dense_compl]
    have hcompl : (D k)ᶜ =
        {u : Lp ℝ ⊤ μ |
          MvPolynomial.eval (herglotzJetMap μ w x n u) (P k) ≠ 0} := by
      ext u
      simp [hDdef]
    rw [hcompl]
    exact dense_nondegenerate_herglotzJetMap μ hsupp w hw hwpos x hx hupper n
      (P k) (hP k)
  have hnd : ∀ k, IsNowhereDense (D k) := fun k =>
    isNowhereDense_of_isClosed_of_interior_eq_empty (hclosed k) (hinterior k)
  have hdense := dense_setOf_forall_notMem_of_isNowhereDense D hnd
  convert! hdense using 2 with u

end

end GaloisForLFunctions.HTGeometry
