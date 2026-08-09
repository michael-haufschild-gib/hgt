import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaMoments

/-!
# A uniform bound for the finite Euler products

The Euler factors of a contracting nome family are at least one and form a multipliable family, so
every finite partial product is bounded by the infinite one.  Raising the nomes to a higher power
only shrinks the factors, so the bound is uniform in the power as well as in the nome set.

This is the estimate the counterterm jet needs: the finite Euler products appearing in the
jet's coefficients never grow, whatever nome set and whatever order they are taken at.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

/-- The real Euler factors of the genus power form a multipliable family. -/
theorem multipliable_realEulerFactor {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1))) :
    Multipliable (fun a => (1 - ‖p a‖ ^ (g + 1))⁻¹) := by
  classical
  have hlt : ∀ a, ‖p a‖ ^ (g + 1) < 1 :=
    fun a => pow_lt_one₀ (norm_nonneg _) (hp_lt a) (by omega)
  have hpos : ∀ a, (0 : ℝ) < 1 - ‖p a‖ ^ (g + 1) := fun a => by linarith [hlt a]
  have hfin : {a : ι | (1 : ℝ) / 2 ≤ ‖p a‖ ^ (g + 1)}.Finite := by
    have h := hsum.tendsto_cofinite_zero
    have h2 : ∀ᶠ a in Filter.cofinite, ‖p a‖ ^ (g + 1) ∈ Metric.ball (0 : ℝ) (1 / 2) :=
      h (Metric.ball_mem_nhds 0 (by norm_num))
    refine (Filter.eventually_cofinite.mp h2).subset ?_
    intro a ha
    simp only [Set.mem_setOf_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt] at ha ⊢
    exact le_trans ha (le_abs_self _)
  set F : Finset ι := hfin.toFinset with hF
  set f : ι → ℝ := fun a => ‖p a‖ ^ (g + 1) / (1 - ‖p a‖ ^ (g + 1)) with hfdef
  have hfnn : ∀ a, 0 ≤ f a := fun a => by
    rw [hfdef]
    exact div_nonneg (by positivity) (le_of_lt (hpos a))
  have hmaj : Summable (fun a => (if a ∈ F then f a else 0) + 2 * ‖p a‖ ^ (g + 1)) := by
    refine Summable.add ?_ (hsum.mul_left 2)
    exact summable_of_ne_finset_zero (s := F) fun a ha => by simp [ha]
  have hfsum : Summable f := by
    refine Summable.of_nonneg_of_le hfnn (fun a => ?_) hmaj
    by_cases haF : a ∈ F
    · have h2 : (0 : ℝ) ≤ 2 * ‖p a‖ ^ (g + 1) := by positivity
      simp only [haF, if_true]
      linarith
    · have hsmall : ‖p a‖ ^ (g + 1) < 1 / 2 := by
        by_contra hcon
        apply haF
        rw [hF, Set.Finite.mem_toFinset]
        show (1 : ℝ) / 2 ≤ ‖p a‖ ^ (g + 1)
        linarith [not_lt.mp hcon]
      have hden : (1 : ℝ) / 2 < 1 - ‖p a‖ ^ (g + 1) := by linarith
      have hle : f a ≤ 2 * ‖p a‖ ^ (g + 1) := by
        rw [hfdef, div_le_iff₀ (hpos a)]
        nlinarith [pow_nonneg (norm_nonneg (p a)) (g + 1)]
      simp only [haF, if_false, zero_add]
      exact hle
  have hmul := Real.multipliable_one_add_of_summable hfsum
  refine hmul.congr fun a => ?_
  have hne : (1 : ℝ) - ‖p a‖ ^ (g + 1) ≠ 0 := ne_of_gt (hpos a)
  rw [hfdef]
  field_simp
  ring

/-- **The finite Euler products are uniformly bounded.**  The bound is independent of the nome set
and of the power, as long as the power is at least the genus. -/
theorem norm_finiteEulerProduct_le {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    (S : Finset ι) {k : ℕ} (hk : g + 1 ≤ k) :
    ‖∏ a ∈ S, (1 - p a ^ k)⁻¹‖ ≤ ∏' a, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
  classical
  have hlt : ∀ a, ‖p a‖ ^ (g + 1) < 1 :=
    fun a => pow_lt_one₀ (norm_nonneg _) (hp_lt a) (by omega)
  have hpos : ∀ a, (0 : ℝ) < 1 - ‖p a‖ ^ (g + 1) := fun a => by linarith [hlt a]
  have hfactor : ∀ a : ι, ‖(1 - p a ^ k)⁻¹‖ ≤ (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    intro a
    have hpk : ‖p a‖ ^ k ≤ ‖p a‖ ^ (g + 1) :=
      pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt (hp_lt a)) hk
    have hlow : 1 - ‖p a‖ ^ (g + 1) ≤ ‖1 - p a ^ k‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (p a ^ k)
      rw [norm_one, norm_pow] at h
      linarith
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (hpos a) hlow
  have hprodle : ‖∏ a ∈ S, (1 - p a ^ k)⁻¹‖ ≤ ∏ a ∈ S, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun a _ => norm_nonneg _) (fun a _ => hfactor a)
  refine hprodle.trans ?_
  have hone : ∀ a : ι, (1 : ℝ) ≤ (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    intro a
    have h2 : (1 : ℝ) - ‖p a‖ ^ (g + 1) ≤ 1 := by
      have := pow_nonneg (norm_nonneg (p a)) (g + 1)
      linarith
    simpa using one_div_le_one_div_of_le (hpos a) h2
  have hmul := multipliable_realEulerFactor g p hp_lt hsum
  refine ge_of_tendsto hmul.hasProd ?_
  filter_upwards [eventually_ge_atTop S] with T hT
  have hsub : S ⊆ T := hT
  have hsplit : (∏ a ∈ T \ S, (1 - ‖p a‖ ^ (g + 1))⁻¹) *
      ∏ a ∈ S, (1 - ‖p a‖ ^ (g + 1))⁻¹
      = ∏ a ∈ T, (1 - ‖p a‖ ^ (g + 1))⁻¹ := Finset.prod_sdiff hsub
  have hge1 : (1 : ℝ) ≤ ∏ a ∈ T \ S, (1 - ‖p a‖ ^ (g + 1))⁻¹ := by
    calc (1 : ℝ) = ∏ _a ∈ T \ S, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ a ∈ T \ S, (1 - ‖p a‖ ^ (g + 1))⁻¹ :=
          Finset.prod_le_prod (fun a _ => by norm_num) (fun a _ => hone a)
  have hSnn : (0 : ℝ) ≤ ∏ a ∈ S, (1 - ‖p a‖ ^ (g + 1))⁻¹ :=
    Finset.prod_nonneg fun a _ => le_trans (by norm_num) (hone a)
  rw [← hsplit]
  nlinarith [hge1, hSnn]

end HTGeometry
