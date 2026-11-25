import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BudgetComparisons.AnalyticCoefficients

/-! # Power-law separation from zero for continuous functions algebraic over analytic time -/

open Set Filter Topology Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability
open BudgetComparisons
noncomputable section

/-- A nonzero analytic coefficient has a power lower bound at every
date, including dates of tangency of arbitrary finite order. -/
private theorem analytic_margin (c : coefficients) (hc : c≠0) (v : ℝ) :
    ∃ m : ℕ, ∃ B>0, ∀ᶠ t in 𝓝 v, B*|t-v|^m≤|atTime t c| := by
  let g (t : ℝ) := atTime t c
  have ha : AnalyticOnNhd ℝ g univ := analytic_coefficient c
  have hn : ¬∀ᶠ t in 𝓝 v, g t=0 := by
    intro h
    have he := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ v) h
    exact hc (Subtype.ext (funext fun t => he (mem_univ t)))
  obtain ⟨m,k,hk,hv,he⟩ := (ha v (mem_univ _)).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hn
  have hpos := abs_pos.mpr hv
  refine ⟨m,|k v|/2,half_pos hpos,?_⟩
  filter_upwards [he,hk.continuousAt.abs.eventually (lt_mem_nhds (half_lt_self hpos))] with t ht hnear
  change _≤|g t|
  rw [ht,smul_eq_mul,abs_mul,abs_pow,mul_comm]
  exact mul_le_mul_of_nonneg_left hnear.le (pow_nonneg (abs_nonneg _) _)

/-- On each side where the function is nonzero, its distance from zero
decays at most polynomially in the distance to the contact. -/
theorem algebraic_power_margin {f : ℝ → ℝ} (hf : Continuous f) (ha : IsAlgebraic coefficients f)
    (v : ℝ) : ∃ m : ℕ, 0<m ∧ ∃ B>0, ∀ᶠ t in 𝓝 v, f t≠0 → B*|t-v|^m≤|f t| := by
  obtain ⟨Q,hQ,hz⟩ := deflated_equation ha
  obtain ⟨m,b,hb,hc⟩ := analytic_margin _ hQ v
  let k (t : ℝ) := Q.divX.eval₂ (atTime t) (f t)
  let M := |k v|+1
  have hM : 0<M := by dsimp only [M]; positivity
  have hbound : ∀ᶠ t in 𝓝 v, |k t|<M :=
    (continuous_root_test Q.divX hf).continuousAt.abs.eventually (gt_mem_nhds (by dsimp only [M]; linarith))
  have hdist : ∀ᶠ t in 𝓝 v, |t-v|<1 := by
    exact ((continuous_id.sub continuous_const).abs.continuousAt).eventually (gt_mem_nhds (by simp))
  refine ⟨m+1,Nat.succ_pos _,b/M,div_pos hb hM,?_⟩
  filter_upwards [hc,hbound,hdist] with t ht hk hdt
  intro hne
  have hp := congrArg (eval₂RingHom (atTime t) (f t)) (divX_mul_X_add Q)
  change (Q.divX*Polynomial.X+C (Q.coeff 0)).eval₂ (atTime t) (f t)=_ at hp
  rw [eval₂_add,eval₂_mul,eval₂_X,eval₂_C,coeff_zero_eq_eval_zero,hz t hne] at hp
  have he : atTime t (Q.eval 0)=-(k t*f t) := by
    change k t*f t+atTime t (Q.eval 0)=0 at hp
    linarith only [hp]
  rw [he,abs_neg,abs_mul] at ht
  have hsmall : |t-v|^(m+1)≤|t-v|^m := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) _) hdt.le
  have h := (mul_le_mul_of_nonneg_left hsmall hb.le).trans (ht.trans
    (mul_le_mul_of_nonneg_right hk.le (abs_nonneg _)))
  calc
    b/M*|t-v|^(m+1) = (b*|t-v|^(m+1))/M := by ring
    _ ≤ |f t| := (div_le_iff₀ hM).mpr (h.trans_eq (mul_comm ..))

#print axioms algebraic_power_margin
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.ContactStability
