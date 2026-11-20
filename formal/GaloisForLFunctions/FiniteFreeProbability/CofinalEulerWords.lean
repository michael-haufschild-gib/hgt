import GaloisForLFunctions.FiniteFreeProbability.CofinalEulerJensenTest
import GaloisForLFunctions.FiniteFreeProbability.QuadraticCostOfEulerFilters

/-!
# Cofinal Xi tests with variable lists of Euler weights

Descending from degree `n` to `d` raises every Euler weight by `n-d`.
A normalized list whose total squared reciprocal weight tends to zero thus
recovers every fixed lower polynomial. The test allows an unbounded number
of degree-dependent filters, including every subquadratic list length.
-/

open Polynomial Filter Topology RHTower
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

/-- Weights transported by a descent of `m` degrees in the Jensen ladder. -/
def raisedEulerWeights (w : List ℕ) (m : ℕ) := w.map fun s => s+m

private theorem word_deriv (w : List ℕ) (p : ℝ[X]) :
    derivative (eulerWord w p) = eulerWord (raisedEulerWeights w 1) (derivative p) := by
  induction w generalizing p with
  | nil => rfl
  | cons s w ih =>
    change derivative (eulerWord w (eulerFilter s p)) = eulerWord (raisedEulerWeights w 1) _
    rw [ih, derivative_eulerFilter]

private theorem word_scalar (w : List ℕ) (p : ℝ[X]) (a : ℝ) :
    eulerWord w (C a*p) = C a*eulerWord w p := by
  ext j
  simp only [eulerWord_coeff, coeff_C_mul]
  ring

private theorem word_descend_one {w : List ℕ} {d : ℕ}
    (hs : (eulerWord w (xiJensenReal (d+1))).Splits) :
    (eulerWord (raisedEulerWeights w 1) (xiJensenReal d)).Splits := by
  have hd := splits_laguerreShift hs 0
  have hJ : derivative (xiJensenReal (d+1)) = C ((d : ℝ)+1)*xiJensenReal d := by
    rw [xiJensenReal_eq, xiJensenReal_eq, derivative_jensenRev]
  simp only [laguerreShift, map_zero, zero_mul, sub_zero, word_deriv, hJ, word_scalar] at hd
  exact (splits_mul_iff_right (C_ne_zero.mpr (by positivity)) (Polynomial.Splits.C _)).mp hd

private theorem word_descend (w : List ℕ) (d m : ℕ)
    (hs : (eulerWord w (xiJensenReal (d+m))).Splits) :
    (eulerWord (raisedEulerWeights w m) (xiJensenReal d)).Splits := by
  induction m generalizing w with
  | zero => simpa [raisedEulerWeights] using hs
  | succ m ih =>
    have h := ih (raisedEulerWeights w 1) (word_descend_one hs)
    simpa [raisedEulerWeights, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm 1] using h

private theorem cost_cons (s : ℕ) (w : List ℕ) :
    eulerCollisionCost (s::w) = ((s : ℝ)+2)⁻¹^2 + eulerCollisionCost w := rfl

private theorem cost_pos (w : List ℕ) : 0 ≤ eulerCollisionCost w := by
  induction w with
  | nil => exact le_rfl
  | cons s w ih => rw [cost_cons]; exact add_nonneg (sq_nonneg _) ih

private theorem cost_tail (w : List ℕ) {d m : ℕ} (hd : d ≤ m) :
    eulerCollisionCost (raisedEulerWeights w m) ≤ 4 * eulerCollisionCost (raisedEulerWeights w (m+d)) := by
  induction w with
  | nil => simp [raisedEulerWeights, eulerCollisionCost]
  | cons s w ih =>
    change eulerCollisionCost ((s+m)::raisedEulerWeights w m) ≤ 4*eulerCollisionCost ((s+(m+d))::raisedEulerWeights w (m+d))
    rw [cost_cons, cost_cons]
    have hpos : (0 : ℝ) < (s+m : ℕ)+2 := by positivity
    have hpos' : (0 : ℝ) < (s+(m+d) : ℕ)+2 := by positivity
    have hinv : (((s+m : ℕ) : ℝ)+2)⁻¹ ≤ 2*(((s+(m+d) : ℕ) : ℝ)+2)⁻¹ := by
      rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hpos hpos']
      push_cast
      linarith only [show (d : ℝ) ≤ m by exact_mod_cast hd, Nat.cast_nonneg s]
    have hs := pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv 2
    nlinarith only [hs,ih]

/-- Cost after descent is at most the word length times the squared reciprocal degree scale. -/
theorem eulerCollisionCost_degree_bound (w : List ℕ) (m : ℕ) :
    eulerCollisionCost (raisedEulerWeights w m) ≤ (w.length : ℝ)*((m : ℝ)+2)⁻¹^2 := by
  induction w with
  | nil => simp [raisedEulerWeights, eulerCollisionCost]
  | cons s w ih =>
    change eulerCollisionCost ((s+m)::raisedEulerWeights w m) ≤ _
    rw [cost_cons, List.length_cons, Nat.cast_succ]
    have hs : (((s+m : ℕ) : ℝ)+2)⁻¹ ≤ ((m : ℝ)+2)⁻¹ :=
      inv_anti₀ (by positivity) (by push_cast; linarith only [Nat.cast_nonneg s])
    have hh := pow_le_pow_left₀ (by positivity) hs 2
    linarith only [ih,hh]

private theorem norm_degree (w : List ℕ) (p : ℝ[X]) :
    (normalizedEulerWord w p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [normalizedEulerWord_coeff, coeff_eq_zero_of_natDegree_lt hj, mul_zero]

private theorem norm_limit (w : ℕ → List ℕ)
    (hw : Tendsto (fun i => eulerCollisionCost (w i)) atTop (𝓝 0)) (p : ℝ[X]) (j : ℕ) :
    Tendsto (fun i => (normalizedEulerWord (w i) p).coeff j) atTop (𝓝 (p.coeff j)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_)
    (show Tendsto (fun i => (|p.coeff j| * (j.choose 2 : ℝ))*eulerCollisionCost (w i)) atTop (𝓝 0) by
      simpa using hw.const_mul (|p.coeff j| * (j.choose 2 : ℝ)))
  simpa only [Real.norm_eq_abs] using normalizedEulerWord_error (w i) p j

/-- A cofinal sequence of split filtered polynomials with vanishing quadratic
cost forces every unfiltered degree to split. Both degree and filters may vary. -/
theorem riemannHypothesis_iff_vanishing_euler_cost :
    RiemannHypothesis ↔ ∃ (n : ℕ → ℕ) (w : ℕ → List ℕ),
      Tendsto n atTop atTop ∧ Tendsto (fun i => eulerCollisionCost (raisedEulerWeights (w i) (n i))) atTop (𝓝 0) ∧
      ∀ i, (eulerWord (w i) (xiJensenReal (n i))).Splits := by
  constructor
  · intro h
    exact ⟨id, fun _ => [], tendsto_id, tendsto_const_nhds, fun i =>
      JensenStrict.jensenReverse_splits (riemannHypothesis_iff_laguerrePolya_XiC.mp h) XiC_conj i⟩
  · rintro ⟨n,w,hn,hw,hs⟩
    apply riemannHypothesis_iff_frequently_splits_jensenPoly_XiC.mpr
    apply Frequently.of_forall
    intro d
    have hd : ∀ᶠ i in atTop, 2*d ≤ n i := hn.eventually_ge_atTop _
    let v i := raisedEulerWeights (w i) (n i-d)
    have hv : Tendsto (fun i => eulerCollisionCost (v i)) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall fun _ => cost_pos _) ?_
        (show Tendsto (fun i => 4*eulerCollisionCost (raisedEulerWeights (w i) (n i))) atTop (𝓝 0) by
          simpa using hw.const_mul 4)
      filter_upwards [hd] with i hi
      have h := cost_tail (w i) (d := d) (m := n i-d) (by omega)
      rwa [Nat.sub_add_cancel (show d ≤ n i by omega)] at h
    have hsplit : (xiJensenReal d).Splits := by
      by_contra hb
      have hbad := _root_.HTGeometry.eventually_not_splits_of_coeff_limit
        (p := fun i => normalizedEulerWord (v i) (xiJensenReal d))
        (fun _ => norm_degree _ _) le_rfl (xiJensenReal_ne_zero d) (norm_limit v hv _ ) hb
      obtain ⟨i,hi,hbadi⟩ := (hd.and hbad).exists
      have hs' : (eulerWord (w i) (xiJensenReal (d+(n i-d)))).Splits := by
        rwa [Nat.add_sub_of_le (show d ≤ n i by omega)]
      exact hbadi (normalizedEulerWord_splits _ _ (word_descend _ _ _ hs'))
    rw [← reflect_jensenReverse]
    exact Splits.reflect hsplit (natDegree_jensenReverse_le _ _)

/-- Subquadratic word length suffices even if the anchor weights are chosen adversarially. -/
theorem riemannHypothesis_iff_subquadratic_euler_words :
    RiemannHypothesis ↔ ∃ (n : ℕ → ℕ) (w : ℕ → List ℕ), Tendsto n atTop atTop ∧
      Tendsto (fun i => ((w i).length : ℝ)*((n i : ℝ)+2)⁻¹^2) atTop (𝓝 0) ∧
      ∀ i, (eulerWord (w i) (xiJensenReal (n i))).Splits := by
  constructor
  · intro h
    refine ⟨id, fun _ => [], tendsto_id, ?_, fun i =>
      JensenStrict.jensenReverse_splits (riemannHypothesis_iff_laguerrePolya_XiC.mp h) XiC_conj i⟩
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · rintro ⟨n,w,hn,hw,hs⟩
    exact riemannHypothesis_iff_vanishing_euler_cost.mpr ⟨n,w,hn,
      squeeze_zero (fun _ => cost_pos _) (fun _ => eulerCollisionCost_degree_bound _ _) hw,hs⟩


end

end FiniteFreeProbability
