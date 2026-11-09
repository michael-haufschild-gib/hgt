import GaloisForLFunctions.InfiniteRankWeilTheory.OscillatorySamplingDimension
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Residual exponential cancellation for a positive conjugate pair

The resonant grids of `cos(n ell)` become arbitrarily fine. Baire's theorem therefore gives a
dense G-delta of bases with arbitrarily strong exponential cancellations. On positive bases
this set has Hausdorff dimension zero, despite being uncountable in every open interval.
-/

open Set Metric Filter Topology

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

private def cosineCancellationWindow (m N : ℕ) : Set ℝ :=
  ⋃ n ≥ N, {ℓ | |Real.cos (((n : ℝ) + 1) * ℓ)| <
    Real.exp (-((m : ℝ) + 1) * ((n : ℝ) + 1))}

private theorem isOpen_cosineCancellationWindow (m N : ℕ) :
    IsOpen (cosineCancellationWindow m N) := by
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro _
  exact isOpen_lt (Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs
    continuous_const

private theorem dense_cosineCancellationWindow (m N : ℕ) :
    Dense (cosineCancellationWindow m N) := by
  apply Metric.dense_iff.mpr
  intro x ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (Real.pi / ε))
  have hnN : N ≤ n := by exact_mod_cast ((le_max_left _ _).trans_lt hn).le
  let ν : ℝ := (n : ℝ) + 1
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνε : Real.pi < ν * ε := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    dsimp [ν]
    nlinarith only [h, hε]
  let j : ℤ := ⌊ν * x / Real.pi - 1 / 2⌋
  let y : ℝ := (Real.pi / 2 + (j : ℝ) * Real.pi) / ν
  have hy : ν * y = Real.pi / 2 + (j : ℝ) * Real.pi := by
    dsimp [y]
    field_simp
  have hlo : Real.pi / 2 + (j : ℝ) * Real.pi ≤ ν * x := by
    have h := mul_le_mul_of_nonneg_right (Int.floor_le (ν * x / Real.pi - 1 / 2)) Real.pi_pos.le
    have heq : (ν * x / Real.pi - 1 / 2) * Real.pi = ν * x - Real.pi / 2 := by
      field_simp <;> ring
    rw [heq] at h
    change (j : ℝ) * Real.pi ≤ ν * x - Real.pi / 2 at h
    linarith only [h]
  have hhi : ν * x < Real.pi / 2 + (j : ℝ) * Real.pi + Real.pi := by
    have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (ν * x / Real.pi - 1 / 2)) Real.pi_pos
    have heq : (ν * x / Real.pi - 1 / 2) * Real.pi = ν * x - Real.pi / 2 := by
      field_simp <;> ring
    rw [heq] at h
    change ν * x - Real.pi / 2 < ((j : ℝ) + 1) * Real.pi at h
    linarith only [h]
  refine ⟨y, ?_, mem_iUnion₂.mpr ⟨n, hnN, ?_⟩⟩
  · rw [mem_ball, Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> nlinarith only [hlo, hhi, hy, hν, hνε, hε]
  · change |Real.cos (ν * y)| < _
    rw [hy, Real.cos_add_int_mul_pi, Real.cos_pi_div_two, mul_zero, abs_zero]
    exact Real.exp_pos _

/-- Bases with exponential cosine cancellations beyond every finite cutoff and at every
integer decay rate. -/
def cosineCancellationBases : Set ℝ :=
  ⋂ p : ℕ × ℕ, cosineCancellationWindow p.1 p.2

theorem isGδ_cosineCancellationBases : IsGδ cosineCancellationBases :=
  IsGδ.iInter_of_isOpen fun p => isOpen_cosineCancellationWindow p.1 p.2

theorem dense_cosineCancellationBases : Dense cosineCancellationBases :=
  dense_iInter_of_isOpen (fun p => isOpen_cosineCancellationWindow p.1 p.2)
    (fun p => dense_cosineCancellationWindow p.1 p.2)

/-- The cancellation set is uncountable in every nonempty open interval. -/
theorem not_countable_cosineCancellationBases_inter_Ioo {a b : ℝ} (hab : a < b) :
    ¬ (cosineCancellationBases ∩ Ioo a b).Countable := by
  intro hcount
  have hm (x : ℝ) : IsMeagre ({x} : Set ℝ) :=
    residual_of_dense_open isClosed_singleton.isOpen_compl (dense_compl_singleton x)
  have hsmall : IsMeagre (cosineCancellationBases ∩ Ioo a b) := by
    have heq : (⋃ x ∈ cosineCancellationBases ∩ Ioo a b, ({x} : Set ℝ)) =
        cosineCancellationBases ∩ Ioo a b := by ext x; simp
    rw [← heq]
    exact isMeagre_biUnion hcount (fun x _ => hm x)
  have hcompl : IsMeagre cosineCancellationBasesᶜ := by
    rw [IsMeagre, compl_compl]
    exact residual_of_dense_Gδ isGδ_cosineCancellationBases dense_cosineCancellationBases
  apply not_isMeagre_of_isOpen isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  apply (hsmall.union hcompl).mono
  intro x hx
  by_cases hxs : x ∈ cosineCancellationBases
  · exact Or.inl ⟨hxs, hx⟩
  · exact Or.inr hxs

/-- Every positive base in the residual set has infinitely many cancellations at any prescribed
decay rate measured in the sampled time. -/
theorem cosineCancellationBases_exp_small {ℓ : ℝ} (hℓ : ℓ ∈ cosineCancellationBases)
    (hℓ0 : 0 < ℓ) (δ : ℝ) :
    ℓ ∈ exponentiallySmallSamplingBases (fun t => (Real.cos t : ℂ)) δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (δ * ℓ)
  refine ⟨hℓ0, frequently_atTop.mpr fun N => ?_⟩
  have hwin := mem_iInter.mp hℓ (m, N)
  obtain ⟨n, hn, hsmall⟩ := mem_iUnion₂.mp hwin
  refine ⟨n + 1, by omega, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one]
  refine hsmall.le.trans (Real.exp_le_exp.mpr ?_)
  have hrate : δ * ℓ ≤ (m : ℝ) + 1 := by linarith only [hm]
  have hmul := mul_le_mul_of_nonneg_right hrate
    (by positivity : 0 ≤ (n : ℝ) + 1)
  nlinarith only [hmul]

/-- Cosine is the finite oscillatory sum of two positive conjugate coefficients. -/
theorem cosine_eq_positive_oscillatory_pair (t : ℝ) :
    (Real.cos t : ℂ) = oscillatoryJet ![1, -1] (fun _ : Fin 2 => (1 / 2 : ℂ)) 0 t := by
  rw [Complex.ofReal_cos]
  simp only [oscillatoryJet, TrigSum.trigSum, pow_zero, mul_one, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Complex.ofReal_one,
    Complex.ofReal_neg, one_mul, neg_one_mul]
  have h := Complex.two_cos (t : ℂ)
  rw [mul_comm (t : ℂ) Complex.I, show -(t : ℂ) * Complex.I = Complex.I * -(t : ℂ) by ring] at h
  linear_combination h / 2

/-- Multiplying the positive conjugate pair by any exponential growth factor still leaves
recurrent readings below every prescribed exponential rate on the same residual set of bases. -/
theorem cosineCancellationBases_growing_pair_recurrence {ℓ : ℝ}
    (hℓ : ℓ ∈ cosineCancellationBases) (hℓ0 : 0 < ℓ) (θ a : ℝ) :
    ∃ᶠ n : ℕ in atTop,
      ‖(Real.exp (θ * ((n : ℝ) * ℓ)) : ℂ) * (Real.cos ((n : ℝ) * ℓ) : ℂ)‖ ≤
        Real.exp (a * ((n : ℝ) * ℓ)) := by
  have hsmall := (cosineCancellationBases_exp_small hℓ hℓ0 (θ - a)).2
  refine hsmall.mono fun n hn => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (θ * ((n : ℝ) * ℓ)) * ‖(Real.cos ((n : ℝ) * ℓ) : ℂ)‖
      ≤ Real.exp (θ * ((n : ℝ) * ℓ)) * Real.exp (-(θ - a) * ((n : ℝ) * ℓ)) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = Real.exp (a * ((n : ℝ) * ℓ)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A dense G-delta of positive bases can lie inside a dimension-zero exceptional sampling set,
even for the positive conjugate pair defining cosine. -/
theorem dimH_positive_cosineCancellationBases_eq_zero :
    dimH (cosineCancellationBases ∩ Ioi 0) = 0 := by
  have hfreq : Function.Injective (![1, -1] : Fin 2 → ℝ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> norm_num at h ⊢
  have hc : (fun _ : Fin 2 => (1 / 2 : ℂ)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  have heq : (fun t => (Real.cos t : ℂ)) =
      oscillatoryJet ![1, -1] (fun _ : Fin 2 => (1 / 2 : ℂ)) 0 :=
    funext cosine_eq_positive_oscillatory_pair
  have hdim : dimH (exponentiallySmallSamplingBases (fun t => (Real.cos t : ℂ)) 1) = 0 := by
    rw [heq]
    exact dimH_oscillatory_exp_small_eq_zero _ hfreq _ hc zero_lt_one
  have hsub : cosineCancellationBases ∩ Ioi 0 ⊆
      exponentiallySmallSamplingBases (fun t => (Real.cos t : ℂ)) 1 :=
    fun _ hℓ => cosineCancellationBases_exp_small hℓ.1 hℓ.2 1
  exact le_antisymm ((dimH_mono hsub).trans_eq hdim) bot_le

#print axioms dense_cosineCancellationBases
#print axioms not_countable_cosineCancellationBases_inter_Ioo
#print axioms cosineCancellationBases_growing_pair_recurrence
#print axioms dimH_positive_cosineCancellationBases_eq_zero

end GaloisForLFunctions.InfiniteRankWeilTheory
