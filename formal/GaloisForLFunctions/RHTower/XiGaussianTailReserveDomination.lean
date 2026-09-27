import GaloisForLFunctions.RHTower.XiGaussianFinitePhaseRemainder

/-!
# Uniform domination of the high spectral tail by the actual real reserve

At each finite order, one fixed spectral cutoff makes the whole high tail
smaller than any prescribed fraction of the independent critical-node floor
at every sufficiently late time, uniformly in every coefficient direction.
The exact finite low-shell imaginary energy remains; no sign assumption is
made about that remainder.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

/-- A fixed cutoff controls the complete tail relative to the independently constructed
coefficient floor, to any positive relative tolerance, uniformly in all coefficients. -/
theorem exists_xiGaussianTail_dominated_by_critical_floor (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧ ∃ R : ℝ, L < R ∧
      (∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        c * Real.exp (-(L * (t : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) ≤
          xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t) ∧
      ∀ ε : {ε : ℝ // 0 < ε}, ∃ T : ℝ, 1 ≤ T ∧
        ∀ (a : ℕ → ℝ) (t : {t : {t : ℝ // 0 < t} // T ≤ (t : ℝ)}),
          xiGaussianTailEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R ≤
              (ε : ℝ) * c * Real.exp (-(L * (t.1 : ℝ))) *
                (∑ j ∈ Finset.range N, a j ^ 2) := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  let R := L + 1
  let k := Real.exp R * xiGaussianCoefficientAnchor N
  have hk : 0 ≤ k := mul_nonneg (Real.exp_pos _).le (xiGaussianCoefficientAnchor_nonneg N)
  refine ⟨c, hc, L, hL, R, by dsimp only [R]; linarith, hfloor, ?_⟩
  intro ε
  have hec : 0 < (ε : ℝ) * c := mul_pos ε.property hc
  let T := 1 + k / ((ε : ℝ) * c)
  have hT : 1 ≤ T := le_add_of_nonneg_right (div_nonneg hk hec.le)
  refine ⟨T, hT, ?_⟩
  intro a t
  have ht1 : 1 ≤ (t.1 : ℝ) := hT.trans t.property
  have hratio : k / ((ε : ℝ) * c) ≤ (t.1 : ℝ) := by
    have h := t.property
    change 1 + k / ((ε : ℝ) * c) ≤ (t.1 : ℝ) at h
    linarith only [h]
  have hkt : k ≤ (ε : ℝ) * c * (t.1 : ℝ) := by
    simpa only [mul_comm (t.1 : ℝ)] using (div_le_iff₀ hec).mp hratio
  have hte : (t.1 : ℝ) ≤ Real.exp (t.1 : ℝ) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hke := hkt.trans (mul_le_mul_of_nonneg_left hte hec.le)
  have hsmall : k * Real.exp (-(t.1 : ℝ)) ≤ (ε : ℝ) * c := by
    have h := mul_le_mul_of_nonneg_right hke (Real.exp_pos (-(t.1 : ℝ))).le
    rwa [mul_assoc ((ε : ℝ) * c), ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h
  have htail := xiGaussianTailEnergy_rangeSum_le_anchor N a ⟨t.1, ht1⟩ R
  have hexp : Real.exp (-(((t.1 : ℝ) - 1) * R)) * xiGaussianCoefficientAnchor N =
      (k * Real.exp (-(t.1 : ℝ))) * Real.exp (-(L * (t.1 : ℝ))) := by
    dsimp only [k]
    calc
      _ = xiGaussianCoefficientAnchor N *
          Real.exp (R + -(t.1 : ℝ) + -(L * (t.1 : ℝ))) := by
        rw [mul_comm]
        congr 2
        dsimp only [R]
        ring
      _ = xiGaussianCoefficientAnchor N *
          (Real.exp R * Real.exp (-(t.1 : ℝ)) * Real.exp (-(L * (t.1 : ℝ)))) := by
        rw [Real.exp_add, Real.exp_add]
      _ = _ := by ring
  change xiGaussianTailEnergy _ t.1 R ≤ _ at htail
  rw [hexp] at htail
  exact htail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- The full tail is an arbitrarily small fraction of actual real-channel energy at all
sufficiently late times; both cutoff and time threshold are coefficient-independent. -/
theorem exists_xiGaussianTail_relative_realChannel_control (N : ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε : {ε : ℝ // 0 < ε}, ∃ T : ℝ, 1 ≤ T ∧
      ∀ (a : ℕ → ℝ) (t : {t : {t : ℝ // 0 < t} // T ≤ (t : ℝ)}),
        xiGaussianTailEnergy
          (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R ≤
            (ε : ℝ) * xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 := by
  obtain ⟨c, hc, L, hL, R, hR, hfloor, htail⟩ :=
    exists_xiGaussianTail_dominated_by_critical_floor N
  refine ⟨R, by linarith only [hL, hR], ?_⟩
  intro ε
  obtain ⟨T, hT, hbound⟩ := htail ε
  refine ⟨T, hT, ?_⟩
  intro a t
  calc
    _ ≤ (ε : ℝ) * c * Real.exp (-(L * (t.1 : ℝ))) *
        (∑ j ∈ Finset.range N, a j ^ 2) := hbound a t
    _ = (ε : ℝ) * (c * Real.exp (-(L * (t.1 : ℝ))) *
        (∑ j ∈ Finset.range N, a j ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hfloor a t.1) ε.property.le

/-- At every finite order, the only remaining late-time loss is the exact finite head phase
energy; the entire infinite tail has been absorbed by half of the independent reserve. -/
theorem exists_xiHeatHankelForm_finite_phase_remainder (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧ ∃ R : ℝ, L < R ∧
      ∃ T : ℝ, 1 ≤ T ∧
        ∀ (a : ℕ → ℝ) (t : {t : {t : ℝ // 0 < t} // T ≤ (t : ℝ)}),
          (c / 2) * Real.exp (-(L * (t.1 : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) -
            xiGaussianHeadPhaseEnergy
              (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R ≤
                xiHeatHankelForm N a t.1 := by
  obtain ⟨c, hc, L, hL, R, hR, hfloor, htail⟩ :=
    exists_xiGaussianTail_dominated_by_critical_floor N
  obtain ⟨T, hT, hbound⟩ := htail ⟨1 / 2, by positivity⟩
  refine ⟨c, hc, L, hL, R, hR, T, hT, ?_⟩
  intro a t
  have hj := hfloor a t.1
  have hk := hbound a t
  have hh := xiGaussianTrace_ge_realChannel_sub_headPhase_sub_tail
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 R
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property] at hh
  change xiGaussianTailEnergy _ t.1 R ≤
    (1 / 2 : ℝ) * c * Real.exp (-(L * (t.1 : ℝ))) * (∑ j ∈ Finset.range N, a j ^ 2) at hk
  linarith only [hj, hk, hh]

/-- Complete three-by-three specialization, retaining every coefficient cross term in the
actual form and in the finite phase remainder. -/
theorem exists_xiHeatThirdQuadratic_finite_phase_remainder :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧ ∃ R : ℝ, L < R ∧
      ∃ T : ℝ, 1 ≤ T ∧
        ∀ (a b c : ℝ) (t : {t : {t : ℝ // 0 < t} // T ≤ (t : ℝ)}),
          (c₀ / 2) * Real.exp (-(L * (t.1 : ℝ))) * (a ^ 2 + b ^ 2 + c ^ 2) -
            xiGaussianHeadPhaseEnergy (xiHeatThirdPolynomial a b c) t.1 R ≤
              xiHeatThirdQuadratic a b c t.1 := by
  obtain ⟨c₀, hc₀, L, hL, R, hR, T, hT, hbound⟩ :=
    exists_xiHeatHankelForm_finite_phase_remainder 3
  refine ⟨c₀, hc₀, L, hL, R, hR, T, hT, ?_⟩
  intro a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [xiHeatThirdPolynomial, Finset.sum_range_succ] using
    hbound (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
