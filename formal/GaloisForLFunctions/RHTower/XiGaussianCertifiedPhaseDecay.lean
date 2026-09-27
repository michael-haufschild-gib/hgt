import GaloisForLFunctions.RHTower.XiGaussianCertifiedPhaseGap
import GaloisForLFunctions.RHTower.XiGaussianUniformCutoff

/-!
# Coefficient-uniform decay of the complete Xi phase channel

The source-certified gap applies to the entire imaginary channel. An arbitrary
positive anchor time gives its exponential ceiling, uniformly over coefficients
at each finite order. Choosing half the current time makes the bound available
on the whole positive time axis. Combining it with the independent critical
reserve yields a signed bound for every actual Hankel form, including the full
three-by-three form. No sign is claimed for the resulting difference of bounds.
-/

open scoped Real BigOperators
noncomputable section

namespace RHTower

/-- Every nonempty coefficient family has a strictly positive anchor at each positive time. -/
theorem xiGaussianCoefficientAnchorAt_pos (n : ℕ) (s : {s : ℝ // 0 < s}) :
    0 < xiGaussianCoefficientAnchorAt (n + 1) s := by
  obtain ⟨_, q, _, _, _⟩ := exists_xiCriticalGaussian_nodes 1
  let p := q 0
  have hterm : 0 < ‖xiPolynomialGaussianHeatTerm 1 s p‖ := by
    rw [norm_xiPolynomialGaussianHeatTerm]
    simp only [evalRealPolynomial, Polynomial.map_one, Polynomial.eval_one,
      norm_one, one_pow, one_mul]
    exact Real.exp_pos _
  have hsum := (summable_norm_xiPolynomialGaussianHeatTerm s.property 1).sum_le_tsum
    {p} (fun _ _ => norm_nonneg _)
  simp only [Finset.sum_singleton] at hsum
  have hanchor := Finset.single_le_sum
    (s := Finset.range (n + 1))
    (f := fun j => ∑' r : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm (Polynomial.X ^ j) s r‖)
    (fun j _ => tsum_nonneg fun _ => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simp only [pow_zero] at hanchor
  exact hterm.trans_le (hsum.trans hanchor)

/-- A fixed positive anchor controls the whole phase channel, not only a selected tail. -/
theorem xiGaussianImaginaryChannel_le_certified_anchorAt (N : ℕ) (a : ℕ → ℝ)
    (s : {s : ℝ // 0 < s}) (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1 q) ≤
        Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) *
          xiGaussianCoefficientAnchorAt N s * (∑ j ∈ Finset.range N, a j ^ 2) := by
  rw [xiGaussianImaginaryChannel_eq_certifiedTail]
  exact (xiGaussianTailPhaseEnergy_le_energy _ t.1 xiGaussianCertifiedPhaseGap).trans
    (xiGaussianTailEnergy_le_anchorAt N a s t xiGaussianCertifiedPhaseGap)

/-- Half-time anchoring gives a complete phase ceiling for every positive time. -/
theorem xiGaussianImaginaryChannel_le_certified_halfTime (N : ℕ) (a : ℕ → ℝ)
    (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q) ≤
        Real.exp (-((t : ℝ) / 2 * xiGaussianCertifiedPhaseGap)) *
          xiGaussianCoefficientAnchorAt N (xiGaussianHalfHeat t) *
            (∑ j ∈ Finset.range N, a j ^ 2) := by
  have h := xiGaussianImaginaryChannel_le_certified_anchorAt N a (xiGaussianHalfHeat t)
    ⟨t, by change (t : ℝ) / 2 ≤ (t : ℝ); linarith only [t.property]⟩
  change (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom _ t q) ≤
    Real.exp (-(((t : ℝ) - (t : ℝ) / 2) * xiGaussianCertifiedPhaseGap)) * _ * _ at h
  rw [show (t : ℝ) - (t : ℝ) / 2 = (t : ℝ) / 2 by ring] at h
  exact h

/-- Past time one the coefficient-independent anchor is constant in time. -/
theorem xiGaussianImaginaryChannel_le_certified_timeOne (N : ℕ) (a : ℕ → ℝ)
    (t : {t : ℝ // 1 ≤ t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t q) ≤
        Real.exp (-(((t : ℝ) - 1) * xiGaussianCertifiedPhaseGap)) *
          xiGaussianCoefficientAnchor N * (∑ j ∈ Finset.range N, a j ^ 2) := by
  rw [xiGaussianImaginaryChannel_eq_certifiedTail _
    ⟨t, zero_lt_one.trans_le t.property⟩]
  exact (xiGaussianTailPhaseEnergy_le_energy _ _ xiGaussianCertifiedPhaseGap).trans
    (xiGaussianTailEnergy_rangeSum_le_anchor N a t xiGaussianCertifiedPhaseGap)

/-- Every finite head phase is controlled by the same complete-channel ceiling. -/
theorem xiGaussianHeadPhaseEnergy_le_certified_halfTime (N : ℕ) (a : ℕ → ℝ)
    (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianHeadPhaseEnergy
      (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t R ≤
        Real.exp (-((t : ℝ) / 2 * xiGaussianCertifiedPhaseGap)) *
          xiGaussianCoefficientAnchorAt N (xiGaussianHalfHeat t) *
            (∑ j ∈ Finset.range N, a j ^ 2) := by
  have h := (summable_xiGaussianImaginaryChannelAtom
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t).sum_le_tsum
      (finite_xiHeatShell R).toFinset (fun q _ => xiGaussianImaginaryChannelAtom_nonneg _ t q)
  exact h.trans (xiGaussianImaginaryChannel_le_certified_halfTime N a t)

/-- The independent reserve and the complete phase ceiling bound every actual Hankel form
at every positive time, without leaving an unbounded finite phase remainder. -/
theorem exists_xiHeatHankelForm_allTime_certifiedPhase_lower (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a : ℕ → ℝ) (t : {t : ℝ // 0 < t}),
        (c * Real.exp (-(L * (t : ℝ))) -
          Real.exp (-((t : ℝ) / 2 * xiGaussianCertifiedPhaseGap)) *
            xiGaussianCoefficientAnchorAt N (xiGaussianHalfHeat t)) *
              (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  refine ⟨c, hc, L, hL, ?_⟩
  intro a t
  have hf := hfloor a t
  have hd := xiGaussianImaginaryChannel_le_certified_halfTime N a t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.property] at he
  nlinarith only [hf, hd, he]

/-- A time-independent coefficient anchor exposes the exact late-time rate comparison. -/
theorem exists_xiHeatHankelForm_certifiedPhase_anchor_lower (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a : ℕ → ℝ) (s : {s : ℝ // 0 < s})
        (t : {t : {t : ℝ // 0 < t} // (s : ℝ) ≤ (t : ℝ)}),
        (c * Real.exp (-(L * (t.1 : ℝ))) -
          Real.exp (-(((t.1 : ℝ) - (s : ℝ)) * xiGaussianCertifiedPhaseGap)) *
            xiGaussianCoefficientAnchorAt N s) *
              (∑ j ∈ Finset.range N, a j ^ 2) ≤ xiHeatHankelForm N a t.1 := by
  obtain ⟨c, hc, L, hL, hfloor⟩ := exists_xiGaussianRealChannel_allTime_floor N
  refine ⟨c, hc, L, hL, ?_⟩
  intro a s t
  have hf := hfloor a t.1
  have hd := xiGaussianImaginaryChannel_le_certified_anchorAt N a s t
  have he := xiGaussianTrace_eq_realChannel_sub_imaginary
    (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) t.1
  rw [xiPolynomialGaussianHeatTraceReal_rangeSum t.1.property] at he
  nlinarith only [hf, hd, he]

/-- The full degree-two imaginary channel retains every coefficient cross term. -/
theorem xiHeatThirdImaginaryChannel_le_certified_halfTime (a b c : ℝ)
    (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom (xiHeatThirdPolynomial a b c) t q) ≤
      Real.exp (-((t : ℝ) / 2 * xiGaussianCertifiedPhaseGap)) *
        xiGaussianCoefficientAnchorAt 3 (xiGaussianHalfHeat t) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  simpa [xiHeatThirdPolynomial, Finset.sum_range_succ] using
    xiGaussianImaginaryChannel_le_certified_halfTime 3
      (fun n => if n = 0 then a else if n = 1 then b else c) t

/-- The native three-by-three phase debt is exactly twice the complete imaginary channel. -/
theorem xiHeatThirdPhaseDebt_eq_two_mul_imaginaryChannel (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a b c τ =
      2 * ∑' q : XiZeroCopy,
        xiGaussianImaginaryChannelAtom (xiHeatThirdPolynomial a b c) (Real.exp τ) q := by
  have hp (q : XiZeroCopy) :
      xiGaussianImaginaryChannelAtom (xiHeatThirdPolynomial a b c) (Real.exp τ) q =
        (xiHeatThirdAmplitude a b c τ q).im ^ 2 := by
    rw [xiGaussianImaginaryChannelAtom, ← xiHeatThirdAmplitude_sq, norm_pow,
      Complex.sq_norm, Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  simp only [xiHeatThirdPhaseDebt, hp]

/-- An unconditional bound on the whole actual three-by-three debt for every heat time. -/
theorem xiHeatThirdPhaseDebt_le_certified_halfTime (a b c τ : ℝ) :
    xiHeatThirdPhaseDebt a b c τ ≤
      2 * (Real.exp (-(Real.exp τ / 2 * xiGaussianCertifiedPhaseGap)) *
        xiGaussianCoefficientAnchorAt 3
          (xiGaussianHalfHeat ⟨Real.exp τ, Real.exp_pos τ⟩) * (a ^ 2 + b ^ 2 + c ^ 2)) := by
  rw [xiHeatThirdPhaseDebt_eq_two_mul_imaginaryChannel]
  exact mul_le_mul_of_nonneg_left
    (xiHeatThirdImaginaryChannel_le_certified_halfTime a b c ⟨Real.exp τ, Real.exp_pos τ⟩)
    (by positivity)

/-- Every diagonal and all three mixed coefficient terms remain in the complete form. -/
theorem exists_xiHeatThirdQuadratic_allTime_certifiedPhase_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ L : ℝ, 32 < L ∧
      ∀ (a b c : ℝ) (t : {t : ℝ // 0 < t}),
        (c₀ * Real.exp (-(L * (t : ℝ))) -
          Real.exp (-((t : ℝ) / 2 * xiGaussianCertifiedPhaseGap)) *
            xiGaussianCoefficientAnchorAt 3 (xiGaussianHalfHeat t)) *
              (a ^ 2 + b ^ 2 + c ^ 2) ≤ xiHeatThirdQuadratic a b c t := by
  obtain ⟨c₀, hc₀, L, hL, hbound⟩ := exists_xiHeatHankelForm_allTime_certifiedPhase_lower 3
  refine ⟨c₀, hc₀, L, hL, ?_⟩
  intro a b c t
  rw [xiHeatThirdQuadratic_eq_hankel]
  simpa [Finset.sum_range_succ] using
    hbound (fun n => if n = 0 then a else if n = 1 then b else c) t

end RHTower
