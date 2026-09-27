import GaloisForLFunctions.RHTower.XiGaussianFinitePhaseRemainder
import GaloisForLFunctions.RHTower.XiHeatFiniteUniformPositivity

/-!
# Actual imaginary-channel tails and their small-time relative control

The complete imaginary channel is half the phase debt. Its tail is bounded
both by the full imaginary channel and by the positive norm tail. These two
bounds permit different estimates near zero and away from zero heat time.
-/

open scoped Real BigOperators
open Filter Topology Complex
noncomputable section

namespace RHTower

def xiGaussianTailPhaseEnergy (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) (R : ℝ) : ℝ :=
  ∑' q : {q : XiZeroCopy // R < (xiSpectralPoint q ^ 2).re},
    xiGaussianImaginaryChannelAtom Q t q.1

theorem xiGaussianTailPhaseEnergy_le_energy (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianTailPhaseEnergy Q t R ≤ xiGaussianTailEnergy Q t R := by
  exact Summable.tsum_le_tsum (fun q => xiGaussianImaginaryChannelAtom_le_norm Q t q.1)
    ((summable_xiGaussianImaginaryChannelAtom Q t).subtype _)
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property Q).subtype _)

theorem xiGaussianTailPhaseEnergy_le_full (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiGaussianTailPhaseEnergy Q t R ≤ ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q :=
  Summable.tsum_subtype_le _ _ (xiGaussianImaginaryChannelAtom_nonneg Q t)
    (summable_xiGaussianImaginaryChannelAtom Q t)

theorem xiGaussianTrace_eq_realChannel_sub_imaginary (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiPolynomialGaussianHeatTraceReal Q t = xiGaussianRealChannelEnergy Q t -
      ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom Q t q := by
  have hs := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hre := (Complex.hasSum_re hs.hasSum).summable
  rw [xiGaussianRealChannelEnergy_eq_half_energy_add_trace]
  simp only [xiGaussianImaginaryChannelAtom, tsum_div_const, hs.norm.tsum_sub hre]
  rw [← Complex.re_tsum hs]
  change xiPolynomialGaussianHeatTraceReal Q t =
    (_ + xiPolynomialGaussianHeatTraceReal Q t) / 2 -
      (_ - xiPolynomialGaussianHeatTraceReal Q t) / 2
  ring

/-- Exact finite-head/tail phase split of the actual full trace. -/
theorem xiGaussianTrace_eq_realChannel_sub_head_sub_tailPhase (Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (R : ℝ) :
    xiPolynomialGaussianHeatTraceReal Q t = xiGaussianRealChannelEnergy Q t -
      xiGaussianHeadPhaseEnergy Q t R - xiGaussianTailPhaseEnergy Q t R := by
  classical
  have h := (summable_xiGaussianImaginaryChannelAtom Q t).sum_add_tsum_compl
    (s := (finite_xiHeatShell R).toFinset)
  have hset : ((finite_xiHeatShell R).toFinset : Set XiZeroCopy)ᶜ =
      {q : XiZeroCopy | R < (xiSpectralPoint q ^ 2).re} := by
    ext q
    simp only [Set.mem_compl_iff, Finset.mem_coe, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_le]
  rw [hset] at h
  change xiGaussianHeadPhaseEnergy Q t R + xiGaussianTailPhaseEnergy Q t R = _ at h
  rw [xiGaussianTrace_eq_realChannel_sub_imaginary, ← h]
  ring

/-- Exact identification with the existing finite-degree phase-debt budget. -/
theorem xiGaussianImaginaryChannel_finitePolynomial {N : ℕ} (a : Fin N → ℝ) (τ : ℝ) :
    (∑' q : XiZeroCopy,
      xiGaussianImaginaryChannelAtom (xiHeatFinitePolynomial a τ) (Real.exp τ) q) =
        xiHeatFinitePhaseDebt a τ / 2 := by
  have hp (q : XiZeroCopy) :
      xiGaussianImaginaryChannelAtom (xiHeatFinitePolynomial a τ) (Real.exp τ) q =
        (xiHeatFiniteAmplitude a τ q).im ^ 2 := by
    rw [xiGaussianImaginaryChannelAtom, ← xiHeatFiniteAmplitude_sq, norm_pow,
      Complex.sq_norm, Complex.normSq_apply, pow_two, Complex.mul_re]
    ring
  simp only [hp, xiHeatFinitePhaseDebt, xiHeatFiniteAmplitude_im]
  ring

theorem xiHeatFinitePolynomial_unscale (N : ℕ) (a : ℕ → ℝ) (τ : ℝ) :
    xiHeatFinitePolynomial (fun j : Fin N => a j / (Real.exp τ) ^ (j : ℕ)) τ =
      ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j := by
  unfold xiHeatFinitePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  simp only [xiHeatScaledCoefficients, dif_pos (Finset.mem_range.mp hj)]
  rw [div_mul_cancel₀ _ (pow_ne_zero j (Real.exp_pos τ).ne')]

/-- The full imaginary channel is relatively negligible at small time, uniformly in every
coefficient direction of a fixed finite order. -/
theorem eventually_xiGaussianImaginary_le_realChannel (N : ℕ) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ τ : ℝ in atBot, ∀ a : ℕ → ℝ,
      (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
        (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j) (Real.exp τ) q) ≤
          (ε : ℝ) * xiGaussianRealChannelEnergy
            (∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j)
            ⟨Real.exp τ, Real.exp_pos τ⟩ := by
  obtain ⟨η, hη, hfloor⟩ := xiHeatHankelForm_eventually_scaled_coercive N
  have hbudget := (xiHeatFinitePhaseBudget_tendsto_zero N).eventually_lt_const
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2) ε.property) hη)
  filter_upwards [hfloor, hbudget] with τ hf hb a
  let b : Fin N → ℝ := fun j => a j / (Real.exp τ) ^ (j : ℕ)
  let P := xiHeatFinitePolynomial b τ
  let t : {t : ℝ // 0 < t} := ⟨Real.exp τ, Real.exp_pos τ⟩
  have hH := hf b
  rw [← xiPolynomialGaussianHeatTraceReal_rangeSum (Real.exp_pos τ)] at hH
  change η * (∑ j, b j ^ 2) ≤ xiPolynomialGaussianHeatTraceReal P t at hH
  have hD := xiHeatFinitePhaseDebt_le_budget b τ
  have hA : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsmall := mul_le_mul_of_nonneg_left hb.le hA
  have hI := xiGaussianImaginaryChannel_finitePolynomial b τ
  change (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) = _ at hI
  have hIJ : xiPolynomialGaussianHeatTraceReal P t ≤ xiGaussianRealChannelEnergy P t := by
    rw [xiGaussianTrace_eq_realChannel_sub_imaginary]
    exact sub_le_self _ (tsum_nonneg (xiGaussianImaginaryChannelAtom_nonneg P t))
  have hmult := mul_le_mul_of_nonneg_left (hH.trans hIJ) ε.property.le
  have hfinal : (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) ≤
      (ε : ℝ) * xiGaussianRealChannelEnergy P t := by
    nlinarith only [hD, hsmall, hI, hmult]
  simpa only [P, b, xiHeatFinitePolynomial_unscale] using hfinal

end RHTower
