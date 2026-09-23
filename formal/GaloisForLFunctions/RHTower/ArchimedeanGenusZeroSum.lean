import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The archimedean genus is the regularised count of the zeros

The prime-side constant of the exponential-pole self-energy, `2 + γ − log 4π`, equals the
zero-side sum `Σ_ρ 1/(ρ(1−ρ))` over the nontrivial zeros of `ξ` counted with multiplicity:

* `completedRiemannZeta₀ 1 = 1 + (γ − log 4π)/2` from Mathlib's limit of
  `ζ(s) − 1/(Γℝ(s)(s−1))` at `s = 1`; this is the first Li coefficient `λ₁ = ξ'(1)/ξ(1)`;
* the Hadamard product `XiC = XiC(0)·Π_q E₁(z/t_q)` over the multiplicity copies `t_q` of the
  zeros gives `logDeriv XiC z = Σ_q [(z − t_q)⁻¹ + t_q⁻¹]`, and the point `z = −I/2` is `s = 1`;
* reflection `t_q ↦ −t_q` (the functional equation) pairs the terms into `I/(¼ + t_q²)`, and
  `¼ + t_q² = ρ_q(1 − ρ_q)`.

Hence `Σ'_q 1/(ρ_q(1−ρ_q)) = 2λ₁ = 2 + γ − log 4π`, the constant of `PoleBoundaryLogSharpConstant`.
No RH premise enters: the zeros are the actual divisor of `ξ`.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- `Λ₀(1) = 1 + (γ − log 4π)/2`: the first Li coefficient. -/
theorem completedRiemannZeta₀_one :
    completedRiemannZeta₀ 1 =
      1 + ((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 := by
  have h1 : Tendsto (fun s : ℂ => (completedRiemannZeta₀ s - 1 / s) / Gammaℝ s) (𝓝[≠] 1)
      (𝓝 ((completedRiemannZeta₀ 1 - 1 / 1) / Gammaℝ 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Tendsto.div
    · exact (differentiable_completedZeta₀.continuous.tendsto 1).sub
        (tendsto_const_nhds.div tendsto_id one_ne_zero)
    · exact Complex.hasDerivAt_Gammaℝ_one.continuousAt.tendsto
    · rw [Complex.Gammaℝ_one]
      exact one_ne_zero
  have h2 : Tendsto (fun s : ℂ => (completedRiemannZeta₀ s - 1 / s) / Gammaℝ s) (𝓝[≠] 1)
      (𝓝 (((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2)) := by
    refine ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ.congr' ?_
    have hopen : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) := by
      apply (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
      simp
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hopen, self_mem_nhdsWithin]
      with s hs hs1
    have hs1' : s ≠ 1 := hs1
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      exact absurd hs (by norm_num)
    have hG : Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1'
    have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1')
    rw [riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
    field_simp
    ring
  have := tendsto_nhds_unique h1 h2
  rw [Complex.Gammaℝ_one, div_one, div_one] at this
  linear_combination this

theorem hasDerivAt_xi_one_archimedeanGenusZeroSum : HasDerivAt xi (completedRiemannZeta₀ 1 / 2) 1 := by
  have h1 : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) ((1 * (1 - 1) + 1 * 1) / 2) 1 := by
    have := ((hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).div_const 2
    simpa using this
  have h2 := (differentiable_completedZeta₀ 1).hasDerivAt
  have h3 := (h1.mul h2).add_const (1 / 2 : ℂ)
  have key : xi = fun s : ℂ => s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2 := rfl
  rw [key]
  refine h3.congr_deriv ?_
  ring

/-- The `XiC`-coordinate of `s = 1` is `z = −I/2`. -/
theorem half_add_neg_I_half_mul_I : (1 / 2 : ℂ) + (-I / 2) * I = 1 := by
  linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I

theorem half_add_I_half_mul_I : (1 / 2 : ℂ) + I / 2 * I = 0 := by
  linear_combination (1 / 2 : ℂ) * Complex.I_mul_I

theorem XiC_neg_I_half : XiC (-I / 2) = 1 / 2 := by
  unfold XiC
  rw [half_add_neg_I_half_mul_I, xi_one]

theorem XiC_I_half : XiC (I / 2) = 1 / 2 := by
  unfold XiC
  rw [half_add_I_half_mul_I, xi_zero]

/-- `logDeriv XiC (−I/2) = I · Λ₀(1)`. -/
theorem logDeriv_XiC_neg_I_half : logDeriv XiC (-I / 2) = I * completedRiemannZeta₀ 1 := by
  have hg : HasDerivAt (fun z : ℂ => 1 / 2 + z * I) I (-I / 2) := by
    simpa using ((hasDerivAt_id (-I / 2 : ℂ)).mul_const I).const_add (1 / 2 : ℂ)
  have hxi : HasDerivAt xi (completedRiemannZeta₀ 1 / 2)
      ((fun z : ℂ => 1 / 2 + z * I) (-I / 2)) := by
    simp only [half_add_neg_I_half_mul_I]
    exact hasDerivAt_xi_one_archimedeanGenusZeroSum
  have hd : HasDerivAt XiC (completedRiemannZeta₀ 1 / 2 * I) (-I / 2) := hxi.comp (-I / 2) hg
  rw [logDeriv_apply, hd.deriv, XiC_neg_I_half]
  field_simp

/-- No zero copy sits at the `XiC`-coordinate of `s = 1`. -/
theorem neg_I_half_ne_xiSpectralPoint (q : XiZeroCopy) : (-I / 2 : ℂ) ≠ xiSpectralPoint q := by
  intro h
  have := XiC_xiSpectralPoint_eq_zero q
  rw [← h, XiC_neg_I_half] at this
  norm_num at this

/-- No zero copy sits at the `XiC`-coordinate of `s = 0`. -/
theorem I_half_ne_xiSpectralPoint (q : XiZeroCopy) : (I / 2 : ℂ) ≠ xiSpectralPoint q := by
  intro h
  have := XiC_xiSpectralPoint_eq_zero q
  rw [← h, XiC_I_half] at this
  norm_num at this

/-- `ρ_q = ½ + t_q I`. -/
theorem xiZeroCopy_eq_half_add (q : XiZeroCopy) :
    (q.1 : ℂ) = 1 / 2 + xiSpectralPoint q * I := by
  rw [xiSpectralPoint]
  linear_combination ((q.1 : ℂ) - 1 / 2) * Complex.I_mul_I

theorem pair_inv_add_inv {z t : ℂ} (h1 : z - t ≠ 0) (h2 : z + t ≠ 0) :
    (z - t)⁻¹ + (z + t)⁻¹ = 2 * z / (z ^ (2 : ℕ) - t ^ (2 : ℕ)) := by
  have h3 : z ^ (2 : ℕ) - t ^ (2 : ℕ) ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero h2 h1
  field_simp
  ring

theorem neg_I_half_sq : (-I / 2 : ℂ) ^ (2 : ℕ) = -1 / 4 := by
  rw [div_pow, neg_sq, Complex.I_sq]
  norm_num

/-- Reflection symmetrisation of the Mittag-Leffler sum at `z = −I/2`. -/
theorem tsum_logDerivTerm_eq :
    (∑' q : XiZeroCopy, ((-I / 2 - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹)) =
      I / 2 * ∑' q : XiZeroCopy, (1 : ℂ) / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ)) := by
  obtain ⟨f, hf⟩ : ∃ f : XiZeroCopy → ℂ,
      f = fun q => (-I / 2 - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹ := ⟨_, rfl⟩
  have hsumm : Summable f := by
    have := summable_canonicalProductE1LogDerivTerm xiSpectralPoint_ne_zero
      xiSpectralPoint_inv_sq_summable neg_I_half_ne_xiSpectralPoint
    refine this.neg.congr fun q => ?_
    simp only [hf]
    rw [show xiSpectralPoint q - (-I / 2) = -(-I / 2 - xiSpectralPoint q) by ring, inv_neg]
    ring
  have hσ : Summable (f ∘ xiZeroCopyReflectEquiv) :=
    (xiZeroCopyReflectEquiv.summable_iff).mpr hsumm
  have hpair : ∀ q, f q + (f ∘ xiZeroCopyReflectEquiv) q =
      I * (1 / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ))) := by
    intro q
    simp only [hf, Function.comp_def, xiSpectralPoint_reflect]
    have h1 : -I / 2 - xiSpectralPoint q ≠ 0 :=
      sub_ne_zero.mpr (neg_I_half_ne_xiSpectralPoint q)
    have h2 : -I / 2 + xiSpectralPoint q ≠ 0 := by
      intro h
      apply I_half_ne_xiSpectralPoint q
      linear_combination -h
    have h3 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hden : (1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
      have : (1 / 4 : ℂ) + xiSpectralPoint q ^ (2 : ℕ) = -((-I / 2) ^ (2 : ℕ) - xiSpectralPoint q ^ (2 : ℕ)) := by
        rw [neg_I_half_sq]
        ring
      rw [this, neg_ne_zero, sub_ne_zero]
      intro h
      have : (-I / 2 - xiSpectralPoint q) * (-I / 2 + xiSpectralPoint q) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h1 h'
      · exact h2 h'
    have e1 : (-I / 2 - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹ +
        ((-I / 2 - -xiSpectralPoint q)⁻¹ + (-xiSpectralPoint q)⁻¹) =
        (-I / 2 - xiSpectralPoint q)⁻¹ + (-I / 2 + xiSpectralPoint q)⁻¹ := by
      rw [sub_neg_eq_add, inv_neg]
      ring
    have hden' : (-1 / 4 : ℂ) - xiSpectralPoint q ^ (2 : ℕ) ≠ 0 := by
      intro h
      apply hden
      linear_combination -h
    rw [e1, pair_inv_add_inv h1 h2, neg_I_half_sq, mul_one_div, div_eq_div_iff hden' hden]
    ring
  have hsym : ∑' q, f q = ∑' q, (f ∘ xiZeroCopyReflectEquiv) q :=
    (Equiv.tsum_eq xiZeroCopyReflectEquiv f).symm
  have hadd : ∑' q, f q + ∑' q, (f ∘ xiZeroCopyReflectEquiv) q =
      ∑' q, (f q + (f ∘ xiZeroCopyReflectEquiv) q) := (hsumm.tsum_add hσ).symm
  rw [← hsym] at hadd
  simp_rw [hpair, tsum_mul_left] at hadd
  rw [hf] at hadd
  linear_combination (1 / 2 : ℂ) * hadd

/-- **The archimedean genus is the regularised zero count.** -/
theorem tsum_inv_zero_mul_one_sub_zero :
    (∑' q : XiZeroCopy, (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) = (poleSharpConstant : ℂ) := by
  have hL : logDeriv XiC (-I / 2) =
      ∑' q, ((-I / 2 - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹) := by
    rw [XiC_eq_constant_mul_canonicalProduct]
    rw [show ((fun _ => XiC 0) * xiCanonicalProduct) = fun z => XiC 0 * xiCanonicalProduct z from
      rfl]
    rw [logDeriv_const_mul _ _ XiC_zero_ne]
    exact logDeriv_canonicalProductE1Indexed xiSpectralPoint_ne_zero
      xiSpectralPoint_inv_sq_summable neg_I_half_ne_xiSpectralPoint
  rw [logDeriv_XiC_neg_I_half, tsum_logDerivTerm_eq] at hL
  have hterm : ∀ q : XiZeroCopy, (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      1 / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ)) := by
    intro q
    rw [xiZeroCopy_eq_half_add q]
    congr 1
    linear_combination (-(xiSpectralPoint q ^ (2 : ℕ))) * Complex.I_mul_I
  simp_rw [hterm]
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hS : (∑' q : XiZeroCopy, (1 : ℂ) / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ))) =
      2 * completedRiemannZeta₀ 1 := by
    apply mul_left_cancel₀ hI
    calc I * ∑' q : XiZeroCopy, (1 : ℂ) / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ))
        = 2 * (I / 2 * ∑' q : XiZeroCopy, (1 : ℂ) / (1 / 4 + xiSpectralPoint q ^ (2 : ℕ))) := by ring
      _ = 2 * (I * completedRiemannZeta₀ 1) := by rw [hL]
      _ = I * (2 * completedRiemannZeta₀ 1) := by ring
  rw [hS, completedRiemannZeta₀_one]
  unfold poleSharpConstant
  push_cast
  rw [Complex.ofReal_log (by positivity : (0 : ℝ) ≤ 4 * Real.pi)]
  push_cast
  ring

/-- Real form: `Σ_ρ 1/(ρ(1−ρ))` is real and equals `2 + γ − log 4π`. -/
theorem tsum_inv_zero_mul_one_sub_zero_re :
    (∑' q : XiZeroCopy, (1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re = poleSharpConstant := by
  rw [tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re]

end

end RHTower
