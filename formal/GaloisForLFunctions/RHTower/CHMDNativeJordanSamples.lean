import GaloisForLFunctions.RHTower.PaperThetaCompactMeyerRealization
import GaloisForLFunctions.RHTower.PaperThetaNativeMomentIdentity
import GaloisForLFunctions.RHTower.PaperThetaCutTransform

/-!
# Exact Xi samples of the original native Jordan chains

The actual theta-weighted transform of a native divisor jet has denominator
`(w-a)^(j+1)`. The removable value at its own root is zero below the terminal
layer and nonzero at the terminal layer, with no simplicity assumption.
Consequently, the Xi-sample kernel of every finite original packet is exactly
its lower Jordan layers.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BoundedContinuousFunction Classical

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource

theorem differentiable_boundedThetaMoment (f : NativeContinuousSpace) :
    Differentiable ℂ (fun w => boundedThetaMomentCLM w f) :=
  differentiable_bounded_thetaTransform f.continuous.aestronglyMeasurable f.norm_coe_le_norm

theorem nativeThetaDivisorJet_moment_zero_equation (rho : XiDivisorSupport) (w : ℂ) :
    (w-xiSpectralPointSupport rho) * boundedThetaMomentCLM w
      (nativeThetaDivisorJet rho ⟨0, xiSupportMultiplicity_pos rho⟩) =
      -w * flatConnection w := by
  let f := nativeThetaDivisorJet rho ⟨0, xiSupportMultiplicity_pos rho⟩
  have h := boundedThetaMoment_source_equation w f
    ((xiSpectralPointSupport rho-w) • f) (-1)
    (differentiable_flatParameterJet 0 (xiSpectralPointSupport rho)) (fun x => by
      have he := flatQuotient_source_equation (xiSpectralPointSupport rho) x
      change deriv (flatQuotient (xiSpectralPointSupport rho)) x +
        sourceLogDerivative x * (flatQuotient (xiSpectralPointSupport rho) x - (-1)) +
        I*w*flatQuotient (xiSpectralPointSupport rho) x =
        -I*((xiSpectralPointSupport rho-w)*flatQuotient (xiSpectralPointSupport rho) x)
      linear_combination he)
  rw [map_smul] at h
  change (xiSpectralPointSupport rho-w)*boundedThetaMomentCLM w f+
    w*(-1)*flatConnection w = 0 at h
  dsimp only [f] at h
  linear_combination -h

theorem nativeThetaDivisorJet_moment_succ_equation (rho : XiDivisorSupport)
    (n : ℕ) (hn : n+1 < xiSupportMultiplicity rho) (w : ℂ) :
    (w-xiSpectralPointSupport rho) * boundedThetaMomentCLM w
      (nativeThetaDivisorJet rho ⟨n+1, hn⟩) =
      ((n : ℂ)+1) * boundedThetaMomentCLM w
        (nativeThetaDivisorJet rho ⟨n, by omega⟩) := by
  let f := nativeThetaDivisorJet rho ⟨n+1, hn⟩
  let p := nativeThetaDivisorJet rho ⟨n, by omega⟩
  have h := boundedThetaMoment_source_equation w f
    ((xiSpectralPointSupport rho-w) • f+((n : ℂ)+1) • p) 0
    (differentiable_flatParameterJet (n+1) (xiSpectralPointSupport rho)) (fun x => by
      have he := flatParameterJet_succ_source_equation n (xiSpectralPointSupport rho) x
      change deriv (flatParameterJet (n+1) (xiSpectralPointSupport rho)) x +
        sourceLogDerivative x * (flatParameterJet (n+1) (xiSpectralPointSupport rho) x-0) +
        I*w*flatParameterJet (n+1) (xiSpectralPointSupport rho) x =
        -I*((xiSpectralPointSupport rho-w)*flatParameterJet (n+1) (xiSpectralPointSupport rho) x+
          ((n : ℂ)+1)*flatParameterJet n (xiSpectralPointSupport rho) x)
      linear_combination he)
  simp only [map_add, map_smul, smul_eq_mul, mul_zero, zero_mul, add_zero] at h
  dsimp only [f, p] at h
  linear_combination -h

/-- The literal transform identity includes its removable value at the root. -/
theorem nativeThetaDivisorJet_moment_power (rho : XiDivisorSupport)
    (n : ℕ) (hn : n < xiSupportMultiplicity rho) (w : ℂ) :
    (w-xiSpectralPointSupport rho)^(n+1) * boundedThetaMomentCLM w
      (nativeThetaDivisorJet rho ⟨n, hn⟩) = -(n.factorial : ℂ)*w*flatConnection w := by
  induction n with
  | zero => simpa using nativeThetaDivisorJet_moment_zero_equation rho w
  | succ n ih =>
      have hn' : n < xiSupportMultiplicity rho := by omega
      calc
        _ = (w-xiSpectralPointSupport rho)^(n+1) *
            ((w-xiSpectralPointSupport rho)*boundedThetaMomentCLM w
              (nativeThetaDivisorJet rho ⟨n+1, hn⟩)) := by ring
        _ = (w-xiSpectralPointSupport rho)^(n+1) *
            (((n : ℂ)+1)*boundedThetaMomentCLM w
              (nativeThetaDivisorJet rho ⟨n, hn'⟩)) := by
          rw [nativeThetaDivisorJet_moment_succ_equation rho n hn]
        _ = ((n : ℂ)+1)*((w-xiSpectralPointSupport rho)^(n+1) *
            boundedThetaMomentCLM w (nativeThetaDivisorJet rho ⟨n, hn'⟩)) := by ring
        _ = _ := by rw [ih hn', Nat.factorial_succ]; push_cast; ring

theorem nativeThetaDivisorJet_moment_other (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) {w : ℂ} (hw : XiC w = 0)
    (hwa : w ≠ xiSpectralPointSupport rho) :
    boundedThetaMomentCLM w (nativeThetaDivisorJet rho j) = 0 := by
  have he := nativeThetaDivisorJet_moment_power rho j.val j.isLt w
  rw [flatConnection_eq_all, hw, zero_div, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hwa))

theorem nativeThetaDivisorJet_moment_lower (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (hj : j.val+1 < xiSupportMultiplicity rho) :
    boundedThetaMomentCLM (xiSpectralPointSupport rho) (nativeThetaDivisorJet rho j) = 0 := by
  have he := nativeThetaDivisorJet_moment_succ_equation rho j.val hj (xiSpectralPointSupport rho)
  rw [sub_self, zero_mul] at he
  have hn : (j.val : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j.val
  exact (mul_eq_zero.mp he.symm).resolve_left hn

def nativeTerminalJetIndex (rho : XiDivisorSupport) : Fin (xiSupportMultiplicity rho) :=
  ⟨xiSupportMultiplicity rho-1, by have := xiSupportMultiplicity_pos rho; omega⟩

def nativeTerminalSample (rho : XiDivisorSupport) : ℂ :=
  boundedThetaMomentCLM (xiSpectralPointSupport rho)
    (nativeThetaDivisorJet rho (nativeTerminalJetIndex rho))

/-- Exact multiplicity forces the surviving terminal sample to be nonzero. -/
theorem nativeTerminalSample_ne_zero (rho : XiDivisorSupport) : nativeTerminalSample rho ≠ 0 := by
  let a := xiSpectralPointSupport rho
  let m := xiSupportMultiplicity rho
  let j := nativeTerminalJetIndex rho
  have ha0 : a ≠ 0 := by
    have hz := XiC_xiSpectralPoint_eq_zero
      (⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩ : XiZeroCopy)
    intro ha
    change XiC a = 0 at hz
    rw [ha] at hz
    exact XiC_zero_ne hz
  have hj : j.val+1 = m := by dsimp [j, nativeTerminalJetIndex, m]; have := xiSupportMultiplicity_pos rho; omega
  obtain ⟨G, hG, hG0, hfac⟩ :=
    (XiC_differentiable.analyticAt a).analyticOrderAt_eq_natCast.mp
      (XiC_analyticOrderAt_support rho)
  let M : ℂ → ℂ := fun w => boundedThetaMomentCLM w (nativeThetaDivisorJet rho j)
  let V : ℂ → ℂ := fun w => -(j.val.factorial : ℂ)*w*G w/(thetaSource.mass : ℂ)
  have he : M =ᶠ[𝓝[≠] a] V := by
    filter_upwards [hfac.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwa
    have hwa' : w-a ≠ 0 := sub_ne_zero.mpr hwa
    have hpow := nativeThetaDivisorJet_moment_power rho j.val j.isLt w
    rw [hj, flatConnection_eq_all, hw] at hpow
    change (w-a)^m*M w = -(j.val.factorial : ℂ)*w*((w-a)^m*G w/(thetaSource.mass : ℂ)) at hpow
    apply mul_left_cancel₀ (pow_ne_zero m hwa')
    change (w-a)^m*M w = (w-a)^m*V w
    rw [hpow]
    dsimp [V]
    ring
  have hM : ContinuousAt M a := (differentiable_boundedThetaMoment _).continuous.continuousAt
  have hV : ContinuousAt V a := ((continuousAt_const.mul continuousAt_id).mul hG.continuousAt).div_const _
  have hval : M a = V a := tendsto_nhds_unique
    (hM.tendsto.mono_left nhdsWithin_le_nhds)
    ((hV.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  change M a ≠ 0
  rw [hval]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast Nat.factorial_ne_zero j.val)) ha0) hG0)
    (Complex.ofReal_ne_zero.mpr thetaSource.mass_ne_zero)

theorem nativeThetaDivisorJet_moment_at_self (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) :
    boundedThetaMomentCLM (xiSpectralPointSupport rho) (nativeThetaDivisorJet rho j) =
      if j = nativeTerminalJetIndex rho then nativeTerminalSample rho else 0 := by
  split_ifs with h
  · subst j; rfl
  · apply nativeThetaDivisorJet_moment_lower
    have hj := j.isLt
    have hn : j.val ≠ xiSupportMultiplicity rho-1 := by
      intro he
      exact h (Fin.ext he)
    omega

theorem nativeThetaDivisorJet_moment_zero_of_nonterminal (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (hj : j ≠ nativeTerminalJetIndex rho)
    {w : ℂ} (hw : XiC w = 0) :
    boundedThetaMomentCLM w (nativeThetaDivisorJet rho j) = 0 := by
  by_cases hwa : w = xiSpectralPointSupport rho
  · rw [hwa, nativeThetaDivisorJet_moment_at_self, if_neg hj]
  · exact nativeThetaDivisorJet_moment_other rho j hw hwa

def nativeTerminalWeight (rho : XiDivisorSupport) : ℂ :=
  ((nativeTerminalJetIndex rho).val.factorial : ℂ)⁻¹ * nativeTerminalSample rho

theorem nativeTerminalWeight_ne_zero (rho : XiDivisorSupport) : nativeTerminalWeight rho ≠ 0 :=
  mul_ne_zero (inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (nativeTerminalJetIndex rho).val))
    (nativeTerminalSample_ne_zero rho)

/-- Each actual finite packet has one surviving Xi sample per root. -/
theorem nativeFiniteSynthesis_sample (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) (rho : ↥S) :
    boundedThetaMomentCLM (xiSpectralPointSupport rho.val) (nativeFiniteSynthesis S c) =
      c ⟨rho, nativeTerminalJetIndex rho.val⟩ * nativeTerminalWeight rho.val := by
  let q0 : DeningerMeyerFiniteXiJetSlot S := ⟨rho, nativeTerminalJetIndex rho.val⟩
  rw [nativeFiniteSynthesis, Fintype.linearCombination_apply, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hs : (∑ q : DeningerMeyerFiniteXiJetSlot S,
      c q * ((q.2.val.factorial : ℂ)⁻¹ *
        boundedThetaMomentCLM (xiSpectralPointSupport rho.val) (nativeThetaDivisorJet q.1.val q.2))) =
      c q0 * ((q0.2.val.factorial : ℂ)⁻¹ *
        boundedThetaMomentCLM (xiSpectralPointSupport rho.val) (nativeThetaDivisorJet q0.1.val q0.2)) := by
    apply Finset.sum_eq_single q0
    · rintro ⟨tau, j⟩ _ hq
      by_cases ht : tau = rho
      · subst tau
        have hj : j ≠ nativeTerminalJetIndex rho.val := by
          intro he
          exact hq (by cases he; rfl)
        rw [nativeThetaDivisorJet_moment_at_self, if_neg hj, mul_zero, mul_zero]
      · have hne : xiSpectralPointSupport rho.val ≠ xiSpectralPointSupport tau.val := by
          intro he
          exact ht (Subtype.ext (xiSpectralPointSupport_injective he.symm))
        have hz : XiC (xiSpectralPointSupport rho.val) = 0 :=
          XiC_xiSpectralPoint_eq_zero ⟨rho.val, ⟨0, xiSupportMultiplicity_pos rho.val⟩⟩
        rw [nativeThetaDivisorJet_moment_other tau.val j hz hne, mul_zero, mul_zero]
    · simp
  exact hs

/-- The full Xi-sample kernel consists exactly of the lower Jordan coefficients. -/
theorem nativeFiniteSynthesis_Xi_silent_iff_terminal_zero (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    (∀ w : ℂ, XiC w = 0 → boundedThetaMomentCLM w (nativeFiniteSynthesis S c) = 0) ↔
      ∀ rho : ↥S, c ⟨rho, nativeTerminalJetIndex rho.val⟩ = 0 := by
  constructor
  · intro h rho
    have hz : XiC (xiSpectralPointSupport rho.val) = 0 :=
      XiC_xiSpectralPoint_eq_zero ⟨rho.val, ⟨0, xiSupportMultiplicity_pos rho.val⟩⟩
    have he := h _ hz
    rw [nativeFiniteSynthesis_sample] at he
    exact (mul_eq_zero.mp he).resolve_right (nativeTerminalWeight_ne_zero rho.val)
  · intro h w hw
    rw [nativeFiniteSynthesis, Fintype.linearCombination_apply, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    apply Finset.sum_eq_zero
    rintro ⟨rho, j⟩ _
    by_cases hj : j = nativeTerminalJetIndex rho.val
    · subst j
      rw [h rho, zero_mul]
    · rw [nativeThetaDivisorJet_moment_zero_of_nonterminal rho.val j hj hw, mul_zero, mul_zero]

end RHTower.PaperThetaEndpoint
