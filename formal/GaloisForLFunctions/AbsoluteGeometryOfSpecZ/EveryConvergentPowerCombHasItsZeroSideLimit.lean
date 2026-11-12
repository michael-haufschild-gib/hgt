import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerContactLimitsAreForced
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailArchimedeanMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailReferenceMellinIntegral
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroPairing
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorSymbolSplitsAtTheZeros

/-!
# Every convergent power comb has its zero-side limit

The real boundary residue fixes the leading prime-contact coefficient.
After the reference and archimedean terms are restored, the only possible
limit is the reflected zero pairing. This includes a convergence endpoint
at which the supremum of zero depths need not be attained.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Convergence alone identifies the literal power comb's limit; a strict
gap from the actual zero width is unnecessary. -/
theorem tendsto_powerCombTail_zeroPairing_of_converges
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) (hc : PowerCombTailConverges a) :
    Tendsto (fun N => (powerCombTail a N : ℂ)) atTop (𝓝 (powerTailZeroPairing a)) := by
  obtain ⟨L, hL⟩ :=
    (powerCombTailConverges_iff_normalizedPowerContacts_converges ha ha2).mp hc
  let K := powerTailArchimedeanRowLimit a / (1 - 2 * a) - 2 * L -
    2 * (∫ t in Set.Ioc (0 : ℝ) 1, powerTailReferenceProfile a t)
  have hk := (((tendsto_normalized_powerTailArchimedean ha ha2).sub (hL.const_mul 2)).sub
    ((riemannOn_powerTailReferenceProfile ha ha2).2.const_mul 2)).add
      (tendsto_powerTailCombRemainder ha ha2)
  rw [add_zero] at hk
  have hT : Tendsto (powerCombTail a) atTop (𝓝 K) := by
    apply hk.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (powerCombTail_eq_mellin_meshes a hN).symm
  have ha1 : a < 1 := by linarith only [ha2]
  have hθ : 1 - 2 * (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - 2 * a ≠ 0 by linarith only [ha2])
  have hθ' : 1 - (a : ℂ) * 2 ≠ 0 := by simpa only [mul_comm] using hθ
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hs0 : 1 - (a : ℂ) ≠ 0 := by
    exact_mod_cast (show (1 : ℝ) - a ≠ 0 by linarith only [ha1])
  have hs1 : 1 - (a : ℂ) ≠ 1 := by
    intro h
    exact ha0 (by linear_combination -h)
  have hre : 0 < (1 - (a : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith only [ha1]
  have hζ : riemannZeta (1 - (a : ℂ)) ≠ 0 := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
      RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo
        (show 0 < 1 - a by linarith only [ha2]) (show 1 - a < 1 by linarith only [ha])
  have hxi := ArithmeticCorrespondencePositivity.logDeriv_xi_eq_add hre hs1 hζ
  have hpoles : ∀ n : ℕ, (1 - (a : ℂ)) / 2 ≠ -(n : ℂ) := by
    intro n h
    have hh := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re,
      Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hh
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [ha1, hh, hn]
  rw [BohrGeneratorAxis.logDeriv_GammaR _ hpoles] at hxi
  conv_rhs at hxi => rw [logDeriv_apply]
  have hprime := normalizedPowerContacts_limit_coefficient ha ha2 hL
  have href := mul_referencePowerMellinIntegral_eq ha ha2
  have harch := ofReal_powerTailArchimedeanRowLimit ha ha1
  have hsplit : (1 - 2 * (a : ℂ)) * (K : ℂ) =
      (powerTailArchimedeanRowLimit a : ℂ) - 2 * ((1 - 2 * (a : ℂ)) * (L : ℂ)) -
        2 * ((1 - 2 * (a : ℂ)) *
          ((∫ t in Set.Ioc (0 : ℝ) 1, powerTailReferenceProfile a t : ℝ) : ℂ)) := by
    dsimp only [K]
    push_cast
    field_simp [hθ, hθ']
  rw [hprime, href, harch] at hsplit
  have hmain : (1 - 2 * (a : ℂ)) * (K : ℂ) =
      2 * logDeriv _root_.RHTower.xi (1 - (a : ℂ)) := by
    rw [hsplit, hxi]
    have hsub : 1 - (a : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [ha0, hs0, hsub, hζ]
    ring
  have hK : (K : ℂ) = powerTailZeroPairing a := by
    apply mul_left_cancel₀ hθ
    rw [powerTailZeroPairing_eq_logDeriv ha2, hmain]
    field_simp [hθ, hθ']
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hT
  rw [hK] at hcomplex
  exact hcomplex.congr fun _ => rfl

/-- The reflected zero pairing is the unique possible convergence value
throughout the positive subcritical parameter range. -/
theorem powerCombTailConverges_iff_tendsto_zeroPairing
    {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    PowerCombTailConverges a ↔
      Tendsto (fun N => (powerCombTail a N : ℂ)) atTop (𝓝 (powerTailZeroPairing a)) := by
  constructor
  · exact tendsto_powerCombTail_zeroPairing_of_converges ha ha2
  · intro h
    refine ⟨(powerTailZeroPairing a).re, ?_⟩
    have hr := Complex.continuous_re.continuousAt.tendsto.comp h
    exact hr.congr fun _ => by simp only [Function.comp_apply, Complex.ofReal_re]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
