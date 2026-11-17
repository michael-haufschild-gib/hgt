import GaloisForLFunctions.OrderSixMetaplecticTheory.TheSexticTwistAndTheQuadraticTwistShareTheDoublePole

/-!
# The residue of the quadratic relation is a theta period

A bounded remainder `G` (`RemainderData`) has at most a simple pole at `4/3`; its residue is the pairing of
`G` with the residue vector `θ_{res}` of the cubic Eisenstein series (`RemainderData.pairing_residue`):

`(s − 4/3) ∫_{D_Γ} G E(s) → ⟨G, θ_{res}⟩`.

For the quadratic fractional trace `Tr G_λ` this is the main term of the quadratic grade at `q`
(`sexticTwist_residue`):

`(s − 4/3) M(s)(g_λJ₆λ(2)L_λ(s) + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ}(s)) → |P|⁻¹⟨Tr G_λ, θ_{res}⟩`,

a triple theta period `Σ_tλ(t)⟨θ(T_t·)θ(T_{−t}·), θ_{res}⟩` on `Γ(3) ∩ Γ₀(q²)`. The traces fix the double poles of the
quadratic grade up to one relation; its simple pole is this number.
-/

noncomputable section

open MeasureTheory Filter Function
open scoped BigOperators Classical Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace RemainderData

variable {G : HyperbolicSpace → ℂ} (hG : RemainderData G)
include hG

/-- **The residue of a bounded remainder is its period against the Eisenstein residue vector.** -/
theorem pairing_residue :
    Tendsto (fun s => (s - 4 / 3) * hG.pairing s) (𝓝[≠] (4 / 3 : ℂ))
      (𝓝 (levelPairing G hG.memLp cubicEisensteinResidue)) := by
  obtain ⟨hN, hev, hval⟩ := levelPairing_correction_center G hG.memLp
  set N := fun s => levelPairing G hG.memLp (correctionNumerator s)
  have hseed := hG.remainderSeed_differentiableAt (4 / 3) (by norm_num) (by norm_num)
  set F : ℂ → ℂ := fun s => (s - 4 / 3) * remainderSeed G s + N s with hFdef
  have hFc : ContinuousAt F (4 / 3) :=
    (((continuous_id.sub continuous_const).continuousAt).mul hseed.continuousAt).add hN.continuousAt
  have hF0 : F (4 / 3) = levelPairing G hG.memLp cubicEisensteinResidue := by
    simp only [hFdef, N, sub_self, zero_mul, zero_add, hval]
  rw [← hF0]
  refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev] with s hs
  simp only [hFdef, pairing, N]
  rw [mul_add, hs]

end RemainderData

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- **The main term of the quadratic grade is a theta period.** For every odd primary prime `q` the combination
`M(s)(g_λJ₆λ(2)L_λ(s) + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ}(s))` continues to a punctured neighbourhood of `4/3`
with at most a simple pole, whose residue is `|P|⁻¹⟨Tr G_λ, θ_{res}⟩`. -/
theorem sexticTwist_residue (h2 : (2 : P.Res) ≠ 0) :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * (P.quadFactor * besselDirichlet P.quadTwistCoeff s +
          P.sexticFactor s * besselDirichlet P.sexticTwistCoeff s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 ((periodArea : ℂ)⁻¹ * levelPairing P.sourceFracTraceW (P.sourceFracTraceW_remainderData h2).memLp
          cubicEisensteinResidue)) := by
  have hG := P.sourceFracTraceW_remainderData h2
  have hq : (periodArea : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne'
  refine ⟨fun s => periodArea⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show periodArea⁻¹ * hG.pairing s = _
    rw [← hG.pairing_eq s hs4 hs hi, P.integral_sourceFracTraceW_mul_eisenstein h2 s hs4 hs, inv_mul_cancel_left₀ hq,
      P.quadDirichlet_eq, P.sexticDirichlet_eq h2, quadFactor, sexticFactor]
    ring
  · exact (hG.pairing_differentiableAt s hs1 hs hi).const_mul _
  · filter_upwards [hG.pairing_near_four_thirds.1] with s h
    exact h.const_mul _
  · refine (hG.pairing_residue.const_mul (periodArea⁻¹ : ℂ)).congr' (Eventually.of_forall fun s => ?_)
    simp only
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
