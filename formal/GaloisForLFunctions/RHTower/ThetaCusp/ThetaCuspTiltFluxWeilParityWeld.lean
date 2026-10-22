import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltFluxObservabilityWeld
import GaloisForLFunctions.RHTower.XiWeilTwoChannelResolvent
import GaloisForLFunctions.RHTower.GaussHodgeWeilFundamentalSymmetry

/-!
# Theta tilt flux is the two-channel Weil parity-energy deficit

This module welds three exact RH routes.  After the coefficient change
`d j = c j * xiCent (w j)`, the literal theta-source neutral tilt derivative equals the total
reflection-even divisor energy minus the total reflection-odd divisor energy of the canonical
even/odd resolvent channels.

Thus Euler-safe Cauchy observability, theta tilt flux, and the two-channel Weil polarization have
one common unresolved law: the reflection-odd projection must not increase energy on the linked
channel packet span.  The result is unconditional; the final theorem records that this domination
is exactly RH rather than assuming it.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Squared divisor-evaluation energy of the reflection-even part of a Weil test. -/
def xiWeilEvenEnergy (F : ℂ → ℂ) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiWeilEvenPart F (xiSpectralPoint q)‖ ^ (2 : ℕ)

/-- Squared divisor-evaluation energy of the reflection-odd part of a Weil test. -/
def xiWeilOddEnergy (F : ℂ → ℂ) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiWeilOddPart F (xiSpectralPoint q)‖ ^ (2 : ℕ)

/-- The Weil diagonal is exactly reflection-even energy minus reflection-odd energy. -/
theorem xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    {F : ℂ → ℂ} (hF : XiWeilSquareSummable F) :
    xiWeilPolarization F F =
      ((xiWeilEvenEnergy F - xiWeilOddEnergy F : ℝ) : ℂ) := by
  simpa only [xiWeilEvenEnergy, xiWeilOddEnergy] using
    xiWeilPolarization_self_eq_parity_energies hF

/-- Every finite packet of canonical `A` channels is square summable on the Xi divisor. -/
theorem xiWeilSquareSummable_channelPacketA {n : ℕ} (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    XiWeilSquareSummable (channelPacketA c w) := by
  have hbase : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilChannelA ((w j : ℂ))) :=
    fun j _ => xiWeilSquareSummable_channelA _
  change XiWeilSquareSummable
    (fun z => ∑ j, c j * weilChannelA ((w j : ℂ)) z)
  exact XiWeilSquareSummable.finsetSum hbase c

/-- Every finite packet of canonical `B` channels is square summable on the Xi divisor. -/
theorem xiWeilSquareSummable_channelPacketB {n : ℕ} (c : Fin n → ℂ)
    (w : Fin n → {W : ℂ // 1 / 2 < W.re}) :
    XiWeilSquareSummable (channelPacketB c w) := by
  have hbase : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      XiWeilSquareSummable (weilChannelB ((w j : ℂ))) :=
    fun j _ => xiWeilSquareSummable_channelB _
  change XiWeilSquareSummable
    (fun z => ∑ j, c j * weilChannelB ((w j : ℂ)) z)
  exact XiWeilSquareSummable.finsetSum hbase c

/-- The Euler-safe deficit is `π` times the two-channel Weil diagonal on the same packet. -/
theorem eulerSafeDeficit_eq_pi_mul_twoChannelWeil
    {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (d w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
      fun j => ⟨w j, lt_trans ha (hw j)⟩
    eulerSafeDeficit a d w =
      (Real.pi : ℂ) *
        (xiWeilPolarization (channelPacketA d w₀) (channelPacketA d w₀) +
          xiWeilPolarization (channelPacketB d w₀) (channelPacketB d w₀)) := by
  dsimp only
  let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
    fun j => ⟨w j, lt_trans ha (hw j)⟩
  have htwo := twoChannel_packet_eq_kernelEnergy d w₀
  rw [eulerSafeDeficit_eq ha d w hw, htwo, kernelEnergy]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [twoChannelKernel_eq]
  simp only [Complex.conj_conj, w₀]

/-- Real Euler-safe observability is `π` times total even-channel energy minus total odd-channel
energy. -/
theorem eulerSafeDeficit_re_eq_pi_mul_twoChannelParityDeficit
    {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (d w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
      fun j => ⟨w j, lt_trans ha (hw j)⟩
    (eulerSafeDeficit a d w).re = Real.pi *
      (xiWeilEvenEnergy (channelPacketA d w₀) +
          xiWeilEvenEnergy (channelPacketB d w₀) -
        (xiWeilOddEnergy (channelPacketA d w₀) +
          xiWeilOddEnergy (channelPacketB d w₀))) := by
  dsimp only
  let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
    fun j => ⟨w j, lt_trans ha (hw j)⟩
  have hEq := eulerSafeDeficit_eq_pi_mul_twoChannelWeil ha d w hw
  dsimp only at hEq
  have hA := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketA d w₀)
  have hB := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketB d w₀)
  rw [hA, hB] at hEq
  have hre := congrArg Complex.re hEq
  rw [Complex.re_ofReal_mul] at hre
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  nlinarith [hre]

/-- The literal theta-source tilt derivative is the two-channel reflection-parity deficit after
the invertible transform-value coefficient rescaling. -/
theorem tiltCorrelation_thetaCuspTiltSource_deriv_eq_twoChannelParityDeficit
    {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) {D : ℝ}
    (hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0) :
    let d : Fin n → ℂ := fun j => c j * xiCent (w j)
    let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
      fun j => ⟨w j, lt_trans ha (hw j)⟩
    D = xiWeilEvenEnergy (channelPacketA d w₀) +
          xiWeilEvenEnergy (channelPacketB d w₀) -
        (xiWeilOddEnergy (channelPacketA d w₀) +
          xiWeilOddEnergy (channelPacketB d w₀)) := by
  dsimp only
  let d : Fin n → ℂ := fun j => c j * xiCent (w j)
  let w₀ : Fin n → {W : ℂ // 1 / 2 < W.re} :=
    fun j => ⟨w j, lt_trans ha (hw j)⟩
  have hTilt :=
    eulerSafeDeficit_rescaledXi_re_eq_pi_mul_tiltCorrelation_deriv
      ha c w hw hD
  have hParity :=
    eulerSafeDeficit_re_eq_pi_mul_twoChannelParityDeficit ha d w hw
  dsimp only at hParity
  change (eulerSafeDeficit a d w).re = Real.pi * D at hTilt
  change (eulerSafeDeficit a d w).re = Real.pi *
      (xiWeilEvenEnergy (channelPacketA d w₀) +
          xiWeilEvenEnergy (channelPacketB d w₀) -
        (xiWeilOddEnergy (channelPacketA d w₀) +
          xiWeilOddEnergy (channelPacketB d w₀))) at hParity
  nlinarith [Real.pi_pos]

/-- RH is exactly contractivity of reflection-odd projection against reflection-even projection
on every linked two-channel resolvent packet. -/
theorem riemannHypothesis_iff_twoChannelParityEnergy_domination :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c : Fin n → ℂ)
        (w : Fin n → {W : ℂ // 1 / 2 < W.re}),
        xiWeilOddEnergy (channelPacketA c w) +
            xiWeilOddEnergy (channelPacketB c w) ≤
          xiWeilEvenEnergy (channelPacketA c w) +
            xiWeilEvenEnergy (channelPacketB c w) := by
  constructor
  · intro hRH n c w
    have hnonneg :=
      (riemannHypothesis_iff_twoChannel_packet_nonneg.mp hRH) n c w
    have hA := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilSquareSummable_channelPacketA c w)
    have hB := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilSquareSummable_channelPacketB c w)
    rw [hA, hB] at hnonneg
    simp only [Complex.add_re, Complex.ofReal_re] at hnonneg
    linarith
  · intro hdom
    apply riemannHypothesis_iff_twoChannel_packet_nonneg.mpr
    intro n c w
    have h := hdom n c w
    have hA := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilSquareSummable_channelPacketA c w)
    have hB := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
      (xiWeilSquareSummable_channelPacketB c w)
    rw [hA, hB]
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

/-- The diagonal critical logarithmic-derivative kernel is nonnegative throughout the exterior
half-plane.  This is the scalar theta-source current transported through the nonvanishing
coefficient `xiCent w`; no global RH input is used. -/
theorem criticalLogDerivKernel_self_re_nonneg_of_half_lt
    {w : ℂ} (hw : 1 / 2 < w.re) :
    0 ≤ (criticalLogDerivKernel w w).re := by
  have hcoord : ((w.re : ℂ) + (w.im : ℂ) * I) = w := by
    apply Complex.ext <;> simp
  have hsource : 0 ≤ (sourceBezoutian thetaCuspTiltSource w w).re := by
    simpa only [hcoord] using
      sourceBezoutian_thetaCuspTiltSource_self_nonneg_of_half_le hw.le w.im
  have hEq :=
    sourceBezoutian_thetaCuspTiltSource_eq_xiCent_mul_criticalKernel hw hw
  rw [Complex.mul_conj] at hEq
  have hre := congrArg Complex.re hEq
  rw [Complex.re_ofReal_mul] at hre
  have hX : 0 < Complex.normSq (xiCent w) :=
    Complex.normSq_pos.mpr (xiCent_ne_zero_of_half_lt_re hw)
  nlinarith

/-- Every one-node canonical resolvent packet satisfies the linked two-channel reflection-parity
domination unconditionally.  Consequently, any failure of the RH-equivalent domination law must
be a genuine cross-mode interference phenomenon. -/
theorem oneMode_twoChannelParityEnergy_domination
    {c w : ℂ} (hw : 1 / 2 < w.re) :
    let nodes : Fin 1 → {W : ℂ // 1 / 2 < W.re} := fun _ => ⟨w, hw⟩
    let coeff : Fin 1 → ℂ := fun _ => c
    xiWeilOddEnergy (channelPacketA coeff nodes) +
        xiWeilOddEnergy (channelPacketB coeff nodes) ≤
      xiWeilEvenEnergy (channelPacketA coeff nodes) +
        xiWeilEvenEnergy (channelPacketB coeff nodes) := by
  dsimp only
  let a : ℝ := (1 / 2 + w.re) / 2
  have ha : 1 / 2 < a := by
    dsimp [a]
    linarith
  have haw : a < w.re := by
    dsimp [a]
    linarith
  let coeff : Fin 1 → ℂ := fun _ => c
  let rawNodes : Fin 1 → ℂ := fun _ => w
  let nodes : Fin 1 → {W : ℂ // 1 / 2 < W.re} := fun _ => ⟨w, hw⟩
  have hParity :=
    eulerSafeDeficit_re_eq_pi_mul_twoChannelParityDeficit
      ha coeff rawNodes (fun _ => haw)
  dsimp only at hParity
  change (eulerSafeDeficit a coeff rawNodes).re = Real.pi *
      (xiWeilEvenEnergy (channelPacketA coeff nodes) +
          xiWeilEvenEnergy (channelPacketB coeff nodes) -
        (xiWeilOddEnergy (channelPacketA coeff nodes) +
          xiWeilOddEnergy (channelPacketB coeff nodes))) at hParity
  have hDef := eulerSafeDeficit_eq ha coeff rawNodes (fun _ => haw)
  have hCrit := criticalLogDerivKernel_self_re_nonneg_of_half_lt hw
  have hDefRe := congrArg Complex.re hDef
  simp only [Fin.sum_univ_one, coeff, rawNodes, Complex.re_ofReal_mul,
    Complex.mul_conj] at hDefRe
  have hc : 0 ≤ Complex.normSq c := Complex.normSq_nonneg c
  have hnonneg : 0 ≤ (eulerSafeDeficit a coeff rawNodes).re := by
    rw [hDefRe]
    exact mul_nonneg Real.pi_pos.le (mul_nonneg hc hCrit)
  nlinarith [Real.pi_pos]

end

end RHTower
