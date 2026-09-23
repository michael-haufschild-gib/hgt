import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityWeld
import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse

/-!
# Euler-ray rank-two theta/Weil parity weld

The complete squared-Euler divisor response is exactly the critical logarithmic-derivative kernel
on positive real nodes.  Its unconditional strict two-node determinant therefore supplies more
than a separate radial response law: it proves linked two-channel reflection-parity contraction
for every complex coefficient packet supported on two ordered Euler-ray nodes.  Transport through
the theta/CLG/Weil identity then proves nonnegative literal theta tilt flux on the same packets.

Consequently an RH-detecting negative packet cannot be scalar, and it cannot be a two-node packet
confined to the positive Euler ray.  It must use either complex-node geometry or at least three
real-ray modes.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- On the exterior positive Euler ray, the centered Xi logarithmic derivative is the real full
squared-Euler divisor response, as a complex number. -/
theorem logDeriv_xiCent_ofReal_eq_fullQ
    {x : ℝ} (hx : 1 / 2 < x) :
    logDeriv xiCent (x : ℂ) = (xiSquaredEulerFullQ x : ℂ) := by
  have hxhalf : 1 / 2 < ((x : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hconj := logDeriv_xiCent_conj hxhalf
  simp only [Complex.conj_ofReal] at hconj
  have him : (logDeriv xiCent (x : ℂ)).im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  apply Complex.ext
  · rw [logDeriv_xiCent_eq_shift]
    simpa only [Complex.ofReal_re] using
      (xiSquaredEulerFullQ_eq_logDeriv_re (by linarith)).symm
  · simpa only [Complex.ofReal_im] using him

/-- The RH-critical kernel restricted to exterior positive real nodes is exactly the full
multiplicity-exact squared-Euler response kernel. -/
theorem criticalLogDerivKernel_ofReal_eq_fullKernel
    {x y : ℝ} (hx : 1 / 2 < x) (hy : 1 / 2 < y) :
    criticalLogDerivKernel (x : ℂ) (y : ℂ) =
      (xiSquaredEulerFullKernel x y : ℂ) := by
  rw [criticalLogDerivKernel, logDeriv_xiCent_ofReal_eq_fullQ hx,
    logDeriv_xiCent_ofReal_eq_fullQ hy]
  simp only [Complex.conj_ofReal]
  rw [xiSquaredEulerFullKernel, eulerRayResponseKernel]
  push_cast
  rfl

/-- Every complex two-mode critical-kernel energy on two ordered exterior Euler-ray nodes is
nonnegative.  Strict diagonal positivity and the strict complete-divisor determinant give an
explicit two-square completion. -/
theorem twoMode_twoChannelKernel_realRay_energy_nonneg
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) :
    let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
      ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
        ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
    0 ≤ (kernelEnergy twoChannelKernel c nodes).re := by
  dsimp only
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  let A := xiSquaredEulerFullKernel x x
  let B := xiSquaredEulerFullKernel y y
  let C := xiSquaredEulerFullKernel x y
  have hy : 1 / 2 < y := hx.trans hxy
  have hA : 0 < A := xiSquaredEulerFullKernel_diag_pos (by linarith)
  have hdet : 0 < A * B - C ^ (2 : ℕ) := by
    exact xiSquaredEulerFullKernel_twoPoint_det_pos (by linarith) hxy
  have henergy :
      (kernelEnergy twoChannelKernel c nodes).re =
        A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
          2 * C * (conj (c 0) * c 1).re := by
    simp only [kernelEnergy, Fin.sum_univ_two, nodes, Matrix.cons_val_zero,
      Matrix.cons_val_one, twoChannelKernel_eq]
    rw [criticalLogDerivKernel_ofReal_eq_fullKernel hx hx,
      criticalLogDerivKernel_ofReal_eq_fullKernel hx hy,
      criticalLogDerivKernel_ofReal_eq_fullKernel hy hx,
      criticalLogDerivKernel_ofReal_eq_fullKernel hy hy]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, A, B, C]
    rw [show xiSquaredEulerFullKernel y x = xiSquaredEulerFullKernel x y by
      simp [xiSquaredEulerFullKernel, eulerRayResponseKernel, add_comm]]
    simp only [Complex.normSq_apply]
    ring
  have hsquares :
      0 ≤ (A * (c 0).re + C * (c 1).re) ^ (2 : ℕ) +
          (A * (c 0).im + C * (c 1).im) ^ (2 : ℕ) +
          (A * B - C ^ (2 : ℕ)) * ((c 1).re ^ (2 : ℕ) + (c 1).im ^ (2 : ℕ)) := by
    positivity
  rw [henergy]
  have hscaled :
      A * (A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
          2 * C * (conj (c 0) * c 1).re) =
        (A * (c 0).re + C * (c 1).re) ^ (2 : ℕ) +
          (A * (c 0).im + C * (c 1).im) ^ (2 : ℕ) +
          (A * B - C ^ (2 : ℕ)) * ((c 1).re ^ (2 : ℕ) + (c 1).im ^ (2 : ℕ)) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  nlinarith

/-- Every two-node canonical resolvent packet on the ordered positive Euler ray satisfies the
linked reflection-odd versus reflection-even energy domination unconditionally. -/
theorem twoMode_twoChannelParityEnergy_domination_realRay
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) :
    let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
      ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
        ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
    xiWeilOddEnergy (channelPacketA c nodes) +
        xiWeilOddEnergy (channelPacketB c nodes) ≤
      xiWeilEvenEnergy (channelPacketA c nodes) +
        xiWeilEvenEnergy (channelPacketB c nodes) := by
  dsimp only
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  have hpacket :
      0 ≤ (xiWeilPolarization (channelPacketA c nodes) (channelPacketA c nodes) +
          xiWeilPolarization (channelPacketB c nodes) (channelPacketB c nodes)).re := by
    rw [twoChannel_packet_eq_kernelEnergy]
    exact twoMode_twoChannelKernel_realRay_energy_nonneg hx hxy (fun j => conj (c j))
  have hA := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketA c nodes)
  have hB := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketB c nodes)
  rw [hA, hB] at hpacket
  simp only [Complex.add_re, Complex.ofReal_re] at hpacket
  linarith

/-- Literal theta tilt flux is nonnegative for every complex two-mode packet supported on two
ordered exterior positive Euler-ray nodes. -/
theorem thetaCuspTiltSource_twoMode_realRay_tiltFlux_nonneg
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) {D : ℝ}
    (hD : HasDerivAt
      (tiltCorrelation thetaCuspTiltSource c
        ![(x : ℂ), (y : ℂ)]) D 0) :
    0 ≤ D := by
  let a : ℝ := (1 / 2 + x) / 2
  have ha : 1 / 2 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hay : a < y := hax.trans hxy
  let rawNodes : Fin 2 → ℂ := ![(x : ℂ), (y : ℂ)]
  let d : Fin 2 → ℂ := fun j => c j * xiCent (rawNodes j)
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  have hEq :=
    tiltCorrelation_thetaCuspTiltSource_deriv_eq_twoChannelParityDeficit
      ha c rawNodes (fun j => by fin_cases j <;> simp [rawNodes, hax, hay]) hD
  dsimp only at hEq
  change D = xiWeilEvenEnergy (channelPacketA d nodes) +
      xiWeilEvenEnergy (channelPacketB d nodes) -
        (xiWeilOddEnergy (channelPacketA d nodes) +
          xiWeilOddEnergy (channelPacketB d nodes)) at hEq
  have hdom := twoMode_twoChannelParityEnergy_domination_realRay hx hxy d
  dsimp only at hdom
  change xiWeilOddEnergy (channelPacketA d nodes) +
      xiWeilOddEnergy (channelPacketB d nodes) ≤
        xiWeilEvenEnergy (channelPacketA d nodes) +
          xiWeilEvenEnergy (channelPacketB d nodes) at hdom
  linarith

end

end RHTower
