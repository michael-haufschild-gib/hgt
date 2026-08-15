import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureIntertwinerRigidity
import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive

open Complex Filter Matrix Set Topology
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-!
# Route P Ward--Herglotz aperture tangent

The P-G196 rate-change anomaly is not merely nonzero.  The actual Gamma-sewn
Xi Schur phase realizes its first aperture jet as a positive matrix kernel.
At the level of one Schwarz pair, that tangent splits into the two literal
resolved zero channels plus positive Hardy dressings.  Thus rate change is
carried by a positive first-order defect channel, while the remaining Route P
problem is to bound this channel by the coefficient-faithful primitive source.
-/

/-- Matrix first jet of the strict-right Xi Schur defect. -/
def continuedXiWardHerglotzPickMatrix {n : ℕ}
    (w : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (continuedXiAntiCausalWardResponse (w i) +
      star (continuedXiAntiCausalWardResponse (w j))) /
        (w i + star (w j))

private theorem hasDerivAt_realAperture_of_complex_zero_pg197
    {f : ℂ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    HasDerivAt (fun x : ℝ => f x) f' 0 := by
  have houter : HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      (Complex.ofRealCLM 0) := by
    simpa using h.hasFDerivAt.restrictScalars ℝ
  have hcomp := houter.comp (0 : ℝ) Complex.ofRealCLM.hasFDerivAt
  show HasFDerivAt (fun x : ℝ => f x)
    (ContinuousLinearMap.toSpanSingleton ℝ f') 0
  simpa using! hcomp

private theorem tendsto_routePWardTransport_div_aperture
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ) / (a : ℂ))
      (𝓝[>] 0)
      (𝓝 (continuedXiAntiCausalWardResponse w)) := by
  have hderiv : HasDerivAt
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ))
      (continuedXiAntiCausalWardResponse w) 0 :=
    hasDerivAt_realAperture_of_complex_zero_pg197
      (hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw)
  have hzero : mobiusGammaXiAntiCausalWardTransportV w 0 = 0 :=
    mobiusGammaXiAntiCausalWardTransportV_zero hw
  convert hderiv.tendsto_slope_zero_right using 1
  ext a
  simp [hzero, div_eq_inv_mul]

private theorem tendsto_routePWardTransport_zero
    {w : ℂ} (hw : 0 < w.re) :
    Tendsto
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  have hderiv : HasDerivAt
      (fun a : ℝ =>
        mobiusGammaXiAntiCausalWardTransportV w (a : ℂ))
      (continuedXiAntiCausalWardResponse w) 0 :=
    hasDerivAt_realAperture_of_complex_zero_pg197
      (hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw)
  simpa [mobiusGammaXiAntiCausalWardTransportV_zero hw] using
    hderiv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The scaled finite-aperture Pick defect converges entrywise to the Ward
Herglotz kernel. -/
theorem tendsto_xiWardPhasePickDefect_div_aperture
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re) :
    Tendsto
      (fun a : ℝ =>
        (a⁻¹ : ℝ) • rightHalfPlanePickDefect w
          (fun i => xiRightWardBoundarySourcePhaseCrossRatio
            (I * w i) (a : ℂ)))
      (𝓝[>] 0)
      (𝓝 (continuedXiWardHerglotzPickMatrix w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let Vi : ℝ → ℂ := fun a =>
    mobiusGammaXiAntiCausalWardTransportV (w i) (a : ℂ)
  let Vj : ℝ → ℂ := fun a =>
    mobiusGammaXiAntiCausalWardTransportV (w j) (a : ℂ)
  let Ri := continuedXiAntiCausalWardResponse (w i)
  let Rj := continuedXiAntiCausalWardResponse (w j)
  have hiDiv : Tendsto (fun a : ℝ => Vi a / (a : ℂ))
      (𝓝[>] 0) (𝓝 Ri) := by
    simpa only [Vi, Ri] using
      tendsto_routePWardTransport_div_aperture (hw i)
  have hjDiv : Tendsto (fun a : ℝ => Vj a / (a : ℂ))
      (𝓝[>] 0) (𝓝 Rj) := by
    simpa only [Vj, Rj] using
      tendsto_routePWardTransport_div_aperture (hw j)
  have hjConjDiv : Tendsto (fun a : ℝ => star (Vj a) / (a : ℂ))
      (𝓝[>] 0) (𝓝 (star Rj)) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp hjDiv
    convert h using 1 <;> ext a <;>
      simp [map_div₀, Complex.conj_ofReal]
  have hjZero : Tendsto (fun a : ℝ => star (Vj a))
      (𝓝[>] 0) (𝓝 0) := by
    have h := Complex.continuous_conj.continuousAt.tendsto.comp
      (tendsto_routePWardTransport_zero (hw j))
    convert h using 1
    · ext a
      rfl
    · simp
  have hnum := (hiDiv.add hjConjDiv).sub (hiDiv.mul hjZero)
  have hquot := hnum.div_const (w i + star (w j))
  have hden : w i + star (w j) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (w i).re + (w j).re = 0 at hre
    linarith [hw i, hw j]
  have hlim : Tendsto
      (fun a : ℝ =>
        ((Vi a / (a : ℂ) + star (Vj a) / (a : ℂ)) -
          (Vi a / (a : ℂ)) * star (Vj a)) /
            (w i + star (w j)))
      (𝓝[>] 0)
      (𝓝 ((Ri + star Rj) / (w i + star (w j)))) := by
    simpa using hquot
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change 0 < a at ha
  change
    ((Vi a / (a : ℂ) + star (Vj a) / (a : ℂ)) -
      (Vi a / (a : ℂ)) * star (Vj a)) /
        (w i + star (w j)) =
      ((a⁻¹ : ℝ) : ℂ) *
        ((1 - xiRightWardBoundarySourcePhaseCrossRatio
              (I * w i) (a : ℂ) *
            star (xiRightWardBoundarySourcePhaseCrossRatio
              (I * w j) (a : ℂ))) /
          (w i + star (w j)))
  rw [show xiRightWardBoundarySourcePhaseCrossRatio
      (I * w i) (a : ℂ) = 1 - Vi a by
    rw [show Vi a = 1 - xiRightWardBoundarySourcePhaseCrossRatio
      (I * w i) (a : ℂ) by
      exact mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase (hw i) _]
    ring]
  rw [show xiRightWardBoundarySourcePhaseCrossRatio
      (I * w j) (a : ℂ) = 1 - Vj a by
    rw [show Vj a = 1 - xiRightWardBoundarySourcePhaseCrossRatio
      (I * w j) (a : ℂ) by
      exact mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase (hw j) _]
    ring]
  rw [show star (1 - Vj a) = 1 - star (Vj a) by simp]
  push_cast
  field_simp [ha.ne']
  ring

/-- The complete matrix first jet of the strict-right Xi Schur defect is
positive semidefinite on every finite right-half-plane packet. -/
theorem continuedXiWardHerglotzPickMatrix_posSemidef
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re) :
    (continuedXiWardHerglotzPickMatrix w).PosSemidef := by
  apply Matrix.PosSemidef.of_tendsto_complex
    (l := 𝓝[>] (0 : ℝ))
    (A := fun a : ℝ =>
      (a⁻¹ : ℝ) • rightHalfPlanePickDefect w
        (fun i => xiRightWardBoundarySourcePhaseCrossRatio
          (I * w i) (a : ℂ)))
  · filter_upwards [self_mem_nhdsWithin] with a ha
    change 0 < a at ha
    exact (xiWardPhasePickDefect_posSemidef hw ha.le).smul
      (by positivity : 0 ≤ a⁻¹)
  · exact tendsto_xiWardPhasePickDefect_div_aperture hw

/-- Herglotz first-jet kernel carried by one centered strict-right mode. -/
def xiWardModeHerglotzPickMatrix {n : ℕ}
    (w : Fin n → ℂ) (lam : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (2 * (w i + lam)⁻¹ + star (2 * (w j + lam)⁻¹)) /
      (w i + star (w j))

/-- A single zero mode's Herglotz tangent splits exactly into a resolved
rank-one channel and a positively dressed Hardy channel. -/
theorem xiWardModeHerglotzPickMatrix_factorization
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ}
    (hw : ∀ i, 0 < (w i).re) (hlam : 0 < lam.re) :
    xiWardModeHerglotzPickMatrix w lam =
      (2 : ℝ) •
        (xiWardCayleyResolventColumn w lam 0 *
          (xiWardCayleyResolventColumn w lam 0)ᴴ) +
      (4 * lam.re : ℝ) •
        (xiWardCayleyResolventDiagonal w lam 0 *
          rightHalfPlaneHardyCauchyGram w *
            (xiWardCayleyResolventDiagonal w lam 0)ᴴ) := by
  ext i j
  have hwi : w i + lam ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith [hw i, hlam]
  have hwj : star (w j + lam) ≠ 0 := by
    exact map_ne_zero (starRingEnd ℂ) |>.mpr (by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.zero_re] at hre
      linarith [hw j, hlam])
  have hwj' : star (w j) + star lam ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (w j).re + lam.re = 0 at hre
    linarith [hw j, hlam]
  have hwij : w i + star (w j) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (w i).re + (w j).re = 0 at hre
    linarith [hw i, hw j]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  rw [xiWardCayleyResolventColumn_gram_apply,
    xiWardCayleyResolventDiagonal_cauchy_apply]
  simp only [xiWardModeHerglotzPickMatrix, ofReal_zero, add_zero]
  have hreal : (lam.re : ℂ) = (lam + star lam) / 2 := by
    apply Complex.ext <;> simp
  have hstarTerm : star (2 * (w j + lam)⁻¹) =
      2 * (star (w j) + star lam)⁻¹ := by simp
  have hstarInv : star (w j + lam)⁻¹ =
      (star (w j) + star lam)⁻¹ := by simp
  rw [hstarTerm]
  rw [hstarInv]
  field_simp [hwi, hwj, hwj', hwij]
  push_cast
  rw [hreal]
  ring

theorem xiWardModeHerglotzPickMatrix_posSemidef
    {n : ℕ} {w : Fin n → ℂ} {lam : ℂ}
    (hw : ∀ i, 0 < (w i).re) (hlam : 0 < lam.re) :
    (xiWardModeHerglotzPickMatrix w lam).PosSemidef := by
  rw [xiWardModeHerglotzPickMatrix_factorization hw hlam]
  apply Matrix.PosSemidef.add
  · exact (Matrix.posSemidef_self_mul_conjTranspose
      (xiWardCayleyResolventColumn w lam 0)).smul (by norm_num)
  · exact ((rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same
      (xiWardCayleyResolventDiagonal w lam 0)).smul (by positivity)

/-- Herglotz tangent matrix of one complete strict-right Schwarz pair. -/
def xiWardSchwarzPairHerglotzPickMatrix {n : ℕ}
    (w : Fin n → ℂ) (q : XiRightUpperZeroCopy) :
    Matrix (Fin n) (Fin n) ℂ :=
  xiWardModeHerglotzPickMatrix w (xiRightCenteredZero q.1) +
    xiWardModeHerglotzPickMatrix w
      (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1))

theorem xiWardSchwarzPairHerglotzPickMatrix_apply
    {n : ℕ} (w : Fin n → ℂ) (q : XiRightUpperZeroCopy)
    (i j : Fin n) :
    xiWardSchwarzPairHerglotzPickMatrix w q i j =
      (xiAntiCausalWardSchwarzPairResponse q (w i) +
        star (xiAntiCausalWardSchwarzPairResponse q (w j))) /
          (w i + star (w j)) := by
  rw [xiWardSchwarzPairHerglotzPickMatrix,
    xiAntiCausalWardSchwarzPairResponse]
  simp only [Matrix.add_apply, xiWardModeHerglotzPickMatrix]
  simp only [xiAntiCausalWardSchwarzPairResponse]
  rw [show star (2 * ((w j + xiRightCenteredZero q.1)⁻¹ +
      (w j + xiRightCenteredZero
        (xiRightZeroCopyConjEquiv q.1))⁻¹)) =
      star (2 * (w j + xiRightCenteredZero q.1)⁻¹) +
        star (2 * (w j + xiRightCenteredZero
          (xiRightZeroCopyConjEquiv q.1))⁻¹) by
    simp
    ring]
  ring

theorem xiWardSchwarzPairHerglotzPickMatrix_posSemidef
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (q : XiRightUpperZeroCopy) :
    (xiWardSchwarzPairHerglotzPickMatrix w q).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact xiWardModeHerglotzPickMatrix_posSemidef hw
      (xiRightCenteredZero_re_pos q.1)
  · exact xiWardModeHerglotzPickMatrix_posSemidef hw
      (xiRightCenteredZero_re_pos (xiRightZeroCopyConjEquiv q.1))

/-- The resolved two-mode rank-one Gram of one actual Schwarz pair. -/
def xiWardSchwarzPairResolvedGram {n : ℕ}
    (w : Fin n → ℂ) (q : XiRightUpperZeroCopy) :
    Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℝ) •
    (xiWardCayleyResolventColumn w (xiRightCenteredZero q.1) 0 *
      (xiWardCayleyResolventColumn w (xiRightCenteredZero q.1) 0)ᴴ) +
  (2 : ℝ) •
    (xiWardCayleyResolventColumn w
        (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1)) 0 *
      (xiWardCayleyResolventColumn w
        (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1)) 0)ᴴ)

/-- Positive remainder after extracting both resolved zero channels from one
Schwarz-pair Herglotz tangent. -/
theorem xiWardSchwarzPairResolvedGram_le_herglotzPick
    {n : ℕ} {w : Fin n → ℂ} (hw : ∀ i, 0 < (w i).re)
    (q : XiRightUpperZeroCopy) :
    (xiWardSchwarzPairHerglotzPickMatrix w q -
      xiWardSchwarzPairResolvedGram w q).PosSemidef := by
  rw [xiWardSchwarzPairHerglotzPickMatrix,
    xiWardSchwarzPairResolvedGram,
    xiWardModeHerglotzPickMatrix_factorization hw
      (xiRightCenteredZero_re_pos q.1),
    xiWardModeHerglotzPickMatrix_factorization hw
      (xiRightCenteredZero_re_pos (xiRightZeroCopyConjEquiv q.1))]
  let D₁ := xiWardCayleyResolventDiagonal w (xiRightCenteredZero q.1) 0
  let D₂ := xiWardCayleyResolventDiagonal w
    (xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1)) 0
  have h₁ :
      (D₁ * rightHalfPlaneHardyCauchyGram w * D₁ᴴ).PosSemidef :=
    (rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same D₁
  have h₂ :
      (D₂ * rightHalfPlaneHardyCauchyGram w * D₂ᴴ).PosSemidef :=
    (rightHalfPlaneHardyCauchyGram_posSemidef hw).mul_mul_conjTranspose_same D₂
  have hc₁ : 0 ≤ 4 * (xiRightCenteredZero q.1).re := by
    nlinarith [xiRightCenteredZero_re_pos q.1]
  have hc₂ : 0 ≤ 4 * (xiRightCenteredZero
      (xiRightZeroCopyConjEquiv q.1)).re := by
    nlinarith [xiRightCenteredZero_re_pos
      (xiRightZeroCopyConjEquiv q.1)]
  have hs :
      ((4 * (xiRightCenteredZero q.1).re : ℝ) •
          (D₁ * rightHalfPlaneHardyCauchyGram w * D₁ᴴ) +
        (4 * (xiRightCenteredZero
          (xiRightZeroCopyConjEquiv q.1)).re : ℝ) •
          (D₂ * rightHalfPlaneHardyCauchyGram w * D₂ᴴ)).PosSemidef :=
    (h₁.smul hc₁).add (h₂.smul hc₂)
  convert hs using 1
  simp only [D₁, D₂]
  module

end

end RHTower
