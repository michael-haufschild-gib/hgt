import GaloisForLFunctions.RHTower.EulerPrimitiveCommonTestHorizon

/-!
# Critical blow-up of the primitive Euler common-test horizon

The joint source/spectral scaling

`ε = σ - 1`, `w = ε a`

has a nontrivial matrix limit.  The compact head converges to the shifted
polar Cauchy Gram, while the tail converges to the Hadamard product of the
ordinary and shifted Cauchy Grams.  Thus the shifted polar channel is not an
external correction: it is the literal compact-head blow-up of the retained
prime-power horizon.
-/

open Complex Filter Set Matrix
open scoped Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Complexified critical-clock response.  Unlike a characteristic
function, `q` can be any nonzero complex blow-up direction. -/
def eulerPrimeCurrentComplexBlowupResponse
    (sigma : ℝ) (q : ℂ) : ℂ :=
  infinitePrimeFlux
      (1 + (((sigma : ℂ) - 1) * q)) /
    infinitePrimeFlux sigma

private theorem tendsto_eulerPrimeCurrentComplexBlowupParameter_nhdsNE
    {q : ℂ} (hq : q ≠ 0) :
    Tendsto (fun sigma : ℝ =>
        1 + (((sigma : ℂ) - 1) * q))
      (nhdsWithin 1 (Ioi 1)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont :
        ContinuousAt (fun sigma : ℝ =>
          1 + (((sigma : ℂ) - 1) * q)) 1 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    simp only [mem_compl_iff, mem_singleton_iff]
    intro h
    have hmul : ((sigma : ℂ) - 1) * q = 0 := by
      linear_combination h
    have heps : (sigma : ℂ) - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hsigma.ne')
    exact (mul_ne_zero heps hq) hmul

private theorem tendsto_realParameter_nhdsNE_for_blowup :
    Tendsto (fun sigma : ℝ => (sigma : ℂ))
      (nhdsWithin 1 (Ioi 1)) (𝓝[≠] (1 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using!
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    simpa using hsigma.ne'

private theorem infinitePrimeFlux_real_ne_zero_for_blowup
    {sigma : ℝ} (hsigma : 1 < sigma) :
    infinitePrimeFlux sigma ≠ 0 := by
  rw [← ofReal_eulerPrimeCurrentTotal_eq hsigma]
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (eulerPrimeCurrentTotal_pos hsigma))

/-- The von-Mangoldt pole is isotropic under every nonzero complex
blow-up direction: the normalized response tends to `q⁻¹`. -/
theorem tendsto_eulerPrimeCurrentComplexBlowupResponse
    {q : ℂ} (hq : q ≠ 0) :
    Tendsto (fun sigma : ℝ =>
        eulerPrimeCurrentComplexBlowupResponse sigma q)
      (nhdsWithin 1 (Ioi 1)) (nhds q⁻¹) := by
  let path : ℝ → ℂ := fun sigma =>
    1 + (((sigma : ℂ) - 1) * q)
  have hresPath :
      Tendsto
        (fun sigma : ℝ =>
          (path sigma - 1) * infinitePrimeFlux (path sigma))
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have h := neg_logDeriv_zeta_residue.comp
      (tendsto_eulerPrimeCurrentComplexBlowupParameter_nhdsNE hq)
    apply h.congr'
    filter_upwards with sigma
    dsimp only [path]
    simp only [Function.comp_apply, infinitePrimeFlux, logDeriv_apply]
    ring_nf
  have hresReal :
      Tendsto
        (fun sigma : ℝ =>
          ((sigma : ℂ) - 1) * infinitePrimeFlux sigma)
        (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
    have h := neg_logDeriv_zeta_residue.comp
      tendsto_realParameter_nhdsNE_for_blowup
    apply h.congr'
    filter_upwards with sigma
    simp only [Function.comp_apply, infinitePrimeFlux, logDeriv_apply]
    ring_nf
  have hregularized :
      Tendsto
        (fun sigma : ℝ =>
          ((path sigma - 1) * infinitePrimeFlux (path sigma)) /
            ((((sigma : ℂ) - 1) * infinitePrimeFlux sigma) * q))
        (nhdsWithin 1 (Ioi 1)) (nhds q⁻¹) := by
    have h := hresPath.div (hresReal.mul_const q)
      (mul_ne_zero one_ne_zero hq)
    simpa [hq, Pi.div_apply] using! h
  apply hregularized.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  have heps : ((sigma : ℂ) - 1) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hsigma.ne')
  have hflux : infinitePrimeFlux sigma ≠ 0 :=
    infinitePrimeFlux_real_ne_zero_for_blowup hsigma
  have hpath : path sigma - 1 = ((sigma : ℂ) - 1) * q := by
    simp [path]
  rw [eulerPrimeCurrentComplexBlowupResponse, hpath]
  change
    (((sigma : ℂ) - 1) * q * infinitePrimeFlux (path sigma)) /
        (((sigma : ℂ) - 1) * infinitePrimeFlux sigma * q) =
      infinitePrimeFlux (path sigma) / infinitePrimeFlux sigma
  field_simp [heps, hflux, hq]

/-- Critical tail blow-up: ordinary Hardy Cauchy test times the shifted
polar Cauchy test. -/
def eulerPrimitiveHorizonBlowupTailGram
    {N : ℕ} (a : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (rightHalfPlaneHardyCauchyGram a) ⊙
    (shiftedPolarRightHalfPlaneGram a)

/-- Critical head blow-up. -/
def eulerPrimitiveHorizonBlowupHeadGram
    {N : ℕ} (a : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  shiftedPolarRightHalfPlaneGram a

theorem shiftedPolarRightHalfPlaneGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (shiftedPolarRightHalfPlaneGram a).PosSemidef := by
  have hEq :
      shiftedPolarRightHalfPlaneGram a =
        rightHalfPlaneHardyCauchyGram (fun i => a i + 1 / 2) := by
    ext i j
    simp [shiftedPolarRightHalfPlaneGram,
      rightHalfPlaneHardyCauchyGram]
    ring
  rw [hEq]
  apply rightHalfPlaneHardyCauchyGram_posSemidef
  intro i
  simp
  linarith [ha i]

theorem eulerPrimitiveHorizonBlowupTailGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveHorizonBlowupTailGram a).PosSemidef :=
  (rightHalfPlaneHardyCauchyGram_posSemidef ha).hadamard
    (shiftedPolarRightHalfPlaneGram_posSemidef a ha)

theorem eulerPrimitiveHorizonBlowupHeadGram_posSemidef
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    (eulerPrimitiveHorizonBlowupHeadGram a).PosSemidef :=
  shiftedPolarRightHalfPlaneGram_posSemidef a ha

def eulerPrimitiveHorizonBlowupNode
    {N : ℕ} (sigma : ℝ) (a : Fin N → ℂ) : Fin N → ℂ :=
  fun i => ((sigma : ℂ) - 1) * a i

def eulerPrimitiveHorizonScaledTailGram
    {N : ℕ} (sigma : ℝ) (a : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((sigma : ℂ) - 1) •
    eulerPrimitiveHorizonTailGram sigma
      (eulerPrimitiveHorizonBlowupNode sigma a)

def eulerPrimitiveHorizonScaledHeadGram
    {N : ℕ} (sigma : ℝ) (a : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ((sigma : ℂ) - 1) •
    eulerPrimitiveHorizonHeadGram sigma
      (eulerPrimitiveHorizonBlowupNode sigma a)

theorem eulerPrimitiveHorizonScaledTailGram_apply_eq_response
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ k, 0 < (a k).re) (i j : Fin N) :
    eulerPrimitiveHorizonScaledTailGram sigma a i j =
      eulerPrimeCurrentComplexBlowupResponse sigma
          (1 + a i + star (a j)) *
        rightHalfPlaneHardyCauchyGram a i j := by
  rw [eulerPrimitiveHorizonScaledTailGram,
    eulerPrimitiveHorizonTailGram,
    eulerPrimitiveHorizonShiftedTailGram]
  simp only [Matrix.smul_apply, Matrix.hadamard_apply, smul_eq_mul,
    vonMangoldtPrimeRightHalfPlaneGram,
    rightHalfPlaneHardyCauchyGram]
  rw [ofReal_eulerPrimeCurrentTotal_eq hsigma]
  let eps : ℂ := (sigma : ℂ) - 1
  let s : ℂ := a i + star (a j)
  let q : ℂ := 1 + s
  have heps : ((sigma : ℂ) - 1) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hsigma.ne')
  have hs : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  have hnode :
      eulerPrimitiveHorizonBlowupNode sigma a i +
          star (eulerPrimitiveHorizonBlowupNode sigma a j) =
        eps * s := by
    simp [eulerPrimitiveHorizonBlowupNode, eps, s]
    ring
  have hshift :
      eulerPrimitiveHorizonShift sigma
            (eulerPrimitiveHorizonBlowupNode sigma a i) +
          star (eulerPrimitiveHorizonShift sigma
            (eulerPrimitiveHorizonBlowupNode sigma a j)) + 1 =
        1 + eps * q := by
    simp [eulerPrimitiveHorizonShift,
      eulerPrimitiveHorizonBlowupNode, eps, q, s]
    ring
  have hargRe : 1 < (1 + eps * q).re := by
    have hepsRe : 0 < eps.re := by
      simp [eps]
      linarith
    have hqRe : 0 < q.re := by
      simp [q, s]
      linarith [ha i, ha j]
    rw [Complex.add_re, Complex.mul_re]
    have hepsIm : eps.im = 0 := by simp [eps]
    rw [hepsIm]
    simp only [one_re, zero_mul, sub_zero]
    nlinarith
  have hchannel :
      vonMangoldtPrimeLaplaceChannelComplex
          (eulerPrimitiveHorizonShift sigma
              (eulerPrimitiveHorizonBlowupNode sigma a i) +
            star (eulerPrimitiveHorizonShift sigma
              (eulerPrimitiveHorizonBlowupNode sigma a j))) =
        infinitePrimeFlux (1 + eps * q) := by
    unfold vonMangoldtPrimeLaplaceChannelComplex
    rw [infinitePrimeFlux_eq_vonMangoldtLSeries hargRe]
    rw [hshift]
  rw [hchannel, hnode]
  unfold eulerPrimeCurrentComplexBlowupResponse
  have hflux : infinitePrimeFlux sigma ≠ 0 :=
    infinitePrimeFlux_real_ne_zero_for_blowup hsigma
  dsimp only [eps, q, s] at *
  field_simp [heps, hs, hflux]
  congr 2
  ring

/-- Exact critical tail blow-up on every finite packet. -/
theorem tendsto_eulerPrimitiveHorizonScaledTailGram
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    Tendsto (fun sigma : ℝ =>
        eulerPrimitiveHorizonScaledTailGram sigma a)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveHorizonBlowupTailGram a)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let q : ℂ := 1 + a i + star (a j)
  have hq : q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change 1 + (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  have hresponse :=
    (tendsto_eulerPrimeCurrentComplexBlowupResponse hq).mul_const
      (rightHalfPlaneHardyCauchyGram a i j)
  have hcongr :
      (fun sigma : ℝ =>
          eulerPrimitiveHorizonScaledTailGram sigma a i j) =ᶠ[
            nhdsWithin 1 (Ioi 1)]
        fun sigma =>
          eulerPrimeCurrentComplexBlowupResponse sigma q *
            rightHalfPlaneHardyCauchyGram a i j := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact eulerPrimitiveHorizonScaledTailGram_apply_eq_response
      hsigma a ha i j
  have hlimit := hresponse.congr' hcongr.symm
  simpa [eulerPrimitiveHorizonBlowupTailGram,
    rightHalfPlaneHardyCauchyGram,
    shiftedPolarRightHalfPlaneGram, q, add_assoc, add_comm,
    add_left_comm, mul_comm] using hlimit

theorem eulerPrimitiveHorizonScaledCauchyGram
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    ((sigma : ℂ) - 1) •
        rightHalfPlaneHardyCauchyGram
          (eulerPrimitiveHorizonBlowupNode sigma a) =
      rightHalfPlaneHardyCauchyGram a := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul,
    rightHalfPlaneHardyCauchyGram]
  have heps : ((sigma : ℂ) - 1) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hsigma.ne')
  have hs : a i + star (a j) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  have hden :
      eulerPrimitiveHorizonBlowupNode sigma a i +
          star (eulerPrimitiveHorizonBlowupNode sigma a j) =
        ((sigma : ℂ) - 1) * (a i + star (a j)) := by
    simp [eulerPrimitiveHorizonBlowupNode]
    ring
  rw [hden]
  field_simp [heps, hs]

theorem eulerPrimitiveHorizonScaledHeadGram_add_tail
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    eulerPrimitiveHorizonScaledHeadGram sigma a +
        eulerPrimitiveHorizonScaledTailGram sigma a =
      rightHalfPlaneHardyCauchyGram a := by
  rw [eulerPrimitiveHorizonScaledHeadGram,
    eulerPrimitiveHorizonScaledTailGram,
    eulerPrimitiveHorizonHeadGram]
  rw [smul_sub, sub_add_cancel]
  exact eulerPrimitiveHorizonScaledCauchyGram hsigma a ha

/-- Blow-up head and tail reconstruct the whole Hardy Gram exactly. -/
theorem eulerPrimitiveHorizonBlowupHeadGram_add_tail
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    eulerPrimitiveHorizonBlowupHeadGram a +
        eulerPrimitiveHorizonBlowupTailGram a =
      rightHalfPlaneHardyCauchyGram a := by
  ext i j
  simp only [eulerPrimitiveHorizonBlowupHeadGram,
    eulerPrimitiveHorizonBlowupTailGram, Matrix.add_apply,
    Matrix.hadamard_apply, shiftedPolarRightHalfPlaneGram,
    rightHalfPlaneHardyCauchyGram]
  have hs : a i + star (a j) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (a i).re + (a j).re = 0 at hre
    linarith [ha i, ha j]
  have hs1 : a i + star (a j) + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change (a i).re + (a j).re + 1 = 0 at hre
    linarith [ha i, ha j]
  field_simp [hs, hs1]

/-- Exact critical head blow-up. -/
theorem tendsto_eulerPrimitiveHorizonScaledHeadGram
    {N : ℕ} (a : Fin N → ℂ) (ha : ∀ i, 0 < (a i).re) :
    Tendsto (fun sigma : ℝ =>
        eulerPrimitiveHorizonScaledHeadGram sigma a)
      (nhdsWithin 1 (Ioi 1))
      (nhds (eulerPrimitiveHorizonBlowupHeadGram a)) := by
  have htail := tendsto_eulerPrimitiveHorizonScaledTailGram a ha
  have hsub :
      Tendsto
        (fun sigma : ℝ =>
          rightHalfPlaneHardyCauchyGram a -
            eulerPrimitiveHorizonScaledTailGram sigma a)
        (nhdsWithin 1 (Ioi 1))
        (nhds
          (rightHalfPlaneHardyCauchyGram a -
            eulerPrimitiveHorizonBlowupTailGram a)) :=
    tendsto_const_nhds.sub htail
  have hsource :
      (fun sigma : ℝ =>
          eulerPrimitiveHorizonScaledHeadGram sigma a) =ᶠ[
            nhdsWithin 1 (Ioi 1)]
        fun sigma =>
          rightHalfPlaneHardyCauchyGram a -
            eulerPrimitiveHorizonScaledTailGram sigma a := by
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    have hsplit :=
      eulerPrimitiveHorizonScaledHeadGram_add_tail hsigma a ha
    rw [← hsplit]
    simp
  have hlim := hsub.congr' hsource.symm
  have htarget :
      rightHalfPlaneHardyCauchyGram a -
          eulerPrimitiveHorizonBlowupTailGram a =
        eulerPrimitiveHorizonBlowupHeadGram a := by
    have hsplit :=
      eulerPrimitiveHorizonBlowupHeadGram_add_tail a ha
    rw [← hsplit]
    simp
  rwa [htarget] at hlim

end

end RHTower
