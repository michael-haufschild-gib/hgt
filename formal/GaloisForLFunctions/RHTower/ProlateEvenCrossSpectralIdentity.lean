import GaloisForLFunctions.RHTower.ProlateIndexedSeparationSpectrum
import GaloisForLFunctions.RHTower.ProlateEvenBandEigenvalueSimplicity

open MeasureTheory

noncomputable section

namespace RHTower

/-- Every positive-aperture live band eigenpair has a normalized local branch whose eigenvector
and eigenvalue are both differentiable at the base aperture. -/
theorem exists_differentiable_bandOperatorL2_branch_of_pos
    {c₀ ν₀ : ℝ}
    {ψ₀ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1}
    (hc₀ : 0 < c₀)
    (heig : GaloisForLFunctions.RHTower.bandOperatorL2 c₀ ψ₀ = ν₀ • ψ₀)
    (hnorm : (inner ℝ ψ₀ ψ₀ : ℝ) = 1) (hν₀ : ν₀ ≠ 0) :
    ∃ (ψ : ℝ → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1)
        (ν : ℝ → ℝ),
      ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      DifferentiableAt ℝ ψ c₀ ∧ DifferentiableAt ℝ ν c₀ ∧
      ∀ᶠ c in nhds c₀,
        GaloisForLFunctions.RHTower.bandOperatorL2 c (ψ c) = ν c • ψ c ∧
          (inner ℝ (ψ c) (ψ c) : ℝ) = 1 := by
  have hψne : ψ₀ ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hnorm
    exact zero_ne_one hnorm
  have hsimple : ∀ φ : GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1,
      GaloisForLFunctions.RHTower.bandOperatorL2 c₀ φ = ν₀ • φ →
        ∃ s : ℝ, φ = s • ψ₀ := by
    intro φ hφ
    exact bandOperatorL2_eigenvectors_proportional hc₀ hν₀ heig hψne hφ
  obtain ⟨R, hR, hRψ⟩ :=
    GaloisForLFunctions.HTGeometry.exists_pseudoInverse_of_isCompactOperator
      (GaloisForLFunctions.RHTower.isCompactOperator_bandOperatorL2 c₀)
      (GaloisForLFunctions.RHTower.bandOperatorL2_symmetric c₀)
      heig hnorm hν₀ hsimple
  exact GaloisForLFunctions.HTGeometry.exists_differentiable_normalized_simple_eigen_branch
    (GaloisForLFunctions.RHTower.hasStrictFDerivAt_bandOperatorL2_apply c₀ ψ₀)
    (GaloisForLFunctions.RHTower.bandOperatorL2_symmetric c₀)
    heig hnorm hsimple hR hRψ

private theorem deriv_neg_of_even_crossSpectral {f : ℝ → ℝ}
    (heven : Function.Even f) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have hneg : HasDerivAt (fun y : ℝ => -y) (-1) x := (hasDerivAt_id x).neg
  have hcomp : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * (-1)) x :=
    (hf (-x)).hasDerivAt.comp x hneg
  have heq : (fun y : ℝ => f (-y)) = f := funext heven
  have hderiv := congrArg (fun g : ℝ → ℝ => deriv g x) heq
  change deriv (fun y : ℝ => f (-y)) x = deriv f x at hderiv
  rw [hcomp.deriv] at hderiv
  linarith

/-- Distinct Slepian eigenvalues scale the two second-derivative pairings exactly. -/
theorem integral_secondDeriv_pairing_scaled_of_bandEigenvalues
    {c lam_f lam_g : ℝ} {f g : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hfb : ∀ x, bandTransform c f x = lam_f * f x)
    (hgb : ∀ x, bandTransform c g x = lam_g * g x) :
    lam_f * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) =
      lam_g * (∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x) := by
  have hs := bandSecondTransform_symmetric c hf.continuous hg.continuous
  have hleft : (∫ x in (-1 : ℝ)..1, bandSecondTransform c f x * g x) =
      lam_f * ∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandSecondTransform_eq_eigen_secondDeriv hf hf2 hfb]
    ring
  have hright : (∫ x in (-1 : ℝ)..1, f x * bandSecondTransform c g x) =
      lam_g * ∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [bandSecondTransform_eq_eigen_secondDeriv hg hg2 hgb]
    ring
  rw [hleft, hright] at hs
  exact hs

/-- Same-parity second-order analogue of Slepian--Pollak equation (40). -/
theorem even_bandEigenvalue_sub_mul_secondDerivPairing
    {c lam_f lam_g : ℝ} {f g : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hf2c : Continuous (deriv (deriv f)))
    (hg2c : Continuous (deriv (deriv g)))
    (hfe : Function.Even f) (hge : Function.Even g)
    (hfb : ∀ x, bandTransform c f x = lam_f * f x)
    (hgb : ∀ x, bandTransform c g x = lam_g * g x) :
    (lam_f - lam_g) * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) =
      2 * lam_g * (f 1 * deriv g 1 - deriv f 1 * g 1) := by
  let W : ℝ → ℝ := fun x => deriv f x * g x - f x * deriv g x
  have hWd : ∀ x, HasDerivAt W
      (deriv (deriv f) x * g x - f x * deriv (deriv g) x) x := by
    intro x
    dsimp [W]
    have hraw := ((hf2 x).hasDerivAt.mul (hg x).hasDerivAt).sub
      ((hf x).hasDerivAt.mul (hg2 x).hasDerivAt)
    have heq :
        deriv (deriv f) x * g x + deriv f x * deriv g x -
            (deriv f x * deriv g x + f x * deriv (deriv g) x) =
          deriv (deriv f) x * g x - f x * deriv (deriv g) x := by ring
    rw [heq] at hraw
    exact hraw
  have hWderiv : deriv W =
      fun x => deriv (deriv f) x * g x - f x * deriv (deriv g) x :=
    funext fun x => (hWd x).deriv
  have hWInt : IntervalIntegrable (deriv W) volume (-1) 1 := by
    rw [hWderiv]
    exact ((hf2c.mul hg.continuous).intervalIntegrable _ _).sub
      ((hf.continuous.mul hg2c).intervalIntegrable _ _)
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (f := W) (fun x _ => (hWd x).differentiableAt) hWInt
  have hfneg := deriv_neg_of_even_crossSpectral hfe hf 1
  have hgneg := deriv_neg_of_even_crossSpectral hge hg 1
  have hfval := hfe 1
  have hgval := hge 1
  have hdiff :
      (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) -
          (∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x) =
        2 * (deriv f 1 * g 1 - f 1 * deriv g 1) := by
    rw [hWderiv, intervalIntegral.integral_sub] at hFTC
    · dsimp [W] at hFTC
      rw [hfneg, hgneg, hfval, hgval] at hFTC
      linarith
    · exact (hf2c.mul hg.continuous).intervalIntegrable _ _
    · exact (hf.continuous.mul hg2c).intervalIntegrable _ _
  have hscaled := integral_secondDeriv_pairing_scaled_of_bandEigenvalues
    hf hf2 hg hg2 hfb hgb
  calc
    (lam_f - lam_g) * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) =
        lam_f * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) -
          lam_g * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) := by ring
    _ = lam_g * (∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x) -
          lam_g * (∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) := by rw [hscaled]
    _ = -lam_g * ((∫ x in (-1 : ℝ)..1, deriv (deriv f) x * g x) -
          (∫ x in (-1 : ℝ)..1, f x * deriv (deriv g) x)) := by ring
    _ = -lam_g * (2 * (deriv f 1 * g 1 - f 1 * deriv g 1)) := by rw [hdiff]
    _ = 2 * lam_g * (f 1 * deriv g 1 - deriv f 1 * g 1) := by ring

/-- Exact cross-spectral identity for every pair of actual indexed even prolate modes. -/
theorem signedModeRadialData_crossSpectral_identity
    {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    (evenProlateSignedValue a m ^ (2 : ℕ) - evenProlateSignedValue a n ^ (2 : ℕ)) *
        (∫ x in (-1 : ℝ)..1,
          deriv (deriv (signedModeRadialData a m).R) x *
            (signedModeRadialData a n).R x) =
      evenProlateSignedValue a n ^ (2 : ℕ) * signedModeRadialBandwidth a ^ (2 : ℕ) *
        ((signedModeRadialData a n).s - (signedModeRadialData a m).s) := by
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  rcases hm with ⟨_, _, _, _, hmRdef, hmRSmooth, hmREven, hmROne, hmBand,
    _, _, _, hmEnd, _⟩
  rcases hn with ⟨_, _, _, _, hnRdef, hnRSmooth, hnREven, hnROne, hnBand,
    _, _, _, hnEnd, _⟩
  have hmRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a m).R x =
        evenProlateSignedValue a m ^ (2 : ℕ) * (signedModeRadialData a m).R x := by
    rw [hmRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hmBand
  have hnRBand : ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ (2 : ℕ) * (signedModeRadialData a n).R x := by
    rw [hnRdef]
    exact GaloisForLFunctions.RHTower.bandTransform_endpointNormalize_eigen hnBand
  have hmD : Differentiable ℝ (signedModeRadialData a m).R :=
    (contDiff_infty_iff_deriv.mp hmRSmooth).1
  have hmD2 : Differentiable ℝ (deriv (signedModeRadialData a m).R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hmRSmooth).2).1
  have hmD2c : Continuous (deriv (deriv (signedModeRadialData a m).R)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hmRSmooth).2).2.continuous
  have hnD : Differentiable ℝ (signedModeRadialData a n).R :=
    (contDiff_infty_iff_deriv.mp hnRSmooth).1
  have hnD2 : Differentiable ℝ (deriv (signedModeRadialData a n).R) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hnRSmooth).2).1
  have hnD2c : Continuous (deriv (deriv (signedModeRadialData a n).R)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hnRSmooth).2).2.continuous
  have hcross := even_bandEigenvalue_sub_mul_secondDerivPairing
    hmD hmD2 hnD hnD2 hmD2c hnD2c hmREven hnREven hmRBand hnRBand
  rw [hmROne, hnROne] at hcross
  have hend : 2 * (deriv (signedModeRadialData a n).R 1 -
      deriv (signedModeRadialData a m).R 1) =
      ((signedModeRadialData a n).s - (signedModeRadialData a m).s) *
        signedModeRadialBandwidth a ^ (2 : ℕ) := by
    linarith
  calc
    _ = 2 * evenProlateSignedValue a n ^ (2 : ℕ) *
        (deriv (signedModeRadialData a n).R 1 -
          deriv (signedModeRadialData a m).R 1) := by
      simpa [mul_sub, sub_mul] using hcross
    _ = evenProlateSignedValue a n ^ (2 : ℕ) *
        (2 * (deriv (signedModeRadialData a n).R 1 -
          deriv (signedModeRadialData a m).R 1)) := by ring
    _ = evenProlateSignedValue a n ^ (2 : ℕ) *
        (((signedModeRadialData a n).s - (signedModeRadialData a m).s) *
          signedModeRadialBandwidth a ^ (2 : ℕ)) := by rw [hend]
    _ = _ := by ring

/-- Distinct actual indexed modes have a nonzero oriented second-derivative pairing. -/
theorem signedModeRadialData_secondDerivPairing_ne_zero
    {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m ≠ n) :
    (∫ x in (-1 : ℝ)..1,
      deriv (deriv (signedModeRadialData a m).R) x *
        (signedModeRadialData a n).R x) ≠ 0 := by
  have hsne : (signedModeRadialData a n).s - (signedModeRadialData a m).s ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hmn ((signedModeRadialData_s_injective ha h.symm))
  have hval : evenProlateSignedValue a n ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n)
  have hc : signedModeRadialBandwidth a ^ (2 : ℕ) ≠ 0 := by
    dsimp [signedModeRadialBandwidth]
    positivity
  have hrhs : evenProlateSignedValue a n ^ (2 : ℕ) * signedModeRadialBandwidth a ^ (2 : ℕ) *
      ((signedModeRadialData a n).s - (signedModeRadialData a m).s) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hval hc) hsne
  intro hzero
  have hident := signedModeRadialData_crossSpectral_identity ha m n
  rw [hzero, mul_zero] at hident
  exact hrhs hident.symm

/-- For increasing greedy band index, separation orientation is exactly positivity of one
same-parity cross-derivative pairing. -/
theorem signedModeRadialData_secondDerivPairing_pos_iff_s_lt
    {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m < n) :
    0 < (∫ x in (-1 : ℝ)..1,
      deriv (deriv (signedModeRadialData a m).R) x *
        (signedModeRadialData a n).R x) ↔
      (signedModeRadialData a m).s < (signedModeRadialData a n).s := by
  have hgap : 0 < evenProlateSignedValue a m ^ (2 : ℕ) -
      evenProlateSignedValue a n ^ (2 : ℕ) := by
    exact sub_pos.mpr (evenProlateSignedValue_sq_strictAnti ha hmn)
  have hcoef : 0 < evenProlateSignedValue a n ^ (2 : ℕ) *
      signedModeRadialBandwidth a ^ (2 : ℕ) := by
    exact mul_pos (sq_pos_of_ne_zero (evenProlateSignedValue_ne_zero ha n)) (by
      dsimp [signedModeRadialBandwidth]
      positivity)
  have hident := signedModeRadialData_crossSpectral_identity ha m n
  calc
    0 < (∫ x in (-1 : ℝ)..1,
        deriv (deriv (signedModeRadialData a m).R) x *
          (signedModeRadialData a n).R x) ↔
        0 < (evenProlateSignedValue a m ^ (2 : ℕ) - evenProlateSignedValue a n ^ (2 : ℕ)) *
          (∫ x in (-1 : ℝ)..1,
            deriv (deriv (signedModeRadialData a m).R) x *
              (signedModeRadialData a n).R x) :=
      (mul_pos_iff_of_pos_left hgap).symm
    _ ↔ 0 < evenProlateSignedValue a n ^ (2 : ℕ) * signedModeRadialBandwidth a ^ (2 : ℕ) *
          ((signedModeRadialData a n).s - (signedModeRadialData a m).s) := by rw [hident]
    _ ↔ 0 < (signedModeRadialData a n).s - (signedModeRadialData a m).s :=
      mul_pos_iff_of_pos_left hcoef
    _ ↔ (signedModeRadialData a m).s < (signedModeRadialData a n).s := sub_pos

end RHTower
